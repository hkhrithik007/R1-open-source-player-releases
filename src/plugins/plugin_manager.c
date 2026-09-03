#include "plugin_manager.h"
#include "gui.h"
#include "gui_reload.h"
#include "audio.h"
#include "peq.h"
#include "http_client.h"
#include "playlist_files.h"
#include "plugin_json.h"
#include "plugin_storage.h"
#include "plugin_disabled_list.h"
#include "app_version.h"
#include "fallback_font.h"
#include "mbedtls/md5.h" /* plugin.md5() -- same primitive subsonic_client.c already uses for its own token auth */

#include "lua.h"
#include "lauxlib.h"
#include "lualib.h"

#include <dirent.h>
#include <fcntl.h>
#include <string.h>
#include <strings.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/stat.h>
#include <pthread.h>
#include <time.h>
#include <errno.h>
#include <stdatomic.h>
#include <limits.h>
#include <unistd.h>

#ifdef HOST_BUILD
  #define MUSIC_ROOT_DIR "./music"
#else
  /* SD card mount point -- see gui.c's own MUSIC_ROOT_DIR comment; each
   * file that needs it defines its own copy rather than sharing a header,
   * matching gui.c/remote_control.c/metadata_db.c already doing the same. */
  #define MUSIC_ROOT_DIR "/data/mnt/sd_0"

  /* Same override root assets.c's own asset_path() checks (see its own
   * comment there) -- duplicated here rather than shared via a header,
   * same convention as MUSIC_ROOT_DIR above. Only defined on target:
   * asset_path() never checks any override root on HOST_BUILD, so
   * plugin.set_icon() is a no-op there (see its own comment below) rather
   * than writing files nothing would ever read. */
  #define PLUGIN_THEME_OVERRIDE_ROOT "/usr/data/theme_overrides/"
#endif

/* Same "each file defines its own derived-path macro" convention as
 * MUSIC_ROOT_DIR above -- matches gui.c's own PLAYLISTS_DIR exactly. */
#define PLAYLISTS_DIR MUSIC_ROOT_DIR "/Playlists"

#define PLUGIN_MAX_FILES 16
#define PLUGIN_MAX_LIST_ITEMS 500
#define PLUGIN_MAX_ASYNC_HTTP 4
#define PLUGIN_ASYNC_HTTP_DEFAULT_MAX (512U * 1024U)
#define PLUGIN_ASYNC_HTTP_MAX_RESPONSE (2U * 1024U * 1024U)
#define PLUGIN_ASYNC_HTTP_MAX_REQUEST (1024U * 1024U)

typedef struct {
    lua_State * L;
    int open_ref; /* LUA_REGISTRYINDEX ref to the on_open function */
    char id[40];  /* only set/used for plugin_home_tiles[] -- empty for plugin_stream_tiles[],
                     which has no reordering concept and so never needs a stable name to
                     reference; home_layout_config.order[]/tiles[] key lookups need one. */
    char label[64];
    char icon[96];
    char icon_selected[96];
} plugin_tile_t;

/* Leaner sibling of plugin_tile_t for plugin.register_list_item() -- pill-
 * list rows (screen_builders.h's pill_list_item_t) now DO have an icon/
 * height/width/text_size slot (this session's row-layout work),
 * populated from this call's optional 4th `options` table -- see
 * append_list_item()'s own comment. Empty string ("") means "unset" for
 * icon_path/text_size, matching pill_list_item_t's own NULL convention one
 * level up (plugin_manager_get_*_list_item_options() below translates
 * empty-string back to NULL for its callers). */
typedef struct {
    lua_State * L;
    int open_ref;
    char label[64];
    char icon_path[256];
    int32_t row_height;
    int32_t row_width;
    char text_size[8];
} plugin_list_item_t;

typedef struct {
    lua_State * L;
    char id[64];
    char name[96];
    char version[32];
    bool defined;
    time_t last_library_refresh;
    /* Source filename (basename, e.g. "Themes.lua"), not just the derived
     * plugin id -- needed by plugin_manager_scan_available() to map a
     * loaded instance back to the file it came from even when the plugin
     * declared its own custom plugin.define() id rather than falling back
     * to the "legacy.<filename>" id below. */
    char filename[256];
} plugin_instance_t;

static plugin_instance_t plugin_instances[PLUGIN_MAX_FILES];
static int plugin_instance_count = 0;
static int loading_plugin_slot = -1;

/* plugin.storage and plugin.secrets need to know WHICH plugin is calling
 * at arbitrary runtime (not just at plugin.define() time, unlike
 * loading_plugin_slot above) -- each plugin owns exactly one lua_State for
 * its whole lifetime (this file's own top comment), so a linear scan
 * matching L is enough; PLUGIN_MAX_FILES is small and this only runs on
 * an explicit plugin.storage/secrets call, not per frame. */
static plugin_instance_t * plugin_instance_for_state(lua_State * L) {
    for (int i = 0; i < PLUGIN_MAX_FILES; i++) {
        if (plugin_instances[i].L == L) return &plugin_instances[i];
    }
    return NULL;
}

/* Shared by every plugin.storage and plugin.secrets binding below --
 * requires plugin.define({id=...}) to have already run on this lua_State,
 * matching plugin_storage.c's own expectation that plugin_id is a real,
 * validated identity, not an empty/default string. */
static const char * require_plugin_id(lua_State * L) {
    plugin_instance_t * inst = plugin_instance_for_state(L);
    if (!inst || !inst->defined || !inst->id[0]) {
        luaL_error(L, "plugin.storage/secrets requires plugin.define({id=...}) to run first");
        return NULL; /* unreachable -- luaL_error() longjmps */
    }
    return inst->id;
}

static const char * check_plugin_external_path(lua_State * L, int index, const char * api) {
    const char * path = luaL_checkstring(L, index);
    if (plugin_storage_path_is_reserved(path)) {
        luaL_error(L, "%s: path is reserved for plugin.storage/plugin.secrets", api);
        return NULL; /* unreachable -- luaL_error() longjmps */
    }
    return path;
}

static plugin_list_item_t plugin_books_list_items[PLUGIN_MAX_BOOKS_LIST_ITEMS];
static int plugin_books_list_item_count = 0;

static plugin_list_item_t plugin_settings_list_items[PLUGIN_MAX_SETTINGS_LIST_ITEMS];
static int plugin_settings_list_item_count = 0;

static plugin_list_item_t plugin_display_list_items[PLUGIN_MAX_DISPLAY_LIST_ITEMS];
static int plugin_display_list_item_count = 0;

static plugin_list_item_t plugin_playback_list_items[PLUGIN_MAX_PLAYBACK_LIST_ITEMS];
static int plugin_playback_list_item_count = 0;

static plugin_list_item_t plugin_power_list_items[PLUGIN_MAX_POWER_LIST_ITEMS];
static int plugin_power_list_item_count = 0;

static plugin_list_item_t plugin_system_list_items[PLUGIN_MAX_SYSTEM_LIST_ITEMS];
static int plugin_system_list_item_count = 0;

static plugin_tile_t plugin_stream_tiles[PLUGIN_MAX_STREAM_TILES];
static int plugin_stream_tile_count = 0;

static plugin_tile_t plugin_home_tiles[PLUGIN_MAX_HOME_TILES];
static int plugin_home_tile_count = 0;

typedef struct {
    lua_State * L;
    int select_ref;
} plugin_list_callback_t;

static plugin_list_callback_t plugin_list_callbacks[PLUGIN_LIST_SCREEN_POOL_SIZE];

typedef struct {
    lua_State * L;
    int callback_ref;
} plugin_settings_list_row_ref_t;

static plugin_settings_list_row_ref_t
    plugin_settings_list_rows[PLUGIN_SETTINGS_LIST_SCREEN_POOL_SIZE][PLUGIN_SETTINGS_LIST_MAX_ROWS];
static int plugin_settings_list_row_counts[PLUGIN_SETTINGS_LIST_SCREEN_POOL_SIZE];

static void fill_tile_icon(plugin_tile_t * t, const char * icon, const char * default_icon,
                            const char * default_icon_selected) {
    if (icon) {
        char base[80];
        snprintf(base, sizeof(base), "%s", icon);
        char * dot = strrchr(base, '.');
        if (dot) *dot = '\0';
        snprintf(t->icon, sizeof(t->icon), "%s", icon);
        snprintf(t->icon_selected, sizeof(t->icon_selected), "%s_s.png", base);
    } else {
        snprintf(t->icon, sizeof(t->icon), "%s", default_icon);
        snprintf(t->icon_selected, sizeof(t->icon_selected), "%s", default_icon_selected);
    }
}

static bool is_valid_text_size(const char * text_size) {
    return strcmp(text_size, "small") == 0 || strcmp(text_size, "medium") == 0 || strcmp(text_size, "large") == 0 ||
           strcmp(text_size, "mono") == 0;
}

static void append_list_item(plugin_list_item_t * array, int * count, lua_State * L, const char * label) {
    lua_pushvalue(L, 3);
    int ref = luaL_ref(L, LUA_REGISTRYINDEX);

    plugin_list_item_t * item = &array[(*count)++];
    item->L = L;
    item->open_ref = ref;
    utf8_truncate_safe(item->label, label, sizeof(item->label));
    utf8_sanitize(item->label);
    item->icon_path[0] = '\0';
    item->row_height = 0;
    item->row_width = 0;
    item->text_size[0] = '\0';

    if (lua_gettop(L) >= 4 && lua_istable(L, 4)) {
        lua_getfield(L, 4, "icon");
        const char * icon = lua_tostring(L, -1);
        if (icon) snprintf(item->icon_path, sizeof(item->icon_path), "%s", icon);
        lua_pop(L, 1);

        lua_getfield(L, 4, "height");
        item->row_height = (int32_t) luaL_optinteger(L, -1, 0);
        lua_pop(L, 1);

        lua_getfield(L, 4, "width");
        item->row_width = (int32_t) luaL_optinteger(L, -1, 0);
        lua_pop(L, 1);

        lua_getfield(L, 4, "text_size");
        const char * text_size = lua_tostring(L, -1);
        if (text_size) {
            if (!is_valid_text_size(text_size)) {
                lua_pop(L, 1);
                luaL_error(L, "plugin.register_list_item: unknown text_size '%s' (expected \"small\", \"medium\", \"large\", or \"mono\")",
                           text_size);
            }
            snprintf(item->text_size, sizeof(item->text_size), "%s", text_size);
        }
        lua_pop(L, 1);
    }
}

static int l_plugin_register_list_item(lua_State * L) {
    const char * list_id = luaL_checkstring(L, 1);
    const char * label = luaL_checkstring(L, 2);
    luaL_checktype(L, 3, LUA_TFUNCTION);

    if (strcmp(list_id, "books") == 0) {
        if (plugin_books_list_item_count >= PLUGIN_MAX_BOOKS_LIST_ITEMS) {
            return luaL_error(L, "plugin.register_list_item: too many items registered for \"books\" (max %d)",
                               PLUGIN_MAX_BOOKS_LIST_ITEMS);
        }
        append_list_item(plugin_books_list_items, &plugin_books_list_item_count, L, label);
    } else if (strcmp(list_id, "settings") == 0) {
        if (plugin_settings_list_item_count >= PLUGIN_MAX_SETTINGS_LIST_ITEMS) {
            return luaL_error(L, "plugin.register_list_item: too many items registered for \"settings\" (max %d)",
                               PLUGIN_MAX_SETTINGS_LIST_ITEMS);
        }
        append_list_item(plugin_settings_list_items, &plugin_settings_list_item_count, L, label);
    } else if (strcmp(list_id, "display") == 0) {
        if (plugin_display_list_item_count >= PLUGIN_MAX_DISPLAY_LIST_ITEMS) {
            return luaL_error(L, "plugin.register_list_item: too many items registered for \"display\" (max %d)",
                               PLUGIN_MAX_DISPLAY_LIST_ITEMS);
        }
        append_list_item(plugin_display_list_items, &plugin_display_list_item_count, L, label);
    } else if (strcmp(list_id, "playback") == 0) {
        if (plugin_playback_list_item_count >= PLUGIN_MAX_PLAYBACK_LIST_ITEMS) {
            return luaL_error(L, "plugin.register_list_item: too many items registered for \"playback\" (max %d)",
                               PLUGIN_MAX_PLAYBACK_LIST_ITEMS);
        }
        append_list_item(plugin_playback_list_items, &plugin_playback_list_item_count, L, label);
    } else if (strcmp(list_id, "power") == 0) {
        if (plugin_power_list_item_count >= PLUGIN_MAX_POWER_LIST_ITEMS) {
            return luaL_error(L, "plugin.register_list_item: too many items registered for \"power\" (max %d)",
                               PLUGIN_MAX_POWER_LIST_ITEMS);
        }
        append_list_item(plugin_power_list_items, &plugin_power_list_item_count, L, label);
    } else if (strcmp(list_id, "system") == 0) {
        if (plugin_system_list_item_count >= PLUGIN_MAX_SYSTEM_LIST_ITEMS) {
            return luaL_error(L, "plugin.register_list_item: too many items registered for \"system\" (max %d)",
                               PLUGIN_MAX_SYSTEM_LIST_ITEMS);
        }
        append_list_item(plugin_system_list_items, &plugin_system_list_item_count, L, label);
    } else {
        return luaL_error(L, "plugin.register_list_item: unknown list_id '%s' (expected \"books\", \"settings\", \"display\", \"playback\", \"power\", or \"system\")", list_id);
    }
    return 0;
}

static int l_plugin_register_stream_media_tile(lua_State * L) {
    const char * label = luaL_checkstring(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION);
    const char * icon = (lua_gettop(L) >= 3 && !lua_isnil(L, 3)) ? luaL_checkstring(L, 3) : NULL;

    if (plugin_stream_tile_count >= PLUGIN_MAX_STREAM_TILES) {
        return luaL_error(L, "too many stream media tiles registered (max %d)", PLUGIN_MAX_STREAM_TILES);
    }

    lua_pushvalue(L, 2);
    int ref = luaL_ref(L, LUA_REGISTRYINDEX);

    plugin_tile_t * t = &plugin_stream_tiles[plugin_stream_tile_count++];
    t->L = L;
    t->open_ref = ref;
    utf8_truncate_safe(t->label, label, sizeof(t->label));
    utf8_sanitize(t->label);
    fill_tile_icon(t, icon, "stream_media/radio.png", "stream_media/radio_s.png");
    return 0;
}

static bool plugin_id_is_valid(const char * id);

static int l_plugin_register_home_tile(lua_State * L) {
    const char * id = luaL_checkstring(L, 1);
    const char * label = luaL_checkstring(L, 2);
    luaL_checktype(L, 3, LUA_TFUNCTION);
    const char * icon = luaL_checkstring(L, 4);

    if (!plugin_id_is_valid(id) || strlen(id) >= sizeof(plugin_home_tiles[0].id)) {
        return luaL_error(L, "plugin.register_home_tile: id must be 1-%zu characters using letters, digits, '.', '_' or '-'",
                           sizeof(plugin_home_tiles[0].id) - 1);
    }
    for (int k = 0; k < HOME_LAYOUT_TILE_COUNT; k++) {
        if (strcmp(id, home_layout_tile_keys[k]) == 0) {
            return luaL_error(L, "plugin.register_home_tile: id '%s' is reserved for the native Home tile of "
                               "the same name -- pick a different id", id);
        }
    }
    if (plugin_manager_find_home_tile_by_id(id) >= 0) {
        return luaL_error(L, "plugin.register_home_tile: id '%s' is already registered", id);
    }
    if (plugin_home_tile_count >= PLUGIN_MAX_HOME_TILES) {
        return luaL_error(L, "too many home tiles registered (max %d)", PLUGIN_MAX_HOME_TILES);
    }
    if (icon[0] == '\0') {
        return luaL_error(L, "plugin.register_home_tile: icon must not be empty");
    }
    if (strlen(icon) >= 80) {
        return luaL_error(L, "plugin.register_home_tile: icon path '%s' is too long (max 79 characters)", icon);
    }

    lua_pushvalue(L, 3);
    int ref = luaL_ref(L, LUA_REGISTRYINDEX);

    plugin_tile_t * t = &plugin_home_tiles[plugin_home_tile_count++];
    t->L = L;
    t->open_ref = ref;
    snprintf(t->id, sizeof(t->id), "%s", id);
    utf8_truncate_safe(t->label, label, sizeof(t->label));
    utf8_sanitize(t->label);
    fill_tile_icon(t, icon, "", "");
    return 0;
}

static int l_plugin_show_list(lua_State * L) {
    const char * title = luaL_checkstring(L, 1);
    luaL_checktype(L, 2, LUA_TTABLE);
    luaL_checktype(L, 3, LUA_TFUNCTION);

    lua_Unsigned raw_n = lua_rawlen(L, 2);
    int n = (raw_n > (lua_Unsigned) PLUGIN_MAX_LIST_ITEMS) ? PLUGIN_MAX_LIST_ITEMS : (int) raw_n;

    static char label_bufs[PLUGIN_MAX_LIST_ITEMS][160];
    static const char * labels[PLUGIN_MAX_LIST_ITEMS];
    static char icon_bufs[PLUGIN_MAX_LIST_ITEMS][256];
    static const char * icon_paths[PLUGIN_MAX_LIST_ITEMS];
    static char text_size_bufs[PLUGIN_MAX_LIST_ITEMS][8];
    static const char * text_sizes[PLUGIN_MAX_LIST_ITEMS];

    for (int i = 0; i < n; i++) {
        lua_rawgeti(L, 2, i + 1);
        icon_bufs[i][0] = '\0';
        icon_paths[i] = NULL;
        text_size_bufs[i][0] = '\0';
        text_sizes[i] = NULL;

        if (lua_istable(L, -1)) {
            lua_getfield(L, -1, "label");
            const char * s = lua_tostring(L, -1);
            snprintf(label_bufs[i], sizeof(label_bufs[i]), "%s", s ? s : "");
            lua_pop(L, 1);

            lua_getfield(L, -1, "icon");
            const char * icon = lua_tostring(L, -1);
            if (icon) {
                snprintf(icon_bufs[i], sizeof(icon_bufs[i]), "%s", icon);
                icon_paths[i] = icon_bufs[i];
            }
            lua_pop(L, 1);

            lua_getfield(L, -1, "text_size");
            const char * text_size = lua_tostring(L, -1);
            if (text_size) {
                if (!is_valid_text_size(text_size)) {
                    return luaL_error(L, "plugin.show_list: row %d has an unknown text_size '%s' (expected \"small\", \"medium\", \"large\", or \"mono\")",
                                       i + 1, text_size);
                }
                snprintf(text_size_bufs[i], sizeof(text_size_bufs[i]), "%s", text_size);
                text_sizes[i] = text_size_bufs[i];
            }
            lua_pop(L, 1);
        } else {
            const char * s = lua_tostring(L, -1);
            snprintf(label_bufs[i], sizeof(label_bufs[i]), "%s", s ? s : "");
        }
        labels[i] = label_bufs[i];
        lua_pop(L, 1);
    }

    int32_t height = 0;
    int32_t width = 0;
    int selected_index = -1;
    if (lua_gettop(L) >= 4 && lua_istable(L, 4)) {
        lua_getfield(L, 4, "height");
        height = (int32_t) luaL_optinteger(L, -1, 0);
        lua_pop(L, 1);
        lua_getfield(L, 4, "width");
        width = (int32_t) luaL_optinteger(L, -1, 0);
        lua_pop(L, 1);
        lua_getfield(L, 4, "selected");
        if (!lua_isnil(L, -1)) {
            lua_Integer selected = luaL_checkinteger(L, -1);
            if (selected < 1 || selected > n)
                return luaL_error(L, "plugin.show_list: selected index %lld is outside 1..%d",
                                  (long long) selected, n);
            selected_index = (int) selected - 1;
        }
        lua_pop(L, 1);
    }

    lua_pushvalue(L, 3);
    int new_ref = luaL_ref(L, LUA_REGISTRYINDEX);
    int slot = gui_plugin_show_list(title, labels, icon_paths, text_sizes, height, width, selected_index, n);
    plugin_list_callback_t * cb = &plugin_list_callbacks[slot];
    if (cb->L && cb->select_ref != LUA_NOREF) luaL_unref(cb->L, LUA_REGISTRYINDEX, cb->select_ref);
    cb->L = L;
    cb->select_ref = new_ref;
    return 0;
}

static int l_plugin_show_settings_list(lua_State * L) {
    const char * title = luaL_checkstring(L, 1);
    luaL_checktype(L, 2, LUA_TTABLE);

    lua_Unsigned raw_n = lua_rawlen(L, 2);
    int n = (raw_n > (lua_Unsigned) PLUGIN_SETTINGS_LIST_MAX_ROWS) ? PLUGIN_SETTINGS_LIST_MAX_ROWS : (int) raw_n;

    static char label_bufs[PLUGIN_SETTINGS_LIST_MAX_ROWS][96];
    static const char * labels[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static int row_types[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static bool toggle_initial[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static int slider_min[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static int slider_max[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static int slider_value[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static char icon_bufs[PLUGIN_SETTINGS_LIST_MAX_ROWS][256];
    static const char * icon_paths[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static int32_t heights[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static int32_t widths[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    static char text_size_bufs[PLUGIN_SETTINGS_LIST_MAX_ROWS][8];
    static const char * text_sizes[PLUGIN_SETTINGS_LIST_MAX_ROWS];
    int new_refs[PLUGIN_SETTINGS_LIST_MAX_ROWS];

    int count = 0;
    int slider_count = 0;
    for (int i = 0; i < n; i++) {
        lua_rawgeti(L, 2, i + 1);
        if (!lua_istable(L, -1)) {
            lua_pop(L, 1);
            continue;
        }

        lua_getfield(L, -1, "type");
        const char * type = lua_tostring(L, -1);
        int row_type = -1;
        if (type) {
            if (strcmp(type, "row") == 0) row_type = PLUGIN_SETTINGS_ROW_TAP;
            else if (strcmp(type, "toggle") == 0) row_type = PLUGIN_SETTINGS_ROW_TOGGLE;
            else if (strcmp(type, "slider") == 0) row_type = PLUGIN_SETTINGS_ROW_SLIDER;
        }
        if (row_type < 0) {
            return luaL_error(L, "plugin.show_settings_list: row %d has an unknown or missing type (expected \"row\", \"toggle\", or \"slider\")", i + 1);
        }
        lua_pop(L, 1);

        if (row_type == PLUGIN_SETTINGS_ROW_SLIDER && slider_count >= PLUGIN_SETTINGS_LIST_MAX_SLIDERS) {
            lua_pop(L, 1);
            continue;
        }

        lua_getfield(L, -1, "label");
        const char * label = lua_tostring(L, -1);
        snprintf(label_bufs[count], sizeof(label_bufs[count]), "%s", label ? label : "");
        lua_pop(L, 1);

        const char * cb_field = (row_type == PLUGIN_SETTINGS_ROW_TAP) ? "on_select" : "on_change";
        lua_getfield(L, -1, cb_field);
        if (!lua_isfunction(L, -1)) {
            return luaL_error(L, "plugin.show_settings_list: row %d ('%s') missing %s function", i + 1, label ? label : "", cb_field);
        }
        new_refs[count] = luaL_ref(L, LUA_REGISTRYINDEX);

        toggle_initial[count] = false;
        slider_min[count] = 0;
        slider_max[count] = 100;
        slider_value[count] = 0;
        if (row_type == PLUGIN_SETTINGS_ROW_TOGGLE) {
            lua_getfield(L, -1, "value");
            toggle_initial[count] = lua_toboolean(L, -1);
            lua_pop(L, 1);
        } else if (row_type == PLUGIN_SETTINGS_ROW_SLIDER) {
            lua_getfield(L, -1, "min");
            slider_min[count] = (int) luaL_optinteger(L, -1, 0);
            lua_pop(L, 1);
            lua_getfield(L, -1, "max");
            slider_max[count] = (int) luaL_optinteger(L, -1, 100);
            lua_pop(L, 1);
            lua_getfield(L, -1, "value");
            slider_value[count] = (int) luaL_optinteger(L, -1, slider_min[count]);
            lua_pop(L, 1);
        }

        icon_bufs[count][0] = '\0';
        icon_paths[count] = NULL;
        lua_getfield(L, -1, "icon");
        const char * icon = lua_tostring(L, -1);
        if (icon) {
            snprintf(icon_bufs[count], sizeof(icon_bufs[count]), "%s", icon);
            icon_paths[count] = icon_bufs[count];
        }
        lua_pop(L, 1);

        lua_getfield(L, -1, "height");
        heights[count] = (int32_t) luaL_optinteger(L, -1, 0);
        lua_pop(L, 1);

        lua_getfield(L, -1, "width");
        widths[count] = (int32_t) luaL_optinteger(L, -1, 0);
        lua_pop(L, 1);

        text_size_bufs[count][0] = '\0';
        text_sizes[count] = NULL;
        lua_getfield(L, -1, "text_size");
        const char * text_size = lua_tostring(L, -1);
        if (text_size) {
            if (!is_valid_text_size(text_size)) {
                return luaL_error(L, "plugin.show_settings_list: row %d has an unknown text_size '%s' (expected \"small\", \"medium\", \"large\", or \"mono\")",
                                   i + 1, text_size);
            }
            snprintf(text_size_bufs[count], sizeof(text_size_bufs[count]), "%s", text_size);
            text_sizes[count] = text_size_bufs[count];
        }
        lua_pop(L, 1);

        labels[count] = label_bufs[count];
        row_types[count] = row_type;
        if (row_type == PLUGIN_SETTINGS_ROW_SLIDER) slider_count++;
        count++;

        lua_pop(L, 1);
    }

    int slot = gui_plugin_show_settings_list(title, row_types, labels, toggle_initial, slider_min, slider_max,
                                              slider_value, icon_paths, heights, widths, text_sizes, count);
    if (slot < 0 || slot >= PLUGIN_SETTINGS_LIST_SCREEN_POOL_SIZE) return 0;

    for (int i = 0; i < plugin_settings_list_row_counts[slot]; i++) {
        if (plugin_settings_list_rows[slot][i].L) {
            luaL_unref(plugin_settings_list_rows[slot][i].L, LUA_REGISTRYINDEX,
                       plugin_settings_list_rows[slot][i].callback_ref);
        }
    }
    for (int i = 0; i < count; i++) {
        plugin_settings_list_rows[slot][i].L = L;
        plugin_settings_list_rows[slot][i].callback_ref = new_refs[i];
    }
    plugin_settings_list_row_counts[slot] = count;

    return 0;
}

static int l_plugin_list_dir(lua_State * L) {
    const char * path = check_plugin_external_path(L, 1, "plugin.list_dir");
    lua_newtable(L);

    DIR * d = opendir(path);
    if (!d) return 1;

    int idx = 1;
    struct dirent * ent;
    while ((ent = readdir(d)) != NULL) {
        if (ent->d_name[0] == '.') continue;

        char full[1024];
        snprintf(full, sizeof(full), "%s/%s", path, ent->d_name);
        struct stat st;
        bool is_dir = false;
        if (stat(full, &st) == 0) is_dir = S_ISDIR(st.st_mode);

        lua_newtable(L);
        lua_pushstring(L, ent->d_name);
        lua_setfield(L, -2, "name");
        lua_pushboolean(L, is_dir);
        lua_setfield(L, -2, "dir");
        lua_rawseti(L, -2, idx++);
    }
    closedir(d);
    return 1;
}

static int l_plugin_sd_root(lua_State * L) {
    lua_pushstring(L, MUSIC_ROOT_DIR);
    return 1;
}

static int l_plugin_mkdir(lua_State * L) {
    const char * path = check_plugin_external_path(L, 1, "plugin.mkdir");
    size_t len = strlen(path);
    if (len == 0 || len >= PATH_MAX) {
        lua_pushnil(L);
        lua_pushstring(L, "invalid path");
        return 2;
    }

    char buf[PATH_MAX];
    memcpy(buf, path, len + 1);
    while (len > 1 && buf[len - 1] == '/') buf[--len] = '\0';

    for (size_t i = 1; i <= len; i++) {
        if (buf[i] != '/' && buf[i] != '\0') continue;
        char saved = buf[i];
        buf[i] = '\0';
        if (buf[0] != '\0' && mkdir(buf, 0755) != 0) {
            int saved_errno = errno;
            struct stat st;
            if (saved_errno != EEXIST || stat(buf, &st) != 0 || !S_ISDIR(st.st_mode)) {
                buf[i] = saved;
                lua_pushnil(L);
                lua_pushstring(L, strerror(saved_errno));
                return 2;
            }
        }
        buf[i] = saved;
    }

    lua_pushboolean(L, true);
    return 1;
}

static int l_plugin_play_file(lua_State * L) {
    const char * path = check_plugin_external_path(L, 1, "plugin.play_file");
    gui_plugin_play_paths(&path, 1, 0);
    return 0;
}

static int l_plugin_play_list(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);
    int start = (int) luaL_optinteger(L, 2, 1) - 1;

    lua_Unsigned raw_n = lua_rawlen(L, 1);
    int n = (raw_n > (lua_Unsigned) PLUGIN_MAX_LIST_ITEMS) ? PLUGIN_MAX_LIST_ITEMS : (int) raw_n;
    if (n <= 0) return 0;
    if (start < 0) start = 0;
    if (start >= n) start = n - 1;

    static char path_bufs[PLUGIN_MAX_LIST_ITEMS][512];
    static const char * paths[PLUGIN_MAX_LIST_ITEMS];
    for (int i = 0; i < n; i++) {
        lua_rawgeti(L, 1, i + 1);
        const char * s = lua_tostring(L, -1);
        if (s && plugin_storage_path_is_reserved(s)) {
            lua_pop(L, 1);
            return luaL_error(L, "plugin.play_list: path is reserved for plugin.storage/plugin.secrets");
        }
        snprintf(path_bufs[i], sizeof(path_bufs[i]), "%s", s ? s : "");
        paths[i] = path_bufs[i];
        lua_pop(L, 1);
    }

    gui_plugin_play_paths(paths, n, start);
    return 0;
}

static lua_Number check_bounded_number(lua_State * L, int table_index, const char * field, const char * fn_name, lua_Number max_value) {
    lua_getfield(L, table_index, field);
    lua_Number val = luaL_optnumber(L, -1, 0);
    lua_pop(L, 1);
    if (!(val >= 0) || !(val <= max_value)) {
        luaL_error(L, "%s: %s must be a finite number between 0 and %.0f", fn_name, field, (double) max_value);
    }
    return val;
}

static void parse_remote_track_table(lua_State * L, int table_index, remote_track_meta_t * out, const char * fn_name) {
    memset(out, 0, sizeof(*out));

    lua_getfield(L, table_index, "provider");
    const char * provider = luaL_checkstring(L, -1);
    if (provider[0] == '\0') luaL_error(L, "%s: provider must not be empty", fn_name);
    if (strlen(provider) >= sizeof(out->provider)) luaL_error(L, "%s: provider is too long", fn_name);
    snprintf(out->provider, sizeof(out->provider), "%s", provider);
    lua_pop(L, 1);

    lua_getfield(L, table_index, "track_id");
    const char * track_id = luaL_checkstring(L, -1);
    if (track_id[0] == '\0') luaL_error(L, "%s: track_id must not be empty", fn_name);
    if (strlen(track_id) >= sizeof(out->track_id)) luaL_error(L, "%s: track_id is too long", fn_name);
    snprintf(out->track_id, sizeof(out->track_id), "%s", track_id);
    lua_pop(L, 1);

    {
        char key[256];
        if (!remote_track_make_key(out->provider, out->track_id, key, sizeof(key))) {
            luaL_error(L, "%s: provider/track_id must not contain '/' or control characters, and must fit the synthetic key", fn_name);
        }
    }

    lua_getfield(L, table_index, "stream_url");
    const char * stream_url = luaL_checkstring(L, -1);
    if (stream_url[0] == '\0') luaL_error(L, "%s: stream_url must not be empty", fn_name);
    if (strlen(stream_url) >= sizeof(out->stream_url)) luaL_error(L, "%s: stream_url is too long", fn_name);
    snprintf(out->stream_url, sizeof(out->stream_url), "%s", stream_url);
    lua_pop(L, 1);

#define OPT_STR_FIELD(field, name) \
    lua_getfield(L, table_index, name); \
    const char * field##_val = luaL_optstring(L, -1, ""); \
    if (strlen(field##_val) >= sizeof(out->field)) luaL_error(L, "%s: " name " is too long", fn_name); \
    snprintf(out->field, sizeof(out->field), "%s", field##_val); \
    lua_pop(L, 1);

    OPT_STR_FIELD(title, "title")
    OPT_STR_FIELD(artist, "artist")
    OPT_STR_FIELD(album, "album")
    OPT_STR_FIELD(artwork_url, "artwork_url")
#undef OPT_STR_FIELD

    lua_getfield(L, table_index, "codec");
    const char * codec_val = luaL_optstring(L, -1, "");
    if (codec_val[0] != '\0' && strcasecmp(codec_val, "mp3") != 0 && strcasecmp(codec_val, "flac") != 0 &&
        strcasecmp(codec_val, "aac") != 0) {
        luaL_error(L, "%s: unknown codec '%s' -- must be \"mp3\", \"flac\", \"aac\", or omitted", fn_name, codec_val);
    }
    if (strlen(codec_val) >= sizeof(out->codec)) luaL_error(L, "%s: codec is too long", fn_name);
    snprintf(out->codec, sizeof(out->codec), "%s", codec_val);
    lua_pop(L, 1);

    out->duration_ms = (uint32_t) check_bounded_number(L, table_index, "duration_ms", fn_name, 24.0 * 3600.0 * 1000.0);
    out->sample_rate = (unsigned int) check_bounded_number(L, table_index, "sample_rate", fn_name, 1000000.0);
    out->bit_depth = (unsigned int) check_bounded_number(L, table_index, "bit_depth", fn_name, 64.0);
    out->channels = (unsigned int) check_bounded_number(L, table_index, "channels", fn_name, 64.0);
    out->bitrate_kbps = (unsigned int) check_bounded_number(L, table_index, "bitrate_kbps", fn_name, 100000.0);

    lua_getfield(L, table_index, "replaygain_db");
    if (!lua_isnil(L, -1)) {
        double gain = luaL_checknumber(L, -1);
        if (!(gain >= -100.0 && gain <= 100.0)) luaL_error(L, "%s: replaygain_db must be a finite number between -100 and 100", fn_name);
        out->has_replaygain = true;
        out->replaygain_db = gain;
    }
    lua_pop(L, 1);

    lua_getfield(L, table_index, "verify_tls");
    out->verify_tls = lua_isnil(L, -1) ? true : lua_toboolean(L, -1);
    lua_pop(L, 1);
}

static int l_plugin_play_remote(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);
    remote_track_meta_t track;
    parse_remote_track_table(L, 1, &track, "plugin.play_remote");
    gui_plugin_play_remote_tracks(&track, 1, 0);
    return 0;
}

static int l_plugin_queue_remote_list(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);
    int start = (int) luaL_optinteger(L, 2, 1) - 1;

    lua_Unsigned raw_n = lua_rawlen(L, 1);
    int n = (raw_n > (lua_Unsigned) PLUGIN_MAX_LIST_ITEMS) ? PLUGIN_MAX_LIST_ITEMS : (int) raw_n;
    if (n <= 0) return 0;
    if (start < 0) start = 0;
    if (start >= n) start = n - 1;

    remote_track_meta_t * tracks = (remote_track_meta_t *) lua_newuserdata(L, sizeof(remote_track_meta_t) * (size_t) n);
    for (int i = 0; i < n; i++) {
        lua_rawgeti(L, 1, i + 1);
        luaL_checktype(L, -1, LUA_TTABLE);
        parse_remote_track_table(L, lua_gettop(L), &tracks[i], "plugin.queue_remote_list");
        lua_pop(L, 1);
    }

    gui_plugin_play_remote_tracks(tracks, n, start);
    return 0;
}

static int l_plugin_show_toast(lua_State * L) {
    const char * msg = luaL_checkstring(L, 1);
    lua_Integer duration_ms = luaL_optinteger(L, 2, 5000);
    if (duration_ms < 100 || duration_ms > 30000)
        return luaL_error(L, "plugin.show_toast: duration_ms must be between 100 and 30000");
    gui_plugin_show_toast(msg, (uint32_t) duration_ms);
    return 0;
}

#ifndef HOST_BUILD
static bool files_identical(const char * a_path, const char * b_path) {
    struct stat sa, sb;
    if (stat(a_path, &sa) != 0 || stat(b_path, &sb) != 0) return false;
    if (!S_ISREG(sa.st_mode) || !S_ISREG(sb.st_mode)) return false;
    if (sa.st_size != sb.st_size) return false;

    FILE * a = fopen(a_path, "rb");
    FILE * b = fopen(b_path, "rb");
    if (!a || !b) {
        if (a) fclose(a);
        if (b) fclose(b);
        return false;
    }

    char ba[4096], bb[4096];
    bool same = true;
    for (;;) {
        size_t na = fread(ba, 1, sizeof(ba), a);
        size_t nb = fread(bb, 1, sizeof(bb), b);
        if (na != nb || memcmp(ba, bb, na) != 0) {
            same = false;
            break;
        }
        if (na == 0) break;
    }
    if (ferror(a) || ferror(b)) same = false;
    fclose(a);
    fclose(b);
    return same;
}

static bool copy_file(const char * src_path, const char * dst_path) {
    if (files_identical(src_path, dst_path)) return true;
    FILE * in = fopen(src_path, "rb");
    if (!in) return false;
    char tmp_path[640];
    if (snprintf(tmp_path, sizeof(tmp_path), "%s.tmp.%ld", dst_path, (long) getpid()) >= (int) sizeof(tmp_path)) {
        fclose(in);
        return false;
    }
    FILE * out = fopen(tmp_path, "wb");
    if (!out) {
        fclose(in);
        return false;
    }

    bool ok = true;
    char buf[65536];
    size_t n;
    while ((n = fread(buf, 1, sizeof(buf), in)) > 0) {
        if (fwrite(buf, 1, n, out) != n) {
            ok = false;
            break;
        }
    }
    ok = ok && !ferror(in);
    fclose(in);
    if (fclose(out) != 0) ok = false;

    if (ok) ok = rename(tmp_path, dst_path) == 0;
    if (!ok) remove(tmp_path);
    return ok;
}

static void set_home_background_image(lua_State * L, const char * source_path, home_layout_config_t * config) {
    const char * dot = strrchr(source_path, '.');
    const char * ext = NULL;
    if (dot && strcasecmp(dot, ".png") == 0) ext = ".png";
    else if (dot && strcasecmp(dot, ".jpg") == 0) ext = ".jpg";
    else if (dot && strcasecmp(dot, ".jpeg") == 0) ext = ".jpeg";
    if (!ext) {
        luaL_error(L, "plugin.set_home_layout: options.background_image '%s' must be a .png, .jpg, or .jpeg file",
                   source_path);
        return;
    }

    char relative_path[32];
    snprintf(relative_path, sizeof(relative_path), "home/background%s", ext);
    char dst_path[600];
    snprintf(dst_path, sizeof(dst_path), "%s%s", PLUGIN_THEME_OVERRIDE_ROOT, relative_path);

    mkdir(PLUGIN_THEME_OVERRIDE_ROOT, 0755);
    char dir_only[600];
    snprintf(dir_only, sizeof(dir_only), "%shome", PLUGIN_THEME_OVERRIDE_ROOT);
    mkdir(dir_only, 0755);

    if (!copy_file(source_path, dst_path)) {
        luaL_error(L, "plugin.set_home_layout: could not copy options.background_image '%s' to '%s'",
                   source_path, relative_path);
        return;
    }

    snprintf(config->background_image, sizeof(config->background_image), "%s", relative_path);
    config->has_background_image = true;
}
#endif

static int l_plugin_set_icon(lua_State * L) {
    const char * relative_path = luaL_checkstring(L, 1);
    const char * source_path = check_plugin_external_path(L, 2, "plugin.set_icon");

#ifndef HOST_BUILD
    if (relative_path[0] == '/' || strstr(relative_path, "..") != NULL) {
        return luaL_error(L, "plugin.set_icon: relative_path must be a plain path under the theme root, got '%s'",
                           relative_path);
    }

    char dst_path[600];
    snprintf(dst_path, sizeof(dst_path), "%s%s", PLUGIN_THEME_OVERRIDE_ROOT, relative_path);

    mkdir(PLUGIN_THEME_OVERRIDE_ROOT, 0755);
    char dir_only[600];
    snprintf(dir_only, sizeof(dir_only), "%s", dst_path);
    char * slash = strrchr(dir_only, '/');
    if (slash) {
        *slash = '\0';
        mkdir(dir_only, 0755);
    }

    if (!copy_file(source_path, dst_path)) {
        return luaL_error(L, "plugin.set_icon: could not copy '%s' to '%s'", source_path, relative_path);
    }
#else
    (void) source_path;
#endif
    return 0;
}

static int l_plugin_set_background_color(lua_State * L) {
    const char * slot = luaL_checkstring(L, 1);
    lua_Integer rgb = luaL_checkinteger(L, 2);

    if (strcmp(slot, "screen") != 0 && strcmp(slot, "card") != 0 && strcmp(slot, "list_row") != 0) {
        return luaL_error(L, "plugin.set_background_color: unknown slot '%s' (expected \"screen\", \"card\", or \"list_row\")",
                           slot);
    }

    gui_plugin_set_background_color(slot, (uint32_t) rgb);
    return 0;
}

static int l_plugin_set_text_color(lua_State * L) {
    const char * slot = luaL_checkstring(L, 1);
    lua_Integer rgb = luaL_checkinteger(L, 2);

    if (strcmp(slot, "primary") != 0 && strcmp(slot, "muted") != 0) {
        return luaL_error(L, "plugin.set_text_color: unknown slot '%s' (expected \"primary\" or \"muted\")", slot);
    }

    gui_plugin_set_text_color(slot, (uint32_t) rgb);
    return 0;
}

static void get_opt_color_field(lua_State * L, int idx, const char * field, bool * out_has, uint32_t * out_value) {
    lua_getfield(L, idx, field);
    if (!lua_isnil(L, -1)) {
        *out_has = true;
        *out_value = (uint32_t) luaL_checkinteger(L, -1);
    }
    lua_pop(L, 1);
}

static void get_opt_bool_field(lua_State * L, int idx, const char * field, bool * out_has, bool * out_value) {
    lua_getfield(L, idx, field);
    if (!lua_isnil(L, -1)) {
        *out_has = true;
        *out_value = lua_toboolean(L, -1);
    }
    lua_pop(L, 1);
}

static int32_t check_int32_field(lua_State * L, lua_Integer value, const char * fn_name, const char * field) {
    if (value < INT32_MIN || value > INT32_MAX) {
        return (int32_t) luaL_error(L, "%s: %s (%lld) is out of range", fn_name, field, (long long) value);
    }
    return (int32_t) value;
}

static int l_plugin_set_home_layout(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);

    home_layout_config_t config;
    memset(&config, 0, sizeof(config));
    config.configured = true;

    lua_Unsigned raw_n = lua_rawlen(L, 1);
    if (raw_n > (lua_Unsigned) HOME_LAYOUT_MAX_TILES) {
        return luaL_error(L, "plugin.set_home_layout: tiles has %lld entries, more than the %d-tile limit",
                           (long long) raw_n, HOME_LAYOUT_MAX_TILES);
    }
    int n = (int) raw_n;
    for (int i = 0; i < n; i++) {
        lua_rawgeti(L, 1, i + 1);
        if (!lua_istable(L, -1)) {
            return luaL_error(L, "plugin.set_home_layout: tile %d must be a table", i + 1);
        }

        lua_getfield(L, -1, "key");
        const char * key = lua_tostring(L, -1);
        if (!key || key[0] == '\0') {
            return luaL_error(L, "plugin.set_home_layout: tile %d has a missing or empty key", i + 1);
        }
        if (strlen(key) >= sizeof(config.tiles[0].key)) {
            return luaL_error(L, "plugin.set_home_layout: tile %d's key '%s' is too long", i + 1, key);
        }
        char key_copy[sizeof(config.tiles[0].key)];
        snprintf(key_copy, sizeof(key_copy), "%s", key);
        lua_pop(L, 1);

        int idx = -1;
        for (int t = 0; t < config.tile_count; t++) {
            if (strcmp(config.tiles[t].key, key_copy) == 0) { idx = t; break; }
        }
        if (idx < 0) {
            if (config.tile_count >= HOME_LAYOUT_MAX_TILES) {
                return luaL_error(L, "plugin.set_home_layout: too many distinct tile keys (max %d)",
                                   HOME_LAYOUT_MAX_TILES);
            }
            idx = config.tile_count++;
            snprintf(config.tiles[idx].key, sizeof(config.tiles[idx].key), "%s", key_copy);
        }
        home_tile_override_t * ov = &config.tiles[idx].override;
        memset(ov, 0, sizeof(*ov));
        int row_idx = lua_gettop(L);

        get_opt_color_field(L, row_idx, "bg_color", &ov->has_bg_color, &ov->bg_color);
        get_opt_color_field(L, row_idx, "text_color", &ov->has_text_color, &ov->text_color);

        lua_getfield(L, row_idx, "radius");
        if (!lua_isnil(L, -1)) {
            lua_Integer radius = luaL_checkinteger(L, -1);
            if (radius < 0) {
                lua_pop(L, 1);
                return luaL_error(L, "plugin.set_home_layout: tile %d has a negative radius", i + 1);
            }
            ov->has_radius = true;
            ov->radius = check_int32_field(L, radius, "plugin.set_home_layout", "radius");
        }
        lua_pop(L, 1);

        lua_getfield(L, row_idx, "height");
        ov->height = check_int32_field(L, luaL_optinteger(L, -1, 0), "plugin.set_home_layout", "height");
        lua_pop(L, 1);

        lua_getfield(L, row_idx, "width");
        ov->width = check_int32_field(L, luaL_optinteger(L, -1, 0), "plugin.set_home_layout", "width");
        lua_pop(L, 1);

        lua_getfield(L, row_idx, "align");
        const char * align = lua_tostring(L, -1);
        if (align) {
            if (strcmp(align, "left") != 0 && strcmp(align, "center") != 0 && strcmp(align, "right") != 0) {
                lua_pop(L, 1);
                return luaL_error(L, "plugin.set_home_layout: tile %d has an unknown align '%s' "
                                   "(expected \"left\", \"center\", or \"right\")", i + 1, align);
            }
            snprintf(ov->align, sizeof(ov->align), "%s", align);
        }
        lua_pop(L, 1);

        get_opt_bool_field(L, row_idx, "accessory", &ov->has_accessory, &ov->accessory);
        get_opt_bool_field(L, row_idx, "icon", &ov->has_icon, &ov->icon);

        lua_getfield(L, row_idx, "text_size");
        const char * text_size = lua_tostring(L, -1);
        if (text_size) {
            if (!is_valid_text_size(text_size)) {
                lua_pop(L, 1);
                return luaL_error(L, "plugin.set_home_layout: tile %d has an unknown text_size '%s' "
                                   "(expected \"small\", \"medium\", \"large\", or \"mono\")", i + 1, text_size);
            }
            snprintf(ov->text_size, sizeof(ov->text_size), "%s", text_size);
        }
        lua_pop(L, 1);

        lua_pop(L, 1);
    }

    if (lua_gettop(L) >= 2 && !lua_isnil(L, 2) && !lua_istable(L, 2)) {
        return luaL_error(L, "plugin.set_home_layout: options must be a table");
    }
    if (lua_gettop(L) >= 2 && lua_istable(L, 2)) {
        lua_getfield(L, 2, "mode");
        const char * mode = lua_tostring(L, -1);
        if (mode) {
            if (strcmp(mode, "tile") == 0) config.list_mode = false;
            else if (strcmp(mode, "list") == 0) config.list_mode = true;
            else {
                lua_pop(L, 1);
                return luaL_error(L, "plugin.set_home_layout: unknown mode '%s' (expected \"tile\" or \"list\")", mode);
            }
        }
        lua_pop(L, 1);

        lua_getfield(L, 2, "tile_gap");
        config.tile_gap = check_int32_field(L, luaL_optinteger(L, -1, 0), "plugin.set_home_layout", "tile_gap");
        lua_pop(L, 1);

        lua_getfield(L, 2, "row_gap");
        config.row_gap = check_int32_field(L, luaL_optinteger(L, -1, 0), "plugin.set_home_layout", "row_gap");
        lua_pop(L, 1);

#ifndef HOST_BUILD
        lua_getfield(L, 2, "background_image");
        if (!lua_isnil(L, -1)) {
            const char * source_path = check_plugin_external_path(L, -1, "plugin.set_home_layout");
            set_home_background_image(L, source_path, &config);
        }
        lua_pop(L, 1);
#endif

        lua_getfield(L, 2, "order");
        if (!lua_isnil(L, -1)) {
            if (!lua_istable(L, -1)) {
                return luaL_error(L, "plugin.set_home_layout: options.order must be an array table");
            }
            lua_Unsigned order_n = lua_rawlen(L, -1);
            if (order_n > (lua_Unsigned) HOME_LAYOUT_MAX_TILES) {
                return luaL_error(L, "plugin.set_home_layout: options.order has %lld entries, more than the %d-tile limit",
                                   (long long) order_n, HOME_LAYOUT_MAX_TILES);
            }
            int order_idx = lua_gettop(L);
            int order_n_int = (int) order_n;
            for (int i = 0; i < order_n_int; i++) {
                lua_rawgeti(L, order_idx, i + 1);
                const char * entry = lua_tostring(L, -1);
                if (!entry || entry[0] == '\0') {
                    return luaL_error(L, "plugin.set_home_layout: options.order entry %d must be a non-empty string",
                                       i + 1);
                }
                if (strlen(entry) >= sizeof(config.order[0])) {
                    return luaL_error(L, "plugin.set_home_layout: options.order entry %d ('%s') is too long",
                                       i + 1, entry);
                }
                for (int j = 0; j < i; j++) {
                    if (strcmp(config.order[j], entry) == 0) {
                        return luaL_error(L, "plugin.set_home_layout: options.order has a duplicate entry '%s'", entry);
                    }
                }
                snprintf(config.order[i], sizeof(config.order[i]), "%s", entry);
                lua_pop(L, 1);
            }
            config.order_count = order_n_int;
        }
        lua_pop(L, 1);

        if (!config.list_mode && config.order_count > 6) {
            return luaL_error(L, "plugin.set_home_layout: tile mode supports at most 6 tiles (got %d in "
                               "options.order) -- use { mode = \"list\" } for more", config.order_count);
        }
    }

    gui_plugin_set_home_layout(&config);
    return 0;
}

static void parse_launcher_menu_layout(lua_State * L, int idx, const char * menu,
                                       launcher_menu_layout_t * out) {
    idx = lua_absindex(L, idx);
    lua_getfield(L, idx, "mode");
    const char * mode = luaL_optstring(L, -1, "tile");
    if (strcmp(mode, "tile") != 0 && strcmp(mode, "list") != 0)
        luaL_error(L, "plugin.set_launcher_layout: %s.mode must be \"tile\" or \"list\"", menu);
    out->list_mode = strcmp(mode, "list") == 0;
    lua_pop(L, 1);

    lua_getfield(L, idx, "row_gap");
    out->row_gap = check_int32_field(L, luaL_optinteger(L, -1, 0),
                                     "plugin.set_launcher_layout", "row_gap");
    lua_pop(L, 1);
    lua_getfield(L, idx, "height");
    out->height = check_int32_field(L, luaL_optinteger(L, -1, 0),
                                    "plugin.set_launcher_layout", "height");
    lua_pop(L, 1);
    lua_getfield(L, idx, "width");
    out->width = check_int32_field(L, luaL_optinteger(L, -1, 0),
                                   "plugin.set_launcher_layout", "width");
    lua_pop(L, 1);

    get_opt_color_field(L, idx, "bg_color", &out->has_bg_color, &out->bg_color);
    get_opt_color_field(L, idx, "text_color", &out->has_text_color, &out->text_color);
    lua_getfield(L, idx, "radius");
    if (!lua_isnil(L, -1)) {
        lua_Integer radius = luaL_checkinteger(L, -1);
        if (radius < 0) luaL_error(L, "plugin.set_launcher_layout: %s.radius cannot be negative", menu);
        out->has_radius = true;
        out->radius = check_int32_field(L, radius, "plugin.set_launcher_layout", "radius");
    }
    lua_pop(L, 1);

    lua_getfield(L, idx, "align");
    const char * align = lua_tostring(L, -1);
    if (align) {
        if (strcmp(align, "left") != 0 && strcmp(align, "center") != 0 && strcmp(align, "right") != 0)
            luaL_error(L, "plugin.set_launcher_layout: %s.align must be left, center, or right", menu);
        snprintf(out->align, sizeof(out->align), "%s", align);
    }
    lua_pop(L, 1);
    lua_getfield(L, idx, "text_size");
    const char * text_size = lua_tostring(L, -1);
    if (text_size) {
        if (!is_valid_text_size(text_size))
            luaL_error(L, "plugin.set_launcher_layout: %s.text_size is invalid", menu);
        snprintf(out->text_size, sizeof(out->text_size), "%s", text_size);
    }
    lua_pop(L, 1);
    get_opt_bool_field(L, idx, "accessory", &out->has_accessory, &out->accessory);
    get_opt_bool_field(L, idx, "icon", &out->has_icon, &out->icon);
}

static int l_plugin_set_launcher_layout(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);
    launcher_layout_config_t config;
    memset(&config, 0, sizeof(config));
    const char * names[] = { "music", "stream_media", "wireless" };
    launcher_menu_layout_t * menus[] = { &config.music, &config.stream_media, &config.wireless };
    for (int i = 0; i < 3; i++) {
        lua_getfield(L, 1, names[i]);
        if (!lua_isnil(L, -1)) {
            if (!lua_istable(L, -1))
                return luaL_error(L, "plugin.set_launcher_layout: %s must be a table", names[i]);
            parse_launcher_menu_layout(L, -1, names[i], menus[i]);
        }
        lua_pop(L, 1);
    }
    gui_plugin_set_launcher_layout(&config);
    return 0;
}

static int l_plugin_reload_ui(lua_State * L) {
    (void) L;
    gui_reload_request();
    return 0;
}

static int l_plugin_refresh_theme(lua_State * L) {
    (void) L;
    gui_theme_refresh_request();
    return 0;
}

static int l_plugin_eq_load_profile(lua_State * L) {
    const char * path = check_plugin_external_path(L, 1, "plugin.eq_load_profile");
    bool ok = peq_load_from_path(path);
    if (ok) peq_save();
    lua_pushboolean(L, ok);
    return 1;
}

static int l_plugin_eq_save_profile(lua_State * L) {
    const char * path = check_plugin_external_path(L, 1, "plugin.eq_save_profile");
    lua_pushboolean(L, peq_save_to_path(path));
    return 1;
}

static int l_plugin_eq_reset(lua_State * L) {
    (void) L;
    peq_reset_to_defaults();
    peq_save();
    return 0;
}

static int l_plugin_eq_set_bypass(lua_State * L) {
    bool enabled = lua_toboolean(L, 1);
    peq_set_bypass(enabled);
    peq_save();
    return 0;
}

static int l_plugin_eq_set_preamp(lua_State * L) {
    double db = luaL_checknumber(L, 1);
    peq_set_preamp_db(db);
    peq_save();
    return 0;
}

static int check_eq_band_index(lua_State * L, int arg) {
    lua_Integer index = luaL_checkinteger(L, arg);
    if (index < 1 || index > PEQ_NUM_BANDS) {
        luaL_error(L, "band index %d out of range (expected 1..%d)", (int) index, PEQ_NUM_BANDS);
    }
    return (int) index - 1;
}

static int l_plugin_eq_set_band(lua_State * L) {
    int index = check_eq_band_index(L, 1);
    double freq_hz = luaL_checknumber(L, 2);
    double gain_db = luaL_checknumber(L, 3);
    double q = luaL_checknumber(L, 4);
    peq_set_band(index, freq_hz, gain_db, q);
    peq_save();
    return 0;
}

static int l_plugin_eq_set_band_type(lua_State * L) {
    int index = check_eq_band_index(L, 1);
    const char * type = luaL_checkstring(L, 2);

    peq_band_type_t t;
    if (strcmp(type, "peaking") == 0) t = PEQ_TYPE_PEAKING;
    else if (strcmp(type, "low_shelf") == 0) t = PEQ_TYPE_LOW_SHELF;
    else if (strcmp(type, "high_shelf") == 0) t = PEQ_TYPE_HIGH_SHELF;
    else return luaL_error(L, "plugin.eq_set_band_type: unknown type '%s' (expected \"peaking\", \"low_shelf\", or \"high_shelf\")", type);

    peq_set_band_type(index, t);
    peq_save();
    return 0;
}

static int l_plugin_eq_set_band_enabled(lua_State * L) {
    int index = check_eq_band_index(L, 1);
    bool enabled = lua_toboolean(L, 2);
    peq_set_band_enabled(index, enabled);
    peq_save();
    return 0;
}

static int l_plugin_set_gain(lua_State * L) {
    const char * mode = luaL_checkstring(L, 1);
    if (strcmp(mode, "low") == 0) {
        audio_set_gain_mode(AUDIO_GAIN_LOW);
    } else if (strcmp(mode, "high") == 0) {
        audio_set_gain_mode(AUDIO_GAIN_HIGH);
    } else {
        return luaL_error(L, "plugin.set_gain: expected \"low\" or \"high\"");
    }
    return 0;
}

static int l_plugin_get_gain(lua_State * L) {
    switch (audio_get_gain_mode()) {
        case AUDIO_GAIN_LOW: lua_pushstring(L, "low"); break;
        case AUDIO_GAIN_HIGH: lua_pushstring(L, "high"); break;
        default: lua_pushnil(L); break;
    }
    return 1;
}

static int l_plugin_toggle_pause(lua_State * L) {
    (void) L;
    gui_plugin_toggle_pause();
    return 0;
}

static int l_plugin_stop(lua_State * L) {
    (void) L;
    gui_plugin_stop();
    return 0;
}

static int l_plugin_next_track(lua_State * L) {
    (void) L;
    gui_plugin_next_track();
    return 0;
}

static int l_plugin_prev_track(lua_State * L) {
    (void) L;
    gui_plugin_prev_track();
    return 0;
}

static int l_plugin_seek(lua_State * L) {
    double seconds = luaL_checknumber(L, 1);
    gui_plugin_seek(seconds);
    return 0;
}

static int l_plugin_set_volume(lua_State * L) {
    lua_Integer percent = luaL_checkinteger(L, 1);
    gui_plugin_set_volume((int) percent);
    return 0;
}

static int l_plugin_is_playing(lua_State * L) {
    lua_pushboolean(L, gui_plugin_is_playing());
    return 1;
}

static int l_plugin_is_paused(lua_State * L) {
    lua_pushboolean(L, gui_plugin_is_paused());
    return 1;
}

static int l_plugin_get_position(lua_State * L) {
    lua_pushnumber(L, gui_plugin_get_position_seconds());
    return 1;
}

static int l_plugin_get_duration(lua_State * L) {
    lua_pushnumber(L, gui_plugin_get_duration_seconds());
    return 1;
}

static int l_plugin_http_get(lua_State * L) {
    const char * url = luaL_checkstring(L, 1);
    bool verify_tls = lua_gettop(L) >= 2 ? lua_toboolean(L, 2) : true;

    int status = 0;
    uint8_t * body = NULL;
    size_t body_size = 0;
    bool ok = http_get_to_buffer(url, verify_tls, &status, &body, &body_size);
    if (!ok) {
        lua_pushnil(L);
        lua_pushstring(L, "network error");
        return 2;
    }

    lua_pushinteger(L, status);
    lua_pushlstring(L, (const char *) body, body_size);
    free(body);
    return 2;
}

static int l_plugin_http_post(lua_State * L) {
    const char * url = luaL_checkstring(L, 1);
    size_t body_len = 0;
    const char * body = luaL_checklstring(L, 2, &body_len);
    const char * content_type =
        (lua_gettop(L) >= 3 && !lua_isnil(L, 3)) ? luaL_checkstring(L, 3) : "application/x-www-form-urlencoded";
    bool verify_tls = lua_gettop(L) >= 4 ? lua_toboolean(L, 4) : true;

    int status = 0;
    uint8_t * resp_body = NULL;
    size_t resp_body_size = 0;
    bool ok = http_post_to_buffer(url, verify_tls, content_type, (const uint8_t *) body, body_len, &status,
                                   &resp_body, &resp_body_size);
    if (!ok) {
        lua_pushnil(L);
        lua_pushstring(L, "network error");
        return 2;
    }

    lua_pushinteger(L, status);
    lua_pushlstring(L, (const char *) resp_body, resp_body_size);
    free(resp_body);
    return 2;
}

typedef struct {
    bool active;
    atomic_bool done;
    http_cancel_token_t cancel;
    uint16_t generation;
    pthread_t thread;
    lua_State * L;
    int callback_ref;
    bool is_download;
    char dest_path[PATH_MAX];
    bool verify_tls;

    char url[2048];
    http_method_t method;
    http_header_t headers[HTTP_MAX_HEADERS];
    int header_count;
    uint8_t * request_body;
    size_t request_body_size;
    char content_type[128];
    size_t max_response_size;
    uint32_t connect_timeout_ms;
    uint32_t read_timeout_ms;
    uint32_t total_timeout_ms;
    int redirect_limit;

    bool ok;
    int status;
    uint8_t * response_body;
    size_t response_body_size;
    http_header_t response_headers[HTTP_MAX_HEADERS];
    int response_header_count;
    const char * response_error;
} plugin_async_http_t;

static plugin_async_http_t plugin_async_http[PLUGIN_MAX_ASYNC_HTTP];

static bool plugin_async_download_progress(uint64_t downloaded, uint64_t total, void * user_data) {
    (void) downloaded;
    (void) total;
    plugin_async_http_t * req = (plugin_async_http_t *) user_data;
    return !http_cancel_token_is_cancelled(&req->cancel);
}

static void plugin_dedupe_headers_case_insensitive(http_header_t * headers, int * count) {
    int out = 0;
    for (int i = 0; i < *count; i++) {
        bool superseded = false;
        for (int j = i + 1; j < *count; j++) {
            if (strcasecmp(headers[i].name, headers[j].name) == 0) { superseded = true; break; }
        }
        if (superseded) continue;
        if (out != i) headers[out] = headers[i];
        out++;
    }
    *count = out;
}

static void * plugin_async_http_thread_func(void * arg) {
    plugin_async_http_t * req = (plugin_async_http_t *) arg;
    if (req->is_download) {
        char temp_path[PATH_MAX];
        int n;
        if (plugin_storage_path_is_reserved(req->dest_path)) {
            n = -1;
        } else {
            n = snprintf(temp_path, sizeof(temp_path), "%s.part.XXXXXX", req->dest_path);
        }
        if (n <= 0 || (size_t) n >= sizeof(temp_path)) {
            req->ok = false;
        } else {
            int fd = mkstemp(temp_path);
            if (fd < 0) {
                req->ok = false;
            } else {
                close(fd);
                req->ok = http_get_to_file_bounded(req->url, req->verify_tls, temp_path, 0,
                                                    plugin_async_download_progress, req);
                bool cancelled = http_cancel_token_is_cancelled(&req->cancel);
                if (req->ok && !cancelled) {
                    req->ok = rename(temp_path, req->dest_path) == 0;
                }
                if (!req->ok || cancelled) remove(temp_path);
            }
        }
    } else {
        http_request_t hreq;
        memset(&hreq, 0, sizeof(hreq));
        snprintf(hreq.url, sizeof(hreq.url), "%s", req->url);
        hreq.method = req->method;
        memcpy(hreq.headers, req->headers, sizeof(hreq.headers));
        hreq.header_count = req->header_count;
        bool method_has_body = req->method == HTTP_METHOD_POST || req->method == HTTP_METHOD_PUT ||
                                req->method == HTTP_METHOD_PATCH;
        hreq.body = method_has_body ? req->request_body : NULL;
        hreq.body_len = method_has_body ? req->request_body_size : 0;
        hreq.content_type = (method_has_body && req->content_type[0]) ? req->content_type : NULL;
        hreq.verify_tls = req->verify_tls;
        hreq.connect_timeout_ms = req->connect_timeout_ms;
        hreq.read_timeout_ms = req->read_timeout_ms;
        hreq.total_timeout_ms = req->total_timeout_ms;
        hreq.max_response_bytes = req->max_response_size;
        hreq.redirect_limit = req->redirect_limit;

        http_response_t hresp;
        req->ok = http_request_ex(&hreq, &req->cancel, &hresp);
        req->status = hresp.status;
        req->response_body = hresp.body;
        req->response_body_size = hresp.body_len;
        memcpy(req->response_headers, hresp.headers, sizeof(req->response_headers));
        req->response_header_count = hresp.header_count;
        plugin_dedupe_headers_case_insensitive(req->response_headers, &req->response_header_count);
        req->response_error = hresp.error;
    }
    free(req->request_body);
    req->request_body = NULL;
    req->request_body_size = 0;
    atomic_store(&req->done, true);
    return NULL;
}

static int l_plugin_http_request(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);
    luaL_checktype(L, 2, LUA_TFUNCTION);

    int slot = -1;
    for (int i = 0; i < PLUGIN_MAX_ASYNC_HTTP; i++) {
        if (!plugin_async_http[i].active) { slot = i; break; }
    }
    if (slot < 0) {
        lua_pushnil(L);
        lua_pushstring(L, "too many active HTTP requests");
        return 2;
    }

    lua_getfield(L, 1, "url");
    const char * url = luaL_checkstring(L, -1);
    if (strlen(url) >= sizeof(plugin_async_http[slot].url)) {
        return luaL_error(L, "plugin.http_request: URL is too long");
    }
    lua_pop(L, 1);

    lua_getfield(L, 1, "method");
    const char * method_str = luaL_optstring(L, -1, "GET");
    http_method_t method;
    if (strcasecmp(method_str, "GET") == 0) method = HTTP_METHOD_GET;
    else if (strcasecmp(method_str, "POST") == 0) method = HTTP_METHOD_POST;
    else if (strcasecmp(method_str, "PUT") == 0) method = HTTP_METHOD_PUT;
    else if (strcasecmp(method_str, "PATCH") == 0) method = HTTP_METHOD_PATCH;
    else if (strcasecmp(method_str, "DELETE") == 0) method = HTTP_METHOD_DELETE;
    else if (strcasecmp(method_str, "HEAD") == 0) method = HTTP_METHOD_HEAD;
    else return luaL_error(L, "plugin.http_request: unknown method '%s'", method_str);
    lua_pop(L, 1);

    lua_getfield(L, 1, "body");
    size_t body_size = 0;
    const char * body = lua_isnil(L, -1) ? NULL : luaL_checklstring(L, -1, &body_size);
    if (body_size > PLUGIN_ASYNC_HTTP_MAX_REQUEST) {
        return luaL_error(L, "plugin.http_request: request body exceeds %u bytes", PLUGIN_ASYNC_HTTP_MAX_REQUEST);
    }
    uint8_t * body_copy = NULL;
    if (body_size > 0) {
        body_copy = malloc(body_size);
        if (!body_copy) return luaL_error(L, "plugin.http_request: out of memory");
        memcpy(body_copy, body, body_size);
    }
    lua_pop(L, 1);

    lua_getfield(L, 1, "content_type");
    const char * content_type = luaL_optstring(L, -1, "application/x-www-form-urlencoded");
    if (strlen(content_type) >= sizeof(plugin_async_http[slot].content_type)) {
        free(body_copy);
        return luaL_error(L, "plugin.http_request: content_type is too long");
    }
    lua_pop(L, 1);

    http_header_t headers[HTTP_MAX_HEADERS];
    int header_count = 0;
    lua_getfield(L, 1, "headers");
    if (lua_istable(L, -1)) {
        lua_pushnil(L);
        while (header_count < HTTP_MAX_HEADERS && lua_next(L, -2) != 0) {
            if (lua_type(L, -2) == LUA_TSTRING) {
                size_t name_len = 0, value_len = 0;
                const char * name = lua_tolstring(L, -2, &name_len);
                const char * value = lua_tolstring(L, -1, &value_len);
                if (name && value) {
                    if (name_len >= sizeof(headers[header_count].name) || value_len >= sizeof(headers[header_count].value)) {
                        free(body_copy);
                        return luaL_error(L, "plugin.http_request: header '%s' name/value exceeds %d/%d bytes",
                                          name, (int) sizeof(headers[0].name) - 1, (int) sizeof(headers[0].value) - 1);
                    }
                    memcpy(headers[header_count].name, name, name_len + 1);
                    memcpy(headers[header_count].value, value, value_len + 1);
                    header_count++;
                }
            }
            lua_pop(L, 1);
        }
    }
    lua_pop(L, 1);

    lua_getfield(L, 1, "verify_tls");
    bool verify_tls = lua_isnil(L, -1) ? true : lua_toboolean(L, -1);
    lua_pop(L, 1);
    lua_getfield(L, 1, "max_response_bytes");
    lua_Integer requested_max = luaL_optinteger(L, -1, PLUGIN_ASYNC_HTTP_DEFAULT_MAX);
    lua_pop(L, 1);
    if (requested_max < 1 || requested_max > PLUGIN_ASYNC_HTTP_MAX_RESPONSE) {
        free(body_copy);
        return luaL_error(L, "plugin.http_request: max_response_bytes must be 1..%u",
                          PLUGIN_ASYNC_HTTP_MAX_RESPONSE);
    }

    lua_getfield(L, 1, "connect_timeout_ms");
    lua_Integer connect_timeout_ms = luaL_optinteger(L, -1, 0);
    lua_pop(L, 1);
    lua_getfield(L, 1, "read_timeout_ms");
    lua_Integer read_timeout_ms = luaL_optinteger(L, -1, 0);
    lua_pop(L, 1);
    lua_getfield(L, 1, "total_timeout_ms");
    lua_Integer total_timeout_ms = luaL_optinteger(L, -1, 0);
    lua_pop(L, 1);
    lua_getfield(L, 1, "redirect_limit");
    lua_Integer redirect_limit = luaL_optinteger(L, -1, 0);
    lua_pop(L, 1);
    if (connect_timeout_ms < 0 || read_timeout_ms < 0 || total_timeout_ms < 0 || redirect_limit < 0) {
        free(body_copy);
        return luaL_error(L, "plugin.http_request: timeout/redirect_limit fields must not be negative");
    }

#define PLUGIN_HTTP_MAX_TIMEOUT_MS (5 * 60 * 1000)
#define PLUGIN_HTTP_MAX_REDIRECTS 10
    if (connect_timeout_ms > PLUGIN_HTTP_MAX_TIMEOUT_MS || read_timeout_ms > PLUGIN_HTTP_MAX_TIMEOUT_MS ||
        total_timeout_ms > PLUGIN_HTTP_MAX_TIMEOUT_MS) {
        free(body_copy);
        return luaL_error(L, "plugin.http_request: connect_timeout_ms/read_timeout_ms/total_timeout_ms must not exceed %d",
                          PLUGIN_HTTP_MAX_TIMEOUT_MS);
    }
    if (redirect_limit > PLUGIN_HTTP_MAX_REDIRECTS) {
        free(body_copy);
        return luaL_error(L, "plugin.http_request: redirect_limit must not exceed %d", PLUGIN_HTTP_MAX_REDIRECTS);
    }

    plugin_async_http_t * req = &plugin_async_http[slot];
    uint16_t generation = (uint16_t) (req->generation + 1);
    if (generation == 0) generation = 1;
    memset(req, 0, sizeof(*req));
    atomic_init(&req->done, false);
    http_cancel_token_init(&req->cancel);
    req->generation = generation;
    req->active = true;
    req->L = L;
    req->method = method;
    memcpy(req->headers, headers, sizeof(req->headers));
    req->header_count = header_count;
    req->verify_tls = verify_tls;
    req->request_body = body_copy;
    req->request_body_size = body_size;
    req->max_response_size = (size_t) requested_max;
    req->connect_timeout_ms = (uint32_t) connect_timeout_ms;
    req->read_timeout_ms = (uint32_t) read_timeout_ms;
    req->total_timeout_ms = (uint32_t) total_timeout_ms;
    req->redirect_limit = (int) redirect_limit;
    snprintf(req->url, sizeof(req->url), "%s", url);
    snprintf(req->content_type, sizeof(req->content_type), "%s", content_type);
    lua_pushvalue(L, 2);
    req->callback_ref = luaL_ref(L, LUA_REGISTRYINDEX);

    if (pthread_create(&req->thread, NULL, plugin_async_http_thread_func, req) != 0) {
        luaL_unref(L, LUA_REGISTRYINDEX, req->callback_ref);
        free(req->request_body);
        req->request_body = NULL;
        req->active = false;
        http_cancel_token_destroy(&req->cancel);
        lua_pushnil(L);
        lua_pushstring(L, "could not start HTTP worker");
        return 2;
    }

    int handle = ((int) generation << 8) | (slot + 1);
    lua_pushinteger(L, handle);
    return 1;
}

static int l_plugin_download_file_async(lua_State * L) {
    const char * url = luaL_checkstring(L, 1);
    const char * dest_path = luaL_checkstring(L, 2);
    int callback_index = lua_isfunction(L, 3) ? 3 : 4;
    bool verify_tls = callback_index == 3 ? true : lua_toboolean(L, 3);
    luaL_checktype(L, callback_index, LUA_TFUNCTION);

    if (strlen(url) >= sizeof(plugin_async_http[0].url))
        return luaL_error(L, "plugin.download_file_async: URL is too long");
    if (dest_path[0] == '\0' || strlen(dest_path) >= sizeof(plugin_async_http[0].dest_path) - 12)
        return luaL_error(L, "plugin.download_file_async: destination path is invalid or too long");
    if (plugin_storage_path_is_reserved(dest_path))
        return luaL_error(L, "plugin.download_file_async: path is reserved for plugin.storage/plugin.secrets");

    int slot = -1;
    for (int i = 0; i < PLUGIN_MAX_ASYNC_HTTP; i++) {
        if (!plugin_async_http[i].active) { slot = i; break; }
    }
    if (slot < 0) {
        lua_pushnil(L);
        lua_pushstring(L, "too many active HTTP requests");
        return 2;
    }

    plugin_async_http_t * req = &plugin_async_http[slot];
    uint16_t generation = (uint16_t) (req->generation + 1);
    if (generation == 0) generation = 1;
    memset(req, 0, sizeof(*req));
    atomic_init(&req->done, false);
    http_cancel_token_init(&req->cancel);
    req->generation = generation;
    req->active = true;
    req->L = L;
    req->is_download = true;
    req->verify_tls = verify_tls;
    snprintf(req->url, sizeof(req->url), "%s", url);
    snprintf(req->dest_path, sizeof(req->dest_path), "%s", dest_path);
    lua_pushvalue(L, callback_index);
    req->callback_ref = luaL_ref(L, LUA_REGISTRYINDEX);

    if (pthread_create(&req->thread, NULL, plugin_async_http_thread_func, req) != 0) {
        luaL_unref(L, LUA_REGISTRYINDEX, req->callback_ref);
        req->active = false;
        http_cancel_token_destroy(&req->cancel);
        lua_pushnil(L);
        lua_pushstring(L, "could not start HTTP worker");
        return 2;
    }

    lua_pushinteger(L, ((int) generation << 8) | (slot + 1));
    return 1;
}

static int l_plugin_cancel(lua_State * L) {
    int handle = (int) luaL_checkinteger(L, 1);
    int slot = (handle & 0xFF) - 1;
    uint16_t generation = (uint16_t) ((unsigned int) handle >> 8);
    bool cancelled = false;
    if (slot >= 0 && slot < PLUGIN_MAX_ASYNC_HTTP) {
        plugin_async_http_t * req = &plugin_async_http[slot];
        if (req->active && req->generation == generation) {
            http_cancel_token_cancel(&req->cancel);
            cancelled = true;
        }
    }
    lua_pushboolean(L, cancelled);
    return 1;
}

static int l_plugin_md5(lua_State * L) {
    size_t len = 0;
    const char * data = luaL_checklstring(L, 1, &len);

    unsigned char digest[16];
    mbedtls_md5((const unsigned char *) data, len, digest);

    char hex[33];
    for (int i = 0; i < 16; i++) snprintf(hex + i * 2, 3, "%02x", digest[i]);
    lua_pushstring(L, hex);
    return 1;
}

static lua_State * pending_text_input_L = NULL;
static int pending_text_input_ref = LUA_NOREF;

static int l_plugin_show_text_input(lua_State * L) {
    const char * title = luaL_checkstring(L, 1);
    const char * initial_text = (lua_gettop(L) >= 2 && !lua_isnil(L, 2)) ? luaL_checkstring(L, 2) : NULL;
    bool is_password = lua_toboolean(L, 3);
    luaL_checktype(L, 4, LUA_TFUNCTION);

    if (pending_text_input_L && pending_text_input_ref != LUA_NOREF) {
        lua_pushboolean(L, false);
        lua_pushstring(L, "text input busy");
        return 2;
    }
    lua_pushvalue(L, 4);
    pending_text_input_ref = luaL_ref(L, LUA_REGISTRYINDEX);
    pending_text_input_L = L;

    gui_plugin_show_text_input(title, initial_text, is_password);
    lua_pushboolean(L, true);
    return 1;
}

static int l_plugin_get_now_playing(lua_State * L) {
    char title[128], artist[128], album[128];
    double duration_seconds = 0.0;
    if (!gui_plugin_get_now_playing(title, sizeof(title), artist, sizeof(artist), album, sizeof(album),
                                     &duration_seconds)) {
        lua_pushnil(L);
        return 1;
    }

    lua_pushstring(L, title);
    lua_pushstring(L, artist);
    lua_pushstring(L, album);
    lua_pushnumber(L, duration_seconds);
    return 4;
}

static int l_plugin_get_play_mode(lua_State * L) {
    lua_pushstring(L, gui_plugin_get_play_mode());
    return 1;
}

static int l_plugin_get_current_track_path(lua_State * L) {
    const char * path = gui_plugin_get_current_track_path();
    if (!path) {
        lua_pushnil(L);
        return 1;
    }
    lua_pushstring(L, path);
    return 1;
}

static int push_string_array_result(lua_State * L, char ** items, int count) {
    if (!items || count <= 0) {
        lua_pushnil(L);
        return 1;
    }
    lua_newtable(L);
    for (int i = 0; i < count; i++) {
        lua_pushstring(L, items[i]);
        lua_rawseti(L, -2, i + 1);
    }
    gui_plugin_free_string_array(items, count);
    return 1;
}

static int l_plugin_get_artist_albums(lua_State * L) {
    const char * artist = luaL_checkstring(L, 1);
    int count = 0;
    char ** albums = gui_plugin_get_artist_albums(artist, &count);
    return push_string_array_result(L, albums, count);
}

static int l_plugin_get_album_tracks(lua_State * L) {
    const char * artist = luaL_checkstring(L, 1);
    const char * album = luaL_checkstring(L, 2);
    int count = 0;
    char ** tracks = gui_plugin_get_album_tracks(artist, album, &count);
    return push_string_array_result(L, tracks, count);
}

static int l_plugin_get_next_album_tracks(lua_State * L) {
    const char * artist = luaL_checkstring(L, 1);
    const char * current_album = luaL_checkstring(L, 2);
    int count = 0;
    char ** tracks = gui_plugin_get_next_album_tracks(artist, current_album, &count);
    return push_string_array_result(L, tracks, count);
}

static bool plugin_playlist_name_valid(const char * name) {
    if (!name || !name[0] || strlen(name) > 200 || strcmp(name, ".") == 0 || strcmp(name, "..") == 0) return false;
    for (const unsigned char * p = (const unsigned char *) name; *p; p++)
        if (*p < 0x20 || *p == 0x7f || *p == '/' || *p == '\\') return false;
    return true;
}

static bool plugin_playlist_path_valid(const char * path) {
    if (!path || plugin_storage_path_is_reserved(path)) return false;
    char root_real[PATH_MAX], path_real[PATH_MAX];
    if (!realpath(PLAYLISTS_DIR, root_real) || !realpath(path, path_real)) return false;
    size_t root_len = strlen(root_real);
    if (strncmp(path_real, root_real, root_len) != 0 || path_real[root_len] != '/') return false;
    const char * base = path_real + root_len + 1;
    if (!base[0] || strchr(base, '/')) return false;
    const char * ext = strrchr(base, '.');
    if (!ext || (strcasecmp(ext, ".m3u") != 0 && strcasecmp(ext, ".m3u8") != 0)) return false;
    struct stat st;
    return stat(path_real, &st) == 0 && S_ISREG(st.st_mode);
}

static bool plugin_song_path_valid(const char * path) {
    if (!path || plugin_storage_path_is_reserved(path)) return false;
    char root_real[PATH_MAX], path_real[PATH_MAX];
    if (!realpath(MUSIC_ROOT_DIR, root_real) || !realpath(path, path_real)) return false;
    size_t root_len = strlen(root_real);
    if (strncmp(path_real, root_real, root_len) != 0 || path_real[root_len] != '/') return false;
    struct stat st;
    return stat(path_real, &st) == 0 && S_ISREG(st.st_mode);
}

static int push_plugin_error(lua_State * L, const char * message) {
    lua_pushnil(L);
    lua_pushstring(L, message);
    return 2;
}

static int l_plugin_playlist_list(lua_State * L) {
    char ** paths = NULL;
    int count = 0;
    if (!playlist_files_scan(PLAYLISTS_DIR, &paths, &count)) {
        lua_pushnil(L);
        return 1;
    }
    return push_string_array_result(L, paths, count);
}

static int l_plugin_playlist_read(lua_State * L) {
    const char * m3u_path = luaL_checkstring(L, 1);
    if (!plugin_playlist_path_valid(m3u_path)) return push_plugin_error(L, "playlist path must be an existing .m3u file in the SD Playlists folder");
    char ** paths = NULL;
    int count = 0;
    if (!playlist_files_read(m3u_path, &paths, &count)) {
        lua_pushnil(L);
        return 1;
    }
    return push_string_array_result(L, paths, count);
}

static int l_plugin_playlist_create(lua_State * L) {
    const char * name = luaL_checkstring(L, 1);
    const char * song_path = luaL_checkstring(L, 2);

    if (!plugin_playlist_name_valid(name)) return push_plugin_error(L, "invalid playlist name");
    if (!plugin_song_path_valid(song_path)) return push_plugin_error(L, "song path must be an existing file on the SD card");

    char created_path[512];
    if (!playlist_files_create(PLAYLISTS_DIR, name, song_path, created_path, sizeof(created_path))) {
        return push_plugin_error(L, errno == EEXIST ? "playlist already exists" : "could not create playlist");
    }
    metadata_db_playlist_insert_one(created_path);
    lua_pushstring(L, created_path);
    return 1;
}

static int l_plugin_playlist_add(lua_State * L) {
    const char * m3u_path = luaL_checkstring(L, 1);
    const char * song_path = luaL_checkstring(L, 2);
    if (!plugin_playlist_path_valid(m3u_path)) return push_plugin_error(L, "invalid playlist path");
    if (!plugin_song_path_valid(song_path)) return push_plugin_error(L, "invalid song path");
    if (!playlist_files_append(m3u_path, song_path)) return push_plugin_error(L, "could not update playlist");
    lua_pushboolean(L, true);
    return 1;
}

static int l_plugin_playlist_remove(lua_State * L) {
    const char * m3u_path = luaL_checkstring(L, 1);
    const char * song_path = luaL_checkstring(L, 2);
    if (!plugin_playlist_path_valid(m3u_path)) return push_plugin_error(L, "invalid playlist path");
    if (!plugin_song_path_valid(song_path)) return push_plugin_error(L, "invalid song path");
    if (!playlist_files_remove(m3u_path, song_path)) return push_plugin_error(L, "could not update playlist");
    lua_pushboolean(L, true);
    return 1;
}

static int l_plugin_playlist_delete(lua_State * L) {
    const char * m3u_path = luaL_checkstring(L, 1);
    if (!plugin_playlist_path_valid(m3u_path)) return push_plugin_error(L, "invalid playlist path");
    bool ok = playlist_files_delete(m3u_path);
    if (ok) metadata_db_playlist_delete_one(m3u_path);
    lua_pushboolean(L, ok);
    return 1;
}

static void push_song_row(lua_State * L, const song_row_t * row) {
    char display_title[128];
    metadata_db_song_display_title(row, display_title, sizeof(display_title));

    lua_newtable(L);
    lua_pushinteger(L, (lua_Integer) row->id); lua_setfield(L, -2, "id");
    lua_pushstring(L, row->path); lua_setfield(L, -2, "path");
    lua_pushstring(L, display_title); lua_setfield(L, -2, "title");
    lua_pushstring(L, row->tags.artist); lua_setfield(L, -2, "artist");
    lua_pushstring(L, row->tags.album); lua_setfield(L, -2, "album");
    lua_pushstring(L, row->tags.album_artist); lua_setfield(L, -2, "album_artist");
}

static void push_group_row(lua_State * L, const group_row_t * row) {
    lua_newtable(L);
    lua_pushstring(L, row->name); lua_setfield(L, -2, "name");
    lua_pushinteger(L, row->song_count); lua_setfield(L, -2, "count");
    lua_pushinteger(L, (lua_Integer) row->first_song_id); lua_setfield(L, -2, "first_song_id");
    lua_pushstring(L, row->album_artist); lua_setfield(L, -2, "album_artist");
}

static int push_song_rows_result(lua_State * L, const song_row_t * rows, int count) {
    lua_newtable(L);
    for (int i = 0; i < count; i++) {
        push_song_row(L, &rows[i]);
        lua_rawseti(L, -2, i + 1);
    }
    return 1;
}

static int l_plugin_library_song_count(lua_State * L) {
    lua_pushinteger(L, (lua_Integer) gui_plugin_library_song_count());
    return 1;
}

static int l_plugin_library_get_songs(lua_State * L) {
    int offset = (int) luaL_optinteger(L, 1, 0);
    int limit = (int) luaL_optinteger(L, 2, GUI_PLUGIN_LIBRARY_MAX_PAGE);
    const char * query = NULL, * artist = NULL, * album_artist = NULL, * album = NULL;
    if (lua_istable(L, 3)) {
        lua_getfield(L, 3, "query"); query = lua_tostring(L, -1);
        lua_getfield(L, 3, "artist"); artist = lua_tostring(L, -1);
        lua_getfield(L, 3, "album_artist"); album_artist = lua_tostring(L, -1);
        lua_getfield(L, 3, "album"); album = lua_tostring(L, -1);
    }

    song_row_t * rows = malloc(sizeof(song_row_t) * GUI_PLUGIN_LIBRARY_MAX_PAGE);
    int64_t total = 0;
    int n = rows ? gui_plugin_library_get_songs(query, artist, album_artist, album, offset, limit, rows, &total) : 0;
    push_song_rows_result(L, rows, n);
    free(rows);
    lua_pushinteger(L, (lua_Integer) total);
    return 2;
}

static int l_plugin_library_search(lua_State * L) {
    const char * query = luaL_checkstring(L, 1);
    int limit = (int) luaL_optinteger(L, 2, GUI_PLUGIN_LIBRARY_MAX_PAGE);

    song_row_t * rows = malloc(sizeof(song_row_t) * GUI_PLUGIN_LIBRARY_MAX_PAGE);
    int n = rows ? gui_plugin_library_search(query, limit, rows) : 0;
    int result = push_song_rows_result(L, rows, n);
    free(rows);
    return result;
}

static int l_plugin_library_get_song(lua_State * L) {
    int64_t id = (int64_t) luaL_checkinteger(L, 1);
    song_row_t row;
    if (!gui_plugin_library_get_song(id, &row)) {
        lua_pushnil(L);
        return 1;
    }
    push_song_row(L, &row);
    return 1;
}

static int l_plugin_library_get_artists(lua_State * L) {
    int offset = (int) luaL_optinteger(L, 1, 0);
    int limit = (int) luaL_optinteger(L, 2, GUI_PLUGIN_LIBRARY_MAX_PAGE);

    group_row_t * rows = malloc(sizeof(group_row_t) * GUI_PLUGIN_LIBRARY_MAX_PAGE);
    int n = rows ? gui_plugin_library_get_artists(offset, limit, rows) : 0;
    lua_newtable(L);
    for (int i = 0; i < n; i++) {
        push_group_row(L, &rows[i]);
        lua_rawseti(L, -2, i + 1);
    }
    free(rows);
    return 1;
}

static int l_plugin_library_get_albums(lua_State * L) {
    int offset = (int) luaL_optinteger(L, 1, 0);
    int limit = (int) luaL_optinteger(L, 2, GUI_PLUGIN_LIBRARY_MAX_PAGE);
    const char * artist_filter = luaL_optstring(L, 3, NULL);

    group_row_t * rows = malloc(sizeof(group_row_t) * GUI_PLUGIN_LIBRARY_MAX_PAGE);
    int n = rows ? gui_plugin_library_get_albums(offset, limit, artist_filter, rows) : 0;
    lua_newtable(L);
    for (int i = 0; i < n; i++) {
        push_group_row(L, &rows[i]);
        lua_rawseti(L, -2, i + 1);
    }
    free(rows);
    return 1;
}

static int l_plugin_refresh_library(lua_State * L) {
    plugin_instance_t * inst = plugin_instance_for_state(L);
    if (!inst || !inst->defined) return luaL_error(L, "plugin.refresh_library requires plugin.define first");
    time_t now = time(NULL);
    if (inst->last_library_refresh > 0 && now >= inst->last_library_refresh && now - inst->last_library_refresh < 60) {
        lua_pushboolean(L, false); lua_pushliteral(L, "rate_limited"); return 2;
    }
    if (!gui_plugin_refresh_library()) {
        lua_pushboolean(L, false); lua_pushliteral(L, "already_running"); return 2;
    }
    inst->last_library_refresh = now;
    lua_pushboolean(L, true); lua_pushliteral(L, "started"); return 2;
}

typedef enum {
    PLUGIN_EVENT_TRACK_STARTED = 0,
    PLUGIN_EVENT_PAUSED,
    PLUGIN_EVENT_RESUMED,
    PLUGIN_EVENT_STOPPED,
    PLUGIN_EVENT_SCREEN_WOKE,
    PLUGIN_EVENT_COUNT,
} plugin_event_t;

typedef struct {
    lua_State * L;
    int ref;
} plugin_event_subscriber_t;

static plugin_event_subscriber_t plugin_event_subscribers[PLUGIN_EVENT_COUNT][PLUGIN_MAX_EVENT_SUBSCRIBERS];
static int plugin_event_subscriber_count[PLUGIN_EVENT_COUNT];

static int l_plugin_on(lua_State * L) {
    const char * event = luaL_checkstring(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION);

    plugin_event_t idx;
    if (strcmp(event, "track_started") == 0) idx = PLUGIN_EVENT_TRACK_STARTED;
    else if (strcmp(event, "paused") == 0) idx = PLUGIN_EVENT_PAUSED;
    else if (strcmp(event, "resumed") == 0) idx = PLUGIN_EVENT_RESUMED;
    else if (strcmp(event, "stopped") == 0) idx = PLUGIN_EVENT_STOPPED;
    else if (strcmp(event, "screen_woke") == 0) idx = PLUGIN_EVENT_SCREEN_WOKE;
    else return luaL_error(L, "plugin.on: unknown event '%s' (expected \"track_started\", \"paused\", \"resumed\", \"stopped\", or \"screen_woke\")", event);

    if (plugin_event_subscriber_count[idx] >= PLUGIN_MAX_EVENT_SUBSCRIBERS) {
        return luaL_error(L, "plugin.on: too many subscribers registered for \"%s\" (max %d)", event,
                           PLUGIN_MAX_EVENT_SUBSCRIBERS);
    }

    lua_pushvalue(L, 2);
    int ref = luaL_ref(L, LUA_REGISTRYINDEX);
    plugin_event_subscriber_t * sub = &plugin_event_subscribers[idx][plugin_event_subscriber_count[idx]++];
    sub->L = L;
    sub->ref = ref;
    return 0;
}

typedef struct {
    lua_State * L;
    int ref;
    bool active;
} plugin_interval_t;

static plugin_interval_t plugin_intervals[PLUGIN_MAX_INTERVALS];

static int l_plugin_set_interval(lua_State * L) {
    double seconds = luaL_checknumber(L, 1);
    luaL_checktype(L, 2, LUA_TFUNCTION);

    int slot = -1;
    for (int i = 0; i < PLUGIN_MAX_INTERVALS; i++) {
        if (!plugin_intervals[i].active) { slot = i; break; }
    }
    if (slot < 0) {
        return luaL_error(L, "plugin.set_interval: too many active intervals (max %d)", PLUGIN_MAX_INTERVALS);
    }

    uint32_t period_ms = (uint32_t) (seconds * 1000.0);
    if (period_ms < PLUGIN_INTERVAL_MIN_MS) period_ms = PLUGIN_INTERVAL_MIN_MS;

    lua_pushvalue(L, 2);
    int ref = luaL_ref(L, LUA_REGISTRYINDEX);
    plugin_intervals[slot].L = L;
    plugin_intervals[slot].ref = ref;
    plugin_intervals[slot].active = true;

    gui_plugin_set_interval(slot, period_ms);
    lua_pushinteger(L, slot + 1);
    return 1;
}

static int l_plugin_clear_interval(lua_State * L) {
    lua_Integer handle = luaL_checkinteger(L, 1);
    int slot = (int) handle - 1;
    if (slot < 0 || slot >= PLUGIN_MAX_INTERVALS || !plugin_intervals[slot].active) return 0;

    luaL_unref(plugin_intervals[slot].L, LUA_REGISTRYINDEX, plugin_intervals[slot].ref);
    plugin_intervals[slot].active = false;
    plugin_intervals[slot].L = NULL;
    gui_plugin_clear_interval(slot);
    return 0;
}

static bool plugin_id_is_valid(const char * id) {
    if (!id || !id[0]) return false;
    for (const unsigned char * p = (const unsigned char *) id; *p; p++) {
        if (!( (*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') ||
               (*p >= '0' && *p <= '9') || *p == '.' || *p == '_' || *p == '-')) return false;
    }
    return true;
}

static bool plugin_id_collides(const char * id, int exclude_slot) {
    for (int i = 0; i < plugin_instance_count; i++) {
        if (i != exclude_slot && plugin_instances[i].defined && strcmp(plugin_instances[i].id, id) == 0) return true;
    }
    return false;
}

static int l_plugin_define(lua_State * L) {
    luaL_checktype(L, 1, LUA_TTABLE);
    if (loading_plugin_slot < 0 || loading_plugin_slot >= PLUGIN_MAX_FILES ||
        plugin_instances[loading_plugin_slot].L != L) {
        return luaL_error(L, "plugin.define may only be called once during plugin loading");
    }
    plugin_instance_t * inst = &plugin_instances[loading_plugin_slot];
    if (inst->defined) return luaL_error(L, "plugin.define may only be called once");

    lua_getfield(L, 1, "id");
    const char * id = luaL_checkstring(L, -1);
    if (!plugin_id_is_valid(id) || strlen(id) >= sizeof(inst->id)) {
        return luaL_error(L, "plugin.define: id must be 1-%zu characters using letters, digits, '.', '_' or '-'",
                          sizeof(inst->id) - 1);
    }
    if (plugin_id_collides(id, loading_plugin_slot)) {
        return luaL_error(L, "plugin.define: duplicate plugin id '%s'", id);
    }
    snprintf(inst->id, sizeof(inst->id), "%s", id);
    lua_pop(L, 1);

    lua_getfield(L, 1, "name");
    const char * name = luaL_optstring(L, -1, id);
    snprintf(inst->name, sizeof(inst->name), "%s", name);
    lua_pop(L, 1);
    lua_getfield(L, 1, "version");
    const char * version = luaL_optstring(L, -1, "0");
    snprintf(inst->version, sizeof(inst->version), "%s", version);
    lua_pop(L, 1);
    lua_getfield(L, 1, "api_min");
    lua_Integer api_min = luaL_optinteger(L, -1, 1);
    lua_pop(L, 1);
    if (api_min > PLUGIN_API_VERSION) {
        return luaL_error(L, "plugin '%s' requires API %lld, player provides API %d", id,
                          (long long) api_min, PLUGIN_API_VERSION);
    }
    inst->defined = true;
    return 0;
}

static int l_plugin_api_version(lua_State * L) {
    lua_pushinteger(L, PLUGIN_API_VERSION);
    return 1;
}

static const char * const plugin_capabilities[] = {
    "ui.list", "ui.settings", "ui.row_width", "ui.text_input", "ui.toast", "ui.theme",
    "filesystem.sd", "playback.control", "playback.state", "playback.events",
    "library.artist_albums", "library.paged", "network.http.sync", "network.http.async",
    "network.http.download", "filesystem.mkdir", "crypto.md5", "audio.peq", "data.json",
    "storage.namespaced", "storage.secrets", "playback.remote", "filesystem.playlists", "library.refresh",
    "ui.home_layout", "ui.theme_refresh", "ui.reload", "ui.home_tiles", "ui.launcher_layout",
    "ui.home_background", "audio.gain"
};

static int l_plugin_has_capability(lua_State * L) {
    const char * requested = luaL_checkstring(L, 1);
    bool found = false;
    for (size_t i = 0; i < sizeof(plugin_capabilities) / sizeof(plugin_capabilities[0]); i++) {
        if (strcmp(requested, plugin_capabilities[i]) == 0) { found = true; break; }
    }
    lua_pushboolean(L, found);
    return 1;
}

static int l_plugin_media_capabilities(lua_State * L) {
    lua_newtable(L);

    lua_newtable(L);
    lua_pushstring(L, "mp3");  lua_rawseti(L, -2, 1);
    lua_pushstring(L, "aac");  lua_rawseti(L, -2, 2);
    lua_pushstring(L, "flac"); lua_rawseti(L, -2, 3);
    lua_setfield(L, -2, "codecs");

    lua_newtable(L);
    lua_pushstring(L, "mp3");  lua_rawseti(L, -2, 1);
    lua_pushstring(L, "adts"); lua_rawseti(L, -2, 2);
    lua_pushstring(L, "flac"); lua_rawseti(L, -2, 3);
    lua_setfield(L, -2, "containers");

    lua_pushinteger(L, 0);  lua_setfield(L, -2, "max_sample_rate");
    lua_pushinteger(L, 16); lua_setfield(L, -2, "max_bit_depth");
    lua_pushinteger(L, 2);  lua_setfield(L, -2, "max_channels");

    lua_pushboolean(L, true);  lua_setfield(L, -2, "direct_http_streaming");
    lua_pushboolean(L, false); lua_setfield(L, -2, "range_seeking");
    lua_pushboolean(L, false); lua_setfield(L, -2, "hls");
    lua_pushboolean(L, false); lua_setfield(L, -2, "dash");

    lua_newtable(L); lua_setfield(L, -2, "encryption_modes");
    lua_newtable(L); lua_setfield(L, -2, "drm_systems");

    return 1;
}

static int l_plugin_storage_get(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * key = luaL_checkstring(L, 1);
    char * value = NULL;
    size_t value_len = 0;
    if (plugin_storage_get(id, key, &value, &value_len)) {
        lua_pushlstring(L, value, value_len);
        free(value);
        return 1;
    }
    if (lua_gettop(L) >= 2) {
        lua_pushvalue(L, 2);
        return 1;
    }
    lua_pushnil(L);
    return 1;
}

static int l_plugin_storage_set(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * key = luaL_checkstring(L, 1);
    size_t value_len = 0;
    const char * value = luaL_checklstring(L, 2, &value_len);
    if (!plugin_storage_set(id, key, value, value_len)) {
        lua_pushboolean(L, false);
        lua_pushstring(L, "plugin.storage.set failed");
        return 2;
    }
    lua_pushboolean(L, true);
    return 1;
}

static int l_plugin_storage_delete(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * key = luaL_checkstring(L, 1);
    lua_pushboolean(L, plugin_storage_delete(id, key));
    return 1;
}

static int l_plugin_storage_list(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * prefix = luaL_optstring(L, 1, "");
    char ** keys = NULL;
    int count = plugin_storage_list(id, prefix, &keys);
    if (count < 0) {
        lua_pushnil(L);
        lua_pushstring(L, "plugin.storage.list failed");
        return 2;
    }
    lua_newtable(L);
    for (int i = 0; i < count; i++) {
        lua_pushstring(L, keys[i]);
        lua_rawseti(L, -2, i + 1);
        free(keys[i]);
    }
    free(keys);
    return 1;
}

static int l_plugin_secrets_set(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * key = luaL_checkstring(L, 1);
    size_t value_len = 0;
    const char * value = luaL_checklstring(L, 2, &value_len);
    lua_pushboolean(L, plugin_secrets_set(id, key, value, value_len));
    return 1;
}

static int l_plugin_secrets_exists(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * key = luaL_checkstring(L, 1);
    lua_pushboolean(L, plugin_secrets_exists(id, key));
    return 1;
}

static int l_plugin_secrets_delete(lua_State * L) {
    const char * id = require_plugin_id(L);
    const char * key = luaL_checkstring(L, 1);
    lua_pushboolean(L, plugin_secrets_delete(id, key));
    return 1;
}

static int l_plugin_get_app_info(lua_State * L) {
    lua_newtable(L);
    lua_pushstring(L, app_version_label()); lua_setfield(L, -2, "version");
    lua_pushstring(L, app_build_identifier()); lua_setfield(L, -2, "build");
#ifdef HOST_BUILD
    lua_pushstring(L, "host");
#else
    lua_pushstring(L, "hiby-r1");
#endif
    lua_setfield(L, -2, "platform");
    lua_pushinteger(L, PLUGIN_API_VERSION); lua_setfield(L, -2, "plugin_api");
    return 1;
}

static const luaL_Reg plugin_funcs[] = {
    { "define",                    l_plugin_define },
    { "api_version",               l_plugin_api_version },
    { "has_capability",            l_plugin_has_capability },
    { "get_app_info",              l_plugin_get_app_info },
    { "register_list_item",        l_plugin_register_list_item },
    { "register_stream_media_tile", l_plugin_register_stream_media_tile },
    { "register_home_tile",        l_plugin_register_home_tile },
    { "show_list",                 l_plugin_show_list },
    { "show_settings_list",        l_plugin_show_settings_list },
    { "list_dir",                  l_plugin_list_dir },
    { "sd_root",                   l_plugin_sd_root },
    { "playlist_list",             l_plugin_playlist_list },
    { "playlist_read",             l_plugin_playlist_read },
    { "playlist_create",           l_plugin_playlist_create },
    { "playlist_add",              l_plugin_playlist_add },
    { "playlist_remove",           l_plugin_playlist_remove },
    { "playlist_delete",           l_plugin_playlist_delete },
    { "mkdir",                     l_plugin_mkdir },
    { "play_file",                 l_plugin_play_file },
    { "play_list",                 l_plugin_play_list },
    { "play_remote",               l_plugin_play_remote },
    { "queue_remote_list",         l_plugin_queue_remote_list },
    { "show_toast",                l_plugin_show_toast },
    { "set_gain",                  l_plugin_set_gain },
    { "get_gain",                  l_plugin_get_gain },
    { "set_icon",                  l_plugin_set_icon },
    { "set_background_color",      l_plugin_set_background_color },
    { "set_text_color",            l_plugin_set_text_color },
    { "set_home_layout",           l_plugin_set_home_layout },
    { "set_launcher_layout",       l_plugin_set_launcher_layout },
    { "refresh_theme",             l_plugin_refresh_theme },
    { "reload_ui",                 l_plugin_reload_ui },
    { "eq_load_profile",           l_plugin_eq_load_profile },
    { "eq_save_profile",           l_plugin_eq_save_profile },
    { "eq_reset",                  l_plugin_eq_reset },
    { "eq_set_bypass",             l_plugin_eq_set_bypass },
    { "eq_set_preamp",             l_plugin_eq_set_preamp },
    { "eq_set_band",               l_plugin_eq_set_band },
    { "eq_set_band_type",          l_plugin_eq_set_band_type },
    { "eq_set_band_enabled",       l_plugin_eq_set_band_enabled },
    { "toggle_pause",              l_plugin_toggle_pause },
    { "stop",                      l_plugin_stop },
    { "next_track",                l_plugin_next_track },
    { "prev_track",                l_plugin_prev_track },
    { "seek",                      l_plugin_seek },
    { "set_volume",                l_plugin_set_volume },
    { "is_playing",                l_plugin_is_playing },
    { "is_paused",                 l_plugin_is_paused },
    { "get_position",              l_plugin_get_position },
    { "get_duration",              l_plugin_get_duration },
    { "http_get",                  l_plugin_http_get },
    { "http_post",                 l_plugin_http_post },
    { "http_request",              l_plugin_http_request },
    { "download_file_async",       l_plugin_download_file_async },
    { "cancel",                    l_plugin_cancel },
    { "md5",                       l_plugin_md5 },
    { "json_decode",               l_plugin_json_decode },
    { "json_encode",               l_plugin_json_encode },
    { "media_capabilities",        l_plugin_media_capabilities },
    { "show_text_input",           l_plugin_show_text_input },
    { "get_now_playing",           l_plugin_get_now_playing },
    { "get_play_mode",             l_plugin_get_play_mode },
    { "get_current_track_path",    l_plugin_get_current_track_path },
    { "get_artist_albums",         l_plugin_get_artist_albums },
    { "get_album_tracks",          l_plugin_get_album_tracks },
    { "get_next_album_tracks",     l_plugin_get_next_album_tracks },
    { "library_song_count",        l_plugin_library_song_count },
    { "library_get_songs",         l_plugin_library_get_songs },
    { "library_search",            l_plugin_library_search },
    { "library_get_song",          l_plugin_library_get_song },
    { "library_get_artists",       l_plugin_library_get_artists },
    { "library_get_albums",        l_plugin_library_get_albums },
    { "refresh_library",           l_plugin_refresh_library },
    { "on",                        l_plugin_on },
    { "set_interval",              l_plugin_set_interval },
    { "clear_interval",            l_plugin_clear_interval },
    { NULL, NULL }
};

static const luaL_Reg plugin_storage_funcs[] = {
    { "get",    l_plugin_storage_get },
    { "set",    l_plugin_storage_set },
    { "delete", l_plugin_storage_delete },
    { "list",   l_plugin_storage_list },
    { NULL, NULL }
};

static const luaL_Reg plugin_secrets_funcs[] = {
    { "set",    l_plugin_secrets_set },
    { "exists", l_plugin_secrets_exists },
    { "delete", l_plugin_secrets_delete },
    { NULL, NULL }
};

#define PLUGIN_CALL_MAX_MS 2000

static struct timespec plugin_call_deadline_start;

static void plugin_call_exclude_native_elapsed(const struct timespec * started) {
    struct timespec ended;
    clock_gettime(CLOCK_MONOTONIC, &ended);
    time_t sec = ended.tv_sec - started->tv_sec;
    long nsec = ended.tv_nsec - started->tv_nsec;
    if (nsec < 0) { sec--; nsec += 1000000000L; }
    plugin_call_deadline_start.tv_sec += sec;
    plugin_call_deadline_start.tv_nsec += nsec;
    if (plugin_call_deadline_start.tv_nsec >= 1000000000L) {
        plugin_call_deadline_start.tv_sec++;
        plugin_call_deadline_start.tv_nsec -= 1000000000L;
    }
}

static int plugin_call_native(lua_State * L, lua_CFunction fn) {
    int nargs = lua_gettop(L);
    struct timespec started;
    clock_gettime(CLOCK_MONOTONIC, &started);
    lua_pushcfunction(L, fn);
    lua_insert(L, 1);
    int rc = lua_pcall(L, nargs, LUA_MULTRET, 0);
    plugin_call_exclude_native_elapsed(&started);
    if (rc != LUA_OK) return lua_error(L);
    return lua_gettop(L);
}

static int l_plugin_api_guard(lua_State * L) {
    return plugin_call_native(L, lua_tocfunction(L, lua_upvalueindex(1)));
}

static void register_plugin_lib(lua_State * L, const luaL_Reg * regs) {
    lua_newtable(L);
    for (; regs->name != NULL; regs++) {
        lua_pushcfunction(L, regs->func);
        lua_pushcclosure(L, l_plugin_api_guard, 1);
        lua_setfield(L, -2, regs->name);
    }
}

static void register_plugin_api(lua_State * L) {
    register_plugin_lib(L, plugin_funcs);
    register_plugin_lib(L, plugin_storage_funcs);
    lua_setfield(L, -2, "storage");
    register_plugin_lib(L, plugin_secrets_funcs);
    lua_setfield(L, -2, "secrets");
    lua_setglobal(L, "plugin");
}

static lua_CFunction real_io_open = NULL;
static lua_CFunction real_io_lines = NULL;
static lua_CFunction real_io_input = NULL;
static lua_CFunction real_io_output = NULL;
static lua_CFunction real_os_remove = NULL;
static lua_CFunction real_os_rename = NULL;

static int l_guarded_io_open(lua_State * L) {
    const char * path = luaL_optstring(L, 1, "");
    if (plugin_storage_path_is_reserved(path)) {
        lua_pushnil(L);
        lua_pushliteral(L, "io.open: path is reserved for plugin.storage/plugin.secrets");
        return 2;
    }
    return plugin_call_native(L, real_io_open);
}

static int l_guarded_io_lines(lua_State * L) {
    if (lua_gettop(L) >= 1 && lua_isstring(L, 1)) {
        const char * path = lua_tostring(L, 1);
        if (plugin_storage_path_is_reserved(path)) {
            return luaL_error(L, "io.lines: path is reserved for plugin.storage/plugin.secrets");
        }
    }
    return plugin_call_native(L, real_io_lines);
}

static int l_guarded_io_input(lua_State * L) {
    if (lua_gettop(L) >= 1 && lua_isstring(L, 1)) {
        const char * path = lua_tostring(L, 1);
        if (plugin_storage_path_is_reserved(path)) {
            return luaL_error(L, "io.input: path is reserved for plugin.storage/plugin.secrets");
        }
    }
    return plugin_call_native(L, real_io_input);
}

static int l_guarded_io_output(lua_State * L) {
    if (lua_gettop(L) >= 1 && lua_isstring(L, 1)) {
        const char * path = lua_tostring(L, 1);
        if (plugin_storage_path_is_reserved(path)) {
            return luaL_error(L, "io.output: path is reserved for plugin.storage/plugin.secrets");
        }
    }
    return plugin_call_native(L, real_io_output);
}

static int l_guarded_os_remove(lua_State * L) {
    const char * path = luaL_optstring(L, 1, "");
    if (plugin_storage_path_is_reserved(path)) {
        lua_pushnil(L);
        lua_pushliteral(L, "os.remove: path is reserved for plugin.storage/plugin.secrets");
        return 2;
    }
    return plugin_call_native(L, real_os_remove);
}

static int l_guarded_os_rename(lua_State * L) {
    const char * from = luaL_optstring(L, 1, "");
    const char * to = luaL_optstring(L, 2, "");
    if (plugin_storage_path_is_reserved(from) || plugin_storage_path_is_reserved(to)) {
        lua_pushnil(L);
        lua_pushliteral(L, "os.rename: path is reserved for plugin.storage/plugin.secrets");
        return 2;
    }
    return plugin_call_native(L, real_os_rename);
}

static void sandbox_plugin_lua_state(lua_State * L) {
    lua_pushnil(L); lua_setglobal(L, "load");
    lua_pushnil(L); lua_setglobal(L, "loadstring");
    lua_pushnil(L); lua_setglobal(L, "loadfile");
    lua_pushnil(L); lua_setglobal(L, "dofile");
    lua_pushnil(L); lua_setglobal(L, "require");
    lua_pushnil(L); lua_setglobal(L, "package");
    lua_pushnil(L); lua_setglobal(L, "debug");

    lua_getglobal(L, "os");
    if (lua_istable(L, -1)) {
        static const char * dangerous_os[] = { "execute", "getenv", "exit", "tmpname" };
        for (size_t i = 0; i < sizeof(dangerous_os) / sizeof(dangerous_os[0]); i++) {
            lua_pushnil(L);
            lua_setfield(L, -2, dangerous_os[i]);
        }

        lua_getfield(L, -1, "remove");
        if (lua_iscfunction(L, -1)) real_os_remove = lua_tocfunction(L, -1);
        lua_pop(L, 1);
        lua_getfield(L, -1, "rename");
        if (lua_iscfunction(L, -1)) real_os_rename = lua_tocfunction(L, -1);
        lua_pop(L, 1);
        if (real_os_remove) { lua_pushcfunction(L, l_guarded_os_remove); lua_setfield(L, -2, "remove"); }
        if (real_os_rename) { lua_pushcfunction(L, l_guarded_os_rename); lua_setfield(L, -2, "rename"); }
    }
    lua_pop(L, 1);

    lua_getglobal(L, "io");
    if (lua_istable(L, -1)) {
        lua_pushnil(L);
        lua_setfield(L, -2, "popen");

        lua_getfield(L, -1, "open");
        if (lua_iscfunction(L, -1)) real_io_open = lua_tocfunction(L, -1);
        lua_pop(L, 1);
        lua_getfield(L, -1, "lines");
        if (lua_iscfunction(L, -1)) real_io_lines = lua_tocfunction(L, -1);
        lua_pop(L, 1);
        lua_getfield(L, -1, "input");
        if (lua_iscfunction(L, -1)) real_io_input = lua_tocfunction(L, -1);
        lua_pop(L, 1);
        lua_getfield(L, -1, "output");
        if (lua_iscfunction(L, -1)) real_io_output = lua_tocfunction(L, -1);
        lua_pop(L, 1);
        if (real_io_open) { lua_pushcfunction(L, l_guarded_io_open); lua_setfield(L, -2, "open"); }
        if (real_io_lines) { lua_pushcfunction(L, l_guarded_io_lines); lua_setfield(L, -2, "lines"); }
        if (real_io_input) { lua_pushcfunction(L, l_guarded_io_input); lua_setfield(L, -2, "input"); }
        if (real_io_output) { lua_pushcfunction(L, l_guarded_io_output); lua_setfield(L, -2, "output"); }
    }
    lua_pop(L, 1);
}

static void plugin_call_timeout_hook(lua_State * L, lua_Debug * ar) {
    (void) ar;
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    long elapsed_ms = (now.tv_sec - plugin_call_deadline_start.tv_sec) * 1000L +
                      (now.tv_nsec - plugin_call_deadline_start.tv_nsec) / 1000000L;
    if (elapsed_ms > PLUGIN_CALL_MAX_MS) {
        luaL_error(L, "plugin call exceeded %dms time budget -- aborted to keep the UI responsive", PLUGIN_CALL_MAX_MS);
    }
}

static int plugin_call(lua_State * L, int nargs, int nresults, int errfunc) {
    clock_gettime(CLOCK_MONOTONIC, &plugin_call_deadline_start);
    lua_sethook(L, plugin_call_timeout_hook, LUA_MASKCOUNT, 10000);
    int result = lua_pcall(L, nargs, nresults, errfunc);
    lua_sethook(L, NULL, 0, 0);
    return result;
}

static void load_plugin_file(const char * path) {
    lua_State * L = luaL_newstate();
    if (!L) return;
    int slot = plugin_instance_count;
    plugin_instance_t * inst = &plugin_instances[slot];
    memset(inst, 0, sizeof(*inst));
    inst->L = L;
    const char * base = strrchr(path, '/');
    base = base ? base + 1 : path;
    snprintf(inst->filename, sizeof(inst->filename), "%s", base);
    loading_plugin_slot = slot;
    luaL_openlibs(L);
    sandbox_plugin_lua_state(L);
    register_plugin_api(L);

    if ((luaL_loadfile(L, path) || plugin_call(L, 0, LUA_MULTRET, 0)) != LUA_OK) {
        const char * err = lua_tostring(L, -1);
        fprintf(stderr, "[plugins] failed to load %s: %s\n", path, err ? err : "unknown error");
        lua_close(L);
        memset(inst, 0, sizeof(*inst));
        loading_plugin_slot = -1;
        return;
    }

    if (!inst->defined) {
        snprintf(inst->id, sizeof(inst->id), "legacy.%.*s", (int) sizeof(inst->id) - 8, base);
        char * dot = strrchr(inst->id, '.');
        if (dot && strcasecmp(dot, ".lua") == 0) *dot = '\0';
        if (plugin_id_collides(inst->id, slot)) {
            uint64_t h = 0xcbf29ce484222325ULL;
            for (const char * p = path; *p; p++) { h ^= (unsigned char) *p; h *= 0x100000001b3ULL; }
            char base_no_ext[sizeof(inst->id)];
            snprintf(base_no_ext, sizeof(base_no_ext), "%s", base);
            char * base_dot = strrchr(base_no_ext, '.');
            if (base_dot && strcasecmp(base_dot, ".lua") == 0) *base_dot = '\0';
            snprintf(inst->id, sizeof(inst->id), "legacy.%.*s.%016llx",
                     (int) sizeof(inst->id) - 7 - 1 - 16 - 1, base_no_ext, (unsigned long long) h);
            if (plugin_id_collides(inst->id, slot)) {
                fprintf(stderr, "[plugins] refusing to load %s: generated id '%s' still collides with another plugin's id\n",
                        path, inst->id);
                lua_close(L);
                memset(inst, 0, sizeof(*inst));
                loading_plugin_slot = -1;
                return;
            }
        }
        snprintf(inst->name, sizeof(inst->name), "%.*s", (int) sizeof(inst->name) - 1, base);
        snprintf(inst->version, sizeof(inst->version), "0");
        inst->defined = true;
    }
    loading_plugin_slot = -1;
    plugin_instance_count++;
}

static int plugin_filename_cmp(const void * a, const void * b) {
    return strcmp((const char *) a, (const char *) b);
}

static char (*scan_plugin_dir_sorted_names(char dir_path_out[600], int * out_count))[256] {
    *out_count = 0;
    snprintf(dir_path_out, 600, "%s/.plugins", MUSIC_ROOT_DIR);

    DIR * d = opendir(dir_path_out);
    if (!d) return NULL;

    int total = 0;
    struct dirent * ent;
    while ((ent = readdir(d)) != NULL) {
        size_t len = strlen(ent->d_name);
        if (len < 5 || strcasecmp(ent->d_name + len - 4, ".lua") != 0) continue;
        total++;
    }
    if (total == 0) {
        closedir(d);
        return NULL;
    }

    char (*names)[256] = malloc((size_t) total * sizeof(*names));
    if (!names) {
        closedir(d);
        return NULL;
    }

    rewinddir(d);
    int name_count = 0;
    while (name_count < total && (ent = readdir(d)) != NULL) {
        size_t len = strlen(ent->d_name);
        if (len < 5 || strcasecmp(ent->d_name + len - 4, ".lua") != 0) continue;
        snprintf(names[name_count], sizeof(names[0]), "%s", ent->d_name);
        name_count++;
    }
    closedir(d);

    qsort(names, (size_t) name_count, sizeof(names[0]), plugin_filename_cmp);
    *out_count = name_count;
    return names;
}

void plugin_manager_init(void) {
    plugin_disabled_list_load();

    char dir_path[600];
    int name_count = 0;
    char (*names)[256] = scan_plugin_dir_sorted_names(dir_path, &name_count);
    if (!names) return;

    int enabled_count = 0;
    for (int i = 0; i < name_count; i++) {
        if (plugin_disabled_list_contains(names[i])) continue;
        if (enabled_count != i) memcpy(names[enabled_count], names[i], sizeof(names[0]));
        enabled_count++;
    }

    int load_count = (enabled_count > PLUGIN_MAX_FILES) ? PLUGIN_MAX_FILES : enabled_count;
    for (int i = 0; i < load_count; i++) {
        if (plugin_instance_count >= PLUGIN_MAX_FILES) break;
        char full_path[700];
        snprintf(full_path, sizeof(full_path), "%s/%s", dir_path, names[i]);
        load_plugin_file(full_path);
    }
    free(names);
}

static void fill_available_entry(plugin_available_entry_t * e, const char * filename) {
    snprintf(e->filename, sizeof(e->filename), "%s", filename);
    e->disabled = plugin_disabled_list_contains(filename);
    e->loaded = false;
    snprintf(e->display_name, sizeof(e->display_name), "%s", filename);

    for (int j = 0; j < plugin_instance_count; j++) {
        if (strcmp(plugin_instances[j].filename, filename) == 0) {
            e->loaded = true;
            snprintf(e->display_name, sizeof(e->display_name), "%s", plugin_instances[j].name);
            break;
        }
    }
}

int plugin_manager_scan_available(plugin_available_entry_t * out, int max) {
    char dir_path[600];
    int name_count = 0;
    char (*names)[256] = scan_plugin_dir_sorted_names(dir_path, &name_count);
    if (!names) return 0;

    int count = 0;
    if (name_count <= max) {
        for (int i = 0; i < name_count; i++) fill_available_entry(&out[count++], names[i]);
    } else {
        bool * included = calloc((size_t) name_count, sizeof(bool));
        if (!included) { free(names); return 0; }

        for (int i = 0; i < name_count && count < max; i++) {
            bool is_loaded = false;
            for (int j = 0; j < plugin_instance_count; j++) {
                if (strcmp(plugin_instances[j].filename, names[i]) == 0) { is_loaded = true; break; }
            }
            if (is_loaded) {
                fill_available_entry(&out[count++], names[i]);
                included[i] = true;
            }
        }
        for (int i = 0; i < name_count && count < max; i++) {
            if (!included[i]) fill_available_entry(&out[count++], names[i]);
        }
        free(included);
    }

    free(names);
    return count;
}

void plugin_manager_cancel_all_async_http(void) {
    for (int i = 0; i < PLUGIN_MAX_ASYNC_HTTP; i++) {
        plugin_async_http_t * req = &plugin_async_http[i];
        if (!req->active) continue;
        http_cancel_token_cancel(&req->cancel);
        pthread_join(req->thread, NULL);
        luaL_unref(req->L, LUA_REGISTRYINDEX, req->callback_ref);
        free(req->response_body);
        req->response_body = NULL;
        req->response_body_size = 0;
        req->active = false;
        atomic_store(&req->done, false);
        http_cancel_token_destroy(&req->cancel);
        req->L = NULL;
        req->callback_ref = LUA_NOREF;
    }
}

static void deinit_diag(const char * step) {
    int fd = open("/data/mnt/sd_0/reload_diag.log", O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644);
    if (fd < 0) return;
    char line[224];
    int len = snprintf(line, sizeof(line), "[pid=%ld] %s\n", (long) getpid(), step);
    if (len > 0) {
        if (len >= (int) sizeof(line)) len = (int) sizeof(line) - 1;
        write(fd, line, (size_t) len);
        fsync(fd);
    }
    close(fd);
}

void plugin_manager_deinit(void) {
    deinit_diag("plugin_manager_deinit: reset_home_layout before");
    gui_plugin_reset_home_layout();
    gui_plugin_reset_launcher_layout();
    deinit_diag("plugin_manager_deinit: cancel_all_async_http before");
    plugin_manager_cancel_all_async_http();
    deinit_diag("plugin_manager_deinit: cancel_all_async_http after");

    for (int i = 0; i < PLUGIN_MAX_INTERVALS; i++) {
        if (!plugin_intervals[i].active) continue;
        char msg[96];
        snprintf(msg, sizeof(msg), "plugin_manager_deinit: clearing interval slot %d before", i);
        deinit_diag(msg);
        luaL_unref(plugin_intervals[i].L, LUA_REGISTRYINDEX, plugin_intervals[i].ref);
        plugin_intervals[i].active = false;
        plugin_intervals[i].L = NULL;
        gui_plugin_clear_interval(i);
    }

    deinit_diag("plugin_manager_deinit: text_input_cancelled before");
    plugin_manager_text_input_cancelled();

    for (int i = 0; i < plugin_instance_count; i++) {
        if (plugin_instances[i].L) {
            char msg[160];
            snprintf(msg, sizeof(msg), "plugin_manager_deinit: lua_close slot %d id='%s' name='%s' before", i,
                     plugin_instances[i].id, plugin_instances[i].name);
            deinit_diag(msg);
            lua_close(plugin_instances[i].L);
        }
    }
    deinit_diag("plugin_manager_deinit: all lua_close done, memset before");
    memset(plugin_instances, 0, sizeof(plugin_instances));
    plugin_instance_count = 0;

    memset(plugin_books_list_items, 0, sizeof(plugin_books_list_items));
    plugin_books_list_item_count = 0;
    memset(plugin_settings_list_items, 0, sizeof(plugin_settings_list_items));
    plugin_settings_list_item_count = 0;
    memset(plugin_display_list_items, 0, sizeof(plugin_display_list_items));
    plugin_display_list_item_count = 0;
    memset(plugin_playback_list_items, 0, sizeof(plugin_playback_list_items));
    plugin_playback_list_item_count = 0;
    memset(plugin_power_list_items, 0, sizeof(plugin_power_list_items));
    plugin_power_list_item_count = 0;
    memset(plugin_system_list_items, 0, sizeof(plugin_system_list_items));
    plugin_system_list_item_count = 0;
    memset(plugin_stream_tiles, 0, sizeof(plugin_stream_tiles));
    plugin_stream_tile_count = 0;
    memset(plugin_home_tiles, 0, sizeof(plugin_home_tiles));
    plugin_home_tile_count = 0;
    memset(plugin_list_callbacks, 0, sizeof(plugin_list_callbacks));
    memset(plugin_settings_list_rows, 0, sizeof(plugin_settings_list_rows));
    memset(plugin_settings_list_row_counts, 0, sizeof(plugin_settings_list_row_counts));
    memset(plugin_event_subscriber_count, 0, sizeof(plugin_event_subscriber_count));
}

void plugin_manager_poll(void) {
    for (int i = 0; i < PLUGIN_MAX_ASYNC_HTTP; i++) {
        plugin_async_http_t * req = &plugin_async_http[i];
        if (!req->active || !atomic_load(&req->done)) continue;
        pthread_join(req->thread, NULL);

        if (!http_cancel_token_is_cancelled(&req->cancel)) {
            lua_rawgeti(req->L, LUA_REGISTRYINDEX, req->callback_ref);
            int callback_args;
            if (req->is_download) {
                if (req->ok) {
                    lua_pushstring(req->L, req->dest_path);
                    lua_pushnil(req->L);
                } else {
                    lua_pushnil(req->L);
                    lua_pushstring(req->L, "download failed");
                }
                callback_args = 2;
            } else if (req->ok) {
                lua_pushinteger(req->L, req->status);
                lua_pushlstring(req->L, req->response_body ? (const char *) req->response_body : "",
                                req->response_body_size);
                lua_pushnil(req->L);
                lua_newtable(req->L);
                for (int h = 0; h < req->response_header_count; h++) {
                    lua_pushstring(req->L, req->response_headers[h].value);
                    lua_setfield(req->L, -2, req->response_headers[h].name);
                }
                callback_args = 4;
            } else {
                lua_pushnil(req->L);
                lua_pushnil(req->L);
                lua_pushstring(req->L, (req->response_error && req->response_error[0])
                                           ? req->response_error : "network error or response limit exceeded");
                callback_args = 3;
            }
            if (plugin_call(req->L, callback_args, 0, 0) != LUA_OK) {
                const char * err = lua_tostring(req->L, -1);
                fprintf(stderr, "[plugins] HTTP callback error: %s\n", err ? err : "unknown error");
                lua_pop(req->L, 1);
            }
        }

        luaL_unref(req->L, LUA_REGISTRYINDEX, req->callback_ref);
        free(req->response_body);
        req->response_body = NULL;
        req->response_body_size = 0;
        req->active = false;
        atomic_store(&req->done, false);
        http_cancel_token_destroy(&req->cancel);
        req->L = NULL;
        req->callback_ref = LUA_NOREF;
    }
}

bool plugin_manager_has_background_work(void) {
    for (int i = 0; i < PLUGIN_MAX_ASYNC_HTTP; i++)
        if (plugin_async_http[i].active) return true;
    return false;
}

static void dispatch_list_item_open(plugin_list_item_t * item, const char * kind) {
    lua_rawgeti(item->L, LUA_REGISTRYINDEX, item->open_ref);
    if (plugin_call(item->L, 0, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(item->L, -1);
        fprintf(stderr, "[plugins] %s '%s' on_open error: %s\n", kind, item->label, err ? err : "unknown error");
        lua_pop(item->L, 1);
    }
}

static void get_list_item_options(const plugin_list_item_t * array, int count, int index, const char ** out_icon,
                                   int32_t * out_height, int32_t * out_width, const char ** out_text_size) {
    *out_icon = NULL;
    *out_height = 0;
    *out_width = 0;
    *out_text_size = NULL;
    if (index < 0 || index >= count) return;

    const plugin_list_item_t * item = &array[index];
    if (item->icon_path[0]) *out_icon = item->icon_path;
    *out_height = item->row_height;
    *out_width = item->row_width;
    if (item->text_size[0]) *out_text_size = item->text_size;
}

int plugin_manager_get_books_list_item_count(void) {
    return plugin_books_list_item_count;
}

const char * plugin_manager_get_books_list_item_label(int index) {
    if (index < 0 || index >= plugin_books_list_item_count) return "";
    return plugin_books_list_items[index].label;
}

void plugin_manager_books_list_item_clicked(int index) {
    if (index < 0 || index >= plugin_books_list_item_count) return;
    dispatch_list_item_open(&plugin_books_list_items[index], "books list item");
}

void plugin_manager_get_books_list_item_options(int index, const char ** out_icon, int32_t * out_height,
                                                 int32_t * out_width, const char ** out_text_size) {
    get_list_item_options(plugin_books_list_items, plugin_books_list_item_count, index, out_icon, out_height,
                           out_width, out_text_size);
}

int plugin_manager_get_settings_list_item_count(void) {
    return plugin_settings_list_item_count;
}

const char * plugin_manager_get_settings_list_item_label(int index) {
    if (index < 0 || index >= plugin_settings_list_item_count) return "";
    return plugin_settings_list_items[index].label;
}

void plugin_manager_settings_list_item_clicked(int index) {
    if (index < 0 || index >= plugin_settings_list_item_count) return;
    dispatch_list_item_open(&plugin_settings_list_items[index], "settings list item");
}

void plugin_manager_get_settings_list_item_options(int index, const char ** out_icon, int32_t * out_height,
                                                    int32_t * out_width, const char ** out_text_size) {
    get_list_item_options(plugin_settings_list_items, plugin_settings_list_item_count, index, out_icon, out_height,
                           out_width, out_text_size);
}

int plugin_manager_get_display_list_item_count(void) {
    return plugin_display_list_item_count;
}

const char * plugin_manager_get_display_list_item_label(int index) {
    if (index < 0 || index >= plugin_display_list_item_count) return "";
    return plugin_display_list_items[index].label;
}

void plugin_manager_display_list_item_clicked(int index) {
    if (index < 0 || index >= plugin_display_list_item_count) return;
    dispatch_list_item_open(&plugin_display_list_items[index], "display list item");
}

void plugin_manager_get_display_list_item_options(int index, const char ** out_icon, int32_t * out_height,
                                                   int32_t * out_width, const char ** out_text_size) {
    get_list_item_options(plugin_display_list_items, plugin_display_list_item_count, index, out_icon, out_height,
                           out_width, out_text_size);
}

int plugin_manager_get_playback_list_item_count(void) {
    return plugin_playback_list_item_count;
}

const char * plugin_manager_get_playback_list_item_label(int index) {
    if (index < 0 || index >= plugin_playback_list_item_count) return "";
    return plugin_playback_list_items[index].label;
}

void plugin_manager_playback_list_item_clicked(int index) {
    if (index < 0 || index >= plugin_playback_list_item_count) return;
    dispatch_list_item_open(&plugin_playback_list_items[index], "playback list item");
}

void plugin_manager_get_playback_list_item_options(int index, const char ** out_icon, int32_t * out_height,
                                                    int32_t * out_width, const char ** out_text_size) {
    get_list_item_options(plugin_playback_list_items, plugin_playback_list_item_count, index, out_icon, out_height,
                           out_width, out_text_size);
}

int plugin_manager_get_power_list_item_count(void) {
    return plugin_power_list_item_count;
}

const char * plugin_manager_get_power_list_item_label(int index) {
    if (index < 0 || index >= plugin_power_list_item_count) return "";
    return plugin_power_list_items[index].label;
}

void plugin_manager_power_list_item_clicked(int index) {
    if (index < 0 || index >= plugin_power_list_item_count) return;
    dispatch_list_item_open(&plugin_power_list_items[index], "power list item");
}

void plugin_manager_get_power_list_item_options(int index, const char ** out_icon, int32_t * out_height,
                                                 int32_t * out_width, const char ** out_text_size) {
    get_list_item_options(plugin_power_list_items, plugin_power_list_item_count, index, out_icon, out_height,
                           out_width, out_text_size);
}

int plugin_manager_get_system_list_item_count(void) {
    return plugin_system_list_item_count;
}

const char * plugin_manager_get_system_list_item_label(int index) {
    if (index < 0 || index >= plugin_system_list_item_count) return "";
    return plugin_system_list_items[index].label;
}

void plugin_manager_system_list_item_clicked(int index) {
    if (index < 0 || index >= plugin_system_list_item_count) return;
    dispatch_list_item_open(&plugin_system_list_items[index], "system list item");
}

void plugin_manager_get_system_list_item_options(int index, const char ** out_icon, int32_t * out_height,
                                                  int32_t * out_width, const char ** out_text_size) {
    get_list_item_options(plugin_system_list_items, plugin_system_list_item_count, index, out_icon, out_height,
                           out_width, out_text_size);
}

static void dispatch_tile_open(plugin_tile_t * t) {
    lua_rawgeti(t->L, LUA_REGISTRYINDEX, t->open_ref);
    if (plugin_call(t->L, 0, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(t->L, -1);
        fprintf(stderr, "[plugins] tile '%s' on_open error: %s\n", t->label, err ? err : "unknown error");
        lua_pop(t->L, 1);
    }
}

int plugin_manager_get_stream_tile_count(void) {
    return plugin_stream_tile_count;
}

const char * plugin_manager_get_stream_tile_label(int index) {
    if (index < 0 || index >= plugin_stream_tile_count) return "";
    return plugin_stream_tiles[index].label;
}

const char * plugin_manager_get_stream_tile_icon(int index) {
    if (index < 0 || index >= plugin_stream_tile_count) return "stream_media/radio.png";
    return plugin_stream_tiles[index].icon;
}

const char * plugin_manager_get_stream_tile_icon_selected(int index) {
    if (index < 0 || index >= plugin_stream_tile_count) return "stream_media/radio_s.png";
    return plugin_stream_tiles[index].icon_selected;
}

void plugin_manager_stream_tile_clicked(int index) {
    if (index < 0 || index >= plugin_stream_tile_count) return;
    dispatch_tile_open(&plugin_stream_tiles[index]);
}

int plugin_manager_get_home_tile_count(void) {
    return plugin_home_tile_count;
}

int plugin_manager_find_home_tile_by_id(const char * id) {
    if (!id) return -1;
    for (int i = 0; i < plugin_home_tile_count; i++) {
        if (strcmp(plugin_home_tiles[i].id, id) == 0) return i;
    }
    return -1;
}

const char * plugin_manager_get_home_tile_id(int index) {
    if (index < 0 || index >= plugin_home_tile_count) return "";
    return plugin_home_tiles[index].id;
}

const char * plugin_manager_get_home_tile_label(int index) {
    if (index < 0 || index >= plugin_home_tile_count) return "";
    return plugin_home_tiles[index].label;
}

const char * plugin_manager_get_home_tile_icon(int index) {
    if (index < 0 || index >= plugin_home_tile_count) return "";
    return plugin_home_tiles[index].icon;
}

const char * plugin_manager_get_home_tile_icon_selected(int index) {
    if (index < 0 || index >= plugin_home_tile_count) return "";
    return plugin_home_tiles[index].icon_selected;
}

void plugin_manager_home_tile_clicked(int index) {
    if (index < 0 || index >= plugin_home_tile_count) return;
    dispatch_tile_open(&plugin_home_tiles[index]);
}

void plugin_manager_list_item_selected(int slot, int index) {
    if (slot < 0 || slot >= PLUGIN_LIST_SCREEN_POOL_SIZE) return;
    plugin_list_callback_t * cb = &plugin_list_callbacks[slot];
    if (!cb->L || cb->select_ref == LUA_NOREF) return;

    lua_rawgeti(cb->L, LUA_REGISTRYINDEX, cb->select_ref);
    lua_pushinteger(cb->L, index + 1);
    if (plugin_call(cb->L, 1, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(cb->L, -1);
        fprintf(stderr, "[plugins] show_list on_select error: %s\n", err ? err : "unknown error");
        lua_pop(cb->L, 1);
    }
}

static bool settings_list_row_ref(int slot, int row, lua_State ** out_L, int * out_ref) {
    if (slot < 0 || slot >= PLUGIN_SETTINGS_LIST_SCREEN_POOL_SIZE) return false;
    if (row < 0 || row >= plugin_settings_list_row_counts[slot]) return false;
    plugin_settings_list_row_ref_t * r = &plugin_settings_list_rows[slot][row];
    if (!r->L) return false;
    *out_L = r->L;
    *out_ref = r->callback_ref;
    return true;
}

void plugin_manager_settings_list_row_selected(int slot, int row) {
    lua_State * L;
    int ref;
    if (!settings_list_row_ref(slot, row, &L, &ref)) return;

    lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
    if (plugin_call(L, 0, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(L, -1);
        fprintf(stderr, "[plugins] show_settings_list on_select error: %s\n", err ? err : "unknown error");
        lua_pop(L, 1);
    }
}

void plugin_manager_settings_list_toggled(int slot, int row, bool new_value) {
    lua_State * L;
    int ref;
    if (!settings_list_row_ref(slot, row, &L, &ref)) return;

    lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
    lua_pushboolean(L, new_value);
    if (plugin_call(L, 1, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(L, -1);
        fprintf(stderr, "[plugins] show_settings_list on_change error: %s\n", err ? err : "unknown error");
        lua_pop(L, 1);
    }
}

void plugin_manager_settings_list_slid(int slot, int row, int new_value) {
    lua_State * L;
    int ref;
    if (!settings_list_row_ref(slot, row, &L, &ref)) return;

    lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
    lua_pushinteger(L, new_value);
    if (plugin_call(L, 1, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(L, -1);
        fprintf(stderr, "[plugins] show_settings_list on_change error: %s\n", err ? err : "unknown error");
        lua_pop(L, 1);
    }
}

void plugin_manager_notify_track_started(const char * title, const char * artist, const char * album,
                                          double duration_seconds, const char * provider, const char * track_id) {
    for (int i = 0; i < plugin_event_subscriber_count[PLUGIN_EVENT_TRACK_STARTED]; i++) {
        plugin_event_subscriber_t * sub = &plugin_event_subscribers[PLUGIN_EVENT_TRACK_STARTED][i];
        lua_rawgeti(sub->L, LUA_REGISTRYINDEX, sub->ref);
        lua_pushstring(sub->L, title ? title : "");
        lua_pushstring(sub->L, artist ? artist : "");
        lua_pushstring(sub->L, album ? album : "");
        lua_pushnumber(sub->L, duration_seconds);
        lua_pushstring(sub->L, provider ? provider : "");
        lua_pushstring(sub->L, track_id ? track_id : "");
        if (plugin_call(sub->L, 6, 0, 0) != LUA_OK) {
            const char * err = lua_tostring(sub->L, -1);
            fprintf(stderr, "[plugins] track_started handler error: %s\n", err ? err : "unknown error");
            lua_pop(sub->L, 1);
        }
    }
}

static void notify_event_no_args(plugin_event_t idx, const char * kind) {
    for (int i = 0; i < plugin_event_subscriber_count[idx]; i++) {
        plugin_event_subscriber_t * sub = &plugin_event_subscribers[idx][i];
        lua_rawgeti(sub->L, LUA_REGISTRYINDEX, sub->ref);
        if (plugin_call(sub->L, 0, 0, 0) != LUA_OK) {
            const char * err = lua_tostring(sub->L, -1);
            fprintf(stderr, "[plugins] %s handler error: %s\n", kind, err ? err : "unknown error");
            lua_pop(sub->L, 1);
        }
    }
}

void plugin_manager_notify_paused(void) {
    notify_event_no_args(PLUGIN_EVENT_PAUSED, "paused");
}

void plugin_manager_notify_resumed(void) {
    notify_event_no_args(PLUGIN_EVENT_RESUMED, "resumed");
}

void plugin_manager_notify_stopped(void) {
    notify_event_no_args(PLUGIN_EVENT_STOPPED, "stopped");
}

void plugin_manager_notify_screen_woke(void) {
    notify_event_no_args(PLUGIN_EVENT_SCREEN_WOKE, "screen_woke");
}

void plugin_manager_interval_fired(int slot) {
    if (slot < 0 || slot >= PLUGIN_MAX_INTERVALS || !plugin_intervals[slot].active) return;

    lua_State * L = plugin_intervals[slot].L;
    lua_rawgeti(L, LUA_REGISTRYINDEX, plugin_intervals[slot].ref);
    if (plugin_call(L, 0, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(L, -1);
        fprintf(stderr, "[plugins] set_interval callback error: %s\n", err ? err : "unknown error");
        lua_pop(L, 1);
    }
}

void plugin_manager_text_input_submitted(const char * text) {
    if (!pending_text_input_L || pending_text_input_ref == LUA_NOREF) return;

    lua_State * L = pending_text_input_L;
    int ref = pending_text_input_ref;
    pending_text_input_L = NULL;
    pending_text_input_ref = LUA_NOREF;

    lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
    lua_pushstring(L, text ? text : "");
    if (plugin_call(L, 1, 0, 0) != LUA_OK) {
        const char * err = lua_tostring(L, -1);
        fprintf(stderr, "[plugins] show_text_input on_submit error: %s\n", err ? err : "unknown error");
        lua_pop(L, 1);
    }
    luaL_unref(L, LUA_REGISTRYINDEX, ref);
}

void plugin_manager_text_input_cancelled(void) {
    if (!pending_text_input_L || pending_text_input_ref == LUA_NOREF) return;
    luaL_unref(pending_text_input_L, LUA_REGISTRYINDEX, pending_text_input_ref);
    pending_text_input_L = NULL;
    pending_text_input_ref = LUA_NOREF;
}
EOF
