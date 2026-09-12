#include "gui_lock_screen.h"
#include "gui_navigation.h"
#include "gui_shell.h"
#include "gui_theme.h"
#include "gui_player.h"
#include "app_clock.h"
#include "assets.h"
#include "screen_builders.h"
#include "backlight.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static lv_obj_t * lock_screen = NULL;
static lv_obj_t * lock_image_obj = NULL;
static lv_obj_t * lock_clock_label = NULL;
static lv_timer_t * lock_clock_timer = NULL;
static lv_timer_t * lock_touch_timer = NULL;

static gui_lock_screen_mode_t current_mode = LOCK_SCREEN_MODE_OFF;
static bool current_clock_24h = true;

static void stop_timers(void);

/* Live swipe-up-to-dismiss tracking. This deliberately mirrors the existing
 * Home swipe in gui_shell.c: the transition is created once at the deadzone,
 * the finger drives its position every poll tick, and release gets a short
 * ease-out settle instead of waiting for a gesture event and then starting a
 * fresh animation. */
static bool lock_swipe_candidate = false;
static bool lock_swipe_tracking = false;
static bool lock_swipe_just_confirmed = false;
static int32_t lock_swipe_touch_start_y = 0;
static int32_t lock_swipe_last_v = 0;
static int32_t lock_swipe_last_velocity = 0;
static slide_transition_ctx_t * lock_swipe_ctx = NULL;
#define LOCK_SWIPE_DEADZONE 20
#define LOCK_SWIPE_SETTLE_MS 120

lv_obj_t * gui_lock_screen_get_screen(void) {
    return lock_screen;
}

bool gui_lock_screen_is_showing(void) {
    return lock_screen != NULL && lv_screen_active() == lock_screen;
}

static void lock_image_opa_anim_cb(void * obj, int32_t value) {
    lv_obj_set_style_opa((lv_obj_t *) obj, (lv_opa_t) value, 0);
}

static void animate_custom_lock_image(void) {
    if (!lock_image_obj) return;

    /* Custom images are decoded from the SD card when lv_image_set_src() is
     * called, so unlike album art they can already be fully visible by the
     * time nav_push() begins its screen transition. Fade the image in over
     * the opening transition so it does not pop onto the screen instantly.
     */
    lv_anim_del(lock_image_obj, lock_image_opa_anim_cb);
    lv_obj_set_style_opa(lock_image_obj, 0, 0);

    lv_anim_t anim;
    lv_anim_init(&anim);
    lv_anim_set_var(&anim, lock_image_obj);
    lv_anim_set_values(&anim, 0, LV_OPA_COVER);
    lv_anim_set_duration(&anim, 180);
    lv_anim_set_exec_cb(&anim, lock_image_opa_anim_cb);
    lv_anim_start(&anim);
}

static void update_clock_display(void) {
    if (!lock_clock_label) return;
    struct tm tm_info;
    app_clock_localtime(&tm_info);
    char buf[16];
    strftime(buf, sizeof(buf), current_clock_24h ? "%H:%M" : "%I:%M", &tm_info);
    lv_label_set_text(lock_clock_label, buf);


}

static void lock_clock_timer_cb(lv_timer_t * timer) {
    (void) timer;
    update_clock_display();
}

static void lock_touch_timer_cb(lv_timer_t * timer) {
    (void) timer;
    if (!gui_lock_screen_is_showing()) return;
    if (!backlight_screen_is_on()) return;

    lv_indev_t * indev = find_pointer_indev();
    if (!indev) return;

    bool pressed = (lv_indev_get_state(indev) == LV_INDEV_STATE_PRESSED);
    lv_point_t p;
    lv_indev_get_point(indev, &p);
    int32_t h = lv_display_get_vertical_resolution(lv_display_get_default());

    if (pressed && !lock_swipe_candidate && !lock_swipe_tracking) {
        lock_swipe_candidate = true;
        lock_swipe_touch_start_y = p.y;
        lock_swipe_last_v = 0;
        lock_swipe_last_velocity = 0;
    }

    if (pressed && lock_swipe_candidate && !lock_swipe_tracking) {
        int32_t dy = p.y - lock_swipe_touch_start_y;
        int32_t ady = dy < 0 ? -dy : dy;

        if (ady >= LOCK_SWIPE_DEADZONE) {
            /* Only an upward, predominantly vertical drag dismisses the lock
             * screen. A horizontal/ downward movement is rejected for this
             * press so taps and other input are not stolen. */
            if (dy < 0) {
                lv_obj_t * target = NULL;
                int depth = gui_navigation_get_depth();
                if (depth > 1)
                    target = gui_navigation_get_screen_at(depth - 2);

                if (target) {
                    lock_swipe_ctx = begin_slide_transition_ex(
                        target, true, true, true);
                    if (lock_swipe_ctx) {
                        /* Do not change the nav stack until release. A
                         * cancelled drag therefore returns to the lock screen
                         * without disturbing navigation history. */
                        lock_swipe_ctx->commit = false;
                        lock_swipe_tracking = true;
                        lock_swipe_just_confirmed = true;
                        lock_swipe_last_v = 0;
                        lock_swipe_last_velocity = 0;

                        /* The transition overlay is now directly under the
                         * still-down finger. Keep the eventual release from
                         * being delivered to whatever is exposed underneath. */
                        lv_indev_wait_release(indev);
                    }
                }
            } else {
                /* Once the movement is horizontal/downward, stop considering
                 * this press a lock-screen swipe. */
                lv_indev_wait_release(indev);
            }
            lock_swipe_candidate = false;
        }
    }

    if (pressed && lock_swipe_tracking) {
        int32_t v = p.y - lock_swipe_touch_start_y;
        if (v > 0) v = 0;
        if (v < -h) v = -h;

        int32_t delta = v - lock_swipe_last_v;
        if (delta != 0) lock_swipe_last_velocity = delta;
        lock_swipe_last_v = v;

        /* The first tick after begin_slide_transition_ex() is deliberately
         * skipped. The transition setup can take long enough that presenting
         * frame 0 in that same tick produces the exact start-of-swipe hitch
         * seen in the old implementation. */
        if (lock_swipe_just_confirmed) {
            lock_swipe_just_confirmed = false;
        } else if (lock_swipe_ctx) {
            slide_transition_anim_x_cb(lock_swipe_ctx, v);
        }
    }

    if (!pressed && lock_swipe_tracking && lock_swipe_ctx) {
        lock_swipe_tracking = false;
        lock_swipe_candidate = false;

        int32_t current_v = lock_swipe_last_v;
        bool commit;
        if (lock_swipe_last_velocity < 0) {
            commit = true;
        } else if (lock_swipe_last_velocity > 0) {
            commit = false;
        } else {
            commit = current_v < -h / 2;
        }

        slide_transition_ctx_t * ctx = lock_swipe_ctx;
        ctx->commit = commit;

        if (commit) {
            /* Keep the navigation stack unchanged until the settle animation
             * finishes, exactly like gui_shell.c's live Home swipe. */
            nav_pop_stack_only();
            stop_timers();
        }

        lv_anim_t a;
        lv_anim_init(&a);
        lv_anim_set_var(&a, ctx);
        lv_anim_set_user_data(&a, ctx);
        lv_anim_set_values(&a, current_v, commit ? -h : 0);
        lv_anim_set_duration(&a, LOCK_SWIPE_SETTLE_MS);
        lv_anim_set_exec_cb(&a, slide_transition_anim_x_cb);
        lv_anim_set_completed_cb(&a, slide_transition_done_cb);
        lv_anim_set_path_cb(&a, lv_anim_path_ease_out);
        lv_anim_start(&a);
        lock_swipe_ctx = NULL;
    }
}

static void start_timers(void) {
    /* Symmetric, not just a conditional start -- gui_lock_screen_show() can
     * be called again with a DIFFERENT mode while already showing (e.g. a
     * second screen_woke fires before the user dismisses), and this must
     * leave lock_clock_timer matching the NEW mode either way. A one-sided
     * "start if clock" here previously left a stale timer running forever
     * (until the eventual hide/teardown) after switching away from clock
     * mode without an intervening hide(). */
    if (current_mode == LOCK_SCREEN_MODE_CLOCK ||
        current_mode == LOCK_SCREEN_MODE_IMAGE ||
        current_mode == LOCK_SCREEN_MODE_ALBUM_ART) {
        if (!lock_clock_timer) {
            lock_clock_timer = lv_timer_create(lock_clock_timer_cb, 1000, NULL);
        }
    } else if (lock_clock_timer) {
        lv_timer_delete(lock_clock_timer);
        lock_clock_timer = NULL;
    }
    if (!lock_touch_timer) {
        lock_touch_timer = lv_timer_create(lock_touch_timer_cb, 20, NULL);
    }
}

static void stop_timers(void) {
    if (lock_clock_timer) {
        lv_timer_delete(lock_clock_timer);
        lock_clock_timer = NULL;
    }
    if (lock_touch_timer) {
        lv_timer_delete(lock_touch_timer);
        lock_touch_timer = NULL;
    }
    gesture_home_state_reset(&lock_gesture_state);
}

static void build_lock_screen_if_needed(void) {
    if (lock_screen) return;

    lock_screen = lv_obj_create(NULL);
    lv_obj_add_style(lock_screen, &style_theme_screen_bg, 0);
    lv_obj_remove_flag(lock_screen, LV_OBJ_FLAG_SCROLLABLE);

    lock_image_obj = lv_image_create(lock_screen);
    lv_obj_align(lock_image_obj, LV_ALIGN_CENTER, 0, 0);
    lv_obj_add_flag(lock_image_obj, LV_OBJ_FLAG_HIDDEN);

    lock_clock_label = lv_label_create(lock_screen);
    lv_obj_add_style(lock_clock_label, &style_theme_text_primary, 0);
    lv_obj_set_style_text_align(lock_clock_label, LV_TEXT_ALIGN_CENTER, 0);
    lv_obj_set_style_text_font(lock_clock_label, gui_theme_font(GUI_FONT_ROLE_TITLE), 0);
    lv_obj_align(lock_clock_label, LV_ALIGN_CENTER, 0, 0);
    lv_obj_add_flag(lock_clock_label, LV_OBJ_FLAG_HIDDEN);
}

bool gui_lock_screen_show(const gui_lock_screen_options_t * options) {
    if (!options || options->mode == LOCK_SCREEN_MODE_OFF) {
        return false;
    }

    build_lock_screen_if_needed();

    current_mode = options->mode;
    current_clock_24h = options->clock_24h;
    /* Reset elements */
    lv_anim_del(lock_image_obj, lock_image_opa_anim_cb);
    lv_obj_set_style_opa(lock_image_obj, LV_OPA_COVER, 0);
    lv_obj_add_flag(lock_image_obj, LV_OBJ_FLAG_HIDDEN);
    lv_obj_add_flag(lock_clock_label, LV_OBJ_FLAG_HIDDEN);

    if (current_mode == LOCK_SCREEN_MODE_ALBUM_ART) {
        const lv_image_dsc_t * cover = gui_player_get_current_cover_dsc();
        /* Start from the image's natural/content size so we can read its
         * loaded dimensions using the object itself. This avoids newer LVGL
         * helper APIs that are not linked into the R1 firmware. */
        lv_obj_set_size(lock_image_obj, LV_SIZE_CONTENT, LV_SIZE_CONTENT);
        lv_obj_set_align(lock_image_obj, LV_ALIGN_CENTER);
        lv_image_set_inner_align(lock_image_obj, LV_IMAGE_ALIGN_DEFAULT);
        lv_image_set_scale(lock_image_obj, 256);

        if (cover && cover->data) {
            lv_image_set_src(lock_image_obj, cover);
        } else {
            lv_image_set_src(lock_image_obj, asset_path("playing_plane/default_cover_565.png"));
        }

        /* lv_image_set_src() only marks the content-sized object's layout
         * dirty (lv_obj_refresh_self_size() -> lv_obj_mark_layout_as_dirty());
         * the actual resize is deferred to the next layout pass. Force it now
         * so the lv_obj_get_width/height() calls below see this image's real
         * natural size instead of stale (often zero, on first show) coords --
         * same fix already applied for this exact LVGL behavior elsewhere in
         * this codebase (gui_lyrics.c, gui_shell.c, gui_library.c). */
        lv_obj_update_layout(lock_image_obj);

        /* Album art should behave like a full-screen wallpaper: make the
         * image widget cover the whole lock screen while preserving the
         * artwork's aspect ratio. The R1's LVGL build does not provide
         * LV_IMAGE_ALIGN_COVER or the newer get-src-dimensions helpers, so
         * use the natural size reported by the image object and calculate
         * the equivalent zoom manually. The larger scale factor is used so
         * the image completely covers the screen; the excess is cropped by
         * the image object's full-screen bounds. */
        int32_t image_w = lv_obj_get_width(lock_image_obj);
        int32_t image_h = lv_obj_get_height(lock_image_obj);
        int32_t screen_w = lv_obj_get_width(lock_screen);
        int32_t screen_h = lv_obj_get_height(lock_screen);
        uint32_t cover_scale = 256;

        if (image_w > 0 && image_h > 0 && screen_w > 0 && screen_h > 0) {
            uint32_t scale_x = ((uint32_t) screen_w * 256U + (uint32_t) image_w - 1U) / (uint32_t) image_w;
            uint32_t scale_y = ((uint32_t) screen_h * 256U + (uint32_t) image_h - 1U) / (uint32_t) image_h;
            cover_scale = scale_x > scale_y ? scale_x : scale_y;
        }

        lv_obj_set_size(lock_image_obj, LV_PCT(100), LV_PCT(100));
        lv_obj_set_align(lock_image_obj, LV_ALIGN_CENTER);
        lv_image_set_inner_align(lock_image_obj, LV_IMAGE_ALIGN_CENTER);
        lv_image_set_scale(lock_image_obj, cover_scale);

        lv_obj_remove_flag(lock_image_obj, LV_OBJ_FLAG_HIDDEN);
        update_clock_display();
        lv_obj_remove_flag(lock_clock_label, LV_OBJ_FLAG_HIDDEN);
    } else if (current_mode == LOCK_SCREEN_MODE_IMAGE) {
        /* LVGL's lv_fs_get_drv() picks a driver off src[0] -- a plain POSIX
         * path (what plugin.sd_root() and every plugin-supplied path use)
         * has no registered driver (only the 'S' POSIX driver is, see
         * lv_conf.h), so lv_fs_open() fails silently and the image never
         * loads without this prefix. Same "S:" convention every other
         * file-path image source in this codebase uses (assets.c's
         * asset_path()). lv_image_set_src() strdup()s file-path sources
         * internally, so this stack buffer doesn't need to outlive the call. */
        char prefixed_path[sizeof(options->image_path) + 2];
        snprintf(prefixed_path, sizeof(prefixed_path), "S:%s", options->image_path);
        lv_image_set_src(lock_image_obj, prefixed_path);

        /* Custom images keep their existing natural/content-sized behavior.
         * Only Album Art is treated as a full-screen cover. Reset the image
         * scale here so the previous album-art scale cannot carry over. */
        lv_obj_set_size(lock_image_obj, LV_SIZE_CONTENT, LV_SIZE_CONTENT);
        lv_obj_set_align(lock_image_obj, LV_ALIGN_CENTER);
        lv_image_set_inner_align(lock_image_obj, LV_IMAGE_ALIGN_DEFAULT);
        lv_image_set_scale(lock_image_obj, 256);

        lv_obj_remove_flag(lock_image_obj, LV_OBJ_FLAG_HIDDEN);
        update_clock_display();
        lv_obj_remove_flag(lock_clock_label, LV_OBJ_FLAG_HIDDEN);
    } else if (current_mode == LOCK_SCREEN_MODE_CLOCK) {
        update_clock_display();
        lv_obj_remove_flag(lock_clock_label, LV_OBJ_FLAG_HIDDEN);
    }

    start_timers();

    bool opening = (lv_screen_active() != lock_screen);
    if (opening) {
        nav_push(lock_screen);

        if (current_mode == LOCK_SCREEN_MODE_IMAGE) {
            animate_custom_lock_image();
        }
    }

    return true;
}

/* Dismissal is a swipe-up gesture (see lock_touch_timer_cb() above), so it
 * plays the same "swipe up to reveal" transition as swipe-up-to-Home
 * (gui_shell.c's home-swipe): forward=true, vertical=true, reveal=true --
 * the underlying screen stays fixed in place, revealed as the lock screen
 * slides up and away over it, rather than a plain horizontal back-slide. */
void gui_lock_screen_hide(void) {
    stop_timers();
    lock_swipe_candidate = false;
    lock_swipe_tracking = false;
    lock_swipe_just_confirmed = false;
    if (lock_swipe_ctx) {
        slide_transition_cancel(&lock_swipe_ctx);
    }
    if (lock_screen && lv_screen_active() == lock_screen) {
        nav_pop_ex(true, true, true);
    }
}

/* Called by gui_navigation.c if the shared transition compositor reports a
 * hard presentation failure while a lock-screen swipe is in flight. The
 * navigation layer restores the logical source/destination screen before
 * freeing the transition context; all we need to do here is drop our stale
 * tracking pointer so it can never be driven after that free. */
void gui_lock_screen_swipe_recover(void * ctx) {
    if (ctx == (void *) lock_swipe_ctx) lock_swipe_ctx = NULL;
    lock_swipe_tracking = false;
    lock_swipe_candidate = false;
    lock_swipe_just_confirmed = false;
    lock_swipe_last_v = 0;
    lock_swipe_last_velocity = 0;
}

void gui_lock_screen_init(void) {
    lock_screen = NULL;
    lock_image_obj = NULL;
    lock_clock_label = NULL;
    lock_clock_timer = NULL;
    lock_touch_timer = NULL;
    current_mode = LOCK_SCREEN_MODE_OFF;
    lock_swipe_candidate = false;
    lock_swipe_tracking = false;
    lock_swipe_just_confirmed = false;
    lock_swipe_touch_start_y = 0;
    lock_swipe_last_v = 0;
    lock_swipe_last_velocity = 0;
    lock_swipe_ctx = NULL;
}

/* Called from gui_soft_reload() (gui_reload.c), after gui_navigation_teardown()
 * has already zeroed nav_stack/nav_depth -- calling nav_pop() here (as an
 * earlier version of this function did) would read nav_stack[-1], the exact
 * out-of-bounds class of crash already found and fixed once in this reload
 * path for the Plugin Manager. A reload rebuilds the whole screen stack from
 * scratch (gui_navigation_init() loads Home again further down the same
 * sequence), so the lock screen doesn't need to navigate anywhere on its way
 * out -- it only needs to release its own owned resources. */
void gui_lock_screen_teardown(void) {
    stop_timers();
    if (lock_screen) {
        lv_obj_delete(lock_screen);
    }
    gui_lock_screen_init();
}