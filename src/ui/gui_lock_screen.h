#ifndef GUI_LOCK_SCREEN_H
#define GUI_LOCK_SCREEN_H

#include <lvgl/lvgl.h>
#include <stdbool.h>

typedef enum {
    LOCK_SCREEN_MODE_OFF = 0,
    LOCK_SCREEN_MODE_ALBUM_ART,
    LOCK_SCREEN_MODE_IMAGE,
    LOCK_SCREEN_MODE_CLOCK,
} gui_lock_screen_mode_t;

typedef struct {
    gui_lock_screen_mode_t mode;
    char image_path[256];
    bool clock_24h;
} gui_lock_screen_options_t;

lv_obj_t * gui_lock_screen_get_screen(void);
bool gui_lock_screen_is_showing(void);
bool gui_lock_screen_show(const gui_lock_screen_options_t * options);
void gui_lock_screen_hide(void);
void gui_lock_screen_init(void);
void gui_lock_screen_teardown(void);
void gui_lock_screen_reset_drag_state(void);
void gui_lock_screen_swipe_recover(void * ctx);

#endif /* GUI_LOCK_SCREEN_H */
