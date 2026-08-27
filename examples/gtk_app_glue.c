/*
 * gtk_app_glue.c — Thin C bridge between Nexa and GTK3.
 *
 * All GTK callback wiring lives here. Nexa calls these functions via
 * extern "C", passing opaque Pointer handles obtained from these
 * same functions. No function pointers cross the FFI boundary.
 *
 * Build:
 *   gcc -shared -fPIC -o gtk_app_glue.o gtk_app_glue.c $(pkg-config --cflags --libs gtk+-3.0)
 */
#include <gtk/gtk.h>
#include <stdio.h>

/* ── internal state ────────────────────────────────────────────── */
static GtkWidget *g_label   = NULL;
static int        g_clicks  = 0;

/* ── callbacks (all in C, never exposed to Nexa) ───────────────── */
static void on_destroy(GtkWidget *w, gpointer d) {
    (void)w; (void)d;
    gtk_main_quit();
}

static void on_button_click(GtkButton *btn, gpointer d) {
    (void)btn; (void)d;
    g_clicks++;
    char buf[80];
    snprintf(buf, sizeof buf, "Clicked %d time%s!", g_clicks, g_clicks == 1 ? "" : "s");
    gtk_label_set_text(GTK_LABEL(g_label), buf);
}

static void on_quit(GtkButton *btn, gpointer d) {
    (void)btn; (void)d;
    gtk_main_quit();
}

/* ── public API consumed by Nexa extern "C" ────────────────────── */

void gtk_app_init(void) {
    gtk_init(NULL, NULL);
}

/* window --------------------------------------------------------- */
void *gtk_app_window_new(const char *title) {
    GtkWidget *w = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title(GTK_WINDOW(w), title);
    gtk_window_set_default_size(GTK_WINDOW(w), 360, 240);
    g_signal_connect(w, "destroy", G_CALLBACK(on_destroy), NULL);
    return (void *)w;
}

/* layout --------------------------------------------------------- */
void *gtk_app_box_new(int horizontal) {
    GtkOrientation o = horizontal ? GTK_ORIENTATION_HORIZONTAL
                                  : GTK_ORIENTATION_VERTICAL;
    return (void *)gtk_box_new(o, 8);
}

void gtk_app_box_pack(void *box_, void *child,
                      int expand, int fill, int padding) {
    gtk_box_pack_start(GTK_BOX(box_), GTK_WIDGET(child),
                       expand, fill, padding);
}

void gtk_app_container_add(void *container, void *child) {
    gtk_container_add(GTK_CONTAINER(container), GTK_WIDGET(child));
}

/* widgets -------------------------------------------------------- */
void *gtk_app_label_new(const char *text) {
    g_label = gtk_label_new(text);
    return (void *)g_label;
}

void *gtk_app_button_new(const char *text) {
    return (void *)gtk_button_new_with_label(text);
}

void gtk_app_button_on_click(void *button) {
    g_signal_connect(button, "clicked", G_CALLBACK(on_button_click), NULL);
}

void gtk_app_button_on_quit(void *button) {
    g_signal_connect(button, "clicked", G_CALLBACK(on_quit), NULL);
}

/* display -------------------------------------------------------- */
void gtk_app_widget_show(void *widget) {
    gtk_widget_show_all(GTK_WIDGET(widget));
}

/* main loop ------------------------------------------------------ */
void gtk_app_main(void) {
    gtk_main();
}

int gtk_app_get_click_count(void) {
    return g_clicks;
}
