// gtk_app_callbacks.c — Minimal GTK callback stubs for gtk_app_pure.ts
//
// Nexa cannot produce C-compatible function pointers, so GTK signal
// callbacks must live in C.  This file is the thinnest possible bridge:
// it holds no app logic — just the callback shells that GTK demands.

#include <gtk/gtk.h>
#include <stdio.h>

static GtkWidget *g_label = NULL;
static int g_counter = 0;

// Called from Nexa after creating the label widget.
void register_label(GtkWidget *label) { g_label = label; }

// "Click Me" button callback — increments counter, updates the label.
void on_click_me(GtkWidget *widget, gpointer data) {
    (void)widget; (void)data;
    g_counter++;
    char buf[64];
    snprintf(buf, sizeof(buf), "Clicked %d times", g_counter);
    gtk_label_set_text(GTK_LABEL(g_label), buf);
}

// "Quit" button callback — also usable for window "destroy" signal.
void on_quit(GtkWidget *widget, gpointer data) {
    (void)widget; (void)data;
    gtk_main_quit();
}
