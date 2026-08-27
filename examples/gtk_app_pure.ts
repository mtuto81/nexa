// gtk_app_pure.ts — GTK3 app using Nexa's extern "C" directly (no C wrapper).
//
// All GTK calls go through extern "C" declarations. The only trick is using
// dlsym to resolve C function pointers (like gtk_main_quit) at runtime,
// since Nexa cannot create or pass function pointers across the FFI.
//
// Parameters that receive NULL are declared as `number` rather than `Pointer`
// because Nexa numeric literals (0) are type `Number`. At the ABI level both
// are i64, so this is safe and has no runtime effect.

class Widget {
  handle: Pointer;
  constructor(h: Pointer) {
    this.handle = h;
  }
}

extern "C" {
  // dlsym: resolve a C symbol by name at runtime.
  // Pass handle = 0 (RTLD_DEFAULT) to search all loaded shared libraries.
  function dlsym(handle: number, symbol: Pointer): Pointer;

  // GLib signal connection (g_signal_connect is a C macro; this is the real function)
  function g_signal_connect_data(instance: Pointer, signal: Pointer,
      handler: Pointer, data: number, destroy: number, flags: number): number;

  // GTK lifecycle
  function gtk_init(argc: number, argv: number): void;
  function gtk_main(): void;
  function gtk_main_quit(): void;

  // Windows
  function gtk_window_new(type_: number): Pointer;
  function gtk_window_set_title(window: Pointer, title: Pointer): void;
  function gtk_window_set_default_size(window: Pointer, w: number, h: number): void;

  // Widgets
  function gtk_widget_show_all(widget: Pointer): void;
  function gtk_label_new(text: Pointer): Pointer;
  function gtk_button_new_with_label(label: Pointer): Pointer;

  // Layout
  function gtk_box_new(orientation: number, spacing: number): Pointer;
  function gtk_box_pack_start(box_: Pointer, child: Pointer,
      expand: number, fill: number, padding: number): void;
  function gtk_container_add(container: Pointer, child: Pointer): void;
}

function main(): number {
  // Init GTK. Passing 0 (NULL) for argc/argv.
  unsafe { gtk_init(0, 0); }

  // Resolve gtk_main_quit as a C function pointer via dlsym.
  // This is the only way to get a C function pointer into Nexa —
  // we look it up by name in the process's loaded symbols.
  let quit_fn = unsafe { dlsym(0, std.toCString("gtk_main_quit")) };

  // Create window (type 0 = GTK_WINDOW_TOPLEVEL).
  let win = new Widget(unsafe { gtk_window_new(0) });
  unsafe { gtk_window_set_title(win.handle, std.toCString("Nexa GTK App")); }
  unsafe { gtk_window_set_default_size(win.handle, 400, 300); }

  // Wire the window's "destroy" signal to gtk_main_quit.
  // g_signal_connect_data(instance, signal, handler, data, destroy, flags)
  // data=0 and destroy=0 are NULL pointers (no extra data, no closure notify).
  unsafe {
    g_signal_connect_data(
      win.handle,
      std.toCString("destroy"),
      quit_fn, 0, 0, 0
    );
  }

  // Layout: vertical box with spacing.
  let vbox = new Widget(unsafe { gtk_box_new(1, 12) });

  // Label.
  let label = new Widget(unsafe { gtk_label_new(std.toCString("Hello from Nexa!")) });
  unsafe { gtk_box_pack_start(vbox.handle, label.handle, 0, 0, 0); }

  // Buttons.
  let click_btn = new Widget(unsafe { gtk_button_new_with_label(std.toCString("Click Me")) });
  unsafe { gtk_box_pack_start(vbox.handle, click_btn.handle, 0, 0, 0); }

  let quit_btn = new Widget(unsafe { gtk_button_new_with_label(std.toCString("Quit")) });
  unsafe { gtk_box_pack_start(vbox.handle, quit_btn.handle, 0, 0, 0); }

  // Wire "clicked" on Quit button to gtk_main_quit as well.
  // The callback receives (button_instance, user_data) in registers that
  // gtk_main_quit ignores — safe at the ABI level on x86_64.
  unsafe {
    g_signal_connect_data(
      quit_btn.handle,
      std.toCString("clicked"),
      quit_fn, 0, 0, 0
    );
  }

  // Assemble the widget tree and show everything.
  unsafe { gtk_container_add(win.handle, vbox.handle); }
  unsafe { gtk_widget_show_all(win.handle); }

  // Enter the GTK main loop. Blocks until the window is destroyed.
  unsafe { gtk_main(); }

  std.log(1);
  return 0;
}
