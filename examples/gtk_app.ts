class Widget {
  handle: Pointer;
  constructor(h: Pointer) {
    this.handle = h;
  }
}
//comment
extern "C" {
  function gtk_app_init(): void;
  function gtk_app_window_new(title: Pointer): Pointer;
  function gtk_app_box_new(horizontal: number): Pointer;
  function gtk_app_label_new(text: Pointer): Pointer;
  function gtk_app_button_new(text: Pointer): Pointer;
  function gtk_app_box_pack(box_: Pointer, child: Pointer, expand: number, fill: number, padding: number): void;
  function gtk_app_container_add(container: Pointer, child: Pointer): void;
  function gtk_app_button_on_click(button: Pointer): void;
  function gtk_app_button_on_quit(button: Pointer): void;
  function gtk_app_widget_show(widget: Pointer): void;
  function gtk_app_main(): void;
  function gtk_app_get_click_count(): number;
}

function main(): number {
  unsafe { gtk_app_init(); }

  let win = new Widget(unsafe { gtk_app_window_new(std.toCString("Nexa GTK App")) });
  let vbox = new Widget(unsafe { gtk_app_box_new(0) });

  let title = new Widget(unsafe { gtk_app_label_new(std.toCString("Hello from Nexa!")) });
  let counter = new Widget(unsafe { gtk_app_label_new(std.toCString("No clicks yet")) });
  let click_btn = new Widget(unsafe { gtk_app_button_new(std.toCString("Click Me")) });
  let quit_btn = new Widget(unsafe { gtk_app_button_new(std.toCString("Quit")) });

  unsafe { gtk_app_button_on_click(click_btn.handle); }
  unsafe { gtk_app_button_on_quit(quit_btn.handle); }

  unsafe { gtk_app_box_pack(vbox.handle, title.handle, 0, 0, 0); }
  unsafe { gtk_app_box_pack(vbox.handle, counter.handle, 0, 0, 0); }
  unsafe { gtk_app_box_pack(vbox.handle, click_btn.handle, 0, 0, 0); }
  unsafe { gtk_app_box_pack(vbox.handle, quit_btn.handle, 0, 0, 0); }

  unsafe { gtk_app_container_add(win.handle, vbox.handle); }
  unsafe { gtk_app_widget_show(win.handle); }

  unsafe { gtk_app_main(); }

  std.log(1);
  return 0;
}