// Bundled stdlib module: native memory allocation (std/mem).
//
// The exported names are intentionally alloc/dealloc. The underlying libc
// symbols remain malloc/free, while Nexa code gets a small typed module API:
// `import * as mem from "std/mem";`.

extern "C" {
  function malloc(size: number): Pointer;
  function free(ptr: Pointer): void;
}

export function alloc(size: number): Pointer {
  return unsafe { malloc(size) };
}

export function dealloc(ptr: Pointer): void {
  unsafe { free(ptr); }
}
