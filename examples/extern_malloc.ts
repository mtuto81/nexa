// extern_malloc.ts — extern "C" FFI acceptance test
// Verifies: Pointer type, unsafe blocks, libc malloc/free linking.

extern "C" {
  function malloc(size: number): Pointer;
  function free(ptr: Pointer): void;
}

function main(): number {
  let p: Pointer = unsafe { malloc(64) };
  unsafe { free(p); }
  console.log(1);
  return 0;
}
