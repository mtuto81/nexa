// Bundled synchronous filesystem module for native command-line programs.
// Binary data is the default; use readTextFile/writeTextFile for text.

extern "C" {
  function nexa_fs_read_file(path: Pointer): Pointer;
  function nexa_fs_read_file_len(path: Pointer): number;
  function nexa_fs_write_file(path: Pointer, data: Pointer, len: number, append: number): number;
  function nexa_fs_exists(path: Pointer): number;
  function free(ptr: Pointer): void;
}

export class Buffer {
  data: Pointer;
  length: number;
  constructor(p: Pointer, n: number) {
    this.data = p;
    this.length = n;
  }
}

export function readFile(path: string): Buffer {
  if (!exists(path)) { return new Buffer(0, 0); }
  let cpath: Pointer = std.toCString(path);
  let raw: Pointer = unsafe { nexa_fs_read_file(cpath) };
  let length: number = unsafe { nexa_fs_read_file_len(cpath) };
  return new Buffer(raw, length);
}

export function freeBuffer(buffer: Buffer): void {
  unsafe { free(buffer.data); }
}

export function writeFile(path: string, data: Buffer): number {
  return unsafe { nexa_fs_write_file(std.toCString(path), data.data, data.length, 0) };
}

export function appendFile(path: string, data: Buffer): number {
  return unsafe { nexa_fs_write_file(std.toCString(path), data.data, data.length, 1) };
}

export function readTextFile(path: string): string {
  let buffer: Buffer = readFile(path);
  let text: string = std.fromCString(buffer.data, buffer.length);
  freeBuffer(buffer);
  return text;
}

export function writeTextFile(path: string, data: string): number {
  return unsafe { nexa_fs_write_file(std.toCString(path), std.toCString(data), std.strlen(data), 0) };
}

export function appendTextFile(path: string, data: string): number {
  return unsafe { nexa_fs_write_file(std.toCString(path), std.toCString(data), std.strlen(data), 1) };
}

export function exists(path: string): boolean {
  return unsafe { nexa_fs_exists(std.toCString(path)) } != 0;
}
