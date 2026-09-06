// Bundled stdlib module: process group (std/process).
//
// Wraps fork/wait/exit as plain extern "C" calls (mirroring how the old
// std.process.* intrinsics behaved). This ships inside the nexa binary and is
// reached through the reserved `std/` import prefix:
// `import * as process from "std/process";`.
//
// exec1/exec2 and the pipe trio (pipe/pipeReadFd/pipeWriteFd) remain
// compiler-baked std.process.* intrinsics.

extern "C" {
  function nexa_process_fork(): number;
  function nexa_process_wait(pid: number): number;
  function nexa_process_exit(code: number): void;
}

export function fork(): number {
  return unsafe { nexa_process_fork() };
}

export function wait(pid: number): number {
  return unsafe { nexa_process_wait(pid) };
}

export function exit(code: number): void {
  unsafe { nexa_process_exit(code); }
}