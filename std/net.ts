// Bundled stdlib module: network group (std/net).
//
// Every export is a thin extern "C" wrapper over the matching nexa_net_*
// runtime helper, which performs the raw libc syscall (socket/bind/...).
// This file ships inside the nexa binary and is reached through the reserved
// `std/` import prefix: `import * as net from "std/net";`.
//
// It is NOT a parser-reserved intrinsic set anymore: the old std.net.* names
// no longer exist in the compiler's std reservoir. Programs that want the
// network helpers must import this module (or declare the libc externs
// directly, like examples/http_server/server.ts does).

extern "C" {
  function nexa_net_sockaddr_in(port: number, addr: number): Pointer;
  function nexa_net_socket(domain: number, ctype: number, protocol: number): number;
  function nexa_net_setsockopt(fd: number, level: number, option: number, value: Pointer, length: number): number;
  function nexa_net_bind(fd: number, addr: Pointer, len: number): number;
  function nexa_net_listen(fd: number, backlog: number): number;
  function nexa_net_accept(fd: number): number;
  function nexa_net_recv(fd: number, buf: Pointer, n: number, flags: number): number;
  function nexa_net_send(fd: number, buf: Pointer, n: number, flags: number): number;
  function nexa_net_close(fd: number): number;
}

export function sockaddrIn(port: number, addr: number): Pointer {
  return unsafe { nexa_net_sockaddr_in(port, addr) };
}

export function socket(domain: number, ctype: number, protocol: number): number {
  return unsafe { nexa_net_socket(domain, ctype, protocol) };
}

export function setSockOpt(fd: number, level: number, option: number, value: Pointer, length: number): number {
  return unsafe { nexa_net_setsockopt(fd, level, option, value, length) };
}

export function bind(fd: number, addr: Pointer, len: number): number {
  return unsafe { nexa_net_bind(fd, addr, len) };
}

export function listen(fd: number, backlog: number): number {
  return unsafe { nexa_net_listen(fd, backlog) };
}

export function accept(fd: number): number {
  return unsafe { nexa_net_accept(fd) };
}

export function recv(fd: number, buf: Pointer, n: number, flags: number): number {
  return unsafe { nexa_net_recv(fd, buf, n, flags) };
}

export function send(fd: number, buf: Pointer, n: number, flags: number): number {
  return unsafe { nexa_net_send(fd, buf, n, flags) };
}

export function close(fd: number): number {
  return unsafe { nexa_net_close(fd) };
}
