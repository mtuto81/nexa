// Minimal native HTTP/1.1 client using Nexa's bundled std/net module.
//
// It connects to the pure-Nexa example server at 127.0.0.1:5000, sends one
// GET request, reads the response, and returns it as a Nexa string. This is
// intentionally a small blocking client: no TLS, redirects, chunked decoding,
// or asynchronous I/O are part of this example.

import * as net from "std/net";

extern "C" {
  function connect(fd: number, addr: Pointer, len: number): number;
  function malloc(size: number): Pointer;
  function free(ptr: Pointer): void;
}

function httpGet(path: string): string {
  let fd: number = net.socket(2, 1, 0); // AF_INET, SOCK_STREAM
  let address: Pointer = net.sockaddrIn(5000, 2130706433); // 127.0.0.1
  let connected: number = unsafe { connect(fd, address, 16) };
  if (connected < 0) {
    net.close(fd);
    return "connect failed";
  }

  let request: string = "GET " + path + " HTTP/1.1\r\n"
    + "Host: localhost\r\n"
    + "Connection: close\r\n"
    + "\r\n";
  unsafe { net.send(fd, std.toCString(request), std.strlen(request), 0); }

  let buffer: Pointer = unsafe { malloc(8192) };
  let count: number = unsafe { net.recv(fd, buffer, 8192, 0) };
  let response: string = "";
  if (count > 0) {
    response = std.fromCString(buffer, count);
  }

  unsafe { free(buffer); }
  net.close(fd);
  return response;
}

function main(): number {
  std.log(httpGet("/"));
  return 0;
}
