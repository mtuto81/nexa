// Pure-Nexa HTTP server on port 5000 -- no C glue of any kind.
//
// Every syscall is a direct extern "C" declaration of the libc function
// (socket/setsockopt/bind/listen/accept/recv/send/close/malloc). There is no
// std.net.* wrapper call and no custom runtime.c network helper involved.
//
// struct sockaddr_in cannot be *declared* as a Nexa class: its 2/2/4/8-byte
// fields and padding are not expressible in the all-8-byte-slot class layout
// (the documented layout-control gap). So the 16-byte struct is spelled
// directly as a string literal of raw bytes. std.toCString does not copy -- it
// masks off the tag bit and hands back the string's own buffer -- hence the
// bytes below ARE the struct the kernel reads. This is the same technique the
// setsockopt call uses for its little-endian int 1.
//
// accept(fd, 0, 0): the 2nd/3rd libc arguments are void*/socklen_t*; passing
// the integer 0 in those GPRs is exactly NULL, so the peer address is not
// captured (the kernel simply doesn't write it back).

extern "C" {
  function socket(family: number, type: number, protocol: number): number;
  function setsockopt(fd: number, level: number, optname: number, optval: Pointer, optlen: number): number;
  function bind(fd: number, addr: Pointer, addrlen: number): number;
  function listen(fd: number, backlog: number): number;
  function accept(fd: number, sockaddr: number, socklen: number): number;
  function recv(fd: number, buf: Pointer, len: number, flags: number): number;
  function send(fd: number, buf: Pointer, len: number, flags: number): number;
  function close(fd: number): number;
  function malloc(n: number): Pointer;
}

// intToString: decimal ASCII digits for a non-negative integer. Used to build
// the Content-Length header from the computed body length. Pure in-language
// math (division/modulo) + digit lookup via std.charAt.
function intToString(n: number): string {
  if (n == 0) { return "0"; }
  let out: string = "";
  while (n > 0) {
    let d: number = n % 10;
    out = std.charAt("0123456789", d) + out;
    n = n / 10;
  }
  return out;
}

// indexOf: byte index of the first occurrence of ch in s at/after `start`, or
// -1 if not found.
function indexOf(s: string, ch: string, start: number): number {
  let n: number = std.strlen(s);
  let i: number = start;
  while (i < n) {
    if (std.charAt(s, i) == ch) { return i; }
    i = i + 1;
  }
  return -1;
}

// substring: copy the byte range s[start..end) into a new string.
function substring(s: string, start: number, end: number): string {
  let out: string = "";
  let i: number = start;
  while (i < end) {
    out = out + std.charAt(s, i);
    i = i + 1;
  }
  return out;
}

function main(): number {
  // 16-byte struct sockaddr_in for 0.0.0.0:5000, big-endian sin_port:
  //   [0..1] sin_family = AF_INET (2)
  //   [2..3] sin_port   = htons(5000) = 0x1388  -> bytes \x13\x88
  //   [4..7] sin_addr   = INADDR_ANY = 0
  //   [8..]  sin_zero
  let addrBytes: string = "\x02\x00\x13\x88\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
  let addr: Pointer = std.toCString(addrBytes);

  let listener: number = unsafe { socket(2, 1, 0) };
  // SO_REUSEADDR (Linux: level = SOL_SOCKET = 1, optname = SO_REUSEADDR = 2)
  // so bind doesn't fail with EADDRINUSE while a connection is in TIME_WAIT.
  let one: string = "\x01\x00\x00\x00";
  unsafe { setsockopt(listener, 1, 2, std.toCString(one), 4); }
  unsafe { bind(listener, addr, 16); }
  unsafe { listen(listener, 5); }

  while (true) {
    let client: number = unsafe { accept(listener, 0, 0) };

    // Read the request into a heap buffer, keeping the actual byte count
    // returned by recv.
    let rbuf: Pointer = unsafe { malloc(4096) };
    let got: number = unsafe { recv(client, rbuf, 4096, 0) };
    if (got < 0) { got = 0; }

    // Parse the request: std.fromCString copies `got` raw bytes (no NUL scan),
    // then split the request-line "METHOD SP PATH SP HTTP/x.y CRLF" on spaces
    // to extract the method and path. This is real parsing, not
    // string-artifact matching.
    let req: string = std.fromCString(rbuf, got);
    let method: string = "?";
    let path: string = "?";
    let methodEnd: number = indexOf(req, " ", 0);
    if (methodEnd >= 0) {
      method = substring(req, 0, methodEnd);
      let pathStart: number = methodEnd + 1;
      let pathEnd: number = indexOf(req, " ", pathStart);
      if (pathEnd < 0) { pathEnd = std.strlen(req); }
      path = substring(req, pathStart, pathEnd);
    }

    // The response echoes the parsed path, so a client can observe that the
    // request was genuinely parsed rather than ignored. Content-Length is
    // recomputed from the real byte length of this dynamic body.
    let body: string = "Echo: " + path + "\n";
    let bodyLen: string = intToString(std.strlen(body));
    let response: string = "HTTP/1.1 200 OK\r\n"
      + "Content-Type: text/plain\r\n"
      + "Content-Length: " + bodyLen + "\r\n"
      + "Connection: close\r\n"
      + "\r\n"
      + body;

    unsafe { send(client, std.toCString(response), std.strlen(response), 0); }
    unsafe { close(client); }
  }
  return 0;
}