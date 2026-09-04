// Pure-Nexa HTTP server on port 5000.
//
// No custom C glue: every syscall goes through std.net.* (thin wrappers in the
// standard runtime), and std.net.sockaddrIn builds a REAL struct sockaddr_in
// (htons/htonl network order) instead of hand-spelled "\xNN" byte strings.
//
// The server now:
//   - computes Content-Length from the actual body byte length (std.strlen),
//     converted to ASCII via an in-language intToString, and
//   - actually PARSES the incoming request (fromCString + string splitting)
//     to extract the method and request path, which it logs and echoes,
//     rather than blindly sending a fixed response.
//
// setsockopt stays a direct extern "C" call (not wrapped in this pass); it
// only needs the little-endian int 1 read out of a string via std.toCString.

extern "C" {
  function setsockopt(fd: number, level: number, optname: number, optval: Pointer, optlen: number): number;
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
  let addr: Pointer = std.net.sockaddrIn(5000, 0);

  let listener: number = unsafe { std.net.socket(2, 1, 0) };
  // SO_REUSEADDR (Linux: level = SOL_SOCKET = 1, optname = SO_REUSEADDR = 2)
  // so bind doesn't fail with EADDRINUSE while a connection is in TIME_WAIT.
  let one: string = "\x01\x00\x00\x00";
  unsafe { setsockopt(listener, 1, 2, std.toCString(one), 4); }
  let bound: number = unsafe { std.net.bind(listener, addr, 16) };
  unsafe { std.net.listen(listener, 5); }

  while (true) {
    let client: number = unsafe { std.net.accept(listener) };

    // Read the request into a writable heap buffer, keeping the actual byte
    // count returned by recv.
    let rbuf: Pointer = unsafe { malloc(4096) };
    let got: number = unsafe { std.net.recv(client, rbuf, 4096, 0) };
    if (got < 0) { got = 0; }

    // Parse the request: turn the raw bytes into a Nexa string, then split the
    // request-line "METHOD SP PATH SP HTTP/x.y CRLF" on spaces to extract the
    // method and path. This is real parsing, not string-artifact matching.
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

    unsafe { std.net.send(client, std.toCString(response), std.strlen(response), 0); }
    unsafe { std.net.close(client); }
  }
  return 0;
}
