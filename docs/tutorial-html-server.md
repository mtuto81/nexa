# Build an HTML server with Nexa

This tutorial builds a small static website server entirely in Nexa
TypeScript. It uses the bundled `std/net` module and the native Nexa runtime;
there is no custom C source file.

The server will listen on `127.0.0.1:8080` and serve an HTML page at `/`.

## 1. Create the project

From the Nexa repository:

```bash
mkdir -p examples/website
cd examples/website
```

Create `server.ts`:

```ts
import * as net from "std/net";

// Nexa's socket API works with raw buffers. malloc/free are ordinary libc
// functions exposed through typed extern declarations.
extern "C" {
  function malloc(size: number): Pointer;
  function free(ptr: Pointer): void;
}

function indexOf(s: string, needle: string): number {
  let i: number = 0;
  let limit: number = std.strlen(s) - std.strlen(needle);
  while (i <= limit) {
    let j: number = 0;
    let matches: boolean = true;
    while (j < std.strlen(needle)) {
      if (std.charAt(s, i + j) != std.charAt(needle, j)) {
        matches = false;
      }
      j = j + 1;
    }
    if (matches) { return i; }
    i = i + 1;
  }
  return -1;
}

function requestPath(request: string): string {
  // A request line has the form: GET /path HTTP/1.1
  let firstSpace: number = indexOf(request, " ");
  if (firstSpace < 0) { return "/"; }
  let secondSpace: number = firstSpace + 1;
  while (secondSpace < std.strlen(request) &&
         std.charAt(request, secondSpace) != " ") {
    secondSpace = secondSpace + 1;
  }

  let path: string = "";
  let i: number = firstSpace + 1;
  while (i < secondSpace) {
    path = path + std.charAt(request, i);
    i = i + 1;
  }
  return path;
}

function page(): string {
  return "<!doctype html>"
    + "<html><head><meta charset=\"utf-8\">"
    + "<title>Nexa website</title>"
    + "<style>body{font-family:sans-serif;margin:4rem;background:#f5f5f5}"
    + "main{max-width:42rem;margin:auto;background:white;padding:2rem;"
    + "border-radius:12px;box-shadow:0 2px 12px #ccc}</style>"
    + "</head><body><main>"
    + "<h1>Hello from Nexa</h1>"
    + "<p>This page was served by native TypeScript.</p>"
    + "</main></body></html>";
}

function response(status: string, contentType: string, body: string): string {
  return "HTTP/1.1 " + status + "\r\n"
    + "Content-Type: " + contentType + "\r\n"
    + "Content-Length: " + numberText(std.strlen(body)) + "\r\n"
    + "Connection: close\r\n"
    + "\r\n"
    + body;
}

function numberText(n: number): string {
  if (n == 0) { return "0"; }
  let result: string = "";
  while (n > 0) {
    let digit: number = n % 10;
    result = std.charAt("0123456789", digit) + result;
    n = n / 10;
  }
  return result;
}

function main(): number {
  let listener: number = net.socket(2, 1, 0); // AF_INET, SOCK_STREAM
  let address: Pointer = net.sockaddrIn(8080, 0); // 0.0.0.0:8080
  unsafe { net.bind(listener, address, 16); }
  unsafe { net.listen(listener, 16); }

  std.log("Nexa website listening on http://127.0.0.1:8080");

  while (true) {
    let client: number = net.accept(listener);
    let buffer: Pointer = unsafe { malloc(8192) };
    let received: number = unsafe { net.recv(client, buffer, 8192, 0) };

    if (received > 0) {
      let request: string = std.fromCString(buffer, received);
      let path: string = requestPath(request);
      let body: string = page();
      let reply: string = response("200 OK", "text/html; charset=utf-8", body);

      if (path != "/") {
        body = "<h1>404 Not Found</h1>";
        reply = response("404 Not Found", "text/html; charset=utf-8", body);
      }

      unsafe { net.send(client, std.toCString(reply), std.strlen(reply), 0); }
    }

    unsafe { free(buffer); }
    net.close(client);
  }

  return 0;
}

main();
```

## 2. Build it

Run the compiler from the Nexa repository root so it can find `runtime.c`:

```bash
cd ~/Documents/Code/nexa
cargo build --release
./target/release/nexa examples/website/server.ts \
  -o examples/website/server
```

## 3. Run it

Start the server:

```bash
./examples/website/server
```

Open `http://127.0.0.1:8080/` in a browser, or test it with curl:

```bash
curl -i http://127.0.0.1:8080/
curl -i http://127.0.0.1:8080/missing
```

The first request returns the HTML page. The second returns a `404 Not Found`
response.

## How it works

- `std/net` wraps native Linux socket operations.
- `sockaddrIn(8080, 0)` creates the IPv4 address structure.
- `recv` writes request bytes into a native `Pointer` buffer.
- `std.fromCString(buffer, received)` copies exactly the received bytes into a
  Nexa string.
- `std.toCString(reply)` exposes the reply string as a C-compatible pointer
  for `send`.
- The server is deliberately synchronous and handles one connection at a time.

## Current limitations

This is a foundation for a website server, not a production HTTP framework.
It currently has no TLS, keep-alive, chunked transfer decoding, request-body
limits, concurrent workers, routing table, or MIME-file serving. The next
natural additions are a `std/fs` static-file route, request-header parsing,
and a poll/epoll-based event loop.
