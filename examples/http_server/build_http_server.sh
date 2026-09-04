#!/usr/bin/env bash
# Build the pure-Nexa HTTP server with no custom C glue.
# Compiles server.ts with nexa, then links the resulting object against the
# standard Nexa runtime (runtime.c) -- the same runtime every nexa program uses.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
NEXA=${NEXA:-$ROOT/target/release/nexa}

# nexa writes /tmp/nexa.o and links runtime.c from its CWD, so run it from the
# repo root where runtime.c lives.
(cd "$ROOT" && "$NEXA" "$HERE/server.ts" -o "$HERE/http_server")
echo "built $HERE/http_server (pure TS, libc only, no custom glue)"
