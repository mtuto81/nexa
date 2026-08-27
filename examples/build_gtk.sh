#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

SRC=examples/gtk_app.ts
GLUE=examples/gtk_app_glue.c
OUT=gtk_app

echo "=== compiling Nexa source ==="
# nexa compiles to /tmp/nexa.o then tries a bare link that will fail
# because GTK symbols are unresolved. The .o is already written.
cargo run --quiet -- "$SRC" -o "$OUT" 2>/dev/null || true

echo "=== compiling C glue ==="
gcc -c -fPIC -o /tmp/gtk_app_glue.o "$GLUE" $(pkg-config --cflags gtk+-3.0)

echo "=== linking ==="
gcc /tmp/nexa.o /tmp/gtk_app_glue.o runtime.c \
    $(pkg-config --libs gtk+-3.0) \
    -lpthread \
    -o "$OUT"

echo "=== built $OUT ==="
echo "run with: ./$OUT"
