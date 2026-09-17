#!/usr/bin/env bash
# Build the HTTP client against Nexa's normal runtime; no compiler changes or
# custom C glue are required.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
NEXA=${NEXA:-$ROOT/target/release/nexa}

(cd "$ROOT" && "$NEXA" "$HERE/client.ts" -o "$HERE/http_client")
echo "built $HERE/http_client"
