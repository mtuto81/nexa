#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
NEXA=${NEXA:-$ROOT/target/release/nexa}

(cd "$ROOT" && "$NEXA" "$HERE/classic_algorithms.ts" -o "$HERE/classic_algorithms")
echo "built $HERE/classic_algorithms"
