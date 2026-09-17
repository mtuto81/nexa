#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"

echo "Nexa"
/usr/bin/time -f 'elapsed=%e user=%U sys=%S maxrss=%MKB' "$HERE/classic_algorithms" >/dev/null
echo "Rust -O"
/usr/bin/time -f 'elapsed=%e user=%U sys=%S maxrss=%MKB' "$HERE/classic_algorithms_rust" >/dev/null
echo "Node.js"
/usr/bin/time -f 'elapsed=%e user=%U sys=%S maxrss=%MKB' node "$HERE/classic_algorithms.js" >/dev/null
