#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
rustc -O "$HERE/classic_algorithms.rs" -o "$HERE/classic_algorithms_rust"
echo "built $HERE/classic_algorithms_rust"
