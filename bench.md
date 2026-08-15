# Nexa Benchmark Results

Date: 2026-08-14

## Environment

- OS: Fedora Linux
- Kernel: `7.1.8-200.fc44.x86_64`
- Architecture: x86-64
- CPU: AMD Ryzen 5 3500U with Radeon Vega Mobile Gfx
- CPUs: 8
- CPU range: 1.4–3.7 GHz
- Rust: `rustc 1.97.1`
- Cargo: `cargo 1.97.1`
- GCC: `16.1.1`
- GNU ld: `2.46.1`
- Backend: Cranelift object generation, GCC final linking

## Benchmark program

The unchanged `benchmark.ts` was compiled to a native Linux executable.
It exercises recursion, arithmetic loops, primality testing, numeric arrays,
indexed array writes, indexed array reads, and bubble sort.

Command:

```bash
cargo run -- benchmark.ts -o benchmark
./benchmark
```

Output:

```text
2178309
4999999950000000
17984
333332833333500000
1
```

## Binary size

The generated executable is dynamically linked and currently unstripped.

| Executable | File size | Text | Data | BSS | Text/data/BSS total |
|---|---:|---:|---:|---:|---:|
| `nexa-benchmark` | 13,232 bytes | 2,953 bytes | 564 bytes | 16 bytes | 3,533 bytes |
| no-op executable | 13,032 bytes | 1,851 bytes | 564 bytes | 16 bytes | 2,431 bytes |

## Timing

Full benchmark execution, five runs:

```text
0.16 s
0.18 s
0.17 s
0.17 s
0.17 s
```

Observed average: approximately **0.17 seconds**.

Startup was estimated with a generated no-op Nexa executable over 1,000
launches:

```text
1.38 seconds total
approximately 1.38 ms per launch
```

The startup figure includes the shell loop and process-launch overhead; it is
not a cycle-accurate runtime startup measurement.

## Notes

- The benchmark source was not modified.
- Numeric arrays currently use Nexa's preallocated native array path.
- The result is a baseline for the current prototype, not a comparison with
  an optimized Node.js, Deno, or Rust build.
