# Nexa prototype

This is a deliberately small native TypeScript compiler experiment for
non-web applications.

Nexa is not a browser JavaScript implementation and does not target the DOM,
web APIs, bundlers, or JavaScript compatibility. Its goal is to compile a
native-oriented TypeScript language and standard library directly to Linux
executables.

## Build and run

```sh
cargo run -- examples/arithmetic.ts -o /tmp/nexa-app
/tmp/nexa-app
```

The compiler emits a native ELF object through Cranelift and links it with
`runtime.c` using GCC. The sample program exits with status `42`.

## TypeScript front end

Nexa uses SWC's `swc_ecma_parser` in TypeScript mode as its syntax front end.
This gives Nexa a production-grade parser for TypeScript grammar, including
automatic semicolon insertion, JSX ambiguity handling, and generic-call
ambiguities. The current migration validates the complete SWC module first;
the native lowering adapter is still being expanded over the SWC AST subset.

Nexa now also runs a Rust type-checking pass over that SWC AST before native
lowering. It checks scalar annotations and inference, function parameters and
returns, assignments, arithmetic/logical/comparison operators, conditions,
and calls. A mismatch is reported before GCC or Cranelift runs.

## Type-system boundary

Nexa intentionally uses a native-oriented subset of TypeScript rather than
trying to reproduce every edge case of the JavaScript ecosystem's type model.
The checker will support practical scalar types, local inference, function
signatures, unions where they map cleanly to a native representation, and
useful diagnostics. It will skip most structural-typing compatibility edge
cases and most type-level computation features such as conditional, mapped,
and template-literal type programming.

The pipeline is:

```text
SWC TypeScript AST → Nexa type checking → type erasure → native typed IR → Cranelift
```

Types affect diagnostics and overload/signature decisions, but they do not
survive into the native runtime unless a feature explicitly needs runtime type
information.

Nexa now has a small typed SSA-style IR with value IDs, basic blocks,
concrete `Number`/`Boolean`/`String`/`Any`/`Void` value types, arithmetic,
calls, prints, returns, and reserved phi nodes. Inspect it while compiling with:

```sh
NEXA_DUMP_IR=1 cargo run -- examples/typed.ts -o /tmp/nexa-app
```

The current Cranelift backend still consumes the temporary lowering AST; the
IR is the migration seam for the next backend step. Control-flow block and phi
construction are intentionally next.

## Current subset

- `function name(a, b) { ... }`
- integer and string literals
- `number`, `string`, `boolean`, and `void` annotations are accepted
- `let` and `const` declarations
- local variables and integer parameters
- `+`, `-`, `*`, `/`
- comparisons: `==`, `!=`, `<`, `<=`, `>`, `>=`
- strict equality syntax `===` (lowered to the current scalar equality path)
- `%` modulo
- booleans: `true`, `false`, `!`, `&&`, `||`
- string concatenation with `string + string`
- assignment to existing variables
- `if`/`else` and `while`
- `for` loops
- `return`
- `number[]` arrays with indexed reads and writes
- `console.log(<numeric expression>)` and `console.log("text")`

Annotations are checked for the supported scalar and numeric-array subset.
`any` and implicit function types are rejected until a checked boxed-value
path exists; this prevents dynamic values from entering raw native operations.
There is no control flow in the type checker for closures, objects, imports,
or garbage collector semantics yet. Numeric arrays currently use a native
preallocated storage path for the benchmark workload.

Inferred local declarations are accepted when their initializer has a concrete
supported type. Untyped function parameters and return values are rejected
until inference and boxed-value lowering are implemented.

## Dependencies

- Rust 1.97 and Cargo
- Cranelift 0.125 (`codegen`, `frontend`, `module`, `object`)
- SWC 45 (`swc_ecma_parser`, `swc_ecma_ast`, `swc_common`)
- GCC for final linking
- The host Linux C runtime for `printf`

## Next architectural step

Introduce a typed intermediate representation between parsing and Cranelift.
That IR should make `i64`, strings, and later objects explicit, centralize name
resolution/type checking, and give the runtime a stable ABI. The first useful
extension would be a real string constant/data section plus `console.log` for
strings, followed by conditionals and loops.

The platform direction is:

```text
TypeScript source → Nexa type checker → native typed IR → Cranelift/GCC → Linux executable
```

The standard library will be native-focused: filesystem, processes, sockets,
HTTP clients/servers, crypto, concurrency, serialization, and OS integration.
Browser-only APIs are out of scope.

## Parser/checker safety boundary

SWC parsing is completed before any lowering begins, and the checker must
accept the resulting AST before the temporary lowering parser or Cranelift is
invoked. This is covered by a regression test for optional chaining:
SWC accepts `value?.length`, while Nexa rejects the unsupported AST with a
checker error. Unsupported TS grammar therefore cannot silently fall through
as a monomorphic native value.

The unchanged `test.ts` acceptance file now compiles and runs. The typed print
ABI routes boolean expressions to `nexa_print_bool`, so native output uses
`true`/`false` rather than numeric `1`/`0`; numeric and string values use their
own print entry points.

See [ARCHITECTURE.md](ARCHITECTURE.md) for the monomorphic typed-value,
fixed-layout object, closure-environment, and memory-management design.
