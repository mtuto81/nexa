# Nexa native runtime architecture

## Core representation strategy

Nexa uses type-directed monomorphization. The Rust type checker annotates the
SSA IR with concrete types, and Cranelift receives raw machine values whenever
the type is fully known:

```text
number  → i64/f64 machine value
boolean → i8/i64 machine value
string  → pointer + length / runtime string handle
class   → typed fixed-layout pointer
any     → boxed dynamic Value
```

The boxed path is reserved for `any`, unresolved dynamic property access, and
unions that cannot be narrowed. Typed function calls do not pay a boxing cost.

## Objects and classes

Every statically known class gets a compile-time layout. Fields have fixed
offsets and typed storage, similar to a C struct. Interfaces contribute type
checking but do not require runtime objects.

Dynamic object literals and `any`-typed objects use a separate shape/property
runtime. That path is intentionally isolated from ordinary monomorphic class
access.

## Closures

A closure is represented as:

```text
code pointer + environment pointer
```

The capture analysis runs before Cranelift lowering. Non-captured locals remain
ordinary SSA values or stack slots. Captured mutable locals are placed in
heap cells shared by the enclosing function and closure environment, preserving
TypeScript/JavaScript capture-by-reference behavior.

## Memory management

The runtime boundary will make heap ownership explicit so the first allocator
can be replaced later. The initial implementation can use reference-counted
objects for deterministic reclamation, with weak back-references where the
language subset permits them. The long-term target is a tracing mark-sweep GC
for cycles and general TypeScript object behavior.

## Implementation order

1. Add a type field to every SSA value and lower monomorphic `number` and
   `boolean` instructions directly to Cranelift machine values.
2. Add typed function signatures and reject accidental boxed/typed crossings.
3. Add `Value` boxing only for `any` and dynamic boundaries.
4. Add fixed-layout classes and typed field offsets.
5. Add capture analysis and heap environments for closures.
6. Introduce the heap API and then choose reference counting versus tracing GC
   based on real Nexa allocation patterns.
