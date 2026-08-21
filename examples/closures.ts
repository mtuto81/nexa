// closures.ts — basic closure feature coverage
// Tests: capture by value, capture in expression, closure as argument

function makeAdder(n: number): () => number {
    let base: number = n;
    let f: () => number = () => { return base; };
    return f;
}

function main(): number {
    let x: number = 42;
    let f: () => number = () => { return x; };
    console.log(f());

    let a: number = 10;
    let b: number = 20;
    let g: () => number = () => { return a + b; };
    console.log(g());

    let h: () => number = makeAdder(7);
    console.log(h());

    return 0;
}

main();
