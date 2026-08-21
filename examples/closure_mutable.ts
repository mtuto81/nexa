// closure_mutable.ts — test mutable capture via cells
function main(): number {
    let counter: number = 0;
    let f: () => number = () => { return counter; };
    counter = 10;
    console.log(f());
    return 0;
}

main();
