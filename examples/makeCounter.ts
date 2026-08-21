function makeCounter(): (() => number) {
    let count: number = 0;
    const closure: () => number = (): number => {
        count = count + 1;
        return count;
    };
    return closure;
}

function main(): number {
    const counter: (() => number) = makeCounter();
    console.log(counter());
    console.log(counter());
    console.log(counter());
    return 0;
}

main();
