
extern "C"{
    function abs(s: number): number;
}


function main(): number {
    const num: number = -5;
    const result: number = unsafe { abs(num) };
    console.log(result);
    return 0;
}

main();