
extern "C"{
    function abs(s: number): number;
}


let console: number = 0;

function main(): number {
    const number = "hi";
    const num: number = -5;
    const result: number = unsafe { abs(num) };
    console.log(number);
    return 0;
}

