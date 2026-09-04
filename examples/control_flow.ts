let total: number = 0;

function main(total: number): number {
    let i: number = 1;
    while (i <= 5) {
        if (i == 3) {
            total = total + 10;
        } else {
            total = total + i;
        }
        i = i + 1;
    }
    console.log(total);
    return total;
}
