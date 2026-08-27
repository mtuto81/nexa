function main(): number {
    let total: number = 0;
    let i: number = 1;
    while (i <= 5) {
        if (i == 3) {
            total = total + 10;
        } else {
            total = total + i;
        }
        i = i + 2;
    }
    console.log(total);
    return total;
}
