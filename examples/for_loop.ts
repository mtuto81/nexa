// for_loop.ts — demonstrates the classic C-style for loop

function main(): number {
  let total: number = 0;
  for (let i: number = 1; i <= 5; i = i + 1) {
    console.log(i);
    total = total + i;
  }
  console.log(total); // 15
  return 0;
}

main();
