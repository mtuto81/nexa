// for_of_array.ts — demonstrates for...of over a number[] array,
// which desugars to the indexed for(;;) loop (arr.length / arr[__i])

function main(): number {
  let scores: number[] = new Array<number>(4);
  scores[0] = 10; scores[1] = 20; scores[2] = 30; scores[3] = 40;

  console.log(scores.length); // 4

  let total: number = 0;
  for (const x of scores) {
    total = total + x;
  }
  console.log(total); // 100

  // copy into a fresh array, preserving order
  let copy: number[] = new Array<number>(4);
  let i: number = 0;
  for (const x of scores) {
    copy[i] = x;
    i = i + 1;
  }
  console.log(copy[0]); // 10
  console.log(copy[3]); // 40
  return 0;
}

main();
