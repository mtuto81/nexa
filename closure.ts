function makeCounter(): () => number {
  let count: number = 0;
  return () => {
    count = count + 1;
    return count;
  };
}

function main(): number {
  let a = makeCounter();
  let b = makeCounter();
  console.log(a()); // 1
  console.log(a()); // 2
  console.log(b()); // 1  <- would reveal a shared-cell bug if one exists
  console.log(a()); // 3  <- confirms a's cell wasn't corrupted by b
  return 0;
}