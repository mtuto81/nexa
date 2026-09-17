class Point {
  x: number;
  y: number;

  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }
}

function inspectValues(n: number): number {
  let flag: boolean = n > 0;
  let text: string = "debug";
  let numbers: number[] = new Array<number>(3);
  numbers[0] = n;
  numbers[1] = n + 1;
  numbers[2] = n + 2;
  let point: Point = new Point(numbers[0], numbers[1]);
  let result: number = point.x + point.y;
  console.log(text);
  console.log(flag);
  return result;
}

function main(): number {
  let result: number = inspectValues(7);
  console.log(result);
  return 0;
}

main();
