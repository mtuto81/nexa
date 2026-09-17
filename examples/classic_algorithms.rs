// The Rust counterpart to classic_algorithms.ts.
// Keep the workloads and inputs identical for a direct native comparison.

fn fibonacci(n: i64) -> i64 {
    let (mut a, mut b) = (0, 1);
    for _ in 0..n {
        let next = a + b;
        a = b;
        b = next;
    }
    a
}

fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn binary_search(values: &[i64], target: i64) -> i64 {
    let (mut low, mut high) = (0_i64, values.len() as i64 - 1);
    while low <= high {
        let middle = (low + high) / 2;
        let value = values[middle as usize];
        if value == target { return middle; }
        if value < target { low = middle + 1; } else { high = middle - 1; }
    }
    -1
}

fn insertion_sort(values: &mut [i64]) -> i64 {
    for i in 1..values.len() {
        let item = values[i];
        let mut j = i;
        while j > 0 && values[j - 1] > item {
            values[j] = values[j - 1];
            j -= 1;
        }
        values[j] = item;
    }
    values[0] + values[values.len() - 1]
}

fn sieve(limit: usize) -> i64 {
    let mut composite = vec![false; limit];
    let mut p = 2;
    while p * p < limit {
        if !composite[p] {
            let mut multiple = p * p;
            while multiple < limit {
                composite[multiple] = true;
                multiple += p;
            }
        }
        p += 1;
    }
    composite[2..].iter().filter(|&&is_composite| !is_composite).count() as i64
}

fn main() {
    let sorted: Vec<i64> = (0..100_000).map(|i| i * 2).collect();
    let mut unsorted: Vec<i64> = (0..3000).rev().map(|i| i + 1).collect();

    println!("{}", fibonacci(45));
    println!("{}", gcd(1_234_567_890, 987_654_321));
    println!("{}", binary_search(&sorted, 199_998));
    println!("{}", insertion_sort(&mut unsorted));
    println!("{}", sieve(200_000));
}
