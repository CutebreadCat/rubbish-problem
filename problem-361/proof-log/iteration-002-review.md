# Iteration 002 Review

## Lean Check

- **Command**: `lean iteration-002.lean`
- **Output**: Lean toolchain not found.
- **Status**: Cannot verify Lean compilation. The proof attempt contains one `sorry` in `sum_ge_of_card_ge`.

## Validity Issues

### 1. Critical Error: The `sorry` in `sum_ge_of_card_ge`

The key step `h_ceil : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n + 1` is marked with `sorry`. This is not a minor gap—it's the core of the proof. Without this, the entire argument fails.

**Analysis**: The claim is that for any n ≥ 1 and k ≥ 1:
  (k + 1) * ⌈n / (k + 1)⌉ ≥ n + 1

This is equivalent to: ⌈n / (k + 1)⌉ ≥ (n + 1) / (k + 1)

But by definition of ceiling: ⌈x⌉ ≥ x, so:
  ⌈n / (k + 1)⌉ ≥ n / (k + 1)

And we need: n / (k + 1) ≥ (n + 1) / (k + 1)? No, that's false.

Actually, we need: (k + 1) * ⌈n / (k + 1)⌉ ≥ n + 1

Let's test with n = 10, k = 2:
  ⌈10 / 3⌉ = ⌈3.33...⌉ = 4
  3 * 4 = 12 ≥ 11 ✓

Let's test with n = 9, k = 2:
  ⌈9 / 3⌉ = ⌈3⌉ = 3
  3 * 3 = 9 ≥ 10? No! ✗

**COUNTEREXAMPLE FOUND**: For n = 9, k = 2:
  A = {m : ⌈9/3⌉ ≤ m ≤ ⌊9/2⌋} = {3, 4}
  Sum of {3, 4} = 7 ≠ 9 ✓ (so the set is admissible)
  But the claim (k+1) * ⌈n/(k+1)⌉ ≥ n+1 fails: 3 * 3 = 9 < 10

This means the proof attempt has a **fundamental error** in the `sum_ge_of_card_ge` lemma.

### 2. The Construction May Still Be Admissible

Even though the proof of `sum_ge_of_card_ge` fails, the construction itself may still be admissible. Let's verify:

For n = 9, k = 2:
  A = {3, 4}
  Subsets: {}, {3}, {4}, {3,4}
  Sums: 0, 3, 4, 7
  None equal 9 ✓

For n = 10, k = 2:
  A = {m : ⌈10/3⌉ ≤ m ≤ ⌊10/2⌋} = {4, 5}
  Subsets: {}, {4}, {5}, {4,5}
  Sums: 0, 4, 5, 9
  None equal 10 ✓

For n = 11, k = 2:
  A = {m : ⌈11/3⌉ ≤ m ≤ ⌊11/2⌋} = {4, 5}
  Same as above, no subset sums to 11 ✓

For n = 12, k = 2:
  A = {m : ⌈12/3⌉ ≤ m ≤ ⌊12/2⌋} = {4, 5, 6}
  Subsets: {}, {4}, {5}, {6}, {4,5}, {4,6}, {5,6}, {4,5,6}
  Sums: 0, 4, 5, 6, 9, 10, 11, 15
  None equal 12 ✓

So the construction seems admissible, but the proof is wrong.

### 3. The Real Argument

The correct argument is:
- Any subset with ≤ k elements has sum ≤ k * ⌊n/k⌋ ≤ n
- Any subset with ≥ k+1 elements has sum ≥ (k+1) * ⌈n/(k+1)⌉

But (k+1) * ⌈n/(k+1)⌉ may be ≤ n (as shown in the counterexample).

So we need a different approach:
- If we pick k+1 elements, the minimum sum is achieved by picking the k+1 smallest elements.
- The k+1 smallest elements in A are: ⌈n/(k+1)⌉, ⌈n/(k+1)⌉+1, ..., ⌈n/(k+1)⌉+k
- Their sum is: (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2

This is much larger than n for reasonable k. Let's verify:
For n = 9, k = 2:
  Smallest 3 elements: 3, 4, 5 (but A only has {3, 4})
  Wait, A = {3, 4}, so we can't pick 3 elements!

Ah, the issue is that for some n and k, the interval A may have fewer than k+1 elements. In that case, any subset has at most k elements, and the sum is ≤ k * ⌊n/k⌋ ≤ n.

So the correct argument is:
1. If |A| ≤ k, then any subset has at most k elements, so sum ≤ k * ⌊n/k⌋ ≤ n
2. If |A| ≥ k+1, then the sum of the k+1 smallest elements is ≥ n+1

But we need to compute the sum of the k+1 smallest elements correctly.

## Mathematical Fit

The construction is from the source notes: "interval constructions of the form [n/(k+1), n/k] avoid a subset sum of n, because any k elements are too small and any k+1 elements are too large."

But the proof attempt doesn't correctly handle the "any k+1 elements are too large" part.

## Verdict

**reject**

The proof attempt has a fundamental error in the `sum_ge_of_card_ge` lemma. The counterexample n = 9, k = 2 shows that (k+1) * ⌈n/(k+1)⌉ < n+1.

## Next Narrower Target

1. **Fix the proof**: Compute the sum of the k+1 smallest elements in A correctly, and show it's ≥ n+1 when |A| ≥ k+1.

2. **Alternative approach**: Prove admissibility directly by considering all possible subset sizes:
   - For subsets of size 1 to k: sum ≤ k * ⌊n/k⌋ ≤ n
   - For subsets of size k+1 or more: sum ≥ (sum of k+1 smallest elements) ≥ n+1

3. **Weaker target**: Prove the construction is admissible without the exact size formula. This avoids the ceiling arithmetic issues.
