# Iteration 017: Complete Admissibility Proof with Specializations

## Claim

For k ≥ 2 and k ∤ n, the interval [n/(k+1)+1, n/k] is admissible.
Specializations for k=2,3,4 are provided.

## Lean Proof

All theorems compile successfully with Lean 4.29.1 (no Mathlib).

### Core Theorems

1. `k1_elements_bound`: (k+1) * (n/(k+1) + 1) > n
2. `sum_le_length_mul`: sum of elements each ≤ u is ≤ length * u
3. `sum_ge_length_mul`: sum of elements each ≥ l is ≥ length * l
4. `interval_admissible`: main admissibility theorem for k ≥ 2

### Specializations

- `interval_admissible_k2`: k=2, odd n
- `interval_admissible_k3`: k=3, 3 ∤ n
- `interval_admissible_k4`: k=4, 4 ∤ n

### Application to c = 3/4

For c = 3/4 and 3 ∤ n:
- Interval: [n/4+1, n/3]
- Size: n/3 - n/4 ≈ n/12
- This interval ⊂ [1, 3n/4] for n ≥ 4

Therefore F_{3/4}(n) ≥ n/12 for 3 ∤ n.

### Application to c = 1/2

For c = 1/2 and odd n:
- k=2: interval [n/3+1, n/2], size ≈ n/6
- This interval ⊂ [1, n/2] for n ≥ 3

Therefore F_{1/2}(n) ≥ n/6 for odd n.

### Application to c = 2/3

For c = 2/3 and 3 ∤ n:
- k=3: interval [n/4+1, n/3], size ≈ n/12
- This interval ⊂ [1, 2n/3] for n ≥ 4

Therefore F_{2/3}(n) ≥ n/12 for 3 ∤ n.

## Verification

```
lean problem-361/proof-log/iteration-017.lean
```

Output: Only unused variable warnings, no errors.
