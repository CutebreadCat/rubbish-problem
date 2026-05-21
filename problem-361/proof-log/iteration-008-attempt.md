# Iteration 008: Standalone Lean Test

## Claim

For k=1, if a ≥ (n+1)/2 and b ≥ (n+1)/2 and a ≠ b, then a+b > n.

## Lean Proof

```lean
theorem k1_sum_gt (n a b : Nat) (ha : a ≥ (n + 1) / 2) (hb : b ≥ (n + 1) / 2) (hab : a ≠ b) :
    a + b > n := by
  have h_bound : a + b ≥ 2 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  have h_both : a = (n + 1) / 2 ∧ b = (n + 1) / 2 := by omega
  exact hab (Eq.trans h_both.1 h_both.2.symm)
```

## Lean Check

- **Command**: `lean iteration-008.lean`
- **Output**: warning: failed to query latest release, using existing version 'leanprover/lean4:v4.29.1'
- **Status**: ✅ Compiled successfully

## Analysis

This is a key building block for the k=1 case. It shows that two distinct elements from the interval [(n+1)/2, n-1] cannot sum to n.

The proof strategy:
1. Show a+b ≥ 2 * ((n+1)/2) ≥ n
2. If a+b = n, then both a and b must equal (n+1)/2
3. But a ≠ b, contradiction

## Next Steps

1. Extend this to prove the full k=1 admissibility
2. Generalize to arbitrary k
3. Set up a Lake project with Mathlib for more complex proofs
