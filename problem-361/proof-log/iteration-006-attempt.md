# Iteration 006: Lemma C - Interval Lower Bound (Attempt 006)

## Claim

For c in (1/(k+1), 1/k] with k ≥ 1, the set
  A = {m ∈ ℕ : ⌈n/(k+1)⌉ ≤ m ≤ ⌊n/k⌋}
is admissible (no subset sums to n).

## Lean Proof Attempt

```lean
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Floor
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Erdos361

/-- The interval construction for Lemma C -/
def intervalSet (n k : ℕ) : Finset ℕ :=
  (Icc (Nat.ceil (n / (k + 1) : ℚ)) (n / k))

/-- If sum = n and elements are distinct, then |s| ≤ k -/
lemma card_le_of_sum_eq (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (h_sum : ∑ i in s, i = n) :
    s.card ≤ k := by
  by_contra h_card
  push_neg at h_card
  have h_card_ge : s.card ≥ k + 1 := by omega

  -- Each element ≥ ⌈n/(k+1)⌉
  have h_bound : ∀ x ∈ s, x ≥ Nat.ceil (n / (k + 1) : ℚ) := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).1

  -- Sum ≥ |s| * ⌈n/(k+1)⌉
  have h_sum_ge : ∑ i in s, i ≥ s.card * Nat.ceil (n / (k + 1) : ℚ) := by
    calc ∑ i in s, i ≥ ∑ _ in s, Nat.ceil (n / (k + 1) : ℚ) :=
      sum_le_sum (fun x hx => h_bound x hx)
      _ = s.card * Nat.ceil (n / (k + 1) : ℚ) := by rw [sum_const, nsmul_eq_mul]

  -- |s| * ⌈n/(k+1)⌉ ≥ (k+1) * ⌈n/(k+1)⌉
  have h_card_bound : s.card * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * Nat.ceil (n / (k + 1) : ℚ) := by
    exact Nat.mul_le_mul_right _ h_card_ge

  -- (k+1) * ⌈n/(k+1)⌉ ≥ n
  have h_ceil : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n := by
    have : Nat.ceil (n / (k + 1) : ℚ) ≥ n / (k + 1) := Nat.le_ceil _
    calc (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_left _ this
      _ = n := by ring

  -- So ∑ i in s, i ≥ n
  -- But we need to show ∑ i in s, i > n to get a contradiction
  sorry

/-- The interval set is admissible: no subset sums to n -/
theorem interval_admissible (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∀ s ⊆ intervalSet n k, ∑ i in s, i ≠ n := by
  intro s hs
  by_contra h_sum
  have h_card := card_le_of_sum_eq n k hk s hs h_sum
  have h_bound : ∀ x ∈ s, x ≤ n / k := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).2
  have h_sum_le : ∑ i in s, i ≤ k * (n / k) := by
    calc ∑ i in s, i ≤ ∑ _ in s, (n / k) := sum_le_sum (fun x hx => h_bound x hx)
      _ = s.card * (n / k) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ k * (n / k) := by exact Nat.mul_le_mul_right (n / k) h_card
  have h_div : k * (n / k) ≤ n := by exact Nat.div_mul_le_self n k
  omega

end Erdos361
```

## Floor, Parity, Endpoint, and Large-n Obligations

1. **Floor issues**: The set uses `Nat.ceil` for the lower bound and `n / k` (floor division) for the upper bound.

2. **Endpoint issues**: When n is divisible by k, the element n/k is included. But we can only use each element once, so we can't form n using k copies of n/k.

3. **Parity issues**: None for this construction.

4. **Large-n issues**: The construction works for all n ≥ 1.

## Weakest Formalization Step

The key step is showing that if |s| ≥ k+1, then ∑ i in s, i > n. The current proof shows ∑ i in s, i ≥ n, but not > n.

The correct argument is that the k+1 smallest elements in A have sum:
(k+1) * ⌈n/(k+1)⌉ + k(k+1)/2 ≥ n+1

But this requires proving that distinct elements are spaced out, which is not captured by the simple lower bound |s| * ⌈n/(k+1)⌉.

## Suggested Narrower Next Target

1. **Prove for specific k values**: First prove the lemma for k=1, k=2, etc., to build intuition.

2. **Use a different proof strategy**: Instead of trying to prove the exact bound, try to prove by contradiction that if ∑ i in s, i = n, then |s| ≤ k.

3. **Use existing Mathlib lemmas**: Look for lemmas about sums of distinct elements in intervals.
