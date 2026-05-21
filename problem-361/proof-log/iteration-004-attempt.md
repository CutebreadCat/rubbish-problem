# Iteration 004: Lemma C - Interval Lower Bound (Attempt 004)

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

/-- The sum of first m natural numbers -/
def sumFirstN (m : ℕ) : ℕ := m * (m + 1) / 2

/-- The sum of k+1 smallest elements in the interval is ≥ n+1 -/
lemma sum_k_plus_1_smallest_ge (n k : ℕ) (hk : k ≥ 1) :
    (k + 1) * Nat.ceil (n / (k + 1) : ℚ) + k * (k + 1) / 2 ≥ n + 1 := by
  have h1 : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n := by
    have : Nat.ceil (n / (k + 1) : ℚ) ≥ n / (k + 1) := Nat.le_ceil _
    calc (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_left _ this
      _ = n := by ring
  have h2 : k * (k + 1) / 2 ≥ 1 := by
    have : k * (k + 1) ≥ 2 := by
      calc k * (k + 1) ≥ 1 * (1 + 1) := by exact Nat.mul_le_mul hk (Nat.add_le_add_right hk 1)
        _ = 2 := by ring
    omega
  omega

/-- Any subset of size ≤ k has sum ≤ n -/
lemma sum_le_of_card_le (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≤ k) :
    ∑ i in s, i ≤ n := by
  have h_bound : ∀ x ∈ s, x ≤ n / k := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).2
  calc ∑ i in s, i ≤ ∑ _ in s, (n / k) := sum_le_sum (fun x hx => h_bound x hx)
    _ = s.card * (n / k) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ k * (n / k) := by exact Nat.mul_le_mul_right (n / k) hcard
    _ ≤ n := by exact Nat.div_mul_le_self n k

/-- Helper: The sum of k+1 distinct elements from an interval is bounded below -/
lemma sum_distinct_elements_ge (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≥ k + 1) :
    ∑ i in s, i ≥ (k + 1) * Nat.ceil (n / (k + 1) : ℚ) + k * (k + 1) / 2 := by
  sorry  -- This is the key step that needs to be proved

/-- Any subset of size ≥ k+1 has sum ≥ n+1 -/
lemma sum_ge_of_card_ge (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≥ k + 1) :
    ∑ i in s, i ≥ n + 1 := by
  have h_sum := sum_distinct_elements_ge n k hk s hs hcard
  have h_bound := sum_k_plus_1_smallest_ge n k hk
  omega

/-- The interval set is admissible: no subset sums to n -/
theorem interval_admissible (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∀ s ⊆ intervalSet n k, ∑ i in s, i ≠ n := by
  intro s hs
  by_contra h_sum
  by_cases hcard : s.card ≤ k
  · have h_le := sum_le_of_card_le n k hk s hs hcard
    omega
  · have h_ge := sum_ge_of_card_ge n k hk s hs (by omega)
    omega

end Erdos361
```

## Floor, Parity, Endpoint, and Large-n Obligations

1. **Floor issues**: The set uses `Nat.ceil` for the lower bound and `n / k` (floor division) for the upper bound.

2. **Endpoint issues**: When n is divisible by k, the element n/k is included. But we can only use each element once, so we can't form n using k copies of n/k.

3. **Parity issues**: None for this construction.

4. **Large-n issues**: The construction works for all n ≥ 1.

## Weakest Formalization Step

The key step is `sum_distinct_elements_ge`: proving that the sum of k+1 distinct elements from A is at least (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2.

This requires showing that:
1. The elements are distinct (given by Finset)
2. The elements are in the interval [⌈n/(k+1)⌉, ⌊n/k⌋]
3. The minimum sum is achieved by taking the k+1 smallest elements

This is a combinatorial argument about the structure of finite sets of integers.

## Suggested Narrower Next Target

1. **Prove for specific k values**: First prove the lemma for k=1, k=2, etc., to build intuition.

2. **Use a different proof strategy**: Instead of trying to prove the exact bound, try to prove by contradiction that if ∑ i in s, i = n, then |s| ≤ k.

3. **Use existing Mathlib lemmas**: Look for lemmas about sums of distinct elements in intervals.
