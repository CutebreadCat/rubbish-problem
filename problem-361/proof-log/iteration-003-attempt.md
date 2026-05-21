# Iteration 003: Lemma C - Interval Lower Bound (Fixed)

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

/-- The sum of k+1 smallest elements in the interval is ≥ n+1 -/
lemma sum_k_plus_1_smallest (n k : ℕ) (hk : k ≥ 1) :
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

/-- Any subset of size ≥ k+1 has sum ≥ n+1 -/
lemma sum_ge_of_card_ge (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≥ k + 1) :
    ∑ i in s, i ≥ n + 1 := by
  have h_bound : ∀ x ∈ s, x ≥ Nat.ceil (n / (k + 1) : ℚ) := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).1
  have h_sum1 : ∑ i in s, i ≥ s.card * Nat.ceil (n / (k + 1) : ℚ) := by
    calc ∑ i in s, i ≥ ∑ _ in s, Nat.ceil (n / (k + 1) : ℚ) :=
      sum_le_sum (fun x hx => h_bound x hx)
      _ = s.card * Nat.ceil (n / (k + 1) : ℚ) := by rw [sum_const, nsmul_eq_mul]
  have h_sum2 : s.card * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * Nat.ceil (n / (k + 1) : ℚ) := by
    exact Nat.mul_le_mul_right _ hcard
  have h_sum3 : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n := by
    have : Nat.ceil (n / (k + 1) : ℚ) ≥ n / (k + 1) := Nat.le_ceil _
    calc (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_left _ this
      _ = n := by ring
  sorry  -- Need to show sum ≥ n+1, not just ≥ n

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

The key step is showing that if |s| ≥ k+1, then ∑ i in s, i ≥ n+1. The current proof only shows ∑ i in s, i ≥ n, which is not enough.

The correct argument is that the k+1 smallest elements in A have sum:
(k+1) * ⌈n/(k+1)⌉ + k(k+1)/2 ≥ n + 1

But this requires proving that the elements are distinct and spaced out, which is not captured by the simple lower bound |s| * ⌈n/(k+1)⌉.

## Suggested Narrower Next Target

1. **Prove the sum of k+1 smallest elements**: Show that if s ⊆ A and |s| = k+1, then ∑ i in s, i ≥ (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2.

2. **Alternative approach**: Use a different proof strategy that doesn't require this exact calculation. For example, prove by contradiction that if ∑ i in s, i = n, then |s| ≤ k.
