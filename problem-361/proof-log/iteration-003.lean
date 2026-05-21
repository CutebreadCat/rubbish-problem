import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Floor
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 361 - Lemma C: Interval Lower Bound (Fixed)

For c in (1/(k+1), 1/k] with k ≥ 1, the set
  A = {m ∈ ℕ : ⌈n/(k+1)⌉ ≤ m ≤ ⌊n/k⌋}
is admissible (no subset sums to n).

## Fixed Proof Idea

Case 1: If |A| ≤ k, any subset has at most k elements, so sum ≤ k * ⌊n/k⌋ ≤ n
Case 2: If |A| ≥ k+1, the sum of the k+1 smallest elements is:
  (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2 ≥ n + 1

This is because:
- (k+1) * ⌈n/(k+1)⌉ ≥ n (by definition of ceiling)
- k(k+1)/2 ≥ 1 for k ≥ 1
- So total ≥ n + 1
-/

open Finset
open scoped BigOperators

namespace Erdos361

/-- The interval construction for Lemma C -/
def intervalSet (n k : ℕ) : Finset ℕ :=
  (Icc (Nat.ceil (n / (k + 1) : ℚ)) (n / k))

/-- The sum of k+1 smallest elements in the interval is ≥ n+1 -/
lemma sum_k_plus_1_smallest (n k : ℕ) (hk : k ≥ 1) :
    (k + 1) * Nat.ceil (n / (k + 1) : ℚ) + k * (k + 1) / 2 ≥ n + 1 := by
  -- First part: (k+1) * ⌈n/(k+1)⌉ ≥ n
  have h1 : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n := by
    have : Nat.ceil (n / (k + 1) : ℚ) ≥ n / (k + 1) := Nat.le_ceil _
    calc (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_left _ this
      _ = n := by ring
  -- Second part: k(k+1)/2 ≥ 1 for k ≥ 1
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
  -- The k+1 smallest elements in A are: ⌈n/(k+1)⌉, ⌈n/(k+1)⌉+1, ..., ⌈n/(k+1)⌉+k
  -- Their sum is: (k+1) * ⌈n/(k+1)⌉ + 0 + 1 + ... + k = (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2
  -- Any subset of size ≥ k+1 has sum ≥ this value

  -- Lower bound: each element ≥ ⌈n/(k+1)⌉
  have h_bound : ∀ x ∈ s, x ≥ Nat.ceil (n / (k + 1) : ℚ) := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).1

  -- Sum of s ≥ |s| * ⌈n/(k+1)⌉
  have h_sum1 : ∑ i in s, i ≥ s.card * Nat.ceil (n / (k + 1) : ℚ) := by
    calc ∑ i in s, i ≥ ∑ _ in s, Nat.ceil (n / (k + 1) : ℚ) :=
      sum_le_sum (fun x hx => h_bound x hx)
      _ = s.card * Nat.ceil (n / (k + 1) : ℚ) := by rw [sum_const, nsmul_eq_mul]

  -- Since |s| ≥ k+1, we have |s| * ⌈n/(k+1)⌉ ≥ (k+1) * ⌈n/(k+1)⌉
  have h_sum2 : s.card * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * Nat.ceil (n / (k + 1) : ℚ) := by
    exact Nat.mul_le_mul_right _ hcard

  -- And (k+1) * ⌈n/(k+1)⌉ ≥ n
  have h_sum3 : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n := by
    have : Nat.ceil (n / (k + 1) : ℚ) ≥ n / (k + 1) := Nat.le_ceil _
    calc (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_left _ this
      _ = n := by ring

  -- So ∑ i in s, i ≥ n
  -- But we need ≥ n+1. The issue is that the lower bound above is too weak.
  -- We need to account for the fact that elements are distinct and spaced out.

  -- Actually, the correct argument is more subtle. Let's use a different approach:
  -- If |s| ≥ k+1, then s contains at least k+1 distinct elements from A.
  -- The minimum possible sum of k+1 distinct elements from A is:
  -- ⌈n/(k+1)⌉ + (⌈n/(k+1)⌉+1) + ... + (⌈n/(k+1)⌉+k)
  -- = (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2

  -- For now, we'll use a sorry and fix this in the next iteration
  sorry

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
