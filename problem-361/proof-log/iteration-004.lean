import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Floor
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 361 - Lemma C: Interval Lower Bound (Iteration 004)

For c in (1/(k+1), 1/k] with k ≥ 1, the set
  A = {m ∈ ℕ : ⌈n/(k+1)⌉ ≤ m ≤ ⌊n/k⌋}
is admissible (no subset sums to n).

## Proof Strategy

Case 1: |A| ≤ k → any subset has ≤ k elements → sum ≤ k * ⌊n/k⌋ ≤ n
Case 2: |A| ≥ k+1 → sum of k+1 smallest elements ≥ n+1

The k+1 smallest elements are: ⌈n/(k+1)⌉, ⌈n/(k+1)⌉+1, ..., ⌈n/(k+1)⌉+k
Their sum = (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2 ≥ n+1
-/

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
  -- Part 1: (k+1) * ⌈n/(k+1)⌉ ≥ n
  have h1 : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n := by
    have : Nat.ceil (n / (k + 1) : ℚ) ≥ n / (k + 1) := Nat.le_ceil _
    calc (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * (n / (k + 1)) :=
      Nat.mul_le_mul_left _ this
      _ = n := by ring
  -- Part 2: k(k+1)/2 ≥ 1 for k ≥ 1
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
  -- The k+1 smallest elements in A are: ⌈n/(k+1)⌉, ⌈n/(k+1)⌉+1, ..., ⌈n/(k+1)⌉+k
  -- Any subset of size ≥ k+1 has sum ≥ sum of these k+1 smallest elements

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

  -- So ∑ i in s, i ≥ (k+1) * ⌈n/(k+1)⌉
  -- But we need to add k(k+1)/2 to account for the distinctness of elements
  -- This requires a more detailed argument about the structure of s

  -- For now, we use a sorry to indicate this gap
  sorry

/-- Any subset of size ≥ k+1 has sum ≥ n+1 -/
lemma sum_ge_of_card_ge (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≥ k + 1) :
    ∑ i in s, i ≥ n + 1 := by
  -- Use the helper lemma
  have h_sum := sum_distinct_elements_ge n k hk s hs hcard
  -- And the fact that (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2 ≥ n+1
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
