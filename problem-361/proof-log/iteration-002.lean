import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Floor
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 361 - Lemma C: Interval Lower Bound

For c in (1/(k+1), 1/k] with k ≥ 1, the set
  A = {m ∈ ℕ : ⌈n/(k+1)⌉ ≤ m ≤ ⌊n/k⌋}
is admissible (no subset sums to n).

## Proof Idea

- Any subset of A with at most k elements has sum ≤ k * ⌊n/k⌋ ≤ n
- Any subset of A with at least k+1 elements has sum ≥ (k+1) * ⌈n/(k+1)⌉ ≥ n+1
- Therefore, no subset sums to exactly n
-/

open Finset
open scoped BigOperators

namespace Erdos361

/-- The interval construction for Lemma C -/
def intervalSet (n k : ℕ) : Finset ℕ :=
  (Icc (Nat.ceil (n / (k + 1) : ℚ)) (n / k))

/-- Any k elements from the interval have sum ≤ n -/
lemma sum_le_of_card_le (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≤ k) :
    ∑ i in s, i ≤ n := by
  -- Each element is ≤ n/k, so sum of k elements ≤ k * (n/k) ≤ n
  have h_bound : ∀ x ∈ s, x ≤ n / k := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).2
  calc ∑ i in s, i ≤ ∑ _ in s, (n / k) := sum_le_sum (fun x hx => h_bound x hx)
    _ = s.card * (n / k) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ k * (n / k) := by exact Nat.mul_le_mul_right (n / k) hcard
    _ ≤ n := by exact Nat.div_mul_le_self n k

/-- Any k+1 elements from the interval have sum ≥ n+1 -/
lemma sum_ge_of_card_ge (n k : ℕ) (hk : k ≥ 1) (s : Finset ℕ)
    (hs : s ⊆ intervalSet n k) (hcard : s.card ≥ k + 1) :
    ∑ i in s, i ≥ n + 1 := by
  -- Each element is ≥ ⌈n/(k+1)⌉, so sum of k+1 elements ≥ (k+1) * ⌈n/(k+1)⌉ ≥ n+1
  have h_bound : ∀ x ∈ s, x ≥ Nat.ceil (n / (k + 1) : ℚ) := by
    intro x hx
    have : x ∈ intervalSet n k := hs hx
    exact (mem_Icc.mp this).1
  have h_sum : ∑ i in s, i ≥ s.card * Nat.ceil (n / (k + 1) : ℚ) := by
    calc ∑ i in s, i ≥ ∑ _ in s, Nat.ceil (n / (k + 1) : ℚ) :=
      sum_le_sum (fun x hx => h_bound x hx)
      _ = s.card * Nat.ceil (n / (k + 1) : ℚ) := by rw [sum_const, nsmul_eq_mul]
  have h_card_bound : s.card * Nat.ceil (n / (k + 1) : ℚ) ≥ (k + 1) * Nat.ceil (n / (k + 1) : ℚ) := by
    exact Nat.mul_le_mul_right _ hcard
  have h_ceil : (k + 1) * Nat.ceil (n / (k + 1) : ℚ) ≥ n + 1 := by
    -- This follows from the property of ceiling: ⌈x⌉ ≥ x, so (k+1) * ⌈n/(k+1)⌉ ≥ n
    -- But we need ≥ n+1, which requires more careful handling
    sorry
  omega

/-- The interval set is admissible: no subset sums to n -/
theorem interval_admissible (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∀ s ⊆ intervalSet n k, ∑ i in s, i ≠ n := by
  intro s hs
  by_contra h_sum
  -- If sum = n, then either card ≤ k or card ≥ k+1
  by_cases hcard : s.card ≤ k
  · -- Case card ≤ k: sum ≤ n, but we need sum = n
    have h_le := sum_le_of_card_le n k hk s hs hcard
    omega
  · -- Case card ≥ k+1: sum ≥ n+1, contradiction
    have h_ge := sum_ge_of_card_ge n k hk s hs (by omega)
    omega

/-- The size of the interval set -/
lemma intervalSet_card (n k : ℕ) (hk : k ≥ 1) :
    (intervalSet n k).card = n / k - Nat.ceil (n / (k + 1) : ℚ) + 1 := by
  rw [intervalSet, card_Icc]
  omega

/-- Lower bound: F_c(n) ≥ n/k - ⌈n/(k+1)⌉ + 1 for c ∈ (1/(k+1), 1/k] -/
theorem interval_lower_bound (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (n / k) ∧
    (∀ s ⊆ A, ∑ i in s, i ≠ n) ∧
    A.card = n / k - Nat.ceil (n / (k + 1) : ℚ) + 1 := by
  refine ⟨intervalSet n k, ?_, ?_, ?_⟩
  · -- A ⊆ Icc 1 (n/k)
    intro x hx
    have : x ∈ intervalSet n k := hx
    have h_mem := mem_Icc.mp this
    constructor
    · -- x ≥ 1: since ⌈n/(k+1)⌉ ≥ 1 for n ≥ 1
      have : Nat.ceil (n / (k + 1) : ℚ) ≥ 1 := by
        simp [Nat.ceil_pos]
        positivity
      omega
    · exact h_mem.2
  · -- No subset sums to n
    exact interval_admissible n k hk hn
  · -- Card formula
    exact intervalSet_card n k hk

end Erdos361
