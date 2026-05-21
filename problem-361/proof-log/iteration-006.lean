import Mathlib.Data.Nat.Interval
import Mathlib.Data.Nat.Floor
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 361 - Lemma C: Interval Lower Bound (Iteration 006)

For c in (1/(k+1), 1/k] with k ≥ 1, the set
  A = {m ∈ ℕ : ⌈n/(k+1)⌉ ≤ m ≤ ⌊n/k⌋}
is admissible (no subset sums to n).

## Proof Strategy (New Approach)

Prove by contradiction: assume ∑ i in s, i = n and |s| ≥ k+1.

1. Each element ≥ ⌈n/(k+1)⌉
2. So ∑ i in s, i ≥ |s| * ⌈n/(k+1)⌉
3. |s| * ⌈n/(k+1)⌉ ≥ (k+1) * ⌈n/(k+1)⌉
4. (k+1) * ⌈n/(k+1)⌉ ≥ n
5. So ∑ i in s, i ≥ n
6. But elements are distinct, so ∑ i in s, i > (k+1) * ⌈n/(k+1)⌉
7. Contradiction with ∑ i in s, i = n

The key insight: if elements are distinct and all ≥ ⌈n/(k+1)⌉, then the minimum sum is achieved by taking the k+1 smallest elements: ⌈n/(k+1)⌉, ⌈n/(k+1)⌉+1, ..., ⌈n/(k+1)⌉+k.
-/

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
  have h_sum_ge_n : ∑ i in s, i ≥ n := by omega

  -- But we need to show ∑ i in s, i > n to get a contradiction
  -- The key insight: elements are distinct, so the sum is strictly greater

  -- For now, we use sorry
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
