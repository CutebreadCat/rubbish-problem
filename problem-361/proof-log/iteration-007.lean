import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 361 - Lemma D: Modular Lower Bound

For the smallest prime p not dividing n, the set of multiples of p in [1, ⌊cn⌋] is admissible.
This gives F_c(n) ≥ ⌊⌊cn⌋/p⌋.

## Proof

Any subset sum of multiples of p is divisible by p.
But p does not divide n (by choice of p).
So no subset sums to n.
-/

open Finset
open scoped BigOperators

namespace Erdos361

/-- The set of multiples of p in [1, N] -/
def multiplesSet (p N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => p ∣ x)

/-- Any subset sum of multiples of p is divisible by p -/
lemma subset_sum_dvd (p : ℕ) (s : Finset ℕ) (hs : ∀ x ∈ s, p ∣ x) :
    p ∣ ∑ i in s, i := by
  apply Finset.sum_induction
  · intro a b ha hb
    exact dvd_add ha hb
  · exact dvd_zero p
  · exact hs

/-- The multiples set is admissible: no subset sums to n -/
theorem multiples_admissible (p n c : ℕ) (hp : Nat.Prime p) (hpn : ¬(p ∣ n))
    (s : Finset ℕ) (hs : s ⊆ multiplesSet p (c * n)) :
    ∑ i in s, i ≠ n := by
  by_contra h_sum
  -- All elements in s are multiples of p
  have h_dvd : ∀ x ∈ s, p ∣ x := by
    intro x hx
    have : x ∈ multiplesSet p (c * n) := hs hx
    exact (Finset.mem_filter.mp this).2
  -- So the sum is divisible by p
  have h_sum_dvd : p ∣ ∑ i in s, i := subset_sum_dvd p s h_dvd
  -- But ∑ i in s, i = n, so p ∣ n
  rw [h_sum] at h_sum_dvd
  -- Contradiction with hpn
  exact hpn h_sum_dvd

/-- The size of the multiples set -/
lemma multiplesSet_card (p N : ℕ) (hp : p ≥ 1) :
    (multiplesSet p N).card = N / p := by
  rw [multiplesSet]
  -- Count multiples of p in [1, N]
  -- This is ⌊N/p⌋
  simp [Finset.card_filter]
  sorry  -- Need to prove this counting lemma

/-- Lower bound: F_c(n) ≥ ⌊cn/p⌋ for the smallest prime p not dividing n -/
theorem modular_lower_bound (n c : ℕ) (hn : n ≥ 2) (hc : c ≥ 1) :
    ∃ p : ℕ, Nat.Prime p ∧ ¬(p ∣ n) ∧
    ∃ A : Finset ℕ, A ⊆ Icc 1 (c * n) ∧
    (∀ s ⊆ A, ∑ i in s, i ≠ n) ∧
    A.card = (c * n) / p := by
  -- Let p be the smallest prime not dividing n
  -- Such a prime exists because n ≥ 2
  have h_exists : ∃ p : ℕ, Nat.Prime p ∧ ¬(p ∣ n) := by
    -- The smallest prime factor of n+1 does not divide n
    -- Or we can use the fact that there are infinitely many primes
    sorry
  obtain ⟨p, hp, hpn⟩ := h_exists
  refine ⟨p, hp, hpn, multiplesSet p (c * n), ?_, ?_, ?_⟩
  · -- A ⊆ Icc 1 (c * n)
    intro x hx
    have : x ∈ multiplesSet p (c * n) := hx
    have h_mem := (Finset.mem_filter.mp this).1
    exact (Finset.mem_Icc.mp h_mem).1
  · -- No subset sums to n
    exact multiples_admissible p n c hp hpn
  · -- Card formula
    exact multiplesSet_card p (c * n) (by linarith [hp.two_le])

end Erdos361
