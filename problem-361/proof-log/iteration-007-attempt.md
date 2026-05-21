# Iteration 007: Lemma D - Modular Lower Bound

## Claim

For the smallest prime p not dividing n, the set of multiples of p in [1, ⌊cn⌋] is admissible.
This gives F_c(n) ≥ ⌊⌊cn⌋/p⌋.

## Lean Proof Attempt

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

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
  have h_dvd : ∀ x ∈ s, p ∣ x := by
    intro x hx
    have : x ∈ multiplesSet p (c * n) := hs hx
    exact (Finset.mem_filter.mp this).2
  have h_sum_dvd : p ∣ ∑ i in s, i := subset_sum_dvd p s h_dvd
  rw [h_sum] at h_sum_dvd
  exact hpn h_sum_dvd

/-- The size of the multiples set -/
lemma multiplesSet_card (p N : ℕ) (hp : p ≥ 1) :
    (multiplesSet p N).card = N / p := by
  rw [multiplesSet]
  simp [Finset.card_filter]
  sorry  -- Need to prove this counting lemma

/-- Lower bound: F_c(n) ≥ ⌊cn/p⌋ for the smallest prime p not dividing n -/
theorem modular_lower_bound (n c : ℕ) (hn : n ≥ 2) (hc : c ≥ 1) :
    ∃ p : ℕ, Nat.Prime p ∧ ¬(p ∣ n) ∧
    ∃ A : Finset ℕ, A ⊆ Icc 1 (c * n) ∧
    (∀ s ⊆ A, ∑ i in s, i ≠ n) ∧
    A.card = (c * n) / p := by
  have h_exists : ∃ p : ℕ, Nat.Prime p ∧ ¬(p ∣ n) := by
    sorry  -- Need to prove existence of prime not dividing n
  obtain ⟨p, hp, hpn⟩ := h_exists
  refine ⟨p, hp, hpn, multiplesSet p (c * n), ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ multiplesSet p (c * n) := hx
    have h_mem := (Finset.mem_filter.mp this).1
    exact (Finset.mem_Icc.mp h_mem).1
  · exact multiples_admissible p n c hp hpn
  · exact multiplesSet_card p (c * n) (by linarith [hp.two_le])

end Erdos361
```

## Analysis

**优点**:
1. 核心论证（子集和能被 p 整除，但 n 不能被 p 整除）非常简洁
2. `subset_sum_dvd` 引理使用 `Finset.sum_induction` 证明，应该可以直接通过
3. `multiples_admissible` 定理的证明逻辑清晰

**剩余问题**:
1. `multiplesSet_card` - 需要证明 [1, N] 中 p 的倍数的数量是 ⌊N/p⌋
2. `h_exists` - 需要证明存在不整除 n 的素数

**下一步**:
1. 填补 `multiplesSet_card` 的 sorry - 这是一个标准的计数引理
2. 填补 `h_exists` 的 sorry - 使用 n+1 的素因子
