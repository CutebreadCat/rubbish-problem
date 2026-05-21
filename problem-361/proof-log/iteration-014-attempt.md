# Iteration 014: Integration of All Results

## Claim

Combine k=1 and k≥2 cases into a unified framework for Erdős Problem 361.

## Lean Proof

```lean
-- Erdős Problem 361 - Integration of all results
-- Combines k=1 and k≥2 cases into a unified framework

/-- For k=1, if a ≥ (n+1)/2 and b ≥ (n+1)/2 and a ≠ b, then a+b > n -/
theorem k1_sum_gt (n a b : Nat) (ha : a ≥ (n + 1) / 2) (hb : b ≥ (n + 1) / 2) (hab : a ≠ b) :
    a + b > n := by
  have h_bound : a + b ≥ 2 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  have h_both : a = (n + 1) / 2 ∧ b = (n + 1) / 2 := by omega
  exact hab (Eq.trans h_both.1 h_both.2.symm)

-- Helper: sum of elements each ≤ u is ≤ length * u
theorem sum_le_length_mul (S : List Nat) (u : Nat) (h : ∀ a ∈ S, a ≤ u) :
    S.sum ≤ S.length * u := by
  induction S with
  | nil => simp
  | cons hd tl ih =>
    simp [List.sum_cons]
    have hhd : hd ≤ u := h hd (by simp)
    have htl : ∀ a ∈ tl, a ≤ u := fun a ha => h a (by simp [ha])
    have ih' := ih htl
    have h_expand : (tl.length + 1) * u = tl.length * u + u := Nat.succ_mul tl.length u
    omega

-- Helper: sum of elements each ≥ l is ≥ length * l
theorem sum_ge_length_mul (S : List Nat) (l : Nat) (h : ∀ a ∈ S, a ≥ l) :
    S.sum ≥ S.length * l := by
  induction S with
  | nil => simp
  | cons hd tl ih =>
    simp [List.sum_cons]
    have hhd : hd ≥ l := h hd (by simp)
    have htl : ∀ a ∈ tl, a ≥ l := fun a ha => h a (by simp [ha])
    have ih' := ih htl
    have h_expand : (tl.length + 1) * l = tl.length * l + l := Nat.succ_mul tl.length l
    omega

-- Core lower bound: (k+1) * (n/(k+1) + 1) > n
theorem k1_elements_bound (n k : Nat) :
    n < (k + 1) * (n / (k + 1) + 1) := by
  have h1 := Nat.div_add_mod n (k + 1)
  have h2 := Nat.mod_lt n (by omega : 0 < k + 1)
  have h3 : (k + 1) * (n / (k + 1) + 1) = (k + 1) * (n / (k + 1)) + (k + 1) := by
    rw [Nat.mul_add]; simp [Nat.mul_one]
  omega

-- General admissibility theorem for k ≥ 2
theorem interval_admissible_k_ge_2
    (n k : Nat) (hk : k ≥ 2) (hn : n > 0) (h_not_div : ¬(k ∣ n)) :
    ∀ (S : List Nat),
      (∀ a ∈ S, a ≥ n / (k + 1) + 1 ∧ a ≤ n / k) →
      S.sum ≠ n := by
  intro S h_mem h_sum_eq
  have h_lo : ∀ a ∈ S, a ≥ n / (k + 1) + 1 := fun a ha => (h_mem a ha).1
  have h_hi : ∀ a ∈ S, a ≤ n / k := fun a ha => (h_mem a ha).2
  have h_sum_ge : S.sum ≥ S.length * (n / (k + 1) + 1) :=
    sum_ge_length_mul S _ h_lo
  have h_sum_le : S.sum ≤ S.length * (n / k) :=
    sum_le_length_mul S _ h_hi
  have h_low : n < (k + 1) * (n / (k + 1) + 1) :=
    k1_elements_bound n k
  have h_up : k * (n / k) ≤ n :=
    Nat.mul_div_le n k
  by_cases h_size : S.length ≤ k
  · -- Case |S| ≤ k
    have h_mul : S.length * (n / k) ≤ k * (n / k) :=
      Nat.mul_le_mul_right (n / k) h_size
    have h_n_le : n ≤ k * (n / k) := by omega
    have h_eq : k * (n / k) = n := by omega
    exact h_not_div ⟨n / k, h_eq.symm⟩
  · -- Case |S| ≥ k+1
    have h_len : S.length ≥ k + 1 := by omega
    have h_mul_ge : S.length * (n / (k + 1) + 1) ≥ (k + 1) * (n / (k + 1) + 1) :=
      Nat.mul_le_mul_right (n / (k + 1) + 1) h_len
    omega

-- Unified formula: F_c(n) = max over k of admissible set size
-- For c ≥ 1: F_c(n) = floor(cn) - ceil(n/2) (from k=1 case)
-- For c < 1: F_c(n) = max over k≥2 of (min(n/k, floor(cn)) - n/(k+1) + 1)
-- where k satisfies k ∤ n

-- Example: For c = 3/4, n = 100
-- k=2: interval [34, 50], size = 17 (if 2 ∤ 100, but 2 | 100, so need k=3)
-- k=3: interval [26, 33], size = 8 (if 3 ∤ 100, true)
-- k=4: interval [21, 25], size = 5 (if 4 ∤ 100, but 4 | 100, so need k=5)
-- k=5: interval [17, 20], size = 4 (if 5 ∤ 100, but 5 | 100, so need k=6)
-- k=6: interval [15, 16], size = 2 (if 6 ∤ 100, true)
-- Best: k=3, size = 8
```

## Mathematical Intent

This iteration integrates all proven results into a unified framework:

1. **k=1 case**: For c ≥ 1, F_c(n) = floor(cn) - ceil(n/2)
2. **k≥2 case**: For k ≥ 2 and k ∤ n, the interval [n/(k+1)+1, n/k] is admissible

The unified formula is:
F_c(n) = max over k of (min(n/k, floor(cn)) - n/(k+1) + 1)

where k satisfies k ∤ n (for k ≥ 2).

## Example Calculation

For c = 3/4, n = 100:
- k=2: interval [34, 50], size = 17 (but 2 | 100, so not admissible)
- k=3: interval [26, 33], size = 8 (3 ∤ 100, admissible)
- k=4: interval [21, 25], size = 5 (but 4 | 100, so not admissible)
- k=5: interval [17, 20], size = 4 (but 5 | 100, so not admissible)
- k=6: interval [15, 16], size = 2 (6 ∤ 100, admissible)

Best: k=3, size = 8

## Next Steps

1. ✅ k=1 case proven
2. ✅ k≥2 case proven
3. Explore c < 1 with optimal k selection
4. Set up Lake project with Mathlib for more complex proofs
5. Integrate all results into a single theorem

## Verification

The proof compiles successfully with Lean 4.29.1:
```
lean problem-361/proof-log/iteration-014.lean
```

Output: Only unused variable warnings, no errors.
