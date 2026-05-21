# Iteration 016: Exploring c < 1 Case

## Claim

For c < 1, find the optimal k that maximizes the admissible interval size.

## Lean Proof

```lean
-- Erdős Problem 361 - Exploring c < 1 case
-- For c < 1, we need to find the optimal k that maximizes the admissible interval size

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

-- The size of the admissible interval for k ≥ 2
def admissible_interval_size (n k : Nat) : Nat :=
  let lo := n / (k + 1) + 1
  let hi := n / k
  if lo ≤ hi then hi - lo + 1 else 0

-- For c < 1, the optimal k is the smallest k ≥ 2 such that k ∤ n
-- and n/(k+1) + 1 ≤ floor(cn)
def optimal_k_for_c_lt_1 (n : Nat) (cn : Nat) : Nat :=
  -- Find the smallest k ≥ 2 such that k ∤ n and n/(k+1) + 1 ≤ cn
  -- This is a simplified version; in practice, we'd iterate over k
  2

-- Example: For c = 3/4, n = 100
-- We need to find k such that:
-- 1. k ≥ 2
-- 2. k ∤ 100
-- 3. n/(k+1) + 1 ≤ floor(3/4 * 100) = 75

-- k=2: 2 | 100, so not admissible
-- k=3: 3 ∤ 100, n/4 + 1 = 26 ≤ 75, admissible
--   interval [26, 33], size = 8
-- k=4: 4 | 100, so not admissible
-- k=5: 5 | 100, so not admissible
-- k=6: 6 ∤ 100, n/7 + 1 = 15 ≤ 75, admissible
--   interval [15, 16], size = 2
-- k=7: 7 ∤ 100, n/8 + 1 = 13 ≤ 75, admissible
--   interval [13, 14], size = 2
-- ...

-- Best: k=3, size = 8

-- For c = 1/2, n = 100
-- floor(cn) = 50
-- k=2: 2 | 100, so not admissible
-- k=3: 3 ∤ 100, n/4 + 1 = 26 ≤ 50, admissible
--   interval [26, 33], size = 8
-- k=4: 4 | 100, so not admissible
-- k=5: 5 | 100, so not admissible
-- k=6: 6 ∤ 100, n/7 + 1 = 15 ≤ 50, admissible
--   interval [15, 16], size = 2
-- ...

-- Best: k=3, size = 8

-- For c = 1/3, n = 100
-- floor(cn) = 33
-- k=2: 2 | 100, so not admissible
-- k=3: 3 ∤ 100, n/4 + 1 = 26 ≤ 33, admissible
--   interval [26, 33], size = 8
-- k=4: 4 | 100, so not admissible
-- k=5: 5 | 100, so not admissible
-- k=6: 6 ∤ 100, n/7 + 1 = 15 ≤ 33, admissible
--   interval [15, 16], size = 2
-- ...

-- Best: k=3, size = 8

-- Key insight: For c < 1, the optimal k is often 3 (when 3 ∤ n)
-- This gives F_c(n) = n/3 - n/4 = n/12

-- For c ≥ 1/3, we can use k=3 (if 3 ∤ n)
-- For c < 1/3, we need to use larger k values

-- General formula for c < 1:
-- F_c(n) = max over k≥2 of (min(n/k, floor(cn)) - n/(k+1) - 1 + 1)
--        = max over k≥2 of (min(n/k, floor(cn)) - n/(k+1))
-- where k satisfies k ∤ n and n/(k+1) + 1 ≤ floor(cn)
```

## Mathematical Intent

This iteration explores the c < 1 case for Erdős Problem 361.

Key insights:
1. For c < 1, we need to find the optimal k ≥ 2 that maximizes the admissible interval size
2. The admissible interval is [n/(k+1)+1, n/k]
3. The size is n/k - n/(k+1) = n/(k(k+1))
4. For c ≥ 1/3, the optimal k is often 3 (when 3 ∤ n)
5. This gives F_c(n) ≈ n/12

## Example Calculations

For c = 3/4, n = 100:
- k=3: interval [26, 33], size = 8
- Best: k=3, size = 8

For c = 1/2, n = 100:
- k=3: interval [26, 33], size = 8
- Best: k=3, size = 8

For c = 1/3, n = 100:
- k=3: interval [26, 33], size = 8
- Best: k=3, size = 8

## General Formula for c < 1

F_c(n) = max over k≥2 of (min(n/k, floor(cn)) - n/(k+1))

where k satisfies:
1. k ≥ 2
2. k ∤ n
3. n/(k+1) + 1 ≤ floor(cn)

## Next Steps

1. ✅ k=1 case proven
2. ✅ k≥2 case proven
3. ✅ Unified framework established
4. ✅ c < 1 case explored
5. Implement optimal k selection algorithm
6. Test with more examples
7. Set up Lake project with Mathlib for more complex proofs

## Verification

The proof compiles successfully with Lean 4.29.1:
```
lean problem-361/proof-log/iteration-016.lean
```

Output: Only unused variable warnings, no errors.
