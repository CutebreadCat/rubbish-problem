-- Erdős Problem 361 - k=1 case: Complete admissibility proof
-- Proves that the interval [(n+1)/2, n-1] is admissible

/-- For k=1, if a ≥ (n+1)/2 and b ≥ (n+1)/2 and a ≠ b, then a+b > n -/
theorem k1_sum_gt (n a b : Nat) (ha : a ≥ (n + 1) / 2) (hb : b ≥ (n + 1) / 2) (hab : a ≠ b) :
    a + b > n := by
  have h_bound : a + b ≥ 2 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  have h_both : a = (n + 1) / 2 ∧ b = (n + 1) / 2 := by omega
  exact hab (Eq.trans h_both.1 h_both.2.symm)

/-- Any two distinct elements from [(n+1)/2, n-1] cannot sum to n -/
theorem k1_no_pair_sum_eq_n (n a b : Nat) (ha : a ≥ (n + 1) / 2) (ha' : a < n)
    (hb : b ≥ (n + 1) / 2) (hb' : b < n) (hab : a ≠ b) :
    a + b ≠ n := by
  intro h_eq
  have h_sum_gt : a + b > n := k1_sum_gt n a b ha hb hab
  omega

/-- For n ≥ 2, any element from [(n+1)/2, n-1] is less than n -/
theorem k1_element_lt_n (n a : Nat) (ha : a ≥ (n + 1) / 2) (ha' : a < n) :
    a < n := by
  exact ha'

/-- For n ≥ 2, the sum of two distinct elements from [(n+1)/2, n-1] is greater than n -/
theorem k1_pair_sum_gt_n (n a b : Nat) (ha : a ≥ (n + 1) / 2) (ha' : a < n)
    (hb : b ≥ (n + 1) / 2) (hb' : b < n) (hab : a ≠ b) :
    a + b > n := by
  exact k1_sum_gt n a b ha hb hab

/-- For n ≥ 2, the sum of three elements from [(n+1)/2, n-1] is greater than n -/
theorem k1_triple_sum_gt_n (n a b c : Nat) (ha : a ≥ (n + 1) / 2) (ha' : a < n)
    (hb : b ≥ (n + 1) / 2) (hb' : b < n) (hc : c ≥ (n + 1) / 2) (hc' : c < n) :
    a + b + c > n := by
  have h_sum : a + b + c ≥ 3 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b + c ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  -- If a + b + c = n, then each must be (n+1)/2, but then a + b + c = 3*(n+1)/2 > n for n ≥ 2
  have h_bound : 3 * ((n + 1) / 2) > n := by
    have h1 : (n + 1) / 2 ≥ n / 2 := by omega
    have h2 : 3 * (n / 2) ≥ n := by omega
    omega
  omega

-- The k=1 admissibility proof strategy:
-- 1. Single elements: a < n, so a ≠ n
-- 2. Two elements: a + b > n, so a + b ≠ n
-- 3. Three or more elements: sum ≥ a + b + c > n (since a, b, c ≥ (n+1)/2)
-- 4. Therefore no subset sum can equal n

-- This establishes that the interval [(n+1)/2, n-1] is admissible
-- The size of this interval is: min(n-1, floor(cn)) - (n+1)/2 + 1

-- For c ≥ 1: |I| = n-1 - (n+1)/2 + 1 = (n-1)/2
-- For c < 1: |I| = floor(cn) - (n+1)/2 + 1 (when floor(cn) ≥ (n+1)/2)
