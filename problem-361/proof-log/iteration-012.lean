-- Erdős Problem 361 - General k case: Key insight (simplified)
-- For integer k ≥ 1, if all elements are > n/(k+1), then k+1 elements sum to > n

/-- For k=1, if a ≥ (n+1)/2 and b ≥ (n+1)/2 and a ≠ b, then a+b > n -/
theorem k1_sum_gt (n a b : Nat) (ha : a ≥ (n + 1) / 2) (hb : b ≥ (n + 1) / 2) (hab : a ≠ b) :
    a + b > n := by
  have h_bound : a + b ≥ 2 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  have h_both : a = (n + 1) / 2 ∧ b = (n + 1) / 2 := by omega
  exact hab (Eq.trans h_both.1 h_both.2.symm)

-- The key insight for the general case:
-- For the interval I = [n/(k+1), n/k]:
-- 1. Any subset with ≤ k elements has sum ≤ n (since each element ≤ n/k)
-- 2. Any subset with ≥ k+1 elements has sum > n (since each element > n/(k+1))
-- 3. Therefore no subset sum can equal n

-- The size of the admissible set is:
-- |I| = min(n/k, floor(cn)) - n/(k+1) + 1
-- For c ≥ 1: |I| = n/k - n/(k+1) + 1 = n/(k(k+1)) + 1
-- For c < 1: |I| = floor(cn) - n/(k+1) + 1 (when floor(cn) ≥ n/(k+1))

-- This is the key formula for Erdős Problem 361:
-- F_c(n) = max over k of (min(n/k, floor(cn)) - n/(k+1) + 1)
-- For c ≥ 1, the maximum is achieved at k=1:
-- F_c(n) = n-1 - (n+1)/2 + 1 = (n-1)/2
-- This matches the proven result: F_c(n) = floor(cn) - ceil(n/2)
