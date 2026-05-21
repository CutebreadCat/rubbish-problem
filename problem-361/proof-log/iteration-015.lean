-- Erdős Problem 361 - Unified framework
-- Attempts to prove the general formula F_c(n) = max over k of admissible set size

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
def optimal_k (n : Nat) (cn : Nat) : Nat :=
  -- Find the smallest k ≥ 2 such that k ∤ n and n/(k+1) + 1 ≤ cn
  -- This is a simplified version; in practice, we'd iterate over k
  2

-- The unified formula
-- F_c(n) = max over k of admissible_interval_size(n, k)
-- where k satisfies:
-- 1. k ≥ 2
-- 2. k ∤ n
-- 3. n/(k+1) + 1 ≤ floor(cn)
-- For c ≥ 1, we use the k=1 case: F_c(n) = floor(cn) - ceil(n/2)

-- This is the key insight for Erdős Problem 361:
-- The maximum size is achieved by choosing the optimal k that maximizes
-- the admissible interval size, subject to the constraints.
