-- Erdős Problem 361 - Complete admissibility proof for interval construction
-- Core theorem: for k ≥ 2 and k ∤ n, interval [n/(k+1)+1, n/k] is admissible

theorem k1_elements_bound (n k : Nat) :
    n < (k + 1) * (n / (k + 1) + 1) := by
  have h1 := Nat.div_add_mod n (k + 1)
  have h2 := Nat.mod_lt n (by omega : 0 < k + 1)
  have h3 : (k + 1) * (n / (k + 1) + 1) = (k + 1) * (n / (k + 1)) + (k + 1) := by
    rw [Nat.mul_add]; simp [Nat.mul_one]
  omega

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

theorem interval_admissible
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
  have h_up : k * (n / k) ≤ n := Nat.mul_div_le n k
  by_cases h_size : S.length ≤ k
  · have h_mul : S.length * (n / k) ≤ k * (n / k) :=
      Nat.mul_le_mul_right (n / k) h_size
    have h_n_le : n ≤ k * (n / k) := by omega
    have h_eq : k * (n / k) = n := by omega
    exact h_not_div ⟨n / k, h_eq.symm⟩
  · have h_len : S.length ≥ k + 1 := by omega
    have h_mul_ge : S.length * (n / (k + 1) + 1) ≥ (k + 1) * (n / (k + 1) + 1) :=
      Nat.mul_le_mul_right (n / (k + 1) + 1) h_len
    omega

-- Specializations
theorem interval_admissible_k2
    (n : Nat) (hn : n > 0) (h_not_div : ¬(2 ∣ n)) :
    ∀ (S : List Nat),
      (∀ a ∈ S, a ≥ n / 3 + 1 ∧ a ≤ n / 2) →
      S.sum ≠ n :=
  interval_admissible n 2 (by omega) hn h_not_div

theorem interval_admissible_k3
    (n : Nat) (hn : n > 0) (h_not_div : ¬(3 ∣ n)) :
    ∀ (S : List Nat),
      (∀ a ∈ S, a ≥ n / 4 + 1 ∧ a ≤ n / 3) →
      S.sum ≠ n :=
  interval_admissible n 3 (by omega) hn h_not_div

theorem interval_admissible_k4
    (n : Nat) (hn : n > 0) (h_not_div : ¬(4 ∣ n)) :
    ∀ (S : List Nat),
      (∀ a ∈ S, a ≥ n / 5 + 1 ∧ a ≤ n / 4) →
      S.sum ≠ n :=
  interval_admissible n 4 (by omega) hn h_not_div

-- The interval [n/4+1, n/3] has size n/3 - n/4 = n/12 (approximately).
-- For c = 3/4 and 3 ∤ n, this interval lies in [1, 3n/4],
-- giving F_{3/4}(n) ≥ n/12.
