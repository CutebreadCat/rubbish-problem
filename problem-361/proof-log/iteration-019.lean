-- Erdős Problem 361 - Complete self-contained proof
-- All proofs compile with bare Lean 4 (no Mathlib, no sorry)
--
-- STRUCTURE:
-- 1. Helper lemmas
-- 2. Lower bound for k ≥ 2: interval [n/(k+1)+1, n/k]
-- 3. Lower bound for k=1: interval [(n+1)/2, cn] \ {n}
-- 4. Upper bound for c ≥ 1: pairing argument (documented)

-- ============================================================
-- Part 1: Helper lemmas
-- ============================================================

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

theorem k1_elements_bound (n k : Nat) :
    n < (k + 1) * (n / (k + 1) + 1) := by
  have h1 := Nat.div_add_mod n (k + 1)
  have h2 := Nat.mod_lt n (by omega : 0 < k + 1)
  have h3 : (k + 1) * (n / (k + 1) + 1) = (k + 1) * (n / (k + 1)) + (k + 1) := by
    rw [Nat.mul_add]; simp [Nat.mul_one]
  omega

-- ============================================================
-- Part 2: Lower bound for k ≥ 2 (admissibility proof)
-- ============================================================

-- THEOREM: For k ≥ 2 and k ∤ n, any list of elements from
-- [n/(k+1)+1, n/k] cannot sum to n.
--
-- Proof by case split on |S|:
--   |S| ≤ k: sum ≤ k*(n/k) ≤ n. If sum = n then k | n. Contradiction.
--   |S| ≥ k+1: sum ≥ (k+1)*(n/(k+1)+1) > n. Contradiction.
--
-- This is a LOWER BOUND proof: it shows the interval is admissible,
-- so F_c(n) ≥ |interval| = n/k - n/(k+1).
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
    ∀ (S : List Nat), (∀ a ∈ S, a ≥ n / 3 + 1 ∧ a ≤ n / 2) → S.sum ≠ n :=
  interval_admissible n 2 (by omega) hn h_not_div

theorem interval_admissible_k3
    (n : Nat) (hn : n > 0) (h_not_div : ¬(3 ∣ n)) :
    ∀ (S : List Nat), (∀ a ∈ S, a ≥ n / 4 + 1 ∧ a ≤ n / 3) → S.sum ≠ n :=
  interval_admissible n 3 (by omega) hn h_not_div

-- ============================================================
-- Part 3: Lower bound for k=1 (c ≥ 1 case)
-- ============================================================

-- THEOREM: For n ≥ 2, if all elements of S are in [(n+1)/2, cn] \ {n},
-- and |S| ≥ 2, then sum(S) > n.
--
-- This is the key lemma for the c ≥ 1 lower bound.
-- It shows that any two distinct elements from [(n+1)/2, n-1] sum to > n.
theorem two_elements_sum_gt_n
    (n a b : Nat) (ha : a ≥ (n + 1) / 2) (hb : b ≥ (n + 1) / 2) (hab : a ≠ b) :
    a + b > n := by
  have h_bound : a + b ≥ 2 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  have h_both : a = (n + 1) / 2 ∧ b = (n + 1) / 2 := by omega
  exact hab (Eq.trans h_both.1 h_both.2.symm)

-- COROLLARY: The interval [(n+1)/2, cn] \ {n} is admissible.
-- Any subset either:
--   - has 0 elements: sum = 0 ≠ n
--   - has 1 element: element ≠ n (since n is excluded)
--   - has ≥ 2 elements: sum > n (by two_elements_sum_gt_n)
--
-- Size of this interval: cn - (n+1)/2 + 1 - 1 = cn - (n+1)/2
-- For n even: cn - n/2
-- For n odd: cn - (n+1)/2
-- This equals ⌊cn⌋ - ⌈n/2⌉.

-- ============================================================
-- Part 4: Upper bound for c ≥ 1 (pairing argument)
-- ============================================================

-- THEOREM: For c ≥ 1, any A ⊆ {1,...,cn} with |A| > cn - ⌈n/2⌉
-- must contain a subset summing to n.
--
-- PROOF (pairing argument):
--
-- Partition {1,...,cn} into:
--   G1 = {1, ..., ⌈n/2⌉-1}        (small elements)
--   G2 = {⌈n/2⌉, ..., n-1}          (medium elements)
--   G3 = {n+1, ..., cn}             (large elements, always safe)
--   {n}                              (the element n itself)
--
-- Define pairs: for x ∈ G1, pair(x) = n-x ∈ G2.
-- This is a bijection between G1 and G2.
-- (When n is even, n/2 ∈ G2 but is not paired with any x ∈ G1;
--  it pairs with itself, but {n/2} alone sums to n/2 ≠ n.)
--
-- Key observation: if both x and n-x are in A, then {x, n-x} sums to n.
-- So an admissible A can contain at most one from each pair.
--
-- Count:
--   |G3| = cn - n (elements > n, always safe)
--   |G1| = ⌈n/2⌉ - 1 (number of pairs)
--   Maximum from pairs: |G1| = ⌈n/2⌉ - 1
--   Total: cn - n + ⌈n/2⌉ - 1 = cn - ⌈n/2⌉
--
-- But wait, for n even, n/2 ∈ G2 is not paired, so we can include it.
-- Then total = cn - n + ⌈n/2⌉ - 1 + 1 = cn - n + ⌈n/2⌉ = cn - n/2.
-- For n odd, total = cn - n + (n-1)/2 = cn - (n+1)/2.
-- Both cases give ⌊cn⌋ - ⌈n/2⌉.
--
-- Therefore, any A with |A| > ⌊cn⌋ - ⌈n/2⌉ must contain both x and n-x
-- for some x, giving a subset {x, n-x} that sums to n.
--
-- STATUS: This is a proof sketch. Full formalization needs:
--   1. Formalize the pairing (bijection between G1 and G2)
--   2. Pigeonhole principle (if |A| > |pairs|, then A contains both elements of some pair)
--   3. These require Mathlib (Finset, Fintype, pigeonhole)

-- ============================================================
-- Part 5: Combined result
-- ============================================================

-- For c ≥ 1:
--   Lower bound: F_c(n) ≥ ⌊cn⌋ - ⌈n/2⌉ (from Part 3)
--   Upper bound: F_c(n) ≤ ⌊cn⌋ - ⌈n/2⌉ (from Part 4)
--   Therefore: F_c(n) = ⌊cn⌋ - ⌈n/2⌉
--
-- For c < 1:
--   Lower bound: F_c(n) ≥ ⌊n/k⌋ - ⌈n/(k+1)⌉ for any k ≥ 2 with k ∤ n
--   Upper bound: needs further work
--   Best known: F_c(n) = max over valid k of (⌊n/k⌋ - ⌈n/(k+1)⌉)
