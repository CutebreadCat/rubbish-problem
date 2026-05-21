# Iteration 009: k=1 Full Admissibility Proof

## Claim

For k=1, the interval [(n+1)/2, min(n-1, floor(cn))] is an admissible set (no subset sum equals n).

## Lean Proof

```lean
-- Erdős Problem 361 - k=1 case: Full admissibility proof
-- Proves that the interval [(n+1)/2, min(n-1, floor(cn))] is admissible

/-- For k=1, if a ≥ (n+1)/2 and b ≥ (n+1)/2 and a ≠ b, then a+b > n -/
theorem k1_sum_gt (n a b : Nat) (ha : a ≥ (n + 1) / 2) (hb : b ≥ (n + 1) / 2) (hab : a ≠ b) :
    a + b > n := by
  have h_bound : a + b ≥ 2 * ((n + 1) / 2) := by omega
  have h_ge_n : a + b ≥ n := by omega
  apply Nat.lt_of_le_of_ne h_ge_n
  intro h_eq
  have h_both : a = (n + 1) / 2 ∧ b = (n + 1) / 2 := by omega
  exact hab (Eq.trans h_both.1 h_both.2.symm)

/-- The interval [lo, hi] contains hi - lo + 1 elements when lo ≤ hi -/
def interval_size (lo hi : Nat) : Nat :=
  if lo ≤ hi then hi - lo + 1 else 0

/-- For k=1, the admissible set is [(n+1)/2, min(n-1, floor(cn))] -/
def k1_interval (n c_times_n : Nat) : Nat × Nat :=
  let lo := (n + 1) / 2
  let hi := min (n - 1) c_times_n
  (lo, hi)

/-- The size of the k=1 admissible set -/
theorem k1_admissible_size (n cn : Nat) (hn : n ≥ 2) (hcn : cn ≥ (n + 1) / 2) :
    let (lo, hi) := k1_interval n cn
    interval_size lo hi = min (n - 1) cn - (n + 1) / 2 + 1 := by
  simp [k1_interval, interval_size]
  constructor
  · -- Show lo ≤ hi
    omega
  · -- Compute the size
    omega

/-- Any two distinct elements from [(n+1)/2, n-1] cannot sum to n -/
theorem k1_no_pair_sum_eq_n (n a b : Nat) (ha : a ≥ (n + 1) / 2) (ha' : a < n)
    (hb : b ≥ (n + 1) / 2) (hb' : b < n) (hab : a ≠ b) :
    a + b ≠ n := by
  intro h_eq
  have h_sum_gt : a + b > n := k1_sum_gt n a b ha hb hab
  omega

/-- Single elements from [(n+1)/2, n-1] are all < n -/
theorem k1_single_lt_n (n a : Nat) (ha : a ≥ (n + 1) / 2) (ha' : a < n) :
    a < n := by
  exact ha'

/-- The k=1 interval construction is admissible: no subset sum equals n -/
-- This is the key theorem showing the interval [(n+1)/2, n-1] is admissible
-- We prove it by showing:
-- 1. Any single element is < n
-- 2. Any two distinct elements sum to > n
-- 3. Therefore no subset sum can equal n
theorem k1_interval_admissible (n : Nat) (hn : n ≥ 2) :
    ∀ s : Finset Nat,
      (∀ x ∈ s, x ≥ (n + 1) / 2 ∧ x < n) →
      s.sum id ≠ n := by
  intro s hs
  -- Case analysis on the size of s
  have h_cases : s.card = 0 ∨ s.card = 1 ∨ s.card ≥ 2 := by omega
  rcases h_cases with (h0 | h1 | h2)
  · -- Empty set: sum is 0, not n (since n ≥ 2)
    simp [Finset.sum_empty]
    omega
  · -- Singleton: element is < n
    obtain ⟨a, ha_mem, rfl⟩ := Finset.card_eq_one.mp h1
    simp [Finset.sum_singleton]
    exact (hs a (Finset.mem_singleton.mpr rfl)).2
  · -- Two or more elements: sum > n
    -- Take two distinct elements a, b from s
    obtain ⟨a, ha_mem⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    have h_s_nonempty : s.Nonempty := ⟨a, ha_mem⟩
    obtain ⟨b, hb_mem, hab_ne⟩ := Finset.exists_ne_of_card_gt_one h2 a
    have ha_props := hs a ha_mem
    have hb_props := hs b hb_mem
    -- a + b > n by k1_sum_gt
    have h_pair_gt : a + b > n := k1_sum_gt n a b ha_props.1 hb_props.1 hab_ne
    -- The sum of all elements is ≥ a + b > n
    have h_sum_ge : s.sum id ≥ a + b := by
      have ha_in : a ∈ s := ha_mem
      have hb_in : b ∈ s := hb_mem
      calc s.sum id ≥ (s.erase b).sum id + b := by
            rw [← Finset.insert_erase hb_in]
            simp [Finset.sum_insert (Finset.not_mem_erase b s)]
          _ ≥ a + b := by
            have ha_erase : a ∈ s.erase b := Finset.mem_erase.mpr ⟨hab_ne.symm, ha_mem⟩
            have h_erase_ge : (s.erase b).sum id ≥ a := by
              have : (s.erase b).sum id ≥ (s.erase b).sum (fun _ => a) := by
                apply Finset.sum_le_sum
                intro x hx
                exact (hs x (Finset.mem_of_mem_erase hx)).1
              simp [Finset.sum_const] at this
              exact this
            omega
    omega
```

## Mathematical Intent

For k=1, we want to show that the interval I = [(n+1)/2, n-1] is admissible, meaning no subset of I sums to n.

The key insight is:
1. **Singleton case**: Any single element a ∈ I satisfies a < n, so a ≠ n.
2. **Pair case**: Any two distinct elements a, b ∈ I satisfy a+b > n (proven in k1_sum_gt).
3. **Larger subsets**: Any subset with ≥2 elements has sum ≥ a+b > n.

Therefore, no subset sum can equal n.

## Weakest Formalization Step

The main challenge is the case analysis on subset size and showing that the sum of a subset with ≥2 elements is at least the sum of any two elements in it. This requires careful Finset manipulation in Lean.

## Possible Counterexample Search

For n=2: I = [1, 1] = {1}. Sum = 1 ≠ 2. ✓
For n=3: I = [2, 2] = {2}. Sum = 2 ≠ 3. ✓
For n=4: I = [2, 3] = {2, 3}. Possible sums: 0, 2, 3, 5. None equal 4. ✓
For n=5: I = [3, 4] = {3, 4}. Possible sums: 0, 3, 4, 7. None equal 5. ✓

## Size Calculation

The size of the admissible set is:
|I| = min(n-1, floor(cn)) - (n+1)/2 + 1

For c ≥ 1: |I| = n-1 - (n+1)/2 + 1 = (n-1)/2 (approximately)
For c < 1: |I| = floor(cn) - (n+1)/2 + 1 (when floor(cn) ≥ (n+1)/2)

## Next Steps

1. Compile this Lean file to verify correctness
2. Generalize to arbitrary k (interval [n/(k+1), n/k])
3. Combine with the c ≥ 1 result for a complete formula
