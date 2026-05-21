theorem interval_admissible_k2 (n : Nat) (hn : n > 0) (h_not_div : ¬(2 ∣ n)) :
    ∀ (S : List Nat), (∀ a ∈ S, a ≥ n / 3 + 1 ∧ a ≤ n / 2) → S.sum ≠ n
