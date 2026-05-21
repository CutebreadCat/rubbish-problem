Target: Prove Lemma D - modular lower bound.

For the smallest prime p not dividing n, the set of multiples of p in [1, ⌊cn⌋] is admissible.
This gives F_c(n) ≥ ⌊⌊cn⌋/p⌋.

Proof: Any subset sum of multiples of p is divisible by p. But p does not divide n (by choice of p). So no subset sums to n.

This is simpler than Lemma C because the admissibility argument is purely modular.

Produce a Lean proof of this lemma.
