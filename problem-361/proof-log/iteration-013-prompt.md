You are working on Erdős Problem 361 through Lean formalization.

Target for this iteration:
Prove the general k case for Erdős Problem 361

Lean file to create or update:
problem-361/proof-log/iteration-013.lean

Local context:
- Problem: For fixed c > 0 and large n, find the maximum size of A ⊆ {1,...,floor(cn)} such that n is not a subset sum of A.
- c ≥ 1 case: F_c(n) = floor(cn) - ceil(n/2) (proven)
- k=1 case: Interval [(n+1)/2, n-1] is admissible (proven)
- General k case: Interval [n/(k+1), n/k] should be admissible (key insight documented)

Previous iterations:
- iteration-010: k=1 admissibility proven
- iteration-012: General k insight documented

Produce:
1. A precise Lean theorem or lemma statement.
2. A Lean proof attempt as the first fenced code block.
3. Any imports required.
4. A list of all floor, parity, endpoint, and large-n obligations.
5. The weakest formalization step.
6. A suggested narrower Lean target if the proof fails.
