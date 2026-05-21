You are working on a hard mathematical problem through Lean formalization. Do not claim a full solution unless Lean checks the exact theorem without placeholders.

Target for this iteration:
Fill the sorry in sum_ge_of_card_ge. The key is to prove that if s ⊆ A and |s| ≥ k+1, then ∑ i in s, i ≥ (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2.

The argument:
- The k+1 smallest elements in A are: ⌈n/(k+1)⌉, ⌈n/(k+1)⌉+1, ..., ⌈n/(k+1)⌉+k
- Their sum is: (k+1) * ⌈n/(k+1)⌉ + 0 + 1 + 2 + ... + k = (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2
- Any subset of size ≥ k+1 has sum ≥ this value
- And (k+1) * ⌈n/(k+1)⌉ + k(k+1)/2 ≥ n + 1

Lean file to create or update:
C:\Users\Lenovo\Desktop\数学小玩具\rubbish-problem\problem-361\proof-log\iteration-004.lean

Previous review notes:
The proof has a sorry that needs to be filled. The mathematical argument is correct, but the Lean formalization is incomplete.

Produce:
1. A precise Lean theorem or lemma statement.
2. A Lean proof attempt as the first fenced code block.
3. Any imports required.
4. A list of all floor, parity, endpoint, and large-n obligations.
5. The weakest formalization step.
6. A suggested narrower Lean target if the proof fails.
