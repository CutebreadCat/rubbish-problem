# Proof Review Rubric

Use this checklist after every attempted Lean proof.

## Lean Check

- Record the exact command: `lake env lean <file>`, `lake build`, or `lean <file>`.
- Save compiler output, including line and column errors.
- Verify whether the claimed lemma contains `sorry`, `admit`, `axiom`, or an unproved placeholder.
- Separate import/toolchain failures from proof failures.
- Prefer reducing the theorem statement to a smaller lemma when Lean errors show missing infrastructure.

## Validity

- State every quantifier and range.
- Check endpoint cases and floors.
- Identify whether the proof is exact, asymptotic, conditional, or heuristic.
- Confirm the proof does not assume the conclusion in another form.
- Try to build a counterexample from the proof's weakest inequality.

## Mathematical Fit

- Compare the claim with known comments, computations, and source notes.
- Check whether the claim would imply a stronger result than intended.
- For subset-sum problems, distinguish two-term obstructions from arbitrary subset sums.
- For modular constructions, compute the full set of possible residues of subset sums.

## Output Standard

Each iteration should produce:

1. Claim.
2. Lean statement and proof attempt.
3. Lean check command and output.
4. Weakest formalization step.
5. Counterexample search.
6. Review verdict: `pass`, `revise`, or `reject`.
7. Next narrower Lean target.
