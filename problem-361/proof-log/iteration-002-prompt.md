You are working on a hard mathematical problem through Lean formalization. Do not claim a full solution unless Lean checks the exact theorem without placeholders.

Target for this iteration:
Prove an interval lower bound for F_c(n) when 0 < c < 1. Specifically, for integer k >= 1, prove that suitable integer intervals near [n/(k+1), n/k] produce admissible sets. More precisely:

For c in (1/(k+1), 1/k] with k >= 1, the set A = {m ∈ ℕ : ⌈n/(k+1)⌉ ≤ m ≤ ⌊n/k⌋} is admissible (no subset sums to n) and has size approximately n/(k(k+1)).

Lean file to create or update:
C:\Users\Lenovo\Desktop\数学小玩具\rubbish-problem\problem-361\proof-log\iteration-002.lean

Local context:
SOURCE SUMMARY:
# Source Summary for Erdős Problem 361

Access date: 2026-05-21

## Primary Page

- Page: https://www.erdosproblems.com/361
- LaTeX source: https://www.erdosproblems.com/latex/361
- Discussion: https://www.erdosproblems.com/forum/thread/361
- Database repository: https://github.com/teorth/erdosproblems
- Formal statement: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/361.lean

The page lists the problem as open and cites `[ErGr80,p.59]`, meaning Erdős and Graham, *Old and New Problems and Results in Combinatorial Number Theory* (1980), page 59.

## Statement

Let `c > 0` and let `n` be a large integer. Find the largest size of a set

```tex
A \subseteq \{1,\ldots,\lfloor cn\rfloor\}
```

such that no subset of `A` has sum exactly `n`. Determine whether this extremal size depends on `n` in an irregular way.

Equivalent notation:

```tex
F_c(n) = \max\{|A| : A \subseteq [1,\lfloor cn\rfloor],\ n \notin \Sigma(A)\},
```

where `\Sigma(A)` is the set of all finite subset sums of `A`.

## Discussion Notes

The comments on the problem page do not claim a solution. They include several useful constructions and partial observations:

- For `c = 3/4`, a computer check was reported for `100 <= n <= 104`, with maxima `34, 37, 32, 38, 35`. This supports irregular dependence on `n`.
- If `p` is the smallest prime not dividing `n`, then choosing all multiples of `p` up to `floor(cn)` avoids subset sums equal to `n`, giving size roughly `cn/p`.
- For `c <= 1`, interval constructions of the form `[n/(k+1), n/k]` avoid a subset sum of `n`, because any `k` elements are too small and any `k+1` elements are too large, after handling endpoints carefully.
- For `c >= 1`, one comment states that pair arguments give the trivial extremal behavior: choose all `m` with `n <= 2m < 2n`, and all `m > n`; sharpness comes from pairs `{x,n-x}`.
- For `1/2 < c < 1`, one comment suggests an upper bound of the form `cn/2 + O(1)` via pair constraints and small additive configurations.
- For `c = 3/4`, several modular constructions based on residues modulo `3`, `5`, or more generally the smallest prime or prime power not dividing `n`, appear to beat simple interval constructions for some congruence classes.

## Nearby Problems

Problem #360 concerns partitioning `{1,...,n-1}` into few classes so that `n` is not a subset sum inside any class. It has known asymptotic solutions and may provide useful techniques, but #361 is a different extremal single-set problem.

Problem #362 concerns concentration of subset sums at a fixed target and is adjacent to anti-concentration methods.

## Literature Keywords

Use these phrases for further search:

- subset sums avoiding one target
- complete sequence and incomplete sequence
- maximal subset of `[N]` with forbidden subset sum
- zero-sum-free or sum-free in cyclic groups, with positive integer constraints
- Erdős Graham subset sums page 59
- additive combinatorics matching-type extremal families

## Caution

This is an open problem on the source page. Any claimed full solution needs adversarial review, independent verification of all endpoint and floor issues, and a literature check before being treated as publishable.

---

RESEARCH DIRECTIONS:
# Research Directions

## Definitions

Let

```tex
F_c(n)=\max\{|A|: A\subseteq [1,\lfloor cn\rfloor],\ n\notin \Sigma(A)\}.
```

Here `\Sigma(A)` is the set of subset sums of `A`, including the empty sum.

## Baseline Constructions

1. Large interval construction:
   Choose numbers in an interval where any allowed number of summands misses `n`. For example, if all elements are greater than `n/(k+1)` and at most `n/k`, then sums of at most `k` terms are too small and sums of at least `k+1` terms are too large, modulo endpoint issues.

2. Modular construction:
   If `q` does not divide `n`, choose all multiples of `q` in `[1,floor(cn)]`. Any subset sum is divisible by `q`, so it cannot be `n`. More elaborate residue-class constructions may be possible.

3. Pair construction:
   For every pair `{x,n-x}` inside `[1,floor(cn)]`, at most one element may be chosen. This gives immediate upper bounds, especially for `c >= 1/2`.

## First Rigorous Lemmas to Try

### Lemma A: pair upper bound

If both `x` and `n-x` lie in `[1,floor(cn)]`, then an admissible set contains at most one of them. Count these pairs exactly with floors.

### Lemma B: `c >= 1` extremal formula

For `c >= 1`, numbers greater than `n` can always be included, and among `1,...,n-1` the pair constraint is sharp by choosing one from each pair `{x,n-x}`. Work out the exact floor-sensitive formula.

### Lemma C: interval lower bound for `c <= 1`

For integer `k >= 1`, prove that suitable integer intervals near `[n/(k+1),n/k]` produce admissible sets. Optimize over `k` as a function of `c`.

### Lemma D: modular lower bound

For the smallest prime `p` not dividing `n`, prove the lower bound `F_c(n) >= floor(floor(cn)/p)`. Then compare this with interval lower bounds.

## Review Checklist for Claimed Proofs

- Does the proof handle floors and endpoint equalities?
- Is the statement asymptotic, exact, or only for a range of `c`?
- Does the proposed extremal set actually avoid all subset sums equal to `n`, not only two-term sums?
- If a modulo construction uses residues beyond multiples, does every possible subset residue avoid `n mod q`?
- Does any upper bound rely on a false independence assumption between pair constraints?
- Are small `n` exceptions separated from asymptotic claims?
- Does the argument contradict the reported computational values for `c = 3/4`, `100 <= n <= 104`?
- Has the proof been tested against random exact subset-sum searches for small `n`?

## Claude Prompt Seed

Ask Claude to produce only one lemma per iteration. A good first request:

```text
Work on Erdős Problem 361. Prove a rigorous exact formula for F_c(n) when c >= 1, including all floor and parity issues. Do not claim anything about 0<c<1. After proving, list the weakest step and possible counterexamples.
```

Previous review notes:


Produce:
1. A precise Lean theorem or lemma statement.
2. A Lean proof attempt as the first fenced code block.
3. Any imports required.
4. A list of all floor, parity, endpoint, and large-n obligations.
5. The weakest formalization step.
6. A suggested narrower Lean target if the proof fails.
