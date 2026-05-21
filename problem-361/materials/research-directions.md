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
