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
