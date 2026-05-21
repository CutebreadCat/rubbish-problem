# Verified Lemma: Exact Formula for `c >= 1`

## Claim

Let `c >= 1`, `n >= 1`, and `N = floor(cn)`. Then

```tex
F_c(n) = N - \lceil n/2\rceil.
```

Equivalently, the largest `A \subseteq [1,N]` with no subset sum equal to `n` has size

```tex
\lfloor cn\rfloor - \lceil n/2\rceil.
```

## Construction

Take

```tex
A = \{m \in \mathbb N : n/2 \le m < n\}\cup\{m\in\mathbb N:n<m\le N\}.
```

In integer terms, this means all integers from `ceil(n/2)` to `n-1`, plus all integers from `n+1` to `N`.

Its size is

```tex
\lfloor n/2\rfloor + (N-n) = N-\lceil n/2\rceil.
```

No subset of `A` sums to `n`:

- any element greater than `n` is already too large to appear in such a subset;
- among the elements below `n`, every element is at least `n/2`;
- two distinct chosen elements below `n` have sum greater than `n`;
- when `n` is even, the single element `n/2` alone is not `n`, and it cannot be used twice.

So the construction is admissible.

## Upper Bound

Since `c >= 1`, the interval `[1,N]` contains `n`. Any admissible set must omit `n`, otherwise the one-element subset `{n}` sums to `n`.

For each unordered pair

```tex
\{x,n-x\},\quad 1\le x<n-x\le n-1,
```

an admissible set contains at most one of the two elements. There are `floor((n-1)/2)` such pairs. Therefore at least

```tex
1+\lfloor(n-1)/2\rfloor=\lceil n/2\rceil
```

elements of `[1,N]` must be excluded: the element `n`, and at least one element from each pair. Hence

```tex
|A|\le N-\lceil n/2\rceil.
```

The construction attains this bound, proving the formula.

## Review Notes

- The proof uses only positivity of elements, so elements greater than `n` are harmless.
- The parity case `n` even is handled by noting that subset sums cannot reuse `n/2`.
- This does not address `0 < c < 1`.
