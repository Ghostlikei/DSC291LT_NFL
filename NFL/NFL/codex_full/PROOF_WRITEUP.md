# Proof Writeup for the Full No-Free-Lunch Proofs

This note explains the proof strategy behind the two larger formalizations in
this folder:

- `WolpertMacready.lean`
- `BatchStochastic.lean`

The goal is not only to describe the mathematical argument, but also to explain
how the argument is broken into Lean-sized lemmas.

## Wolpert-Macready

### The Natural-Language Roadmap

The Wolpert-Macready theorem says that, for non-revisiting search algorithms,
averaging over all objective functions makes every algorithm induce the same
histogram of observed value sequences.

Concretely, if `A1` and `A2` are two search algorithms, `c : List Y` is a fixed
observation sequence of length `m`, and `m <= Fintype.card X`, then:

```lean
(sum over f : X -> Y, observations A1 f m c)
  =
(sum over f : X -> Y, observations A2 f m c)
```

The informal proof has three moving parts.

1. Separate query choice from objective-function labels.

   The algorithm chooses query points using the labelled history it has seen so
   far. Once a future observation sequence `c` is fixed, the only question is:
   how many target functions are compatible with the labelled trace that would
   produce `c`?

2. Count compatible targets from a labelled history.

   If the labelled history queries distinct points, then it fixes exactly those
   coordinates of the target function. All unqueried points are free. Therefore
   the number of compatible functions is:

   ```text
   |Y| ^ (|X| - length(history))
   ```

3. Prove an invariant stronger than the final theorem.

   Instead of proving only the empty-history theorem, prove a continuation
   statement:

   ```text
   average future observation mass from history h and future values c
     =
   |Y| ^ (|X| - length(h) - length(c))
   ```

   This quantity is independent of the algorithm. The final theorem follows by
   applying this invariant to the empty history.

The original plan also introduced a target-independent query process
`queryTraceFrom`. That object is still useful as a conceptual scaffold and for
support facts, but the final proof becomes cleaner by proving the stronger
`avgFuture_eq_pow` invariant directly.

### The Lean Proof Plan

The Lean proof begins by defining the stochastic search model.

Important objects:

- `SearchAlg X Y`: a stochastic algorithm with
  `nextQuery : List (X * Y) -> PMF X`.
- `SearchAlg.NonRevisiting`: previously queried points have probability zero.
- `trace`: the PMF over labelled traces after `m` steps.
- `observations`: the PMF over observed value lists.
- `traceFrom` and `observationsFrom`: continuation versions starting from a
  labelled history.

The continuation objects are useful because the inductive proof peels off the
next requested observation value.

Key recursion lemmas:

- `observationsFrom_succ`
- `pmf_map_cons_apply`
- `observationsFrom_cons_apply`
- `traceFrom_append_rec`
- `trace_eq_traceFrom_nil`
- `observations_eq_observationsFrom_nil`

These lemmas let Lean rewrite the original theorem into a statement about
future observations from an arbitrary history.

### Counting Compatible Targets

The central combinatorial predicate is:

```lean
def Consistent (f : X -> Y) (h : List (X * Y)) : Prop :=
  forall xy in h, f xy.1 = xy.2
```

The proof needs a bijection:

```text
{f : X -> Y // Consistent f h}
  equivalent to
{x : X // x not in queried points of h} -> Y
```

This is only true when `h.map Prod.fst` is `Nodup`, because then every queried
point has a unique label.

Lean lemmas that build this bijection:

- `eq_of_mem_of_fst_eq_of_nodup_map`: if two entries in a nodup query history
  have the same query point, they are the same labelled pair.
- `queriedLabel`: recovers the unique label attached to a queried point.
- `queriedLabel_eq_of_mem`: proves that `queriedLabel` returns the actual label
  in the history.
- `extendFromComplement`: extends arbitrary labels on the unqueried complement
  to a full target function.
- `extendFromComplement_consistent`: the extension agrees with the history.
- `consistentEquivComplement`: the actual equivalence.

Then the finite count is stated as:

- `consistentCount_eq_pow_card`

It proves:

```text
consistentCount X Y h = |Y| ^ (|X| - h.length)
```

under the `Nodup` hypothesis.

### The Main Averaging Invariant

The key theorem is:

```lean
avgFuture_eq_pow
```

It states that for a non-revisiting algorithm `A`, a nodup labelled history `h`,
and a future value list `c`, if there is enough domain left, then:

```text
avgFuture A h c
  =
|Y| ^ (|X| - (h.length + c.length))
```

The proof is by induction on `c`.

Base case:

- No future observations remain.
- `avgFuture` becomes the number of target functions compatible with `h`.
- Use `consistentCount_eq_pow_card`.

Inductive step:

- Suppose `c = y :: ys`.
- Use `avgFuture_cons` to rewrite the average as a sum over the algorithm's
  next query:

  ```text
  sum_x A.nextQuery h x * avgFuture A (h.concat (x, y)) ys
  ```

- If `x` was already queried, `A.nextQuery h x = 0` by `NonRevisiting`.
- If `x` is fresh, the appended history is still nodup, and the induction
  hypothesis applies.
- Every nonzero term has the same constant value:

  ```text
  |Y| ^ (|X| - (h.length + (y :: ys).length))
  ```

- Pull that constant out of the PMF sum and use `PMF.tsum_coe`, which says that
  the total mass of a PMF is one.

This removes all algorithm dependence.

### Final Assembly

The final theorem is:

```lean
wolpert_macready
```

The proof starts `avgFuture_eq_pow` from the empty history:

- empty history is nodup;
- every target is consistent with the empty history;
- `observations_eq_observationsFrom_nil` bridges the original theorem statement
  to the continuation statement;
- both algorithms reduce to the same power of `Fintype.card Y`.

The average-performance corollary:

```lean
wolpert_macready_avg
```

then multiplies the histogram identity by an arbitrary score functional and
sums over observation lists.

## Batch Stochastic NFL

### The Natural-Language Roadmap

The batch stochastic theorem says that, for every deterministic learner `A` and
sample size `m` with `2m <= |X|`, there is a realizable distribution `D` such
that with probability at least `1/7`, the learner returns a hypothesis with risk
at least `1/8`.

There is one important edge case: if `X` is empty and `m = 0`, there is no
probability measure on `X * Bool`. Therefore the full theorem includes
`[Nonempty X]`.

The proof splits into two cases.

1. Zero samples.

   Pick a point `x0 : X`. Label it with the opposite of what `A []` predicts.
   The Dirac distribution on that labelled point is realizable by a constant
   target, but `A []` has risk one. Therefore the failure probability is one,
   hence at least `1/7`.

2. Positive samples.

   Choose a support set `C` of size `2m`. Think of a random target
   `f : C -> Bool`, and let `D_f` be the uniform distribution on the graph:

   ```text
   {(x, f x) | x in C}
   ```

   For any fixed sample of `m` support points, at most `m` distinct support
   points are seen. Since `|C| = 2m`, at least `m` support points are unseen.

   At an unseen point `z`, pair the two targets that agree everywhere except at
   `z`. The learner sees the same training sample under both targets, so it
   outputs the same hypothesis. Exactly one of the two possible labels at `z`
   is wrong. Therefore the paired loss at `z` sums to one.

   Summing over unseen points gives average risk at least `1/4`.

   Finally, use a finite probabilistic-method argument:

   - if a target has bad-sample rate below `1/7`, then its average sample risk
     is strictly below `1/4`;
   - but the global average over all targets and samples is at least `1/4`;
   - contradiction. So some target has bad-sample rate at least `1/7`.

   Then bridge this finite bad-sample rate to the measure-theoretic
   `failureProb` in the theorem.

### The Lean Proof Plan

The file first defines the theorem's analytic objects:

- `Learner X`
- `zeroOneLoss`
- `risk`
- `failureProb`

The empty-domain diagnostic is:

- `no_probability_measure_empty_prod_bool`

The zero-sample case is:

- `batch_stochastic_NFL_zero`

It uses `Measure.dirac`, `integral_dirac`, and the fact that `Fin 0` has only
the empty sample.

### Uniform Graph Distributions

For the positive case, the proof constructs a uniform realizable distribution
from a target restricted to a finite support.

Important definitions and lemmas:

- `graphEmbedding`
- `graphFinset`
- `graphPMF`
- `risk_graphPMF_self_zero`
- `supportRisk`
- `risk_graphPMF_eq_supportRisk`
- `supportRisk_nonneg`
- `supportRisk_le_one`
- `exists_support_card`

The key bridge here is `risk_graphPMF_eq_supportRisk`: it converts the
measure-theoretic integral into a finite average over the support set. In Lean
this is proved with `PMF.integral_eq_sum` and the explicit formula for
`PMF.uniformOfFinset`.

### Abstract Support Model

The main counting argument is easier if the support is an abstract finite type
`Z`, embedded into `X` by `e : Z -> X`.

Important definitions:

- `abstractSampleList e f S`: the labelled training list produced by target
  `f : Z -> Bool` on sample `S : Fin m -> Z`.
- `abstractRisk e f h`: uniform risk over the abstract support.

The key pairing device is:

- `splitAt z`

This equivalence decomposes a label function `Z -> Bool` into:

```text
labels away from z, and the label at z
```

Then the unseen-point loss lemma is:

- `loss_sum_over_labels_at_unseen`

It proves that if the sample never visits `z`, then:

```text
sum over f : Z -> Bool of loss at z
  =
number of labellings away from z
```

The Lean proof works by:

1. rewriting the sum over `Z -> Bool` using `splitAt z`;
2. grouping the two labels `false` and `true` at `z`;
3. proving the training samples are identical for the paired targets with
   `abstractSampleList_splitAt_false_eq_true`;
4. using `zeroOneLoss_false_add_true`.

### Seen and Unseen Points

For a fixed sample `S : Fin m -> Z`, define:

- `seenFinset S`
- `unseenFinset S`

The important cardinality lemmas are:

- `seenFinset_card_le`: a sample of length `m` sees at most `m` distinct points.
- `unseenFinset_card_ge_half`: if `|Z| = 2m`, then at least `m` points are
  unseen.

These are deliberately stated as finite-set lemmas before any probability
enters the proof.

### Fixed-Sample Average Risk Lower Bound

The heart of the proof is:

```lean
sum_abstractRisk_fixed_sample_ge
```

It proves:

```text
|Z -> Bool| / 4
  <=
sum over f : Z -> Bool of abstractRisk e f (A (abstractSampleList e f S))
```

for each fixed sample `S`.

The proof expands `abstractRisk`, swaps sums over targets and support points,
drops the nonnegative seen-point contribution, and applies
`loss_sum_over_labels_at_unseen` on every unseen point. Since there are at least
`m` unseen points and `|Z| = 2m`, the lower bound simplifies to `1/4` of the
number of targets.

### From Average Risk to a Bad Target

The finite bad-sample set is:

```lean
abstractBadSamples e A f m
```

and the finite bad-sample rate is:

```lean
abstractFailureRate e A f m
```

The proof then establishes:

- `abstractRisk_le_one_of_card_pos`
- `sum_piecewise_one_eighth`
- `sum_abstractRisk_lt_of_failureRate_lt`
- `exists_abstractFailureRate_ge`

The important inequality is:

```text
if failureRate(f) < 1/7, then average sample risk for f < 1/4
```

Why?

- On bad samples, risk is at most `1`.
- On good samples, risk is less than `1/8`.
- If fewer than `1/7` of samples are bad, then

  ```text
  average risk < (1/7) * 1 + (6/7) * (1/8) = 1/4
  ```

In Lean this is encoded by `sum_piecewise_one_eighth`, which rewrites the
piecewise upper bound as:

```text
total_samples / 8 + (7 / 8) * bad_samples
```

Then `exists_abstractFailureRate_ge` argues by contradiction. If every target
had failure rate below `1/7`, summing the strict upper bound over all targets
would contradict the fixed-sample lower bound summed over all samples.

### Bridging the Finite Count to `failureProb`

The finite result is about samples `Fin m -> Z`. The theorem's `failureProb` is
about samples `Fin m -> X * Bool` drawn from a product measure. The final bridge
maps support-indexed samples into labelled samples from the graph.

Important definitions and lemmas:

- `supportTraceEmbedding`
- `supportTrace_list_eq_abstractSampleList`
- `supportRisk_eq_abstractRisk_subtype`
- `risk_graphPMF_eq_abstractRisk_subtype`
- `pi_graph_singleton_supportTrace`
- `pi_graph_measure_supportTraceFinset`
- `supportTrace_weight_toReal`
- `abstractFailureRate_le_failureProb_graph`

The proof idea is:

1. Map every bad support-indexed sample into the corresponding graph-labelled
   sample.
2. Show this image is a subset of the measure-theoretic failure event.
3. Compute the product-measure mass of every singleton sample:

   ```text
   (1 / |C|)^m
   ```

4. Sum those singleton masses over the bad finite image.
5. Convert the resulting `ENNReal` mass to a real number with
   `supportTrace_weight_toReal`.
6. Use measure monotonicity to conclude:

   ```text
   abstractFailureRate <= failureProb
   ```

This is the main reason the proof has a separate bridge section: the finite
counting argument is cleanly isolated from the measure-theoretic bookkeeping.

### Final Assembly

The final theorem is:

```lean
batch_stochastic_NFL
```

The positive case does the following in Lean:

1. choose `C` with `exists_support_card`;
2. set `Z := {x : X // x in C}`;
3. use `exists_abstractFailureRate_ge` to obtain a target `fZ : Z -> Bool`;
4. extend it to `fX : X -> Bool`;
5. define `D := (graphPMF C fX hCnonempty).toMeasure`;
6. prove realizability with `risk_graphPMF_self_zero`;
7. prove the failure lower bound using:

   ```lean
   le_trans hfailZ
     (abstractFailureRate_le_failureProb_graph ...)
   ```

Thus the final proof has two independent parts glued together at the end:

- a finite combinatorial lower bound that produces a bad target;
- a measure bridge showing that the same bad target witnesses the original
  stochastic theorem.

## Summary of the Proof Architecture

The two proofs use the same broad engineering pattern.

1. First define an auxiliary object where the combinatorics are visible.

   - Wolpert-Macready: `avgFuture`.
   - Batch stochastic: `abstractRisk` and `abstractFailureRate`.

2. Prove the core finite counting theorem away from the final API.

   - Wolpert-Macready: `avgFuture_eq_pow`.
   - Batch stochastic: `exists_abstractFailureRate_ge`.

3. Add bridge lemmas back to the original theorem statement.

   - Wolpert-Macready: `observations_eq_observationsFrom_nil`.
   - Batch stochastic: `abstractFailureRate_le_failureProb_graph`.

4. Keep edge cases explicit.

   - Wolpert-Macready: empty history/base observation lists.
   - Batch stochastic: empty domain diagnostic and zero-sample Dirac proof.

This structure makes the Lean proofs less brittle: each difficult idea is
proved once in a small local model, then transported to the theorem statement.
