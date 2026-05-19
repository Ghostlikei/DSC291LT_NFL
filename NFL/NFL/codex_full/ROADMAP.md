# Codex Full Proof Roadmap

This folder is for the full proof track, separate from `NFL/codex_test`.

## Wolpert-Macready first

Target:

```lean
theorem wolpert_macready
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A₁ A₂ : SearchAlg X Y) (m : Nat) (_hm : m ≤ Fintype.card X)
    (_h₁ : A₁.NonRevisiting) (_h₂ : A₂.NonRevisiting)
    (c : List Y) (_hc : c.length = m) :
    (∑ f : X → Y, observations A₁ f m c) =
      ∑ f : X → Y, observations A₂ f m c
```

Proof spine:

1. [done] Define `queryTraceFrom A h c`, the PMF on future query lists obtained by feeding
   the algorithm the already-observed value sequence `c`, independent of a target
   function.
2. [done] Prove support invariants for `queryTraceFrom`:
   length equals `c.length`, and under `NonRevisiting`, new queries avoid the prior
   history and are internally `Nodup`.
3. [done] Define `Consistent f h`, meaning target `f` agrees with a labelled trace `h`.
4. [done] Replace the query-list decomposition with a stronger continuation
   invariant `avgFuture_eq_pow`: from any nodup labelled history, the averaged
   probability of a future observation list is
   `Fintype.card Y ^ (Fintype.card X - (h.length + c.length))`, independent of
   the algorithm.
5. [done] Prove the finite-function count by a bijection between compatible
   targets and arbitrary labels on the unqueried complement.
6. [done] Bridge the continuation process back to the original append-recursive
   `trace`/`observations` definitions.
7. [done] Prove `wolpert_macready`.
8. [done] Prove `wolpert_macready_avg` by summing the histogram identity against
   an arbitrary `ℝ≥0∞` score functional.

The `m = 0` base case remains as a separately checked lemma, but the general
proof now covers it as well.

## Online adversarial

Status: [done]

`OnlineAdversarial.lean` proves the deterministic adversarial target theorem by
induction over a nodup query list. At the head query, choose the opposite of the
learner's prediction, then recurse on the tail with the head observation
prepended to the learner history.

## Batch stochastic

The statement must include `[Nonempty X]`; the empty-domain counterexample is
formalized in `codex_test`. For the full proof:

Status: [done]

Completed in `BatchStochastic.lean`:

1. [done] Formal diagnostic: no probability measure exists on `Empty × Bool`.
2. [done] Dirac construction for `m = 0`.
3. [done] For `m > 0`, choose a subset `C ⊆ X` of size `2m`; work abstractly
   over the support subtype `Z`.
4. [done] Prove the fixed-sample averaging lemma
   `sum_abstractRisk_fixed_sample_ge`: every sample leaves at least `m` support
   points unseen, and paired labels at an unseen point contribute one loss in
   total.
5. [done] Prove the finite probabilistic-method step
   `exists_abstractFailureRate_ge`: if every target failed with rate below
   `1/7`, the total risk sum would be strictly less than the `1/4` lower bound.
6. [done] Bridge the finite count to the measure statement by mapping bad
   support-indexed samples into graph-labelled samples, computing their
   `Measure.pi` mass from singleton products, and using monotonicity into the
   failure event.
7. [done] Assemble `batch_stochastic_NFL` from the zero case and positive case.
