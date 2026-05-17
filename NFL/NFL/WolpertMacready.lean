import NFL.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace NFL.WolpertMacready

open scoped ENNReal

variable {X Y : Type*}

/-- A possibly-stochastic search algorithm: given the trace of previous
(query, observed cost) pairs, sample the next query from a distribution on `X`.
Non-revisiting is enforced as a separate predicate, not in the type. -/
structure SearchAlg (X Y : Type*) where
  nextQuery : List (X × Y) → PMF X

/-- The algorithm never (with positive probability) queries a point already in
the history. -/
def SearchAlg.NonRevisiting (A : SearchAlg X Y) : Prop :=
  ∀ (h : List (X × Y)) (x : X), x ∈ h.map Prod.fst → A.nextQuery h x = 0

/-- The PMF over `m`-step traces when `A` is run against cost function `f`. -/
noncomputable def trace (A : SearchAlg X Y) (f : X → Y) : ℕ → PMF (List (X × Y))
  | 0 => PMF.pure []
  | n + 1 =>
      (trace A f n).bind fun h =>
        (A.nextQuery h).bind fun x =>
          PMF.pure (h.concat (x, f x))

/-- The PMF over observed cost sequences for an `m`-step run of `A` on `f`. -/
noncomputable def observations (A : SearchAlg X Y) (f : X → Y) (m : ℕ) : PMF (List Y) :=
  (trace A f m).map (·.map Prod.snd)

/-- **Theorem 2 — Wolpert–Macready (β, histogram form, original 1997).**
For any two non-revisiting (possibly stochastic) search algorithms `A₁`, `A₂`,
any finite domain `X`, finite codomain `Y`, budget `m ≤ |X|`, and any observed
cost sequence `c` of length `m`, the sum over cost functions `f ∈ Y^X` of the
probability of producing exactly `c` is the same for `A₁` and `A₂`. -/
theorem wolpert_macready
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A₁ A₂ : SearchAlg X Y) (m : ℕ) (_hm : m ≤ Fintype.card X)
    (_h₁ : A₁.NonRevisiting) (_h₂ : A₂.NonRevisiting)
    (c : List Y) (_hc : c.length = m) :
    (∑ f : X → Y, observations A₁ f m c) = ∑ f : X → Y, observations A₂ f m c := by
  sorry

/-- Expected value of a cost-only performance measure `φ` when running `A`
against target `f`. -/
noncomputable def expectedPerformance
    (A : SearchAlg X Y) (f : X → Y) (m : ℕ) (φ : List Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' c, observations A f m c * φ c

/-- **Corollary — averaged performance (γ).**
Averaged uniformly over cost functions `f ∈ Y^X`, no cost-only performance
measure can distinguish two non-revisiting algorithms. Follows from
`wolpert_macready` by summing against `φ`. -/
theorem wolpert_macready_avg
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A₁ A₂ : SearchAlg X Y) (m : ℕ) (_hm : m ≤ Fintype.card X)
    (_h₁ : A₁.NonRevisiting) (_h₂ : A₂.NonRevisiting)
    (φ : List Y → ℝ≥0∞) :
    (∑ f : X → Y, expectedPerformance A₁ f m φ)
      = ∑ f : X → Y, expectedPerformance A₂ f m φ := by
  sorry

end NFL.WolpertMacready
