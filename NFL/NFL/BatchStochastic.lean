import NFL.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fintype.Basic

namespace NFL.BatchStochastic

open MeasureTheory

/-- A deterministic learning algorithm: from a finite training sample, produce
a hypothesis `X → Bool`. -/
abbrev Learner (X : Type*) := List (X × Bool) → (X → Bool)

variable {X : Type*}

/-- 0-1 loss of hypothesis `h` on a labelled example. -/
def zeroOneLoss (h : X → Bool) (xy : X × Bool) : ℝ :=
  if h xy.1 = xy.2 then 0 else 1

variable [MeasurableSpace X]

/-- Risk of a hypothesis `h` under a distribution `D` over `X × Bool`. -/
noncomputable def risk (D : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  ∫ xy, zeroOneLoss h xy ∂D

/-- Probability that the hypothesis returned by `A` on an i.i.d. sample of size `m`
from `D` has risk at least `ε`. -/
noncomputable def failureProb
    (D : Measure (X × Bool)) (A : Learner X) (m : ℕ) (ε : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin m => D))
    {S : Fin m → (X × Bool) | ε ≤ risk D (A (List.ofFn S))}).toReal

/-- **Theorem 3 — Batch stochastic NFL (Shalev-Shwartz & Ben-David, Thm 5.1).**
For any deterministic learning algorithm `A` and any sample size `m` with
`2m ≤ |X|`, there exists a distribution `D` over `X × Bool` such that
  (1) some target function attains zero risk under `D`, and
  (2) with probability at least `1/7` over `S ∼ D^m`, the hypothesis `A(S)`
      has risk at least `1/8`. -/
theorem batch_stochastic_NFL
    [Fintype X] [MeasurableSingletonClass X]
    (A : Learner X) (m : ℕ) (_hm : 2 * m ≤ Fintype.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, risk D f = 0) ∧
      (1 : ℝ) / 7 ≤ failureProb D A m (1 / 8) := by
  sorry

end NFL.BatchStochastic
