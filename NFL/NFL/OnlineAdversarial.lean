import NFL.Basic
import Mathlib.Data.List.Basic

namespace NFL.OnlineAdversarial

/-- A deterministic online learner: given the history of (query, true label) pairs
and a new query, output a prediction in `Bool`. -/
abbrev OnlineLearner (X : Type*) := List (X × Bool) → X → Bool

variable {X : Type*}

/-- The history that learner `A` sees just before round `t`, when run against
target `f` on query sequence `xs`. -/
def historyTo (f : X → Bool) (xs : List X) (t : ℕ) : List (X × Bool) :=
  (xs.take t).map (fun x => (x, f x))

/-- `A` mispredicts at round `t` against target `f` on query sequence `xs`. -/
def MistakeAt (A : OnlineLearner X) (f : X → Bool) (xs : List X) (t : ℕ) : Prop :=
  ∀ h : t < xs.length, A (historyTo f xs t) (xs.get ⟨t, h⟩) ≠ f (xs.get ⟨t, h⟩)

/-- **Theorem 1 — Adversarial online NFL (deterministic).**
For any deterministic online learner `A` and any sequence `xs` of *distinct*
queries, there exists a target function `f : X → Bool` against which `A` errs
on every round. -/
theorem exists_adversarial_target
    (A : OnlineLearner X) (xs : List X) (_hxs : xs.Nodup) :
    ∃ f : X → Bool, ∀ t, MistakeAt A f xs t := by
  sorry

end NFL.OnlineAdversarial
