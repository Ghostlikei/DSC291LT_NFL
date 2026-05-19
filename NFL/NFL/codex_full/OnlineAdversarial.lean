import NFL.Basic
import Mathlib.Data.List.Basic

namespace NFL.CodexFull.OnlineAdversarial

/-- A deterministic online learner: given the history of `(query, true label)`
pairs and a new query, output a prediction in `Bool`. -/
abbrev OnlineLearner (X : Type*) := List (X × Bool) → X → Bool

variable {X : Type*}

/-- The history that learner `A` sees just before round `t`, when run against
target `f` on query sequence `xs`. -/
def historyTo (f : X → Bool) (xs : List X) (t : Nat) : List (X × Bool) :=
  (xs.take t).map fun x => (x, f x)

/-- `A` mispredicts at round `t` against target `f` on query sequence `xs`. -/
def MistakeAt (A : OnlineLearner X) (f : X → Bool) (xs : List X) (t : Nat) : Prop :=
  ∀ h : t < xs.length, A (historyTo f xs t) (xs.get ⟨t, h⟩) ≠ f (xs.get ⟨t, h⟩)

/-- **Adversarial online NFL.** For any deterministic online learner and any
nodup query sequence, some target makes the learner err on every queried round. -/
theorem exists_adversarial_target
    (A : OnlineLearner X) (xs : List X) (hxs : xs.Nodup) :
    ∃ f : X → Bool, ∀ t, MistakeAt A f xs t := by
  classical
  induction xs generalizing A with
  | nil =>
      refine ⟨fun _ => false, ?_⟩
      intro t
      unfold MistakeAt
      intro h
      cases h
  | cons x xs ih =>
      have hx_not_mem : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxs_tail : xs.Nodup := (List.nodup_cons.mp hxs).2
      let b : Bool := !A [] x
      let A' : OnlineLearner X := fun h y => A ((x, b) :: h) y
      obtain ⟨g, hg⟩ := ih A' hxs_tail
      let f : X → Bool := fun y => if y = x then b else g y
      refine ⟨f, ?_⟩
      intro t
      unfold MistakeAt
      intro ht
      cases t with
      | zero =>
          have hget : (x :: xs).get ⟨0, ht⟩ = x := by
            simp
          rw [hget]
          dsimp [historyTo, f, b]
          cases A [] x <;> simp
      | succ t =>
          have ht' : t < xs.length := by
            exact Nat.lt_of_succ_lt_succ (by simpa using ht)
          have hget_ne : xs.get ⟨t, ht'⟩ ≠ x := by
            intro hget
            apply hx_not_mem
            rw [← hget]
            exact List.get_mem xs ⟨t, ht'⟩
          have hmap :
              (xs.take t).map (fun y => (y, f y)) =
                (xs.take t).map (fun y => (y, g y)) := by
            apply List.map_congr_left
            intro y hy
            have hyxs : y ∈ xs := List.mem_of_mem_take hy
            have hyne : y ≠ x := by
              intro hyx
              apply hx_not_mem
              simpa [hyx] using hyxs
            simp [f, hyne]
          have hhist :
              historyTo f (x :: xs) (Nat.succ t) =
                (x, b) :: historyTo g xs t := by
            unfold historyTo
            simp [List.take_succ_cons, f, b, hmap]
          have htail := hg t ht'
          have hget_ne' : xs[t] ≠ x := by
            simpa [List.get_eq_getElem] using hget_ne
          rw [hhist, List.get_cons_succ]
          simpa [A', f, hget_ne'] using htail

end NFL.CodexFull.OnlineAdversarial
