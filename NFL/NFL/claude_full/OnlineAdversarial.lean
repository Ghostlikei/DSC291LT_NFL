import NFL.Basic
import Mathlib.Data.List.Basic

namespace NFL.ClaudeFull.OnlineAdversarial

/-!
# Online Adversarial No-Free-Lunch (Claude full proof)

**Theorem.** For any deterministic online learner and any nodup query
sequence, there exists a Boolean target function that causes the learner
to err on every round.

**Proof strategy.** Induction on the query sequence.

* *Base case* (empty sequence): trivial — no rounds exist.
* *Inductive step* (`x :: xs`):
  1. Compute the "bad label" `b = ¬ A [] x` to fool `A` at round 0.
  2. Define the shifted learner `A' h y = A ((x, b) :: h) y`.
  3. Apply the inductive hypothesis to `A'` and `xs` to obtain `g` that
     fools `A'` at every round of `xs`.
  4. Define `f y = if y = x then b else g y`.
  5. Show `f` fools `A` at round 0 (by definition of `b`) and at every
     later round (by relating `A`'s history to `A'`'s history and using
     the inductive hypothesis).
-/

/-- A deterministic online learner: given the history of (query, true label)
pairs and a new query, output a prediction in `Bool`. -/
abbrev OnlineLearner (X : Type*) := List (X × Bool) → X → Bool

variable {X : Type*}

/-- The history that learner `A` sees just before round `t`. -/
def historyTo (f : X → Bool) (xs : List X) (t : Nat) : List (X × Bool) :=
  (xs.take t).map fun x => (x, f x)

/-- `A` mispredicts at round `t` against target `f` on query sequence `xs`. -/
def MistakeAt (A : OnlineLearner X) (f : X → Bool) (xs : List X) (t : Nat) : Prop :=
  ∀ h : t < xs.length, A (historyTo f xs t) (xs.get ⟨t, h⟩) ≠ f (xs.get ⟨t, h⟩)

/-- **Adversarial Online NFL.**
For any deterministic online learner `A` and any nodup query sequence
`xs`, there exists a target `f : X → Bool` against which `A` errs on
every round. -/
theorem exists_adversarial_target
    (A : OnlineLearner X) (xs : List X) (hxs : xs.Nodup) :
    ∃ f : X → Bool, ∀ t, MistakeAt A f xs t := by
  classical
  induction xs generalizing A with
  | nil =>
      -- No rounds: any target works vacuously.
      exact ⟨fun _ => false, fun t => fun h => absurd h (by simp)⟩
  | cons x xs ih =>
      have hx_not_mem : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxs_tail : xs.Nodup := (List.nodup_cons.mp hxs).2
      -- Step 1: the adversarial label for the first query.
      let b : Bool := !A [] x
      -- Step 2: the shifted learner (prepend (x, b) to every history).
      let A' : OnlineLearner X := fun h y => A ((x, b) :: h) y
      -- Step 3: apply IH to A' on the tail.
      obtain ⟨g, hg⟩ := ih A' hxs_tail
      -- Step 4: combined target.
      let f : X → Bool := fun y => if y = x then b else g y
      refine ⟨f, fun t => ?_⟩
      unfold MistakeAt
      intro ht
      cases t with
      | zero =>
          -- Round 0: the query is x, history is empty.
          have hget : (x :: xs).get ⟨0, ht⟩ = x := List.get_cons_zero
          rw [hget]
          -- Unfold all local definitions; goal becomes A [] x ≠ !A [] x.
          dsimp [historyTo, f, b]
          cases A [] x <;> simp
      | succ t =>
          -- Round t+1: the query is xs[t].
          have ht' : t < xs.length := Nat.lt_of_succ_lt_succ (by simpa using ht)
          -- xs[t] ≠ x (since x ∉ xs).
          have hget_ne : xs.get ⟨t, ht'⟩ ≠ x :=
            fun heq => hx_not_mem (heq ▸ List.get_mem xs ⟨t, ht'⟩)
          -- The history A sees at round t+1 against f equals (x, b) :: historyTo g xs t.
          have hmap :
              (xs.take t).map (fun y => (y, f y)) =
                (xs.take t).map (fun y => (y, g y)) := by
            apply List.map_congr_left
            intro y hy
            have hyxs : y ∈ xs := List.mem_of_mem_take hy
            have hyne : y ≠ x := fun hyx => hx_not_mem (hyx ▸ hyxs)
            simp [f, hyne]
          have hhist :
              historyTo f (x :: xs) (Nat.succ t) =
                (x, b) :: historyTo g xs t := by
            unfold historyTo
            simp [List.take_succ_cons, f, b, hmap]
          -- The query at round t+1 is xs[t].
          have hget_succ : (x :: xs).get ⟨Nat.succ t, ht⟩ = xs.get ⟨t, ht'⟩ :=
            List.get_cons_succ
          rw [hhist, hget_succ]
          -- A's prediction equals A' applied to the g-history.
          change A ((x, b) :: historyTo g xs t) (xs.get ⟨t, ht'⟩) ≠ f (xs.get ⟨t, ht'⟩)
          -- f(xs[t]) = g(xs[t]) since xs[t] ≠ x.
          have hget_ne' : xs[t] ≠ x := by
            simpa [List.get_eq_getElem] using hget_ne
          -- A' mistakes at round t of xs against g.
          have htail := hg t ht'
          simpa [A', f, hget_ne'] using htail

end NFL.ClaudeFull.OnlineAdversarial
