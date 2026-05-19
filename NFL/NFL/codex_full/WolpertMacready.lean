import NFL.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Full-proof workspace for Wolpert--Macready

This file intentionally lives under `NFL.CodexFull.WolpertMacready` so it can
develop a proof plan without colliding with the project theorem names.

Roadmap:

1. Define the original stochastic search objects.
2. Define `queryTraceFrom`, a target-independent process driven by a value list.
3. Prove support invariants for that process.
4. Relate the original `trace`/`observations` PMFs to `queryTraceFrom`.
5. Count compatible target functions for any nodup query list.
6. Collapse the algorithm-dependent query PMF by `PMF.tsum_coe`.
-/

namespace NFL.CodexFull.WolpertMacready

open scoped ENNReal

variable {X Y : Type*}

/-- A possibly-stochastic search algorithm: given the trace of previous
(query, observed cost) pairs, sample the next query from a distribution on `X`.
Non-revisiting is enforced as a separate predicate, not in the type. -/
structure SearchAlg (X Y : Type*) where
  nextQuery : List (X × Y) → PMF X

/-- The algorithm never assigns positive probability to a point already queried
in the history. -/
def SearchAlg.NonRevisiting (A : SearchAlg X Y) : Prop :=
  ∀ (h : List (X × Y)) (x : X), x ∈ h.map Prod.fst → A.nextQuery h x = 0

/-- The PMF over `m`-step traces when `A` is run against cost function `f`. -/
noncomputable def trace (A : SearchAlg X Y) (f : X → Y) : Nat → PMF (List (X × Y))
  | 0 => PMF.pure []
  | n + 1 =>
      (trace A f n).bind fun h =>
        (A.nextQuery h).bind fun x =>
          PMF.pure (h.concat (x, f x))

/-- The PMF over observed cost sequences for an `m`-step run of `A` on `f`. -/
noncomputable def observations (A : SearchAlg X Y) (f : X → Y) (m : Nat) : PMF (List Y) :=
  (trace A f m).map (·.map Prod.snd)

/-- A continuation version of `trace`: starting from an already-labelled
history `h`, return just the future labelled suffix. This front-recursive form
matches induction over an observation list. -/
noncomputable def traceFrom (A : SearchAlg X Y) (f : X → Y) :
    List (X × Y) → Nat → PMF (List (X × Y))
  | _, 0 => PMF.pure []
  | h, n + 1 =>
      (A.nextQuery h).bind fun x =>
        (traceFrom A f (h.concat (x, f x)) n).map fun t => (x, f x) :: t

/-- The corresponding future-observation process from a labelled history. -/
noncomputable def observationsFrom
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y)) (m : Nat) :
    PMF (List Y) :=
  (traceFrom A f h m).map (·.map Prod.snd)

/-- Universe-polymorphic composition law for `PMF.map`. -/
theorem pmf_map_map {α β γ : Type*} (p : PMF α) (f : α → β) (g : β → γ) :
    PMF.map g (PMF.map f p) = PMF.map (fun a => g (f a)) p := by
  rw [← PMF.bind_pure_comp g (PMF.map f p)]
  rw [← PMF.bind_pure_comp f p]
  rw [PMF.bind_bind]
  apply congrArg
  funext a
  change (PMF.pure (f a)).bind (PMF.pure ∘ g) = PMF.pure (g (f a))
  rw [PMF.pure_bind]
  rfl

/-- The continuation observation process peels off the next query and conses
its observed value onto the future observations. -/
theorem observationsFrom_succ
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y)) (n : Nat) :
    observationsFrom A f h (n + 1) =
      (A.nextQuery h).bind fun x =>
        (observationsFrom A f (h.concat (x, f x)) n).map fun ys => f x :: ys := by
  unfold observationsFrom
  change PMF.map (fun t : List (X × Y) => t.map Prod.snd)
      ((A.nextQuery h).bind fun x =>
        PMF.map (fun t : List (X × Y) => (x, f x) :: t)
          (traceFrom A f (h.concat (x, f x)) n)) =
    (A.nextQuery h).bind fun x =>
      PMF.map (fun ys : List Y => f x :: ys)
        (PMF.map (fun t : List (X × Y) => t.map Prod.snd)
          (traceFrom A f (h.concat (x, f x)) n))
  rw [PMF.map_bind]
  apply congrArg
  funext x
  rw [pmf_map_map]
  rw [pmf_map_map]
  rfl

theorem pmf_map_cons_apply [DecidableEq Y]
    (p : PMF (List Y)) (a b : Y) (ys : List Y) :
    (PMF.map (fun zs : List Y => a :: zs) p) (b :: ys) =
      if a = b then p ys else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    rw [PMF.map_apply]
    rw [tsum_eq_single ys]
    · simp
    · intro zs hzs
      have hyzs : ys ≠ zs := fun h => hzs h.symm
      simp [hyzs]
  · rw [if_neg hab]
    rw [PMF.map_apply]
    rw [← tsum_zero]
    apply tsum_congr
    intro zs
    by_cases hb : b = a
    · exact False.elim (hab hb.symm)
    · simp [hb]

/-- Pointwise recursion for future observation probabilities. -/
theorem observationsFrom_cons_apply [DecidableEq Y]
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y))
    (y : Y) (ys : List Y) :
    observationsFrom A f h (ys.length + 1) (y :: ys) =
      ∑' x : X, A.nextQuery h x *
        (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0) := by
  rw [observationsFrom_succ]
  rw [PMF.bind_apply]
  apply tsum_congr
  intro x
  congr 1
  rw [pmf_map_cons_apply]
  by_cases hxy : f x = y
  · subst y
    simp
  · simp [hxy]

/-- The front-recursive continuation trace also satisfies the append-at-the-end
recursion used by the original `trace`. -/
theorem traceFrom_append_rec
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y)) (n : Nat) :
    traceFrom A f h (n + 1) =
      (traceFrom A f h n).bind fun t =>
        (A.nextQuery (h ++ t)).bind fun x => PMF.pure (t.concat (x, f x)) := by
  induction n generalizing h with
  | zero =>
      unfold traceFrom
      rw [PMF.pure_bind]
      simp only [List.append_nil]
      apply congrArg
      funext x
      simp [traceFrom, PMF.map, PMF.pure_bind]
  | succ n ih =>
      unfold traceFrom
      rw [PMF.bind_bind]
      apply congrArg
      funext x
      rw [ih (h.concat (x, f x))]
      rw [PMF.map_bind]
      rw [← PMF.bind_pure_comp
        (fun t : List (X × Y) => (x, f x) :: t)
        (traceFrom A f (h.concat (x, f x)) n)]
      rw [PMF.bind_bind]
      apply congrArg
      funext t
      change PMF.map (fun t : List (X × Y) => (x, f x) :: t)
          ((A.nextQuery (h.concat (x, f x) ++ t)).bind fun z =>
            PMF.pure (t.concat (z, f z))) =
        (PMF.pure ((x, f x) :: t)).bind fun ttotal =>
          (A.nextQuery (h ++ ttotal)).bind fun z =>
            PMF.pure (ttotal.concat (z, f z))
      rw [PMF.pure_bind]
      rw [PMF.map_bind]
      simp [PMF.map, PMF.pure_bind, List.concat_eq_append, List.append_assoc]

/-- The original append-recursive trace agrees with the continuation trace
started from the empty history. -/
theorem trace_eq_traceFrom_nil
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) :
    trace A f m = traceFrom A f [] m := by
  induction m with
  | zero =>
      simp [trace, traceFrom]
  | succ m ih =>
      simp only [trace]
      rw [ih]
      rw [traceFrom_append_rec A f [] m]
      simp

theorem observations_eq_observationsFrom_nil
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) :
    observations A f m = observationsFrom A f [] m := by
  unfold observations observationsFrom
  rw [trace_eq_traceFrom_nil]

/-- Target-independent query process: starting from a labelled history `h`, feed
the algorithm the future observed values `ys` and return the future query list.

This is the object that carries all algorithm dependence in the full proof. -/
noncomputable def queryTraceFrom (A : SearchAlg X Y) :
    List (X × Y) → List Y → PMF (List X)
  | _, [] => PMF.pure []
  | h, y :: ys =>
      (A.nextQuery h).bind fun x =>
        (queryTraceFrom A (h.concat (x, y)) ys).map fun xs => x :: xs

/-- The labelled trace induced by a query list and an observation list. -/
def labelledTrace (xs : List X) (ys : List Y) : List (X × Y) :=
  xs.zip ys

/-- A target function agrees with every labelled point in a trace. -/
def Consistent (f : X → Y) (h : List (X × Y)) : Prop :=
  ∀ xy ∈ h, f xy.1 = xy.2

/-- Average future observation mass over all target functions compatible with
the already-labelled history. -/
noncomputable def avgFuture [Fintype (X → Y)]
    (A : SearchAlg X Y) (h : List (X × Y)) (c : List Y) : ℝ≥0∞ :=
  by
    classical
    exact ∑ f : X → Y,
      if Consistent f h then observationsFrom A f h c.length c else 0

/-- If a query appears in a nodup labelled history, its label is unique. -/
theorem eq_of_mem_of_fst_eq_of_nodup_map
    {h : List (X × Y)} {a b : X × Y}
    (ha : a ∈ h) (hb : b ∈ h) (hh : (h.map Prod.fst).Nodup)
    (hab : a.1 = b.1) :
    a = b := by
  induction h with
  | nil =>
      cases ha
  | cons z zs ih =>
      rw [List.map_cons, List.nodup_cons] at hh
      rcases hh with ⟨hz_not_mem, hzs⟩
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · rfl
        · exfalso
          exact hz_not_mem (by
            rw [List.mem_map]
            exact ⟨b, hb, hab.symm⟩)
      · rcases hb with rfl | hb
        · exfalso
          exact hz_not_mem (by
            rw [List.mem_map]
            exact ⟨a, ha, hab⟩)
        · exact ih ha hb hzs

/-- The label attached to a queried point in a history. The proof argument is
what lets us avoid assuming `Y` is inhabited. -/
noncomputable def queriedLabel (h : List (X × Y)) (x : X)
    (hx : x ∈ h.map Prod.fst) : Y :=
  (Classical.choose (List.mem_map.mp hx)).2

theorem queriedLabel_eq_of_mem
    {h : List (X × Y)} (hh : (h.map Prod.fst).Nodup)
    {xy : X × Y} (hxy : xy ∈ h) :
    queriedLabel h xy.1 (List.mem_map_of_mem hxy) = xy.2 := by
  classical
  unfold queriedLabel
  let witness := Classical.choose (List.mem_map.mp (List.mem_map_of_mem (f := Prod.fst) hxy))
  have hwitness := Classical.choose_spec (List.mem_map.mp (List.mem_map_of_mem (f := Prod.fst) hxy))
  have hw_mem : witness ∈ h := hwitness.1
  have hw_fst : witness.1 = xy.1 := hwitness.2
  have h_eq : witness = xy :=
    eq_of_mem_of_fst_eq_of_nodup_map hw_mem hxy hh hw_fst
  simp [witness, h_eq]

/-- Extend a labelling of the unqueried complement to a full target function by
using the labels already present in the history on queried points. -/
noncomputable def extendFromComplement [DecidableEq X]
    (h : List (X × Y)) (g : {x : X // x ∉ h.map Prod.fst} → Y) : X → Y :=
  fun x =>
    if hx : x ∈ h.map Prod.fst then
      queriedLabel h x hx
    else
      g ⟨x, hx⟩

theorem extendFromComplement_consistent [DecidableEq X]
    {h : List (X × Y)} (hh : (h.map Prod.fst).Nodup)
    (g : {x : X // x ∉ h.map Prod.fst} → Y) :
    Consistent (extendFromComplement h g) h := by
  intro xy hxy
  unfold extendFromComplement
  have hx : xy.1 ∈ h.map Prod.fst := List.mem_map_of_mem hxy
  simp [hx, queriedLabel_eq_of_mem hh hxy]

/-- Compatible targets are equivalent to arbitrary labels on the unqueried
complement of a nodup history. -/
noncomputable def consistentEquivComplement [DecidableEq X]
    (h : List (X × Y)) (hh : (h.map Prod.fst).Nodup) :
    {f : X → Y // Consistent f h} ≃ ({x : X // x ∉ h.map Prod.fst} → Y) where
  toFun f := fun x => f.1 x.1
  invFun g := ⟨extendFromComplement h g, extendFromComplement_consistent hh g⟩
  left_inv f := by
    ext x
    unfold extendFromComplement
    by_cases hx : x ∈ h.map Prod.fst
    · rcases List.mem_map.mp hx with ⟨xy, hxy, hfst⟩
      have hlabel := queriedLabel_eq_of_mem hh hxy
      have hfxy := f.2 xy hxy
      change
        (if hx' : x ∈ h.map Prod.fst then
            queriedLabel h x hx'
          else
            (fun x : {x : X // x ∉ h.map Prod.fst} => f.1 x.1) ⟨x, hx'⟩) =
          f.1 x
      rw [dif_pos hx]
      calc
        queriedLabel h x hx = xy.2 := by
          subst hfst
          simpa using hlabel
        _ = f.1 xy.1 := hfxy.symm
        _ = f.1 x := by
          subst hfst
          rfl
    · simp [hx]
  right_inv g := by
    funext x
    unfold extendFromComplement
    simp [x.2]

/-- The number, as an `ℝ≥0∞`, of target functions compatible with a labelled
trace. This is the combinatorial factor that should become independent of the
algorithm. -/
noncomputable def consistentCount (X Y : Type*) [Fintype (X → Y)]
    (h : List (X × Y)) : ℝ≥0∞ :=
  by
    classical
    exact ∑ f : X → Y, if Consistent f h then 1 else 0

/-- The finite set of target functions compatible with a labelled trace. -/
noncomputable def consistentTargets (X Y : Type*) [Fintype (X → Y)]
    (h : List (X × Y)) : Finset (X → Y) :=
  by
    classical
    exact Finset.univ.filter fun f => Consistent f h

/-- Base case of the histogram identity. -/
theorem wolpert_macready_zero
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A₁ A₂ : SearchAlg X Y) :
    (∑ f : X → Y, observations A₁ f 0 []) =
      ∑ f : X → Y, observations A₂ f 0 [] := by
  simp [observations, trace]

/-- `labelledTrace` has the expected query projection when the lists have the
same length. -/
theorem map_fst_labelledTrace
    {xs : List X} {ys : List Y} (h : xs.length ≤ ys.length) :
    (labelledTrace xs ys).map Prod.fst = xs := by
  simpa [labelledTrace] using List.map_fst_zip (l₁ := xs) (l₂ := ys) h

/-- `labelledTrace` has the expected value projection when the lists have the
same length. -/
theorem map_snd_labelledTrace
    {xs : List X} {ys : List Y} (h : ys.length ≤ xs.length) :
    (labelledTrace xs ys).map Prod.snd = ys := by
  simpa [labelledTrace] using List.map_snd_zip (l₁ := xs) (l₂ := ys) h

/-- Compatibility with an appended labelled point splits into compatibility
with the prefix and agreement on the appended point. -/
theorem consistent_concat (f : X → Y) (h : List (X × Y)) (x : X) (y : Y) :
    Consistent f (h.concat (x, y)) ↔ Consistent f h ∧ f x = y := by
  constructor
  · intro hf
    constructor
    · intro xy hxy
      exact hf xy (by
        rw [List.concat_eq_append, List.mem_append]
        exact Or.inl hxy)
    · exact hf (x, y) (by
        rw [List.concat_eq_append, List.mem_append, List.mem_singleton]
        exact Or.inr rfl)
  · rintro ⟨hh, hxy⟩ xy hmem
    rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact hh xy hmem
    · exact hxy

/-- Averaging after the next observed value splits over the algorithm's next
query distribution. -/
theorem avgFuture_cons
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A : SearchAlg X Y) (h : List (X × Y)) (y : Y) (ys : List Y) :
    avgFuture A h (y :: ys) =
      ∑' x : X, A.nextQuery h x * avgFuture A (h.concat (x, y)) ys := by
  classical
  unfold avgFuture
  simp only [List.length_cons]
  simp_rw [observationsFrom_cons_apply]
  rw [tsum_fintype]
  calc
    (∑ f : X → Y,
        if Consistent f h then
          ∑' x : X,
            A.nextQuery h x *
              (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0)
        else 0) =
      ∑ f : X → Y, ∑ x : X,
        if Consistent f h then
          A.nextQuery h x *
            (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0)
        else 0 := by
        apply Finset.sum_congr rfl
        intro f _hf
        by_cases hC : Consistent f h
        · simp [hC, tsum_fintype]
        · simp [hC]
    _ = ∑ x : X, ∑ f : X → Y,
        if Consistent f h then
          A.nextQuery h x *
            (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0)
        else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ x : X,
        A.nextQuery h x *
          ∑ f : X → Y,
            if Consistent f (h.concat (x, y)) then
              observationsFrom A f (h.concat (x, y)) ys.length ys
            else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _hf
        rw [consistent_concat]
        by_cases hC : Consistent f h <;>
          by_cases hxy : f x = y <;>
          simp [hC, hxy]

/-- Every target function is compatible with the empty trace. -/
theorem consistent_nil (f : X → Y) : Consistent f [] := by
  intro xy hxy
  cases hxy

/-- The compatible-target count for the empty trace is the total number of
target functions. -/
theorem consistentCount_nil
    [Fintype X] [Fintype Y] [DecidableEq X] :
    consistentCount X Y [] = (Fintype.card (X → Y) : ℝ≥0∞) := by
  classical
  unfold consistentCount
  simp [consistent_nil]

/-- Membership in `consistentTargets` is exactly consistency. -/
theorem mem_consistentTargets
    [Fintype (X → Y)] (h : List (X × Y)) (f : X → Y) :
    f ∈ consistentTargets X Y h ↔ Consistent f h := by
  classical
  unfold consistentTargets
  simp

/-- `consistentCount` is the cardinality of `consistentTargets`, coerced to
`ℝ≥0∞`. -/
theorem consistentCount_eq_card
    [Fintype (X → Y)] (h : List (X × Y)) :
    consistentCount X Y h = ((consistentTargets X Y h).card : ℝ≥0∞) := by
  classical
  unfold consistentCount consistentTargets
  simp

/-- A nodup labelled history fixes exactly its queried coordinates, so the
number of compatible target functions is `|Y| ^ (|X| - history length)`. -/
theorem consistentCount_eq_pow_card
    [Fintype X] [Fintype Y] [DecidableEq X]
    {h : List (X × Y)} (hh : (h.map Prod.fst).Nodup) :
    consistentCount X Y h =
      (Fintype.card Y ^ (Fintype.card X - h.length) : ℝ≥0∞) := by
  classical
  rw [consistentCount_eq_card]
  letI : Fintype {f : X → Y // Consistent f h} := Fintype.ofFinite _
  letI : Fintype {x : X // x ∉ h.map Prod.fst} := Fintype.ofFinite _
  have htargets :
      (consistentTargets X Y h).card =
        Fintype.card {f : X → Y // Consistent f h} := by
    rw [Fintype.card_subtype (p := fun f : X → Y => Consistent f h)]
    simp [consistentTargets]
  rw [htargets]
  have hcomp_card :
      Fintype.card {x : X // x ∉ h.map Prod.fst} =
        Fintype.card X - h.length := by
    have hsub := Fintype.card_subtype
      (p := fun x : X => x ∉ h.map Prod.fst)
    rw [hsub]
    have hs :
        ({x | x ∉ h.map Prod.fst} : Finset X) =
          ((h.map Prod.fst).toFinset)ᶜ := by
      ext x
      simp [List.mem_toFinset]
    have hcard :
        ({x | x ∉ h.map Prod.fst} : Finset X).card =
          ((h.map Prod.fst).toFinset)ᶜ.card := by
      rw [hs]
    rw [hcard, Finset.card_compl, List.toFinset_card_of_nodup hh]
    simp
  have hnat :
      Fintype.card {f : X → Y // Consistent f h} =
        Fintype.card Y ^ (Fintype.card X - h.length) := by
    rw [Fintype.card_congr (consistentEquivComplement h hh)]
    rw [Fintype.card_fun]
    rw [hcomp_card]
  rw [hnat]
  norm_num

/-- Strong averaged NFL invariant from an arbitrary nodup history. The value
depends only on how many fresh observations remain, not on the algorithm. -/
theorem avgFuture_eq_pow
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A : SearchAlg X Y) (hA : A.NonRevisiting)
    (h : List (X × Y)) (hh : (h.map Prod.fst).Nodup)
    (c : List Y) (hbound : h.length + c.length ≤ Fintype.card X) :
    avgFuture A h c =
      (Fintype.card Y ^ (Fintype.card X - (h.length + c.length)) : ℝ≥0∞) := by
  classical
  induction c generalizing h with
  | nil =>
      simp only [List.length_nil, Nat.add_zero]
      rw [← consistentCount_eq_pow_card (X := X) (Y := Y) hh]
      unfold avgFuture consistentCount
      simp [observationsFrom, traceFrom]
  | cons y ys ih =>
      rw [avgFuture_cons]
      let K : ℝ≥0∞ :=
        (Fintype.card Y ^ (Fintype.card X - (h.length + (y :: ys).length)) : ℝ≥0∞)
      have hterm : ∀ x : X,
          A.nextQuery h x * avgFuture A (h.concat (x, y)) ys =
            A.nextQuery h x * K := by
        intro x
        by_cases hx : x ∈ h.map Prod.fst
        · rw [hA h x hx]
          simp [K]
        · have hh' : (((h.concat (x, y)).map Prod.fst).Nodup) := by
            rw [List.map_concat]
            exact hh.concat hx
          have hb' : (h.concat (x, y)).length + ys.length ≤ Fintype.card X := by
            simpa [List.length_cons, Nat.add_left_comm, Nat.add_comm] using hbound
          have hih := ih (h.concat (x, y)) hh' hb'
          rw [hih]
          congr 1
          unfold K
          congr 1
          congr 1
          simp [List.length_cons, Nat.add_left_comm, Nat.add_comm]
      calc
        (∑' x : X, A.nextQuery h x * avgFuture A (h.concat (x, y)) ys) =
            ∑' x : X, A.nextQuery h x * K := by
              apply tsum_congr
              exact hterm
        _ = (∑' x : X, A.nextQuery h x) * K := by
              rw [ENNReal.tsum_mul_right]
        _ = K := by
              rw [PMF.tsum_coe]
              simp [K]
        _ = (Fintype.card Y ^ (Fintype.card X - (h.length + (y :: ys).length)) : ℝ≥0∞) := rfl

/-- **Wolpert--Macready no-free-lunch histogram identity.**

For non-revisiting search algorithms, averaging over all target functions gives
the same probability for every fixed observation sequence. -/
theorem wolpert_macready
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A₁ A₂ : SearchAlg X Y) (m : Nat) (hm : m ≤ Fintype.card X)
    (h₁ : A₁.NonRevisiting) (h₂ : A₂.NonRevisiting)
    (c : List Y) (hc : c.length = m) :
    (∑ f : X → Y, observations A₁ f m c) =
      ∑ f : X → Y, observations A₂ f m c := by
  classical
  have hbound : ([] : List (X × Y)).length + c.length ≤ Fintype.card X := by
    simpa [hc] using hm
  have hnodup : (([] : List (X × Y)).map Prod.fst).Nodup := by
    simp
  have havg₁ :=
    avgFuture_eq_pow (X := X) (Y := Y) A₁ h₁ ([] : List (X × Y)) hnodup c hbound
  have havg₂ :=
    avgFuture_eq_pow (X := X) (Y := Y) A₂ h₂ ([] : List (X × Y)) hnodup c hbound
  have hsum₁ :
      (∑ f : X → Y, observations A₁ f m c) =
        avgFuture A₁ ([] : List (X × Y)) c := by
    unfold avgFuture
    apply Finset.sum_congr rfl
    intro f _hf
    rw [observations_eq_observationsFrom_nil A₁ f m, ← hc]
    simp [consistent_nil]
  have hsum₂ :
      (∑ f : X → Y, observations A₂ f m c) =
        avgFuture A₂ ([] : List (X × Y)) c := by
    unfold avgFuture
    apply Finset.sum_congr rfl
    intro f _hf
    rw [observations_eq_observationsFrom_nil A₂ f m, ← hc]
    simp [consistent_nil]
  rw [hsum₁, hsum₂, havg₁, havg₂]

/-- Relabel the query component of a labelled trace by a permutation of `X`. -/
def relabelTrace (π : X ≃ X) (h : List (X × Y)) : List (X × Y) :=
  h.map fun xy => (π xy.1, xy.2)

/-- Consistency with a relabelled trace is equivalent to consistency after
precomposing the target with the relabelling. -/
theorem consistent_relabel (π : X ≃ X) (f : X → Y) (h : List (X × Y)) :
    Consistent f (relabelTrace π h) ↔ Consistent (fun x => f (π x)) h := by
  unfold Consistent relabelTrace
  constructor
  · intro hf xy hxy
    exact hf (π xy.1, xy.2) (List.mem_map_of_mem hxy)
  · intro hf xy hxy
    rcases List.mem_map.mp hxy with ⟨xy0, hxy0, rfl⟩
    exact hf xy0 hxy0

/-- Compatible-target counts are invariant under permutation of the domain. -/
theorem consistentCount_relabel
    [Fintype (X → Y)] (π : X ≃ X) (h : List (X × Y)) :
    consistentCount X Y (relabelTrace π h) = consistentCount X Y h := by
  classical
  rw [consistentCount_eq_card, consistentCount_eq_card]
  have hb :
      Function.Bijective (fun f : X → Y => fun x => f (π x)) := by
    constructor
    · intro f g hfg
      funext x
      have hx := congr_fun hfg (π.symm x)
      simpa using hx
    · intro g
      refine ⟨fun x => g (π.symm x), ?_⟩
      funext x
      simp
  exact_mod_cast
    (Finset.card_bijective
      (s := consistentTargets X Y (relabelTrace π h))
      (t := consistentTargets X Y h)
      (fun f : X → Y => fun x => f (π x))
      hb
      (fun f => by
        rw [mem_consistentTargets, mem_consistentTargets, consistent_relabel]))

/-- Every query list in `queryTraceFrom A h ys` has length `ys.length`. -/
theorem queryTraceFrom_support_length
    (A : SearchAlg X Y) (h : List (X × Y)) (ys : List Y) (xs : List X) :
    xs ∈ (queryTraceFrom A h ys).support → xs.length = ys.length := by
  induction ys generalizing h xs with
  | nil =>
      intro hxs
      have hx : xs = [] := by
        simpa [queryTraceFrom, PMF.mem_support_pure_iff] using hxs
      simp [hx]
  | cons y ys ih =>
      intro hxs
      rcases (PMF.mem_support_bind_iff
        (p := A.nextQuery h)
        (f := fun x => (queryTraceFrom A (h.concat (x, y)) ys).map fun xs => x :: xs)
        xs).mp (by simpa [queryTraceFrom] using hxs) with ⟨x, _hx, hmap⟩
      rcases (PMF.mem_support_map_iff
        (p := queryTraceFrom A (h.concat (x, y)) ys)
        (f := fun xs => x :: xs)
        xs).mp hmap with ⟨tail, htail, rfl⟩
      simp [ih (h.concat (x, y)) tail htail]

/-- If the starting history has nodup query projection, every supported future
query list remains internally nodup and avoids all previously queried points.

This is the next support invariant needed for the full Wolpert proof. -/
theorem queryTraceFrom_support_nodup_disjoint
    (A : SearchAlg X Y) (h : List (X × Y)) (ys : List Y) (xs : List X)
    (_hA : A.NonRevisiting) (_hh : (h.map Prod.fst).Nodup) :
    xs ∈ (queryTraceFrom A h ys).support →
      xs.Nodup ∧ ∀ x ∈ xs, x ∉ h.map Prod.fst := by
  induction ys generalizing h xs with
  | nil =>
      intro hxs
      have hx : xs = [] := by
        simpa [queryTraceFrom, PMF.mem_support_pure_iff] using hxs
      subst xs
      simp
  | cons y ys ih =>
      intro hxs
      rcases (PMF.mem_support_bind_iff
        (p := A.nextQuery h)
        (f := fun x => (queryTraceFrom A (h.concat (x, y)) ys).map fun xs => x :: xs)
        xs).mp (by simpa [queryTraceFrom] using hxs) with ⟨x, hx_support, hmap⟩
      have hx_not_mem : x ∉ h.map Prod.fst := by
        intro hxmem
        have hz : A.nextQuery h x = 0 := _hA h x hxmem
        exact hx_support hz
      rcases (PMF.mem_support_map_iff
        (p := queryTraceFrom A (h.concat (x, y)) ys)
        (f := fun xs => x :: xs)
        xs).mp hmap with ⟨tail, htail, rfl⟩
      have hh' : ((h.concat (x, y)).map Prod.fst).Nodup := by
        rw [List.map_concat]
        exact _hh.concat hx_not_mem
      rcases ih (h.concat (x, y)) tail hh' htail with ⟨htail_nodup, htail_avoid⟩
      constructor
      · refine htail_nodup.cons ?_
        intro hx_tail
        have : x ∉ (h.concat (x, y)).map Prod.fst := htail_avoid x hx_tail
        rw [List.map_concat] at this
        exact this (by simp)
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz_tail
        · exact hx_not_mem
        · intro zmem
          exact htail_avoid z hz_tail (by
            rw [List.map_concat]
            simp [zmem])

/-- Histories in the support of `trace A f m` have length exactly `m`. -/
theorem trace_support_length
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (h : List (X × Y)) :
    h ∈ (trace A f m).support → h.length = m := by
  induction m generalizing h with
  | zero =>
      intro hh
      have : h = [] := by
        simpa [trace, PMF.mem_support_pure_iff] using hh
      simp [this]
  | succ m ih =>
      intro hh
      rcases (PMF.mem_support_bind_iff
        (p := trace A f m)
        (f := fun h => (A.nextQuery h).bind fun x => PMF.pure (h.concat (x, f x)))
        h).mp (by simpa [trace] using hh) with ⟨h₀, hh₀, hbind⟩
      rcases (PMF.mem_support_bind_iff
        (p := A.nextQuery h₀)
        (f := fun x => PMF.pure (h₀.concat (x, f x)))
        h).mp hbind with ⟨x, _hx, hpure⟩
      have h_eq : h = h₀.concat (x, f x) := by
        simpa [PMF.mem_support_pure_iff] using hpure
      subst h
      simp [ih h₀ hh₀]

/-- Histories in the support of `trace A f m` are labelled by `f`. -/
theorem trace_support_consistent
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (h : List (X × Y)) :
    h ∈ (trace A f m).support → Consistent f h := by
  induction m generalizing h with
  | zero =>
      intro hh xy hxy
      have : h = [] := by
        simpa [trace, PMF.mem_support_pure_iff] using hh
      simp [this] at hxy
  | succ m ih =>
      intro hh
      rcases (PMF.mem_support_bind_iff
        (p := trace A f m)
        (f := fun h => (A.nextQuery h).bind fun x => PMF.pure (h.concat (x, f x)))
        h).mp (by simpa [trace] using hh) with ⟨h₀, hh₀, hbind⟩
      rcases (PMF.mem_support_bind_iff
        (p := A.nextQuery h₀)
        (f := fun x => PMF.pure (h₀.concat (x, f x)))
        h).mp hbind with ⟨x, _hx, hpure⟩
      have h_eq : h = h₀.concat (x, f x) := by
        simpa [PMF.mem_support_pure_iff] using hpure
      subst h
      intro xy hxy
      rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at hxy
      rcases hxy with hxy | rfl
      · exact ih h₀ hh₀ xy hxy
      · rfl

/-- Under the non-revisiting condition, supported traces never repeat a query. -/
theorem trace_support_nodup
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (h : List (X × Y))
    (hA : A.NonRevisiting) :
    h ∈ (trace A f m).support → (h.map Prod.fst).Nodup := by
  induction m generalizing h with
  | zero =>
      intro hh
      have : h = [] := by
        simpa [trace, PMF.mem_support_pure_iff] using hh
      simp [this]
  | succ m ih =>
      intro hh
      rcases (PMF.mem_support_bind_iff
        (p := trace A f m)
        (f := fun h => (A.nextQuery h).bind fun x => PMF.pure (h.concat (x, f x)))
        h).mp (by simpa [trace] using hh) with ⟨h₀, hh₀, hbind⟩
      rcases (PMF.mem_support_bind_iff
        (p := A.nextQuery h₀)
        (f := fun x => PMF.pure (h₀.concat (x, f x)))
        h).mp hbind with ⟨x, hx, hpure⟩
      have h_eq : h = h₀.concat (x, f x) := by
        simpa [PMF.mem_support_pure_iff] using hpure
      have hx_not_mem : x ∉ h₀.map Prod.fst := by
        intro hxmem
        exact hx (hA h₀ x hxmem)
      subst h
      rw [List.map_concat]
      exact (ih h₀ hh₀).concat hx_not_mem

/-- The trace-level expansion of the mapped PMF defining `observations`. -/
noncomputable def traceObservationMass
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (c : List Y) : ℝ≥0∞ :=
  by
    classical
    exact ∑' h : List (X × Y), if c = h.map Prod.snd then trace A f m h else 0

/-- Expanding the mapped PMF defining `observations`. -/
theorem observations_apply
  (A : SearchAlg X Y) (f : X → Y) (m : Nat) (c : List Y) :
    observations A f m c = traceObservationMass A f m c := by
  unfold observations traceObservationMass
  rw [PMF.map_apply]
  apply tsum_congr
  intro h
  by_cases hc : c = h.map Prod.snd <;> simp [hc]

/-- Observed value lists in the support of `observations A f m` have length
exactly `m`. -/
theorem observations_support_length
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (c : List Y) :
    c ∈ (observations A f m).support → c.length = m := by
  intro hc
  rcases (PMF.mem_support_map_iff
      (p := trace A f m)
      (f := fun h : List (X × Y) => h.map Prod.snd)
      c).mp (by simpa [observations] using hc) with ⟨h, hh, hmap⟩
  rw [← hmap, List.length_map]
  exact trace_support_length A f m h hh

/-- A value list of the wrong length has zero observation probability. -/
theorem observations_apply_eq_zero_of_length_ne
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (c : List Y)
    (hc : c.length ≠ m) :
    observations A f m c = 0 := by
  rw [(observations A f m).apply_eq_zero_iff]
  intro hsupport
  exact hc (observations_support_length A f m c hsupport)

/-- Expected performance for an arbitrary score functional on observation
sequences. -/
noncomputable def expectedPerformance
    (A : SearchAlg X Y) (f : X → Y) (m : Nat)
    (φ : List Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' c, observations A f m c * φ c

/-- Expected-performance form of Wolpert--Macready, obtained by summing the
histogram identity against any nonnegative score functional. -/
theorem wolpert_macready_avg
    [Fintype X] [Fintype Y] [DecidableEq X]
    (A₁ A₂ : SearchAlg X Y) (m : Nat) (hm : m ≤ Fintype.card X)
    (h₁ : A₁.NonRevisiting) (h₂ : A₂.NonRevisiting)
    (φ : List Y → ℝ≥0∞) :
    (∑ f : X → Y, expectedPerformance A₁ f m φ) =
      ∑ f : X → Y, expectedPerformance A₂ f m φ := by
  classical
  have hpoint : ∀ c : List Y,
      (∑ f : X → Y, observations A₁ f m c) =
        ∑ f : X → Y, observations A₂ f m c := by
    intro c
    by_cases hc : c.length = m
    · exact wolpert_macready (X := X) (Y := Y) A₁ A₂ m hm h₁ h₂ c hc
    · have hz₁ : ∀ f : X → Y, observations A₁ f m c = 0 := by
        intro f
        exact observations_apply_eq_zero_of_length_ne A₁ f m c hc
      have hz₂ : ∀ f : X → Y, observations A₂ f m c = 0 := by
        intro f
        exact observations_apply_eq_zero_of_length_ne A₂ f m c hc
      simp [hz₁, hz₂]
  calc
    (∑ f : X → Y, expectedPerformance A₁ f m φ) =
        ∑' f : X → Y, expectedPerformance A₁ f m φ := by
          rw [tsum_fintype]
    _ = ∑' f : X → Y, ∑' c : List Y, observations A₁ f m c * φ c := rfl
    _ = ∑' c : List Y, ∑' f : X → Y, observations A₁ f m c * φ c := by
          rw [ENNReal.tsum_comm]
    _ = ∑' c : List Y, (∑ f : X → Y, observations A₁ f m c) * φ c := by
          apply tsum_congr
          intro c
          rw [ENNReal.tsum_mul_right]
          rw [tsum_fintype]
    _ = ∑' c : List Y, (∑ f : X → Y, observations A₂ f m c) * φ c := by
          apply tsum_congr
          intro c
          rw [hpoint c]
    _ = ∑' c : List Y, ∑' f : X → Y, observations A₂ f m c * φ c := by
          apply tsum_congr
          intro c
          rw [ENNReal.tsum_mul_right]
          rw [tsum_fintype]
    _ = ∑' f : X → Y, ∑' c : List Y, observations A₂ f m c * φ c := by
          rw [ENNReal.tsum_comm]
    _ = ∑' f : X → Y, expectedPerformance A₂ f m φ := rfl
    _ = ∑ f : X → Y, expectedPerformance A₂ f m φ := by
          rw [tsum_fintype]

end NFL.CodexFull.WolpertMacready
