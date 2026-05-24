import NFL.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace NFL.ClaudeFull.WolpertMacready

/-!
# Wolpert--Macready No-Free-Lunch (Claude full proof)

**Theorem.** For any two non-revisiting stochastic search algorithms,
averaged over all cost functions, every fixed observation sequence has
the same total probability.

**Proof strategy.**

Define `avgFuture A h c` = sum over targets consistent with `h` of the
probability that `A` produces observation sequence `c` from history `h`.

**Key lemma** (`avgFuture_eq_pow`): Under the non-revisiting condition and
a nodup history `h` with `|h| + |c| ≤ |X|`,
```
  avgFuture A h c = |Y| ^ (|X| - |h| - |c|)
```

This is proved by induction on `c`:

* *Base case*: the count of consistent targets is `|Y|^(|X| - |h|)`.
* *Inductive step*: expand `avgFuture` via the next-query distribution,
  apply the non-revisiting condition to kill the already-queried summands,
  apply the induction hypothesis to the fresh query, and use `Σ PMF = 1`.

The main theorem follows by applying the lemma from the empty history for
both algorithms; the resulting value `|Y|^(|X| - m)` is algorithm-free.
-/

open scoped ENNReal

variable {X Y : Type*}

/-- A possibly-stochastic search algorithm. -/
structure SearchAlg (X Y : Type*) where
  nextQuery : List (X × Y) → PMF X

/-- Non-revisiting: zero probability on already-queried points. -/
def SearchAlg.NonRevisiting (A : SearchAlg X Y) : Prop :=
  ∀ (h : List (X × Y)) (x : X), x ∈ h.map Prod.fst → A.nextQuery h x = 0

/-- PMF over `m`-step traces. -/
noncomputable def trace (A : SearchAlg X Y) (f : X → Y) : Nat → PMF (List (X × Y))
  | 0 => PMF.pure []
  | n + 1 =>
      (trace A f n).bind fun h =>
        (A.nextQuery h).bind fun x =>
          PMF.pure (h.concat (x, f x))

/-- PMF over observed cost sequences. -/
noncomputable def observations (A : SearchAlg X Y) (f : X → Y) (m : Nat) : PMF (List Y) :=
  (trace A f m).map (·.map Prod.snd)

/-- Front-recursive continuation trace from a history `h`. -/
noncomputable def traceFrom (A : SearchAlg X Y) (f : X → Y) :
    List (X × Y) → Nat → PMF (List (X × Y))
  | _, 0 => PMF.pure []
  | h, n + 1 =>
      (A.nextQuery h).bind fun x =>
        (traceFrom A f (h.concat (x, f x)) n).map fun t => (x, f x) :: t

/-- Observation PMF from a given history. -/
noncomputable def observationsFrom
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y)) (m : Nat) :
    PMF (List Y) :=
  (traceFrom A f h m).map (·.map Prod.snd)

/-! ## PMF composition lemmas -/

private theorem pmf_map_map {α β γ : Type*} (p : PMF α) (f : α → β) (g : β → γ) :
    PMF.map g (PMF.map f p) = PMF.map (fun a => g (f a)) p := by
  rw [← PMF.bind_pure_comp g (PMF.map f p), ← PMF.bind_pure_comp f p, PMF.bind_bind]
  apply congrArg; funext a
  change (PMF.pure (f a)).bind (PMF.pure ∘ g) = PMF.pure (g (f a))
  rw [PMF.pure_bind]; rfl

private theorem observationsFrom_succ
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
  rw [PMF.map_bind]; apply congrArg; funext x
  rw [pmf_map_map, pmf_map_map]; rfl

private theorem pmf_map_cons_apply [DecidableEq Y]
    (p : PMF (List Y)) (a b : Y) (ys : List Y) :
    (PMF.map (fun zs : List Y => a :: zs) p) (b :: ys) =
      if a = b then p ys else 0 := by
  by_cases hab : a = b
  · subst b; rw [if_pos rfl, PMF.map_apply, tsum_eq_single ys]
    · simp
    · intro zs hzs
      have hyzs : ys ≠ zs := fun h => hzs h.symm
      simp [hyzs]
  · rw [if_neg hab, PMF.map_apply, ← tsum_zero]
    apply tsum_congr; intro zs
    by_cases hb : b = a
    · exact False.elim (hab hb.symm)
    · simp [hb]

private theorem observationsFrom_cons_apply [DecidableEq Y]
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y))
    (y : Y) (ys : List Y) :
    observationsFrom A f h (ys.length + 1) (y :: ys) =
      ∑' x : X, A.nextQuery h x *
        (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0) := by
  rw [observationsFrom_succ, PMF.bind_apply]
  apply tsum_congr; intro x; congr 1
  rw [pmf_map_cons_apply]
  by_cases hxy : f x = y
  · subst y; simp
  · simp [hxy]

/-! ## Trace-observation equivalence -/

private theorem traceFrom_append_rec
    (A : SearchAlg X Y) (f : X → Y) (h : List (X × Y)) (n : Nat) :
    traceFrom A f h (n + 1) =
      (traceFrom A f h n).bind fun t =>
        (A.nextQuery (h ++ t)).bind fun x => PMF.pure (t.concat (x, f x)) := by
  induction n generalizing h with
  | zero =>
      unfold traceFrom
      rw [PMF.pure_bind]; simp only [List.append_nil]
      apply congrArg; funext x
      simp [traceFrom, PMF.map, PMF.pure_bind]
  | succ n ih =>
      unfold traceFrom
      rw [PMF.bind_bind]; apply congrArg; funext x
      rw [ih (h.concat (x, f x)), PMF.map_bind,
          ← PMF.bind_pure_comp (fun t : List (X × Y) => (x, f x) :: t)
            (traceFrom A f (h.concat (x, f x)) n),
          PMF.bind_bind]
      apply congrArg; funext t
      change PMF.map (fun t : List (X × Y) => (x, f x) :: t)
          ((A.nextQuery (h.concat (x, f x) ++ t)).bind fun z =>
            PMF.pure (t.concat (z, f z))) =
        (PMF.pure ((x, f x) :: t)).bind fun ttotal =>
          (A.nextQuery (h ++ ttotal)).bind fun z =>
            PMF.pure (ttotal.concat (z, f z))
      rw [PMF.pure_bind, PMF.map_bind]
      simp [PMF.map, PMF.pure_bind, List.concat_eq_append, List.append_assoc]

private theorem trace_eq_traceFrom_nil
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) :
    trace A f m = traceFrom A f [] m := by
  induction m with
  | zero => simp [trace, traceFrom]
  | succ m ih =>
      simp only [trace]; rw [ih, traceFrom_append_rec A f [] m]; simp

private theorem observations_eq_observationsFrom_nil
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) :
    observations A f m = observationsFrom A f [] m := by
  unfold observations observationsFrom; rw [trace_eq_traceFrom_nil]

/-! ## Consistency and compatible-target counting -/

/-- A target function agrees with every entry in a labelled history. -/
def Consistent (f : X → Y) (h : List (X × Y)) : Prop :=
  ∀ xy ∈ h, f xy.1 = xy.2

theorem consistent_nil (f : X → Y) : Consistent f [] :=
  fun _ hxy => nomatch hxy

theorem consistent_concat (f : X → Y) (h : List (X × Y)) (x : X) (y : Y) :
    Consistent f (h.concat (x, y)) ↔ Consistent f h ∧ f x = y := by
  constructor
  · intro hf
    exact ⟨fun xy hxy => hf xy (by
              rw [List.concat_eq_append, List.mem_append]; exact Or.inl hxy),
           hf (x, y) (by
              rw [List.concat_eq_append, List.mem_append, List.mem_singleton]
              exact Or.inr rfl)⟩
  · rintro ⟨hh, hxy⟩ xy hmem
    rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact hh xy hmem
    · exact hxy

/-- Unique label on a queried point in a nodup history. -/
private theorem eq_of_mem_nodup_fst
    {h : List (X × Y)} {a b : X × Y}
    (ha : a ∈ h) (hb : b ∈ h) (hh : (h.map Prod.fst).Nodup) (hab : a.1 = b.1) :
    a = b := by
  induction h with
  | nil => exact nomatch ha
  | cons z zs ih =>
      rw [List.map_cons, List.nodup_cons] at hh
      rcases hh with ⟨hz_not_mem, hzs⟩
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exfalso; exact hz_not_mem (List.mem_map.mpr ⟨b, hb, hab.symm⟩)
      · exfalso; exact hz_not_mem (List.mem_map.mpr ⟨a, ha, hab⟩)
      · exact ih ha hb hzs

/-- The label recorded for a queried point in a history. -/
noncomputable def queriedLabel (h : List (X × Y)) (x : X)
    (hx : x ∈ h.map Prod.fst) : Y :=
  (Classical.choose (List.mem_map.mp hx)).2

private theorem queriedLabel_eq_of_mem
    {h : List (X × Y)} (hh : (h.map Prod.fst).Nodup)
    {xy : X × Y} (hxy : xy ∈ h) :
    queriedLabel h xy.1 (List.mem_map_of_mem hxy) = xy.2 := by
  classical
  unfold queriedLabel
  have hwitness :=
    Classical.choose_spec
      (List.mem_map.mp (List.mem_map_of_mem (f := Prod.fst) hxy))
  have h_eq : Classical.choose _ = xy :=
    eq_of_mem_nodup_fst hwitness.1 hxy hh hwitness.2
  simp [h_eq]

/-- Extend a labelling of the complement to a full function consistent with `h`. -/
noncomputable def extendFromComplement [DecidableEq X]
    (h : List (X × Y)) (g : {x : X // x ∉ h.map Prod.fst} → Y) : X → Y :=
  fun x =>
    if hx : x ∈ h.map Prod.fst then queriedLabel h x hx else g ⟨x, hx⟩

private theorem extendFromComplement_consistent [DecidableEq X]
    {h : List (X × Y)} (hh : (h.map Prod.fst).Nodup)
    (g : {x : X // x ∉ h.map Prod.fst} → Y) :
    Consistent (extendFromComplement h g) h := fun xy hxy => by
  unfold extendFromComplement
  simp [List.mem_map_of_mem hxy, queriedLabel_eq_of_mem hh hxy]

/-- Consistent targets biject with labellings of the unqueried complement. -/
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
      calc queriedLabel h x hx
          = xy.2 := by subst hfst; simpa using hlabel
        _ = f.1 xy.1 := hfxy.symm
        _ = f.1 x := by subst hfst; rfl
    · simp [hx]
  right_inv g := by funext x; simp [extendFromComplement, x.2]

/-- Number of target functions consistent with `h`, as `ℝ≥0∞`. -/
noncomputable def consistentCount (X Y : Type*) [Fintype (X → Y)]
    (h : List (X × Y)) : ℝ≥0∞ := by
  classical
  exact ∑ f : X → Y, if Consistent f h then 1 else 0

/-- `consistentCount` via the `consistentTargets` finset. -/
noncomputable def consistentTargets (X Y : Type*) [Fintype (X → Y)]
    (h : List (X × Y)) : Finset (X → Y) := by
  classical
  exact Finset.univ.filter fun f => Consistent f h

private theorem mem_consistentTargets [Fintype (X → Y)] (h : List (X × Y)) (f : X → Y) :
    f ∈ consistentTargets X Y h ↔ Consistent f h := by
  classical
  simp [consistentTargets]

private theorem consistentCount_eq_card [Fintype (X → Y)] (h : List (X × Y)) :
    consistentCount X Y h = ((consistentTargets X Y h).card : ℝ≥0∞) := by
  classical
  simp [consistentCount, consistentTargets]

/-- A nodup history fixes exactly `|h|` coordinates, so consistent count
    equals `|Y|^(|X| - |h|)`. -/
private theorem consistentCount_eq_pow_card
    [Fintype X] [Fintype Y] [DecidableEq X]
    {h : List (X × Y)} (hh : (h.map Prod.fst).Nodup) :
    consistentCount X Y h = (Fintype.card Y ^ (Fintype.card X - h.length) : ℝ≥0∞) := by
  classical
  rw [consistentCount_eq_card]
  letI : Fintype {f : X → Y // Consistent f h} := Fintype.ofFinite _
  letI : Fintype {x : X // x ∉ h.map Prod.fst} := Fintype.ofFinite _
  have htargets :
      (consistentTargets X Y h).card =
        Fintype.card {f : X → Y // Consistent f h} := by
    rw [Fintype.card_subtype]; simp [consistentTargets]
  rw [htargets]
  have hcomp :
      Fintype.card {x : X // x ∉ h.map Prod.fst} = Fintype.card X - h.length := by
    rw [Fintype.card_subtype]
    have hs : ({x | x ∉ h.map Prod.fst} : Finset X) = ((h.map Prod.fst).toFinset)ᶜ := by
      ext x; simp [List.mem_toFinset]
    rw [show ({x | x ∉ h.map Prod.fst} : Finset X).card = _ from by rw [hs]]
    rw [Finset.card_compl, List.toFinset_card_of_nodup hh]; simp
  have hnat :
      Fintype.card {f : X → Y // Consistent f h} =
        Fintype.card Y ^ (Fintype.card X - h.length) := by
    rw [Fintype.card_congr (consistentEquivComplement h hh), Fintype.card_fun, hcomp]
  rw [hnat]; norm_num

/-! ## Algorithm-independent average future observation -/

/-- The sum over consistent targets of the probability of producing `c`
    from history `h`. -/
noncomputable def avgFuture [Fintype (X → Y)]
    (A : SearchAlg X Y) (h : List (X × Y)) (c : List Y) : ℝ≥0∞ := by
  classical
  exact ∑ f : X → Y,
    if Consistent f h then observationsFrom A f h c.length c else 0

private theorem avgFuture_cons
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
          ∑' x : X, A.nextQuery h x *
            (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0)
        else 0) =
      ∑ f : X → Y, ∑ x : X,
        if Consistent f h then
          A.nextQuery h x *
            (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0)
        else 0 := by
        apply Finset.sum_congr rfl; intro f _
        by_cases hC : Consistent f h
        · simp [hC, tsum_fintype]
        · simp [hC]
    _ = ∑ x : X, ∑ f : X → Y,
        if Consistent f h then
          A.nextQuery h x *
            (if f x = y then observationsFrom A f (h.concat (x, y)) ys.length ys else 0)
        else 0 := Finset.sum_comm
    _ = ∑ x : X, A.nextQuery h x *
          ∑ f : X → Y,
            if Consistent f (h.concat (x, y)) then
              observationsFrom A f (h.concat (x, y)) ys.length ys
            else 0 := by
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro f _
        rw [consistent_concat]
        by_cases hC : Consistent f h <;>
          by_cases hxy : f x = y <;>
          simp [hC, hxy]

/-- **Main lemma**: `avgFuture` depends only on the sizes, not on the
    algorithm. -/
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
      rw [← consistentCount_eq_pow_card hh]
      unfold avgFuture consistentCount
      simp [observationsFrom, traceFrom]
  | cons y ys ih =>
      rw [avgFuture_cons]
      let K : ℝ≥0∞ :=
        (Fintype.card Y ^ (Fintype.card X - (h.length + (y :: ys).length)) : ℝ≥0∞)
      have hterm : ∀ x : X,
          A.nextQuery h x * avgFuture A (h.concat (x, y)) ys = A.nextQuery h x * K := by
        intro x
        by_cases hx : x ∈ h.map Prod.fst
        · rw [hA h x hx]; simp [K]
        · have hh' : (((h.concat (x, y)).map Prod.fst).Nodup) := by
              rw [List.map_concat]; exact hh.concat hx
          have hb' : (h.concat (x, y)).length + ys.length ≤ Fintype.card X := by
              simpa [List.length_cons, Nat.add_left_comm, Nat.add_comm] using hbound
          rw [ih (h.concat (x, y)) hh' hb']
          congr 1; unfold K; congr 1; congr 1
          simp [List.length_cons, Nat.add_left_comm, Nat.add_comm]
      calc ∑' x : X, A.nextQuery h x * avgFuture A (h.concat (x, y)) ys
          = ∑' x : X, A.nextQuery h x * K := tsum_congr hterm
        _ = (∑' x : X, A.nextQuery h x) * K := ENNReal.tsum_mul_right
        _ = K := by rw [PMF.tsum_coe]; simp [K]
        _ = _ := rfl

/-! ## Observation-support length facts -/

private theorem trace_support_length
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (h : List (X × Y)) :
    h ∈ (trace A f m).support → h.length = m := by
  induction m generalizing h with
  | zero =>
      intro hh
      have h_eq : h = [] := by simpa [trace, PMF.mem_support_pure_iff] using hh
      simp [h_eq]
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
      subst h; simp [ih h₀ hh₀]

private theorem observations_support_length
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (c : List Y) :
    c ∈ (observations A f m).support → c.length = m := by
  intro hc
  rcases (PMF.mem_support_map_iff
      (p := trace A f m) (f := fun h : List (X × Y) => h.map Prod.snd) c).mp
    (by simpa [observations] using hc) with ⟨h, hh, hmap⟩
  rw [← hmap, List.length_map]
  exact trace_support_length A f m h hh

private theorem observations_apply_eq_zero_of_length_ne
    (A : SearchAlg X Y) (f : X → Y) (m : Nat) (c : List Y)
    (hc : c.length ≠ m) :
    observations A f m c = 0 := by
  rw [(observations A f m).apply_eq_zero_iff]
  exact fun hs => hc (observations_support_length A f m c hs)

/-! ## Main theorems -/

/-- **Wolpert--Macready histogram identity.**

Summing over all cost functions `f ∈ Y^X`, the probability of producing
any fixed length-`m` observation sequence `c` is the same for every pair
of non-revisiting stochastic search algorithms. -/
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
  have hnodup : (([] : List (X × Y)).map Prod.fst).Nodup := by simp
  have havg₁ :=
    avgFuture_eq_pow (X := X) (Y := Y) A₁ h₁ ([] : List (X × Y)) hnodup c hbound
  have havg₂ :=
    avgFuture_eq_pow (X := X) (Y := Y) A₂ h₂ ([] : List (X × Y)) hnodup c hbound
  have hsum₁ :
      (∑ f : X → Y, observations A₁ f m c) = avgFuture A₁ ([] : List (X × Y)) c := by
    unfold avgFuture
    apply Finset.sum_congr rfl; intro f _
    rw [observations_eq_observationsFrom_nil A₁ f m, ← hc]; simp [consistent_nil]
  have hsum₂ :
      (∑ f : X → Y, observations A₂ f m c) = avgFuture A₂ ([] : List (X × Y)) c := by
    unfold avgFuture
    apply Finset.sum_congr rfl; intro f _
    rw [observations_eq_observationsFrom_nil A₂ f m, ← hc]; simp [consistent_nil]
  rw [hsum₁, hsum₂, havg₁, havg₂]

/-- **Expected-performance corollary.**

No non-revisiting algorithm can achieve better expected performance than
any other when performance is measured only through the observation
sequence and averaged over all cost functions. -/
noncomputable def expectedPerformance
    (A : SearchAlg X Y) (f : X → Y) (m : Nat)
    (φ : List Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' c, observations A f m c * φ c

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
    · exact wolpert_macready A₁ A₂ m hm h₁ h₂ c hc
    · simp [observations_apply_eq_zero_of_length_ne _ _ _ _ hc]
  calc
    (∑ f : X → Y, expectedPerformance A₁ f m φ)
        = ∑' f : X → Y, expectedPerformance A₁ f m φ := by rw [tsum_fintype]
      _ = ∑' f : X → Y, ∑' c : List Y, observations A₁ f m c * φ c := rfl
      _ = ∑' c : List Y, ∑' f : X → Y, observations A₁ f m c * φ c := by
            rw [ENNReal.tsum_comm]
      _ = ∑' c : List Y, (∑ f : X → Y, observations A₁ f m c) * φ c := by
            apply tsum_congr; intro c
            rw [ENNReal.tsum_mul_right, tsum_fintype]
      _ = ∑' c : List Y, (∑ f : X → Y, observations A₂ f m c) * φ c := by
            apply tsum_congr; intro c; rw [hpoint c]
      _ = ∑' c : List Y, ∑' f : X → Y, observations A₂ f m c * φ c := by
            apply tsum_congr; intro c
            rw [ENNReal.tsum_mul_right, tsum_fintype]
      _ = ∑' f : X → Y, ∑' c : List Y, observations A₂ f m c * φ c := by
            rw [ENNReal.tsum_comm]
      _ = ∑' f : X → Y, expectedPerformance A₂ f m φ := rfl
      _ = ∑ f : X → Y, expectedPerformance A₂ f m φ := by rw [tsum_fintype]

end NFL.ClaudeFull.WolpertMacready
