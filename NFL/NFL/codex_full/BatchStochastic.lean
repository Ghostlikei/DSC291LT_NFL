import NFL.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.PowersetCard
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace NFL.CodexFull.BatchStochastic

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unnecessarySeqFocus false

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

/-- Probability that the hypothesis returned by `A` on an i.i.d. sample of size
`m` from `D` has risk at least `ε`. -/
noncomputable def failureProb
    (D : Measure (X × Bool)) (A : Learner X) (m : Nat) (ε : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin m => D))
    {S : Fin m → (X × Bool) | ε ≤ risk D (A (List.ofFn S))}).toReal

/-- Without `[Nonempty X]`, the batch statement has a real edge-case blocker:
there is no probability measure on `Empty × Bool`. -/
theorem no_probability_measure_empty_prod_bool :
    ¬ ∃ D : Measure (Empty × Bool), IsProbabilityMeasure D := by
  rintro ⟨D, hD⟩
  haveI : IsProbabilityMeasure D := hD
  exact (MeasureTheory.nonempty_of_isProbabilityMeasure D).elim
    (fun x => Empty.elim x.1)

/-- The batch stochastic theorem for the zero-sample case. A Dirac distribution
at a point labelled opposite to `A []` makes `A []` incur unit risk, while the
constant target realizes the distribution. -/
theorem batch_stochastic_NFL_zero
    [Nonempty X] [MeasurableSingletonClass X]
    (A : Learner X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, risk D f = 0) ∧
      (1 : ℝ) / 7 ≤ failureProb D A 0 (1 / 8) := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  let b : Bool := !(A [] x0)
  let D : Measure (X × Bool) := Measure.dirac (x0, b)
  have hRealizable : risk D (fun _ => b) = 0 := by
    unfold risk zeroOneLoss D
    rw [integral_dirac]
    simp
  have hRiskA : risk D (A []) = 1 := by
    unfold risk zeroOneLoss D b
    rw [integral_dirac]
    cases A [] x0 <;> simp
  have hEvent :
      {S : Fin 0 → (X × Bool) | (1 : ℝ) / 8 ≤ risk D (A (List.ofFn S))}
        = Set.univ := by
    ext S
    simp [List.ofFn_zero, hRiskA]
    norm_num
  refine ⟨D, inferInstance, ⟨fun _ => b, hRealizable⟩, ?_⟩
  unfold failureProb
  rw [hEvent]
  simp
  norm_num

section PositiveSampleScaffold

variable [Fintype X] [MeasurableSingletonClass X]

/-- Embed a target-labelled domain point into the labelled example space. -/
def graphEmbedding (f : X → Bool) : X ↪ X × Bool where
  toFun x := (x, f x)
  inj' := by
    intro x y hxy
    exact congrArg Prod.fst hxy

/-- The finite graph of a target restricted to a finite support set. -/
def graphFinset (C : Finset X) (f : X → Bool) : Finset (X × Bool) :=
  C.map (graphEmbedding f)

@[simp]
theorem mem_graphFinset {C : Finset X} {f : X → Bool} {xy : X × Bool} :
    xy ∈ graphFinset C f ↔ xy.1 ∈ C ∧ xy.2 = f xy.1 := by
  constructor
  · intro hxy
    rcases Finset.mem_map.mp hxy with ⟨x, hxC, hxy_eq⟩
    rcases hxy_eq with rfl
    exact ⟨hxC, rfl⟩
  · rintro ⟨hxC, hlabel⟩
    rw [← Prod.eta xy, hlabel]
    exact Finset.mem_map.mpr ⟨xy.1, hxC, rfl⟩

@[simp]
theorem graphFinset_card (C : Finset X) (f : X → Bool) :
    (graphFinset C f).card = C.card := by
  simp [graphFinset]

theorem graphFinset_nonempty {C : Finset X} (f : X → Bool) (hC : C.Nonempty) :
    (graphFinset C f).Nonempty := by
  rcases hC with ⟨x, hxC⟩
  exact ⟨(x, f x), by simp [hxC]⟩

/-- Uniform distribution on the graph of `f` over support `C`. -/
noncomputable def graphPMF (C : Finset X) (f : X → Bool) (hC : C.Nonempty) :
    PMF (X × Bool) :=
  PMF.uniformOfFinset (graphFinset C f) (graphFinset_nonempty f hC)

/-- The graph distribution is realizable by the target whose graph defines it. -/
theorem risk_graphPMF_self_zero
    (C : Finset X) (f : X → Bool) (hC : C.Nonempty) :
    risk (graphPMF C f hC).toMeasure f = 0 := by
  classical
  unfold risk
  rw [PMF.integral_eq_sum]
  apply Finset.sum_eq_zero
  intro xy _hxy
  by_cases hxyC : xy ∈ graphFinset C f
  · have hlabel : xy.2 = f xy.1 := (mem_graphFinset.mp hxyC).2
    simp [graphPMF, zeroOneLoss, hxyC, hlabel]
  · have hp : (graphPMF C f hC xy).toReal = 0 := by
      rw [graphPMF, PMF.uniformOfFinset_apply_of_notMem _ hxyC]
      simp
    simp [hp]

/-- Finite risk of a hypothesis on the uniform support `C` labelled by target
`f`, written as an explicit finite average. -/
noncomputable def supportRisk (C : Finset X) (f h : X → Bool) : ℝ :=
  ∑ x ∈ C, (C.card : ℝ)⁻¹ * zeroOneLoss h (x, f x)

/-- The measure-theoretic risk under the uniform graph PMF is the explicit
finite average over the support. -/
theorem risk_graphPMF_eq_supportRisk
    (C : Finset X) (f h : X → Bool) (hC : C.Nonempty) :
    risk (graphPMF C f hC).toMeasure h = supportRisk C f h := by
  classical
  unfold risk supportRisk
  rw [PMF.integral_eq_sum]
  calc
    (∑ xy : X × Bool, (graphPMF C f hC xy).toReal • zeroOneLoss h xy) =
        ∑ xy : X × Bool,
          if xy ∈ graphFinset C f then
            (C.card : ℝ)⁻¹ * zeroOneLoss h xy
          else 0 := by
      apply Finset.sum_congr rfl
      intro xy _hxy
      by_cases hxyC : xy ∈ graphFinset C f
      · simp [graphPMF, PMF.uniformOfFinset_apply_of_mem _ hxyC,
          graphFinset_card, hxyC]
      · simp [graphPMF, PMF.uniformOfFinset_apply_of_notMem _ hxyC, hxyC]
    _ = ∑ xy ∈ graphFinset C f, (C.card : ℝ)⁻¹ * zeroOneLoss h xy := by
      rw [← Finset.sum_filter]
      congr
      ext xy
      simp
    _ = ∑ x ∈ C, (C.card : ℝ)⁻¹ * zeroOneLoss h (x, f x) := by
      simp [graphFinset, graphEmbedding]

theorem supportRisk_nonneg (C : Finset X) (f h : X → Bool) :
    0 ≤ supportRisk C f h := by
  classical
  unfold supportRisk
  apply Finset.sum_nonneg
  intro x _hx
  unfold zeroOneLoss
  split <;> positivity

theorem supportRisk_le_one {C : Finset X} (hC : C.Nonempty) (f h : X → Bool) :
    supportRisk C f h ≤ 1 := by
  classical
  unfold supportRisk
  have hcard_pos : (0 : ℝ) < C.card := by
    exact_mod_cast Finset.card_pos.mpr hC
  calc
    (∑ x ∈ C, (C.card : ℝ)⁻¹ * zeroOneLoss h (x, f x)) ≤
        ∑ x ∈ C, (C.card : ℝ)⁻¹ * 1 := by
      apply Finset.sum_le_sum
      intro x _hx
      have hloss : zeroOneLoss h (x, f x) ≤ 1 := by
        unfold zeroOneLoss
        split <;> norm_num
      nlinarith [inv_pos.mpr hcard_pos]
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp [ne_of_gt hcard_pos]

/-- A support finset of size `2 * m`, extracted from the cardinality hypothesis. -/
theorem exists_support_card
    (m : Nat) (hm : 2 * m ≤ Fintype.card X) :
    ∃ C : Finset X, C.card = 2 * m := by
  classical
  rw [← Finset.card_univ] at hm
  rcases Finset.exists_subset_card_eq (s := (Finset.univ : Finset X)) hm with
    ⟨C, _hCsub, hCcard⟩
  exact ⟨C, hCcard⟩

/-- A sample of indices from the finite support, converted to the labelled
training list supplied to the learner. -/
def supportSampleList {C : Finset X} (f : X → Bool) {m : Nat}
    (S : Fin m → {x : X // x ∈ C}) : List (X × Bool) :=
  List.ofFn fun i => ((S i).1, f (S i).1)

theorem supportSampleList_eq_of_agree {C : Finset X} {f g : X → Bool}
    {m : Nat} {S : Fin m → {x : X // x ∈ C}}
    (hfg : ∀ i, f (S i).1 = g (S i).1) :
    supportSampleList f S = supportSampleList g S := by
  unfold supportSampleList
  rw [List.ofFn_inj]
  funext i
  simp [hfg i]

/-- The support-risk incurred by `A` after seeing a support-indexed sample. -/
noncomputable def sampleRisk (C : Finset X) (A : Learner X)
    (f : X → Bool) {m : Nat} (S : Fin m → {x : X // x ∈ C}) : ℝ :=
  supportRisk C f (A (supportSampleList f S))

theorem sampleRisk_nonneg (C : Finset X) (A : Learner X)
    (f : X → Bool) {m : Nat} (S : Fin m → {x : X // x ∈ C}) :
    0 ≤ sampleRisk C A f S :=
  supportRisk_nonneg C f (A (supportSampleList f S))

theorem sampleRisk_le_one {C : Finset X} (hC : C.Nonempty) (A : Learner X)
    (f : X → Bool) {m : Nat} (S : Fin m → {x : X // x ∈ C}) :
    sampleRisk C A f S ≤ 1 :=
  supportRisk_le_one hC f (A (supportSampleList f S))

/-- The finite counting version of the failure probability over support-indexed
samples. -/
noncomputable def finiteFailureRate (C : Finset X) (A : Learner X)
    (f : X → Bool) (m : Nat) : ℝ :=
  (Fintype.card
      {S : Fin m → {x : X // x ∈ C} // (1 : ℝ) / 8 ≤ sampleRisk C A f S} : ℝ) /
    (Fintype.card (Fin m → {x : X // x ∈ C}) : ℝ)

end PositiveSampleScaffold

section FiniteCombinatorics

variable {Z : Type*} [Fintype Z] [DecidableEq Z]
variable [Fintype X] [MeasurableSingletonClass X]

/-- Split a Boolean labelling into the label at `z` and the labels away from
`z`. -/
def splitAt (z : Z) : (Z → Bool) ≃ ({x : Z // x ≠ z} → Bool) × Bool where
  toFun f := (fun x => f x.1, f z)
  invFun gb := fun x => if hx : x = z then gb.2 else gb.1 ⟨x, hx⟩
  left_inv f := by
    funext x
    by_cases hx : x = z
    · subst hx
      simp
    · simp [hx]
  right_inv gb := by
    ext x
    · simp [x.2]
    · simp

/-- Batch sample generated from support indices. -/
def abstractSampleList (e : Z ↪ X) (f : Z → Bool) {m : Nat}
    (S : Fin m → Z) : List (X × Bool) :=
  List.ofFn fun i => (e (S i), f (S i))

theorem abstractSampleList_eq_of_agree (e : Z ↪ X) {f g : Z → Bool}
    {m : Nat} {S : Fin m → Z} (hfg : ∀ i, f (S i) = g (S i)) :
    abstractSampleList e f S = abstractSampleList e g S := by
  unfold abstractSampleList
  rw [List.ofFn_inj]
  funext i
  simp [hfg i]

/-- Explicit uniform risk on the abstract support type. -/
noncomputable def abstractRisk (e : Z ↪ X) (f : Z → Bool) (h : X → Bool) : ℝ :=
  ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * zeroOneLoss h (e z, f z)

theorem zeroOneLoss_false_add_true (h : X → Bool) (x : X) :
    zeroOneLoss h (x, false) + zeroOneLoss h (x, true) = 1 := by
  unfold zeroOneLoss
  cases h x <;> norm_num

theorem abstractSampleList_splitAt_false_eq_true
    (e : Z ↪ X) {m : Nat} (S : Fin m → Z) {z : Z}
    (hz : ∀ i, S i ≠ z) (r : {x : Z // x ≠ z} → Bool) :
    abstractSampleList e ((splitAt z).symm (r, false)) S =
      abstractSampleList e ((splitAt z).symm (r, true)) S := by
  apply abstractSampleList_eq_of_agree
  intro i
  simp [splitAt, hz i]

theorem loss_sum_over_labels_at_unseen
    (e : Z ↪ X) (A : Learner X) {m : Nat} (S : Fin m → Z) {z : Z}
    (hz : ∀ i, S i ≠ z) :
    (∑ f : Z → Bool,
        zeroOneLoss (A (abstractSampleList e f S)) (e z, f z)) =
      (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by
  classical
  let L : (Z → Bool) → ℝ :=
    fun f => zeroOneLoss (A (abstractSampleList e f S)) (e z, f z)
  calc
    (∑ f : Z → Bool, L f) =
        ∑ rb : ({x : Z // x ≠ z} → Bool) × Bool, L ((splitAt z).symm rb) := by
      exact ((splitAt z).symm.sum_comp L).symm
    _ = ∑ r : {x : Z // x ≠ z} → Bool,
        (L ((splitAt z).symm (r, false)) +
          L ((splitAt z).symm (r, true))) := by
      rw [← Finset.univ_product_univ]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro r _hr
      simp [add_comm]
    _ = ∑ _r : {x : Z // x ≠ z} → Bool, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _hr
      have hsample :
          abstractSampleList e ((splitAt z).symm (r, false)) S =
            abstractSampleList e ((splitAt z).symm (r, true)) S :=
        abstractSampleList_splitAt_false_eq_true e S hz r
      unfold L
      rw [hsample]
      simp [splitAt, zeroOneLoss_false_add_true]
    _ = (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by
      simp

/-- The support points touched by a support-indexed sample. -/
def seenFinset {m : Nat} (S : Fin m → Z) : Finset Z :=
  Finset.univ.image S

/-- The support points not touched by a support-indexed sample. -/
def unseenFinset {m : Nat} (S : Fin m → Z) : Finset Z :=
  Finset.univ \ seenFinset S

@[simp]
theorem mem_seenFinset {m : Nat} {S : Fin m → Z} {z : Z} :
    z ∈ seenFinset S ↔ ∃ i, S i = z := by
  classical
  simp [seenFinset]

@[simp]
theorem mem_unseenFinset {m : Nat} {S : Fin m → Z} {z : Z} :
    z ∈ unseenFinset S ↔ ∀ i, S i ≠ z := by
  classical
  simp [unseenFinset]

theorem seenFinset_card_le {m : Nat} (S : Fin m → Z) :
    (seenFinset S).card ≤ m := by
  classical
  calc
    (seenFinset S).card = (Finset.univ.image S).card := rfl
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    _ = m := by simp

theorem unseenFinset_card_eq {m : Nat} (S : Fin m → Z) :
    (unseenFinset S).card = Fintype.card Z - (seenFinset S).card := by
  classical
  unfold unseenFinset
  rw [Finset.card_sdiff]
  simp [Finset.card_univ]

theorem unseenFinset_card_ge_half {m : Nat} (S : Fin m → Z)
    (hcard : Fintype.card Z = 2 * m) :
    m ≤ (unseenFinset S).card := by
  classical
  rw [unseenFinset_card_eq S, hcard]
  exact Nat.le_sub_of_add_le (by
    nlinarith [seenFinset_card_le S])

theorem labels_card_eq_two_mul_away (z : Z) :
    (Fintype.card (Z → Bool) : ℝ) =
      2 * (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by
  classical
  have hcard :
      Fintype.card (Z → Bool) =
        Fintype.card (({x : Z // x ≠ z} → Bool) × Bool) :=
    Fintype.card_congr (splitAt z)
  rw [Fintype.card_prod, Fintype.card_bool] at hcard
  norm_num [hcard, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]

/-- For a fixed support-indexed sample, the average (over all targets on the
support) risk is at least `1/4` when the support has size `2m`. -/
theorem sum_abstractRisk_fixed_sample_ge
    (e : Z ↪ X) (A : Learner X) {m : Nat} (S : Fin m → Z)
    (hm : 0 < m) (hcard : Fintype.card Z = 2 * m) :
    (Fintype.card (Z → Bool) : ℝ) / 4 ≤
      ∑ f : Z → Bool, abstractRisk e f (A (abstractSampleList e f S)) := by
  classical
  let L : Z → ℝ := fun z =>
    ∑ f : Z → Bool, zeroOneLoss (A (abstractSampleList e f S)) (e z, f z)
  have hZpos_nat : 0 < Fintype.card Z := by
    rw [hcard]
    nlinarith
  have hZpos : (0 : ℝ) < (Fintype.card Z : ℝ) := by
    exact_mod_cast hZpos_nat
  have hmposR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hZcardR : (Fintype.card Z : ℝ) = 2 * (m : ℝ) := by
    rw [hcard]
    norm_num [Nat.cast_mul]
  have hsum_rewrite :
      (∑ f : Z → Bool, abstractRisk e f (A (abstractSampleList e f S))) =
        ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * L z := by
    unfold abstractRisk L
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _hz
    rw [← Finset.mul_sum]
  have hnonneg_z : ∀ z : Z, 0 ≤ (Fintype.card Z : ℝ)⁻¹ * L z := by
    intro z
    apply mul_nonneg
    · exact inv_nonneg.mpr (le_of_lt hZpos)
    · unfold L
      apply Finset.sum_nonneg
      intro f _hf
      unfold zeroOneLoss
      split <;> norm_num
  have hsum_unseen_le :
      (∑ z ∈ (unseenFinset S), (Fintype.card Z : ℝ)⁻¹ * L z) ≤
        ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * L z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by intro z hz; simp)
      (by intro z _hz _hznot; exact hnonneg_z z)
  have hterm : ∀ z, z ∈ unseenFinset S →
      (Fintype.card Z : ℝ)⁻¹ * L z =
        (Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ)) := by
    intro z hz
    have hL : L z = (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by
      unfold L
      exact loss_sum_over_labels_at_unseen e A S (mem_unseenFinset.mp hz)
    rw [hL]
    have hsplit := labels_card_eq_two_mul_away (Z := Z) z
    rw [hsplit]
    field_simp [ne_of_gt hZpos]
  have hunseen_sum_eq :
      (∑ z ∈ (unseenFinset S), (Fintype.card Z : ℝ)⁻¹ * L z) =
        ((unseenFinset S).card : ℝ) *
          ((Fintype.card (Z → Bool) : ℝ) /
            (2 * (Fintype.card Z : ℝ))) := by
    apply Eq.trans (Finset.sum_congr rfl hterm)
    simp [nsmul_eq_mul]
  have hconst_nonneg :
      0 ≤ (Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ)) := by
    positivity
  have hcard_ge_real :
      (m : ℝ) ≤ ((unseenFinset S).card : ℝ) := by
    exact_mod_cast unseenFinset_card_ge_half S hcard
  have hbase :
      (m : ℝ) *
          ((Fintype.card (Z → Bool) : ℝ) /
            (2 * (Fintype.card Z : ℝ))) =
        (Fintype.card (Z → Bool) : ℝ) / 4 := by
    rw [hZcardR]
    field_simp [ne_of_gt hmposR]
    ring
  calc
    (Fintype.card (Z → Bool) : ℝ) / 4 =
        (m : ℝ) *
          ((Fintype.card (Z → Bool) : ℝ) /
            (2 * (Fintype.card Z : ℝ))) := hbase.symm
    _ ≤ ((unseenFinset S).card : ℝ) *
          ((Fintype.card (Z → Bool) : ℝ) /
            (2 * (Fintype.card Z : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard_ge_real hconst_nonneg
    _ = ∑ z ∈ (unseenFinset S), (Fintype.card Z : ℝ)⁻¹ * L z :=
        hunseen_sum_eq.symm
    _ ≤ ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * L z := hsum_unseen_le
    _ = ∑ f : Z → Bool, abstractRisk e f (A (abstractSampleList e f S)) :=
        hsum_rewrite.symm

/-- Bad support-indexed samples for the abstract support model. -/
noncomputable def abstractBadSamples (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat) : Finset (Fin m → Z) :=
  Finset.univ.filter fun S =>
    (1 : ℝ) / 8 ≤ abstractRisk e f (A (abstractSampleList e f S))

/-- Finite failure rate for the abstract support model. -/
noncomputable def abstractFailureRate (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat) : ℝ :=
  ((abstractBadSamples e A f m).card : ℝ) /
    (Fintype.card (Fin m → Z) : ℝ)

theorem abstractRisk_le_one_of_card_pos
    (hZpos : 0 < Fintype.card Z) (e : Z ↪ X) (f : Z → Bool)
    (h : X → Bool) :
    abstractRisk e f h ≤ 1 := by
  classical
  have hZposR : (0 : ℝ) < (Fintype.card Z : ℝ) := by
    exact_mod_cast hZpos
  unfold abstractRisk
  calc
    (∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * zeroOneLoss h (e z, f z)) ≤
        ∑ _z : Z, (Fintype.card Z : ℝ)⁻¹ * 1 := by
      apply Finset.sum_le_sum
      intro z _hz
      have hloss : zeroOneLoss h (e z, f z) ≤ 1 := by
        unfold zeroOneLoss
        split <;> norm_num
      nlinarith [inv_pos.mpr hZposR]
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp [ne_of_gt hZposR]

theorem sum_piecewise_one_eighth {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset Ω) :
    (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) =
      (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) := by
  classical
  have hpoint : ∀ S : Ω,
      (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ)) =
        (1 / 8 : ℝ) + if S ∈ B then (7 / 8 : ℝ) else 0 := by
    intro S
    by_cases hS : S ∈ B <;> simp [hS] <;> norm_num
  calc
    (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) =
        ∑ S : Ω, ((1 / 8 : ℝ) + if S ∈ B then (7 / 8 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro S _hS
      exact hpoint S
    _ = (Fintype.card Ω : ℝ) / 8 +
          ∑ S : Ω, (if S ∈ B then (7 / 8 : ℝ) else 0) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) := by
      congr 1
      calc
        (∑ S : Ω, (if S ∈ B then (7 / 8 : ℝ) else 0)) =
            ∑ S ∈ (Finset.univ : Finset Ω),
              (if S ∈ B then (7 / 8 : ℝ) else 0) := rfl
        _ = ∑ S ∈ ((Finset.univ : Finset Ω) ∩ B), (7 / 8 : ℝ) := by
          rw [Finset.sum_ite_mem]
        _ = (7 / 8 : ℝ) * (B.card : ℝ) := by
          simp [nsmul_eq_mul, mul_comm]

theorem sum_abstractRisk_lt_of_failureRate_lt
    (hZpos : 0 < Fintype.card Z) (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat)
    (hfail : abstractFailureRate e A f m < (1 : ℝ) / 7) :
    (∑ S : Fin m → Z, abstractRisk e f (A (abstractSampleList e f S))) <
      (Fintype.card (Fin m → Z) : ℝ) / 4 := by
  classical
  let Ω := Fin m → Z
  let B : Finset Ω := abstractBadSamples e A f m
  have hZnonempty : Nonempty Z := Fintype.card_pos_iff.mp hZpos
  haveI : Nonempty Z := hZnonempty
  have hΩpos_nat : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr inferInstance
  have hΩpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast hΩpos_nat
  have hfail' : (B.card : ℝ) / (Fintype.card Ω : ℝ) < (1 : ℝ) / 7 := by
    simpa [B, Ω, abstractFailureRate] using hfail
  have hbad_lt : (B.card : ℝ) < (Fintype.card Ω : ℝ) / 7 := by
    have this := mul_lt_mul_of_pos_right hfail' hΩpos
    field_simp [ne_of_gt hΩpos] at this
    nlinarith
  have hpoint : ∀ S : Ω,
      abstractRisk e f (A (abstractSampleList e f S)) ≤
        if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ) := by
    intro S
    by_cases hS : S ∈ B
    · simp [hS, abstractRisk_le_one_of_card_pos hZpos e f]
    · have hnot :
          ¬ (1 : ℝ) / 8 ≤ abstractRisk e f (A (abstractSampleList e f S)) := by
        simpa [B, abstractBadSamples] using hS
      have hlt :
          abstractRisk e f (A (abstractSampleList e f S)) < (1 : ℝ) / 8 :=
        lt_of_not_ge hnot
      simpa [hS] using le_of_lt hlt
  have hsum_le :
      (∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S))) ≤
        (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) := by
    apply Finset.sum_le_sum
    intro S _hS
    exact hpoint S
  have hpiece := sum_piecewise_one_eighth B
  have hupper_lt :
      (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) <
        (Fintype.card Ω : ℝ) / 4 := by
    have hmul : (7 / 8 : ℝ) * (B.card : ℝ) <
        (7 / 8 : ℝ) * ((Fintype.card Ω : ℝ) / 7) := by
      exact mul_lt_mul_of_pos_left hbad_lt (by norm_num)
    calc
      (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) <
          (Fintype.card Ω : ℝ) / 8 +
            (7 / 8 : ℝ) * ((Fintype.card Ω : ℝ) / 7) := by
        exact add_lt_add_of_le_of_lt le_rfl hmul
      _ = (Fintype.card Ω : ℝ) / 4 := by
        ring
  have hsum_piece_lt :
      (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) <
        (Fintype.card Ω : ℝ) / 4 := by
    rw [hpiece]
    exact hupper_lt
  simpa [Ω] using lt_of_le_of_lt hsum_le hsum_piece_lt

/-- Finite probabilistic-method conclusion on an abstract support of size
`2m`: some target has empirical failure rate at least `1/7`. -/
theorem exists_abstractFailureRate_ge
    (e : Z ↪ X) (A : Learner X) {m : Nat}
    (hm : 0 < m) (hcard : Fintype.card Z = 2 * m) :
    ∃ f : Z → Bool, (1 : ℝ) / 7 ≤ abstractFailureRate e A f m := by
  classical
  by_contra hno
  let Ω := Fin m → Z
  let F := Z → Bool
  have hZpos : 0 < Fintype.card Z := by
    rw [hcard]
    nlinarith
  have hFnonempty : Nonempty F := ⟨fun _ => false⟩
  haveI : Nonempty F := hFnonempty
  have hall_lt : ∀ f : F, abstractFailureRate e A f m < (1 : ℝ) / 7 := by
    intro f
    have hf : ¬ (1 : ℝ) / 7 ≤ abstractFailureRate e A f m := by
      intro hf
      exact hno ⟨f, hf⟩
    exact not_le.mp hf
  have hlower_each : ∀ S : Ω,
      (Fintype.card F : ℝ) / 4 ≤
        ∑ f : F, abstractRisk e f (A (abstractSampleList e f S)) := by
    intro S
    exact sum_abstractRisk_fixed_sample_ge e A S hm hcard
  have hlower_sum :
      (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) ≤
        ∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S)) := by
    calc
      (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) =
          ∑ _S : Ω, ((Fintype.card F : ℝ) / 4) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S)) := by
        apply Finset.sum_le_sum
        intro S _hS
        exact hlower_each S
  have hupper_each : ∀ f : F,
      (∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S))) <
        (Fintype.card Ω : ℝ) / 4 := by
    intro f
    exact sum_abstractRisk_lt_of_failureRate_lt hZpos e A f m (hall_lt f)
  have hupper_sum :
      (∑ f : F, ∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S))) <
        ∑ _f : F, ((Fintype.card Ω : ℝ) / 4) := by
    apply Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset F))
    · exact Finset.univ_nonempty
    · intro f _hf
      exact hupper_each f
  have hswap :
      (∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S))) =
        ∑ f : F, ∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S)) := by
    rw [Finset.sum_comm]
  have hstrict :
      (∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S))) <
        (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) := by
    calc
      (∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S))) =
          ∑ f : F, ∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S)) :=
        hswap
      _ < ∑ _f : F, ((Fintype.card Ω : ℝ) / 4) := hupper_sum
      _ = (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  exact not_lt_of_ge hlower_sum hstrict

end FiniteCombinatorics

section ConcreteBridge

variable [Fintype X] [MeasurableSingletonClass X]

/-- A support-indexed sample as an actual labelled sample from the graph of
`f`. -/
def supportTraceEmbedding (C : Finset X) (f : X → Bool) (m : Nat) :
    (Fin m → {x : X // x ∈ C}) ↪ (Fin m → X × Bool) where
  toFun S := fun i => ((S i).1, f (S i).1)
  inj' := by
    intro S T hST
    funext i
    apply Subtype.ext
    exact congrArg Prod.fst (congrFun hST i)

theorem supportTrace_list_eq_abstractSampleList
    (C : Finset X) (fX : X → Bool) (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z)
    {m : Nat} (S : Fin m → {x : X // x ∈ C}) :
    List.ofFn (supportTraceEmbedding C fX m S) =
      abstractSampleList (Function.Embedding.subtype (fun x : X => x ∈ C)) fZ S := by
  unfold supportTraceEmbedding abstractSampleList
  rw [List.ofFn_inj]
  funext i
  simp [hExt (S i)]

theorem supportRisk_eq_abstractRisk_subtype
    (C : Finset X) (fX h : X → Bool) (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z) :
    supportRisk C fX h =
      abstractRisk (Function.Embedding.subtype (fun x : X => x ∈ C)) fZ h := by
  classical
  unfold supportRisk abstractRisk
  have hcard : Fintype.card {x : X // x ∈ C} = C.card := by
    exact Fintype.card_ofFinset C (by intro x; rfl)
  rw [hcard]
  rw [← Finset.sum_attach C
    (fun x => (C.card : ℝ)⁻¹ * zeroOneLoss h (x, fX x))]
  apply Finset.sum_congr rfl
  intro z _hz
  simp [Function.Embedding.subtype, hExt z]

theorem risk_graphPMF_eq_abstractRisk_subtype
    (C : Finset X) (fX h : X → Bool) (hC : C.Nonempty)
    (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z) :
    risk (graphPMF C fX hC).toMeasure h =
      abstractRisk (Function.Embedding.subtype (fun x : X => x ∈ C)) fZ h := by
  rw [risk_graphPMF_eq_supportRisk C fX h hC]
  exact supportRisk_eq_abstractRisk_subtype C fX h fZ hExt

theorem pi_graph_singleton_supportTrace
    (C : Finset X) (f : X → Bool) (hC : C.Nonempty) (m : Nat)
    (S : Fin m → {x : X // x ∈ C}) :
    (Measure.pi (fun _ : Fin m => (graphPMF C f hC).toMeasure))
        {supportTraceEmbedding C f m S} =
      ((C.card : ℝ≥0∞)⁻¹) ^ m := by
  classical
  rw [Measure.pi_singleton]
  calc
    (∏ i : Fin m, ((graphPMF C f hC).toMeasure)
        {supportTraceEmbedding C f m S i}) =
        ∏ _i : Fin m, ((C.card : ℝ≥0∞)⁻¹) := by
      apply Finset.prod_congr rfl
      intro i _hi
      have hmem : supportTraceEmbedding C f m S i ∈ graphFinset C f := by
        simp [supportTraceEmbedding]
      rw [PMF.toMeasure_apply_singleton _ _
        (MeasurableSingletonClass.measurableSet_singleton _)]
      simp [graphPMF, PMF.uniformOfFinset_apply_of_mem _ hmem, graphFinset_card]
    _ = ((C.card : ℝ≥0∞)⁻¹) ^ m := by
      simp

theorem pi_graph_measure_supportTraceFinset
    (C : Finset X) (f : X → Bool) (hC : C.Nonempty) (m : Nat)
    (B : Finset (Fin m → {x : X // x ∈ C})) :
    (Measure.pi (fun _ : Fin m => (graphPMF C f hC).toMeasure))
        ↑(B.map (supportTraceEmbedding C f m)) =
      (B.card : ℝ≥0∞) * ((C.card : ℝ≥0∞)⁻¹) ^ m := by
  classical
  let μ := Measure.pi (fun _ : Fin m => (graphPMF C f hC).toMeasure)
  calc
    μ ↑(B.map (supportTraceEmbedding C f m)) =
        ∑ T ∈ B.map (supportTraceEmbedding C f m), μ {T} := by
      rw [← MeasureTheory.sum_measure_singleton]
    _ = ∑ T ∈ B.map (supportTraceEmbedding C f m),
        ((C.card : ℝ≥0∞)⁻¹) ^ m := by
      apply Finset.sum_congr rfl
      intro T hT
      rcases Finset.mem_map.mp hT with ⟨S, _hS, rfl⟩
      exact pi_graph_singleton_supportTrace C f hC m S
    _ = (B.card : ℝ≥0∞) * ((C.card : ℝ≥0∞)⁻¹) ^ m := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_map]

theorem supportTrace_weight_toReal
    (C : Finset X) (m : Nat) (Bcard : Nat) :
    ((Bcard : ℝ≥0∞) * ((C.card : ℝ≥0∞)⁻¹) ^ m).toReal =
      (Bcard : ℝ) / (Fintype.card (Fin m → {x : X // x ∈ C}) : ℝ) := by
  classical
  have hCcard : Fintype.card {x : X // x ∈ C} = C.card := by
    exact Fintype.card_ofFinset C (by intro x; rfl)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast]
  rw [Fintype.card_fun, Fintype.card_fin, hCcard]
  norm_num [div_eq_mul_inv, Nat.cast_pow]

theorem abstractFailureRate_le_failureProb_graph
    (C : Finset X) (hC : C.Nonempty) (A : Learner X)
    (fX : X → Bool) (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z)
    (m : Nat) :
    abstractFailureRate
        (Function.Embedding.subtype (fun x : X => x ∈ C)) A fZ m ≤
      failureProb (graphPMF C fX hC).toMeasure A m (1 / 8) := by
  classical
  let e : {x : X // x ∈ C} ↪ X :=
    Function.Embedding.subtype (fun x : X => x ∈ C)
  let B : Finset (Fin m → {x : X // x ∈ C}) := abstractBadSamples e A fZ m
  let μ := Measure.pi (fun _ : Fin m => (graphPMF C fX hC).toMeasure)
  let event : Set (Fin m → X × Bool) :=
    {S | (1 : ℝ) / 8 ≤ risk (graphPMF C fX hC).toMeasure (A (List.ofFn S))}
  have hsubset : ↑(B.map (supportTraceEmbedding C fX m)) ⊆ event := by
    intro T hT
    rcases Finset.mem_map.mp hT with ⟨S, hS, rfl⟩
    have hbad :
        (1 : ℝ) / 8 ≤ abstractRisk e fZ (A (abstractSampleList e fZ S)) := by
      simpa [B, abstractBadSamples] using hS
    have hlist :
        List.ofFn (supportTraceEmbedding C fX m S) = abstractSampleList e fZ S := by
      exact supportTrace_list_eq_abstractSampleList C fX fZ hExt S
    have hrisk :
        risk (graphPMF C fX hC).toMeasure
            (A (List.ofFn (supportTraceEmbedding C fX m S))) =
          abstractRisk e fZ (A (abstractSampleList e fZ S)) := by
      rw [hlist]
      exact risk_graphPMF_eq_abstractRisk_subtype C fX
        (A (abstractSampleList e fZ S)) hC fZ hExt
    exact (show (1 : ℝ) / 8 ≤
        risk (graphPMF C fX hC).toMeasure
          (A (List.ofFn (supportTraceEmbedding C fX m S))) from by
      rwa [hrisk])
  have hmono :
      μ ↑(B.map (supportTraceEmbedding C fX m)) ≤ μ event :=
    measure_mono hsubset
  have himage_toReal :
      (μ ↑(B.map (supportTraceEmbedding C fX m))).toReal =
        abstractFailureRate e A fZ m := by
    rw [pi_graph_measure_supportTraceFinset C fX hC m B]
    rw [supportTrace_weight_toReal C m B.card]
    rfl
  haveI : IsProbabilityMeasure μ := inferInstance
  have hevent_ne_top : μ event ≠ ∞ := measure_ne_top μ event
  calc
    abstractFailureRate e A fZ m =
        (μ ↑(B.map (supportTraceEmbedding C fX m))).toReal := himage_toReal.symm
    _ ≤ (μ event).toReal := ENNReal.toReal_mono hevent_ne_top hmono
    _ = failureProb (graphPMF C fX hC).toMeasure A m (1 / 8) := rfl

end ConcreteBridge

/-- **Batch stochastic NFL.** For any deterministic learner on a nonempty finite
domain and any sample size `m` with `2m ≤ |X|`, there is a realizable
distribution on labelled examples such that the learner returns a hypothesis
with risk at least `1/8` with probability at least `1/7`. -/
theorem batch_stochastic_NFL
    [Fintype X] [Nonempty X] [MeasurableSingletonClass X]
    (A : Learner X) (m : Nat) (hm : 2 * m ≤ Fintype.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, risk D f = 0) ∧
      (1 : ℝ) / 7 ≤ failureProb D A m (1 / 8) := by
  cases m with
  | zero =>
      exact batch_stochastic_NFL_zero A
  | succ k =>
      classical
      rcases exists_support_card (X := X) (Nat.succ k) hm with ⟨C, hCcard⟩
      have hCnonempty : C.Nonempty := by
        apply Finset.card_pos.mp
        rw [hCcard]
        nlinarith
      let Z := {x : X // x ∈ C}
      let e : Z ↪ X := Function.Embedding.subtype (fun x : X => x ∈ C)
      have hZcard : Fintype.card Z = 2 * Nat.succ k := by
        change Fintype.card ↥C = 2 * Nat.succ k
        rw [Fintype.card_coe C, hCcard]
      rcases exists_abstractFailureRate_ge (X := X) (Z := Z) e A
          (Nat.succ_pos k) hZcard with ⟨fZ, hfailZ⟩
      let fX : X → Bool := fun x => if hx : x ∈ C then fZ ⟨x, hx⟩ else false
      have hExt : ∀ z : Z, fX z.1 = fZ z := by
        intro z
        simp [fX, z.2]
      let D : Measure (X × Bool) := (graphPMF C fX hCnonempty).toMeasure
      refine ⟨D, inferInstance, ⟨fX, ?_⟩, ?_⟩
      · exact risk_graphPMF_self_zero C fX hCnonempty
      · exact le_trans hfailZ
          (abstractFailureRate_le_failureProb_graph C hCnonempty A fX fZ hExt
            (Nat.succ k))

/-!
Positive-sample proof structure:

1. Choose a finset `C : Finset X` of cardinality `2 * m` from
   `2 * m ≤ Fintype.card X`.
2. Work abstractly on the support subtype `Z`, averaging over all labellings
   `Z → Bool`.
3. Prove `sum_abstractRisk_fixed_sample_ge`: every fixed sample sees at most
   `m` points, hence at least `m` points are unseen, and label-pairing gives
   average risk at least `1 / 4`.
4. Prove `exists_abstractFailureRate_ge` by contradiction from the finite risk
   upper bound `risk ≤ 1` on bad samples and `risk < 1 / 8` on good samples.
5. Map bad support-indexed samples into graph-labelled samples and compute their
   `Measure.pi` mass from singleton products.
6. Assemble the graph PMF, realizability, and the failure-probability lower
   bound in `batch_stochastic_NFL`.
-/

end NFL.CodexFull.BatchStochastic
