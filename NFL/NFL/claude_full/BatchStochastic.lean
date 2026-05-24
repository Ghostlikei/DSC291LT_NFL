import NFL.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.PowersetCard
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace NFL.ClaudeFull.BatchStochastic

/-!
# Batch Stochastic No-Free-Lunch (Claude full proof)

**Theorem.** For any deterministic learner `A` on a finite domain with
`2m ≤ |X|`, there exists a realizable distribution `D` such that with
probability at least `1/7` over an i.i.d. sample `S ∼ D^m`, the learner's
hypothesis has risk at least `1/8`.

## Proof outline

1. **$m = 0$ case**: Dirac measure at a point labelled to fool `A([])`.

2. **$m ≥ 1$ case**:
   a. Fix a support `C ⊆ X` with `|C| = 2m`.
   b. Abstract away to the subtype `Z = C`, using the sub-embedding.
   c. **Fixed-sample lower bound**: For any sample `S : Fin m → Z`,
      the average (over all labellings `Z → Bool`) of the abstract risk
      is ≥ `|Bool^Z| / 4`, because ≥ m points are unseen and contribute
      independent label pairs summing to 1 each.
   d. **Contradiction argument**: If every target had abstract failure
      rate `< 1/7` (fraction of samples with risk ≥ 1/8), the double
      sum `Σ_S Σ_f R(f,S)` would be `< |Ω|·|Bool^Z|/4` (using
      the piecewise upper bound `7/8 · (1/7) = 1/8`), contradicting (c).
   e. **Bridge to the continuous setting**: bad support-indexed samples
      embed injectively into bad continuous samples; measure is preserved.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unnecessarySeqFocus false

/-- A deterministic learning algorithm. -/
abbrev Learner (X : Type*) := List (X × Bool) → (X → Bool)

variable {X : Type*}

/-- 0-1 loss on a single labelled example. -/
def zeroOneLoss (h : X → Bool) (xy : X × Bool) : ℝ :=
  if h xy.1 = xy.2 then 0 else 1

variable [MeasurableSpace X]

/-- Measure-theoretic risk under distribution `D`. -/
noncomputable def risk (D : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  ∫ xy, zeroOneLoss h xy ∂D

/-- Failure probability: fraction of i.i.d. samples with risk ≥ ε. -/
noncomputable def failureProb
    (D : Measure (X × Bool)) (A : Learner X) (m : Nat) (ε : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin m => D))
    {S : Fin m → (X × Bool) | ε ≤ risk D (A (List.ofFn S))}).toReal

/-! ## Zero-sample case -/

/-- For `m = 0`, a Dirac measure at the point labelled opposite to `A []` works. -/
theorem batch_stochastic_NFL_zero
    [Nonempty X] [MeasurableSingletonClass X]
    (A : Learner X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, risk D f = 0) ∧
      (1 : ℝ) / 7 ≤ failureProb D A 0 (1 / 8) := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  -- Label x0 opposite to what A would predict.
  let b : Bool := !(A [] x0)
  let D : Measure (X × Bool) := Measure.dirac (x0, b)
  have hRealizable : risk D (fun _ => b) = 0 := by
    unfold risk zeroOneLoss D; rw [integral_dirac]; simp
  have hRiskA : risk D (A []) = 1 := by
    unfold risk zeroOneLoss D b; rw [integral_dirac]; cases A [] x0 <;> simp
  have hEvent :
      {S : Fin 0 → (X × Bool) | (1 : ℝ) / 8 ≤ risk D (A (List.ofFn S))} = Set.univ := by
    ext S; simp [List.ofFn_zero, hRiskA]; norm_num
  refine ⟨D, inferInstance, ⟨fun _ => b, hRealizable⟩, ?_⟩
  unfold failureProb; rw [hEvent]; simp; norm_num

/-! ## Positive-sample scaffold -/

section PositiveSampleScaffold

variable [Fintype X] [MeasurableSingletonClass X]

/-- Injective embedding of the graph of `f` over a support. -/
def graphEmbedding (f : X → Bool) : X ↪ X × Bool where
  toFun x := (x, f x)
  inj' := fun x y hxy => congrArg Prod.fst hxy

/-- The labelled graph finset. -/
def graphFinset (C : Finset X) (f : X → Bool) : Finset (X × Bool) :=
  C.map (graphEmbedding f)

@[simp]
theorem mem_graphFinset {C : Finset X} {f : X → Bool} {xy : X × Bool} :
    xy ∈ graphFinset C f ↔ xy.1 ∈ C ∧ xy.2 = f xy.1 := by
  constructor
  · intro hxy
    rcases Finset.mem_map.mp hxy with ⟨x, hxC, hxy_eq⟩
    subst hxy_eq; exact ⟨hxC, rfl⟩
  · rintro ⟨hxC, hlabel⟩; rw [← Prod.eta xy, hlabel]; exact Finset.mem_map.mpr ⟨xy.1, hxC, rfl⟩

@[simp]
theorem graphFinset_card (C : Finset X) (f : X → Bool) :
    (graphFinset C f).card = C.card := by simp [graphFinset]

theorem graphFinset_nonempty {C : Finset X} (f : X → Bool) (hC : C.Nonempty) :
    (graphFinset C f).Nonempty :=
  let ⟨x, hxC⟩ := hC; ⟨(x, f x), by simp [hxC]⟩

/-- The uniform distribution on the labelled graph of `f` over `C`. -/
noncomputable def graphPMF (C : Finset X) (f : X → Bool) (hC : C.Nonempty) :
    PMF (X × Bool) :=
  PMF.uniformOfFinset (graphFinset C f) (graphFinset_nonempty f hC)

/-- The target `f` itself has zero risk under the graph PMF. -/
theorem risk_graphPMF_self_zero
    (C : Finset X) (f : X → Bool) (hC : C.Nonempty) :
    risk (graphPMF C f hC).toMeasure f = 0 := by
  classical
  unfold risk; rw [PMF.integral_eq_sum]
  apply Finset.sum_eq_zero; intro xy _
  by_cases hxyC : xy ∈ graphFinset C f
  · have hlabel : xy.2 = f xy.1 := (mem_graphFinset.mp hxyC).2
    simp [graphPMF, zeroOneLoss, hxyC, hlabel]
  · have hp : (graphPMF C f hC xy).toReal = 0 := by
      rw [graphPMF, PMF.uniformOfFinset_apply_of_notMem _ hxyC]; simp
    simp [hp]

/-- Explicit finite risk on the support: `(1/|C|) Σ_{x ∈ C} loss(h(x), f(x))`. -/
noncomputable def supportRisk (C : Finset X) (f h : X → Bool) : ℝ :=
  ∑ x ∈ C, (C.card : ℝ)⁻¹ * zeroOneLoss h (x, f x)

/-- The measure-theoretic risk under `graphPMF` equals `supportRisk`. -/
theorem risk_graphPMF_eq_supportRisk
    (C : Finset X) (f h : X → Bool) (hC : C.Nonempty) :
    risk (graphPMF C f hC).toMeasure h = supportRisk C f h := by
  classical
  unfold risk supportRisk; rw [PMF.integral_eq_sum]
  calc (∑ xy : X × Bool, (graphPMF C f hC xy).toReal • zeroOneLoss h xy)
      = ∑ xy : X × Bool,
          if xy ∈ graphFinset C f then (C.card : ℝ)⁻¹ * zeroOneLoss h xy else 0 := by
        apply Finset.sum_congr rfl; intro xy _
        by_cases hxyC : xy ∈ graphFinset C f
        · simp [graphPMF, PMF.uniformOfFinset_apply_of_mem _ hxyC, graphFinset_card, hxyC]
        · simp [graphPMF, PMF.uniformOfFinset_apply_of_notMem _ hxyC, hxyC]
    _ = ∑ xy ∈ graphFinset C f, (C.card : ℝ)⁻¹ * zeroOneLoss h xy := by
        rw [← Finset.sum_filter]; congr; ext xy; simp
    _ = ∑ x ∈ C, (C.card : ℝ)⁻¹ * zeroOneLoss h (x, f x) := by
        simp [graphFinset, graphEmbedding]

theorem supportRisk_nonneg (C : Finset X) (f h : X → Bool) :
    0 ≤ supportRisk C f h := by
  apply Finset.sum_nonneg; intro x _
  unfold zeroOneLoss; split <;> positivity

theorem supportRisk_le_one {C : Finset X} (hC : C.Nonempty) (f h : X → Bool) :
    supportRisk C f h ≤ 1 := by
  classical
  unfold supportRisk
  have hcard_pos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  calc (∑ x ∈ C, (C.card : ℝ)⁻¹ * zeroOneLoss h (x, f x))
      ≤ ∑ _x ∈ C, (C.card : ℝ)⁻¹ * 1 := by
        apply Finset.sum_le_sum; intro x _
        have hloss : zeroOneLoss h (x, f x) ≤ 1 := by
          unfold zeroOneLoss; split <;> norm_num
        nlinarith [inv_pos.mpr hcard_pos]
    _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp [ne_of_gt hcard_pos]

/-- Extract a finset of cardinality `2m` from `2m ≤ |X|`. -/
theorem exists_support_card
    (m : Nat) (hm : 2 * m ≤ Fintype.card X) :
    ∃ C : Finset X, C.card = 2 * m := by
  classical
  rw [← Finset.card_univ] at hm
  exact let ⟨C, _, hCcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hm; ⟨C, hCcard⟩

end PositiveSampleScaffold

/-! ## Abstract finite combinatorics -/

section FiniteCombinatorics

variable {Z : Type*} [Fintype Z] [DecidableEq Z]
variable [Fintype X] [MeasurableSingletonClass X]

/-- Split a Boolean labelling at a point `z`. -/
def splitAt (z : Z) : (Z → Bool) ≃ ({x : Z // x ≠ z} → Bool) × Bool where
  toFun f := (fun x => f x.1, f z)
  invFun gb := fun x => if hx : x = z then gb.2 else gb.1 ⟨x, hx⟩
  left_inv f := by funext x; by_cases hx : x = z <;> simp [hx]
  right_inv gb := by
    ext x
    · simp [x.2]
    · simp

/-- Abstract training sample: embed `Z` into `X` and label by `f`. -/
def abstractSampleList (e : Z ↪ X) (f : Z → Bool) {m : Nat}
    (S : Fin m → Z) : List (X × Bool) :=
  List.ofFn fun i => (e (S i), f (S i))

theorem abstractSampleList_eq_of_agree (e : Z ↪ X) {f g : Z → Bool}
    {m : Nat} {S : Fin m → Z} (hfg : ∀ i, f (S i) = g (S i)) :
    abstractSampleList e f S = abstractSampleList e g S := by
  unfold abstractSampleList; rw [List.ofFn_inj]; funext i; simp [hfg i]

/-- Abstract risk: average 0-1 loss over `Z`. -/
noncomputable def abstractRisk (e : Z ↪ X) (f : Z → Bool) (h : X → Bool) : ℝ :=
  ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * zeroOneLoss h (e z, f z)

/-- The pair (false, true) contributes total loss 1 at any point. -/
theorem zeroOneLoss_false_add_true (h : X → Bool) (x : X) :
    zeroOneLoss h (x, false) + zeroOneLoss h (x, true) = 1 := by
  unfold zeroOneLoss; cases h x <;> norm_num

/-- Flipping the label at an unseen point `z` doesn't change the training sample. -/
theorem abstractSampleList_splitAt_false_eq_true
    (e : Z ↪ X) {m : Nat} (S : Fin m → Z) {z : Z}
    (hz : ∀ i, S i ≠ z) (r : {x : Z // x ≠ z} → Bool) :
    abstractSampleList e ((splitAt z).symm (r, false)) S =
      abstractSampleList e ((splitAt z).symm (r, true)) S := by
  apply abstractSampleList_eq_of_agree; intro i; simp [splitAt, hz i]

/-- Summing the loss at an unseen point `z` over all labellings gives `|{x≠z}→Bool|`. -/
theorem loss_sum_over_labels_at_unseen
    (e : Z ↪ X) (A : Learner X) {m : Nat} (S : Fin m → Z) {z : Z}
    (hz : ∀ i, S i ≠ z) :
    (∑ f : Z → Bool,
        zeroOneLoss (A (abstractSampleList e f S)) (e z, f z)) =
      (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by
  classical
  let L : (Z → Bool) → ℝ :=
    fun f => zeroOneLoss (A (abstractSampleList e f S)) (e z, f z)
  calc (∑ f : Z → Bool, L f)
      = ∑ rb : ({x : Z // x ≠ z} → Bool) × Bool, L ((splitAt z).symm rb) :=
          ((splitAt z).symm.sum_comp L).symm
    _ = ∑ r : {x : Z // x ≠ z} → Bool,
          (L ((splitAt z).symm (r, false)) + L ((splitAt z).symm (r, true))) := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        apply Finset.sum_congr rfl; intro r _; simp [add_comm]
    _ = ∑ _r : {x : Z // x ≠ z} → Bool, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro r _
        have hsample : abstractSampleList e ((splitAt z).symm (r, false)) S =
            abstractSampleList e ((splitAt z).symm (r, true)) S :=
          abstractSampleList_splitAt_false_eq_true e S hz r
        unfold L; rw [hsample]; simp [splitAt, zeroOneLoss_false_add_true]
    _ = (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by simp

/-- The seen and unseen finsets. -/
def seenFinset {m : Nat} (S : Fin m → Z) : Finset Z := Finset.univ.image S
def unseenFinset {m : Nat} (S : Fin m → Z) : Finset Z := Finset.univ \ seenFinset S

@[simp] theorem mem_seenFinset {m : Nat} {S : Fin m → Z} {z : Z} :
    z ∈ seenFinset S ↔ ∃ i, S i = z := by
  classical
  simp [seenFinset]

@[simp] theorem mem_unseenFinset {m : Nat} {S : Fin m → Z} {z : Z} :
    z ∈ unseenFinset S ↔ ∀ i, S i ≠ z := by
  classical
  simp [unseenFinset]

theorem seenFinset_card_le {m : Nat} (S : Fin m → Z) :
    (seenFinset S).card ≤ m := by
  calc (seenFinset S).card = (Finset.univ.image S).card := rfl
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
  exact Nat.le_sub_of_add_le (by nlinarith [seenFinset_card_le S])

theorem labels_card_eq_two_mul_away (z : Z) :
    (Fintype.card (Z → Bool) : ℝ) =
      2 * (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) := by
  classical
  have hcard : Fintype.card (Z → Bool) =
      Fintype.card (({x : Z // x ≠ z} → Bool) × Bool) :=
    Fintype.card_congr (splitAt z)
  rw [Fintype.card_prod, Fintype.card_bool] at hcard
  norm_num [hcard, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]

/-- **Fixed-sample lower bound.**
For any sample `S`, the average abstract risk over all labellings is ≥ `|Bool^Z|/4`. -/
theorem sum_abstractRisk_fixed_sample_ge
    (e : Z ↪ X) (A : Learner X) {m : Nat} (S : Fin m → Z)
    (hm : 0 < m) (hcard : Fintype.card Z = 2 * m) :
    (Fintype.card (Z → Bool) : ℝ) / 4 ≤
      ∑ f : Z → Bool, abstractRisk e f (A (abstractSampleList e f S)) := by
  classical
  let L : Z → ℝ := fun z =>
    ∑ f : Z → Bool, zeroOneLoss (A (abstractSampleList e f S)) (e z, f z)
  have hZpos_nat : 0 < Fintype.card Z := by rw [hcard]; nlinarith
  have hZpos : (0 : ℝ) < (Fintype.card Z : ℝ) := by exact_mod_cast hZpos_nat
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hZcardR : (Fintype.card Z : ℝ) = 2 * (m : ℝ) := by rw [hcard]; norm_num [Nat.cast_mul]
  have hsum_rewrite :
      (∑ f : Z → Bool, abstractRisk e f (A (abstractSampleList e f S))) =
        ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * L z := by
    unfold abstractRisk L; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro z _; rw [← Finset.mul_sum]
  have hnonneg_z : ∀ z : Z, 0 ≤ (Fintype.card Z : ℝ)⁻¹ * L z := fun z => by
    apply mul_nonneg
    · exact inv_nonneg.mpr (le_of_lt hZpos)
    · apply Finset.sum_nonneg; intro f _; unfold zeroOneLoss; split <;> norm_num
  have hterm : ∀ z, z ∈ unseenFinset S →
      (Fintype.card Z : ℝ)⁻¹ * L z =
        (Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ)) := by
    intro z hz
    rw [show L z = (Fintype.card ({x : Z // x ≠ z} → Bool) : ℝ) from
      loss_sum_over_labels_at_unseen e A S (mem_unseenFinset.mp hz)]
    rw [labels_card_eq_two_mul_away z]
    field_simp [ne_of_gt hZpos]
  have hunseen_sum_eq :
      (∑ z ∈ (unseenFinset S), (Fintype.card Z : ℝ)⁻¹ * L z) =
        ((unseenFinset S).card : ℝ) *
          ((Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ))) := by
    apply Eq.trans (Finset.sum_congr rfl hterm); simp [nsmul_eq_mul]
  have hconst_nonneg :
      0 ≤ (Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ)) := by positivity
  have hbase :
      (m : ℝ) * ((Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ))) =
        (Fintype.card (Z → Bool) : ℝ) / 4 := by
    rw [hZcardR]; field_simp [ne_of_gt hmposR]; ring
  calc (Fintype.card (Z → Bool) : ℝ) / 4
      = (m : ℝ) * ((Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ))) :=
          hbase.symm
    _ ≤ ((unseenFinset S).card : ℝ) *
          ((Fintype.card (Z → Bool) : ℝ) / (2 * (Fintype.card Z : ℝ))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast unseenFinset_card_ge_half S hcard)
            hconst_nonneg
    _ = ∑ z ∈ (unseenFinset S), (Fintype.card Z : ℝ)⁻¹ * L z := hunseen_sum_eq.symm
    _ ≤ ∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * L z :=
          Finset.sum_le_sum_of_subset_of_nonneg (by intro z hz; simp)
            (by intro z _ _; exact hnonneg_z z)
    _ = ∑ f : Z → Bool, abstractRisk e f (A (abstractSampleList e f S)) := hsum_rewrite.symm

/-- Bad samples for target `f`. -/
noncomputable def abstractBadSamples (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat) : Finset (Fin m → Z) :=
  Finset.univ.filter fun S =>
    (1 : ℝ) / 8 ≤ abstractRisk e f (A (abstractSampleList e f S))

/-- Abstract failure rate. -/
noncomputable def abstractFailureRate (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat) : ℝ :=
  ((abstractBadSamples e A f m).card : ℝ) / (Fintype.card (Fin m → Z) : ℝ)

theorem abstractRisk_le_one_of_card_pos
    (hZpos : 0 < Fintype.card Z) (e : Z ↪ X) (f : Z → Bool)
    (h : X → Bool) :
    abstractRisk e f h ≤ 1 := by
  classical
  have hZposR : (0 : ℝ) < (Fintype.card Z : ℝ) := by exact_mod_cast hZpos
  unfold abstractRisk
  calc (∑ z : Z, (Fintype.card Z : ℝ)⁻¹ * zeroOneLoss h (e z, f z))
      ≤ ∑ _z : Z, (Fintype.card Z : ℝ)⁻¹ * 1 := by
          apply Finset.sum_le_sum; intro z _
          have hloss : zeroOneLoss h (e z, f z) ≤ 1 := by
            unfold zeroOneLoss; split <;> norm_num
          nlinarith [inv_pos.mpr hZposR]
    _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          field_simp [ne_of_gt hZposR]

/-- Piecewise sum formula: `Σ_S (if S ∈ B then 1 else 1/8) = |Ω|/8 + 7/8·|B|`. -/
theorem sum_piecewise_one_eighth {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Finset Ω) :
    (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) =
      (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) := by
  classical
  have hpoint : ∀ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ)) =
      (1 / 8 : ℝ) + if S ∈ B then (7 / 8 : ℝ) else 0 := by
    intro S; by_cases hS : S ∈ B <;> simp [hS] <;> norm_num
  calc (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ)))
      = ∑ S : Ω, ((1 / 8 : ℝ) + if S ∈ B then (7 / 8 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro S _; exact hpoint S
    _ = (Fintype.card Ω : ℝ) / 8 + ∑ S : Ω, (if S ∈ B then (7 / 8 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib]; simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) := by
          congr 1
          calc (∑ S : Ω, (if S ∈ B then (7 / 8 : ℝ) else 0))
              = ∑ S ∈ ((Finset.univ : Finset Ω) ∩ B), (7 / 8 : ℝ) := by
                  rw [Finset.sum_ite_mem]
            _ = (7 / 8 : ℝ) * (B.card : ℝ) := by simp [nsmul_eq_mul, mul_comm]

/-- If failure rate `< 1/7`, then total risk over samples `< |Ω|/4`.
    This uses `(7/8) · (1/7) = 1/8`. -/
theorem sum_abstractRisk_lt_of_failureRate_lt
    (hZpos : 0 < Fintype.card Z) (e : Z ↪ X) (A : Learner X)
    (f : Z → Bool) (m : Nat)
    (hfail : abstractFailureRate e A f m < (1 : ℝ) / 7) :
    (∑ S : Fin m → Z, abstractRisk e f (A (abstractSampleList e f S))) <
      (Fintype.card (Fin m → Z) : ℝ) / 4 := by
  classical
  let Ω := Fin m → Z
  let B : Finset Ω := abstractBadSamples e A f m
  haveI : Nonempty Z := Fintype.card_pos_iff.mp hZpos
  have hΩpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hfail' : (B.card : ℝ) / (Fintype.card Ω : ℝ) < (1 : ℝ) / 7 := by
    simpa [B, Ω, abstractFailureRate] using hfail
  have hbad_lt : (B.card : ℝ) < (Fintype.card Ω : ℝ) / 7 := by
    have := mul_lt_mul_of_pos_right hfail' hΩpos
    field_simp [ne_of_gt hΩpos] at this; nlinarith
  have hpoint : ∀ S : Ω, abstractRisk e f (A (abstractSampleList e f S)) ≤
      if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ) := by
    intro S; by_cases hS : S ∈ B
    · simp [hS, abstractRisk_le_one_of_card_pos hZpos e f]
    · have hnot : ¬ (1 : ℝ) / 8 ≤ abstractRisk e f (A (abstractSampleList e f S)) := by
        simpa [B, abstractBadSamples] using hS
      simpa [hS] using le_of_lt (lt_of_not_ge hnot)
  have hpiece := sum_piecewise_one_eighth B
  have hupper_lt :
      (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ) <
        (Fintype.card Ω : ℝ) / 4 := by
    have hmul : (7 / 8 : ℝ) * (B.card : ℝ) < (7 / 8 : ℝ) * ((Fintype.card Ω : ℝ) / 7) :=
      mul_lt_mul_of_pos_left hbad_lt (by norm_num)
    calc (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * (B.card : ℝ)
        < (Fintype.card Ω : ℝ) / 8 + (7 / 8 : ℝ) * ((Fintype.card Ω : ℝ) / 7) :=
            add_lt_add_of_le_of_lt le_rfl hmul
      _ = (Fintype.card Ω : ℝ) / 4 := by ring
  have hsum_le :
      (∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S))) ≤
        (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) :=
    Finset.sum_le_sum (fun S _ => hpoint S)
  have hsum_piece_lt :
      (∑ S : Ω, (if S ∈ B then (1 : ℝ) else (1 / 8 : ℝ))) <
        (Fintype.card Ω : ℝ) / 4 := by
    rw [hpiece]; exact hupper_lt
  simpa [Ω] using lt_of_le_of_lt hsum_le hsum_piece_lt

/-- **Probabilistic method**: some target achieves abstract failure rate ≥ 1/7. -/
theorem exists_abstractFailureRate_ge
    (e : Z ↪ X) (A : Learner X) {m : Nat}
    (hm : 0 < m) (hcard : Fintype.card Z = 2 * m) :
    ∃ f : Z → Bool, (1 : ℝ) / 7 ≤ abstractFailureRate e A f m := by
  classical
  by_contra hno
  let Ω := Fin m → Z
  let F := Z → Bool
  have hZpos : 0 < Fintype.card Z := by rw [hcard]; nlinarith
  haveI : Nonempty F := ⟨fun _ => false⟩
  have hall_lt : ∀ f : F, abstractFailureRate e A f m < (1 : ℝ) / 7 := fun f =>
    not_le.mp (fun hf => hno ⟨f, hf⟩)
  have hlower_each : ∀ S : Ω,
      (Fintype.card F : ℝ) / 4 ≤
        ∑ f : F, abstractRisk e f (A (abstractSampleList e f S)) :=
    fun S => sum_abstractRisk_fixed_sample_ge e A S hm hcard
  have hlower_sum :
      (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) ≤
        ∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S)) :=
    calc (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4)
        = ∑ _S : Ω, ((Fintype.card F : ℝ) / 4) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ S : Ω, ∑ f : F, abstractRisk e f (A (abstractSampleList e f S)) :=
            Finset.sum_le_sum (fun S _ => hlower_each S)
  have hupper_each : ∀ f : F,
      (∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S))) <
        (Fintype.card Ω : ℝ) / 4 :=
    fun f => sum_abstractRisk_lt_of_failureRate_lt hZpos e A f m (hall_lt f)
  have hupper_sum :
      (∑ f : F, ∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S))) <
        (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) := by
    calc (∑ f : F, ∑ S : Ω, abstractRisk e f (A (abstractSampleList e f S)))
        < ∑ _f : F, ((Fintype.card Ω : ℝ) / 4) :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
              (fun f _ => hupper_each f)
      _ = (Fintype.card Ω : ℝ) * ((Fintype.card F : ℝ) / 4) := by
            simp [Finset.sum_const, nsmul_eq_mul]; ring
  exact not_lt_of_ge hlower_sum
    (Finset.sum_comm (f := fun S f => abstractRisk e f (A (abstractSampleList e f S))) ▸
      hupper_sum)

end FiniteCombinatorics

/-! ## Concrete bridge: support-indexed ↔ measure-theoretic -/

section ConcreteBridge

variable [Fintype X] [MeasurableSingletonClass X]

/-- Support-indexed samples embed injectively into graph-labelled samples. -/
def supportTraceEmbedding (C : Finset X) (f : X → Bool) (m : Nat) :
    (Fin m → {x : X // x ∈ C}) ↪ (Fin m → X × Bool) where
  toFun S := fun i => ((S i).1, f (S i).1)
  inj' := fun S T hST => funext fun i =>
    Subtype.ext (congrArg Prod.fst (congrFun hST i))

theorem supportTrace_list_eq_abstractSampleList
    (C : Finset X) (fX : X → Bool) (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z)
    {m : Nat} (S : Fin m → {x : X // x ∈ C}) :
    List.ofFn (supportTraceEmbedding C fX m S) =
      abstractSampleList (Function.Embedding.subtype (fun x : X => x ∈ C)) fZ S := by
  unfold supportTraceEmbedding abstractSampleList
  rw [List.ofFn_inj]; funext i; simp [hExt (S i)]

theorem supportRisk_eq_abstractRisk_subtype
    (C : Finset X) (fX h : X → Bool) (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z) :
    supportRisk C fX h =
      abstractRisk (Function.Embedding.subtype (fun x : X => x ∈ C)) fZ h := by
  classical
  unfold supportRisk abstractRisk
  rw [show Fintype.card {x : X // x ∈ C} = C.card from
    Fintype.card_ofFinset C (by intro x; rfl)]
  rw [← Finset.sum_attach C (fun x => (C.card : ℝ)⁻¹ * zeroOneLoss h (x, fX x))]
  apply Finset.sum_congr rfl; intro z _; simp [Function.Embedding.subtype, hExt z]

theorem risk_graphPMF_eq_abstractRisk_subtype
    (C : Finset X) (fX h : X → Bool) (hC : C.Nonempty)
    (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z) :
    risk (graphPMF C fX hC).toMeasure h =
      abstractRisk (Function.Embedding.subtype (fun x : X => x ∈ C)) fZ h :=
  (risk_graphPMF_eq_supportRisk C fX h hC).trans
    (supportRisk_eq_abstractRisk_subtype C fX h fZ hExt)

/-- Measure of a single support-indexed sample under the graph product measure. -/
theorem pi_graph_singleton_supportTrace
    (C : Finset X) (f : X → Bool) (hC : C.Nonempty) (m : Nat)
    (S : Fin m → {x : X // x ∈ C}) :
    (Measure.pi (fun _ : Fin m => (graphPMF C f hC).toMeasure))
        {supportTraceEmbedding C f m S} =
      ((C.card : ℝ≥0∞)⁻¹) ^ m := by
  classical
  rw [Measure.pi_singleton]
  calc (∏ i : Fin m, ((graphPMF C f hC).toMeasure) {supportTraceEmbedding C f m S i})
      = ∏ _i : Fin m, ((C.card : ℝ≥0∞)⁻¹) := by
          apply Finset.prod_congr rfl; intro i _
          have hmem : supportTraceEmbedding C f m S i ∈ graphFinset C f := by
            simp [supportTraceEmbedding]
          rw [PMF.toMeasure_apply_singleton _ _
            (MeasurableSingletonClass.measurableSet_singleton _)]
          simp [graphPMF, PMF.uniformOfFinset_apply_of_mem _ hmem, graphFinset_card]
    _ = ((C.card : ℝ≥0∞)⁻¹) ^ m := by simp

/-- Measure of a finset of support-indexed samples under the graph product measure. -/
theorem pi_graph_measure_supportTraceFinset
    (C : Finset X) (f : X → Bool) (hC : C.Nonempty) (m : Nat)
    (B : Finset (Fin m → {x : X // x ∈ C})) :
    (Measure.pi (fun _ : Fin m => (graphPMF C f hC).toMeasure))
        ↑(B.map (supportTraceEmbedding C f m)) =
      (B.card : ℝ≥0∞) * ((C.card : ℝ≥0∞)⁻¹) ^ m := by
  classical
  let μ := Measure.pi (fun _ : Fin m => (graphPMF C f hC).toMeasure)
  calc μ ↑(B.map (supportTraceEmbedding C f m))
      = ∑ T ∈ B.map (supportTraceEmbedding C f m), μ {T} := by
          rw [← MeasureTheory.sum_measure_singleton]
    _ = ∑ T ∈ B.map (supportTraceEmbedding C f m), ((C.card : ℝ≥0∞)⁻¹) ^ m := by
          apply Finset.sum_congr rfl; intro T hT
          rcases Finset.mem_map.mp hT with ⟨S, _, rfl⟩
          exact pi_graph_singleton_supportTrace C f hC m S
    _ = (B.card : ℝ≥0∞) * ((C.card : ℝ≥0∞)⁻¹) ^ m := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_map]

theorem supportTrace_weight_toReal
    (C : Finset X) (m : Nat) (Bcard : Nat) :
    ((Bcard : ℝ≥0∞) * ((C.card : ℝ≥0∞)⁻¹) ^ m).toReal =
      (Bcard : ℝ) / (Fintype.card (Fin m → {x : X // x ∈ C}) : ℝ) := by
  classical
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast]
  rw [Fintype.card_fun, Fintype.card_fin,
      show Fintype.card {x : X // x ∈ C} = C.card from
        Fintype.card_ofFinset C (by intro x; rfl)]
  norm_num [div_eq_mul_inv, Nat.cast_pow]

/-- Abstract failure rate is ≤ actual failure probability under the graph distribution. -/
theorem abstractFailureRate_le_failureProb_graph
    (C : Finset X) (hC : C.Nonempty) (A : Learner X)
    (fX : X → Bool) (fZ : {x : X // x ∈ C} → Bool)
    (hExt : ∀ z : {x : X // x ∈ C}, fX z.1 = fZ z)
    (m : Nat) :
    abstractFailureRate
        (Function.Embedding.subtype (fun x : X => x ∈ C)) A fZ m ≤
      failureProb (graphPMF C fX hC).toMeasure A m (1 / 8) := by
  classical
  let e : {x : X // x ∈ C} ↪ X := Function.Embedding.subtype _
  let B : Finset (Fin m → {x : X // x ∈ C}) := abstractBadSamples e A fZ m
  let μ := Measure.pi (fun _ : Fin m => (graphPMF C fX hC).toMeasure)
  let event : Set (Fin m → X × Bool) :=
    {S | (1 : ℝ) / 8 ≤ risk (graphPMF C fX hC).toMeasure (A (List.ofFn S))}
  have hsubset : ↑(B.map (supportTraceEmbedding C fX m)) ⊆ event := by
    intro T hT
    rcases Finset.mem_map.mp hT with ⟨S, hS, rfl⟩
    have hbad : (1 : ℝ) / 8 ≤ abstractRisk e fZ (A (abstractSampleList e fZ S)) :=
      by simpa [B, abstractBadSamples] using hS
    have hlist : List.ofFn (supportTraceEmbedding C fX m S) = abstractSampleList e fZ S :=
      supportTrace_list_eq_abstractSampleList C fX fZ hExt S
    have hrisk :
        risk (graphPMF C fX hC).toMeasure
            (A (List.ofFn (supportTraceEmbedding C fX m S))) =
          abstractRisk e fZ (A (abstractSampleList e fZ S)) := by
      rw [hlist]
      exact risk_graphPMF_eq_abstractRisk_subtype C fX _ hC fZ hExt
    exact (show (1 : ℝ) / 8 ≤
        risk (graphPMF C fX hC).toMeasure
          (A (List.ofFn (supportTraceEmbedding C fX m S))) from by
      rwa [hrisk])
  have himage_toReal :
      (μ ↑(B.map (supportTraceEmbedding C fX m))).toReal =
        abstractFailureRate e A fZ m := by
    rw [pi_graph_measure_supportTraceFinset C fX hC m B,
        supportTrace_weight_toReal C m B.card]; rfl
  haveI : IsProbabilityMeasure μ := inferInstance
  calc abstractFailureRate e A fZ m
      = (μ ↑(B.map (supportTraceEmbedding C fX m))).toReal := himage_toReal.symm
    _ ≤ (μ event).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ event) (measure_mono hsubset)
    _ = failureProb (graphPMF C fX hC).toMeasure A m (1 / 8) := rfl

end ConcreteBridge

/-! ## Main theorem -/

/-- **Batch stochastic No-Free-Lunch Theorem.**

For any deterministic learner on a nonempty finite domain and any
sample size `m` with `2m ≤ |X|`, there exists a realizable distribution
on labelled examples under which the learner fails with probability ≥ 1/7. -/
theorem batch_stochastic_NFL
    [Fintype X] [Nonempty X] [MeasurableSingletonClass X]
    (A : Learner X) (m : Nat) (hm : 2 * m ≤ Fintype.card X) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧
      (∃ f : X → Bool, risk D f = 0) ∧
      (1 : ℝ) / 7 ≤ failureProb D A m (1 / 8) := by
  cases m with
  | zero => exact batch_stochastic_NFL_zero A
  | succ k =>
      classical
      -- Choose support C of size 2(k+1).
      rcases exists_support_card (X := X) (Nat.succ k) hm with ⟨C, hCcard⟩
      have hCnonempty : C.Nonempty := Finset.card_pos.mp (by rw [hCcard]; nlinarith)
      let Z := {x : X // x ∈ C}
      let e : Z ↪ X := Function.Embedding.subtype _
      have hZcard : Fintype.card Z = 2 * Nat.succ k := by
        change Fintype.card ↥C = 2 * Nat.succ k
        rw [Fintype.card_coe C, hCcard]
      -- Find a hard target on Z.
      rcases exists_abstractFailureRate_ge (X := X) (Z := Z) e A
          (Nat.succ_pos k) hZcard with ⟨fZ, hfailZ⟩
      -- Extend to all of X.
      let fX : X → Bool := fun x => if hx : x ∈ C then fZ ⟨x, hx⟩ else false
      have hExt : ∀ z : Z, fX z.1 = fZ z := fun z => by simp [fX, z.2]
      -- Use the graph distribution.
      let D : Measure (X × Bool) := (graphPMF C fX hCnonempty).toMeasure
      exact ⟨D, inferInstance, ⟨fX, risk_graphPMF_self_zero C fX hCnonempty⟩,
             le_trans hfailZ
               (abstractFailureRate_le_failureProb_graph C hCnonempty A fX fZ hExt
                 (Nat.succ k))⟩

end NFL.ClaudeFull.BatchStochastic
