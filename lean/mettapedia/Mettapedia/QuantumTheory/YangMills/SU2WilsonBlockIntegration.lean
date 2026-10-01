import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockPilot
import Mettapedia.QuantumTheory.YangMills.WilsonSeparator
import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

/-!
# Exact integration of the four-dimensional SU(2) Wilson block

The existing matrix-group Wilson block is identified with continuous positive
boundary elimination. The boundary/internal coordinate split preserves the
actual normalized Haar product law. In particular its partition function is
positive and continuous, and its effective action is a continuous logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Elementwise

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration

open SU2WilsonBlockPilot WilsonBlockElimination CompactTransferGap

instance su2SecondCountableTopology : SecondCountableTopology SU2 := by
  have : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.secondCountableTopology_induced SU2
    (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val

/-- The genuine matrix SU(2) Wilson potential as a continuous function. -/
def potential : C(SU2, ℝ) :=
  ⟨specialUnitaryWilsonPotential (Fin 2), by
    change Continuous (fun U : SU2 => 1 - (Matrix.trace U.1).re / Fintype.card (Fin 2))
    exact continuous_const.sub ((Complex.continuous_re.comp
      continuous_subtype_val.matrix_trace).div_const _)⟩

theorem potential_bounds (U : SU2) : 0 ≤ potential U ∧ potential U ≤ 2 := by
  have hentry (i : Fin 2) : |(U.1 i i).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (entry_norm_bound_of_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup U.2) i i)
  have h₀ := abs_le.mp (hentry 0)
  have h₁ := abs_le.mp (hentry 1)
  change 0 ≤ 1 - (Matrix.trace U.1).re / Fintype.card (Fin 2) ∧
    1 - (Matrix.trace U.1).re / Fintype.card (Fin 2) ≤ 2
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, Complex.add_re, Fintype.card_fin, Nat.cast_ofNat]
  constructor <;> linarith

/-! ## Local derivatives of the Wilson plaquette -/

/-- A normalized trace contribution to an action derivative. -/
def traceScore (U : SU2) : ℝ := -(Matrix.trace U.val).re / 2

theorem traceScore_eq_potential_sub_one (U : SU2) : traceScore U = potential U - 1 := by
  change -(Matrix.trace U.val).re / 2 =
    (1 - (Matrix.trace U.val).re / Fintype.card (Fin 2)) - 1
  norm_num
  ring

theorem abs_traceScore_le (U : SU2) : |traceScore U| ≤ 1 := by
  rw [traceScore_eq_potential_sub_one, abs_le]
  have h := potential_bounds U
  constructor <;> linarith

@[fun_prop] theorem continuous_traceScore : Continuous traceScore := by
  unfold traceScore
  exact (Complex.continuous_re.comp continuous_subtype_val.matrix_trace).neg.div_const 2

/-- The central half-turn negates the defining matrix. -/
theorem su2CartanElement_pi_val : (su2CartanElement Real.pi).val = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2CartanElement, su2CartanMatrix]

theorem traceScore_flip (U : SU2) :
    traceScore (su2CartanElement Real.pi * U) = -traceScore U := by
  simp only [traceScore, Submonoid.coe_mul, su2CartanElement_pi_val, neg_mul, one_mul,
    Matrix.trace_neg, Complex.neg_re]
  ring

@[simp] theorem traceScore_one : traceScore (1 : SU2) = -1 := by
  norm_num [traceScore, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]

theorem integral_traceScore_zero : (∫ U : SU2, traceScore U) = 0 := by
  have h := integral_mul_left_eq_self (μ := (volume : Measure SU2)) traceScore (su2CartanElement Real.pi)
  simp only [traceScore_flip, integral_neg] at h
  linarith



/-- Insert one ambient link derivative in the correctly oriented plaquette.
For a reversed link the ambient derivative is its adjoint. -/
def holonomyInsertion (v : Fin 4 → SU2) (i : Fin 4) (u : SU2) : SU2 :=
  match i with
  | 0 => u * v 1 * star (v 2) * star (v 3)
  | 1 => v 0 * u * star (v 2) * star (v 3)
  | 2 => v 0 * v 1 * star u * star (v 3)
  | 3 => v 0 * v 1 * star (v 2) * star u

theorem holonomyInsertion_eq_holonomy_update (v : Fin 4 → SU2) (i : Fin 4) (u : SU2) :
    holonomyInsertion v i u = StrongCouplingCrossing.holonomy (Function.update v i u) := by
  fin_cases i <;> simp [holonomyInsertion, StrongCouplingCrossing.holonomy, Function.update]
  all_goals rfl

/-- The exact Wilson action score for the slots that move along explicit
rotation curves. The other slots have zero ambient derivative. -/
def holonomyScore (v u : Fin 4 → SU2) (moving : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ moving, traceScore (holonomyInsertion v i (u i))

theorem continuous_holonomyInsertion (i : Fin 4) :
    Continuous (fun z : (Fin 4 → SU2) × SU2 ↦ holonomyInsertion z.1 i z.2) := by
  fin_cases i <;> simp only [holonomyInsertion] <;> fun_prop

theorem continuous_holonomyScore (moving : Finset (Fin 4)) :
    Continuous (fun z : (Fin 4 → SU2) × (Fin 4 → SU2) ↦ holonomyScore z.1 z.2 moving) := by
  change Continuous (fun z : (Fin 4 → SU2) × (Fin 4 → SU2) ↦
    ∑ i ∈ moving, traceScore (holonomyInsertion z.1 i (z.2 i)))
  refine continuous_finsetSum moving (fun i _ ↦ ?_)
  have hfst : Continuous (fun z : (Fin 4 → SU2) × (Fin 4 → SU2) ↦ z.1) := continuous_fst
  have hi : Continuous (fun z : (Fin 4 → SU2) × (Fin 4 → SU2) ↦ z.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hpair : Continuous (fun z : (Fin 4 → SU2) × (Fin 4 → SU2) ↦ (z.1, z.2 i)) :=
    hfst.prodMk hi
  have hins : Continuous (fun z : (Fin 4 → SU2) × (Fin 4 → SU2) ↦
      holonomyInsertion z.1 i (z.2 i)) := by
    simpa only [Function.comp_def] using (continuous_holonomyInsertion i).comp hpair
  simpa only [Function.comp_def] using continuous_traceScore.comp hins

theorem abs_holonomyScore_le (v u : Fin 4 → SU2) (moving : Finset (Fin 4)) :
    |holonomyScore v u moving| ≤ moving.card := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (s := moving) (fun i _ ↦ abs_traceScore_le _))

theorem hasDerivAt_holonomy_potential (v u : ℝ → Fin 4 → SU2)
    (moving : Finset (Fin 4)) (t : ℝ)
    (hd : ∀ i, HasDerivAt (fun s ↦ (v s i).val)
      (if i ∈ moving then (u t i).val else 0) t) :
    HasDerivAt (fun s ↦ potential (StrongCouplingCrossing.holonomy (v s)))
      (holonomyScore (v t) (u t) moving) t := by
  classical
  have h01 := hasDerivAt_matrix_mul (hd 0) (hd 1)
  have h012 := hasDerivAt_matrix_mul h01 (hd 2).star
  have h0123 := hasDerivAt_matrix_mul h012 (hd 3).star
  have hmat : HasDerivAt (fun s ↦ (StrongCouplingCrossing.holonomy (v s)).val)
      (∑ i ∈ moving, (holonomyInsertion (v t) i (u t i)).val) t := by
    apply h0123.congr_deriv
    rw [show (∑ i ∈ moving, (holonomyInsertion (v t) i (u t i)).val) =
      ∑ i : Fin 4, if i ∈ moving then (holonomyInsertion (v t) i (u t i)).val else 0 by
        simpa using (Finset.sum_ite_mem (Finset.univ : Finset (Fin 4)) moving
          (fun i : Fin 4 ↦ (holonomyInsertion (v t) i (u t i)).val)).symm]
    simp only [Fin.sum_univ_four]
    by_cases h0 : (0 : Fin 4) ∈ moving <;>
      by_cases h1 : (1 : Fin 4) ∈ moving <;>
      by_cases h2 : (2 : Fin 4) ∈ moving <;>
      by_cases h3 : (3 : Fin 4) ∈ moving <;>
      simp only [h0, h1, h2, h3, ↓reduceIte, holonomyInsertion, Submonoid.coe_mul,
        Matrix.specialUnitaryGroup.coe_star, mul_add, add_mul, zero_mul, mul_zero,
        add_zero, zero_add, star_zero]
  have htrace : HasDerivAt
      (fun s ↦ Matrix.trace (StrongCouplingCrossing.holonomy (v s)).val)
      (Matrix.trace (∑ i ∈ moving, (holonomyInsertion (v t) i (u t i)).val)) t := by
    exact HasDerivAt.fun_sum (fun i _ ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp hmat i) i)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t htrace
  have h := (hasDerivAt_const t (1 : ℝ)).sub (hre.div_const 2)
  apply h.congr_deriv
  simp only [holonomyScore, traceScore, zero_sub, Matrix.trace_sum, Complex.reCLM_apply,
    Complex.re_sum, Finset.sum_neg_distrib, Finset.sum_div, neg_div]

/-- Differentiate one inserted score, retaining changes to both the ordinary
plaquette links and the inserted derivative. The latter is the contact term
when two boundary patches meet the same plaquette. -/
theorem hasDerivAt_traceScore_insertion (v u dv du : ℝ → Fin 4 → SU2)
    (moving : Finset (Fin 4)) (i : Fin 4) (t : ℝ)
    (hdv : ∀ j, HasDerivAt (fun s ↦ (v s j).val)
      (if j ∈ moving then (dv t j).val else 0) t)
    (hdu : HasDerivAt (fun s ↦ (u s i).val)
      (if i ∈ moving then (du t i).val else 0) t) :
    HasDerivAt (fun s ↦ traceScore (holonomyInsertion (v s) i (u s i)))
      (holonomyScore (Function.update (v t) i (u t i))
        (Function.update (dv t) i (du t i)) moving) t := by
  have hd : ∀ j, HasDerivAt (fun s ↦ ((Function.update (v s) i (u s i)) j).val)
      (if j ∈ moving then ((Function.update (dv t) i (du t i)) j).val else 0) t := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hdu
    · simpa only [Function.update_of_ne hji] using hdv j
  have h := (hasDerivAt_holonomy_potential
    (fun s ↦ Function.update (v s) i (u s i))
    (fun s ↦ Function.update (dv s) i (du s i)) moving t hd).fun_sub
      (hasDerivAt_const t (1 : ℝ))
  simpa only [traceScore_eq_potential_sub_one, holonomyInsertion_eq_holonomy_update, sub_zero] using h

/-- The mixed action derivative on one plaquette. The inserted first
derivative also changes when the two rotations act on the same slot. -/
def holonomyContact (v u dv du : Fin 4 → SU2) (S T : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ S, holonomyScore (Function.update v i (u i))
    (Function.update dv i (du i)) T

theorem continuous_holonomyContact (S T : Finset (Fin 4)) :
    Continuous (fun z : ((Fin 4 → SU2) × (Fin 4 → SU2)) ×
      ((Fin 4 → SU2) × (Fin 4 → SU2)) ↦
        holonomyContact z.1.1 z.1.2 z.2.1 z.2.2 S T) := by
  apply continuous_finsetSum
  intro i _
  have hv : Continuous (fun z : ((Fin 4 → SU2) × (Fin 4 → SU2)) ×
      ((Fin 4 → SU2) × (Fin 4 → SU2)) ↦ Function.update z.1.1 i (z.1.2 i)) := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne h]
      fun_prop
  have hd : Continuous (fun z : ((Fin 4 → SU2) × (Fin 4 → SU2)) ×
      ((Fin 4 → SU2) × (Fin 4 → SU2)) ↦ Function.update z.2.1 i (z.2.2 i)) := by
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne h]
      fun_prop
  simpa only [Function.comp_def] using (continuous_holonomyScore T).comp (hv.prodMk hd)

theorem abs_holonomyContact_le (v u dv du : Fin 4 → SU2) (S T : Finset (Fin 4)) :
    |holonomyContact v u dv du S T| ≤ (S.card : ℝ) * T.card := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (s := S) (fun i _ ↦ abs_holonomyScore_le _ _ T))

@[simp] theorem holonomyContact_empty (v u dv du : Fin 4 → SU2) (S : Finset (Fin 4)) :
    holonomyContact v u dv du S ∅ = 0 := by
  simp [holonomyContact, holonomyScore]

theorem hasDerivAt_holonomyScore (v u dv du : ℝ → Fin 4 → SU2)
    (S T : Finset (Fin 4)) (t : ℝ)
    (hdv : ∀ j, HasDerivAt (fun s ↦ (v s j).val)
      (if j ∈ T then (dv t j).val else 0) t)
    (hdu : ∀ i ∈ S, HasDerivAt (fun s ↦ (u s i).val)
      (if i ∈ T then (du t i).val else 0) t) :
    HasDerivAt (fun s ↦ holonomyScore (v s) (u s) S)
      (holonomyContact (v t) (u t) (dv t) (du t) S T) t := by
  exact HasDerivAt.fun_sum (fun i hi ↦
    hasDerivAt_traceScore_insertion v u dv du T i t hdv (hdu i hi))

/-- The ordered third action contact. The four new slot fields are the
derivatives of the four fields in `holonomyContact`; coincident slots retain
the order of the inserted group factors. -/
def holonomyThirdContact (v a b c dv da db dc : Fin 4 → SU2)
    (S T V : Finset (Fin 4)) : ℝ :=
  ∑ i ∈ S, holonomyContact (Function.update v i (a i))
    (Function.update b i (c i)) (Function.update dv i (da i))
    (Function.update db i (dc i)) T V

theorem continuous_holonomyThirdContact {Y : Type*} [TopologicalSpace Y]
    (v a b c dv da db dc : Y → Fin 4 → SU2) (S T V : Finset (Fin 4))
    (hv : Continuous v) (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hdv : Continuous dv) (hda : Continuous da) (hdb : Continuous db) (hdc : Continuous dc) :
    Continuous (fun y ↦ holonomyThirdContact (v y) (a y) (b y) (c y)
      (dv y) (da y) (db y) (dc y) S T V) := by
  unfold holonomyThirdContact
  apply continuous_finsetSum
  intro i _
  simpa only [Function.comp_def] using (continuous_holonomyContact T V).comp
    (((hv.update i ((continuous_apply i).comp ha)).prodMk
      (hb.update i ((continuous_apply i).comp hc))).prodMk
      ((hdv.update i ((continuous_apply i).comp hda)).prodMk
        (hdb.update i ((continuous_apply i).comp hdc))))

theorem abs_holonomyThirdContact_le (v a b c dv da db dc : Fin 4 → SU2)
    (S T V : Finset (Fin 4)) :
    |holonomyThirdContact v a b c dv da db dc S T V| ≤
      (S.card : ℝ) * T.card * V.card := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using
    Finset.sum_le_sum (s := S) (fun i _ ↦ abs_holonomyContact_le _ _ _ _ T V)

/-- Differentiate the complete ordered second contact, including changes to
both inserted derivatives when patches act on the same link. -/
theorem hasDerivAt_holonomyContact (v a b c dv da db dc : ℝ → Fin 4 → SU2)
    (S T V : Finset (Fin 4)) (t : ℝ)
    (hv : ∀ j, HasDerivAt (fun s ↦ (v s j).val)
      (if j ∈ V then (dv t j).val else 0) t)
    (ha : ∀ i ∈ S, HasDerivAt (fun s ↦ (a s i).val)
      (if i ∈ V then (da t i).val else 0) t)
    (hb : ∀ j ∈ T, HasDerivAt (fun s ↦ (b s j).val)
      (if j ∈ V then (db t j).val else 0) t)
    (hc : ∀ i ∈ S, HasDerivAt (fun s ↦ (c s i).val)
      (if i ∈ V then (dc t i).val else 0) t) :
    HasDerivAt (fun s ↦ holonomyContact (v s) (a s) (b s) (c s) S T)
      (holonomyThirdContact (v t) (a t) (b t) (c t)
        (dv t) (da t) (db t) (dc t) S T V) t := by
  apply HasDerivAt.fun_sum
  intro i hi
  apply hasDerivAt_holonomyScore
  · intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using ha i hi
    · simpa only [Function.update_of_ne hji] using hv j
  · intro j hj
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hc i hi
    · simpa only [Function.update_of_ne hji] using hb j hj

theorem continuous_plaquetteHolonomy (p : BlockPlaquette) :
    Continuous (fun U : BlockLinkField => plaquetteHolonomy U p) := by
  unfold plaquetteHolonomy
  fun_prop

theorem continuous_plaquettePotential (p : BlockPlaquette) :
    Continuous (fun U : BlockLinkField => plaquettePotential U p) :=
  potential.continuous.comp (continuous_plaquetteHolonomy p)

theorem continuous_wilsonAction (β : ℝ) : Continuous (wilsonAction β) := by
  unfold wilsonAction
  exact continuous_const.mul (continuous_finsetSum _ (fun p _ => continuous_plaquettePotential p))

theorem continuous_assembleField :
    Continuous (fun p : BoundaryField × InternalField => assembleField p.1 p.2) := by
  apply continuous_pi
  intro e
  by_cases he : e.IsBoundary <;> simp only [assembleField, he, ↓reduceDIte] <;> fun_prop

/-- Wilson density on all 216 links, before any elimination. -/
def fullDensity (β : ℝ) : C(BlockLinkField, ℝ) :=
  ⟨fun U => Real.exp (-wilsonAction β U), (continuous_wilsonAction β).neg.rexp⟩

theorem fullDensity_pos (β : ℝ) (U : BlockLinkField) : 0 < fullDensity β U := Real.exp_pos _

/-- The same density in the boundary/internal coordinates of the pilot. -/
def density (β : ℝ) : C(BoundaryField × InternalField, ℝ) :=
  ⟨fun p => fullDensity β (assembleField p.1 p.2),
    (fullDensity β).continuous.comp continuous_assembleField⟩

theorem density_pos (β : ℝ) (p : BoundaryField × InternalField) : 0 < density β p :=
  fullDensity_pos β _

/-- Splitting the actual link variables into the two complementary subtypes
preserves their product Haar measure. -/
theorem measurePreserving_assembleField :
    MeasurePreserving (fun p : BoundaryField × InternalField => assembleField p.1 p.2)
      (volume.prod volume) (volume : Measure BlockLinkField) := by
  exact (volume_preserving_piEquivPiSubtypeProd (fun _ : BlockLink => SU2)
    BlockLink.IsBoundary).symm

theorem integral_assembleField (F : BlockLinkField → ℝ) :
    (∫ p : BoundaryField × InternalField, F (assembleField p.1 p.2) ∂volume.prod volume) =
      ∫ U : BlockLinkField, F U :=
  (volume_preserving_piEquivPiSubtypeProd (fun _ : BlockLink => SU2)
    BlockLink.IsBoundary).symm.integral_comp' F

/-- The previously defined fixed-boundary partition function is exactly the
continuous boundary weight; it is not a new or approximate partition function. -/
theorem blockPartition_eq_marginal (β : ℝ) (V : BoundaryField) :
    blockPartition β V = marginal (volume : Measure InternalField) (density β) V := rfl

theorem blockPartition_pos (β : ℝ) (V : BoundaryField) : 0 < blockPartition β V :=
  marginal_pos volume (density β) (density_pos β) V

theorem continuous_blockPartition (β : ℝ) : Continuous (blockPartition β) :=
  (marginal (volume : Measure InternalField) (density β)).continuous

theorem continuous_effectiveBlockAction (β : ℝ) : Continuous (effectiveBlockAction β) :=
  ((continuous_blockPartition β).log (fun V => (blockPartition_pos β V).ne')).neg

/-- A continuous full-field observable in the split coordinates. -/
def splitObservable (F : C(BlockLinkField, ℝ)) : C(BoundaryField × InternalField, ℝ) :=
  ⟨fun p => F (assembleField p.1 p.2), F.continuous.comp continuous_assembleField⟩

theorem expectation_split (β : ℝ) (F : C(BlockLinkField, ℝ)) :
    expectation (volume.prod volume) (density β) (splitObservable F) =
      expectation (volume : Measure BlockLinkField) (fullDensity β) F := by
  unfold expectation
  change (∫ p, (fullDensity β * F) (assembleField p.1 p.2) ∂volume.prod volume) /
    (∫ p, fullDensity β (assembleField p.1 p.2) ∂volume.prod volume) = _
  rw [integral_assembleField, integral_assembleField]
  rfl

/-- Exact one-marked transport from the original SU(2) Wilson integral. -/
theorem expectation_project (β : ℝ) (F : C(BlockLinkField, ℝ)) :
    expectation (volume : Measure BoundaryField) (marginal volume (density β))
      (project volume (density β) (density_pos β) (splitObservable F)) =
      expectation (volume : Measure BlockLinkField) (fullDensity β) F := by
  rw [WilsonBlockElimination.expectation_project, expectation_split]

/-- Exact two-marked transport on the actual SU(2) block, including the full
conditional-covariance remainder. -/
theorem covariance_transport (β : ℝ) (F G : C(BlockLinkField, ℝ)) :
    covariance (volume : Measure BlockLinkField) (fullDensity β) F G =
      covariance (volume : Measure BoundaryField) (marginal volume (density β))
        (project volume (density β) (density_pos β) (splitObservable F))
        (project volume (density β) (density_pos β) (splitObservable G)) +
      expectation (volume : Measure BoundaryField) (marginal volume (density β))
        (fiberCovariance volume (density β) (density_pos β) (splitObservable F) (splitObservable G)) := by
  have h := covariance_decomposition volume volume (density β) (density_pos β)
    (splitObservable F) (splitObservable G)
  have hmul : splitObservable F * splitObservable G = splitObservable (F * G) := rfl
  simpa only [covariance, hmul, expectation_split] using h

/-- An explicit local gauge-invariant Wilson observable. -/
def plaquetteObservable (p : BlockPlaquette) : C(BlockLinkField, ℝ) :=
  ⟨fun U => plaquettePotential U p, continuous_plaquettePotential p⟩

theorem plaquetteObservable_gaugeAct (p : BlockPlaquette) (g : BlockGaugeTransform)
    (U : BlockLinkField) : plaquetteObservable p (gaugeAct g U) = plaquetteObservable p U :=
  plaquettePotential_gaugeAct g U p

#print axioms potential_bounds
#print axioms abs_holonomyScore_le
#print axioms hasDerivAt_holonomy_potential
#print axioms hasDerivAt_traceScore_insertion
#print axioms hasDerivAt_holonomyScore
#print axioms measurePreserving_assembleField
#print axioms blockPartition_pos
#print axioms continuous_effectiveBlockAction
#print axioms expectation_project
#print axioms covariance_transport

end Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration
