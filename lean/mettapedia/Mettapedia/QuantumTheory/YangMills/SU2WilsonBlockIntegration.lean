import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockPilot
import Mettapedia.QuantumTheory.YangMills.WilsonSeparator

/-!
# Exact integration of the four-dimensional SU(2) Wilson block

The existing matrix-group Wilson block is identified with continuous positive
boundary elimination. The boundary/internal coordinate split preserves the
actual normalized Haar product law. In particular its partition function is
positive and continuous, and its effective action is a continuous logarithm.
-/

set_option autoImplicit false
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
#print axioms measurePreserving_assembleField
#print axioms blockPartition_pos
#print axioms continuous_effectiveBlockAction
#print axioms expectation_project
#print axioms covariance_transport

end Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration
