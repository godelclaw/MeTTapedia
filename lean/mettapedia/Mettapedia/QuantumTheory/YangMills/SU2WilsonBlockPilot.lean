import Mettapedia.QuantumTheory.YangMills.WilsonBlockMajorant
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-!
# The exact `SU(2)`, `b = 2` Wilson-block pilot

This module constructs the finite mechanical object used to test the
coefficient-majorant repair on an evaluated Wilson block.  The block has two
fine edges in each of four directions, hence vertices `Fin 4 → Fin 3`.
Positive links and plaquettes are explicit, as are the boundary/internal split,
the one-edge rooted tree gauge, the seven co-tree fluctuation links, the
normalized `SU(2)` Haar measure, the Wilson action, and its fixed-boundary
internal-link integral.

The topology and normalized measure are proved for the actual matrix group
`Matrix.specialUnitaryGroup (Fin 2) ℂ`; no finite-group replacement or abstract
integration functional is used.  This file deliberately does not assert the
analytic/cumulant estimates required by the one-step RG recursion.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open MeasureTheory Set TopologicalSpace

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2WilsonBlockPilot

/-! ## The compact matrix group and its normalized Haar measure -/

/-- The matrix group used in the pilot is the actual special unitary group of
two-by-two complex matrices. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Matrix adjoint is continuous on the special-unitary subtype, hence so is
the group inverse. -/
instance su2ContinuousInv : ContinuousInv SU2 where
  continuous_inv := by
    change Continuous (fun x : SU2 => star x)
    exact continuous_induced_rng.mpr
      (continuous_star.comp continuous_subtype_val)

instance su2IsTopologicalGroup : IsTopologicalGroup SU2 where

theorem su2_isClosed :
    IsClosed (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [show (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
      (Matrix.unitaryGroup (Fin 2) ℂ : Set _) ∩
        {A | Matrix.det A = 1} by rfl]
  exact isClosed_unitary.inter
    (isClosed_singleton.preimage continuous_id.matrix_det)

theorem su2_isBounded :
    Bornology.IsBounded (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [Metric.isBounded_iff]
  refine ⟨2, ?_⟩
  intro x hx y hy
  calc
    dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
    _ ≤ 2 := by
      have hx' := entrywise_sup_norm_bound_of_unitary
        (Matrix.specialUnitaryGroup_le_unitaryGroup hx)
      have hy' := entrywise_sup_norm_bound_of_unitary
        (Matrix.specialUnitaryGroup_le_unitaryGroup hy)
      linarith

theorem su2_isCompact :
    IsCompact (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨su2_isClosed, su2_isBounded⟩

instance su2CompactSpace : CompactSpace SU2 :=
  isCompact_iff_compactSpace.mp su2_isCompact

instance su2MeasurableSpace : MeasurableSpace SU2 := borel SU2

instance su2BorelSpace : BorelSpace SU2 where
  measurable_eq := rfl

/-- The positive compact used to normalize Haar measure is the whole compact
group. -/
def su2PositiveCompact : PositiveCompacts SU2 :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Normalized Haar measure on the actual matrix group `SU(2)`. -/
def su2Haar : Measure SU2 := Measure.haarMeasure su2PositiveCompact

instance su2HaarIsHaar : su2Haar.IsHaarMeasure := by
  unfold su2Haar
  infer_instance

theorem su2Haar_univ : su2Haar Set.univ = 1 := by
  simpa [su2Haar, su2PositiveCompact] using
    (Measure.haarMeasure_self (K₀ := su2PositiveCompact))

instance su2HaarIsProbability : IsProbabilityMeasure su2Haar where
  measure_univ := su2Haar_univ

instance su2MeasureSpace : MeasureSpace SU2 where
  volume := su2Haar

instance su2VolumeIsProbability : IsProbabilityMeasure (volume : Measure SU2) := by
  change IsProbabilityMeasure su2Haar
  infer_instance

instance su2VolumeIsHaar : (volume : Measure SU2).IsHaarMeasure := by
  change su2Haar.IsHaarMeasure
  infer_instance

/-! ## Exact `b = 2` four-dimensional block geometry -/

abbrev Axis := Fin 4
abbrev BlockCoordinate := Fin 3
abbrev BlockVertex := Axis → BlockCoordinate

/-- A positively oriented fine link.  Its origin coordinate in the selected
direction is `0` or `1`, so its endpoint remains in the `3^4` vertex block. -/
structure BlockLink where
  origin : BlockVertex
  direction : Axis
  canStep : origin direction < 2
deriving DecidableEq, Fintype

/-- Endpoint of a positive block link. -/
def BlockLink.endpoint (e : BlockLink) : BlockVertex :=
  Function.update e.origin e.direction
    ⟨e.origin e.direction + 1, Nat.succ_lt_succ e.canStep⟩

/-- A link lies in the boundary hypersurface exactly when one of the three
coordinates transverse to its direction is `0` or `2`. -/
def BlockLink.IsBoundary (e : BlockLink) : Prop :=
  ∃ a : Axis, a ≠ e.direction ∧
    (e.origin a = (0 : BlockCoordinate) ∨
      e.origin a = (2 : BlockCoordinate))

instance (e : BlockLink) : Decidable e.IsBoundary := by
  unfold BlockLink.IsBoundary
  infer_instance

abbrev BoundaryLink := {e : BlockLink // e.IsBoundary}
abbrev InternalLink := {e : BlockLink // ¬ e.IsBoundary}

/-- A positively oriented elementary plaquette, with ordered directions. -/
structure BlockPlaquette where
  origin : BlockVertex
  first : Axis
  second : Axis
  ordered : first < second
  canStepFirst : origin first < 2
  canStepSecond : origin second < 2
deriving DecidableEq, Fintype

def BlockPlaquette.firstLink (p : BlockPlaquette) : BlockLink :=
  ⟨p.origin, p.first, p.canStepFirst⟩

def BlockPlaquette.secondLink (p : BlockPlaquette) : BlockLink :=
  ⟨p.origin, p.second, p.canStepSecond⟩

def BlockPlaquette.secondAfterFirst (p : BlockPlaquette) : BlockLink :=
  ⟨p.firstLink.endpoint, p.second, by
    have hne : p.second ≠ p.first := p.ordered.ne.symm
    simpa [BlockLink.endpoint, BlockPlaquette.firstLink,
      Function.update, hne] using p.canStepSecond⟩

def BlockPlaquette.firstAfterSecond (p : BlockPlaquette) : BlockLink :=
  ⟨p.secondLink.endpoint, p.first, by
    simpa [BlockLink.endpoint, BlockPlaquette.secondLink,
      Function.update, p.ordered.ne] using p.canStepFirst⟩

@[simp] theorem BlockPlaquette.firstLink_origin (p : BlockPlaquette) :
    p.firstLink.origin = p.origin := rfl

@[simp] theorem BlockPlaquette.secondLink_origin (p : BlockPlaquette) :
    p.secondLink.origin = p.origin := rfl

@[simp] theorem BlockPlaquette.secondAfterFirst_origin (p : BlockPlaquette) :
    p.secondAfterFirst.origin = p.firstLink.endpoint := rfl

@[simp] theorem BlockPlaquette.firstAfterSecond_origin (p : BlockPlaquette) :
    p.firstAfterSecond.origin = p.secondLink.endpoint := rfl

theorem BlockPlaquette.oppositeEndpoint :
    ∀ p : BlockPlaquette,
      p.secondAfterFirst.endpoint = p.firstAfterSecond.endpoint := by
  decide

/-- A plaquette is geometrically on the block boundary when one of its two
transverse coordinates is extremal. -/
def BlockPlaquette.IsBoundary (p : BlockPlaquette) : Prop :=
  ∃ a : Axis, a ≠ p.first ∧ a ≠ p.second ∧
    (p.origin a = (0 : BlockCoordinate) ∨
      p.origin a = (2 : BlockCoordinate))

instance (p : BlockPlaquette) : Decidable p.IsBoundary := by
  unfold BlockPlaquette.IsBoundary
  infer_instance

abbrev BoundaryPlaquette := {p : BlockPlaquette // p.IsBoundary}
abbrev InternalPlaquette := {p : BlockPlaquette // ¬ p.IsBoundary}

theorem blockVertex_count : Fintype.card BlockVertex = 81 := by
  decide

theorem blockLink_count : Fintype.card BlockLink = 216 := by
  decide

theorem internalLink_count : Fintype.card InternalLink = 8 := by
  decide

theorem blockPlaquette_count : Fintype.card BlockPlaquette = 216 := by
  decide

theorem internalPlaquette_count : Fintype.card InternalPlaquette = 24 := by
  decide

/-! ## The one-edge rooted tree gauge -/

/-- The unique interior vertex of the `b = 2` block. -/
def centerVertex : BlockVertex := ![1, 1, 1, 1]

/-- Boundary root adjacent to the center in direction zero. -/
def rootVertex : BlockVertex := ![0, 1, 1, 1]

/-- The selected tree edge joins the fixed boundary root to the unique interior
vertex. -/
def treeBlockLink : BlockLink where
  origin := rootVertex
  direction := 0
  canStep := by decide

theorem treeBlockLink_internal : ¬ treeBlockLink.IsBoundary := by
  decide

def treeLink : InternalLink := ⟨treeBlockLink, treeBlockLink_internal⟩

def internalSpanningTree : Finset InternalLink := {treeLink}

abbrev CoTreeLink := {e : InternalLink // e ∉ internalSpanningTree}

theorem internalSpanningTree_count : internalSpanningTree.card = 1 := by
  simp [internalSpanningTree]

theorem coTreeLink_count : Fintype.card CoTreeLink = 7 := by
  change Fintype.card {e : InternalLink // ¬ e ∈ internalSpanningTree} = 7
  rw [Fintype.card_subtype_compl]
  rw [internalLink_count]
  have htree :
      Fintype.card {e : InternalLink // e ∈ internalSpanningTree} = 1 := by
    rw [Fintype.card_coe, internalSpanningTree_count]
  rw [htree]

theorem treeBlockLink_endpoint : treeBlockLink.endpoint = centerVertex := by
  decide

/-! ## Link fields, gauge action, and plaquette action -/

abbrev BlockLinkField := BlockLink → SU2
abbrev BlockGaugeTransform := BlockVertex → SU2

def gaugeAct (g : BlockGaugeTransform) (U : BlockLinkField) : BlockLinkField :=
  fun e => g e.origin * U e * (g e.endpoint)⁻¹

def plaquetteHolonomy (U : BlockLinkField) (p : BlockPlaquette) : SU2 :=
  U p.firstLink * U p.secondAfterFirst *
    (U p.firstAfterSecond)⁻¹ * (U p.secondLink)⁻¹

theorem plaquetteHolonomy_gaugeAct
    (g : BlockGaugeTransform) (U : BlockLinkField) (p : BlockPlaquette) :
    plaquetteHolonomy (gaugeAct g U) p =
      g p.origin * plaquetteHolonomy U p * (g p.origin)⁻¹ := by
  simp only [plaquetteHolonomy, gaugeAct]
  rw [BlockPlaquette.oppositeEndpoint p]
  simp only [BlockPlaquette.firstLink_origin,
    BlockPlaquette.secondLink_origin,
    BlockPlaquette.secondAfterFirst_origin,
    BlockPlaquette.firstAfterSecond_origin]
  group

/-- The normalized `SU(2)` Wilson plaquette potential. -/
def plaquettePotential (U : BlockLinkField) (p : BlockPlaquette) : ℝ :=
  (specialUnitaryWilsonPotential (Fin 2)) (plaquetteHolonomy U p)

theorem plaquettePotential_gaugeAct
    (g : BlockGaugeTransform) (U : BlockLinkField) (p : BlockPlaquette) :
    plaquettePotential (gaugeAct g U) p = plaquettePotential U p := by
  unfold plaquettePotential
  rw [plaquetteHolonomy_gaugeAct]
  exact (specialUnitaryWilsonPotential (Fin 2)).conjugation_invariant _ _

/-- Genuine Wilson action on all 216 elementary plaquettes of the block. -/
def wilsonAction (β : ℝ) (U : BlockLinkField) : ℝ :=
  β * ∑ p : BlockPlaquette, plaquettePotential U p

theorem wilsonAction_gaugeAct
    (β : ℝ) (g : BlockGaugeTransform) (U : BlockLinkField) :
    wilsonAction β (gaugeAct g U) = wilsonAction β U := by
  unfold wilsonAction
  apply congrArg (β * ·)
  exact Finset.sum_congr rfl fun p _ => plaquettePotential_gaugeAct g U p

/-- Gauge transformation that fixes the boundary and sends the selected tree
link to the identity. -/
def treeGaugeTransform (U : BlockLinkField) : BlockGaugeTransform :=
  fun v => if v = centerVertex then U treeBlockLink else 1

def treeGaugeFix (U : BlockLinkField) : BlockLinkField :=
  gaugeAct (treeGaugeTransform U) U

theorem treeGaugeTransform_root (U : BlockLinkField) :
    treeGaugeTransform U rootVertex = 1 := by
  simp [treeGaugeTransform, rootVertex, centerVertex]

theorem treeGaugeTransform_center (U : BlockLinkField) :
    treeGaugeTransform U centerVertex = U treeBlockLink := by
  simp [treeGaugeTransform]

theorem treeGaugeFix_treeLink (U : BlockLinkField) :
    treeGaugeFix U treeBlockLink = 1 := by
  unfold treeGaugeFix gaugeAct
  rw [show treeBlockLink.origin = rootVertex by rfl,
    treeBlockLink_endpoint, treeGaugeTransform_root,
    treeGaugeTransform_center]
  simp

theorem wilsonAction_treeGaugeFix (β : ℝ) (U : BlockLinkField) :
    wilsonAction β (treeGaugeFix U) = wilsonAction β U :=
  wilsonAction_gaugeAct β (treeGaugeTransform U) U

/-! ## Fixed-boundary internal-link integration -/

abbrev BoundaryField := BoundaryLink → SU2
abbrev InternalField := InternalLink → SU2

def assembleField (V : BoundaryField) (A : InternalField) : BlockLinkField :=
  fun e => if h : e.IsBoundary then V ⟨e, h⟩ else A ⟨e, h⟩

instance internalFieldVolumeIsProbability :
    IsProbabilityMeasure (volume : Measure InternalField) := inferInstance

/-- The exact fixed-boundary block partition function: all eight non-boundary
links are integrated against product normalized `SU(2)` Haar measure.  Tree
gauge may subsequently remove the one gauge-orbit link; this definition keeps
the unmodified invariant integral as the reference object. -/
def blockPartition (β : ℝ) (V : BoundaryField) : ℝ :=
  ∫ A : InternalField,
    Real.exp (-wilsonAction β (assembleField V A)) ∂volume

/-- Effective one-block action before polymer localization. -/
def effectiveBlockAction (β : ℝ) (V : BoundaryField) : ℝ :=
  -Real.log (blockPartition β V)

theorem blockPartition_zero (V : BoundaryField) : blockPartition 0 V = 1 := by
  simp [blockPartition, wilsonAction]

end SU2WilsonBlockPilot
end YangMills
end QuantumTheory
end Mettapedia
