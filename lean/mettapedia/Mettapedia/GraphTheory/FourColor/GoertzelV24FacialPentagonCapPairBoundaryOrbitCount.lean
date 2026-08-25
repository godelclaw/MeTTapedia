import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairOpenHoleOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount

/-!
# The two boundary-face cycles of the literal two-cap opening

The opened face census splits into faces meeting a fresh boundary stub and
faces avoiding all stubs.  This file proves the first count for the literal
facial-cap pair: the retained first-return permutation on its ten boundary
darts has exactly two cycles, the inner and outer five-port families.

This is a C-3 face-count ingredient.  It consumes the explicit C-4
`RemoteBoundaryFacesSeparated` premise and does not count stub-free opened
faces or assert the Euler equation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairBoundaryOrbitCount

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24FacialPentagonCapPairOpenHoleOrbit
open GoertzelV24FacialPentagonCapPairOpenHoleOrbit.FacialPentagonCapBoundaryWalkPair
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OpenRegionRotation
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

private abbrev keep (caps : FacialPentagonCapBoundaryWalkPair data) : V → Prop :=
  deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport

private abbrev successor (caps : FacialPentagonCapBoundaryWalkPair data) :=
  retainedRegionBoundarySuccessor data.toRotationSystem (keep caps)

private abbrev BoundaryOrbit (caps : FacialPentagonCapBoundaryWalkPair data) :=
  Quotient (Equiv.Perm.SameCycle.setoid (successor caps))

/-- Every literal retained boundary dart is one of the ten source coordinates,
now as equality in the actual boundary-dart subtype. -/
theorem boundary_eq_inner_or_outer
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (boundary : BoundaryDart data.toRotationSystem (keep caps)) :
    (∃ step : Fin 5, boundary = innerRetainedBoundary caps step) ∨
      ∃ step : Fin 5, boundary = outerRetainedBoundary caps step := by
  rcases OrientedFacialPentagonCapPair.boundaryDart_eq_inner_or_outer
      caps.toOrientedFacialPentagonCapPair boundary with
    ⟨step, hstep⟩ | ⟨step, hstep⟩
  · left
    refine ⟨step, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hstep.trans (by rfl)
  · right
    refine ⟨step, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hstep.trans (by rfl)

private def IsInnerOrbit
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (orbit : BoundaryOrbit caps) : Prop :=
  ∃ step : Fin 5, Quotient.mk _ (innerRetainedBoundary caps step) = orbit

private theorem innerOrbit_subsingleton
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    Subsingleton {orbit : BoundaryOrbit caps // IsInnerOrbit caps orbit} := by
  constructor
  intro left right
  rcases left.2 with ⟨leftStep, hleft⟩
  rcases right.2 with ⟨rightStep, hright⟩
  apply Subtype.ext
  change left.1 = right.1
  rw [← hleft, ← hright]
  apply Quotient.sound
  exact retainedBoundarySuccessor_inner_sameCycle caps minimal hremote hcubic
    hrotation leftStep rightStep

private theorem innerOrbit_nonempty
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    Nonempty {orbit : BoundaryOrbit caps // IsInnerOrbit caps orbit} :=
  ⟨⟨Quotient.mk _ (innerRetainedBoundary caps 0), 0, rfl⟩⟩

private theorem outerOrbit_not_inner
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    ¬ IsInnerOrbit caps (Quotient.mk _ (outerRetainedBoundary caps 0)) := by
  rintro ⟨step, hstep⟩
  have hsame : (successor caps).SameCycle
      (innerRetainedBoundary caps step) (outerRetainedBoundary caps 0) :=
    Quotient.exact hstep
  have hinner := retainedBoundarySuccessor_inner_sameCycle caps minimal hremote
    hcubic hrotation 0 step
  exact retainedBoundarySuccessor_inner_outer_not_sameCycle
    caps minimal hremote (hinner.trans hsame)

private theorem nonInnerOrbit_subsingleton
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    Subsingleton {orbit : BoundaryOrbit caps // ¬ IsInnerOrbit caps orbit} := by
  constructor
  rintro ⟨left, hleftNotInner⟩ ⟨right, hrightNotInner⟩
  apply Subtype.ext
  suffices hleft : left = Quotient.mk _ (outerRetainedBoundary caps 0) from
    hleft.trans (by
      suffices hright : right = Quotient.mk _ (outerRetainedBoundary caps 0) from
        hright.symm
      induction right using Quotient.inductionOn with
      | _ boundary =>
          rcases boundary_eq_inner_or_outer caps boundary with
            ⟨step, rfl⟩ | ⟨step, rfl⟩
          · exact False.elim (hrightNotInner ⟨step, rfl⟩)
          · apply Quotient.sound
            exact retainedBoundarySuccessor_outer_sameCycle caps minimal hremote
              hcubic hrotation step 0)
  induction left using Quotient.inductionOn with
  | _ boundary =>
      rcases boundary_eq_inner_or_outer caps boundary with
        ⟨step, rfl⟩ | ⟨step, rfl⟩
      · exact False.elim (hleftNotInner ⟨step, rfl⟩)
      · apply Quotient.sound
        exact retainedBoundarySuccessor_outer_sameCycle caps minimal hremote
          hcubic hrotation step 0

private theorem nonInnerOrbit_nonempty
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    Nonempty {orbit : BoundaryOrbit caps // ¬ IsInnerOrbit caps orbit} :=
  ⟨⟨Quotient.mk _ (outerRetainedBoundary caps 0),
    outerOrbit_not_inner caps minimal hremote hcubic hrotation⟩⟩

/-- The retained first-return permutation of the literal two-cap cut has
exactly the two computed cap-boundary cycles. -/
theorem card_boundaryOrbit_eq_two
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    Fintype.card (BoundaryOrbit caps) = 2 := by
  classical
  let innerType := {orbit : BoundaryOrbit caps // IsInnerOrbit caps orbit}
  let outerType := {orbit : BoundaryOrbit caps // ¬ IsInnerOrbit caps orbit}
  have hinnerCard : Fintype.card innerType = 1 := by
    let witness : innerType := Classical.choice (innerOrbit_nonempty caps)
    exact Fintype.card_eq_one_iff.mpr
      ⟨witness, fun other =>
        @Subsingleton.elim innerType
          (innerOrbit_subsingleton caps minimal hremote hcubic hrotation)
          other witness⟩
  have houterCard : Fintype.card outerType = 1 := by
    let witness : outerType := Classical.choice
      (nonInnerOrbit_nonempty caps minimal hremote hcubic hrotation)
    exact Fintype.card_eq_one_iff.mpr
      ⟨witness, fun other =>
        @Subsingleton.elim outerType
          (nonInnerOrbit_subsingleton caps minimal hremote hcubic hrotation)
          other witness⟩
  calc
    Fintype.card (BoundaryOrbit caps) =
      Fintype.card (innerType ⊕ outerType) :=
      Fintype.card_congr (Equiv.sumCompl (IsInnerOrbit caps)).symm
    _ = Fintype.card innerType + Fintype.card outerType := Fintype.card_sum
    _ = 2 := by rw [hinnerCard, houterCard]

/-- Equivalently, the boundary successor permutation has two partition
parts. -/
theorem card_boundarySuccessor_partition_eq_two
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem) :
    (successor caps).partition.parts.card = 2 := by
  rw [← card_permOrbit_eq_card_partition_parts]
  exact card_boundaryOrbit_eq_two caps minimal hremote hcubic hrotation

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairBoundaryOrbitCount

end Mettapedia.GraphTheory.FourColor
