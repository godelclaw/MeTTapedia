import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSlitRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalPair

/-!
# L1: open a selected pair of dual transversals

The source-facing transversal carrier records the actual primal edge crossed
at each dual step and therefore does not require global uniqueness of shared
face-boundary edges.  This file makes that representation operational: the
union of the two selected crossing supports is opened as a literal slit
rotation system, and every selected crossing is proved to reach its own fresh
boundary stub.

This is the selected-edge counterpart of the older
`AlignedSimpleDualCrosscuts.slitRotationSystem`.  It is a genuine construction
of the opened carrier, not a conversion back to the stronger globally unique
representation.  It does not construct the long end-capped pair required to
close L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24FaceOrbitIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SeparatedAlignedSelectedDualTransversals

/-- Membership in the simultaneous selected slit is membership in one of its
two literal crossing supports. -/
@[simp] theorem mem_crossingSupport_iff
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (edge : G.edgeSet) :
    edge ∈ pair.crossingSupport ↔
      edge ∈ pair.left.crossingEdges ∨ edge ∈ pair.right.crossingEdges :=
  Finset.mem_union

/-- The left selected interface is retained in the simultaneous slit support. -/
theorem left_crossingEdges_subset_support
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish) :
    pair.left.crossingEdges ⊆ pair.crossingSupport :=
  Finset.subset_union_left

/-- The right selected interface is retained in the simultaneous slit support. -/
theorem right_crossingEdges_subset_support
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish) :
    pair.right.crossingEdges ⊆ pair.crossingSupport :=
  Finset.subset_union_right

/-- Simultaneously open the two actual selected source transversals.  The
carrier is computed directly from their selected primal crossing edges. -/
noncomputable def slitRotationSystem
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish) :
    RotationSystem
      (SlitVertex RS pair.crossingSupport)
      (slitRewiredDartSystem RS pair.crossingSupport).Edge :=
  GoertzelV24AnnularCrosscutSlitRotation.slitRotationSystem RS
    pair.crossingSupport

/-- Every selected left-interface crossing becomes its own exposed boundary
stub in the simultaneous slit. -/
theorem left_crossing_opens
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (step : Fin pair.left.crosscut.walk.length) (dart : RS.D)
    (hcrossing : RS.edgeOf dart = pair.left.crossingEdge step) :
    pair.slitRotationSystem.alpha (Sum.inl dart) =
      Sum.inr ⟨dart, pair.left_crossingEdges_subset_support
        ((pair.left.mem_crossingEdges_iff _).2 ⟨step, hcrossing.symm⟩)⟩ := by
  exact slitRotationSystem_alpha_old_of_mem RS pair.crossingSupport
    (pair.left_crossingEdges_subset_support
      ((pair.left.mem_crossingEdges_iff _).2 ⟨step, hcrossing.symm⟩))

/-- Every selected right-interface crossing becomes its own exposed boundary
stub in the simultaneous slit. -/
theorem right_crossing_opens
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (step : Fin pair.right.crosscut.walk.length) (dart : RS.D)
    (hcrossing : RS.edgeOf dart = pair.right.crossingEdge step) :
    pair.slitRotationSystem.alpha (Sum.inl dart) =
      Sum.inr ⟨dart, pair.right_crossingEdges_subset_support
        ((pair.right.mem_crossingEdges_iff _).2 ⟨step, hcrossing.symm⟩)⟩ := by
  exact slitRotationSystem_alpha_old_of_mem RS pair.crossingSupport
    (pair.right_crossingEdges_subset_support
      ((pair.right.mem_crossingEdges_iff _).2 ⟨step, hcrossing.symm⟩))

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
