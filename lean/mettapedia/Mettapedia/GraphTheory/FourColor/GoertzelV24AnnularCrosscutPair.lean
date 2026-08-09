import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSlitRotation

/-!
# Two aligned annular crosscuts

The source splice removes the corridor between two equal-profile transverse
interfaces.  A single transversal is an open slit; this file packages two
equal-width, edge-disjoint slits and opens both at once.  The result is the
concrete boundary geometry from which a corridor piece and its eventual
identity replacement are constructed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24FaceOrbitIncidence

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Two source-level simple transversals with the common finite interface
width required to compare profiles.  Their edge-disjointness is geometric:
the two slits do not reuse a primal edge. -/
structure AlignedSimpleDualCrosscuts
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (start finish : AmbientFace allFaces)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces) where
  left : SimpleDualCrosscut faceBoundary allFaces start finish
  right : SimpleDualCrosscut faceBoundary allFaces start finish
  length_eq : left.walk.length = right.walk.length
  crossing_disjoint : Disjoint (left.crossingEdges hunique)
    (right.crossingEdges hunique)

namespace AlignedSimpleDualCrosscuts

/-- All primal edges opened by the pair of transverse interfaces. -/
def crossingSupport
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique) :
    Finset E :=
  pair.left.crossingEdges hunique ∪ pair.right.crossingEdges hunique

@[simp]
theorem mem_crossingSupport_iff
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique)
    (edge : E) :
    edge ∈ pair.crossingSupport ↔
      edge ∈ pair.left.crossingEdges hunique ∨
        edge ∈ pair.right.crossingEdges hunique :=
  Finset.mem_union

/-- The left interface is retained as a subset of the simultaneous slit. -/
theorem left_crossingEdges_subset_support
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique) :
    pair.left.crossingEdges hunique ⊆ pair.crossingSupport :=
  Finset.subset_union_left

/-- The right interface is retained as a subset of the simultaneous slit. -/
theorem right_crossingEdges_subset_support
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique) :
    pair.right.crossingEdges hunique ⊆ pair.crossingSupport :=
  Finset.subset_union_right

/-- Equal profile coordinates are compared by this canonical reindexing of
the right-hand interface. -/
def rightPosition
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique)
    (step : Fin pair.left.walk.length) : Fin pair.right.walk.length :=
  Fin.cast pair.length_eq step

@[simp]
theorem rightPosition_val
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique)
    (step : Fin pair.left.walk.length) :
    (pair.rightPosition step).val = step.val :=
  rfl

/-- The two simple interfaces together have exactly the sum of their widths.
No port multiplicity is hidden in this calculation. -/
theorem card_crossingSupport
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique) :
    pair.crossingSupport.card = pair.left.walk.length + pair.right.walk.length := by
  rw [crossingSupport, Finset.card_union_of_disjoint pair.crossing_disjoint,
    pair.left.card_crossingEdges_eq_length hall hunique,
    pair.right.card_crossingEdges_eq_length hall hunique]

/-- With aligned widths, the simultaneous slit has exactly twice the single
crosscut support size. -/
theorem card_crossingSupport_eq_twice_left_length
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    {hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (pair : AlignedSimpleDualCrosscuts faceBoundary allFaces start finish hunique) :
    pair.crossingSupport.card = 2 * pair.left.walk.length := by
  rw [pair.card_crossingSupport hall, pair.length_eq]
  omega

end AlignedSimpleDualCrosscuts

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace AlignedSimpleDualCrosscuts

/-- Simultaneously open both actual source transversals in the ambient
rotation system.  This is a concrete open-boundary map; it does not assume a
vertex side or a pre-existing deleted component. -/
noncomputable def slitRotationSystem
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique) :
    RotationSystem
      (SlitVertex RS pair.crossingSupport)
      (slitRewiredDartSystem RS pair.crossingSupport).Edge :=
  GoertzelV24AnnularCrosscutSlitRotation.slitRotationSystem RS
    pair.crossingSupport

/-- Every left-interface crossing becomes an actual exposed stub in the
simultaneous slit. -/
theorem left_crossing_opens
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (step : Fin pair.left.walk.length) (dart : RS.D)
    (hcrossing : RS.edgeOf dart = pair.left.crossingEdge hunique step) :
    (pair.slitRotationSystem).alpha (Sum.inl dart) =
      Sum.inr ⟨dart, (pair.left_crossingEdges_subset_support
        ((pair.left.mem_crossingEdges_iff hunique _).2
          ⟨step, hcrossing.symm⟩))⟩ := by
  exact slitRotationSystem_alpha_old_of_mem RS pair.crossingSupport
    (pair.left_crossingEdges_subset_support
      ((pair.left.mem_crossingEdges_iff hunique _).2
        ⟨step, hcrossing.symm⟩))

/-- Every right-interface crossing becomes an actual exposed stub in the
simultaneous slit. -/
theorem right_crossing_opens
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (step : Fin pair.right.walk.length) (dart : RS.D)
    (hcrossing : RS.edgeOf dart = pair.right.crossingEdge hunique step) :
    (pair.slitRotationSystem).alpha (Sum.inl dart) =
      Sum.inr ⟨dart, (pair.right_crossingEdges_subset_support
        ((pair.right.mem_crossingEdges_iff hunique _).2
          ⟨step, hcrossing.symm⟩))⟩ := by
  exact slitRotationSystem_alpha_old_of_mem RS pair.crossingSupport
    (pair.right_crossingEdges_subset_support
      ((pair.right.mem_crossingEdges_iff hunique _).2
        ⟨step, hcrossing.symm⟩))

end AlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
