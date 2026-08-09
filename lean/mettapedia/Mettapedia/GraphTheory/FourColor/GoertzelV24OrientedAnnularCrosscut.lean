import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

/-!
# Oriented boundary ports of an annular crosscut

A facial-dual step has a source face and a target face.  In a two-sided
rotation system this determines the two actual dart ends of the crossed
primal edge.  This file extracts those ends and carries them into the slit
rotation system, giving the open interface an intrinsic left/right port
orientation rather than an arbitrary numbering of stubs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SimpleDualCrosscut

/-- The dart incident to the source face of one oriented facial-dual step.
It is chosen from the actual face occurrence, not from an arbitrary endpoint
of the underlying edge. -/
theorem exists_sourceFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    ∃ dart : RS.D,
      dart ∈ orbitFaceDarts RS (crosscut.walk.getVert step.val).1 ∧
        RS.edgeOf dart = crosscut.crossingEdge hunique step := by
  exact (mem_orbitFaceBoundary_iff RS
    (crosscut.walk.getVert step.val).1
    (crosscut.crossingEdge hunique step)).1
      (dualWalkCrossingEdge_mem_leftFace (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) hunique crosscut.walk step)

/-- Canonical source-face incidence dart for a crossed edge. -/
noncomputable def sourceFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) : RS.D :=
  Classical.choose (crosscut.exists_sourceFaceDart hunique step)

/-- The selected source dart really lies on the face before the dual step. -/
theorem sourceFaceDart_face
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    dartOrbitFace RS (crosscut.sourceFaceDart hunique step) =
      (crosscut.walk.getVert step.val).1 := by
  exact (mem_orbitFaceDarts_iff RS
    (crosscut.walk.getVert step.val).1
    (crosscut.sourceFaceDart hunique step)).1
      (Classical.choose_spec (crosscut.exists_sourceFaceDart hunique step)).1

/-- The selected source dart carries precisely the primal edge crossed by
the corresponding facial-dual step. -/
theorem sourceFaceDart_edge
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    RS.edgeOf (crosscut.sourceFaceDart hunique step) =
      crosscut.crossingEdge hunique step :=
  (Classical.choose_spec (crosscut.exists_sourceFaceDart hunique step)).2

/-- In a two-sided map, the alpha-opposite of the source-face dart lies on
the face after the dual step.  This is the concrete orientation law that
turns a crossed edge into the two ordered sides of an open interface. -/
theorem alpha_sourceFaceDart_face
    {RS : RotationSystem V G.edgeSet}
    (htwoSided : OrbitFacesTwoSided RS)
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    dartOrbitFace RS (RS.alpha (crosscut.sourceFaceDart hunique step)) =
      (crosscut.walk.getVert (step.val + 1)).1 := by
  let sourceFace := (crosscut.walk.getVert step.val).1
  let targetFace := (crosscut.walk.getVert (step.val + 1)).1
  let dart := crosscut.sourceFaceDart hunique step
  have hsourceTargetNe : sourceFace ≠ targetFace := by
    intro hfaces
    exact (crosscut.walk.adj_getVert_succ step.isLt).ne
      (Subtype.ext hfaces)
  have hsourceEdge : RS.edgeOf dart = crosscut.crossingEdge hunique step :=
    crosscut.sourceFaceDart_edge hunique step
  have hsourceBoundary : crosscut.crossingEdge hunique step ∈
      orbitFaceBoundary RS sourceFace := by
    rw [← hsourceEdge]
    change RS.edgeOf dart ∈ orbitFaceBoundary RS
      (crosscut.walk.getVert step.val).1
    rw [← crosscut.sourceFaceDart_face hunique step]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
  have htargetBoundary : crosscut.crossingEdge hunique step ∈
      orbitFaceBoundary RS targetFace := by
    exact dualWalkCrossingEdge_mem_rightFace (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) hunique crosscut.walk step
  have halphaBoundary : crosscut.crossingEdge hunique step ∈
      orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart)) := by
    rw [← hsourceEdge, ← RS.edge_alpha dart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)
  have halphaCases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
      (orbitFace_incidence_le_two RS)
      (by simp) (by simp) (by simp) hsourceTargetNe
      hsourceBoundary htargetBoundary halphaBoundary
  rcases halphaCases with halphaSource | halphaTarget
  · exact (htwoSided dart
      ((crosscut.sourceFaceDart_face hunique step).trans halphaSource.symm)).elim
  · exact halphaTarget

/-- The source-facing boundary port in the concrete slit rotation system. -/
noncomputable def sourcePort
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    CutDart RS (crosscut.crossingEdges hunique) :=
  ⟨crosscut.sourceFaceDart hunique step,
    (crosscut.mem_crossingEdges_iff hunique _).2
      ⟨step, (crosscut.sourceFaceDart_edge hunique step).symm⟩⟩

/-- The target-facing boundary port is the actual opposite dart of the
source port; it is not another choice of endpoint. -/
noncomputable def targetPort
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    CutDart RS (crosscut.crossingEdges hunique) :=
  ⟨RS.alpha (crosscut.sourceFaceDart hunique step),
    (crosscut.mem_crossingEdges_iff hunique _).2
      ⟨step, by
        calc
          crosscut.crossingEdge hunique step =
              RS.edgeOf (crosscut.sourceFaceDart hunique step) :=
            (crosscut.sourceFaceDart_edge hunique step).symm
          _ = RS.edgeOf (RS.alpha (crosscut.sourceFaceDart hunique step)) :=
            (RS.edge_alpha _).symm⟩⟩

@[simp]
theorem sourcePort_val
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    (crosscut.sourcePort hunique step).1 = crosscut.sourceFaceDart hunique step :=
  rfl

@[simp]
theorem targetPort_val
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    (crosscut.targetPort hunique step).1 =
      RS.alpha (crosscut.sourceFaceDart hunique step) :=
  rfl

/-- Opening a crossed source dart connects it to exactly its named source
boundary stub. -/
theorem slitRotationSystem_alpha_sourceFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    (crosscut.slitRotationSystem hunique).alpha
        (Sum.inl (crosscut.sourceFaceDart hunique step)) =
      Sum.inr (crosscut.sourcePort hunique step) := by
  exact slitRotationSystem_alpha_old_of_mem RS
    (crosscut.crossingEdges hunique)
    ((crosscut.mem_crossingEdges_iff hunique _).2
      ⟨step, (crosscut.sourceFaceDart_edge hunique step).symm⟩)

/-- Opening the alpha-opposite source dart connects it to the corresponding
target boundary stub. -/
theorem slitRotationSystem_alpha_targetFaceDart
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) :
    (crosscut.slitRotationSystem hunique).alpha
        (Sum.inl (RS.alpha (crosscut.sourceFaceDart hunique step))) =
      Sum.inr (crosscut.targetPort hunique step) := by
  exact slitRotationSystem_alpha_old_of_mem RS
    (crosscut.crossingEdges hunique)
    ((crosscut.mem_crossingEdges_iff hunique _).2
      ⟨step, by
        calc
          crosscut.crossingEdge hunique step =
              RS.edgeOf (crosscut.sourceFaceDart hunique step) :=
            (crosscut.sourceFaceDart_edge hunique step).symm
          _ = RS.edgeOf (RS.alpha (crosscut.sourceFaceDart hunique step)) :=
            (RS.edge_alpha _).symm⟩)

end SimpleDualCrosscut

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
