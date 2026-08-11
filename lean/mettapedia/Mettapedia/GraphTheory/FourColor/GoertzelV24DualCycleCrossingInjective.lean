import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal

/-!
# Distinct primal crossings of a simple facial-dual cycle

This is small generic rotation-system infrastructure.  A simple cycle in the
facial dual cannot cross the same primal edge twice: two equal crossings
would give the same underlying dual edge, while a cycle has no repeated dual
edges.  Keeping the lemma here avoids making source-local corridor modules
import an unrelated adjacent-pair development merely to use this fact.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualPathTransversal

open GoertzelV24FaceOrbitIncidence
open SimpleGraph

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The unoriented facial-dual edge traversed at one walk position. -/
def coreDualWalkGraphEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) : Sym2 (AmbientFace allFaces) :=
  s(walk.getVert step.val, walk.getVert (step.val + 1))

/-- Equal crossed primal edges force equal unoriented facial-dual edges when
each primal edge has at most two facial incidences. -/
theorem coreDualWalkGraphEdge_eq_of_crossingEdge_eq
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    {first second : Fin walk.length}
    (hedges : dualWalkCrossingEdge faceBoundary allFaces hunique walk first =
      dualWalkCrossingEdge faceBoundary allFaces hunique walk second) :
    coreDualWalkGraphEdge faceBoundary allFaces walk first =
      coreDualWalkGraphEdge faceBoundary allFaces walk second := by
  let firstLeft := walk.getVert first.val
  let firstRight := walk.getVert (first.val + 1)
  let secondLeft := walk.getVert second.val
  let secondRight := walk.getVert (second.val + 1)
  have hfirstAdj := walk.adj_getVert_succ first.isLt
  have hsecondAdj := walk.adj_getVert_succ second.isLt
  have hfirstFaces : firstLeft.1 ≠ firstRight.1 := by
    intro hfaces
    exact hfirstAdj.ne (Subtype.ext hfaces)
  have hsecondFaces : secondLeft.1 ≠ secondRight.1 := by
    intro hfaces
    exact hsecondAdj.ne (Subtype.ext hfaces)
  have hfirstLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary firstLeft.1 :=
    dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique walk first
  have hfirstRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary firstRight.1 :=
    dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique walk first
  have hsecondLeft :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary secondLeft.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_leftFace faceBoundary allFaces hunique
      walk second
  have hsecondRight :
      dualWalkCrossingEdge faceBoundary allFaces hunique walk first ∈
        faceBoundary secondRight.1 := by
    rw [hedges]
    exact dualWalkCrossingEdge_mem_rightFace faceBoundary allFaces hunique
      walk second
  have hleft :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondLeft.2
      hfirstFaces hfirstLeft hfirstRight hsecondLeft
  have hright :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      faceBoundary allFaces hall firstLeft.2 firstRight.2 secondRight.2
      hfirstFaces hfirstLeft hfirstRight hsecondRight
  change s(firstLeft, firstRight) = s(secondLeft, secondRight)
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact False.elim (hsecondFaces (hleft.trans hright.symm))
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨Subtype.ext hleft.symm, Subtype.ext hright.symm⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨Subtype.ext hright.symm, Subtype.ext hleft.symm⟩
  · exact False.elim (hsecondFaces (hleft.trans hright.symm))

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Positional graph-edge reading agrees with the positional facial-dual
edge reading used above. -/
theorem edges_get_coreDualWalkGraphEdge
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {start finish : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start finish)
    (step : Fin walk.length) :
    let edgeStep : Fin walk.edges.length :=
      Fin.cast walk.length_edges.symm step
    walk.edges.get edgeStep =
      coreDualWalkGraphEdge faceBoundary allFaces walk step := by
  dsimp only
  simp [coreDualWalkGraphEdge, SimpleGraph.Walk.edges,
    List.get_eq_getElem, SimpleGraph.Walk.darts_getElem_eq_getVert]

/-- A simple facial-dual cycle crosses distinct primal edges. -/
theorem dualWalkCrossingEdge_injective_of_isCycle_core
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start start)
    (hcycle : walk.IsCycle) :
    Function.Injective
      (dualWalkCrossingEdge faceBoundary allFaces hunique walk) := by
  intro first second hedges
  have hgraphEdge := coreDualWalkGraphEdge_eq_of_crossingEdge_eq
    faceBoundary allFaces hall hunique walk hedges
  have hinjective : Function.Injective walk.edges.get :=
    List.nodup_iff_injective_get.mp hcycle.edges_nodup
  let first' : Fin walk.edges.length :=
    Fin.cast walk.length_edges.symm first
  let second' : Fin walk.edges.length :=
    Fin.cast walk.length_edges.symm second
  have hget : walk.edges.get first' = walk.edges.get second' := by
    rw [edges_get_coreDualWalkGraphEdge faceBoundary allFaces walk first,
      edges_get_coreDualWalkGraphEdge faceBoundary allFaces walk second]
    exact hgraphEdge
  exact Fin.cast_injective walk.length_edges.symm (hinjective hget)

/-- A simple facial-dual cycle of length `n` crosses exactly `n` distinct
primal edges.  This belongs with the lightweight cycle-injectivity lemma, so
open-tangle layer arguments need not import a closed-cubic collar stack just
to count their literal boundary. -/
theorem card_dualWalkCrossingEdges_eq_length_of_isCycle_core
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    {start : AmbientFace allFaces}
    (walk : (interiorDualGraph faceBoundary allFaces).Walk start start)
    (hcycle : walk.IsCycle) :
    (dualWalkCrossingEdges faceBoundary allFaces hunique walk).card =
      walk.length := by
  rw [dualWalkCrossingEdges,
    Finset.card_image_of_injective _
      (dualWalkCrossingEdge_injective_of_isCycle_core faceBoundary allFaces
        hall hunique walk hcycle),
    Finset.card_univ, Fintype.card_fin]

end

end GoertzelV24DualPathTransversal

end Mettapedia.GraphTheory.FourColor
