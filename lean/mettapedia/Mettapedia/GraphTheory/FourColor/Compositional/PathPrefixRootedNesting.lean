import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixCyclicCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore

/-!
# Coherent rooted saturation of nested path prefixes

Rooted saturation preserves nesting when every prefix uses the same exterior
component.  A later prefix supplies the common exterior cycle; all earlier
prefixes see that cycle through the path suffix.  The first forward path edge
added between two distinct cuts witnesses strictness of the resulting
incident-edge shores.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace PathPrefixRootedNesting

open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CyclicThreeCutConnectedSides
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixCyclicCut
open RootedCutSaturation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Strict path prefixes are monotone in the cut coordinate. -/
theorem pathPrefixSide_mono
    {start finish : V} {path : G.Walk start finish}
    {first second : Fin (path.length + 1)} (horder : first ≤ second) :
    ∀ vertex, pathPrefixSide path first vertex →
      pathPrefixSide path second vertex := by
  rintro vertex ⟨coordinate, hcoordinate, rfl⟩
  exact ⟨coordinate, hcoordinate.trans_le horder, rfl⟩

/-- The suffix component for a later cut is contained in the suffix component
for every earlier cut.  The roots differ, but the path segment between them
lies in the earlier complement. -/
theorem prefixExteriorComponent_mono
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    {first second : Fin (path.length + 1)} (horder : first ≤ second) :
    ∀ vertex, prefixExteriorComponent hpath second vertex →
      prefixExteriorComponent hpath first vertex := by
  intro vertex hvertex
  let firstComplement := fun point => ¬pathPrefixSide path first point
  let secondComplement := fun point => ¬pathPrefixSide path second point
  have hcomplementMono : ∀ point, secondComplement point →
      firstComplement point := by
    intro point hnotSecond hfirst
    exact hnotSecond (pathPrefixSide_mono horder point hfirst)
  have hsecondOutsideFirst : firstComplement (path.getVert second) := by
    change ¬pathPrefixSide path first (path.getVert second)
    rw [pathPrefixSide_getVert_iff hpath first second]
    exact not_lt_of_ge horder
  rcases hvertex with ⟨hvertexOutsideSecond, hsecondToVertex⟩
  have hsecondToVertexFirst :
      (G.induce firstComplement).Reachable
        ⟨path.getVert second, hsecondOutsideFirst⟩
        ⟨vertex, hcomplementMono vertex hvertexOutsideSecond⟩ := by
    let inclusion := G.induceHomOfLE hcomplementMono
    have hmapped := hsecondToVertex.map inclusion.toHom
    convert hmapped using 1 <;> apply Subtype.ext <;> rfl
  rcases getVert_mem_prefixExteriorComponent hpath first second horder with
    ⟨_hsecondOutside, hfirstToSecond⟩
  refine ⟨hcomplementMono vertex hvertexOutsideSecond, ?_⟩
  exact hfirstToSecond.trans hsecondToVertexFirst

/-- If a common exterior root lies in an anchor suffix component, every path
coordinate between an earlier cut and that anchor lies in the exterior
component rooted at the common root. -/
theorem getVert_mem_commonRootExteriorComponent
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    {cut coordinate anchor : Fin (path.length + 1)}
    (hcutCoordinate : cut ≤ coordinate) (hcoordinateAnchor : coordinate ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : prefixExteriorComponent hpath anchor outsideRoot) :
    inducedReachableSide G (fun vertex => ¬pathPrefixSide path cut vertex)
      outsideRoot
      (prefixExteriorComponent_mono hpath
        (hcutCoordinate.trans hcoordinateAnchor) outsideRoot hrootAnchor).choose
      (path.getVert coordinate) := by
  have hrootCut := prefixExteriorComponent_mono hpath
    (hcutCoordinate.trans hcoordinateAnchor) outsideRoot hrootAnchor
  have hcoordinateCut :=
    getVert_mem_prefixExteriorComponent hpath cut coordinate hcutCoordinate
  rcases hrootCut with ⟨hrootOutside, hcutToRoot⟩
  rcases hcoordinateCut with ⟨hcoordinateOutside, hcutToCoordinate⟩
  refine ⟨hcoordinateOutside, ?_⟩
  have hrootToCut := hcutToRoot.symm
  exact hrootToCut.trans hcutToCoordinate

/-- Rooted closure sides of two distinct prefixes have strictly nested
incident-edge shores.  The forward edge after the earlier cut belongs only
to the later shore. -/
theorem incidentEdgeShore_closureSide_ssubset
    {start finish : V} {path : G.Walk start finish} (hpath : path.IsPath)
    {first second anchor : Fin (path.length + 1)}
    (hfirstSecond : first < second) (hsecondAnchor : second ≤ anchor)
    (outsideRoot : V)
    (hrootAnchor : prefixExteriorComponent hpath anchor outsideRoot) :
    incidentEdgeShore G
        (closureSide (G := G) (pathPrefixSide path first) outsideRoot
          (prefixExteriorComponent_mono hpath hfirstSecond.le outsideRoot
            (prefixExteriorComponent_mono hpath hsecondAnchor outsideRoot
              hrootAnchor)).choose) ⊂
      incidentEdgeShore G
        (closureSide (G := G) (pathPrefixSide path second) outsideRoot
          (prefixExteriorComponent_mono hpath hsecondAnchor outsideRoot
            hrootAnchor).choose) := by
  let hrootSecond := prefixExteriorComponent_mono hpath hsecondAnchor
    outsideRoot hrootAnchor
  let hrootFirst := prefixExteriorComponent_mono hpath
    (hfirstSecond.le.trans hsecondAnchor) outsideRoot hrootAnchor
  let firstClosure := closureSide (G := G) (pathPrefixSide path first)
    outsideRoot hrootFirst.choose
  let secondClosure := closureSide (G := G) (pathPrefixSide path second)
    outsideRoot hrootSecond.choose
  have hclosureMono : ∀ vertex, firstClosure vertex → secondClosure vertex := by
    intro vertex hvertex
    apply closureSide_mono (G := G) (pathPrefixSide_mono hfirstSecond.le)
      outsideRoot hrootSecond.choose vertex
    simpa only [firstClosure, hrootFirst] using hvertex
  have hshoreMono : incidentEdgeShore G firstClosure ⊆
      incidentEdgeShore G secondClosure :=
    incidentEdgeShore_mono hclosureMono
  apply (Finset.ssubset_iff_of_subset hshoreMono).2
  let next : Fin (path.length + 1) := ⟨first.val + 1, by
    have := second.isLt
    omega⟩
  have hnextPositive : 0 < next.val := by simp [next]
  let edge := forwardPathEdge path next hnextPositive
  refine ⟨edge, ?_, ?_⟩
  · apply (mem_incidentEdgeShore_iff secondClosure edge).2
    refine ⟨path.getVert first, ?_, ?_⟩
    · simp [edge, forwardPathEdge, next]
    · apply side_subset_closureSide
      rw [pathPrefixSide_getVert_iff hpath second first]
      exact hfirstSecond
  · intro hedge
    rcases (mem_incidentEdgeShore_iff firstClosure edge).1 hedge with
      ⟨vertex, hvertexEdge, hvertexClosure⟩
    have hcases : vertex = path.getVert first ∨ vertex = path.getVert next := by
      simpa [edge, forwardPathEdge, next] using hvertexEdge
    have hnextSecond : next ≤ second := by
      apply Fin.mk_le_mk.mpr
      exact hfirstSecond
    have hfirstNext : first ≤ next := by
      apply Fin.mk_le_mk.mpr
      simp [next]
    rcases hcases with rfl | rfl
    · apply hvertexClosure
      exact getVert_mem_commonRootExteriorComponent hpath first.le_rfl
        hfirstSecond.le outsideRoot hrootSecond
    · apply hvertexClosure
      exact getVert_mem_commonRootExteriorComponent hpath hfirstNext
        hnextSecond outsideRoot hrootSecond

end

end PathPrefixRootedNesting

end Mettapedia.GraphTheory.FourColor.Compositional
