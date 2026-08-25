import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionGraphBacking

/-!
# The deleted-region slit graph is the literal open-region carrier

The manuscript-side slit graph deletes a vertex region and attaches one fresh
stub to every outward dart.  The existing open-region rotation construction
does the same operation inside the rotation-system tower.  This file starts
the exact carrier comparison, so later source formations can use the existing
open-region theorems rather than rebuild them for the slit presentation.

The comparison is generic.  It does not choose a source cap, an annular side,
or an ordered boundary word.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedRegionSlitOpenRegionComparison

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphFaceDualConnectedness

-- Use the ordinary subtype equality on retained vertices, matching the
-- graph-backed open-region carrier.

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The retained predicate for a manuscript-side deleted region. -/
abbrev keep (deleted : Finset V) : V → Prop := fun vertex => vertex ∉ deleted

/-- Read a manuscript-side port as the corresponding exposed dart of the
literal open-region construction. -/
def portToBoundaryDart (data : Data G) {deleted : Finset V}
    (port : DeletedRegionBoundaryPort G deleted) :
    BoundaryDart data.toRotationSystem (keep deleted) :=
  ⟨⟨port.dart, by simpa [keep] using port.retained⟩,
    by simpa [keep] using port.removed⟩

/-- Read an exposed dart of the literal open-region construction as the
corresponding manuscript-side fresh port. -/
def boundaryDartToPort (data : Data G) {deleted : Finset V}
    (boundary : BoundaryDart data.toRotationSystem (keep deleted)) :
    DeletedRegionBoundaryPort G deleted :=
  ⟨boundary.1.1, by simpa [keep] using boundary.1.2,
    by simpa [keep] using boundary.2⟩

/-- The two opening presentations have the same literal vertex carrier:
retained ambient vertices are unchanged and each outward dart gives one fresh
stub in either presentation. -/
def slitToOpenRegionVertexEquiv (data : Data G) (deleted : Finset V) :
    DeletedRegionSlitVertex G deleted ≃
      GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem (keep deleted) where
  toFun := fun vertex => match vertex with
    | Sum.inl old => Sum.inl old
    | Sum.inr port => Sum.inr (portToBoundaryDart data port)
  invFun := fun vertex => match vertex with
    | Sum.inl old => Sum.inl old
    | Sum.inr boundary => Sum.inr (boundaryDartToPort data boundary)
  left_inv := by
    intro vertex
    rcases vertex with old | port
    · rfl
    · apply congrArg Sum.inr
      rfl
  right_inv := by
    intro vertex
    rcases vertex with old | boundary
    · rfl
    · apply congrArg Sum.inr
      rfl

@[simp] theorem slitToOpenRegionVertexEquiv_old (data : Data G) (deleted : Finset V)
    (old : {vertex // vertex ∉ deleted}) :
    slitToOpenRegionVertexEquiv data deleted (Sum.inl old) = Sum.inl old :=
  rfl

@[simp] theorem slitToOpenRegionVertexEquiv_stub (data : Data G) (deleted : Finset V)
    (port : DeletedRegionBoundaryPort G deleted) :
    slitToOpenRegionVertexEquiv data deleted (Sum.inr port) =
      Sum.inr (portToBoundaryDart data port) :=
  rfl

/-- On retained vertices, the computed literal open-region graph has exactly
the ambient adjacency. -/
theorem primalGraph_adj_old_old_iff (data : Data G) (deleted : Finset V)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep deleted))
    (left right : {vertex // vertex ∉ deleted}) :
    (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
      (Sum.inl left) (Sum.inl right) ↔ G.Adj left.1 right.1 := by
  constructor
  · intro hadj
    rw [GoertzelV24FaceDualConnectedness.rotationPrimalGraph_adj_iff] at hadj
    rcases hadj with ⟨dart, hleft, hright⟩
    rcases dart with oldDart | boundary
    · by_cases hinternal : keep deleted
          (data.toRotationSystem.vertOf (data.toRotationSystem.alpha oldDart.1))
      · rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_internal
          data.toRotationSystem (keep deleted) outer oldDart hinternal] at hright
        change (Sum.inl ⟨oldDart.1.fst, oldDart.2⟩ :
          GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem
            (keep deleted)) = Sum.inl left at hleft
        change (Sum.inl ⟨oldDart.1.snd, hinternal⟩ :
          GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem
            (keep deleted)) = Sum.inl right at hright
        rw [← rotationPrimalGraph_toRotationSystem_eq G data,
          GoertzelV24FaceDualConnectedness.rotationPrimalGraph_adj_iff]
        refine ⟨oldDart.1, ?_, ?_⟩
        · exact congrArg Subtype.val (Sum.inl.inj hleft)
        · exact congrArg Subtype.val (Sum.inl.inj hright)
      · rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_old_of_boundary
          data.toRotationSystem (keep deleted) outer oldDart hinternal] at hright
        exact False.elim (by simpa using hright)
    · exact False.elim (by simpa using hleft)
  · intro hadj
    apply primalGraph_adj_retained data.toRotationSystem (keep deleted) outer
    change (GoertzelV24FaceDualConnectedness.rotationPrimalGraph
      data.toRotationSystem).Adj left.1 right.1
    rw [rotationPrimalGraph_toRotationSystem_eq G data]
    exact hadj

/-- A fresh open-region stub has exactly the retained endpoint of the
manuscript-side port which created it. -/
theorem primalGraph_adj_stub_old_iff (data : Data G) (deleted : Finset V)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep deleted))
    (port : DeletedRegionBoundaryPort G deleted)
    (old : {vertex // vertex ∉ deleted}) :
    (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
      (Sum.inr (portToBoundaryDart data port)) (Sum.inl old) ↔
      old.1 = port.dart.fst := by
  constructor
  · intro hadj
    rw [GoertzelV24FaceDualConnectedness.rotationPrimalGraph_adj_iff] at hadj
    rcases hadj with ⟨dart, hleft, hright⟩
    rcases dart with oldDart | boundary
    · exact False.elim (by simpa using hleft)
    · change (Sum.inr boundary :
          GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem
            (keep deleted)) = Sum.inr (portToBoundaryDart data port) at hleft
      have hboundary : boundary = portToBoundaryDart data port := Sum.inr.inj hleft
      subst boundary
      rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_stub] at hright
      change (Sum.inl ⟨(portToBoundaryDart data port).1.1.fst,
        (portToBoundaryDart data port).1.2⟩ :
          GoertzelV24OpenRegionRotation.Vertex data.toRotationSystem
            (keep deleted)) = Sum.inl old at hright
      have hvertex : (portToBoundaryDart data port).1.1.fst = old.1 :=
        congrArg Subtype.val (Sum.inl.inj hright)
      simpa [portToBoundaryDart] using hvertex.symm
  · intro hadj
    have hretained :
        (⟨data.toRotationSystem.vertOf (portToBoundaryDart data port).1.1,
          (portToBoundaryDart data port).1.2⟩ :
          GoertzelV24OpenRegionRotation.RetainedVertex (keep deleted)) = old :=
      Subtype.ext (by simpa [portToBoundaryDart] using hadj.symm)
    have hstub := primalGraph_adj_boundary_retained data.toRotationSystem
      (keep deleted) outer (portToBoundaryDart data port)
    rw [hretained] at hstub
    exact hstub

/-- Distinct fresh open-region stubs are never adjacent. -/
theorem primalGraph_not_adj_stub_stub (data : Data G) (deleted : Finset V)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep deleted))
    (first second : DeletedRegionBoundaryPort G deleted) :
    ¬ (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
      (Sum.inr (portToBoundaryDart data first))
      (Sum.inr (portToBoundaryDart data second)) := by
  intro hadj
  rw [GoertzelV24FaceDualConnectedness.rotationPrimalGraph_adj_iff] at hadj
  rcases hadj with ⟨dart, hleft, hright⟩
  rcases dart with oldDart | boundary
  · exact False.elim (by simpa using hleft)
  · rw [GoertzelV24OpenRegionRotation.rotationSystem_alpha_stub] at hright
    exact False.elim (by simpa using hright)

/-- The manuscript-side slit graph is exactly the simple primal graph computed
from the existing literal open-region rotation.  This is the reusable bridge
from a vertex-deletion presentation to the established open-region tower. -/
def slitGraphIsoOpenPrimalGraph (data : Data G) (deleted : Finset V)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep deleted)) :
    (deletedRegionSlitGraph (G := G) deleted).Iso
      (PrimalGraph data.toRotationSystem (keep deleted) outer) where
  toEquiv := slitToOpenRegionVertexEquiv data deleted
  map_rel_iff' := by
    intro first second
    rcases first with oldFirst | portFirst <;>
      rcases second with oldSecond | portSecond
    · change (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
        (Sum.inl oldFirst) (Sum.inl oldSecond) ↔ G.Adj oldFirst.1 oldSecond.1
      exact primalGraph_adj_old_old_iff data deleted outer oldFirst oldSecond
    · change (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
          (Sum.inl oldFirst) (Sum.inr (portToBoundaryDart data portSecond)) ↔
        oldFirst.1 = portSecond.dart.fst
      constructor
      · intro hadj
        exact (primalGraph_adj_stub_old_iff data deleted outer portSecond oldFirst).mp
          ((PrimalGraph data.toRotationSystem (keep deleted) outer).adj_symm hadj)
      · intro hadj
        exact (PrimalGraph data.toRotationSystem (keep deleted) outer).adj_symm
          ((primalGraph_adj_stub_old_iff data deleted outer portSecond oldFirst).mpr hadj)
    · change (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
          (Sum.inr (portToBoundaryDart data portFirst)) (Sum.inl oldSecond) ↔
        portFirst.dart.fst = oldSecond.1
      simpa [eq_comm] using
        (primalGraph_adj_stub_old_iff data deleted outer portFirst oldSecond)
    · change (PrimalGraph data.toRotationSystem (keep deleted) outer).Adj
          (Sum.inr (portToBoundaryDart data portFirst))
          (Sum.inr (portToBoundaryDart data portSecond)) ↔ False
      constructor
      · exact primalGraph_not_adj_stub_stub data deleted outer portFirst portSecond
      · exact False.elim

end

end GoertzelV24DeletedRegionSlitOpenRegionComparison

end Mettapedia.GraphTheory.FourColor
