import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailPointedEdgeComponentOrientation
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathInteriorCrossSplice

/-!
# L1: splice a pointed two-hop bypass into a selected rail

The source-local endpoint allocation now supplies a short walk from the
predecessor to the successor of a strict collision occurrence.  This module
installs that walk in the whole selected rail using the generic interior
cross-splice operation.  The returned rail is simple, has the original outer
endpoints, avoids the removed collision face, and retains a precise support
receipt.

This is generic pointed-walk surgery.  It does not prove the two source-corner
component-membership facts, separation from the companion rail, iteration of
the rolling transition, the two end caps, or Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DualPathInteriorCrossSplice
open GoertzelV24DualPathPointedOccurrence
open GoertzelV24FaceOrbitIncidence

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

private abbrev SelectedFace
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

private abbrev SelectedDualGraph
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) :=
  interiorDualGraph (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))

/-- The repaired whole rail and the receipts needed by the later paired-rail
assembly.  The support statement is intentionally one-sided: loop erasure may
remove old vertices, but it cannot introduce a vertex outside the old rail or
the supplied bypass. -/
structure InteriorOccurrence.SpliceRepair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (bypass : InteriorOccurrence.TwoHopBypass occurrence) where
  walk : (SelectedDualGraph web).Walk start finish
  isPath : walk.IsPath
  current_not_mem_support : current ∉ walk.support
  support_subset : ∀ vertex ∈ walk.support,
    vertex ∈ rail.support ∨ vertex ∈ bypass.walk.support

private theorem InteriorOccurrence.current_mem_support
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail) :
    current ∈ rail.support := by
  apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
  exact ⟨occurrence.index, occurrence.getVert_eq, Nat.le_of_lt occurrence.index_lt⟩

private theorem InteriorOccurrence.length_takeUntil_eq_index
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath) :
    (rail.takeUntil current
      (InteriorOccurrence.current_mem_support occurrence)).length =
      occurrence.index := by
  have hmem := InteriorOccurrence.current_mem_support occurrence
  apply hpath.getVert_injOn
  · exact rail.length_takeUntil_le_length hmem
  · exact Nat.le_of_lt occurrence.index_lt
  · exact (rail.getVert_length_takeUntil hmem).trans occurrence.getVert_eq.symm

private theorem InteriorOccurrence.takeUntil_penultimate_eq_predecessor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath) :
    (rail.takeUntil current
      (InteriorOccurrence.current_mem_support occurrence)).penultimate =
      occurrence.predecessor := by
  have hlength : (rail.takeUntil current
      (InteriorOccurrence.current_mem_support occurrence)).length =
      occurrence.index :=
    InteriorOccurrence.length_takeUntil_eq_index occurrence hpath
  rw [SimpleGraph.Walk.penultimate, hlength]
  rw [rail.getVert_takeUntil
    (InteriorOccurrence.current_mem_support occurrence)
    (hlength ▸ Nat.sub_le occurrence.index 1)]
  rfl

private theorem InteriorOccurrence.dropUntil_snd_eq_successor
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath) :
    (rail.dropUntil current
      (InteriorOccurrence.current_mem_support occurrence)).snd =
      occurrence.successor := by
  have hlength : (rail.takeUntil current
      (InteriorOccurrence.current_mem_support occurrence)).length =
      occurrence.index :=
    InteriorOccurrence.length_takeUntil_eq_index occurrence hpath
  change (rail.dropUntil current
    (InteriorOccurrence.current_mem_support occurrence)).getVert 1 =
      rail.getVert (occurrence.index + 1)
  rw [rail.dropUntil_eq_drop]
  simp only [SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.drop_getVert]
  rw [← rail.length_takeUntil
    (InteriorOccurrence.current_mem_support occurrence), hlength]

private theorem InteriorOccurrence.start_ne_current
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath) : start ≠ current := by
  intro hstart
  have hindex : 0 = occurrence.index := hpath.getVert_injOn
    (by simp) (Nat.le_of_lt occurrence.index_lt) (by
      simpa [hstart] using occurrence.getVert_eq.symm)
  exact (Nat.ne_of_gt occurrence.index_pos) hindex.symm

private theorem InteriorOccurrence.current_ne_finish
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath) : current ≠ finish := by
  intro hfinish
  have hindex : occurrence.index = rail.length := hpath.getVert_injOn
    (Nat.le_of_lt occurrence.index_lt) (by simp) (by
      simpa [hfinish] using occurrence.getVert_eq)
  exact (Nat.ne_of_lt occurrence.index_lt) hindex

/-- **L1 pointed bypass splice.**  Any certified two-hop bypass can be
installed in the entire rail.  The endpoint equalities are derived from the
strict occurrence and path simplicity; they are not extra assumptions. -/
theorem InteriorOccurrence.nonempty_spliceRepair
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}
    {start finish current : SelectedFace web}
    {rail : (SelectedDualGraph web).Walk start finish}
    (occurrence : InteriorOccurrence (current := current) rail)
    (hpath : rail.IsPath)
    (bypass : InteriorOccurrence.TwoHopBypass occurrence) :
    Nonempty (InteriorOccurrence.SpliceRepair occurrence bypass) := by
  let hmem := InteriorOccurrence.current_mem_support occurrence
  let bridge := bypass.walk.copy
    (InteriorOccurrence.takeUntil_penultimate_eq_predecessor occurrence hpath).symm
    (InteriorOccurrence.dropUntil_snd_eq_successor occurrence hpath).symm
  let repaired := crossSpliceAroundWithBridge rail rail hmem hmem bridge
  refine ⟨{
    walk := repaired
    isPath := crossSpliceAroundWithBridge_isPath rail rail hmem hmem bridge
    current_not_mem_support := ?_
    support_subset := ?_
  }⟩
  · apply current_not_mem_crossSpliceAroundWithBridge_support
      rail rail hpath hpath hmem hmem
      (InteriorOccurrence.start_ne_current occurrence hpath)
      (InteriorOccurrence.current_ne_finish occurrence hpath) bridge
    simpa [bridge] using bypass.current_not_mem_support
  · intro vertex hvertex
    rcases crossSpliceAroundWithBridge_support_subset rail rail hmem hmem
        (InteriorOccurrence.start_ne_current occurrence hpath)
        (InteriorOccurrence.current_ne_finish occurrence hpath)
        bridge vertex hvertex with
      hold | hbridge | hnew
    · exact .inl hold
    · exact .inr (by simpa [bridge] using hbridge)
    · exact .inl hnew

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
