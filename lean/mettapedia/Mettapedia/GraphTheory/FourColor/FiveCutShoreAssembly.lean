import Mettapedia.GraphTheory.FourColor.FiveCutCapInstantiation
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapSupport
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapClass
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapSupport
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapClass
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapDetour
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordTransfers

/-!
# Per-shore menu validity at an exact five-cut

Each shore of a nontrivial exact cyclic five-edge cut meets the pentagon
support and the three consecutive Y-cap supports of the word heart, in
the shore's own pinned boundary coordinates.  The caps are instantiated
at reflections of the pinned order (which carry the successor pin to the
cap convention), vertex minimality colours the capped shore, the support
theorems read the boundary word off that colouring, and the dihedral
word transfers land the supports at the required positions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FiveCutShoreAssembly

open Compositional
open Compositional.FiveCutShoreLanguage
open Compositional.FiveCutWordTransfers
open FiveCutCapAssembly
open GoertzelV24CyclicExactCutConnectedSides
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24PortTangleGluing
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSidePrimalKempeTrail
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The reflections' symm acts as the reflection itself. -/
theorem subLeft_symm_apply :
    ∀ c i : Fin 5, (Equiv.subLeft c).symm i = c - i := by
  decide

/-- **Pentagon support on a shore**, keep-generalized: any predicate equal
to the shore keep carries a shore-language word in the pentagon support.
The generalization lets the caller work at the canonical
`deletedRegionKeep` spelling. -/
theorem exists_pentagonSupport_word_of_keep_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hdeletedCard : 6 ≤ (exactCutVertexSide cut).card)
    (keep : V → Prop) (hkeep : shoreKeep cut = keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (orderR : Fin 5 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hpin : orderR.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep) :
    ∃ w, shoreLanguage orderR
        (vertexSidePortTangle graphData keep outer) w ∧
      CAP5WordExtendsAcrossCycle w := by
  subst hkeep
  classical
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hsides := induce_both_sides_connected_of_exactSized
    hconnected hcyclic cut
  set capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut) :=
    (Equiv.subLeft (0 : Fin 5)).trans orderR with hcapOrder
  set capData := pentagonCapDataOfOrder graphData cut capOrder
    outer.1 outer.2 with hcapData
  have hkeepEq : capData.keep =
      deletedRegionKeep (exactCutVertexSide cut) :=
    shoreKeep_eq_deletedRegionKeep cut
  have hequiv : capData.crossingBoundaryDartEquiv = capOrder :=
    crossingBoundaryDartEquiv_pentagonCapDataOfOrder graphData cut capOrder
      outer.1 outer.2
  have hsucc : retainedRegionBoundarySuccessor graphData.toRotationSystem
      capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹ := by
    rw [hequiv]
    exact anti_pin_of_pin_reflection orderR _ 0 hpin
  have hretainedConnected : (G.induce {vertex |
      deletedRegionKeep (exactCutVertexSide cut) vertex}).Connected := by
    have hpred : {vertex |
        deletedRegionKeep (exactCutVertexSide cut) vertex} =
        {vertex | ¬ cut.side vertex} := by
      ext vertex
      change (¬ vertex ∈ exactCutVertexSide cut) ↔ ¬ cut.side vertex
      rw [mem_exactCutVertexSide_iff]
    rw [hpred]
    exact hsides.2
  have hdeletedConnected : (G.induce {vertex |
      ¬ deletedRegionKeep (exactCutVertexSide cut) vertex}).Connected := by
    have hpred : {vertex |
        ¬ deletedRegionKeep (exactCutVertexSide cut) vertex} =
        {vertex | cut.side vertex} := by
      ext vertex
      change (¬ vertex ∉ exactCutVertexSide cut) ↔ cut.side vertex
      rw [not_not, mem_exactCutVertexSide_iff]
    rw [hpred]
    exact hsides.1
  have hretainedAmbient : (retainedAmbientPrimalGraph
      graphData.toRotationSystem capData.keep).Connected := by
    show ((rotationPrimalGraph graphData.toRotationSystem).induce
      {vertex | capData.keep vertex}).Connected
    rw [rotationPrimalGraph_toRotationSystem_eq G graphData]
    have hpred : {vertex | capData.keep vertex} =
        {vertex | ¬ cut.side vertex} := by
      ext vertex
      change vertex ∈ exactCutVertexSide cut.compl ↔ ¬ cut.side vertex
      rw [mem_exactCutVertexSide_iff]
      exact Iff.rfl
    rw [hpred]
    exact hsides.2
  have hdeleted6 : 6 ≤
      (Finset.univ.filter fun v => ¬ capData.keep v).card := by
    have hfilter : (Finset.univ.filter fun v => ¬ capData.keep v) =
        exactCutVertexSide cut := by
      ext vertex
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (¬ vertex ∈ exactCutVertexSide cut.compl) ↔
        vertex ∈ exactCutVertexSide cut
      rw [mem_exactCutVertexSide_iff, mem_exactCutVertexSide_iff]
      exact not_not
    rw [hfilter]
    exact hdeletedCard
  obtain ⟨K, hK⟩ := FiveEdgeCutPentagonCapData.capTaitColorable_of_vertexMinimal
    graphData (exactCutVertexSide cut) minimal capData hsucc
    hretainedConnected hdeletedConnected hkeepEq hretainedAmbient hdeleted6
  obtain ⟨w, hlang, hext⟩ :=
    capData.exists_word_in_pentagonSupport graphData outer K hK
  rw [hequiv] at hlang
  have hlang' := (shoreLanguage_trans_iff (Equiv.subLeft (0 : Fin 5)) orderR
    (vertexSidePortTangle graphData (shoreKeep cut) outer) w).mp hlang
  have hfun : (fun i => w ((Equiv.subLeft (0 : Fin 5)).symm i)) =
      fun i => w ((0 : Fin 5) - i) := by
    funext i
    rw [subLeft_symm_apply]
  rw [hfun] at hlang'
  exact ⟨fun i => w ((0 : Fin 5) - i), hlang',
    extendsAcrossCycle_reflect 0 w hext⟩

end

end FiveCutShoreAssembly

end Mettapedia.GraphTheory.FourColor
