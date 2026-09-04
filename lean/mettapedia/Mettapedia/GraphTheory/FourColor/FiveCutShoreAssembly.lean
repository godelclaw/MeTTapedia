import Mettapedia.GraphTheory.FourColor.FiveCutCapInstantiation
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapSupport
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapClass
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapSupport
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapClass
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapDetour
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordTransfers
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutShorePhysical
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordHeartProof
import Mettapedia.GraphTheory.FourColor.FiveCutSeamSurgery

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
open Compositional.FiveCutShorePhysical
open Compositional.FiveCutWordHeart
open FiveCutSeamSurgery
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

/-- **Y-cap support on a shore**, keep-generalized and parametric in the
reflection base `c`: given distinct seam endpoints at boundary positions
`c` and `c - 1`, the shore language meets the Y-cap support at position
`c - 1`. -/
theorem exists_ySupport_word_of_keep_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hdeletedCard : 6 ≤ (exactCutVertexSide cut).card)
    (keep : V → Prop) (hkeep : shoreKeep cut = keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (orderR : Fin 5 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hpin : orderR.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem keep)
    (c : Fin 5)
    (hseam : graphData.toRotationSystem.vertOf (orderR c).1.1 ≠
      graphData.toRotationSystem.vertOf (orderR (c - 1)).1.1) :
    ∃ w, shoreLanguage orderR
        (vertexSidePortTangle graphData keep outer) w ∧
      CAP5YCapSupport (c - 1) w := by
  subst hkeep
  classical
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hsides := induce_both_sides_connected_of_exactSized
    hconnected hcyclic cut
  set capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut) :=
    (Equiv.subLeft c).trans orderR with hcapOrder
  have hseam' : graphData.toRotationSystem.vertOf (capOrder 0).1.1 ≠
      graphData.toRotationSystem.vertOf (capOrder 1).1.1 := by
    show graphData.toRotationSystem.vertOf (orderR (c - 0)).1.1 ≠
      graphData.toRotationSystem.vertOf (orderR (c - 1)).1.1
    rw [sub_zero]
    exact hseam
  set capData := yCapDataOfOrder graphData cut capOrder outer.1 outer.2
    hseam' with hcapData
  have hkeepEq : capData.keep =
      deletedRegionKeep (exactCutVertexSide cut) :=
    shoreKeep_eq_deletedRegionKeep cut
  have hequiv : capData.crossingBoundaryDartEquiv = capOrder :=
    crossingBoundaryDartEquiv_yCapDataOfOrder graphData cut capOrder
      outer.1 outer.2 hseam'
  have hsucc : retainedRegionBoundarySuccessor graphData.toRotationSystem
      capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹ := by
    rw [hequiv]
    exact anti_pin_of_pin_reflection orderR _ c hpin
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
  have hregular : G.IsRegularOfDegree 3 := by
    intro v
    have hcub :=
      (graphData.toRotationSystem_isCubic_iff).mp minimal.spherical.cubic v
    convert hcub using 2
  have hdetour : ∀ removed : InternalDart graphData.toRotationSystem
      capData.keep,
      (capData.internalDetourGraph removed).Reachable
        (graphData.toRotationSystem.vertOf removed.1.1)
        (graphData.toRotationSystem.vertOf
          (graphData.toRotationSystem.alpha removed.1.1)) :=
    fun removed => capData.internalDetourGraph_reachable_of_cyclicFive
      graphData hregular hconnected hcyclic removed
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (exactCutVertexSide cut).card)
  have hleft : ¬ capData.keep a := fun hmem =>
    (mem_exactCutVertexSide_iff cut.compl a).mp hmem
      ((mem_exactCutVertexSide_iff cut a).mp ha)
  have hright : ¬ capData.keep b := fun hmem =>
    (mem_exactCutVertexSide_iff cut.compl b).mp hmem
      ((mem_exactCutVertexSide_iff cut b).mp hb)
  obtain ⟨K, hK⟩ := FiveEdgeCutYCapData.capTaitColorable_of_vertexMinimal
    graphData (exactCutVertexSide cut) minimal capData hsucc
    hretainedConnected hdeletedConnected hkeepEq hretainedAmbient hdetour
    a b hab hleft hright
  obtain ⟨w, hlang, hsupp⟩ :=
    capData.exists_word_in_ySupport graphData outer K hK
  rw [hequiv] at hlang
  have hlang' := (shoreLanguage_trans_iff (Equiv.subLeft c) orderR
    (vertexSidePortTangle graphData (shoreKeep cut) outer) w).mp hlang
  have hfun : (fun i => w ((Equiv.subLeft c).symm i)) =
      fun i => w (c - i) := by
    funext i
    rw [subLeft_symm_apply]
  rw [hfun] at hlang'
  exact ⟨fun i => w (c - i), hlang', yCapSupport_reflect c w hsupp⟩

/-- The rotations' symm subtracts the base. -/
theorem addRight_symm_apply :
    ∀ k i : Fin 5, (Equiv.addRight k).symm i = i - k := by
  decide

/-- **Pentagon support on a shore in anti-pinned coordinates**: an order
carrying the successor in the cap convention hosts the pentagon cap
directly, with no coordinate transfer. -/
theorem exists_pentagonSupport_word_of_keep_eq_anti
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hdeletedCard : 6 ≤ (exactCutVertexSide cut).card)
    (keep : V → Prop) (hkeep : shoreKeep cut = keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (orderAnti : Fin 5 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hanti : retainedRegionBoundarySuccessor graphData.toRotationSystem
        keep =
      orderAnti.permCongr (finRotate 5)⁻¹) :
    ∃ w, shoreLanguage orderAnti
        (vertexSidePortTangle graphData keep outer) w ∧
      CAP5WordExtendsAcrossCycle w := by
  subst hkeep
  classical
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hsides := induce_both_sides_connected_of_exactSized
    hconnected hcyclic cut
  set capData := pentagonCapDataOfOrder graphData cut orderAnti
    outer.1 outer.2 with hcapData
  have hkeepEq : capData.keep =
      deletedRegionKeep (exactCutVertexSide cut) :=
    shoreKeep_eq_deletedRegionKeep cut
  have hequiv : capData.crossingBoundaryDartEquiv = orderAnti :=
    crossingBoundaryDartEquiv_pentagonCapDataOfOrder graphData cut orderAnti
      outer.1 outer.2
  have hsucc : retainedRegionBoundarySuccessor graphData.toRotationSystem
      capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹ := by
    rw [hequiv]
    exact hanti
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
  exact ⟨w, hlang, hext⟩

/-- **Y-cap support on a shore in anti-pinned coordinates**, parametric in
the rotation base `k`: distinct seam endpoints at positions `0 + k` and
`1 + k` put the shore language in the Y-support at position `k`. -/
theorem exists_ySupport_word_of_keep_eq_anti
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hdeletedCard : 6 ≤ (exactCutVertexSide cut).card)
    (keep : V → Prop) (hkeep : shoreKeep cut = keep)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (orderAnti : Fin 5 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hanti : retainedRegionBoundarySuccessor graphData.toRotationSystem
        keep =
      orderAnti.permCongr (finRotate 5)⁻¹)
    (k : Fin 5)
    (hseam : graphData.toRotationSystem.vertOf (orderAnti (0 + k)).1.1 ≠
      graphData.toRotationSystem.vertOf (orderAnti (1 + k)).1.1) :
    ∃ w, shoreLanguage orderAnti
        (vertexSidePortTangle graphData keep outer) w ∧
      CAP5YCapSupport k w := by
  subst hkeep
  classical
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hsides := induce_both_sides_connected_of_exactSized
    hconnected hcyclic cut
  set capOrder : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (shoreKeep cut) :=
    (Equiv.addRight k).trans orderAnti with hcapOrder
  have hseam' : graphData.toRotationSystem.vertOf (capOrder 0).1.1 ≠
      graphData.toRotationSystem.vertOf (capOrder 1).1.1 := hseam
  set capData := yCapDataOfOrder graphData cut capOrder outer.1 outer.2
    hseam' with hcapData
  have hkeepEq : capData.keep =
      deletedRegionKeep (exactCutVertexSide cut) :=
    shoreKeep_eq_deletedRegionKeep cut
  have hequiv : capData.crossingBoundaryDartEquiv = capOrder :=
    crossingBoundaryDartEquiv_yCapDataOfOrder graphData cut capOrder
      outer.1 outer.2 hseam'
  have hsucc : retainedRegionBoundarySuccessor graphData.toRotationSystem
      capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹ := by
    rw [hequiv]
    exact anti_pin_of_anti_pin_rotation orderAnti _ k hanti
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
  have hregular : G.IsRegularOfDegree 3 := by
    intro v
    have hcub :=
      (graphData.toRotationSystem_isCubic_iff).mp minimal.spherical.cubic v
    convert hcub using 2
  have hdetour : ∀ removed : InternalDart graphData.toRotationSystem
      capData.keep,
      (capData.internalDetourGraph removed).Reachable
        (graphData.toRotationSystem.vertOf removed.1.1)
        (graphData.toRotationSystem.vertOf
          (graphData.toRotationSystem.alpha removed.1.1)) :=
    fun removed => capData.internalDetourGraph_reachable_of_cyclicFive
      graphData hregular hconnected hcyclic removed
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (exactCutVertexSide cut).card)
  have hleft : ¬ capData.keep a := fun hmem =>
    (mem_exactCutVertexSide_iff cut.compl a).mp hmem
      ((mem_exactCutVertexSide_iff cut a).mp ha)
  have hright : ¬ capData.keep b := fun hmem =>
    (mem_exactCutVertexSide_iff cut.compl b).mp hmem
      ((mem_exactCutVertexSide_iff cut b).mp hb)
  obtain ⟨K, hK⟩ := FiveEdgeCutYCapData.capTaitColorable_of_vertexMinimal
    graphData (exactCutVertexSide cut) minimal capData hsucc
    hretainedConnected hdeletedConnected hkeepEq hretainedAmbient hdetour
    a b hab hleft hright
  obtain ⟨w, hlang, hsupp⟩ :=
    capData.exists_word_in_ySupport graphData outer K hK
  rw [hequiv] at hlang
  have hlang' := (shoreLanguage_trans_iff (Equiv.addRight k) orderAnti
    (vertexSidePortTangle graphData (shoreKeep cut) outer) w).mp hlang
  have hfun : (fun i => w ((Equiv.addRight k).symm i)) =
      fun i => w (i - k) := by
    funext i
    rw [addRight_symm_apply]
  rw [hfun] at hlang'
  exact ⟨fun i => w (i - k), hlang', yCapSupport_rotate k w hsupp⟩

/-- The two complement Finsets of complement cuts agree. -/
theorem exactCutVertexSide_compl_compl (cut : ExactSizedCyclicEdgeCut G 5) :
    exactCutVertexSide cut.compl.compl = exactCutVertexSide cut := by
  ext vertex
  rw [mem_exactCutVertexSide_iff, mem_exactCutVertexSide_iff]
  exact not_not

/-- **The heart on the two shores of a nontrivial five-cut**: the pinned
retained-shore language and any anti-pinned complement-shore language
share a boundary word. -/
theorem exists_common_word_on_shores
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5)
    (hdeletedCard : 6 ≤ (exactCutVertexSide cut).card)
    (hretainedCard : 6 ≤ (exactCutVertexSide cut.compl).card)
    (outerA : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (orderRA : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut)))
    (hpinA : orderRA.permCongr (finRotate 5) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem
        (deletedRegionKeep (exactCutVertexSide cut)))
    (outerB : RetainedDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut.compl)))
    (orderBF : Fin 5 ≃ BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut.compl)))
    (hantiB : retainedRegionBoundarySuccessor graphData.toRotationSystem
        (deletedRegionKeep (exactCutVertexSide cut.compl)) =
      orderBF.permCongr (finRotate 5)⁻¹) :
    ∃ w, shoreLanguage orderRA
        (vertexSidePortTangle graphData
          (deletedRegionKeep (exactCutVertexSide cut)) outerA) w ∧
      shoreLanguage orderBF
        (vertexSidePortTangle graphData
          (deletedRegionKeep (exactCutVertexSide cut.compl)) outerB) w := by
  classical
  have hconnected : G.Connected := by
    rw [← rotationPrimalGraph_toRotationSystem_eq G graphData]
    exact minimal.primalConnected
  have hregular : G.IsRegularOfDegree 3 := by
    intro v
    have hcub :=
      (graphData.toRotationSystem_isCubic_iff).mp minimal.spherical.cubic v
    convert hcub using 2
  have hcc : exactCutVertexSide cut.compl.compl = exactCutVertexSide cut :=
    exactCutVertexSide_compl_compl cut
  -- boundary language of shore A at the pinned order
  have hLA : BoundaryLanguage (shoreLanguage orderRA
      (vertexSidePortTangle graphData
        (deletedRegionKeep (exactCutVertexSide cut)) outerA)) :=
    boundaryLanguage_retainedShore graphData minimal.spherical
      minimal.facesTwoSided hconnected minimal.vertexRotationCyclic
      hcyclic cut outerA orderRA hpinA
  -- boundary language of shore B at the anti-pinned order, through the
  -- reflection joining it to a pinned order
  obtain ⟨orderRB, hpinB⟩ :=
    FiveEdgeCutBoundaryOrder.exists_retainedBoundaryOrder_of_exactCyclicFiveCut
      graphData minimal.spherical minimal.facesTwoSided hconnected
      minimal.vertexRotationCyclic hcyclic cut.compl
  obtain ⟨c₀, hc₀⟩ := exists_reflection_of_pins orderRB orderBF
    (retainedRegionBoundarySuccessor graphData.toRotationSystem
      (deletedRegionKeep (exactCutVertexSide cut.compl)))
    hpinB hantiB
  have hLBpred : shoreLanguage orderBF
      (vertexSidePortTangle graphData
        (deletedRegionKeep (exactCutVertexSide cut.compl)) outerB) =
      fun w => shoreLanguage orderRB
        (vertexSidePortTangle graphData
          (deletedRegionKeep (exactCutVertexSide cut.compl)) outerB)
        (fun i => w (c₀ - i)) := by
    funext w
    apply propext
    rw [hc₀]
    rw [shoreLanguage_trans_iff]
    constructor
    · intro h
      have hfun : (fun i => w ((Equiv.subLeft c₀).symm i)) =
          fun i => w (c₀ - i) := by
        funext i
        rw [subLeft_symm_apply]
      rwa [hfun] at h
    · intro h
      have hfun : (fun i => w ((Equiv.subLeft c₀).symm i)) =
          fun i => w (c₀ - i) := by
        funext i
        rw [subLeft_symm_apply]
      rwa [hfun]
  have hLB : BoundaryLanguage (shoreLanguage orderBF
      (vertexSidePortTangle graphData
        (deletedRegionKeep (exactCutVertexSide cut.compl)) outerB)) := by
    rw [hLBpred]
    exact boundaryLanguage_reflect c₀
      (boundaryLanguage_retainedShore graphData minimal.spherical
        minimal.facesTwoSided hconnected minimal.vertexRotationCyclic
        hcyclic cut.compl outerB orderRB hpinB)
  -- seam certificates on shore A
  have hseamA : ∀ c : Fin 5, c ≠ c - 1 →
      graphData.toRotationSystem.vertOf (orderRA c).1.1 ≠
        graphData.toRotationSystem.vertOf (orderRA (c - 1)).1.1 :=
    fun c hc => vertOf_ne_of_boundaryDart_ne graphData hregular hcyclic cut
      hretainedCard (orderRA c) (orderRA (c - 1)) (orderRA.injective.ne hc)
  -- seam certificates on shore B
  have hseamB : ∀ k : Fin 5, (0 + k : Fin 5) ≠ 1 + k →
      graphData.toRotationSystem.vertOf (orderBF (0 + k)).1.1 ≠
        graphData.toRotationSystem.vertOf (orderBF (1 + k)).1.1 := by
    intro k hk
    apply vertOf_ne_of_boundaryDart_ne graphData hregular hcyclic cut.compl
      (by rw [hcc]; exact hdeletedCard) (orderBF (0 + k)) (orderBF (1 + k))
      (orderBF.injective.ne hk)
  -- the four supports of shore A
  have hAP5 := exists_pentagonSupport_word_of_keep_eq graphData minimal
    hcyclic cut hdeletedCard _ (shoreKeep_eq_deletedRegionKeep cut)
    outerA orderRA hpinA
  have hAY0 := exists_ySupport_word_of_keep_eq graphData minimal
    hcyclic cut hdeletedCard _ (shoreKeep_eq_deletedRegionKeep cut)
    outerA orderRA hpinA 1 (hseamA 1 (by decide))
  have hAY1 := exists_ySupport_word_of_keep_eq graphData minimal
    hcyclic cut hdeletedCard _ (shoreKeep_eq_deletedRegionKeep cut)
    outerA orderRA hpinA 2 (hseamA 2 (by decide))
  have hAY2 := exists_ySupport_word_of_keep_eq graphData minimal
    hcyclic cut hdeletedCard _ (shoreKeep_eq_deletedRegionKeep cut)
    outerA orderRA hpinA 3 (hseamA 3 (by decide))
  rw [(by decide : (1 : Fin 5) - 1 = 0)] at hAY0
  rw [(by decide : (2 : Fin 5) - 1 = 1)] at hAY1
  rw [(by decide : (3 : Fin 5) - 1 = 2)] at hAY2
  -- the four supports of shore B
  have hBP5 := exists_pentagonSupport_word_of_keep_eq_anti graphData minimal
    hcyclic cut.compl hretainedCard _
    (shoreKeep_eq_deletedRegionKeep cut.compl) outerB orderBF hantiB
  have hBY0 := exists_ySupport_word_of_keep_eq_anti graphData minimal
    hcyclic cut.compl hretainedCard _
    (shoreKeep_eq_deletedRegionKeep cut.compl) outerB orderBF hantiB
    0 (hseamB 0 (by decide))
  have hBY1 := exists_ySupport_word_of_keep_eq_anti graphData minimal
    hcyclic cut.compl hretainedCard _
    (shoreKeep_eq_deletedRegionKeep cut.compl) outerB orderBF hantiB
    1 (hseamB 1 (by decide))
  have hBY2 := exists_ySupport_word_of_keep_eq_anti graphData minimal
    hcyclic cut.compl hretainedCard _
    (shoreKeep_eq_deletedRegionKeep cut.compl) outerB orderBF hantiB
    2 (hseamB 2 (by decide))
  exact exists_common_word hLA hLB hAP5 hAY0 hAY1 hAY2 hBP5 hBY0 hBY1 hBY2

end

end FiveCutShoreAssembly

end Mettapedia.GraphTheory.FourColor
