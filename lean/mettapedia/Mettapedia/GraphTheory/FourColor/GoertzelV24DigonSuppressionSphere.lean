import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonFirstReturn
import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonSuppression
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk

/-!
# Digon suppression preserves the sphere

The complementary cap of a digon's two-edge cut loses exactly one face — the
digon itself — because the ambient facial walk leaving either exposed
half-edge returns through the other after a detour of length three, and the
digon face is the only ambient face buried entirely in the deleted region.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24FaceDualConnectedness
open GoertzelV24RotationEdgeBridge
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrderedCutFirstReturnCap
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceEuler
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable section

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

/-! ## Naming the two exposed half-edges -/

/-- The retained orientation of `outerU` is `a'`. -/
theorem eq_a'_of_edgeOf_outerU (hD : D.WellFormed RS) {dart : RS.D}
    (hedge : RS.edgeOf dart = D.outerU) (hvert : RS.vertOf dart ≠ D.u) :
    dart = D.a' hD := by
  have hd : dart ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 hedge
  have hp : D.pₐ hD ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 (D.edgeOf_pₐ hD)
  rw [RS.dartsOn_eq_pair_of_mem hp, D.alpha_pₐ hD] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact absurd (D.vertOf_pₐ hD) hvert
  · rfl

/-- The retained orientation of `outerV` is `b'`. -/
theorem eq_b'_of_edgeOf_outerV (hD : D.WellFormed RS) {dart : RS.D}
    (hedge : RS.edgeOf dart = D.outerV) (hvert : RS.vertOf dart ≠ D.v) :
    dart = D.b' hD := by
  have hd : dart ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 hedge
  have hq : D.qᵦ hD ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 (D.edgeOf_qᵦ hD)
  rw [RS.dartsOn_eq_pair_of_mem hq, D.alpha_qᵦ hD] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact absurd (D.vertOf_qᵦ hD) hvert
  · rfl

variable (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
  (hfree : EdgeBridgeFree RS) (houter : D.vFar hD ≠ D.u)

/-- The retained predicate of the complementary cap deletes exactly the two
digon vertices. -/
theorem complement_keep_iff (vertex : V) :
    ¬ (D.twoEdgeCut hD hCubic hfree houter).complementData.keep vertex ↔
      (vertex = D.u ∨ vertex = D.v) := by
  change ¬ (vertex ∈ (D.side)ᶜ) ↔ _
  rw [Finset.mem_compl, not_not]
  simp [side]

theorem complement_keep_a' :
    (D.twoEdgeCut hD hCubic hfree houter).complementData.keep
      (RS.vertOf (D.a' hD)) := by
  by_contra hcon
  rcases (D.complement_keep_iff hD hCubic hfree houter _).1 hcon with h | h
  · exact D.uFar_ne_u hD h
  · exact D.uFar_ne_v hD hCubic houter h

theorem complement_keep_b' :
    (D.twoEdgeCut hD hCubic hfree houter).complementData.keep
      (RS.vertOf (D.b' hD)) := by
  by_contra hcon
  rcases (D.complement_keep_iff hD hCubic hfree houter _).1 hcon with h | h
  · exact houter h
  · exact D.vFar_ne_v hD h

/-! ## The cap loses exactly the digon face -/

/-- The ambient rotation system of the complementary cap: the map itself,
rooted at an exposed dart. -/
def cutAmbient : RotationSystem V E :=
  (D.twoEdgeCut hD hCubic hfree houter).complementRootedRotationSystem

/-- The complementary side of the digon's two-edge cut, as cap data. -/
def cutData : TwoEdgeCutSideData (D.cutAmbient hD hCubic hfree houter) :=
  (D.twoEdgeCut hD hCubic hfree houter).complementData

/-- **Digon suppression destroys exactly one face.** -/
theorem card_orbitFace_suppressed_add_one
    (hrotation : VertexRotationCyclic RS) (hface : D.HasExactDigonFace hD) :
    Fintype.card (OrbitFace (D.suppressed hD hCubic hfree houter)) + 1 =
      Fintype.card (OrbitFace RS) := by
  classical
  have ha : (D.cutData hD hCubic hfree houter).keep (RS.vertOf (D.a' hD)) :=
    D.complement_keep_a' hD hCubic hfree houter
  have hb : (D.cutData hD hCubic hfree houter).keep (RS.vertOf (D.b' hD)) :=
    D.complement_keep_b' hD hCubic hfree houter
  have hkeep : ∀ vertex,
      ¬ (D.cutData hD hCubic hfree houter).keep vertex ↔
        (vertex = D.u ∨ vertex = D.v) :=
    D.complement_keep_iff hD hCubic hfree houter
  have hleftDart : ∀ step : Fin 1,
      (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).leftCrossing
        (D.cutData hD hCubic hfree houter).leftCrosses step).1.1.1 =
        D.a' hD := by
    intro step
    refine D.eq_a'_of_edgeOf_outerU hD
      (orderedBoundaryDart_edgeOf (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).leftCrossing
        (D.cutData hD hCubic hfree houter).leftCrosses step) ?_
    intro hu
    exact ((hkeep _).2 (Or.inl hu))
      (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).leftCrossing
        (D.cutData hD hCubic hfree houter).leftCrosses step).1.1.2
  have hrightDart : ∀ step : Fin 1,
      (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).rightCrossing
        (D.cutData hD hCubic hfree houter).rightCrosses step).1.1.1 =
        D.b' hD := by
    intro step
    refine D.eq_b'_of_edgeOf_outerV hD
      (orderedBoundaryDart_edgeOf (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).rightCrossing
        (D.cutData hD hCubic hfree houter).rightCrosses step) ?_
    intro hv
    exact ((hkeep _).2 (Or.inr hv))
      (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).rightCrossing
        (D.cutData hD hCubic hfree houter).rightCrosses step).1.1.2
  have hleftReturn : ∀ step : Fin 1,
      (nextHit (D.cutAmbient hD hCubic hfree houter).phi
        (RetainedDartMark (D.cutAmbient hD hCubic hfree houter)
          (D.cutData hD hCubic hfree houter).keep)
        (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
          (D.cutData hD hCubic hfree houter).keep
          (D.cutData hD hCubic hfree houter).leftCrossing
          (D.cutData hD hCubic hfree houter).leftCrosses step).1.1).1 =
        (D.cutAmbient hD hCubic hfree houter).rho
          (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
            (D.cutData hD hCubic hfree houter).keep
            (D.cutData hD hCubic hfree houter).rightCrossing
            (D.cutData hD hCubic hfree houter).rightCrosses step).1.1.1 := by
    intro step
    have hsub : (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).leftCrossing
        (D.cutData hD hCubic hfree houter).leftCrosses step).1.1 =
        (⟨D.a' hD, ha⟩ :
          {point // RetainedDartMark (D.cutAmbient hD hCubic hfree houter)
            (D.cutData hD hCubic hfree houter).keep point}) :=
      Subtype.ext (hleftDart step)
    rw [hsub, hrightDart step]
    exact D.nextHit_a'_eq hD hCubic hrotation hface hkeep ha hb
  have hrightReturn : ∀ step : Fin 1,
      (nextHit (D.cutAmbient hD hCubic hfree houter).phi
        (RetainedDartMark (D.cutAmbient hD hCubic hfree houter)
          (D.cutData hD hCubic hfree houter).keep)
        (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
          (D.cutData hD hCubic hfree houter).keep
          (D.cutData hD hCubic hfree houter).rightCrossing
          (D.cutData hD hCubic hfree houter).rightCrosses step).1.1).1 =
        (D.cutAmbient hD hCubic hfree houter).rho
          (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
            (D.cutData hD hCubic hfree houter).keep
            (D.cutData hD hCubic hfree houter).leftCrossing
            (D.cutData hD hCubic hfree houter).leftCrosses step).1.1.1 := by
    intro step
    have hsub : (orderedBoundaryDart (D.cutAmbient hD hCubic hfree houter)
        (D.cutData hD hCubic hfree houter).keep
        (D.cutData hD hCubic hfree houter).rightCrossing
        (D.cutData hD hCubic hfree houter).rightCrosses step).1.1 =
        (⟨D.b' hD, hb⟩ :
          {point // RetainedDartMark (D.cutAmbient hD hCubic hfree houter)
            (D.cutData hD hCubic hfree houter).keep point}) :=
      Subtype.ext (hrightDart step)
    rw [hsub, hleftDart step]
    exact D.nextHit_b'_eq hD hCubic hrotation hface hkeep ha hb
  have hgeneric := card_orbitFace_cap_add_card_nonHitOrbit
    (D.cutAmbient hD hCubic hfree houter)
    (D.cutData hD hCubic hfree houter).keep
    (D.cutData hD hCubic hfree houter).leftCrossing
    (D.cutData hD hCubic hfree houter).rightCrossing
    (D.cutData hD hCubic hfree houter).leftCrosses
    (D.cutData hD hCubic hfree houter).rightCrosses
    (D.cutData hD hCubic hfree houter).leftCrossing_injective
    (D.cutData hD hCubic hfree houter).rightCrossing_injective
    (D.cutData hD hCubic hfree houter).boundaryCover
    (D.cutData hD hCubic hfree houter).cutsDisjoint
    (D.cutData hD hCubic hfree houter).outer_mem
    (D.cutData hD hCubic hfree houter).seamEndpoints
    hleftReturn hrightReturn
  have hburied : Fintype.card
      (NonHitOrbit (D.cutAmbient hD hCubic hfree houter).phi
        (RetainedDartMark (D.cutAmbient hD hCubic hfree houter)
          (D.cutData hD hCubic hfree houter).keep)) = 1 :=
    D.card_nonHitOrbit_eq_one hD hCubic hrotation hface hkeep ha hb
  rw [hburied] at hgeneric
  exact hgeneric

/-! ## The cap loses exactly three edges -/

/-- The edges without a fully retained dart fiber are exactly the four edges
of the digon patch. -/
theorem removedEdge_iff (edge : E) :
    (¬ ∃ dart : InternalDart RS (D.cutData hD hCubic hfree houter).keep,
        RS.edgeOf dart.1.1 = edge) ↔
      edge ∈ ({D.e, D.f, D.outerU, D.outerV} : Finset E) := by
  classical
  have hkeep := D.complement_keep_iff hD hCubic hfree houter
  constructor
  · intro hno
    by_contra hnot
    apply hno
    obtain ⟨dart, hdart⟩ := RS.dartsOn_nonempty edge
    have hedge : RS.edgeOf dart = edge := RS.mem_dartsOn.mp hdart
    have hbase : ∀ base : RS.D, RS.edgeOf base = edge →
        (D.cutData hD hCubic hfree houter).keep (RS.vertOf base) := by
      intro base hbaseEdge
      by_contra hbaseNot
      apply hnot
      have hincident : edge ∈ RS.incidentEdges D.u ∨
          edge ∈ RS.incidentEdges D.v := by
        rcases (hkeep _).1 hbaseNot with hu | hv
        · exact Or.inl (RS.mem_incidentEdges_iff.2 ⟨base, hbaseEdge, hu⟩)
        · exact Or.inr (RS.mem_incidentEdges_iff.2 ⟨base, hbaseEdge, hv⟩)
      rcases D.eq_of_mem_incident hD hincident with h | h | h | h <;>
        simp [h]
    refine ⟨⟨⟨dart, hbase dart hedge⟩, ?_⟩, hedge⟩
    exact hbase (RS.alpha dart) ((RS.edge_alpha dart).trans hedge)
  · rintro hmem ⟨⟨⟨dart, hretained⟩, hinternal⟩, hdart⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hpair : ∀ (named opposite : RS.D), RS.alpha named = opposite →
        RS.edgeOf named = edge →
        dart = named ∨ dart = opposite := by
      intro named opposite hopposite hnamed
      have hmemNamed : named ∈ RS.dartsOn edge := RS.mem_dartsOn.2 hnamed
      have hmemDart : dart ∈ RS.dartsOn edge := RS.mem_dartsOn.2 hdart
      rw [RS.dartsOn_eq_pair_of_mem hmemNamed, hopposite] at hmemDart
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmemDart
    have hdeleted : ∀ base : RS.D,
        (RS.vertOf base = D.u ∨ RS.vertOf base = D.v) →
        ¬ (D.cutData hD hCubic hfree houter).keep (RS.vertOf base) :=
      fun base hbase => (hkeep _).2 hbase
    rcases hmem with rfl | rfl | rfl | rfl
    · rcases hpair (D.p₁ hD) (D.q₁ hD) (D.alpha_p₁ hD) (D.edgeOf_p₁ hD)
        with rfl | rfl
      · exact hdeleted _ (Or.inl (D.vertOf_p₁ hD)) hretained
      · exact hdeleted _ (Or.inr (D.vertOf_q₁ hD)) hretained
    · rcases hpair (D.p₂ hD) (D.q₂ hD) (D.alpha_p₂ hD) (D.edgeOf_p₂ hD)
        with rfl | rfl
      · exact hdeleted _ (Or.inl (D.vertOf_p₂ hD)) hretained
      · exact hdeleted _ (Or.inr (D.vertOf_q₂ hD)) hretained
    · rcases hpair (D.pₐ hD) (D.a' hD) (D.alpha_pₐ hD) (D.edgeOf_pₐ hD)
        with rfl | rfl
      · exact hdeleted _ (Or.inl (D.vertOf_pₐ hD)) hretained
      · exact hdeleted _ (Or.inl (by rw [D.alpha_a' hD, D.vertOf_pₐ hD]))
          hinternal
    · rcases hpair (D.qᵦ hD) (D.b' hD) (D.alpha_qᵦ hD) (D.edgeOf_qᵦ hD)
        with rfl | rfl
      · exact hdeleted _ (Or.inr (D.vertOf_qᵦ hD)) hretained
      · exact hdeleted _ (Or.inr (by rw [D.alpha_b' hD, D.vertOf_qᵦ hD]))
          hinternal

/-- Suppression removes four edges and creates one. -/
theorem card_retainedInternalEdge_add_four :
    Fintype.card
        (RetainedInternalEdge RS
          (D.cutData hD hCubic hfree houter).keep) + 4 = Fintype.card E := by
  classical
  have hsplit := card_retainedInternalEdge_add_card_removedEdge RS
      (D.cutData hD hCubic hfree houter).keep
  have hremoved : Fintype.card
      (RemovedEdge RS (D.cutData hD hCubic hfree houter).keep) = 4 := by
    have hU := D.edges_u_pairwise_ne hD hCubic
    have hV := D.edges_v_pairwise_ne hD hCubic
    have hUV := D.outerU_ne_outerV hD houter
    have hcard : ({D.e, D.f, D.outerU, D.outerV} : Finset E).card = 4 := by
      have h3 : D.outerU ∉ ({D.outerV} : Finset E) := by simpa using hUV
      have h2 : D.f ∉ ({D.outerU, D.outerV} : Finset E) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hU.2.1 h.symm, fun h => hV.2.1 h.symm⟩
      have h1 : D.e ∉ ({D.f, D.outerU, D.outerV} : Finset E) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hU.2.2, fun h => hU.1 h.symm, fun h => hV.1 h.symm⟩
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
    have hequiv : RemovedEdge RS (D.cutData hD hCubic hfree houter).keep ≃
        {edge : E // edge ∈ ({D.e, D.f, D.outerU, D.outerV} : Finset E)} :=
      Equiv.subtypeEquivRight (D.removedEdge_iff hD hCubic hfree houter)
    rw [Fintype.card_congr hequiv, Fintype.card_coe, hcard]
  omega

/-- Suppression leaves three fewer edges. -/
theorem card_suppressed_edge :
    Fintype.card (D.cutData hD hCubic hfree houter).CapEdge + 3 =
      Fintype.card E := by
  have hedges : Fintype.card (D.cutData hD hCubic hfree houter).CapEdge =
      Fintype.card (RetainedInternalEdge RS
        (D.cutData hD hCubic hfree houter).keep) + 1 :=
    card_orderedCutRetainedVertexRotationSystem_edges
      (D.cutAmbient hD hCubic hfree houter)
      (D.cutData hD hCubic hfree houter).keep
      (D.cutData hD hCubic hfree houter).leftCrossing
      (D.cutData hD hCubic hfree houter).rightCrossing
      (D.cutData hD hCubic hfree houter).leftCrosses
      (D.cutData hD hCubic hfree houter).rightCrosses
      (D.cutData hD hCubic hfree houter).leftCrossing_injective
      (D.cutData hD hCubic hfree houter).rightCrossing_injective
      (D.cutData hD hCubic hfree houter).boundaryCover
      (D.cutData hD hCubic hfree houter).cutsDisjoint
      (D.cutData hD hCubic hfree houter).outer_mem
      (D.cutData hD hCubic hfree houter).seamEndpoints
  have hsplit := D.card_retainedInternalEdge_add_four hD hCubic hfree houter
  omega

/-! ## Digon suppression preserves the spherical cubic class -/

/-- **Suppressing a digon keeps the map on the sphere.**  Two vertices, three
edges and one face disappear together. -/
theorem suppressed_orbitSphericalCubicMapData
    (hrotation : VertexRotationCyclic RS) (hface : D.HasExactDigonFace hD)
    (hsphere : OrbitSphericalCubicMapData RS) :
    OrbitSphericalCubicMapData (D.suppressed hD hCubic hfree houter) where
  cubic := D.suppressed_isCubic hD hCubic hfree houter
  euler := by
    show (Fintype.card (D.cutData hD hCubic hfree houter).CapVertex : Int) -
        Fintype.card (D.cutData hD hCubic hfree houter).CapEdge +
        Fintype.card (OrbitFace (D.suppressed hD hCubic hfree houter)) = 2
    have hV : Fintype.card (D.cutData hD hCubic hfree houter).CapVertex + 2 =
        Fintype.card V := D.card_suppressed_vertex hD hCubic hfree houter
    have hE := D.card_suppressed_edge hD hCubic hfree houter
    have hF : Fintype.card
        (OrbitFace (D.suppressed hD hCubic hfree houter)) + 1 =
        Fintype.card (OrbitFace RS) :=
      D.card_orbitFace_suppressed_add_one hD hCubic hfree houter hrotation
        hface
    have hEuler := hsphere.euler
    omega

end DigonPatchData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
