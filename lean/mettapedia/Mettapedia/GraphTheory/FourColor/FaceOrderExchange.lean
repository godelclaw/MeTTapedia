import Mettapedia.GraphTheory.FourColor.FacePathExtension

/-!
# Exchanging the order of two actual facial additions

The common newly exposed edges move from the first step to the second
when the order is exchanged. Strict edge-count inequalities supply both
attachments needed to construct the exchanged intermediate region, with
connected inside and outside. No commuting square is assumed.

If both exchanged steps expose at least three edges, their colourings
extend every original proper colouring. This chooses a construction order
as well as compatible colouring witnesses.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceOrderExchange

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24PrimalCycleFacialBond SimpleGraphDartRotation
open FaceRegionDegree FaceRegionShelling FaceRegionComplement FaceAttachmentCount
open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G) {S R T : Region data} (e : Event S R) (f : Event R T)

/-- Edges first introduced by `e` that also border the face added by `f`. -/
def sharedEdges : Finset G.edgeSet :=
  exposedEdges data e ∩ orbitFaceBoundary data.toRotationSystem f.face

/-- The opposite order retains the same original face identities. -/
structure Exchange where
  middle : Region data
  first : Event S middle
  second : Event middle T
  first_face : first.face = f.face
  second_face : second.face = e.face

theorem face_ne : e.face ≠ f.face := by
  intro h
  apply f.fresh
  rw [e.target, ← h]
  exact Finset.mem_insert_self _ _

include e in
theorem second_fresh : f.face ∉ S.faces := by
  exact fun h => f.fresh (e.subset h)

theorem adj_of_shared {a b : OrbitFace data.toRotationSystem} (hab : a ≠ b)
    {x : G.edgeSet} (ha : x ∈ orbitFaceBoundary data.toRotationSystem a)
    (hb : x ∈ orbitFaceBoundary data.toRotationSystem b) :
    (orbitFaceDualGraph data).Adj a b := by
  exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary data.toRotationSystem) Finset.univ
    (orbitFace_incidence_le_two data.toRotationSystem) hab ha hb

/-- More attachment edges than common new edges forces the second face
to attach to the original region, before the first face is added. -/
theorem second_attaches_to_original
    (h : (sharedEdges data e f).card < (attachmentEdges data f).card) :
    ∃ a ∈ S.faces, (orbitFaceDualGraph data).Adj f.face a := by
  obtain ⟨x, hx, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  obtain ⟨hxR, hxf⟩ := Finset.mem_inter.mp hx
  have hxS : x ∈ edges data.toRotationSystem S.faces := by
    by_contra hxS
    apply hn
    rw [FaceRegionStepBoundary.event_retained_edges data e] at hxR
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
      ⟨(Finset.mem_union.mp hxR).resolve_left hxS, hxS⟩, hxf⟩
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxS
  exact ⟨a, ha, adj_of_shared data
    (fun hfa => second_fresh data e f (hfa.symm ▸ ha)) hxf hxa⟩

/-- An unshared exposed edge of the first face reaches the exterior of
the final region. The neighbour is constructed from the original edge. -/
theorem first_attaches_to_final_exterior
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (h : (sharedEdges data e f).card < (exposedEdges data e).card) :
    ∃ a ∉ T.faces, (orbitFaceDualGraph data).Adj e.face a := by
  obtain ⟨x, hx, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  have hxf : x ∉ orbitFaceBoundary data.toRotationSystem f.face :=
    fun hxf => hn (Finset.mem_inter.mpr ⟨hx, hxf⟩)
  have hxrev : x ∈ attachmentEdges data (reverseEvent data e) := by
    rw [reverse_attachment_edges data ambient e]
    exact hx
  obtain ⟨hxout, hxe⟩ := Finset.mem_inter.mp hxrev
  obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxout
  have haR : a ∉ R.faces := Finset.mem_compl.mp ha
  have hae : e.face ≠ a := by
    intro hea
    apply haR
    rw [e.target, hea]
    exact Finset.mem_insert_self _ _
  have haT : a ∉ T.faces := by
    rw [f.target, Finset.mem_insert]
    rintro (haf | haR')
    · exact hxf (haf ▸ hxa)
    · exact haR haR'
  exact ⟨a, haT, adj_of_shared data hae hxe hxa⟩

/-- Edge counts construct the swapped state and both geometric events,
including connectedness of both shores of the new state. -/
theorem exists_exchange
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hin : (sharedEdges data e f).card < (attachmentEdges data f).card)
    (hout : (sharedEdges data e f).card < (exposedEdges data e).card) :
    Nonempty (Exchange data e f) := by
  obtain ⟨a, ha, hfa⟩ := second_attaches_to_original data e f hin
  obtain ⟨b, hb, heb⟩ := first_attaches_to_final_exterior data e f ambient hout
  have hc : ((insert f.face S.faces : Finset _) : Set _)ᶜ =
      insert e.face (T.faces : Set _)ᶜ := by
    ext x
    simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff,
      Finset.mem_coe, f.target, e.target]
    by_cases hx : x = e.face
    · subst x
      simp [face_ne data e f, e.fresh]
    · simp [hx]
  let U : Region data := {
    faces := insert f.face S.faces
    inside := by
      rw [Finset.coe_insert]
      exact ConnectedBipartitionGrowth.connected_insert_of_adj
        (orbitFaceDualGraph data) S.inside ha hfa
    outside := by
      rw [hc]
      exact ConnectedBipartitionGrowth.connected_insert_of_adj
        (orbitFaceDualGraph data) T.outside hb heb }
  let g : Event S U := ⟨f.face, second_fresh data e f, rfl, a, ha, hfa⟩
  have heU : e.face ∉ U.faces := by
    simp [U, face_ne data e f, e.fresh]
  have hTU : T.faces = insert e.face U.faces := by
    rw [f.target, e.target]
    exact Finset.insert_comm _ _ _
  have hattach : ∃ a ∈ U.faces, (orbitFaceDualGraph data).Adj e.face a := by
    obtain ⟨a, ha, hea⟩ := e.attachment
    exact ⟨a, Finset.mem_insert_of_mem ha, hea⟩
  exact ⟨⟨U, g, ⟨e.face, heU, hTU, hattach⟩, rfl, rfl⟩⟩

/-- The earlier occurrence of the second face gains exactly the common
edges. This is an equality of original edge sets. -/
theorem first_edges (q : Exchange data e f) :
    exposedEdges data q.first = exposedEdges data f ∪ sharedEdges data e f := by
  ext x
  simp only [exposedEdges, q.first_face, sharedEdges,
    FaceRegionStepBoundary.event_retained_edges data e,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

/-- The later occurrence of the first face loses exactly the common
edges. All other newly introduced edges remain unchanged. -/
theorem second_edges (q : Exchange data e f) :
    exposedEdges data q.second =
      exposedEdges data e \ orbitFaceBoundary data.toRotationSystem f.face := by
  ext x
  simp only [exposedEdges, q.second_face,
    FaceRegionStepBoundary.event_retained_edges data q.first, q.first_face,
    Finset.mem_sdiff, Finset.mem_union]
  tauto

theorem first_count (q : Exchange data e f) :
    (exposedEdges data q.first).card =
      (exposedEdges data f).card + (sharedEdges data e f).card := by
  rw [first_edges data e f q]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro x hxF hxK
  exact (Finset.mem_sdiff.mp hxF).2
    (exposed_mem_new data e (Finset.mem_inter.mp hxK).1)

theorem second_count (q : Exchange data e f) :
    (exposedEdges data q.second).card + (sharedEdges data e f).card =
      (exposedEdges data e).card := by
  rw [second_edges data e f q]
  exact Finset.card_sdiff_add_card_inter _ _

/-- The swapped construction extends any original proper colouring
when its two exact edge budgets are at least three. -/
theorem extends_by_exchange
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hin : (sharedEdges data e f).card < (attachmentEdges data f).card)
    (hfirst : 3 ≤ (exposedEdges data f).card + (sharedEdges data e f).card)
    (hsecond : (sharedEdges data e f).card + 3 ≤ (exposedEdges data e).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ q : Exchange data e f, ∃ b c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem q.middle.faces) b ∧
      (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
      (∀ x ∈ edges data.toRotationSystem q.middle.faces, c x = b x) := by
  obtain ⟨q⟩ := exists_exchange data e f ambient hin (by omega)
  have hg : 3 ≤ (exposedEdges data q.first).card := by
    rw [first_count data e f q]
    exact hfirst
  have hh : 3 ≤ (exposedEdges data q.second).card := by
    have hcount := second_count data e f q
    omega
  obtain ⟨b, hb, hba⟩ := FacePathExtension.extends_of_three_le data q.first ambient hg a ha
  obtain ⟨c, hc, hcb⟩ := FacePathExtension.extends_of_three_le data q.second ambient hh b hb
  exact ⟨q, b, c, hb, hba, hc, hcb⟩

/-- Restrict the final witness back to the original intermediate region.
Thus a successful reordered construction also supplies jointly chosen
compatible witnesses for the original two-event route. -/
theorem extends_original_pair
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hin : (sharedEdges data e f).card < (attachmentEdges data f).card)
    (hfirst : 3 ≤ (exposedEdges data f).card + (sharedEdges data e f).card)
    (hsecond : (sharedEdges data e f).card + 3 ≤ (exposedEdges data e).card)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ b c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
      (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
      (∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) := by
  obtain ⟨q, b, c, _, hba, hc, hcb⟩ :=
    extends_by_exchange data e f ambient hin hfirst hsecond a ha
  have hRT : edges data.toRotationSystem R.faces ⊆ edges data.toRotationSystem T.faces := by
    rw [FaceRegionStepBoundary.event_retained_edges data f]
    exact Finset.subset_union_left
  have hSU : edges data.toRotationSystem S.faces ⊆
      edges data.toRotationSystem q.middle.faces := by
    rw [FaceRegionStepBoundary.event_retained_edges data q.first]
    exact Finset.subset_union_left
  exact ⟨c, c, proper_of_subset hRT hc,
    fun x hx => (hcb x (hSU hx)).trans (hba x hx), hc, fun _ _ => rfl⟩

/-- One shared edge turns a four-or-more / two-edge pair into two
three-or-more-edge additions. The second face must also touch the
original patch, here guaranteed by at least two attachment edges. -/
theorem extends_four_two_pair
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hshared : (sharedEdges data e f).card = 1)
    (hattach : 2 ≤ (attachmentEdges data f).card)
    (hfour : 4 ≤ (exposedEdges data e).card)
    (htwo : (exposedEdges data f).card = 2)
    (a : G.edgeSet → Fin 3)
    (ha : Proper data.toRotationSystem.endpoints (edges data.toRotationSystem S.faces) a) :
    ∃ b c : G.edgeSet → Fin 3,
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem R.faces) b ∧
      (∀ x ∈ edges data.toRotationSystem S.faces, b x = a x) ∧
      Proper data.toRotationSystem.endpoints (edges data.toRotationSystem T.faces) c ∧
      (∀ x ∈ edges data.toRotationSystem R.faces, c x = b x) := by
  exact extends_original_pair data e f ambient (by omega) (by omega) (by omega) a ha

end
end Mettapedia.GraphTheory.FourColor.FaceOrderExchange
