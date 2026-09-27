import Mettapedia.GraphTheory.FourColor.FaceAttachmentCount

/-!
# Reversing a facial construction across its complementary shore

Complementing both regions reverses a one-face event. The attachment of
the reversed event is exactly the newly exposed edge set of the original
event. Its vertex count therefore follows from the same disk Euler law.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionComplement

open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24PrimalCycleFacialBond
open SimpleGraphDartRotation FaceRegionDegree FaceRegionShelling
open PhysicalForkCodeCut FaceAttachmentCount

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

local instance : DecidableEq (OrbitFace data.toRotationSystem) :=
  orbitFaceDecidableEq data.toRotationSystem

local instance : Fintype (OrbitFace data.toRotationSystem) :=
  orbitFaceFintype data.toRotationSystem

def complement (S : Region data) : Region data where
  faces := S.facesᶜ
  inside := by
    have he : ((S.facesᶜ : Finset (OrbitFace data.toRotationSystem)) :
        Set (OrbitFace data.toRotationSystem)) = (S.faces : Set (OrbitFace data.toRotationSystem))ᶜ :=
      Finset.coe_compl S.faces
    rw [he]
    exact S.outside
  outside := by
    have he : ((S.facesᶜ : Finset (OrbitFace data.toRotationSystem)) :
        Set (OrbitFace data.toRotationSystem)) = (S.faces : Set (OrbitFace data.toRotationSystem))ᶜ :=
      Finset.coe_compl S.faces
    rw [he, compl_compl]
    exact S.inside

theorem complement_involutive (S : Region data) : complement data (complement data S) = S := by
  apply Region.ext
  exact compl_compl S.faces

theorem complement_target {S R : Region data} (e : Event S R) :
    (complement data S).faces = insert e.face (complement data R).faces := by
  ext f
  simp only [complement, Finset.mem_compl, Finset.mem_insert, e.target]
  by_cases hf : f = e.face
  · subst f
    simp [e.fresh]
  · simp [hf]

/-- The complementary growth event is derived solely from the two actual
connected shores and the original event. -/
def reverseEvent {S R : Region data} (e : Event S R) :
    Event (complement data R) (complement data S) where
  face := e.face
  fresh := by simp [complement, e.target]
  target := complement_target data e
  attachment := by
    have hsub : ((complement data R).faces : Set (OrbitFace data.toRotationSystem)) ⊂
        ((complement data S).faces : Set (OrbitFace data.toRotationSystem)) := by
      rw [complement_target data e]
      simp only [Finset.coe_insert]
      apply Set.ssubset_insert
      simp [complement, e.target]
    obtain ⟨y, hy, hyn, a, ha, hya⟩ := ConnectedBipartitionGrowth.exists_adjacent_outside
      (orbitFaceDualGraph data) (complement data R).inside (complement data S).inside hsub
    have heq : y = e.face := by
      rw [complement_target data e] at hy
      exact (Finset.mem_insert.mp hy).resolve_right hyn
    exact ⟨a, ha, heq ▸ hya⟩

/-- Original face edges not present in the old patch. -/
def exposedEdges {S R : Region data} (e : Event S R) : Finset G.edgeSet :=
  orbitFaceBoundary data.toRotationSystem e.face \ edges data.toRotationSystem S.faces

theorem exposed_mem_new {S R : Region data} (e : Event S R)
    {a : G.edgeSet} (ha : a ∈ exposedEdges data e) : a ∈ edges data.toRotationSystem R.faces := by
  rw [FaceRegionStepBoundary.event_retained_edges data e]
  exact Finset.mem_union_right _ (Finset.mem_sdiff.mp ha).1

theorem exposed_alpha_outside
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {S R : Region data} (e : Event S R) (d : data.toRotationSystem.D)
    (hdf : dartOrbitFace data.toRotationSystem d = e.face)
    (hd : data.toRotationSystem.edgeOf d ∈ exposedEdges data e) :
    dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉ R.faces := by
  have hn := (Finset.mem_sdiff.mp hd).2
  rw [edge_mem_iff] at hn
  rw [e.target, Finset.mem_insert]
  rintro (h | h)
  · exact GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      data.toRotationSystem ambient d (hdf.trans h.symm)
  · exact hn (Or.inr h)

theorem reverse_attachment_edges
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {S R : Region data} (e : Event S R) :
    attachmentEdges data (reverseEvent data e) = exposedEdges data e := by
  ext a
  simp only [attachmentEdges, reverseEvent, complement, exposedEdges,
    Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨haR, haf⟩
    obtain ⟨d, hd, hda⟩ := (mem_orbitFaceBoundary_iff data.toRotationSystem e.face a).mp haf
    have hdf := (mem_orbitFaceDarts_iff _ _ _).mp hd
    rw [← hda, edge_mem_iff, hdf] at haR
    have halpha : dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉ R.faces := by
      simpa only [Finset.mem_compl, e.target, Finset.mem_insert, true_or, not_true_eq_false,
        false_or] using haR
    refine ⟨haf, ?_⟩
    rw [← hda, edge_mem_iff, hdf]
    rintro (h | h)
    · exact e.fresh h
    · exact halpha (e.subset h)
  · rintro ⟨haf, haS⟩
    obtain ⟨d, hd, hda⟩ := (mem_orbitFaceBoundary_iff data.toRotationSystem e.face a).mp haf
    have hdf := (mem_orbitFaceDarts_iff _ _ _).mp hd
    rw [← hda, edge_mem_iff, hdf] at haS
    have htwo := GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
      data.toRotationSystem ambient d
    refine ⟨?_, haf⟩
    rw [← hda, edge_mem_iff]
    right
    simp only [Finset.mem_compl, e.target, Finset.mem_insert]
    rintro (h | h)
    · exact htwo (hdf.trans h.symm)
    · exact haS (Or.inr h)

theorem exposed_count (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {S R : Region data} (e : Event S R) :
    (touched data.toRotationSystem (exposedEdges data e)).card = (exposedEdges data e).card + 1 := by
  rw [← reverse_attachment_edges data ambient e]
  exact attachment_count data ambient (reverseEvent data e)

theorem exposed_nonempty (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    {S R : Region data} (e : Event S R) : (exposedEdges data e).Nonempty := by
  rw [← reverse_attachment_edges data ambient e]
  exact attachment_nonempty data ambient (reverseEvent data e)

end
end Mettapedia.GraphTheory.FourColor.FaceRegionComplement
