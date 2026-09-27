import Mettapedia.GraphTheory.FourColor.FaceRegionStepBoundary

/-!
# Source maps and distance bands admit facial construction routes

Any chosen face can grow, one original face at a time, to all faces except
a distinct designated outer face. Every intermediate region has connected
complement and realizes as an actual plane patch. The final region retains
every original edge, so the construction covers the source graph.

Nested complete distance contours admit the same refinement. No ordering,
intermediate disks, or colouring witnesses are supplied as hypotheses.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionSweep

open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality GoertzelV24BridgelessFaceTwoSided
open SimpleGraphDartRotation FaceRegionShelling FaceRegionDegree
open Mettapedia.GSLT.Ultrainfinite FaceDistanceFrontiers

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

private theorem singleton_connected (f : OrbitFace data.toRotationSystem) :
    ((orbitFaceDualGraph data).induce ({f} : Set _)).Connected := by
  let : Nonempty ({f} : Set (OrbitFace data.toRotationSystem)) := ⟨⟨f, rfl⟩⟩
  exact SimpleGraph.Connected.of_subsingleton

/-- A single original face, with both sides connected by source geometry. -/
def single (f : OrbitFace data.toRotationSystem) : Region data where
  faces := {f}
  inside := by
    rw [Finset.coe_singleton]
    exact singleton_connected data f
  outside := by
    rw [Finset.coe_singleton]
    exact FaceDualNoCutVertex.delete_face_connected data ambient f

/-- All faces except the designated exterior face. -/
def coSingle (outer : OrbitFace data.toRotationSystem) : Region data := by
  let F : Finset (OrbitFace data.toRotationSystem) := Finset.univ.erase outer
  have hcoe : (F : Set _) = ({outer} : Set _)ᶜ := by ext f; simp [F]
  refine ⟨F, ?_, ?_⟩
  · rw [hcoe]
    exact FaceDualNoCutVertex.delete_face_connected data ambient outer
  · rw [hcoe, compl_compl]
    exact singleton_connected data outer

/-- A full source sweep exists with every intermediate patch certified. -/
theorem exists_sweep (first outer : OrbitFace data.toRotationSystem) (hne : first ≠ outer) :
    Nonempty (Route Event (single data ambient first) (coSingle data ambient outer)) := by
  apply exists_route data ambient
  change ({first} : Finset _) ⊆ Finset.univ.erase outer
  simpa using hne

/-- Every source map supplies the two distinct endpoint faces itself. -/
theorem source_sweep :
    Nonempty (Route Event
      (single data ambient (dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha data.toRotationSystem.outer)))
      (coSingle data ambient (dartOrbitFace data.toRotationSystem data.toRotationSystem.outer))) := by
  apply exists_sweep data ambient
  exact (BridgelessSphericalCubicMapData.orbitFacesTwoSided
    data.toRotationSystem ambient data.toRotationSystem.outer).symm

/-- The route adds precisely the faces other than its first and outer faces. -/
theorem sweep_length (first outer : OrbitFace data.toRotationSystem)
    (p : Route Event (single data ambient first) (coSingle data ambient outer)) :
    p.length + 2 = Fintype.card (OrbitFace data.toRotationSystem) := by
  have h := route_length p
  have hc := Finset.card_erase_add_one (s := (Finset.univ : Finset (OrbitFace data.toRotationSystem)))
    (Finset.mem_univ outer)
  change p.length + ({first} : Finset _).card = (Finset.univ.erase outer).card at h
  simp only [Finset.card_singleton] at h
  rw [Finset.card_univ] at hc
  omega

/-- With only one face outside, every original edge has a selected side. -/
theorem coSingle_retains_all_edges (outer : OrbitFace data.toRotationSystem) :
    edges data.toRotationSystem (coSingle data ambient outer).faces = Finset.univ := by
  have htwo := BridgelessSphericalCubicMapData.orbitFacesTwoSided data.toRotationSystem ambient
  apply Finset.eq_univ_of_forall
  intro e
  obtain ⟨d, hd⟩ := data.toRotationSystem.dartsOn_nonempty e
  have he := (data.toRotationSystem.mem_dartsOn).mp hd
  rw [← he, edge_mem_iff]
  change dartOrbitFace data.toRotationSystem d ∈ Finset.univ.erase outer ∨
    dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈ Finset.univ.erase outer
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  by_cases hf : dartOrbitFace data.toRotationSystem d = outer
  · right
    intro hg
    exact htwo d (hf.trans hg.symm)
  · exact Or.inl hf

/-- No original vertex is dropped at the end of the source sweep. -/
theorem coSingle_retains_all_vertices (outer : OrbitFace data.toRotationSystem) :
    PhysicalForkCodeCut.touched data.toRotationSystem
      (edges data.toRotationSystem (coSingle data ambient outer).faces) = Finset.univ := by
  rw [coSingle_retains_all_edges data ambient outer]
  apply Finset.eq_univ_of_forall
  intro v
  have hpos : 0 < (data.toRotationSystem.dartsAt v).card := by
    rw [ambient.spherical.cubic v]
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
  exact PhysicalForkCodeCut.mem_touched.mpr
    ⟨d, (Finset.mem_filter.mp hd).2, Finset.mem_univ _⟩

/-- The actual component beyond a distance contour, as an operational state. -/
def deep (root far : OrbitFace data.toRotationSystem) (depth : ℕ)
    (hdepth : depth < (orbitFaceDualGraph data).dist root far) : Region data := by
  let F := Finset.univ.filter fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far depth
  have hcoe : (F : Set _) = deepRegion (orbitFaceDualGraph data) root far depth := by
    ext f
    simp [F]
  refine ⟨F, ?_, ?_⟩
  · rw [hcoe]
    exact deepRegion_connected _ root far depth hdepth
  · rw [hcoe]
    exact deepRegion_compl_connected _ root far (orbitFaceDualGraph_connected data ambient) depth

/-- Every band between nested complete distance contours refines into
single-face operations with connected sides throughout. -/
theorem exists_deep_route (root far : OrbitFace data.toRotationSystem)
    (near farDepth : ℕ) (horder : near ≤ farDepth)
    (hdepth : farDepth < (orbitFaceDualGraph data).dist root far) :
    Nonempty (Route Event (deep data ambient root far farDepth hdepth)
      (deep data ambient root far near (lt_of_le_of_lt horder hdepth))) := by
  apply exists_route data ambient
  intro f hf
  change f ∈ Finset.univ.filter (fun f => f ∈ deepRegion (orbitFaceDualGraph data) root far near)
  have hh : f ∈ deepRegion (orbitFaceDualGraph data) root far farDepth :=
    (Finset.mem_filter.mp hf).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, deepRegion_antitone _ root far horder hh⟩

end
end Mettapedia.GraphTheory.FourColor.FaceRegionSweep
