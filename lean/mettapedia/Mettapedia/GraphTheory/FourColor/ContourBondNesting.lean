import Mettapedia.GraphTheory.FourColor.SphericalContourMesh

/-!
# Connected bonds in separated depth windows must nest

A connected shore avoiding a mixed frontier cannot contain both a vertex
touching that face region and a vertex not touching it. Apply this to both
shores of a contour bond. The entire earlier outside region is retained
and the entire later touched region is excluded. Bonds in separated depth
windows therefore nest strictly, regardless of how each bond was chosen.

No minimum-cut tie breaking or uncrossing hypothesis is needed here. The
conclusion concerns vertex shores; it does not yet give the local majority
conditions of the compositional nodes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FaceDistanceFrontiers

variable {F V : Type*}

theorem connected_shore_avoids_touches (G : SimpleGraph V)
    (incident : V → Set F) (region : Set F)
    (hshare : ∀ u v, G.Adj u v → ∃ f, f ∈ incident u ∧ f ∈ incident v)
    {S : Set V} (hS : (G.induce S).Connected)
    (hboundary : ∀ v, Mixed incident region v → v ∉ S)
    {a : V} (ha : a ∈ S) (haR : ¬ Touches incident region a) :
    ∀ v ∈ S, ¬ Touches incident region v := by
  intro v hv hvR
  obtain ⟨p, hp⟩ := VertexSeparatorBond.exists_walk_in G hS hv ha
  obtain ⟨x, hx, hmx⟩ := walk_meets_mixed G incident region hshare p hvR haR
  exact hboundary x hmx (hp x hx)

theorem not_touches_subset_of_connected_complement (G : SimpleGraph V)
    (incident : V → Set F) (region : Set F)
    (hshare : ∀ u v, G.Adj u v → ∃ f, f ∈ incident u ∧ f ∈ incident v)
    {S : Set V} (hSc : (G.induce Sᶜ).Connected)
    (hboundary : ∀ v, Mixed incident region v → v ∈ S)
    {b : V} (hb : b ∉ S) (hbR : Touches incident region b) :
    ∀ v, ¬ Touches incident region v → v ∈ S := by
  classical
  intro v hv
  by_contra hn
  obtain ⟨p, hp⟩ := VertexSeparatorBond.exists_walk_in G hSc hb hn
  obtain ⟨x, hx, hmx⟩ := walk_meets_mixed G incident region hshare p hbR hv
  exact hp x hx (hboundary x hmx)

end FaceDistanceFrontiers

namespace SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open SphericalDistanceContours FaceDistanceFrontiers

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every vertex touching the later deep region lies outside the bond. -/
theorem contour_bond_avoids_touches (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : ℕ}
    (hij : i < j) (hi : i < (orbitFaceDualGraph data).dist root far)
    {S : Set V} (hS : (G.induce S).Connected)
    (hfirst : frontier data root far i ⊆ S)
    (hlast : frontier data root far j ⊆ Sᶜ) :
    ∀ v ∈ S, ¬ Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far j) v := by
  obtain ⟨a⟩ := (frontier_connected data hclass htwo root far i hi).nonempty
  exact connected_shore_avoids_touches G (vertexFaces data)
    (deepRegion (orbitFaceDualGraph data) root far j)
    (fun _ _ h => adjacent_share_face data h) hS (fun _ h => hlast h)
    (hfirst a.property)
    (not_touches_of_mixed_lt (orbitFaceDualGraph data) root far (vertexFaces data)
      (vertexFaces_clique data hclass.spherical.cubic hclass.vertexRotationCyclic htwo)
      hij a.property)

/-- All vertices touching an outside face of the earlier region are retained. -/
theorem contour_bond_contains_outside (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : ℕ}
    (hij : i ≤ j) (hj : j < (orbitFaceDualGraph data).dist root far)
    {S : Set V} (hSc : (G.induce Sᶜ).Connected)
    (hfirst : frontier data root far i ⊆ S)
    (hlast : frontier data root far j ⊆ Sᶜ) :
    ∀ v, (∃ f ∈ vertexFaces data v, f ∉ deepRegion (orbitFaceDualGraph data) root far i) →
      v ∈ S := by
  classical
  obtain ⟨b⟩ := (frontier_connected data hclass htwo root far j hj).nonempty
  intro v hv
  by_cases hvR : Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far i) v
  · exact hfirst ⟨hvR, hv⟩
  · exact not_touches_subset_of_connected_complement G (vertexFaces data)
      (deepRegion (orbitFaceDualGraph data) root far i)
      (fun _ _ h => adjacent_share_face data h) hSc (fun _ h => hfirst h)
      (hlast b.property)
      (touches_of_mixed_le (orbitFaceDualGraph data) root far (vertexFaces data) hij b.property)
      v hvR

/-- Separated depth windows force strict inclusion for any such two bonds. -/
theorem contour_bonds_strict (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j p q : ℕ}
    (hij : i < j) (hjp : j ≤ p) (hpq : p < q)
    (hq : q < (orbitFaceDualGraph data).dist root far)
    {S T : Set V} (hS : (G.induce S).Connected) (hTc : (G.induce Tᶜ).Connected)
    (hSi : frontier data root far i ⊆ S) (hSj : frontier data root far j ⊆ Sᶜ)
    (hTp : frontier data root far p ⊆ T) (hTq : frontier data root far q ⊆ Tᶜ) :
    S ⊂ T := by
  classical
  have hav := contour_bond_avoids_touches data hclass htwo root far hij (by omega) hS hSi hSj
  obtain ⟨b⟩ := (frontier_connected data hclass htwo root far q hq).nonempty
  have hnot := not_touches_subset_of_connected_complement G (vertexFaces data)
    (deepRegion (orbitFaceDualGraph data) root far p)
    (fun _ _ h => adjacent_share_face data h) hTc (fun _ h => hTp h) (hTq b.property)
    (touches_of_mixed_le (orbitFaceDualGraph data) root far (vertexFaces data) hpq.le b.property)
  refine ⟨?_, ?_⟩
  · intro v hv
    apply hnot v
    rintro ⟨f, hf, hr⟩
    exact hav v hv ⟨f, hf, deepRegion_antitone (orbitFaceDualGraph data) root far hjp hr⟩
  · intro hTS
    obtain ⟨c⟩ := (frontier_connected data hclass htwo root far p (by omega)).nonempty
    exact hav c (hTS (hTp c.property))
      (touches_of_mixed_le (orbitFaceDualGraph data) root far (vertexFaces data) hjp c.property)

end SphericalContourSeparators
end Mettapedia.GraphTheory.FourColor
