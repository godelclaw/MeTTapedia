import Mettapedia.GraphTheory.FourColor.SphericalContourLinkage

/-!
# Every path between depth contours meets each intermediate contour

Adjacent primal vertices share an incident face. Thus a walk leaving the
vertices touching a face region must meet its mixed frontier. The metric
clique property puts an outer depth contour entirely outside the touched
set of a later region; all deeper contours touch that region. These facts
derive all row-column intersections for the full-ambient linkage.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FaceDistanceFrontiers

variable {F V : Type*}

def Touches (incident : V → Set F) (region : Set F) (v : V) : Prop :=
  ∃ f ∈ incident v, f ∈ region

theorem walk_meets_mixed (G : SimpleGraph V) (incident : V → Set F) (region : Set F)
    (hshare : ∀ u v, G.Adj u v → ∃ f, f ∈ incident u ∧ f ∈ incident v)
    {a b : V} (p : G.Walk a b) (ha : Touches incident region a)
    (hb : ¬ Touches incident region b) : ∃ v ∈ p.support, Mixed incident region v := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b e p ih =>
    by_cases hc : Touches incident region c
    · obtain ⟨v, hv, hm⟩ := ih hc hb
      exact ⟨v, List.mem_cons_of_mem _ hv, hm⟩
    · obtain ⟨f, hf, hg⟩ := hshare a c e
      exact ⟨a, List.mem_cons_self .., ha, f, hf, fun h => hc ⟨f, hg, h⟩⟩

theorem touches_of_mixed_le (H : SimpleGraph F) (root far : F) (incident : V → Set F)
    {i j : ℕ} (hij : i ≤ j) {v : V}
    (hv : Mixed incident (deepRegion H root far j) v) :
    Touches incident (deepRegion H root far i) v := by
  obtain ⟨⟨f, hf, hr⟩, _⟩ := hv
  exact ⟨f, hf, deepRegion_antitone H root far hij hr⟩

theorem not_touches_of_mixed_lt (H : SimpleGraph F) (root far : F) (incident : V → Set F)
    (hclique : ∀ v f g, f ∈ incident v → g ∈ incident v → f = g ∨ H.Adj f g)
    {i j : ℕ} (hij : i < j) {v : V}
    (hv : Mixed incident (deepRegion H root far i) v) :
    ¬ Touches incident (deepRegion H root far j) v := by
  obtain ⟨⟨f, hf, hfd⟩, _⟩ := mixed_distance H root far incident hclique hv
  rintro ⟨g, hg, hr⟩
  have hd := dist_gt_of_mem H root far hr
  rcases hclique v f g hf hg with rfl | hadj
  · omega
  · have hdiff := hadj.diff_dist_adj (u := root)
    omega

end FaceDistanceFrontiers

namespace SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open SphericalDistanceContours FaceDistanceFrontiers

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One side of each original edge is a face incident at both endpoints. -/
theorem adjacent_share_face (data : Data G) {u v : V} (h : G.Adj u v) :
    ∃ f, f ∈ vertexFaces data u ∧ f ∈ vertexFaces data v := by
  let d : G.Dart := ⟨(u, v), h⟩
  let RS := data.toRotationSystem
  refine ⟨dartOrbitFace RS d, ⟨d, rfl, rfl⟩, RS.rho (RS.alpha d), ?_, ?_⟩
  · exact RS.vert_rho (RS.alpha d)
  · have he := dartOrbitFace_alpha_eq_dartOrbitFace_rho RS (RS.alpha d)
    rw [RS.alpha_involutive] at he
    exact he.symm

/-- All intermediate frontiers are crossed, even by paths leaving the band. -/
theorem walk_meets_intermediate (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i d j : ℕ}
    (hid : i ≤ d) (hdj : d ≤ j) {a b : V}
    (ha : a ∈ frontier data root far i) (hb : b ∈ frontier data root far j)
    (p : G.Walk a b) : ∃ v ∈ p.support, v ∈ frontier data root far d := by
  by_cases heq : d = i
  · subst d
    exact ⟨a, p.start_mem_support, ha⟩
  have hlt : i < d := by omega
  have houtside := not_touches_of_mixed_lt (orbitFaceDualGraph data) root far (vertexFaces data)
    (vertexFaces_clique data hclass.spherical.cubic hclass.vertexRotationCyclic htwo) hlt ha
  have hinside := touches_of_mixed_le (orbitFaceDualGraph data) root far (vertexFaces data) hdj hb
  obtain ⟨v, hv, hm⟩ := walk_meets_mixed G (vertexFaces data)
    (deepRegion (orbitFaceDualGraph data) root far d)
    (fun _ _ h => adjacent_share_face data h) p.reverse hinside houtside
  exact ⟨v, by simpa using hv, hm⟩

end SphericalContourSeparators
end Mettapedia.GraphTheory.FourColor
