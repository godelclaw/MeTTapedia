import Mettapedia.GraphTheory.FourColor.SphericalProtectedLinkedBand

/-!
# Connected caps without discarding protected material

A closed contour band need not have one connected cap on each side.
Keep the two complementary components containing the buffered extreme
contours, and absorb the others into the middle. The resulting shell is
connected, has exactly these two nonempty complementary components, and
stays within the original protected band. No width or shrinking claim is
inferred from this geometric repair.
-/

namespace Mettapedia.GraphTheory.FourColor.BufferedContourShell

open SimpleGraph SimpleGraphDartRotation VertexSeparatorBond ProtectedContourBand
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open FaceDistanceFrontiers SphericalDistanceContours SphericalContourSeparators
open SphericalProtectedLinkedBand
open GoertzelV24SimpleGraphFaceDualConnectedness

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Components reached on opposite sides of a separating set cannot meet. -/
theorem floods_disjoint {S : Set V} {x y : V}
    (hsep : ∀ p : G.Walk x y, ∃ z ∈ p.support, z ∈ S) :
    Disjoint (flood G Sᶜ {x}) (flood G Sᶜ {y}) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨a, ha, p, hp⟩ ⟨b, hb, q, hq⟩
  obtain rfl : a = x := ha
  obtain rfl : b = y := hb
  obtain ⟨z, hz, hs⟩ := hsep (p.append q.reverse)
  simp only [SimpleGraph.Walk.support_append, List.mem_append, SimpleGraph.Walk.support_reverse] at hz
  rcases hz with hz | hz
  · exact hp z hz hs
  · exact hq z (by simpa using (List.mem_of_mem_tail hz)) hs

/-- Any connected set containing the seed and avoiding S stays in its component. -/
theorem connected_subset_flood {S A : Set V} {x : V}
    (hA : (G.induce A).Connected) (hx : x ∈ A) (hAS : A ⊆ Sᶜ) :
    A ⊆ flood G Sᶜ {x} := by
  intro v hv
  obtain ⟨p, hp⟩ := exists_walk_in G hA hx hv
  exact ⟨x, by simp, p, fun z hz => hAS (hp z hz)⟩

/-- Absorbing all other components connects the shell, not just its rim. -/
theorem shell_connected (hG : G.Connected) {S : Set V}
    (hS : (G.induce S).Connected) (x y : V) :
    (G.induce (flood G Sᶜ {x} ∪ flood G Sᶜ {y})ᶜ).Connected := by
  have hsub : S ⊆ (flood G Sᶜ {x} ∪ flood G Sᶜ {y})ᶜ := by
    rintro v hv (hc | hc)
    · exact flood_subset G _ _ hc hv
    · exact flood_subset G _ _ hc hv
  apply connected_of_boundary_seed hG hS hsub
  intro u v huv hu hv
  by_contra huS
  have hv' : v ∈ flood G Sᶜ {x} ∪ flood G Sᶜ {y} := not_not.mp hv
  rcases hv' with hv' | hv'
  · exact hu (Or.inl (flood_adj G hv' huv.symm huS))
  · exact hu (Or.inr (flood_adj G hv' huv.symm huS))

/-- A complete connected frontier connects either touched facial side. -/
theorem touches_connected (data : Data G) (hG : G.Connected)
    (R : Set (OrbitFace data.toRotationSystem))
    (hF : (G.induce {v | Mixed (vertexFaces data) R v}).Connected) :
    (G.induce {v | Touches (vertexFaces data) R v}).Connected := by
  apply connected_of_boundary_seed hG hF (fun _ h => h.1)
  intro u v huv hu hv
  obtain ⟨f, hfu, hfv⟩ := adjacent_share_face data huv
  exact ⟨hu, f, hfu, fun hf => hv ⟨f, hfv, hf⟩⟩

theorem touches_compl_connected (data : Data G) (hG : G.Connected)
    (R : Set (OrbitFace data.toRotationSystem))
    (hF : (G.induce {v | Mixed (vertexFaces data) R v}).Connected) :
    (G.induce {v | Touches (vertexFaces data) Rᶜ v}).Connected := by
  apply connected_of_boundary_seed hG hF (fun _ h => h.2)
  intro u v huv hu hv
  obtain ⟨f, hfu, hfv⟩ := adjacent_share_face data huv
  refine ⟨⟨f, hfu, ?_⟩, hu⟩
  by_contra hf
  exact hv ⟨f, hfv, hf⟩

/-- One buffer layer separates the touched outer and inner face regions. -/
theorem touches_disjoint_compl (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : Nat} (hij : i < j) :
    Disjoint {v | Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far i)ᶜ v}
      {v | Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far j) v} := by
  apply Set.disjoint_left.mpr
  intro v ho hi
  have hm : Mixed (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far i) v := by
    obtain ⟨f, hf, hfin⟩ := hi
    exact ⟨⟨f, hf, deepRegion_antitone _ root far hij.le hfin⟩, ho⟩
  exact not_touches_of_mixed_lt _ root far (vertexFaces data)
    (vertexFaces_clique data ambient.spherical.cubic ambient.vertexRotationCyclic htwo) hij hm hi

/-- The middle is a genuine three-region decomposition. Each cap and its
complement are connected. The shell contains the whole unbuffered band
and stays inside the protected buffered band. -/
structure ShellOf (data : Data G) {marks : Finset V} {a n : Nat}
    (B : LinkedBand data marks a n) where
  outer : Set V
  inner : Set V
  disjoint : Disjoint outer inner
  outer_connected : (G.induce outer).Connected
  inner_connected : (G.induce inner).Connected
  outer_complement_connected : (G.induce outerᶜ).Connected
  inner_complement_connected : (G.induce innerᶜ).Connected
  shell_connected : (G.induce (outer ∪ inner)ᶜ).Connected
  contains_middle : band data B.root B.far (B.lo + 1) (B.lo + a - 2) ⊆ (outer ∪ inner)ᶜ
  within_buffer : (outer ∪ inner)ᶜ ⊆ band data B.root B.far B.lo (B.lo + a - 1)
  outer_contour : frontier data B.root B.far B.lo ⊆ outer
  inner_contour : frontier data B.root B.far (B.lo + a - 1) ⊆ inner
  outer_region : {v | Touches (vertexFaces data)
    (deepRegion (orbitFaceDualGraph data) B.root B.far B.lo)ᶜ v} ⊆ outer
  inner_region : {v | Touches (vertexFaces data)
    (deepRegion (orbitFaceDualGraph data) B.root B.far (B.lo + a - 1)) v} ⊆ inner
  no_cross : ∀ u ∈ outer, ∀ v ∈ inner, ¬ G.Adj u v
  boundary_on_middle : ∀ u v, G.Adj u v → u ∈ (outer ∪ inner)ᶜ →
    v ∉ (outer ∪ inner)ᶜ → u ∈ band data B.root B.far (B.lo + 1) (B.lo + a - 2)

/-- Construct the caps by complementary flooding. The buffer controls all
absorbed components, even if a raw cap has several connected components. -/
theorem exists_shell (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    {marks : Finset V} {a n : Nat} (B : LinkedBand data marks a n)
    (ha : 4 ≤ a) (hn : 0 < n) : Nonempty (ShellOf data B) := by
  classical
  let lo := B.lo
  let hi := B.lo + a - 1
  let S := band data B.root B.far (lo + 1) (hi - 1)
  let A := {v | Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) B.root B.far lo)ᶜ v}
  let Z := {v | Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) B.root B.far hi) v}
  have hdepth : hi < (orbitFaceDualGraph data).dist B.root B.far := by
    have := B.depth
    dsimp [hi]
    omega
  have hlow : lo + 1 < hi - 1 := by dsimp [lo, hi]; omega
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  have hF := frontier_connected data ambient htwo B.root B.far lo (by omega)
  have hH := frontier_connected data ambient htwo B.root B.far hi hdepth
  have hA : (G.induce A).Connected := touches_compl_connected data hG _ hF
  have hZ : (G.induce Z).Connected := touches_connected data hG _ hH
  have hAS : A ⊆ Sᶜ := by
    intro v hv hs
    exact Set.disjoint_left.mp (touches_disjoint_compl data ambient htwo B.root B.far
      (i := lo) (j := lo + 1) (by omega)) hv hs.1
  have hZS : Z ⊆ Sᶜ := by
    intro v hv hs
    exact Set.disjoint_left.mp (touches_disjoint_compl data ambient htwo B.root B.far
      (i := hi - 1) (j := hi) (by omega)) hs.2 hv
  obtain ⟨x⟩ := hF.nonempty
  obtain ⟨y⟩ := hH.nonempty
  have hxA : x.val ∈ A := x.property.2
  have hyZ : y.val ∈ Z := y.property.1
  let C := flood G Sᶜ {x.val}
  let D := flood G Sᶜ {y.val}
  have hC : (G.induce C).Connected := flood_singleton_connected G (hAS hxA)
  have hD : (G.induce D).Connected := flood_singleton_connected G (hZS hyZ)
  have hAC : A ⊆ C := connected_subset_flood hA hxA hAS
  have hZD : Z ⊆ D := connected_subset_flood hZ hyZ hZS
  have hCS : C ⊆ Sᶜ := flood_subset G _ _
  have hDS : D ⊆ Sᶜ := flood_subset G _ _
  have hCD : Disjoint C D := by
    apply floods_disjoint
    intro p
    obtain ⟨v, hvp, hv⟩ := walk_meets_intermediate data ambient htwo
      B.root B.far (i := lo) (d := lo + 1) (j := hi)
      (by omega) (by omega) x.property y.property p
    exact ⟨v, hvp, frontier_subset_band data B.root B.far (by rfl) hlow.le hv⟩
  obtain ⟨L, hL⟩ := exists_confined_linkage data ambient htwo B.root B.far
    (lo := lo + 1) (hi := hi - 1) (by dsimp [lo]; omega) hlow
    (by dsimp [hi]; omega) B.linkage
  have hS : (G.induce S).Connected := band_connected data ambient htwo B.root B.far
    hlow.le (by omega) (L.walk ⟨0, hn⟩) (L.start_mem ⟨0, hn⟩)
    (L.finish_mem ⟨0, hn⟩) (hL ⟨0, hn⟩)
  have hmiddle : S ⊆ (C ∪ D)ᶜ := by
    rintro v hv (h | h)
    · exact hCS h hv
    · exact hDS h hv
  have hvface (v : V) : (vertexFaces data v).Nonempty := by
    obtain ⟨d, hd⟩ := GoertzelV24FaceDualConnectedness.exists_dart_vertOf_eq_of_isCubic
      data.toRotationSystem ambient.spherical.cubic v
    exact ⟨_, d, hd, rfl⟩
  have hbuffer : (C ∪ D)ᶜ ⊆ band data B.root B.far lo hi := by
    intro v hv
    obtain ⟨f, hf⟩ := hvface v
    constructor
    · by_contra h
      exact hv (Or.inl (hAC ⟨f, hf, fun hin => h ⟨f, hf, hin⟩⟩))
    · by_contra h
      apply hv
      apply Or.inr
      apply hZD
      refine ⟨f, hf, ?_⟩
      by_contra hout
      exact h ⟨f, hf, hout⟩
  have hidx : hi - 1 = B.lo + a - 2 := by dsimp [hi]; omega
  refine ⟨{
    outer := C, inner := D, disjoint := hCD
    outer_connected := hC, inner_connected := hD
    outer_complement_connected := filled_connected G hG hS x
    inner_complement_connected := filled_connected G hG hS y
    shell_connected := shell_connected hG hS x y
    contains_middle := ?_, within_buffer := hbuffer
    outer_contour := fun _ h => hAC h.2
    inner_contour := fun _ h => hZD h.1
    outer_region := hAC, inner_region := hZD
    no_cross := ?_, boundary_on_middle := ?_ }⟩
  · simpa only [S, lo, hidx] using hmiddle
  · intro u hu v hv huv
    exact Set.disjoint_left.mp hCD (flood_adj G hu huv (hDS hv)) hv
  · intro u v huv hu hv
    have hs : u ∈ S := by
      by_contra hn
      have hv' : v ∈ C ∪ D := not_not.mp hv
      rcases hv' with hv' | hv'
      · exact hu (Or.inl (flood_adj G hv' huv.symm hn))
      · exact hu (Or.inr (flood_adj G hv' huv.symm hn))
    simpa only [S, lo, hidx] using hs

theorem ShellOf.unmarked (data : Data G) {marks : Finset V} {a n : Nat}
    {B : LinkedBand data marks a n} (C : ShellOf data B) :
    ∀ v ∈ marks, v ∉ (C.outer ∪ C.inner)ᶜ := by
  intro v hv hs
  exact B.unmarked v hv (C.within_buffer hs)

/-- All original neighbours of a protected vertex remain on its cap side.
This is stronger than merely preserving the marked endpoint itself. -/
theorem ShellOf.marked_star (data : Data G) {marks : Finset V} {a n : Nat}
    {B : LinkedBand data marks a n} (C : ShellOf data B)
    {v : V} (hv : v ∈ marks) :
    (∀ u, G.Adj v u → u ∈ C.outer) ∨ (∀ u, G.Adj v u → u ∈ C.inner) := by
  classical
  by_cases h : Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) B.root B.far B.lo) v
  · right
    intro u hu
    obtain ⟨f, hfv, hfu⟩ := adjacent_share_face data hu
    apply C.inner_region
    refine ⟨f, hfu, ?_⟩
    by_contra hf
    exact B.unmarked v hv ⟨h, f, hfv, hf⟩
  · left
    intro u hu
    obtain ⟨f, hfv, hfu⟩ := adjacent_share_face data hu
    exact C.outer_region ⟨f, hfu, fun hf => h ⟨f, hfv, hf⟩⟩

end
end Mettapedia.GraphTheory.FourColor.BufferedContourShell
