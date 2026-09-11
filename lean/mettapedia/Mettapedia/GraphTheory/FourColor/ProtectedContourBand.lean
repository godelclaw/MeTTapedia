import Mettapedia.GraphTheory.FourColor.ContourPathCrossing
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Protected regions between complete spherical contours

Keep the actual deep face regions, rather than reconstructing a disk from
an abstract ordered mesh. The closed band includes both contour cycles and
every vertex incident with a face between them. Separated bands are disjoint,
so more bands than marked vertices supply one wholly unmarked band.
Every original edge leaving a band is based on one of its two contours.
There is no uniform width bound or colouring descent claim here.
-/

namespace Mettapedia.GraphTheory.FourColor.ProtectedContourBand

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphFaceDualConnectedness
open FaceDistanceFrontiers SphericalDistanceContours SphericalContourSeparators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The entire closed vertex band, not just the selected paths or corners. -/
def band (data : Data G) (root far : OrbitFace data.toRotationSystem)
    (lo hi : Nat) : Set V :=
  {v | Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far lo) v ∧
    Touches (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far hi)ᶜ v}

theorem frontier_subset_band (data : Data G)
    (root far : OrbitFace data.toRotationSystem) {lo d hi : Nat}
    (hlo : lo ≤ d) (hhi : d ≤ hi) :
    frontier data root far d ⊆ band data root far lo hi := by
  rintro v ⟨hin, f, hf, hout⟩
  refine ⟨?_, f, hf, ?_⟩
  · obtain ⟨g, hg, hgin⟩ := hin
    exact ⟨g, hg, deepRegion_antitone _ root far hlo hgin⟩
  · exact fun h => hout (deepRegion_antitone _ root far hhi h)

/-- Strictly separated depth windows have no shared vertex, even on their
boundaries. Cubic face incidence is what excludes a straddling vertex. -/
theorem bands_disjoint (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {lo hi p q : Nat} (h : hi < p) :
    Disjoint (band data root far lo hi) (band data root far p q) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨_, hout⟩ ⟨hin, _⟩
  have hm : Mixed (vertexFaces data)
      (deepRegion (orbitFaceDualGraph data) root far hi) v := by
    obtain ⟨f, hf, hfin⟩ := hin
    exact ⟨⟨f, hf, deepRegion_antitone _ root far h.le hfin⟩, hout⟩
  exact not_touches_of_mixed_lt _ root far (vertexFaces data)
    (vertexFaces_clique data ambient.spherical.cubic ambient.vertexRotationCyclic htwo) h hm hin

/-- All lateral attachments are accounted for: an original edge exits only
at an actual outer or inner frontier vertex. -/
theorem boundary_based_on_contours (data : Data G)
    (root far : OrbitFace data.toRotationSystem) {lo hi : Nat} {u v : V}
    (hadj : G.Adj u v) (hu : u ∈ band data root far lo hi)
    (hv : v ∉ band data root far lo hi) :
    u ∈ frontier data root far lo ∨ u ∈ frontier data root far hi := by
  obtain ⟨f, hfu, hfv⟩ := adjacent_share_face data hadj
  by_cases hlo : Touches (vertexFaces data)
      (deepRegion (orbitFaceDualGraph data) root far lo) v
  · right
    refine ⟨⟨f, hfu, ?_⟩, hu.2⟩
    by_contra hf
    exact hv ⟨hlo, f, hfv, hf⟩
  · left
    exact ⟨hu.1, f, hfu, fun hf => hlo ⟨f, hfv, hf⟩⟩

/-- A marked vertex spoils at most one separated band. No path-only
avoidance, clean-disk supplier or exclusion premise is used. -/
theorem exists_unmarked_band (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (marks : Finset V)
    (base a n : Nat) (ha : 0 < a) (hn : marks.card < n) :
    ∃ t : Fin n, ∀ v ∈ marks,
      v ∉ band data root far (base + t.val * a) (base + t.val * a + a - 1) := by
  classical
  by_contra h
  push Not at h
  choose v hv hb using h
  let f : Fin n → {x // x ∈ marks} := fun i => ⟨v i, hv i⟩
  have hinj : Function.Injective f := by
    intro i j heq
    have he : v i = v j := congrArg Subtype.val heq
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hm := Nat.mul_le_mul_right a (Nat.succ_le_of_lt hij)
      simp only [Nat.succ_mul] at hm
      exact Set.disjoint_left.mp (bands_disjoint data ambient htwo root far
        (lo := base + i.val * a) (hi := base + i.val * a + a - 1)
        (p := base + j.val * a) (q := base + j.val * a + a - 1) (by omega))
        (hb i) (he ▸ hb j)
    · have hm := Nat.mul_le_mul_right a (Nat.succ_le_of_lt hij)
      simp only [Nat.succ_mul] at hm
      exact Set.disjoint_left.mp (bands_disjoint data ambient htwo root far
        (lo := base + j.val * a) (hi := base + j.val * a + a - 1)
        (p := base + i.val * a) (q := base + i.val * a + a - 1) (by omega))
        (hb j) (he.symm ▸ hb i)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

/-- Trim a supplied ambient path to a genuine path in the closed sub-band.
The construction minimizes length among paths using only its original
vertices; an excursion would give a strictly shorter candidate. -/
theorem exists_confined_path (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {outer lo hi inner : Nat}
    (hol : outer ≤ lo) (hlh : lo < hi) (hhi : hi ≤ inner)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hu : u ∈ frontier data root far outer) (hv : v ∈ frontier data root far inner) :
    ∃ x y, ∃ q : G.Walk x y, q.IsPath ∧ q.support ⊆ p.support ∧
      x ∈ frontier data root far lo ∧ y ∈ frontier data root far hi ∧
      ∀ z ∈ q.support, z ∈ band data root far lo hi := by
  classical
  let P : Nat → Prop := fun n => ∃ x y, ∃ q : G.Walk x y,
    q.length = n ∧ q.IsPath ∧ q.support ⊆ p.support ∧
      x ∈ frontier data root far lo ∧ y ∈ frontier data root far hi
  have hex : ∃ n, P n := by
    obtain ⟨y, hyp, hy⟩ := walk_meets_intermediate data ambient htwo root far
      (hol.trans hlh.le) hhi hu hv p
    let r := p.takeUntil y hyp
    obtain ⟨x, hxr, hx⟩ := walk_meets_intermediate data ambient htwo root far
      hol hlh.le hu hy r
    exact ⟨_, x, y, r.dropUntil x hxr, rfl, (hp.takeUntil hyp).dropUntil hxr,
      fun z hz => p.support_takeUntil_subset_support hyp
        (r.support_dropUntil_subset_support hxr hz), hx, hy⟩
  obtain ⟨x, y, q, hlen, hq, hsub, hx, hy⟩ := Nat.find_spec hex
  have hminimal {x' y'} (r : G.Walk x' y') (hr : r.IsPath)
      (hs : r.support ⊆ p.support)
      (hx' : x' ∈ frontier data root far lo) (hy' : y' ∈ frontier data root far hi) :
      q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨x', y', r, rfl, hr, hs, hx', hy'⟩
  refine ⟨x, y, q, hq, hsub, hx, hy, ?_⟩
  intro z hz
  have houter : Touches (vertexFaces data)
      (deepRegion (orbitFaceDualGraph data) root far lo) z := by
    by_contra hout
    have hzx : z ≠ x := fun h => hout (h ▸ hx.1)
    let r := q.dropUntil z hz
    obtain ⟨w, hwr, hw⟩ := walk_meets_mixed G (vertexFaces data)
      (deepRegion (orbitFaceDualGraph data) root far lo)
      (fun _ _ h => adjacent_share_face data h) r.reverse
      (touches_of_mixed_le _ root far (vertexFaces data) hlh.le hy) hout
    have hwr' : w ∈ r.support := by simpa using hwr
    have hle := hminimal (r.dropUntil w hwr') ((hq.dropUntil hz).dropUntil hwr')
      (fun s hs => hsub (q.support_dropUntil_subset_support hz
        (r.support_dropUntil_subset_support hwr' hs))) hw hy
    have hshort := q.length_dropUntil_lt_length hz hzx
    have hle' := r.length_dropUntil_le_length hwr'
    change r.length < q.length at hshort
    omega
  refine ⟨houter, ?_⟩
  by_contra hout
  have hall (f) (hf : f ∈ vertexFaces data z) :
      f ∈ deepRegion (orbitFaceDualGraph data) root far hi := by
    by_contra h
    exact hout ⟨f, hf, h⟩
  have hzy : z ≠ y := by
    rintro rfl
    obtain ⟨f, hf, hnot⟩ := hy.2
    exact hnot (hall f hf)
  have hin : Touches (vertexFaces data)
      (deepRegion (orbitFaceDualGraph data) root far hi) z := by
    obtain ⟨f, hf, _⟩ := houter
    exact ⟨f, hf, hall f hf⟩
  have hxout := not_touches_of_mixed_lt _ root far (vertexFaces data)
    (vertexFaces_clique data ambient.spherical.cubic ambient.vertexRotationCyclic htwo) hlh hx
  let r := q.takeUntil z hz
  obtain ⟨w, hwr, hw⟩ := walk_meets_mixed G (vertexFaces data)
    (deepRegion (orbitFaceDualGraph data) root far hi)
    (fun _ _ h => adjacent_share_face data h) r.reverse hin hxout
  have hwr' : w ∈ r.support := by simpa using hwr
  have hle := hminimal (r.takeUntil w hwr') ((hq.takeUntil hz).takeUntil hwr')
    (fun s hs => hsub (q.support_takeUntil_subset_support hz
      (r.support_takeUntil_subset_support hwr' hs))) hx hw
  have hshort := q.length_takeUntil_lt_length hz hzy
  have hle' := r.length_takeUntil_le_length hwr'
  change r.length < q.length at hshort
  omega

/-- Restrict all columns without reducing their number or losing disjointness.
Their complete supports lie inside the actual band. -/
theorem exists_confined_linkage (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {outer lo hi inner n : Nat}
    (hol : outer ≤ lo) (hlh : lo < hi) (hhi : hi ≤ inner)
    (L : VertexSplitCut.Linkage G (frontier data root far outer)
      (frontier data root far inner) n) :
    ∃ L' : VertexSplitCut.Linkage G (frontier data root far lo)
      (frontier data root far hi) n,
      ∀ i z, z ∈ (L'.walk i).support → z ∈ band data root far lo hi := by
  have h (i : Fin n) := exists_confined_path data ambient htwo root far hol hlh hhi
    (L.walk i) (L.simple i) (L.start_mem i) (L.finish_mem i)
  choose x y q hq hsub hx hy hband using h
  refine ⟨⟨x, y, hx, hy, q, hq, ?_⟩, hband⟩
  intro i j hij z hi hj
  exact L.disjoint i j hij z (hsub i hi) (hsub j hj)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Before a walk can leave S it reaches its boundary seed C. -/
theorem first_seed_in_side {S C : Set V}
    (hboundary : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x ∈ C)
    {u v : V} (p : G.Walk u v) (hu : u ∈ S) (hv : v ∈ C) :
    ∃ z ∈ C, ∃ q : G.Walk u z, ∀ x ∈ q.support, x ∈ S := by
  classical
  induction p with
  | nil => exact ⟨_, hv, .nil, by simpa using hu⟩
  | @cons u w v hadj p ih =>
    by_cases hc : u ∈ C
    · exact ⟨u, hc, .nil, by simpa using hu⟩
    have hw : w ∈ S := by
      by_contra hn
      exact hc (hboundary u w hadj hu hn)
    obtain ⟨z, hz, q, hq⟩ := ih hw hv
    refine ⟨z, hz, q.cons hadj, ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact hq x hx

/-- A connected subset containing the full inside boundary connects the
whole side. All adjacency here is adjacency in the original graph. -/
theorem connected_of_boundary_seed (hG : G.Connected) {S C : Set V}
    (hC : (G.induce C).Connected) (hCS : C ⊆ S)
    (hboundary : ∀ x y, G.Adj x y → x ∈ S → y ∉ S → x ∈ C) :
    (G.induce S).Connected := by
  obtain ⟨a⟩ := hC.nonempty
  apply VertexSeparatorBond.connected_of_walks G (hCS a.property)
  intro v hv
  obtain ⟨p⟩ := hG v a
  obtain ⟨z, hz, q, hq⟩ := first_seed_in_side hboundary p hv a.property
  obtain ⟨r, hr⟩ := VertexSeparatorBond.exists_walk_in G hC hz a.property
  refine ⟨(q.append r).reverse, ?_⟩
  intro x hx
  simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse,
    SimpleGraph.Walk.support_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hq x hx
  · exact hCS (hr x (List.mem_of_mem_tail hx))

/-- A confined column joins the two complete connected contours. Their
union contains the whole inside boundary and therefore connects the band. -/
theorem band_connected (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {lo hi : Nat}
    (hle : lo ≤ hi) (hdepth : hi < (orbitFaceDualGraph data).dist root far)
    {u v : V} (p : G.Walk u v)
    (hu : u ∈ frontier data root far lo) (hv : v ∈ frontier data root far hi)
    (hp : ∀ z ∈ p.support, z ∈ band data root far lo hi) :
    (G.induce (band data root far lo hi)).Connected := by
  let A := frontier data root far lo
  let B := frontier data root far hi
  let P : Set V := {z | z ∈ p.support}
  have hA := frontier_connected data ambient htwo root far lo (by omega)
  have hB := frontier_connected data ambient htwo root far hi hdepth
  have hAP : (G.induce (A ∪ P)).Connected :=
    SimpleGraph.induce_union_connected hA.preconnected p.connected_induce_support.preconnected
      ⟨u, hu, p.start_mem_support⟩
  have hAPB : (G.induce ((A ∪ P) ∪ B)).Connected :=
    SimpleGraph.induce_union_connected hAP.preconnected hB.preconnected
      ⟨v, Or.inr p.end_mem_support, hv⟩
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using ambient.primalConnected
  apply connected_of_boundary_seed hG hAPB ?_ ?_
  · intro z hz
    rcases hz with (hz | hz) | hz
    · exact frontier_subset_band data root far (by rfl) hle hz
    · exact hp z hz
    · exact frontier_subset_band data root far hle (by rfl) hz
  · intro x y hxy hx hy
    rcases boundary_based_on_contours data root far hxy hx hy with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

end
end Mettapedia.GraphTheory.FourColor.ProtectedContourBand
