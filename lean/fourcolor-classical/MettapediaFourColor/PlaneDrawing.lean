import MettapediaFourColor.CompactPlaneMap
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Topology.Path

/-!
# From a noncrossing graph drawing to compact plane sites

Vertices are distinct points of the real plane. Each oriented edge is an
injective continuous path between its endpoints; reversing the edge reverses
the path. Edge interiors contain no vertices, and interiors of different
unoriented edges are disjoint.

The site of a vertex consists of that vertex and the first closed half of
every outgoing edge. Its exclusive core consists of the same half-edges
without their midpoints. These cores are connected and dense in their sites.
An edge midpoint belongs to exactly its two endpoint sites.

Consequently the nearest-region construction gives a simple plane map whose
adjacencies include every edge of the original graph. This proves the graph
colouring statement from the plane-map Four Colour theorem without assuming
a rotation system or a colouring in the drawing data.
-/

namespace FourColor

open Set Mettapedia.Topology.NearestRegions

variable {V : Type*} (G : SimpleGraph V)

/-- A drawing of a simple graph by noncrossing embedded arcs in the real plane. -/
structure PlaneDrawing where
  position : V → Point
  position_injective : Function.Injective position
  path : ∀ d : G.Dart, Path (position d.fst) (position d.snd)
  path_injective : ∀ d, Function.Injective (path d)
  path_symm : ∀ d, path d.symm = (path d).symm
  interior_no_vertex : ∀ d t, t ∈ Ioo (0 : ℝ) 1 →
    ∀ v, (path d).extend t ≠ position v
  interior_overlap : ∀ d e s t, s ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
    (path d).extend s = (path e).extend t → d = e ∨ d = e.symm

namespace PlaneDrawing

variable {G} (D : PlaneDrawing G)

/-- Truncated outgoing edges, with the centre retained even at isolated vertices. -/
def star (J : Set ℝ) (v : V) : Set Point :=
  {D.position v} ∪ ⋃ d : {d : G.Dart // d.fst = v}, (D.path d).extend '' J

def site (v : V) : Set Point := D.star (Icc 0 (1 / 2)) v

def openStar (v : V) : Set Point := D.star (Ico 0 (1 / 2)) v

theorem position_mem_star (J : Set ℝ) (v : V) : D.position v ∈ D.star J v :=
  Or.inl rfl

theorem half_mem_star {J : Set ℝ} {d : G.Dart} {t : ℝ} (ht : t ∈ J) :
    (D.path d).extend t ∈ D.star J d.fst :=
  Or.inr (mem_iUnion.mpr ⟨⟨d, rfl⟩, ⟨t, ht, rfl⟩⟩)

theorem extend_injective (d : G.Dart) :
    Set.InjOn (D.path d).extend (Icc 0 1) := by
  intro s hs t ht h
  rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at h
  exact congrArg Subtype.val (D.path_injective d h)

theorem extend_symm (d : G.Dart) (t : ℝ) :
    (D.path d.symm).extend t = (D.path d).extend (1 - t) :=
  (congrArg (fun p : Path (D.position d.snd) (D.position d.fst) => p.extend t)
    (D.path_symm d)).trans ((D.path d).extend_symm_apply t)

theorem half_eq_vertex {d : G.Dart} {t : ℝ} (ht : t ∈ Icc 0 (1 / 2))
    {v : V} (h : (D.path d).extend t = D.position v) :
    t = 0 ∧ d.fst = v := by
  by_cases ht0 : t = 0
  · refine ⟨ht0, D.position_injective ?_⟩
    simpa only [ht0, Path.extend_zero] using h
  · exact (D.interior_no_vertex d t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
      by linarith [ht.2]⟩ v h).elim

/-- Closed halves from different vertices can meet only at a common midpoint. -/
theorem half_intersection {d e : G.Dart} (hde : d.fst ≠ e.fst)
    {s t : ℝ} (hs : s ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 (1 / 2))
    (h : (D.path d).extend s = (D.path e).extend t) :
    s = 1 / 2 ∧ t = 1 / 2 ∧ d = e.symm := by
  have hs0 : s ≠ 0 := by
    intro hs0
    have he := D.half_eq_vertex ht (by
      simpa only [hs0, Path.extend_zero] using h.symm)
    exact hde he.2.symm
  have ht0 : t ≠ 0 := by
    intro ht0
    have hd := D.half_eq_vertex hs (by
      simpa only [ht0, Path.extend_zero] using h)
    exact hde hd.2
  rcases D.interior_overlap d e s t
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), by linarith [hs.2]⟩
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), by linarith [ht.2]⟩ h with heq | heq
  · exact (hde (congrArg (fun a : G.Dart => a.fst) heq)).elim
  · have hrev : (D.path e).extend (1 - s) = (D.path e).extend t := by
      have h' := (congrArg (fun a : G.Dart => (D.path a).extend s) heq).symm.trans h
      rwa [D.extend_symm] at h'
    have hst := D.extend_injective e ⟨by linarith [hs.2], by linarith [hs.1]⟩
      ⟨ht.1, by linarith [ht.2]⟩ hrev
    exact ⟨by linarith [hs.2, ht.2], by linarith [hs.2, ht.2], heq⟩

theorem position_mem_site_iff (v w : V) : D.position v ∈ D.site w ↔ v = w := by
  constructor
  · rintro (h | h)
    · exact D.position_injective h
    · obtain ⟨d, t, ht, heq⟩ := mem_iUnion.mp h
      exact (D.half_eq_vertex ht heq).2.symm.trans d.property
  · rintro rfl
    exact D.position_mem_star _ _

theorem midpoint_symm (d : G.Dart) :
    (D.path d.symm).extend (1 / 2) = (D.path d).extend (1 / 2) := by
  rw [D.extend_symm]
  norm_num

theorem midpoint_mem_site_iff (d : G.Dart) (v : V) :
    (D.path d).extend (1 / 2) ∈ D.site v ↔ v = d.fst ∨ v = d.snd := by
  constructor
  · intro h
    by_cases hv : v = d.fst
    · exact Or.inl hv
    · right
      rcases h with h | h
      · exact (D.interior_no_vertex d (1 / 2) (by norm_num) v h).elim
      · obtain ⟨e, t, ht, heq⟩ := mem_iUnion.mp h
        have hde : d.fst ≠ e.val.fst := by
          rw [e.property]
          exact Ne.symm hv
        have hpair := D.half_intersection hde (by norm_num) ht heq.symm
        have he := congrArg (fun a : G.Dart => a.snd) hpair.2.2
        change d.snd = e.val.fst at he
        exact e.property.symm.trans he.symm
  · rintro (rfl | rfl)
    · exact D.half_mem_star (by norm_num)
    · rw [← D.midpoint_symm d]
      exact D.half_mem_star (d := d.symm) (by norm_num)

/-- The open half-stars are exactly the exclusive parts of the closed sites. -/
theorem core_eq_openStar (v : V) : core D.site v = D.openStar v := by
  ext x
  constructor
  · rintro ⟨hx, hex⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨d, t, ht, rfl⟩ := mem_iUnion.mp hx
      have hlt : t < 1 / 2 := by
        by_contra hlt
        have heq : t = 1 / 2 := le_antisymm ht.2 (le_of_not_gt hlt)
        have hmem := (D.midpoint_mem_site_iff d.val d.val.snd).mpr (Or.inr rfl)
        rw [← heq] at hmem
        exact hex d.val.snd (by simpa only [← d.property] using d.val.snd_ne_fst) hmem
      exact Or.inr (mem_iUnion.mpr ⟨d, t, ⟨ht.1, hlt⟩, rfl⟩)
  · intro hx
    have hsite : x ∈ D.site v := by
      rcases hx with hx | hx
      · exact Or.inl hx
      · obtain ⟨d, t, ht, rfl⟩ := mem_iUnion.mp hx
        exact Or.inr (mem_iUnion.mpr ⟨d, t, ⟨ht.1, ht.2.le⟩, rfl⟩)
    refine ⟨hsite, ?_⟩
    intro w hw hxw
    rcases hx with hx | hx
    · have hvw := (D.position_mem_site_iff v w).mp (hx ▸ hxw)
      exact hw hvw.symm
    · obtain ⟨d, s, hs, rfl⟩ := mem_iUnion.mp hx
      rcases hxw with hxw | hxw
      · exact hw ((D.half_eq_vertex ⟨hs.1, hs.2.le⟩ hxw).2.symm.trans d.property)
      · obtain ⟨e, t, ht, heq⟩ := mem_iUnion.mp hxw
        have hde : d.val.fst ≠ e.val.fst := by
          rw [d.property, e.property]
          exact hw.symm
        have hpair := D.half_intersection hde ⟨hs.1, hs.2.le⟩ ht heq.symm
        exact hs.2.ne hpair.1

theorem isConnected_openStar (v : V) : IsConnected (D.openStar v) := by
  refine ⟨⟨D.position v, D.position_mem_star _ _⟩,
    isPreconnected_of_forall (D.position v) ?_⟩
  intro x hx
  rcases hx with hx | hx
  · refine ⟨{D.position v}, ?_, rfl, hx, isPreconnected_singleton⟩
    exact fun _ h => Or.inl h
  · obtain ⟨d, t, ht, rfl⟩ := mem_iUnion.mp hx
    refine ⟨(D.path d).extend '' Ico 0 (1 / 2), ?_, ?_, ⟨t, ht, rfl⟩, ?_⟩
    · exact fun _ h => Or.inr (mem_iUnion.mpr ⟨d, h⟩)
    · refine ⟨0, by norm_num, ?_⟩
      simpa only [Path.extend_zero] using congrArg D.position d.property
    · exact (convex_Ico (0 : ℝ) (1 / 2)).isPreconnected.image _
        (D.path d).continuous_extend.continuousOn

theorem site_subset_closure_openStar (v : V) : D.site v ⊆ closure (D.openStar v) := by
  intro x hx
  rcases hx with hx | hx
  · exact subset_closure (Or.inl hx)
  · obtain ⟨d, hx⟩ := mem_iUnion.mp hx
    have hcl : (D.path d).extend '' Icc 0 (1 / 2) ⊆
        closure ((D.path d).extend '' Ico 0 (1 / 2)) := by
      have h := image_closure_subset_closure_image (D.path d).continuous_extend
        (s := Ico 0 (1 / 2))
      rwa [closure_Ico (by norm_num : (0 : ℝ) ≠ 1 / 2)] at h
    exact closure_mono (fun _ h => Or.inr (mem_iUnion.mpr ⟨d, h⟩)) (hcl hx)

theorem isCompact_site [Finite V] (v : V) : IsCompact (D.site v) := by
  classical
  let : Finite G.Dart := Finite.of_injective SimpleGraph.Dart.toProd
    SimpleGraph.Dart.toProd_injective
  exact isCompact_singleton.union (isCompact_iUnion fun d =>
    isCompact_Icc.image (D.path d).continuous_extend)

/-- The geometric sites are constructed from the drawing, with every required
property proved from the arc conditions. -/
def toSites [Finite V] : CompactPlaneMap.Sites V where
  site := D.site
  compact := D.isCompact_site
  nonempty v := ⟨D.position v, D.position_mem_star _ _⟩
  core_connected v := by
    rw [D.core_eq_openStar]
    exact D.isConnected_openStar v
  core_dense v := by
    rw [D.core_eq_openStar]
    exact D.site_subset_closure_openStar v

include D

/-- The ordinary graph endpoint: a finite simple graph drawn by noncrossing
injective paths is four-colourable whenever the plane-map theorem holds. -/
theorem colorable [Finite V] (hfour : FourColorTheorem) : G.Colorable 4 := by
  apply CompactPlaneMap.Sites.colorable D.toSites hfour G
  intro i j hij
  let d : G.Dart := ⟨(i, j), hij⟩
  refine ⟨(D.path d).extend (1 / 2), ?_, ?_, ?_⟩
  · exact (D.midpoint_mem_site_iff d i).mpr (Or.inl rfl)
  · exact (D.midpoint_mem_site_iff d j).mpr (Or.inr rfl)
  · intro v hv
    exact (D.midpoint_mem_site_iff d v).mp hv

end PlaneDrawing

end FourColor
