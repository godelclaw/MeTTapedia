import MettapediaFourColor.NearestRegions
import FourColor.RealPlaneMathlib
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Compact sites as a plane map

A finite family of compact plane sets with nonempty connected exclusive
cores determines a simple plane map by strict nearest-set regions. Density
of the cores preserves site contacts. A point shared by exactly two sites
gives adjacency in the reference development's precise sense: a common
border point that is not a corner.

The resulting colouring transfer is a bridge from this geometric data to
Mathlib's simple-graph colourings. The `PlaneDrawing` module constructs these
sites and proves their properties from noncrossing injective paths.
-/

namespace FourColor.CompactPlaneMap

open Set Mettapedia.Topology.NearestRegions

variable {V : Type*}

/-- Geometric hypotheses for constructing a map by nearest-site regions. -/
structure Sites (V : Type*) where
  site : V → Set Point
  compact : ∀ v, IsCompact (site v)
  nonempty : ∀ v, (site v).Nonempty
  core_connected : ∀ v, IsConnected (core site v)
  core_dense : ∀ v, site v ⊆ closure (core site v)

namespace Sites

variable (S : Sites V)

/-- Points are related precisely when they belong to the same strict region. -/
def toMap : PlaneMap :=
  fun x => {y | ∃ v, x ∈ region S.site v ∧ y ∈ region S.site v}

theorem map_eq {v : V} {x : Point} (hx : x ∈ region S.site v) :
    S.toMap x = region S.site v := by
  ext y
  constructor
  · rintro ⟨w, hxw, hyw⟩
    have hwv : w = v := by
      by_contra h
      exact Set.disjoint_left.mp (disjoint_region S.site h) hxw hx
    simpa only [hwv] using hyw
  · exact fun hy => ⟨v, hx, hy⟩

theorem map_eq_empty {x : Point} (hx : ¬ ∃ v, x ∈ region S.site v) :
    S.toMap x = ∅ := by
  ext y
  constructor
  · rintro ⟨v, hxv, _⟩
    exact (hx ⟨v, hxv⟩).elim
  · exact False.elim

theorem plain : PlainMap S.toMap where
  symm := by
    rintro x y ⟨v, hx, hy⟩
    exact ⟨v, hy, hx⟩
  trans := by
    rintro x y ⟨v, hx, hy⟩
    rw [S.map_eq hx, S.map_eq hy]

theorem simple [Finite V] : SimpleMap S.toMap where
  plain := S.plain
  isOpen x := by
    apply (isOpenRegion_iff _).mpr
    by_cases hx : ∃ v, x ∈ region S.site v
    · obtain ⟨v, hv⟩ := hx
      rw [S.map_eq hv]
      exact isOpen_region S.site v
    · rw [S.map_eq_empty hx]
      exact isOpen_empty
  isConnected x := by
    apply isConnectedRegion_of_isPreconnected
    by_cases hx : ∃ v, x ∈ region S.site v
    · obtain ⟨v, hv⟩ := hx
      rw [S.map_eq hv]
      exact (isConnected_region S.site S.compact S.nonempty v
        (S.core_connected v)).isPreconnected
    · rw [S.map_eq_empty hx]
      exact isPreconnected_empty

/-- One representative in each nonempty exclusive core. -/
noncomputable def representative (v : V) : Point :=
  (S.core_connected v).nonempty.choose

theorem representative_mem (v : V) : S.representative v ∈ region S.site v :=
  core_subset_region S.site (fun w => (S.compact w).isClosed) S.nonempty v
    (S.core_connected v).nonempty.choose_spec

theorem map_representative (v : V) :
    S.toMap (S.representative v) = region S.site v :=
  S.map_eq (S.representative_mem v)

theorem representative_cover (v : V) : S.representative v ∈ cover S.toMap := by
  change S.representative v ∈ S.toMap (S.representative v)
  rw [S.map_representative]
  exact S.representative_mem v

theorem site_subset_closure (v : V) : S.site v ⊆ closure (region S.site v) :=
  subset_closure_region S.site (fun w => (S.compact w).isClosed) S.nonempty v
    (S.core_dense v)

/-- Exactly two possible site memberships bound the number of incident regions. -/
theorem notCorner_of_contact {i j : V} {z : Point}
    (hzi : z ∈ S.site i) (htwo : ∀ v, z ∈ S.site v → v = i ∨ v = j) :
    z ∈ notCorner S.toMap := by
  refine ⟨fun n => if n = 0 then S.representative i else S.representative j, ?_⟩
  intro x hx
  obtain ⟨hxmap, hzcl⟩ := hx
  obtain ⟨v, hxv, _⟩ := hxmap
  rw [S.map_eq hxv, regionClosure_eq] at hzcl
  have hvsite : z ∈ S.site v := by
    by_contra hzv
    exact notMem_closure_region S.site (fun w => (S.compact w).isClosed)
      S.nonempty hzi hzv hzcl
  rcases htwo v hvsite with rfl | rfl
  · refine ⟨0, by decide, ?_⟩
    change x ∈ S.toMap (if (0 : ℕ) = 0 then S.representative v else S.representative j) ∧ _
    simp only [ite_true, S.map_representative, regionClosure_eq]
    exact ⟨hxv, hzcl⟩
  · refine ⟨1, by decide, ?_⟩
    change x ∈ S.toMap (if (1 : ℕ) = 0 then S.representative i else S.representative v) ∧ _
    simp only [show (1 : ℕ) ≠ 0 from by decide, ite_false,
      S.map_representative, regionClosure_eq]
    exact ⟨hxv, hzcl⟩

/-- A contact belonging to exactly two distinct sites becomes map adjacency. -/
theorem adjacent_of_contact {i j : V} (hij : i ≠ j) {z : Point}
    (hzi : z ∈ S.site i) (hzj : z ∈ S.site j)
    (htwo : ∀ v, z ∈ S.site v → v = i ∨ v = j) :
    Adjacent S.toMap (S.representative i) (S.representative j) := by
  constructor
  · rw [S.map_representative]
    exact fun h => Set.disjoint_left.mp (disjoint_region S.site hij) h
      (S.representative_mem j)
  · refine ⟨z, S.notCorner_of_contact hzi htwo, ?_⟩
    change z ∈ regionClosure (S.toMap (S.representative i)) ∩
      regionClosure (S.toMap (S.representative j))
    rw [S.map_representative, S.map_representative, regionClosure_eq, regionClosure_eq]
    exact ⟨S.site_subset_closure i hzi, S.site_subset_closure j hzj⟩

/-- A plane-map colouring gives vertex colours when each graph edge has a
contact with no third site. No algorithm for finding the colouring is assumed. -/
theorem colorable [Finite V] (hfour : FourColorTheorem) (G : SimpleGraph V)
    (hcontact : ∀ i j, G.Adj i j → ∃ z, z ∈ S.site i ∧ z ∈ S.site j ∧
      ∀ v, z ∈ S.site v → v = i ∨ v = j) : G.Colorable 4 := by
  classical
  obtain ⟨k, hk, f, hf⟩ := hfour S.toMap S.simple
  have hpalette : ∀ v, ∃ c : Fin 4, S.representative v ∈ k (f c) := by
    intro v
    have hv : S.representative v ∈ cover k :=
      hk.consistent _ (S.representative_cover v)
    obtain ⟨n, hn, hmem⟩ := hf _ hv
    exact ⟨⟨n, hn⟩, hmem⟩
  choose c hc using hpalette
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro i j hadj heq
  obtain ⟨z, hzi, hzj, htwo⟩ := hcontact i j hadj
  have hmapadj := S.adjacent_of_contact hadj.ne hzi hzj htwo
  have hi := hc i
  rw [heq] at hi
  have hji := hk.plain.trans _ _ (hk.plain.symm _ _ hi) (hc j)
  exact hk.adjacent _ _ hmapadj hji

end Sites

end FourColor.CompactPlaneMap
