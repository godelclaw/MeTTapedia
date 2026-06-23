import Mathlib

namespace Mettapedia.GraphTheory

/-- A finite simple graph presented as a symmetric irreflexive relation. -/
structure FiniteRelation (α : Type*) [Fintype α] [DecidableEq α] where
  adj : α → α → Prop
  symm : ∀ {x y}, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x
  decidable_adj : DecidableRel adj

namespace FiniteRelation

variable {α : Type*} [Fintype α] [DecidableEq α]

instance (G : FiniteRelation α) : DecidableRel G.adj :=
  G.decidable_adj

variable (G : FiniteRelation α)

noncomputable section

/-- Degree of a vertex in the full finite relation. -/
def degree (v : α) : Nat :=
  (Finset.univ.filter (fun w => G.adj v w)).card

/-- Degree of a vertex inside the induced relation on `S`. -/
def degreeOn (S : Finset α) (v : α) : Nat :=
  ((S.erase v).filter (fun w => G.adj v w)).card

/-- A vertex is a leaf of the induced relation on `S` if it lies in `S` and has
induced degree at most one. -/
def IsLeafOn (S : Finset α) (v : α) : Prop :=
  v ∈ S ∧ G.degreeOn S v ≤ 1

/-- Every nonempty finite set has a member whose induced degree is minimal. -/
theorem exists_min_degree (S : Finset α) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ w ∈ S, G.degreeOn S v ≤ G.degreeOn S w := by
  classical
  have himg : (S.image (fun v => G.degreeOn S v)).Nonempty :=
    Finset.image_nonempty.mpr hS
  let minDeg := (S.image (fun v => G.degreeOn S v)).min' himg
  obtain ⟨v, hv, hvmin⟩ :
      ∃ v ∈ S, G.degreeOn S v = minDeg := by
    have hmin_mem := Finset.min'_mem _ himg
    rcases (Finset.mem_image.mp hmin_mem) with ⟨v, hv, hdeg⟩
    exact ⟨v, hv, hdeg⟩
  refine ⟨v, hv, ?_⟩
  intro w hw
  rw [hvmin]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)

/-- A path in a finite relation, represented as a nonempty list with adjacent
successive vertices. -/
structure Path where
  vertices : List α
  chain : vertices.IsChain G.adj
  nonempty : vertices ≠ []

namespace Path

/-- A path is simple when its listed vertices are pairwise distinct. -/
def IsSimple (p : G.Path) : Prop :=
  p.vertices.Nodup

/-- The edge length of a nonempty list path. -/
def length (p : G.Path) : Nat :=
  p.vertices.length - 1

/-- First vertex of a path. -/
def first (p : G.Path) : α :=
  p.vertices.head p.nonempty

/-- Last vertex of a path. -/
def last (p : G.Path) : α :=
  p.vertices.getLast p.nonempty

/-- Extend a path by one adjacent terminal vertex. This is the reusable no-gap
core needed before any longest-path leaf argument can be revived. -/
def snoc (p : G.Path) (w : α) (h : G.adj p.last w) : G.Path where
  vertices := p.vertices ++ [w]
  chain := by
    apply p.chain.append (List.IsChain.singleton (R := G.adj) w)
    intro x hx y hy
    rcases List.mem_getLast?_eq_getLast hx with ⟨hx_ne, hx_eq⟩
    have hy_eq : y = w := by simpa using hy.symm
    rw [hx_eq, hy_eq]
    simpa [last] using h
  nonempty := by simp

/-- Appending a fresh terminal vertex preserves path simplicity. -/
theorem snoc_isSimple (p : G.Path) {w : α} {h : G.adj p.last w}
    (hp : p.IsSimple) (hw : w ∉ p.vertices) :
    IsSimple (G := G) (snoc (G := G) p w h) := by
  simpa [snoc, IsSimple] using List.Nodup.concat hw hp

theorem snoc_length (p : G.Path) {w : α} {h : G.adj p.last w} :
    (snoc (G := G) p w h).length = p.length + 1 := by
  have hlen_pos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  simp [snoc, length]
  omega

theorem snoc_last (p : G.Path) {w : α} {h : G.adj p.last w} :
    (snoc (G := G) p w h).last = w := by
  simp [snoc, last]

end Path

/-- A simple path can be extended by a fresh adjacent terminal vertex. This is
the clean core of the old longest-path extension lemma. -/
theorem path_extension_from_fresh_adjacent_terminal
    (p : G.Path) {w : α} (h : G.adj p.last w)
    (hp_simple : p.IsSimple) (hp_no_w : w ∉ p.vertices) :
    ∃ p' : G.Path, p'.IsSimple ∧ p'.length = p.length + 1 ∧ p'.last = w := by
  refine ⟨Path.snoc (G := G) p w h, ?_, ?_, ?_⟩
  · exact Path.snoc_isSimple (G := G) p hp_simple hp_no_w
  · exact Path.snoc_length (G := G) p
  · exact Path.snoc_last (G := G) p

/-- Old standalone compatibility surface: the degree and subset hypotheses are
kept because they are part of the former API, but the actual extension follows
from the explicit fresh adjacent endpoint. -/
theorem path_extension_from_degree_two (S : Finset α) (v w : α)
    (_hv : v ∈ S) (_hw : w ∈ S) (hadj : G.adj v w)
    (_hdeg : G.degreeOn S v ≥ 2)
    (p : G.Path) (hp_simple : p.IsSimple) (hp_end : p.last = v)
    (hp_no_w : w ∉ p.vertices) :
    ∃ p' : G.Path, p'.IsSimple ∧ p'.length = p.length + 1 ∧ p'.last = w := by
  have hlast_adj : G.adj p.last w := by
    simpa [hp_end] using hadj
  exact G.path_extension_from_fresh_adjacent_terminal p hlast_adj hp_simple hp_no_w

/-- Every nonempty finite set contains a singleton induced subrelation with a
leaf. This is the no-gap core that the old standalone file used downstream;
the stronger longest-path leaf theorem should be added only when fully proved. -/
theorem exists_singleton_leaf_subset (S : Finset α) (hS : S.Nonempty) :
    ∃ T ⊆ S, ∃ v ∈ T, G.degreeOn T v ≤ 1 := by
  classical
  rcases hS with ⟨v, hv⟩
  refine ⟨{v}, ?_, v, ?_, ?_⟩
  · simp [Finset.singleton_subset_iff, hv]
  · simp
  · simp [degreeOn]

end

end FiniteRelation

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A finite relation on faces represented by finite sets of edges. -/
def FaceRelation
    (adj : Finset E → Finset E → Prop)
    (adj_symm : ∀ {f g}, adj f g → adj g f)
    (adj_irrefl : ∀ f, ¬ adj f f)
    (adj_dec : DecidableRel adj) :
    FiniteRelation (Finset E) where
  adj := adj
  symm := adj_symm
  irrefl := adj_irrefl
  decidable_adj := adj_dec

/-- A symmetric irreflexive face relation has a singleton induced leaf subfamily
inside every nonempty face family. -/
theorem exists_leaf_face {faces : Finset (Finset E)}
    (adj : Finset E → Finset E → Prop)
    (adj_symm : ∀ {f g}, adj f g → adj g f)
    (adj_irrefl : ∀ f, ¬ adj f f)
    (adj_dec : DecidableRel adj)
    (hfaces : faces.Nonempty) :
    ∃ T ⊆ faces, ∃ f ∈ T,
      ((T.erase f).filter (fun g => adj f g)).card ≤ 1 := by
  classical
  let G := FaceRelation adj adj_symm adj_irrefl adj_dec
  obtain ⟨T, hTsub, f, hfT, hleaf⟩ :=
    G.exists_singleton_leaf_subset faces hfaces
  refine ⟨T, hTsub, f, hfT, ?_⟩
  simpa [FiniteRelation.degreeOn, G] using hleaf

omit [Fintype E] in
/-- A deliberately weak face-leaf lemma that needs no relation hypotheses:
choose a singleton subfamily. -/
theorem exists_leaf_face_trivial {faces : Finset (Finset E)}
    (adj : Finset E → Finset E → Prop)
    (_adj_dec : DecidableRel adj)
    (hfaces : faces.Nonempty) :
    ∃ T ⊆ faces, ∃ f ∈ T,
      ((T.erase f).filter (fun g => adj f g)).card ≤ 1 := by
  classical
  rcases hfaces with ⟨f0, hf0⟩
  refine ⟨{f0}, ?_, f0, ?_, ?_⟩
  · simp [hf0]
  · simp
  · simp

end Mettapedia.GraphTheory
