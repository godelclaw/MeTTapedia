import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# The fork law for interface colour support

Pieces of a cubic map compose along a tree, because the monoidal product is
disjoint union.  This file proves the law that composition obeys, for the
colour coordinate, directly against literal colourings.

A piece is a finite set of edges.  What it presents at its interface is, for
each vertex, the set of colours its own edges carry there.  The fork law says
that merging two edge-disjoint pieces merges those sets, and that the only
constraint is disjointness at each vertex:

  support (A union B)
    = image (fun pq => merge pq.1 pq.2)
        (filter Compatible (support A times support B))

Both inclusions are about actual proper colourings, so this is the fork
analogue of the serial transfer's exactness, not a restatement of it.

The interface is then shown to be all that varies: off the middle set a
piece's presentation is determined by the piece alone, so the number of
individual presentations in one support at an interface of `k` vertices is
at most `8 ^ k`.  This does not bound the number of distinct supports by
`8 ^ k`: a powerset bound is needed for that separate state count.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ForkInterfaceSupport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A proper colouring of a piece: edges of the piece meeting at a vertex
carry different colours. -/
def Proper (inc : E → Finset V) (S : Finset E) (c : E → Fin 3) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (inc e ∩ inc f).Nonempty → c e ≠ c f

instance (inc : E → Finset V) (S : Finset E) :
    DecidablePred (Proper inc S) := by
  unfold Proper; infer_instance

/-- What the piece presents at a vertex: the colours its own edges carry. -/
def profile (inc : E → Finset V) (S : Finset E) (c : E → Fin 3) :
    V → Finset (Fin 3) :=
  fun v => (S.filter (fun e => v ∈ inc e)).image c

/-- The interface behaviour of a piece: every presentation it realizes. -/
def support (inc : E → Finset V) (S : Finset E) :
    Finset (V → Finset (Fin 3)) :=
  (Finset.univ.filter (Proper inc S)).image (profile inc S)

def merge (p q : V → Finset (Fin 3)) : V → Finset (Fin 3) := fun v => p v ∪ q v

/-- Two presentations compose exactly when they clash at no vertex. -/
def Compatible (p q : V → Finset (Fin 3)) : Prop := ∀ v, Disjoint (p v) (q v)

instance : DecidablePred (fun pq : (V → Finset (Fin 3)) × (V → Finset (Fin 3)) =>
    Compatible pq.1 pq.2) := by
  unfold Compatible; infer_instance

theorem mem_support {inc : E → Finset V} {S : Finset E} {p : V → Finset (Fin 3)} :
    p ∈ support inc S ↔ ∃ c, Proper inc S c ∧ profile inc S c = p := by
  simp [support, Finset.mem_image, Finset.mem_filter]

omit [Fintype V] [Fintype E] in
theorem profile_union (inc : E → Finset V) (A B : Finset E) (c : E → Fin 3) :
    profile inc (A ∪ B) c = merge (profile inc A c) (profile inc B c) := by
  funext v
  simp only [profile, merge, Finset.filter_union, Finset.image_union]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem proper_of_subset {inc : E → Finset V} {S T : Finset E} (h : S ⊆ T)
    {c : E → Fin 3} (hc : Proper inc T c) : Proper inc S c :=
  fun e he f hf hef hmeet => hc e (h he) f (h hf) hef hmeet

/-- **The fork law.** Merging edge-disjoint pieces merges their presentations,
and disjointness at every vertex is the only constraint. -/
theorem support_union (inc : E → Finset V) (A B : Finset E)
    (hAB : Disjoint A B) :
    support inc (A ∪ B) =
      (((support inc A) ×ˢ (support inc B)).filter
        (fun pq => Compatible pq.1 pq.2)).image (fun pq => merge pq.1 pq.2) := by
  ext p
  constructor
  · intro hp
    obtain ⟨c, hc, rfl⟩ := mem_support.mp hp
    refine Finset.mem_image.mpr ⟨(profile inc A c, profile inc B c), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mem_support.mpr ⟨c, proper_of_subset Finset.subset_union_left hc, rfl⟩
      · exact mem_support.mpr ⟨c, proper_of_subset Finset.subset_union_right hc, rfl⟩
      · intro v
        rw [Finset.disjoint_left]
        rintro x hx hy
        simp only [profile, Finset.mem_image, Finset.mem_filter] at hx hy
        obtain ⟨e, ⟨heA, hev⟩, rfl⟩ := hx
        obtain ⟨f, ⟨hfB, hfv⟩, hfe⟩ := hy
        have hne : e ≠ f := by
          rintro rfl
          exact (Finset.disjoint_left.mp hAB heA) hfB
        exact hc e (Finset.mem_union_left _ heA) f (Finset.mem_union_right _ hfB)
          hne ⟨v, Finset.mem_inter.mpr ⟨hev, hfv⟩⟩ hfe.symm
    · exact (profile_union inc A B c).symm
  · intro hp
    obtain ⟨⟨q, r⟩, hmem, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hprod, hcompat⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hq, hr⟩ := Finset.mem_product.mp hprod
    obtain ⟨a, ha, rfl⟩ := mem_support.mp hq
    obtain ⟨b, hb, rfl⟩ := mem_support.mp hr
    classical
    refine mem_support.mpr ⟨fun e => if e ∈ A then a e else b e, ?_, ?_⟩
    · intro e he f hf hef hmeet
      obtain ⟨v, hv⟩ := hmeet
      obtain ⟨hev, hfv⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp he with heA | heB <;>
        rcases Finset.mem_union.mp hf with hfA | hfB
      · simpa [heA, hfA] using ha e heA f hfA hef ⟨v, hv⟩
      · have hfA : f ∉ A := Finset.disjoint_right.mp hAB hfB
        simp only [heA, if_pos, hfA, if_neg, not_false_iff]
        intro hcol
        have : a e ∈ profile inc A a v :=
          Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heA, hev⟩, rfl⟩
        have hb' : b f ∈ profile inc B b v :=
          Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hfB, hfv⟩, rfl⟩
        rw [hcol] at this
        exact (Finset.disjoint_left.mp (hcompat v) this) hb'
      · have heA' : e ∉ A := Finset.disjoint_right.mp hAB heB
        simp only [heA', if_neg, not_false_iff, hfA, if_pos]
        intro hcol
        have hb' : b e ∈ profile inc B b v :=
          Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heB, hev⟩, rfl⟩
        have : a f ∈ profile inc A a v :=
          Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hfA, hfv⟩, rfl⟩
        rw [← hcol] at this
        exact (Finset.disjoint_left.mp (hcompat v) this) hb'
      · have heA' : e ∉ A := Finset.disjoint_right.mp hAB heB
        have hfA' : f ∉ A := Finset.disjoint_right.mp hAB hfB
        simpa [heA', hfA'] using hb e heB f hfB hef ⟨v, hv⟩
    · rw [profile_union]
      funext v
      have hA : profile inc A (fun e => if e ∈ A then a e else b e) v
          = profile inc A a v := by
        simp only [profile]
        refine Finset.image_congr ?_
        intro e he
        exact if_pos (Finset.mem_filter.mp he).1
      have hB : profile inc B (fun e => if e ∈ A then a e else b e) v
          = profile inc B b v := by
        simp only [profile]
        refine Finset.image_congr ?_
        intro e he
        exact if_neg (Finset.disjoint_right.mp hAB (Finset.mem_filter.mp he).1)
      simp only [merge, hA, hB]

/-! ## Only the interface varies -/

/-- Vertices where the piece meets its complement. -/
def mid (inc : E → Finset V) (S : Finset E) : Finset V :=
  Finset.univ.filter fun v =>
    (S.filter fun e => v ∈ inc e).Nonempty ∧ (Sᶜ.filter fun e => v ∈ inc e).Nonempty

/-- Away from the interface the presentation does not depend on the colouring:
either no edge of the piece is present, or all three are and their colours
exhaust the palette. -/
theorem profile_of_not_mem_mid (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (S : Finset E) {c : E → Fin 3} (hc : Proper inc S c) {v : V}
    (hv : v ∉ mid inc S) :
    profile inc S c v =
      if (S.filter fun e => v ∈ inc e).Nonempty then Finset.univ else ∅ := by
  by_cases hsome : (S.filter fun e => v ∈ inc e).Nonempty
  · rw [if_pos hsome]
    have hnone : ¬ (Sᶜ.filter fun e => v ∈ inc e).Nonempty := fun h =>
      hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsome, h⟩)
    have hall : Finset.univ.filter (fun e => v ∈ inc e) ⊆ S := by
      intro e he
      by_contra hne
      exact hnone ⟨e, Finset.mem_filter.mpr
        ⟨Finset.mem_compl.mpr hne, (Finset.mem_filter.mp he).2⟩⟩
    have hEq : S.filter (fun e => v ∈ inc e)
        = Finset.univ.filter (fun e => v ∈ inc e) :=
      Finset.Subset.antisymm
        (fun e he => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
        (fun e he => Finset.mem_filter.mpr ⟨hall he, (Finset.mem_filter.mp he).2⟩)
    have hinj : Set.InjOn c (Finset.univ.filter fun e => v ∈ inc e) := by
      intro e he f hf hef
      by_contra hne
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
      exact hc e (hall (Finset.mem_coe.mp he)) f (hall (Finset.mem_coe.mp hf)) hne
        ⟨v, Finset.mem_inter.mpr ⟨he'.2, hf'.2⟩⟩ hef
    have hcard : (profile inc S c v).card = 3 := by
      simp only [profile, hEq]
      rw [Finset.card_image_of_injOn hinj, hcubic v]
    exact Finset.eq_univ_of_card _ (by simpa using hcard)
  · rw [if_neg hsome]
    simp only [profile]
    rw [Finset.not_nonempty_iff_eq_empty.mp hsome, Finset.image_empty]

/-- **Finitely many interface behaviours**, with an explicit bound: a piece
whose interface has `k` vertices realizes at most `8 ^ k` presentations. -/
theorem card_support_le (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (S : Finset E) :
    (support inc S).card ≤ 8 ^ (mid inc S).card := by
  have hinj : Set.InjOn (fun (p : V → Finset (Fin 3)) (v : mid inc S) => p v.1)
      (support inc S) := by
    intro p hp q hq hpq
    obtain ⟨a, ha, rfl⟩ := mem_support.mp (Finset.mem_coe.mp hp)
    obtain ⟨b, hb, rfl⟩ := mem_support.mp (Finset.mem_coe.mp hq)
    funext v
    by_cases hv : v ∈ mid inc S
    · exact congrFun hpq ⟨v, hv⟩
    · rw [profile_of_not_mem_mid inc hcubic S ha hv,
        profile_of_not_mem_mid inc hcubic S hb hv]
  calc (support inc S).card
      = ((support inc S).image
          (fun (p : V → Finset (Fin 3)) (v : mid inc S) => p v.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card ((mid inc S) → Finset (Fin 3)) := Finset.card_le_univ _
    _ = 8 ^ (mid inc S).card := by
        rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_coe,
          Fintype.card_fin]
        norm_num

/-! ## A fork audit replayed in the kernel

The smallest simple cubic map, split into two pieces of three edges.  Each
piece's interface behaviour is computed, the compatible pairs are merged, and
the result is checked nonempty -- all by kernel evaluation.  The fork law then
turns that computation into an actual colouring of the whole map, so the audit
is consumed rather than merely reported.
-/

section Audit

set_option Elab.async false
set_option maxRecDepth 8000

/-- `K4`, the smallest simple cubic map. -/
def K4 : Fin 6 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

theorem K4_cubic :
    ∀ v : Fin 4, (Finset.univ.filter fun e => v ∈ K4 e).card = 3 := by
  decide +kernel

def leftPiece : Finset (Fin 6) := {0, 1, 2}

def rightPiece : Finset (Fin 6) := {3, 4, 5}

theorem pieces_disjoint : Disjoint leftPiece rightPiece := by decide +kernel

theorem pieces_cover : leftPiece ∪ rightPiece = Finset.univ := by decide +kernel

/-- **The audit.** Some pair of interface behaviours, one from each piece,
is compatible. -/
theorem fork_audit :
    (((support K4 leftPiece ×ˢ support K4 rightPiece).filter
      fun pq => Compatible pq.1 pq.2)).Nonempty := by
  decide +kernel

/-- **The audit is consumed.** Through the fork law it yields a literal proper
colouring of the whole map. -/
theorem K4_properColouring : ∃ c : Fin 6 → Fin 3, Proper K4 Finset.univ c := by
  have hne : (support K4 Finset.univ).Nonempty := by
    rw [← pieces_cover, support_union K4 leftPiece rightPiece pieces_disjoint]
    exact fork_audit.image _
  obtain ⟨p, hp⟩ := hne
  obtain ⟨c, hc, -⟩ := mem_support.mp hp
  exact ⟨c, hc⟩

/-- The compatibility filter is load bearing: dropping it admits presentations
the map does not realize. -/
theorem compatibility_is_load_bearing :
    ((support K4 leftPiece ×ˢ support K4 rightPiece).image
      fun pq => merge pq.1 pq.2) ≠ support K4 Finset.univ := by
  decide +kernel

/-- The interface of each piece, and the bound the census measures against. -/
theorem piece_interface_card : (mid K4 leftPiece).card = 3 := by decide +kernel

end Audit

end GoertzelV24ForkInterfaceSupport

end Mettapedia.GraphTheory.FourColor
