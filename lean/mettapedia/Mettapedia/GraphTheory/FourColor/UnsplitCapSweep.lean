import Mettapedia.GraphTheory.FourColor.GoertzelV24MeshIsoperimetry
import Mathlib.Tactic

/-!
# Complete interfaces cannot ignore attachments to unsplit caps

An explicit zigzag ring sits between two cyclic caps. The shell alone is
a cycle. Any full vertex cut containing exactly half of the shell, with
each cap wholly on one side, crosses at least n edges. This applies to
every shell order and allows either ownership of either cap at every step.

The conclusion concerns full edge cuts, not optimal branchwidth: caps may
be split, and a simultaneous whole-graph slice has a bounded interface.
This is an auxiliary geometric obstruction, not a zero-Count theorem.
The finite gate separately checks the spherical embeddings.
-/

namespace Mettapedia.GraphTheory.FourColor.UnsplitCapSweep

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry

abbrev Vertex (k : Nat) := Fin 4 × Fin (k + 3)
abbrev Edge (k : Nat) := Fin 6 × Fin (k + 3)
abbrev Slot (k : Nat) := Fin 2 × Fin (k + 3)

def next {k : Nat} (i : Fin (k + 3)) : Fin (k + 3) :=
  ⟨(i.val + 1) % (k + 3), Nat.mod_lt _ (by omega)⟩

def graph (k : Nat) : Multigraph (Vertex k) (Edge k) where
  fst e := match e.1.val with
    | 0 => (0, e.2)
    | 1 => (0, e.2)
    | 2 => (1, e.2)
    | 3 => (2, e.2)
    | 4 => (2, e.2)
    | _ => (3, e.2)
  snd e := match e.1.val with
    | 0 => (0, next e.2)
    | 1 => (1, e.2)
    | 2 => (2, e.2)
    | 3 => (1, next e.2)
    | 4 => (3, e.2)
    | _ => (3, next e.2)

def shellVertex {k : Nat} (p : Slot k) : Vertex k :=
  (if p.1 = 0 then 1 else 2, p.2)

def spoke {k : Nat} (p : Slot k) : Edge k :=
  (if p.1 = 0 then 1 else 4, p.2)

def seen {k : Nat} (S : Finset (Vertex k)) : Finset (Slot k) :=
  Finset.univ.filter fun p => shellVertex p ∈ S

def unseen {k : Nat} (S : Finset (Vertex k)) : Finset (Slot k) :=
  Finset.univ.filter fun p => shellVertex p ∉ S

/-- No condition on the side chosen for the cap, only that it is unsplit. -/
def Atomic {k : Nat} (S : Finset (Vertex k)) (row : Fin 4) : Prop :=
  (∀ i, (row, i) ∈ S) ∨ (∀ i, (row, i) ∉ S)

theorem spoke_injective {k : Nat} : Function.Injective (@spoke k) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  have hij : i = j := congrArg Prod.snd h
  subst j
  fin_cases a <;> fin_cases b <;> simp_all [spoke]

theorem seen_add_unseen {k : Nat} (S : Finset (Vertex k)) :
    (seen S).card + (unseen S).card = 2 * (k + 3) := by
  simpa [seen, unseen, Slot] using
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Slot k)))
      (fun p => shellVertex p ∈ S)

theorem outside_caps {k : Nat} (S : Finset (Vertex k))
    (h0 : ∀ i, ((0 : Fin 4), i) ∉ S) (h3 : ∀ i, ((3 : Fin 4), i) ∉ S) :
    (seen S).card ≤ (boundaryEdges (graph k) S).card := by
  have hsub : (seen S).image spoke ⊆ boundaryEdges (graph k) S := by
    intro e he
    obtain ⟨⟨b, i⟩, hp, rfl⟩ := Finset.mem_image.mp he
    have hs := (Finset.mem_filter.mp hp).2
    fin_cases b <;> simp_all [seen, shellVertex, spoke, boundaryEdges, IsBoundaryEdge, graph]
  exact (Finset.card_image_of_injective _ spoke_injective).symm.trans_le
    (Finset.card_le_card hsub)

theorem boundary_compl {k : Nat} (S : Finset (Vertex k)) :
    boundaryEdges (graph k) Sᶜ = boundaryEdges (graph k) S := by
  ext e
  simp only [boundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    IsBoundaryEdge, Finset.mem_compl, not_not]
  tauto

theorem inside_caps {k : Nat} (S : Finset (Vertex k))
    (h0 : ∀ i, ((0 : Fin 4), i) ∈ S) (h3 : ∀ i, ((3 : Fin 4), i) ∈ S) :
    (unseen S).card ≤ (boundaryEdges (graph k) S).card := by
  have h := outside_caps Sᶜ (by simpa) (by simpa)
  simpa [seen, unseen, boundary_compl] using h

/-- Distinct three-edge columns charge distinct crossing edges when caps
are on opposite sides. No particular shell ordering is involved. -/
theorem opposite_caps {k : Nat} (S : Finset (Vertex k))
    (h0 : ∀ i, ((0 : Fin 4), i) ∈ S) (h3 : ∀ i, ((3 : Fin 4), i) ∉ S) :
    k + 3 ≤ (boundaryEdges (graph k) S).card := by
  let f : Fin (k + 3) → Edge k := fun i =>
    (if ((1 : Fin 4), i) ∉ S then 1 else if ((2 : Fin 4), i) ∉ S then 2 else 4, i)
  have hinj : Function.Injective f := fun i j h => congrArg Prod.snd h
  have hsub : Finset.univ.image f ⊆ boundaryEdges (graph k) S := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    dsimp [f]
    split_ifs <;> simp_all [boundaryEdges, IsBoundaryEdge, graph]
  have h := (Finset.card_image_of_injective Finset.univ hinj).symm.trans_le
    (Finset.card_le_card hsub)
  simpa using h

/-- At half of the shell, every atomic-cap ownership has a large FULL cut. -/
theorem balanced_cut {k : Nat} (S : Finset (Vertex k))
    (hhalf : (seen S).card = k + 3) (h0 : Atomic S 0) (h3 : Atomic S 3) :
    k + 3 ≤ (boundaryEdges (graph k) S).card := by
  rcases h0 with h0 | h0 <;> rcases h3 with h3 | h3
  · have h := inside_caps S h0 h3
    have hc := seen_add_unseen S
    omega
  · exact opposite_caps S h0 h3
  · have h := opposite_caps Sᶜ (by simpa) (by simpa)
    simpa only [boundary_compl] using h
  · simpa only [hhalf] using outside_caps S h0 h3

/-- The middle prefix of ANY shell-vertex order forces the same bound.
Whole caps may switch sides independently at every stage. -/
theorem sweep_width_lower_bound {k : Nat}
    (order : Fin (2 * (k + 3)) ≃ Slot k)
    (sides : Nat → Finset (Vertex k))
    (hprefix : ∀ t p, shellVertex p ∈ sides t ↔ (order.symm p).val < t)
    (h0 : ∀ t, Atomic (sides t) 0) (h3 : ∀ t, Atomic (sides t) 3) :
    k + 3 ≤ (boundaryEdges (graph k) (sides (k + 3))).card := by
  have heq : seen (sides (k + 3)) =
      (Finset.Iio (⟨k + 3, by omega⟩ : Fin (2 * (k + 3)))).image order := by
    ext p
    simp only [seen, Finset.mem_filter, Finset.mem_univ, true_and, hprefix,
      Finset.mem_image, Finset.mem_Iio]
    constructor
    · intro h
      exact ⟨order.symm p, h, order.apply_symm_apply p⟩
    · rintro ⟨i, hi, rfl⟩
      change i.val < k + 3 at hi
      simpa using hi
  apply balanced_cut _ _ (h0 _) (h3 _)
  rw [heq, Finset.card_image_of_injective _ order.injective]
  simp

/-- Realize the sweeps in the bound, with arbitrary ownership of whole caps. -/
def sweepSide {k : Nat} (order : Fin (2 * (k + 3)) ≃ Slot k)
    (t : Nat) (outer inner : Bool) : Finset (Vertex k) :=
  Finset.univ.filter fun v =>
    if v.1 = 0 then outer = true else if v.1 = 3 then inner = true
    else (order.symm (if v.1 = 1 then 0 else 1, v.2)).val < t

theorem sweepSide_prefix {k : Nat} (order : Fin (2 * (k + 3)) ≃ Slot k)
    (t : Nat) (outer inner : Bool) (p : Slot k) :
    shellVertex p ∈ sweepSide order t outer inner ↔ (order.symm p).val < t := by
  rcases p with ⟨b, i⟩
  fin_cases b <;> simp [shellVertex, sweepSide]

theorem sweepSide_atomic {k : Nat} (order : Fin (2 * (k + 3)) ≃ Slot k)
    (t : Nat) (outer inner : Bool) :
    Atomic (sweepSide order t outer inner) 0 ∧ Atomic (sweepSide order t outer inner) 3 := by
  cases outer <;> cases inner <;> simp [Atomic, sweepSide]

/-- No uniform full-width bound exists for unsplit-cap sweeps of this family.
The quantifiers include every order and every stagewise choice of cap side. -/
theorem unbounded_unsplit_cap_sweeps (w : Nat) :
    ∃ k : Nat, ∀ order : Fin (2 * (k + 3)) ≃ Slot k, ∀ outer inner : Nat → Bool,
      w < (boundaryEdges (graph k)
        (sweepSide order (k + 3) (outer (k + 3)) (inner (k + 3)))).card := by
  refine ⟨w, ?_⟩
  intro order outer inner
  have h := sweep_width_lower_bound order
    (fun t => sweepSide order t (outer t) (inner t))
    (fun t p => sweepSide_prefix order t _ _ p)
    (fun t => (sweepSide_atomic order t _ _).1)
    (fun t => (sweepSide_atomic order t _ _).2)
  omega

/-- The escape control cuts through both caps as well as the shell. -/
def slice {k : Nat} (t : Nat) : Finset (Vertex k) :=
  Finset.univ.filter fun v => v.2.val < t

theorem next_val {k : Nat} (i : Fin (k + 3)) :
    (next i).val = if i.val + 1 < k + 3 then i.val + 1 else 0 := by
  dsimp [next]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hi : i.val + 1 = k + 3 := by have := i.isLt; omega
    simp [hi]

theorem crossing_next {k t : Nat} (ht : 0 < t) (_ht' : t < k + 3)
    (i : Fin (k + 3))
    (h : (i.val < t ∧ ¬ (next i).val < t) ∨ (¬ i.val < t ∧ (next i).val < t)) :
    i.val = t - 1 ∨ i.val = k + 2 := by
  rw [next_val] at h
  split_ifs at h <;> have := i.isLt <;> omega

/-- In the permissive whole-graph slice, at most six original edges cross.
This is why the atomic-cap lower bound is not a branchwidth lower bound. -/
theorem slice_width_le_six {k t : Nat} (ht : 0 < t) (ht' : t < k + 3) :
    (boundaryEdges (graph k) (slice t)).card ≤ 6 := by
  let kinds : Fin 3 → Fin 6 := fun j => if j = 0 then 0 else if j = 1 then 3 else 5
  let f : Fin 3 × Fin 2 → Edge k := fun p =>
    (kinds p.1, if p.2 = 0 then ⟨t - 1, by omega⟩ else ⟨k + 2, by omega⟩)
  have hsub : boundaryEdges (graph k) (slice t) ⊆ Finset.univ.image f := by
    rintro ⟨kind, i⟩ he
    have he' := (Finset.mem_filter.mp he).2
    have mk (j : Fin 3) (hj : kinds j = kind)
        (h : i.val = t - 1 ∨ i.val = k + 2) : (kind, i) ∈ Finset.univ.image f := by
      rcases h with h | h
      · refine Finset.mem_image.mpr ⟨(j, 0), Finset.mem_univ _, ?_⟩
        apply Prod.ext
        · exact hj
        · apply Fin.ext; simpa [f] using h.symm
      · refine Finset.mem_image.mpr ⟨(j, 1), Finset.mem_univ _, ?_⟩
        apply Prod.ext
        · exact hj
        · apply Fin.ext; simpa [f] using h.symm
    fin_cases kind
    · exact mk 0 (by simp [kinds]) (crossing_next ht ht' i (by
        simpa [IsBoundaryEdge, graph, slice] using he'))
    · simp [IsBoundaryEdge, graph, slice] at he'; omega
    · simp [IsBoundaryEdge, graph, slice] at he'; omega
    · exact mk 1 (by simp [kinds]) (crossing_next ht ht' i (by
        simpa [IsBoundaryEdge, graph, slice] using he'))
    · simp [IsBoundaryEdge, graph, slice] at he'; omega
    · exact mk 2 (by simp [kinds]) (crossing_next ht ht' i (by
        simpa [IsBoundaryEdge, graph, slice] using he'))
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by decide))

end Mettapedia.GraphTheory.FourColor.UnsplitCapSweep
