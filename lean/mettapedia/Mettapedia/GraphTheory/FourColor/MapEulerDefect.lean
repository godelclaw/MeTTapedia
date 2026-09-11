import Mettapedia.GraphTheory.FourColor.PlanarMapBoundaryRestriction
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact handle creation in an edge presentation

For a fixed rotation, the Euler defect `E + 2C - V - F` increases by
two exactly when a new edge merges two faces in one existing component.
An edge between components merges those components and their faces;
an edge within one face splits it. Both have zero defect increment.

The statement includes disconnected presentations and repeated edge
transpositions. In a genuine ribbon graph the defect is twice the total
genus. Its exact recursion supplies the physical evaluator's irreversible
topology-rejection rule; no colouring or bounded-width premise is used.
-/

namespace Mettapedia.GraphTheory.FourColor.MapEulerDefect

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open GoertzelV24MapEulerBound PlanarMapBoundaryRestriction

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A transposition across components merges exactly two quotient classes. -/
theorem component_drop {L : List (Perm D)} {a b : D}
    (hab : ¬ WordReachable L a b) :
    wordOrbitCount L = wordOrbitCount (swap a b :: L) + 1 := by
  let f : Quotient (wordSetoid L) → Quotient (wordSetoid (swap a b :: L)) :=
    Quotient.lift (fun u => Quotient.mk (wordSetoid (swap a b :: L)) u)
      (fun _ _ huv => Quotient.sound
        (wordReachable_mono (fun _ hg => List.mem_cons_of_mem _ hg) huv))
  have hs : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q
    exact ⟨Quotient.mk (wordSetoid L) z, rfl⟩
  have hn : ¬ Function.Injective f := by
    intro hi
    apply hab
    apply Quotient.exact (s := wordSetoid L)
    apply hi (a₁ := Quotient.mk (wordSetoid L) a) (a₂ := Quotient.mk (wordSetoid L) b)
    change Quotient.mk (wordSetoid (swap a b :: L)) a = Quotient.mk _ b
    apply Quotient.sound
    change WordReachable (swap a b :: L) a b
    simpa using wordReachable_step (L := swap a b :: L) List.mem_cons_self a
  have hlt := Fintype.card_lt_of_surjective_not_injective f hs hn
  change wordOrbitCount (swap a b :: L) < wordOrbitCount L at hlt
  have hle := wordOrbitCount_le_cons_swap_add_one L a b
  omega

def defect (rho : Perm D) (edges : List (D × D)) : Int :=
  (edges.length : Int) + 2 * wordOrbitCount (rho :: swapGenerators edges) -
    orbitCount rho - orbitCount (rho * swapProduct edges)

/-- The tested face positions are the images of the new endpoints under
`rho`, as required by the prepend convention for the edge product. -/
def CreatesHandle (rho : Perm D) (e : D × D) (rest : List (D × D)) : Prop :=
  WordReachable (rho :: swapGenerators rest) e.1 e.2 ∧
    ¬ (rho * swapProduct rest).SameCycle (rho e.1) (rho e.2)

theorem connected_of_same_face (rho : Perm D) (e : D × D) (rest : List (D × D))
    (h : (rho * swapProduct rest).SameCycle (rho e.1) (rho e.2)) :
    WordReachable (rho :: swapGenerators rest) e.1 e.2 := by
  have ha : WordReachable (rho :: swapGenerators rest) e.1 (rho e.1) :=
    wordReachable_step List.mem_cons_self _
  have hb : WordReachable (rho :: swapGenerators rest) e.2 (rho e.2) :=
    wordReachable_step List.mem_cons_self _
  exact ha.trans ((wordReachable_of_sameCycle_mul rho rest h).trans hb.symm)

omit [Fintype D] in
/-- At fresh boundary darts the old edge product is fixed, so the two
face-coordinate conventions agree. This hypothesis is essential for
arbitrary edge words with overlapping transpositions. -/
theorem same_face_iff_of_fresh (rho : Perm D) (e : D × D) (rest : List (D × D))
    (ha : swapProduct rest e.1 = e.1) (hb : swapProduct rest e.2 = e.2) :
    (rho * swapProduct rest).SameCycle (rho e.1) (rho e.2) ↔
      (rho * swapProduct rest).SameCycle e.1 e.2 := by
  have hca : (rho * swapProduct rest).SameCycle e.1 (rho e.1) :=
    ⟨1, by simp [Perm.mul_apply, ha]⟩
  have hcb : (rho * swapProduct rest).SameCycle e.2 (rho e.2) :=
    ⟨1, by simp [Perm.mul_apply, hb]⟩
  exact ⟨fun h => hca.trans (h.trans hcb.symm), fun h => hca.symm.trans (h.trans hcb)⟩

@[simp] theorem defect_nil (rho : Perm D) : defect rho [] = 0 := by
  simp only [defect, List.length_nil, Nat.cast_zero, swapGenerators_nil,
    wordOrbitCount_singleton, swapProduct_nil, mul_one]
  omega

/-- The exact defect increment, with no planarity assumption. -/
theorem defect_cons (rho : Perm D) (e : D × D) (rest : List (D × D))
    (hne : e.1 ≠ e.2) :
    defect rho (e :: rest) = defect rho rest +
      if CreatesHandle rho e rest then 2 else 0 := by
  have hn : rho e.1 ≠ rho e.2 := fun h => hne (rho.injective h)
  by_cases hc : WordReachable (rho :: swapGenerators rest) e.1 e.2
  · have hcomp : wordOrbitCount (rho :: swapGenerators (e :: rest)) =
        wordOrbitCount (rho :: swapGenerators rest) := by
      rw [componentCount_cons, wordOrbitCount_cons_swap_eq_of_reachable hc]
    by_cases hf : (rho * swapProduct rest).SameCycle (rho e.1) (rho e.2)
    · have hface : orbitCount (rho * swapProduct (e :: rest)) =
          orbitCount (rho * swapProduct rest) + 1 := by
        rw [face_cons, orbitCount_swap_mul_of_sameCycle _ hn hf]
      rw [if_neg (by simp [CreatesHandle, hf])]
      simp only [defect, List.length_cons, hcomp, hface, Nat.cast_add, Nat.cast_one]
      omega
    · have hface : orbitCount (rho * swapProduct rest) =
          orbitCount (rho * swapProduct (e :: rest)) + 1 := by
        rw [face_cons]
        exact orbitCount_swap_mul_of_not_sameCycle _ hn hf
      rw [if_pos ⟨hc, hf⟩]
      simp only [defect, List.length_cons, hcomp, Nat.cast_add, Nat.cast_one]
      omega
  · have hcomp : wordOrbitCount (rho :: swapGenerators rest) =
        wordOrbitCount (rho :: swapGenerators (e :: rest)) + 1 := by
      rw [componentCount_cons]
      exact component_drop hc
    have hf : ¬ (rho * swapProduct rest).SameCycle (rho e.1) (rho e.2) :=
      fun h => hc (connected_of_same_face rho e rest h)
    have hface : orbitCount (rho * swapProduct rest) =
        orbitCount (rho * swapProduct (e :: rest)) + 1 := by
      rw [face_cons]
      exact orbitCount_swap_mul_of_not_sameCycle _ hn hf
    rw [if_neg (fun h => hc h.1)]
    simp only [defect, List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- Physical insertion at two as-yet-unpaired boundary darts permits
testing the old face cycles directly at the two ports. -/
theorem defect_cons_fresh (rho : Perm D) (e : D × D) (rest : List (D × D))
    (hne : e.1 ≠ e.2) (ha : swapProduct rest e.1 = e.1) (hb : swapProduct rest e.2 = e.2) :
    defect rho (e :: rest) = defect rho rest +
      if WordReachable (rho :: swapGenerators rest) e.1 e.2 ∧
        ¬ (rho * swapProduct rest).SameCycle e.1 e.2 then 2 else 0 := by
  rw [defect_cons rho e rest hne]
  simp only [CreatesHandle, same_face_iff_of_fresh rho e rest ha hb]

/-- Counts the actual handle-creating steps, evaluated from the tail up. -/
def handles (rho : Perm D) : List (D × D) → Nat
  | [] => 0
  | e :: rest => handles rho rest + if CreatesHandle rho e rest then 1 else 0

theorem defect_eq_twice_handles (rho : Perm D) (edges : List (D × D))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2) :
    defect rho edges = 2 * (handles rho edges : Int) := by
  induction edges with
  | nil => simp [handles]
  | cons e rest ih =>
    rw [defect_cons rho e rest (hne e List.mem_cons_self),
      ih (fun f hf => hne f (List.mem_cons_of_mem _ hf))]
    simp only [handles]
    split_ifs <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;> omega

theorem defect_nonneg (rho : Perm D) (edges : List (D × D))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2) : 0 ≤ defect rho edges := by
  rw [defect_eq_twice_handles rho edges hne]
  omega

theorem defect_mono (rho : Perm D) (added base : List (D × D))
    (hne : ∀ e ∈ added, e.1 ≠ e.2) :
    defect rho base ≤ defect rho (added ++ base) := by
  induction added with
  | nil => exact le_rfl
  | cons e rest ih =>
    have hh := ih (fun f hf => hne f (List.mem_cons_of_mem _ hf))
    rw [List.cons_append, defect_cons rho e (rest ++ base) (hne e List.mem_cons_self)]
    split_ifs <;> omega

theorem plane_iff_defect_zero (rho : Perm D) (edges : List (D × D)) :
    PlaneEdges rho edges ↔ defect rho edges = 0 := by
  unfold PlaneEdges defect
  omega

theorem plane_iff_no_handles (rho : Perm D) (edges : List (D × D))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2) :
    PlaneEdges rho edges ↔ handles rho edges = 0 := by
  rw [plane_iff_defect_zero, defect_eq_twice_handles rho edges hne]
  omega

/-- A rejected prefix cannot be repaired by any later edge additions. -/
theorem no_planar_completion (rho : Perm D) (added base : List (D × D))
    (hne : ∀ e ∈ added, e.1 ≠ e.2) (hbad : 0 < defect rho base) :
    ¬ PlaneEdges rho (added ++ base) := by
  intro hp
  have hh := defect_mono rho added base hne
  have hz := (plane_iff_defect_zero rho (added ++ base)).mp hp
  omega

end
end Mettapedia.GraphTheory.FourColor.MapEulerDefect
