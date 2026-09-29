import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic.FinCases

/-!
# Exact elimination of a diamond interior

The boundary graph and its attachments may be arbitrary. The interior consists
of two adjacent centres and two nonadjacent tips, each joined to both centres.
Choosing the two distinct centre colours leaves independent choices at the
tips, subject to their boundary neighbours. The resulting equivalence retains
actual colouring witnesses and every predicate on the boundary assignment.

This is an exact boundary summary, not an assertion that an arbitrary boundary
colouring extends or that a boundary insertion preserves reducibility.
-/

namespace Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination

variable {B C : Type*}

/-- Interior positions zero and two are the centres; one and three are the tips. -/
def coreAdj (i j : Fin 4) : Prop :=
  i ≠ j ∧ (i = 0 ∨ i = 2 ∨ j = 0 ∨ j = 2)

instance : DecidableRel coreAdj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Attach the four interior vertices to an arbitrary boundary graph. -/
def graph (H : SimpleGraph B) (N : Fin 4 → B → Prop) : SimpleGraph (B ⊕ Fin 4) where
  Adj x y := match x, y with
    | .inl b, .inl b' => H.Adj b b'
    | .inl b, .inr i => N i b
    | .inr i, .inl b => N i b
    | .inr i, .inr j => coreAdj i j
  symm := ⟨by
    rintro (b | i) (b' | j) h
    · exact H.adj_symm h
    · exact h
    · exact h
    · change coreAdj j i
      rcases h with ⟨hne, h⟩
      exact ⟨hne.symm, by rcases h with h | h | h | h <;> simp [h]⟩⟩
  loopless := ⟨by
    rintro (b | i) h
    · exact H.loopless.irrefl b h
    · exact h.1 rfl⟩

instance (H : SimpleGraph B) (N : Fin 4 → B → Prop)
    [DecidableRel H.Adj] [∀ i b, Decidable (N i b)] :
    DecidableRel (graph H N).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [graph] <;> infer_instance

/-- A core colour avoids all the boundary neighbours of its position. -/
def Allows (N : Fin 4 → B → Prop) (b : B → C) (i : Fin 4) (c : C) : Prop :=
  ∀ v, N i v → c ≠ b v

/-- Both tips retain their own choices, coupled through the same two centres. -/
structure Summary (N : Fin 4 → B → Prop) (b : B → C) where
  first : C
  second : C
  centres_ne : first ≠ second
  first_allowed : Allows N b 0 first
  second_allowed : Allows N b 2 second
  lower : {c : C // Allows N b 1 c ∧ c ≠ first ∧ c ≠ second}
  upper : {c : C // Allows N b 3 c ∧ c ≠ first ∧ c ≠ second}

namespace Summary

variable {N : Fin 4 → B → Prop} {b : B → C} (s : Summary N b)

def value (i : Fin 4) : C :=
  match i.val with
  | 0 => s.first
  | 1 => s.lower.val
  | 2 => s.second
  | _ => s.upper.val

theorem allowed (i : Fin 4) : Allows N b i (s.value i) := by
  fin_cases i
  · exact s.first_allowed
  · exact s.lower.property.1
  · exact s.second_allowed
  · exact s.upper.property.1

theorem core_valid (i j : Fin 4) (h : coreAdj i j) : s.value i ≠ s.value j := by
  have hc := s.centres_ne
  have hl := s.lower.property.2
  have hu := s.upper.property.2
  fin_cases i <;> fin_cases j <;> simp_all [coreAdj, value, ne_comm]

end Summary

variable (H : SimpleGraph B) (N : Fin 4 → B → Prop)

def restrict (k : (graph H N).Coloring C) : H.Coloring C :=
  .mk (fun b => k (.inl b)) (fun {v w} h =>
    k.valid (show (graph H N).Adj (.inl v) (.inl w) from h))

def eliminate (k : (graph H N).Coloring C) : Summary N (restrict H N k) where
  first := k (.inr 0)
  second := k (.inr 2)
  centres_ne := k.valid (by change coreAdj 0 2; decide)
  first_allowed := fun v h => k.valid (show (graph H N).Adj (.inr 0) (.inl v) from h)
  second_allowed := fun v h => k.valid (show (graph H N).Adj (.inr 2) (.inl v) from h)
  lower := ⟨k (.inr 1), (fun v h =>
    k.valid (show (graph H N).Adj (.inr 1) (.inl v) from h)),
    k.valid (by change coreAdj 1 0; decide), k.valid (by change coreAdj 1 2; decide)⟩
  upper := ⟨k (.inr 3), (fun v h =>
    k.valid (show (graph H N).Adj (.inr 3) (.inl v) from h)),
    k.valid (by change coreAdj 3 0; decide), k.valid (by change coreAdj 3 2; decide)⟩

/-- Recover a full colouring from its boundary colouring and coupled summary. -/
def reconstruct (b : H.Coloring C) (s : Summary N b) : (graph H N).Coloring C :=
  .mk (Sum.elim b s.value) (by
    rintro (v | i) (w | j) h
    · exact b.valid h
    · exact (s.allowed j v h).symm
    · exact s.allowed i w h
    · exact s.core_valid i j h)

@[simp] theorem reconstruct_boundary (b : H.Coloring C) (s : Summary N b) (v : B) :
    reconstruct H N b s (.inl v) = b v := rfl

@[simp] theorem restrict_reconstruct (b : H.Coloring C) (s : Summary N b) :
    restrict H N (reconstruct H N b s) = b := rfl

theorem reconstruct_eliminate (k : (graph H N).Coloring C) :
    reconstruct H N (restrict H N k) (eliminate H N k) = k := by
  apply DFunLike.ext
  rintro (v | i)
  · rfl
  · fin_cases i <;> rfl

/-- Witness-level elimination; the two tip choices remain independent only
after the same pair of centre colours has been fixed. -/
def coloringEquiv : (graph H N).Coloring C ≃ (Σ b : H.Coloring C, Summary N b) where
  toFun k := ⟨restrict H N k, eliminate H N k⟩
  invFun k := reconstruct H N k.1 k.2
  left_inv := reconstruct_eliminate H N
  right_inv k := by
    rcases k with ⟨b, s⟩
    cases s
    rfl

/-- Elimination is exact inside any additional constraint on the boundary. -/
theorem context_iff (accepts : (B → C) → Prop) :
    (∃ k : (graph H N).Coloring C, accepts (fun b => k (.inl b))) ↔
      ∃ b : H.Coloring C, Nonempty (Summary N b) ∧ accepts b := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨restrict H N k, ⟨eliminate H N k⟩, hk⟩
  · rintro ⟨b, ⟨s⟩, hb⟩
    exact ⟨reconstruct H N b s, hb⟩

end Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination
