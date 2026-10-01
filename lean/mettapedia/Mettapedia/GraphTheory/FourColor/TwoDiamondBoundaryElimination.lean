import Mettapedia.GraphTheory.FourColor.DiamondBoundaryElimination

/-!
# Two diamond interiors with one shared tip

Each diamond keeps its centre and tip choices. Gluing the diamonds identifies
their first tips, so the summaries must agree on that actual colour. The
equivalence below retains complete witnesses, with arbitrary attachments and
arbitrary predicates on the exterior. It makes no universal extension or
reducibility claim.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoDiamondBoundaryElimination

open DiamondBoundaryElimination

variable {B C : Type*}

/-- The common tip is zero; positions one to three and four to six are
the centres and other tip of the respective diamonds. -/
def left (i : Fin 4) : Fin 7 :=
  match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | _ => 3
def right (i : Fin 4) : Fin 7 :=
  match i.val with | 0 => 4 | 1 => 0 | 2 => 5 | _ => 6

def coreAdj (i j : Fin 7) : Prop :=
  (∃ a b, left a = i ∧ left b = j ∧ DiamondBoundaryElimination.coreAdj a b) ∨
  (∃ a b, right a = i ∧ right b = j ∧ DiamondBoundaryElimination.coreAdj a b)

instance : DecidableRel coreAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def graph (H : SimpleGraph B) (N : Fin 7 → B → Prop) : SimpleGraph (B ⊕ Fin 7) where
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
      change coreAdj i j at h
      revert h i j
      decide⟩
  loopless := ⟨by
    rintro (b | i) h
    · exact H.loopless.irrefl b h
    · have hn : ∀ i : Fin 7, ¬ coreAdj i i := by decide
      exact hn i h⟩

instance (H : SimpleGraph B) (N : Fin 7 → B → Prop)
    [DecidableRel H.Adj] [∀ i b, Decidable (N i b)] :
    DecidableRel (graph H N).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [graph] <;> infer_instance

/-- The interface retains agreement at the shared vertex. -/
structure Summary (N : Fin 7 → B → Prop) (b : B → C) where
  first : DiamondBoundaryElimination.Summary (fun i => N (left i)) b
  second : DiamondBoundaryElimination.Summary (fun i => N (right i)) b
  shared : first.lower.val = second.lower.val

namespace Summary

variable {N : Fin 7 → B → Prop} {b : B → C} (s : Summary N b)

def value (i : Fin 7) : C :=
  match i.val with
  | 0 => s.first.lower.val
  | 1 => s.first.first
  | 2 => s.first.second
  | 3 => s.first.upper.val
  | 4 => s.second.first
  | 5 => s.second.second
  | _ => s.second.upper.val

@[simp] theorem value_left (i : Fin 4) :
    s.value (left i) = s.first.value i := by fin_cases i <;> rfl

@[simp] theorem value_right (i : Fin 4) :
    s.value (right i) = s.second.value i := by
  fin_cases i
  · rfl
  · exact s.shared
  · rfl
  · rfl

theorem allowed (i : Fin 7) : ∀ v, N i v → s.value i ≠ b v := by
  fin_cases i
  · exact s.first.lower.property.1
  · exact s.first.first_allowed
  · exact s.first.second_allowed
  · exact s.first.upper.property.1
  · exact s.second.first_allowed
  · exact s.second.second_allowed
  · exact s.second.upper.property.1

theorem core_valid (i j : Fin 7) (h : coreAdj i j) : s.value i ≠ s.value j := by
  rcases h with ⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩
  · simpa only [value_left] using s.first.core_valid a b h
  · simpa only [value_right] using s.second.core_valid a b h

end Summary

variable (H : SimpleGraph B) (N : Fin 7 → B → Prop)

def restrict (k : (graph H N).Coloring C) : H.Coloring C :=
  .mk (fun b => k (.inl b)) (fun {v w} h =>
    k.valid (show (graph H N).Adj (.inl v) (.inl w) from h))

def leftColoring (k : (graph H N).Coloring C) :
    (DiamondBoundaryElimination.graph H (fun i => N (left i))).Coloring C :=
  .mk (Sum.elim (fun b => k (.inl b)) (fun i => k (.inr (left i)))) (by
    rintro (v | i) (w | j) h
    · exact k.valid h
    · exact k.valid h
    · exact k.valid h
    · exact k.valid (Or.inl ⟨i, j, rfl, rfl, h⟩))

def rightColoring (k : (graph H N).Coloring C) :
    (DiamondBoundaryElimination.graph H (fun i => N (right i))).Coloring C :=
  .mk (Sum.elim (fun b => k (.inl b)) (fun i => k (.inr (right i)))) (by
    rintro (v | i) (w | j) h
    · exact k.valid h
    · exact k.valid h
    · exact k.valid h
    · exact k.valid (Or.inr ⟨i, j, rfl, rfl, h⟩))

def eliminate (k : (graph H N).Coloring C) : Summary N (restrict H N k) where
  first := DiamondBoundaryElimination.eliminate H _ (leftColoring H N k)
  second := DiamondBoundaryElimination.eliminate H _ (rightColoring H N k)
  shared := rfl

def reconstruct (b : H.Coloring C) (s : Summary N b) : (graph H N).Coloring C :=
  .mk (Sum.elim b s.value) (by
    rintro (v | i) (w | j) h
    · exact b.valid h
    · exact (s.allowed j v h).symm
    · exact s.allowed i w h
    · exact s.core_valid i j h)

@[simp] theorem reconstruct_boundary (b : H.Coloring C) (s : Summary N b) (v : B) :
    reconstruct H N b s (.inl v) = b v := rfl

theorem reconstruct_eliminate (k : (graph H N).Coloring C) :
    reconstruct H N (restrict H N k) (eliminate H N k) = k := by
  apply DFunLike.ext
  rintro (v | i)
  · rfl
  · fin_cases i <;> rfl

def coloringEquiv : (graph H N).Coloring C ≃ (Σ b : H.Coloring C, Summary N b) where
  toFun k := ⟨restrict H N k, eliminate H N k⟩
  invFun p := reconstruct H N p.1 p.2
  left_inv := reconstruct_eliminate H N
  right_inv p := by
    rcases p with ⟨b, s⟩
    rcases s with ⟨⟨a, c, hac, ha, hc, ⟨l, hl⟩, ⟨u, hu⟩⟩,
      ⟨a', c', hac', ha', hc', ⟨l', hl'⟩, ⟨u', hu'⟩⟩, shared⟩
    cases shared
    rfl

/-- Every additional observation of the joint exterior is preserved. -/
theorem context_iff (accepts : (B → C) → Prop) :
    (∃ k : (graph H N).Coloring C, accepts (fun b => k (.inl b))) ↔
      ∃ p : (Σ b : H.Coloring C, Summary N b), accepts p.1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨coloringEquiv H N k, hk⟩
  · rintro ⟨p, hp⟩
    exact ⟨(coloringEquiv H N).symm p, hp⟩

end Mettapedia.GraphTheory.FourColor.TwoDiamondBoundaryElimination
