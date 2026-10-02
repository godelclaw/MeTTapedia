import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Exact colouring witnesses for wheels with an exterior boundary

One shared centre colour, one cyclic assignment to the rim, and the complete
rim-to-boundary incidence relation determine a colouring. The equivalence
retains the entire witness and fixes every boundary colour. It applies to any
colour type, any boundary graph, and any fixed-point-free successor on the rim.
It asserts exact extension semantics, not the existence of an extension or a
Kempe repair for an arbitrary boundary colouring.
-/

namespace FourColor.WheelColouring

variable {B I C : Type*}

abbrev Vertex (B I : Type*) := B ⊕ Option I

def Adj (H : SimpleGraph B) (next : I → I) (touch : I → B → Prop) :
    Vertex B I → Vertex B I → Prop
  | .inl b, .inl c => H.Adj b c
  | .inl b, .inr (some i) => touch i b
  | .inr (some i), .inl b => touch i b
  | .inr none, .inr (some _) => True
  | .inr (some _), .inr none => True
  | .inr (some i), .inr (some j) => j = next i ∨ i = next j
  | _, _ => False

def graph (H : SimpleGraph B) (next : I → I) (touch : I → B → Prop)
    (loopless : ∀ i, next i ≠ i) : SimpleGraph (Vertex B I) where
  Adj := Adj H next touch
  symm := ⟨by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact h.symm
      | inr b => cases b <;> exact h
    | inr a =>
      cases a with
      | none => cases b with
        | inl b => exact h
        | inr b => cases b <;> exact h
      | some a => cases b with
        | inl b => exact h
        | inr b => cases b with
          | none => exact h
          | some b => exact h.symm⟩
  loopless := ⟨by
    intro a h
    cases a with
    | inl a => exact H.loopless.irrefl a h
    | inr a => cases a with
      | none => exact h
      | some a => exact (loopless a) (h.elim Eq.symm Eq.symm)⟩

instance (H : SimpleGraph B) (next : I → I) (touch : I → B → Prop)
    (loopless : ∀ i, next i ≠ i) [DecidableEq I] [DecidableRel H.Adj]
    [∀ i b, Decidable (touch i b)] : DecidableRel (graph H next touch loopless).Adj := by
  intro a b
  cases a with
  | inl a => cases b with
    | inl b => exact inferInstanceAs (Decidable (H.Adj a b))
    | inr b => cases b <;> dsimp [graph, Adj] <;> infer_instance
  | inr a => cases a <;> cases b with
    | inl b => dsimp [graph, Adj]; infer_instance
    | inr b => cases b <;> dsimp [graph, Adj] <;> infer_instance

structure Witness (next : I → I) (touch : I → B → Prop) (boundary : B → C) where
  center : C
  rim : I → C
  center_ne : ∀ i, rim i ≠ center
  rim_ne : ∀ i, rim i ≠ rim (next i)
  boundary_ne : ∀ i b, touch i b → rim i ≠ boundary b

variable (H : SimpleGraph B) (next : I → I) (touch : I → B → Prop)
  (loopless : ∀ i, next i ≠ i)

def restrict (k : (graph H next touch loopless).Coloring C) : H.Coloring C :=
  .mk (fun b => k (.inl b)) (fun {_ _} h => k.valid h)

def observe (k : (graph H next touch loopless).Coloring C) :
    Witness next touch (restrict H next touch loopless k) where
  center := k (.inr none)
  rim i := k (.inr (some i))
  center_ne i := k.valid (show Adj H next touch (.inr (some i)) (.inr none) from trivial)
  rim_ne i := k.valid (show Adj H next touch (.inr (some i)) (.inr (some (next i)))
    from Or.inl rfl)
  boundary_ne _ _ h := k.valid h

def extend (k : H.Coloring C) (w : Witness next touch k) :
    (graph H next touch loopless).Coloring C :=
  .mk (fun v => v.elim k (fun i => i.elim w.center w.rim)) (by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact k.valid h
      | inr b => cases b with
        | none => exact h.elim
        | some b => exact (w.boundary_ne b a h).symm
    | inr a => cases a with
      | none => cases b with
        | inl b => exact h.elim
        | inr b => cases b with
          | none => exact h.elim
          | some b => exact (w.center_ne b).symm
      | some a => cases b with
        | inl b => exact w.boundary_ne a b h
        | inr b => cases b with
          | none => exact w.center_ne a
          | some b =>
            rcases h with rfl | rfl
            · exact w.rim_ne a
            · exact (w.rim_ne b).symm)

@[simp] theorem extend_boundary (k : H.Coloring C) (w : Witness next touch k) (b : B) :
    extend H next touch loopless k w (.inl b) = k b := rfl

/-- Exact witness transport, including multiplicities and the boundary colouring. -/
def coloringEquiv : (graph H next touch loopless).Coloring C ≃
    (Σ k : H.Coloring C, Witness next touch k) where
  toFun k := ⟨restrict H next touch loopless k, observe H next touch loopless k⟩
  invFun k := extend H next touch loopless k.1 k.2
  left_inv k := by
    ext v
    cases v with
    | inl b => rfl
    | inr i => cases i <;> rfl
  right_inv k := by
    rcases k with ⟨k, z, rim, hc, hr, hb⟩
    rfl

/-- A boundary colouring extends exactly when the joint cyclic choices exist. -/
theorem extends_iff (k : H.Coloring C) :
    (∃ full : (graph H next touch loopless).Coloring C,
      ∀ b, full (.inl b) = k b) ↔ Nonempty (Witness next touch k) := by
  constructor
  · rintro ⟨full, fixed⟩
    have equal : restrict H next touch loopless full = k := by
      ext b
      exact fixed b
    exact ⟨equal ▸ observe H next touch loopless full⟩
  · rintro ⟨w⟩
    exact ⟨extend H next touch loopless k w, fun _ => rfl⟩

end FourColor.WheelColouring
