import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalRightLanguageBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24Square

/-!
# Physical bit tests for an exact context code

Two noncrossing digon pairings encode one bit. A triangle with a stem
tests it. All three pieces have four cubic vertices and four ports.
The rejecting closure has a bridge: this is not a lower bound restricted
to bridgeless target-class contexts.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalContextBits

open GoertzelV24OpenTangleComposition GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PhysicalClosedCountBridge GoertzelV24ClosedCountReplacement

inductive Kind | a | b | test
  deriving DecidableEq, Fintype

abbrev I := Fin 4 × Bool
abbrev D := I ⊕ Fin 4

def ends : Kind → Fin 4 → Fin 4 × Fin 4
  | .a | .b => ![(0, 1), (0, 1), (2, 3), (2, 3)]
  | .test => ![(0, 1), (1, 2), (2, 0), (2, 3)]

def port : Kind → Fin 4 → Fin 4
  | .a => ![0, 1, 2, 3]
  | .b => ![0, 2, 3, 1]
  | .test => ![0, 1, 3, 3]

def vertex (t : Kind) : D → Fin 4
  | .inl (e, false) => (ends t e).1
  | .inl (e, true) => (ends t e).2
  | .inr p => port t p

def dartList : Fin 12 → D :=
  ![.inl (0, false), .inl (0, true), .inl (1, false), .inl (1, true),
    .inl (2, false), .inl (2, true), .inl (3, false), .inl (3, true),
    .inr 0, .inr 1, .inr 2, .inr 3]

def dartIndex : D → Fin 12
  | .inl (e, b) => ⟨2 * e.val + if b then 1 else 0, by split <;> omega⟩
  | .inr p => ⟨8 + p.val, by omega⟩

def dartEquiv : D ≃ Fin 12 where
  toFun := dartIndex
  invFun := dartList
  left_inv := by decide
  right_inv := by decide

/-- The cyclic vertex orders of the three ordered-disc pieces. -/
def rhoList : Kind → Fin 12 → Fin 12
  | .a => ![2, 9, 8, 1, 6, 11, 10, 5, 0, 3, 4, 7]
  | .b => ![2, 11, 8, 1, 6, 10, 9, 5, 0, 4, 7, 3]
  | .test => ![5, 9, 1, 6, 3, 8, 4, 10, 0, 2, 11, 7]

def rhoPerm (t : Kind) : Equiv.Perm (Fin 12) where
  toFun := rhoList t
  invFun := fun d => rhoList t (rhoList t d)
  left_inv := by cases t <;> decide
  right_inv := by cases t <;> decide

def localData (t : Kind) : OpenTangleData (Fin 4) I (Fin 4) where
  interiorVert := fun d => vertex t (.inl d)
  boundaryVert := port t
  interiorAlpha := (Equiv.refl (Fin 4)).prodCongr
    (Function.Involutive.toPerm not Bool.not_not)
  interiorAlpha_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  interiorAlpha_fixfree := by rintro ⟨e, b⟩; cases b <;> simp
  interior_no_self_loops := by cases t <;> decide
  rho := dartEquiv.trans ((rhoPerm t).trans dartEquiv.symm)
  vert_rho := by cases t <;> decide
  outer := .inr 0

def colors (w c : Fin 4 → Color) : D → Color
  | .inl (e, _) => c e
  | .inr p => w p

def Valid (t : Kind) (w c : Fin 4 → Color) : Prop :=
  (∀ d, colors w c d ≠ 0) ∧
    ∀ d e, vertex t d = vertex t e → d ≠ e → colors w c d ≠ colors w c e
  deriving Decidable

theorem valid_a (w c : Fin 4 → Color) :
    Valid .a w c ↔
      ProperColorTriple (w 0) (c 0) (c 1) ∧
      ProperColorTriple (w 1) (c 0) (c 1) ∧
      ProperColorTriple (w 2) (c 2) (c 3) ∧
      ProperColorTriple (w 3) (c 2) (c 3) := by
  simp only [Valid, colors, vertex, ends, port, Sum.forall, Prod.forall,
    Bool.forall_bool, Fin.forall_fin_succ, Fin.succ_zero_eq_one,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, ProperColorTriple]
  aesop

theorem valid_test (w c : Fin 4 → Color) :
    Valid .test w c ↔
      ProperColorTriple (w 0) (c 0) (c 2) ∧
      ProperColorTriple (w 1) (c 0) (c 1) ∧
      ProperColorTriple (c 3) (c 1) (c 2) ∧
      ProperColorTriple (c 3) (w 2) (w 3) := by
  simp only [Valid, colors, vertex, ends, port, Sum.forall, Prod.forall,
    Bool.forall_bool, Fin.forall_fin_succ, Fin.succ_zero_eq_one,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, ProperColorTriple]
  aesop

private theorem third_unique : ∀ a b x y : Color,
    ProperColorTriple x a b → ProperColorTriple y a b → x = y := by decide

private theorem triangle_ports_ne : ∀ a b c x y : Color,
    ProperColorTriple x a c → ProperColorTriple y a b → b ≠ c → x ≠ y := by decide

theorem a_rejected {w c d : Fin 4 → Color}
    (ha : Valid .a w c) (ht : Valid .test w d) : False := by
  obtain ⟨ha0, ha1, -⟩ := (valid_a w c).mp ha
  obtain ⟨ht0, ht1, ht2, -⟩ := (valid_test w d).mp ht
  exact triangle_ports_ne _ _ _ _ _ ht0 ht1 ht2.2.2.2.2.2
    (third_unique _ _ _ _ ha0 ha1)

def bitKind (b : Bool) : Kind := if b then .b else .a

theorem neutral_exists (b : Bool) :
    ∃ w c d, Valid (bitKind b) w c ∧ Valid .a w d := by
  refine ⟨fun _ => red, ![blue, purple, blue, purple],
    ![blue, purple, blue, purple], ?_⟩
  cases b <;> decide

theorem b_accepted : ∃ w c d, Valid .b w c ∧ Valid .test w d := by
  refine ⟨![red, blue, blue, red], ![blue, purple, red, purple],
    ![purple, red, blue, purple], ?_⟩
  decide

theorem bit_test (b : Bool) :
    (∃ w c d, Valid (bitKind b) w c ∧ Valid .test w d) ↔ b = true := by
  cases b
  · simp only [Bool.false_eq_true, iff_false, not_exists]
    intro w c d h
    exact a_rejected h.1 h.2
  · exact iff_of_true b_accepted rfl

end Mettapedia.GraphTheory.FourColor.PhysicalContextBits
