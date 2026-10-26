import Mettapedia.TypeTheory.IndexedPolynomialRepresentation
import Mathlib.Data.Fin.Basic

/-!
# Guarded representations of indexed polynomial families

A partial position encoding retains each recursive occurrence and identifies
unused stored slots. The raw tree stores the original result index and shape.
Its validity guard checks every required child and canonical padding outside
the position image. Encoding and proof-directed decoding are inverse and
preserve constructors. Validity is exactly least constructor-closed membership.
Direct positions and finite-to-natural slots instantiate the same construction.
These are semantic representations; executable storage and native recursive-
space comparison retain their separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPolynomial
universe u v w

structure SlotEncoding (Position : Type u) (Slot : Type v) where
  encode : Position → Slot
  decode : Slot → Option Position
  decode_encode : ∀ position, decode (encode position) = some position
  encode_decode : ∀ slot position, decode slot = some position → encode position = slot

namespace SlotEncoding
variable {Position : Type u} {Slot : Type v} {A : Type w}
variable (encoding : SlotEncoding Position Slot)

def extend (default : A) (values : Position → A) (slot : Slot) : A :=
  match encoding.decode slot with
  | none => default
  | some position => values position

def restrict (values : Slot → A) (position : Position) : A := values (encoding.encode position)

def Canonical (default : A) (values : Slot → A) : Prop :=
  ∀ slot, encoding.decode slot = none → values slot = default

theorem extend_at (default : A) (values : Position → A) (position : Position) :
    encoding.extend default values (encoding.encode position) = values position := by
  simp only [extend, encoding.decode_encode]

theorem extend_canonical (default : A) (values : Position → A) :
    encoding.Canonical default (encoding.extend default values) := by
  intro slot absent
  simp only [extend, absent]

theorem restrict_extend (default : A) (values : Position → A) :
    encoding.restrict (encoding.extend default values) = values := by
  funext position
  exact encoding.extend_at default values position

theorem extend_restrict (default : A) (values : Slot → A)
    (canonical : encoding.Canonical default values) :
    encoding.extend default (encoding.restrict values) = values := by
  funext slot
  cases decoded : encoding.decode slot with
  | none => simpa only [extend, decoded] using (canonical slot decoded).symm
  | some position =>
      simpa only [extend, decoded, restrict] using congrArg values (encoding.encode_decode slot position decoded)

def equivalence (default : A) :
    (Position → A) ≃ {values : Slot → A // encoding.Canonical default values} where
  toFun := fun values => ⟨encoding.extend default values, encoding.extend_canonical default values⟩
  invFun := fun values => encoding.restrict values.val
  left_inv := encoding.restrict_extend default
  right_inv := fun values => Subtype.ext (encoding.extend_restrict default values.val values.property)

def direct (Position : Type u) : SlotEncoding Position Position where
  encode := id
  decode := some
  decode_encode := fun _ => rfl
  encode_decode := fun _ _ same => (Option.some.inj same).symm

def finite {count : Nat} (positions : Position ≃ Fin count) : SlotEncoding Position Nat where
  encode := fun position => (positions position).val
  decode := fun slot => if inside : slot < count then some (positions.symm ⟨slot, inside⟩) else none
  decode_encode := by
    intro position
    simp only [dif_pos (positions position).isLt]
    apply congrArg some
    exact (congrArg positions.symm (Fin.ext rfl)).trans (positions.symm_apply_apply position)
  encode_decode := by
    intro slot position decoded
    split at decoded
    · rename_i inside
      have same := Option.some.inj decoded
      rw [← same, Equiv.apply_symm_apply]
    · cases decoded

theorem finite_decoded_iff {count : Nat} (positions : Position ≃ Fin count) (slot : Nat) :
    (finite positions).decode slot = none ↔ count ≤ slot := by
  simp only [finite]
  split
  · rename_i inside
    simp only [reduceCtorEq, false_iff, Nat.not_le]
    exact inside
  · rename_i outside
    simp only [true_iff]
    exact Nat.le_of_not_gt outside

namespace Controls

def one := finite (Equiv.refl (Fin 1))
def hiddenTail : Nat → Nat := fun slot => if slot = 0 then 7 else 9

theorem tail_refused : ¬ one.Canonical 0 hiddenTail := by
  intro canonical
  have impossible := canonical 1 (by decide)
  change (9 : Nat) = 0 at impossible
  cases impossible

theorem layer_roundtrip :
    (one.equivalence (0 : Nat)).symm ((one.equivalence 0) (fun _ => 7)) = (fun _ => 7) :=
  (one.equivalence (0 : Nat)).symm_apply_apply _

end Controls
#print axioms equivalence
#print axioms finite
#print axioms Controls.tail_refused
end SlotEncoding
end Mettapedia.TypeTheory.IndexedPolynomial

namespace Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
universe b i s p q
variable {Base : Type b} {Index : Base → Type i}
variable (P : IndexedPolynomial.{b, i, s, p} Base Index)

structure Positions where
  Slot : {base : Base} → {index : Index base} → P.Shape base index → Type q
  coding : ∀ {base index} (shape : P.Shape base index), SlotEncoding (P.Position shape) (Slot shape)

variable (slots : Positions.{b, i, s, p, q} P)

def polynomial : IndexedPolynomial.{b, 0, max i s, q} Base (fun _ => PUnit) where
  Shape := fun base _ => Option (Σ index, P.Shape base index)
  Position := fun shape => match shape with
    | none => PEmpty
    | some point => slots.Slot point.2
  next := fun _ _ => PUnit.unit

abbrev Tree (base : Base) := Fix (polynomial P slots) base PUnit.unit

def absent (base : Base) : Tree P slots base := .roll none (fun impossible => PEmpty.elim impossible)

noncomputable def encode : ∀ {base : Base} {index : Index base}, Fix P base index → Tree P slots base :=
  fun {base index} source => Fix.eliminate P (fun base _ _ => Tree P slots base)
    (fun base index shape _children encoded =>
      .roll (some ⟨index, shape⟩) ((slots.coding shape).extend (absent P slots base) encoded)) base index source

noncomputable def Valid {base : Base} (tree : Tree P slots base) : Index base → Prop :=
  Fix.eliminate (polynomial P slots) (fun base _ _ => Index base → Prop)
    (fun base _ shape children indexed => match shape with
      | none => fun _ => False
      | some point => fun index => index = point.1 ∧
          (slots.coding point.2).Canonical (absent P slots base) children ∧
          ∀ position, indexed ((slots.coding point.2).encode position) (P.next point.2 position))
    base PUnit.unit tree

theorem encode_valid {base : Base} {index : Index base} (source : Fix P base index) :
    Valid P slots (encode P slots source) index := by
  induction source with
  | roll shape children hypotheses =>
    refine ⟨rfl, (slots.coding shape).extend_canonical _ _, ?_⟩
    intro position
    change Valid P slots ((slots.coding shape).extend _ _ ((slots.coding shape).encode position)) _
    rw [SlotEncoding.extend_at]
    exact hypotheses position

def atUnit {base : Base} {rawIndex : PUnit} (raw : Fix (polynomial P slots) base rawIndex) : Tree P slots base := by
  cases rawIndex
  exact raw

noncomputable def decode {base : Base} (tree : Tree P slots base) (index : Index base)
    (valid : Valid P slots tree index) : Fix P base index := by
  have decoded : ∀ rawIndex (raw : Fix (polynomial P slots) base rawIndex),
      ∀ index, Valid P slots (atUnit P slots raw) index → Fix P base index :=
    Fix.eliminate (polynomial P slots)
      (fun base rawIndex raw => ∀ index, Valid P slots (atUnit P slots raw) index → Fix P base index)
      (by
        intro base rawIndex shape children hypotheses index present
        cases rawIndex
        cases shape with
        | none => exact False.elim present
        | some point =>
          change index = point.1 ∧ (slots.coding point.2).Canonical (absent P slots base) children ∧
            ∀ position, Valid P slots (children ((slots.coding point.2).encode position)) (P.next point.2 position) at present
          exact present.1.symm ▸ Fix.roll point.2 (fun position =>
            hypotheses ((slots.coding point.2).encode position) (P.next point.2 position) (present.2.2 position))) base
  exact decoded PUnit.unit tree index valid

theorem encode_roll {base : Base} {index : Index base} (shape : P.Shape base index)
    (children : ∀ position, Fix P base (P.next shape position)) :
    encode P slots (Fix.roll shape children) =
      Fix.roll (polynomial := polynomial P slots) (some ⟨index, shape⟩)
        ((slots.coding shape).extend (absent P slots base) (fun position => encode P slots (children position))) := rfl

theorem decode_encode {base : Base} {index : Index base} (source : Fix P base index) :
    decode P slots (encode P slots source) index (encode_valid P slots source) = source := by
  induction source with
  | roll shape children hypotheses =>
    change Fix.roll shape (fun position => decode P slots
      ((slots.coding shape).extend (absent P slots _)
        (fun position => encode P slots (children position)) ((slots.coding shape).encode position))
      _ _) = Fix.roll shape children
    congr 1
    funext position
    simpa only [SlotEncoding.extend_at] using hypotheses position

theorem encode_decode {base : Base} (tree : Tree P slots base) (index : Index base)
    (valid : Valid P slots tree index) : encode P slots (decode P slots tree index valid) = tree := by
  have reconstruction : ∀ rawIndex (raw : Fix (polynomial P slots) base rawIndex),
      ∀ index (present : Valid P slots (atUnit P slots raw) index),
        encode P slots (decode P slots (atUnit P slots raw) index present) = atUnit P slots raw :=
    Fix.eliminate (polynomial P slots)
      (fun base rawIndex raw => ∀ index (present : Valid P slots (atUnit P slots raw) index),
        encode P slots (decode P slots (atUnit P slots raw) index present) = atUnit P slots raw)
      (by
        intro base rawIndex shape children hypotheses index present
        cases rawIndex
        cases shape with
        | none => exact False.elim present
        | some point =>
          change index = point.1 ∧ (slots.coding point.2).Canonical (absent P slots base) children ∧
            ∀ position, Valid P slots (children ((slots.coding point.2).encode position)) (P.next point.2 position) at present
          rcases present with ⟨same, canonical, indexed⟩
          cases same
          change Fix.roll (polynomial := polynomial P slots) (some point)
            ((slots.coding point.2).extend (absent P slots base)
              (fun position => encode P slots (decode P slots
                (children ((slots.coding point.2).encode position)) (P.next point.2 position) (indexed position)))) =
            Fix.roll (polynomial := polynomial P slots) (some point) children
          congr 1
          funext slot
          cases decoded : (slots.coding point.2).decode slot with
          | none => simpa only [SlotEncoding.extend, decoded] using (canonical slot decoded).symm
          | some position =>
            simp only [SlotEncoding.extend, decoded]
            exact (hypotheses ((slots.coding point.2).encode position) _ _).trans
              (congrArg (fun slot => atUnit P slots (children slot))
                ((slots.coding point.2).encode_decode slot position decoded))) base
  exact reconstruction PUnit.unit tree index valid

noncomputable def representation (base : Base) (index : Index base) :
    Fix P base index ≃ {tree : Tree P slots base // Valid P slots tree index} where
  toFun := fun source => ⟨encode P slots source, encode_valid P slots source⟩
  invFun := fun tree => decode P slots tree.val index tree.property
  left_inv := decode_encode P slots
  right_inv := fun tree => Subtype.ext (encode_decode P slots tree.val index tree.property)

#print axioms representation
end Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw

namespace Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
universe b i s p q
variable {Base : Type b} {Index : Base → Type i}
variable (P : IndexedPolynomial.{b, i, s, p} Base Index) (slots : Positions.{b, i, s, p, q} P)

abbrev Family (base : Base) (index : Index base) := {tree : Tree P slots base // Valid P slots tree index}

def algebra : Algebra P (Family P slots) where
  act base index layer :=
    ⟨Fix.roll (polynomial := polynomial P slots) (some ⟨index, layer.1⟩)
      ((slots.coding layer.1).extend (absent P slots base) (fun position => (layer.2 position).val)),
      ⟨rfl, (slots.coding layer.1).extend_canonical _ _, by
        intro position
        change Valid P slots ((slots.coding layer.1).extend _ _ ((slots.coding layer.1).encode position)) _
        rw [SlotEncoding.extend_at]
        exact (layer.2 position).property⟩⟩

noncomputable def algebraRepresentation : Algebra.Representation P (algebra P slots) where
  toEquiv := representation P slots
  commutes := by
    intro base index layer
    cases layer with
    | mk shape children =>
      apply Subtype.ext
      exact encode_roll P slots shape children
end Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw

namespace Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
universe b i s p q
variable {Base : Type b} {Index : Base → Type i}
variable (P : IndexedPolynomial.{b, i, s, p} Base Index) (slots : Positions.{b, i, s, p, q} P)

def step (property : ∀ base, Index base → Tree P slots base → Prop)
    (base : Base) (index : Index base) (tree : Tree P slots base) : Prop :=
  ∃ (shape : P.Shape base index) (children : P.Position shape → Tree P slots base),
    tree = Fix.roll (polynomial := polynomial P slots) (some ⟨index, shape⟩)
      ((slots.coding shape).extend (absent P slots base) children) ∧
      ∀ position, property base (P.next shape position) (children position)

theorem valid_iff_step (base : Base) (index : Index base) (tree : Tree P slots base) :
    Valid P slots tree index ↔ step P slots (fun _ index tree => Valid P slots tree index) base index tree := by
  constructor
  · intro valid
    have reconstruction := encode_decode P slots tree index valid
    cases sourceResult : Fix.out P (decode P slots tree index valid) with
    | mk shape children =>
      have rebuilt : decode P slots tree index valid = Fix.roll shape children := by
        simpa only [sourceResult, Fix.rollExtension] using
          (Fix.rollExtension_out P (decode P slots tree index valid)).symm
      rw [rebuilt, encode_roll] at reconstruction
      exact ⟨shape, (fun position => encode P slots (children position)), reconstruction.symm,
        fun position => encode_valid P slots (children position)⟩
  · rintro ⟨shape, children, rfl, indexed⟩
    refine ⟨rfl, (slots.coding shape).extend_canonical _ _, ?_⟩
    intro position
    change Valid P slots ((slots.coding shape).extend _ _ ((slots.coding shape).encode position)) _
    rw [SlotEncoding.extend_at]
    exact indexed position

def Closed (property : ∀ base, Index base → Tree P slots base → Prop) : Prop :=
  ∀ base index tree, step P slots property base index tree → property base index tree

theorem closed_contains (property : ∀ base, Index base → Tree P slots base → Prop)
    (closed : Closed P slots property) {base : Base} {index : Index base} (source : Fix P base index) :
    property base index (encode P slots source) := by
  induction source with
  | roll shape children hypotheses =>
    exact closed _ _ _ ⟨shape, (fun position => encode P slots (children position)), rfl, hypotheses⟩

def member (base : Base) (index : Index base) (tree : Tree P slots base) : Prop :=
  ∀ property : ∀ base, Index base → Tree P slots base → Prop,
    Closed P slots property → property base index tree

theorem member_iff_valid (base : Base) (index : Index base) (tree : Tree P slots base) :
    member P slots base index tree ↔ Valid P slots tree index := by
  constructor
  · intro present
    exact present (fun _ index tree => Valid P slots tree index)
      (fun base index tree generated => (valid_iff_step P slots base index tree).mpr generated)
  · intro valid property closed
    have generated := closed_contains P slots property closed (decode P slots tree index valid)
    rw [encode_decode P slots tree index valid] at generated
    exact generated

end Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
#print axioms Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw.member_iff_valid

namespace Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
universe b i s p q
variable {Base : Type b} {Index : Base → Type i}
variable (P : IndexedPolynomial.{b, i, s, p} Base Index)

def directPositions : Positions.{b, i, s, p, p} P where
  Slot := P.Position
  coding := fun shape => SlotEncoding.direct (P.Position shape)

variable (slots : Positions.{b, i, s, p, q} P)

theorem valid_index_unique {base : Base} {tree : Tree P slots base} {first second : Index base}
    (left : Valid P slots tree first) (right : Valid P slots tree second) : first = second := by
  cases layerResult : Fix.out (polynomial P slots) tree with
  | mk shape children =>
    have rebuilt : tree = Fix.roll (polynomial := polynomial P slots) shape children := by
      simpa only [layerResult, Fix.rollExtension] using
        (Fix.rollExtension_out (polynomial P slots) tree).symm
    rw [rebuilt] at left right
    cases shape with
    | none => exact False.elim left
    | some point => exact left.1.trans right.1.symm

theorem wrong_child_refused {base : Base} {index : Index base} (shape : P.Shape base index)
    (children : slots.Slot shape → Tree P slots base) (position : P.Position shape)
    (invalid : ¬ Valid P slots (children ((slots.coding shape).encode position)) (P.next shape position)) :
    ¬ Valid P slots (Fix.roll (polynomial := polynomial P slots) (some ⟨index, shape⟩) children) index := by
  intro indexed
  exact invalid (indexed.2.2 position)

theorem wrong_padding_refused {base : Base} {index : Index base} (shape : P.Shape base index)
    (children : slots.Slot shape → Tree P slots base)
    (invalid : ¬ (slots.coding shape).Canonical (absent P slots base) children) :
    ¬ Valid P slots (Fix.roll (polynomial := polynomial P slots) (some ⟨index, shape⟩) children) index :=
  fun indexed => invalid indexed.2.1

theorem absent_not_valid (base : Base) (index : Index base) :
    ¬ Valid P slots (absent P slots base) index := by exact id

theorem step_monotone
    (first second : ∀ base, Index base → Tree P slots base → Prop)
    (inclusion : ∀ base index tree, first base index tree → second base index tree)
    (base : Base) (index : Index base) (tree : Tree P slots base) :
    step P slots first base index tree → step P slots second base index tree := by
  rintro ⟨shape, children, root, valid⟩
  exact ⟨shape, children, root, fun position => inclusion _ _ _ (valid position)⟩

end Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw

namespace Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
namespace Controls
open VectorExample

abbrev vectorPolynomial := VectorExample.polynomial Bool
abbrev vectorPositions := directPositions vectorPolynomial

noncomputable def emptyVectorTree : Tree vectorPolynomial vectorPositions (.star) :=
  encode vectorPolynomial vectorPositions (VectorExample.nil (A := Bool))

noncomputable def oneVectorTree : Tree vectorPolynomial vectorPositions (.star) :=
  encode vectorPolynomial vectorPositions (VectorExample.cons true (VectorExample.nil (A := Bool)))

theorem one_valid : Valid vectorPolynomial vectorPositions oneVectorTree 1 :=
  encode_valid vectorPolynomial vectorPositions _

theorem empty_wrong_index : ¬ Valid vectorPolynomial vectorPositions emptyVectorTree 1 := by
  intro wrong
  have impossible : (0 : Nat) = 1 := valid_index_unique vectorPolynomial vectorPositions
    (encode_valid vectorPolynomial vectorPositions (VectorExample.nil (A := Bool))) wrong
  cases impossible

noncomputable def malformedVectorTree : Tree vectorPolynomial vectorPositions (.star) :=
  Fix.roll (polynomial := polynomial vectorPolynomial vectorPositions) (some ⟨2, VectorExample.Shape.cons 1 true⟩)
    (fun _ => emptyVectorTree)

theorem malformed_refused : ¬ Valid vectorPolynomial vectorPositions malformedVectorTree 2 :=
  wrong_child_refused vectorPolynomial vectorPositions (VectorExample.Shape.cons 1 true)
    (fun _ => emptyVectorTree) .star empty_wrong_index

theorem one_roundtrip :
    decode vectorPolynomial vectorPositions oneVectorTree 1 one_valid =
      VectorExample.cons true (VectorExample.nil (A := Bool)) :=
  decode_encode vectorPolynomial vectorPositions _

theorem one_reencoded :
    encode vectorPolynomial vectorPositions (decode vectorPolynomial vectorPositions oneVectorTree 1 one_valid) = oneVectorTree :=
  encode_decode vectorPolynomial vectorPositions _ _ one_valid

theorem one_index_unique : (1 : Nat) = 1 :=
  valid_index_unique vectorPolynomial vectorPositions one_valid one_valid

end Controls
end Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw
namespace Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw.Controls

theorem one_member : member vectorPolynomial vectorPositions .star 1 oneVectorTree :=
  (member_iff_valid vectorPolynomial vectorPositions _ _ _).mpr one_valid

theorem malformed_not_member : ¬ member vectorPolynomial vectorPositions .star 2 malformedVectorTree :=
  fun present => malformed_refused ((member_iff_valid vectorPolynomial vectorPositions _ _ _).mp present)

end Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw.Controls
#print axioms Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw.Controls.one_roundtrip
#print axioms Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw.Controls.malformed_not_member
