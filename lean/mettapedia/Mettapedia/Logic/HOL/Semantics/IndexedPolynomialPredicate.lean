import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.Semantics.Henkin
import Mettapedia.TypeTheory.IndexedPolynomialGuardedRepresentation

/-!
# HOL least predicates on unindexed polynomial trees

A shared single-operator signature supports both raw-tree and source-family
interpretations. The raw-tree operator builds actual constructor nodes while
retaining the result index and every child occurrence. Its HOL least predicate
recognizes exactly the recursive index guard, at arbitrary polynomial
universes. Missing points, absent raw nodes and malformed children are refused.
Native recursive-space operations and their certificates remain separate.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PolynomialPredicate.OperatorSignature
abbrev element : Ty Unit := .base ()
inductive Const : Ty Unit → Type where
  | operator : Const ((element ⇒ .prop) ⇒ element ⇒ .prop)
end Mettapedia.Logic.HOL.PolynomialPredicate.OperatorSignature

namespace Mettapedia.Logic.HOL.PolynomialPredicate.RawInterpretation
open Mettapedia.TypeTheory
open IndexedPolynomial
open Mettapedia.Logic.HOL
universe b i s p q
variable {Base : Type b} {Index : Base → Type i}
variable (P : IndexedPolynomial.{b, i, s, p} Base Index) (slots : GuardedRaw.Positions.{b, i, s, p, q} P) (base : Base)

abbrev Carrier := ULift.{1} (Option (Σ _index : Index base, GuardedRaw.Tree P slots base))

def valid (point : Carrier P slots base) : Prop :=
  match point.down with
  | none => False
  | some indexed => GuardedRaw.Valid P slots indexed.2 indexed.1

def step (property : Carrier P slots base → Prop) (point : Carrier P slots base) : Prop :=
  ∃ (index : Index base) (shape : P.Shape base index)
      (children : P.Position shape → GuardedRaw.Tree P slots base),
    point.down = some ⟨index, Fix.roll (polynomial := GuardedRaw.polynomial P slots) (some ⟨index, shape⟩) ((slots.coding shape).extend (GuardedRaw.absent P slots base) children)⟩ ∧
      ∀ position, property (.up (some ⟨P.next shape position, children position⟩))

def model : HenkinModel.{0, 0, max i s q} Unit OperatorSignature.Const :=
  .standard (fun _ => Carrier P slots base)
    (fun symbol => match symbol with
      | .operator => fun property point => .up (step P slots base (fun child => (property child).down) point))

def emptyValuation : (model P slots base).Valuation [] := fun impossible => nomatch impossible

def member (point : Carrier P slots base) : Prop :=
  ((model P slots base).denote (PredicateFixedPoint.least (.const .operator)) (emptyValuation P slots base) point).down

theorem step_monotone (first second : Carrier P slots base → Prop)
    (inclusion : ∀ point, first point → second point) (point : Carrier P slots base) :
    step P slots base first point → step P slots base second point := by
  rintro ⟨index, shape, children, root, hypotheses⟩
  exact ⟨index, shape, children, root, fun position => inclusion _ (hypotheses position)⟩

theorem model_monotone : (model P slots base).models (PredicateFixedPoint.monotone (.const .operator)) := by
  intro first _ second _ inclusion point _ present
  exact step_monotone P slots base _ _ (fun child => inclusion child trivial) point present

theorem closed_contains (property : Carrier P slots base → Prop)
    (closed : ∀ point, step P slots base property point → property point)
    (index : Index base) (source : Fix P base index) :
    property (.up (some ⟨index, GuardedRaw.encode P slots source⟩)) := by
  induction source with
  | roll shape children hypotheses =>
    exact closed _ ⟨_, shape, (fun position => GuardedRaw.encode P slots (children position)), rfl, hypotheses⟩

theorem member_iff_valid (point : Carrier P slots base) : member P slots base point ↔ valid P slots base point := by
  constructor
  · intro present
    exact present (fun candidate => .up (valid P slots base candidate)) trivial (by
      intro candidate _ generated
      change step P slots base (valid P slots base) candidate at generated
      rcases generated with ⟨index, shape, children, root, indexed⟩
      change valid P slots base candidate
      unfold valid
      rw [root]
      refine ⟨rfl, (slots.coding shape).extend_canonical _ _, ?_⟩
      intro position
      change GuardedRaw.Valid P slots ((slots.coding shape).extend _ _ ((slots.coding shape).encode position)) _
      rw [Mettapedia.TypeTheory.IndexedPolynomial.SlotEncoding.extend_at]
      exact indexed position)
  · intro indexed property _ closed
    cases point with
    | up point =>
      cases point with
      | none => cases indexed
      | some point =>
        have generated := closed_contains P slots base (fun child => (property child).down)
          (fun child derivation => closed child trivial derivation)
          point.1 (GuardedRaw.decode P slots point.2 point.1 indexed)
        change (property (.up (some point))).down
        rw [GuardedRaw.encode_decode P slots point.2 point.1 indexed] at generated
        exact generated

noncomputable def sourcePoint (index : Index base) (source : Fix P base index) : Carrier P slots base :=
  .up (some ⟨index, GuardedRaw.encode P slots source⟩)

theorem sourcePoint_member (index : Index base) (source : Fix P base index) :
    member P slots base (sourcePoint P slots base index source) :=
  (member_iff_valid P slots base _).mpr (GuardedRaw.encode_valid P slots source)

theorem absent_not_member : ¬ member P slots base (.up none) :=
  fun present => (member_iff_valid P slots base _).mp present

theorem absent_tree_not_member (index : Index base) :
    ¬ member P slots base (.up (some ⟨index, GuardedRaw.absent P slots base⟩)) :=
  fun present => GuardedRaw.absent_not_valid P slots base index ((member_iff_valid P slots base _).mp present)

#print axioms member_iff_valid
end Mettapedia.Logic.HOL.PolynomialPredicate.RawInterpretation
namespace Mettapedia.Logic.HOL.PolynomialPredicate.RawInterpretation.Controls
open Mettapedia.TypeTheory.IndexedPolynomial
open GuardedRaw.Controls

noncomputable def vectorOne : Carrier vectorPolynomial vectorPositions .star :=
  sourcePoint vectorPolynomial vectorPositions .star 1
    (VectorExample.cons true (VectorExample.nil (A := Bool)))

theorem vector_one_member : member vectorPolynomial vectorPositions .star vectorOne :=
  sourcePoint_member vectorPolynomial vectorPositions .star 1 _

noncomputable def malformed : Carrier vectorPolynomial vectorPositions .star :=
  .up (some ⟨2, malformedVectorTree⟩)

theorem malformed_not_member : ¬ member vectorPolynomial vectorPositions .star malformed :=
  fun present => malformed_refused ((member_iff_valid vectorPolynomial vectorPositions .star _).mp present)

end Mettapedia.Logic.HOL.PolynomialPredicate.RawInterpretation.Controls
#print axioms Mettapedia.TypeTheory.IndexedPolynomial.GuardedRaw.Controls.one_roundtrip
#print axioms Mettapedia.Logic.HOL.PolynomialPredicate.RawInterpretation.Controls.malformed_not_member
