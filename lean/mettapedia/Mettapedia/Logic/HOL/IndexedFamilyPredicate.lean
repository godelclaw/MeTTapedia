import Mettapedia.Logic.HOL.RecursiveSpacePredicate
import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpacePredicate

/-!
# HOL predicate operators for indexed polynomial presentations

The interpretation assigns the shape, position and edge symbols their actual
nonrecursive guards from a natural-slot indexed presentation. The compiled
positive operator denotes exactly its guarded constructor step. This model
connection does not supply source definitions of those guards or executable
encoders for arbitrary source declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedFamilyPredicate

open Mettapedia.TypeTheory
open IndexedPolynomial.RecursiveSpaceRepresentation

inductive SortCode where | number | payload | space
abbrev number : Ty SortCode := .base .number
abbrev payload : Ty SortCode := .base .payload
abbrev space : Ty SortCode := .base .space

inductive Symbol : Ty SortCode → Type where
  | bottom : Symbol space
  | construct : Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  | validShape : Symbol (number ⇒ payload ⇒ .prop)
  | active : Symbol (payload ⇒ number ⇒ .prop)
  | validEdge : Symbol (payload ⇒ number ⇒ space ⇒ .prop)

@[reducible] def signature : RecursiveSpacePredicate.Signature Symbol :=
  ⟨number, payload, space, .const .bottom, .const .construct,
    .const .validShape, .const .active, .const .validEdge⟩

universe b i s p
variable {Base : Type b} {Index : Base → Type i}
variable (presentation : Presentation.{b, i, s, p} (Base := Base) (Index := Index))
variable (environment : Base)

def carrier : SortCode → Type (max i s + 1)
  | .number => ULift.{max i s + 1} Nat
  | .payload => ULift.{max i s + 1} (RecursivePayload presentation environment)
  | .space => ULift.{max i s + 1}
      (RecursiveSpace.Tree (RecursivePayload presentation environment))

@[reducible] def model : HenkinModel.{0, 0, max i s + 1} SortCode Symbol :=
  .standard (carrier presentation environment) (fun symbol => match symbol with
    | .bottom => .up RecursiveSpace.bottom
    | .construct => fun tag payload children => .up
        (RecursiveSpace.construct tag.down payload.down (fun n => (children (.up n)).down))
    | .validShape => fun tag payload => .up (shapeGuard presentation tag.down payload.down)
    | .active => fun payload position => .up (activeGuard presentation payload.down position.down)
    | .validEdge => fun payload position child =>
        .up (edgeGuard presentation payload.down position.down child.down))

theorem full : (model presentation environment).FullDomains :=
  HenkinModel.fullDomains_standard _ _

def holds (predicate : RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  (RecursiveSpacePredicate.Signature.denotes (model presentation environment) signature.operator
    (fun value => .up (predicate value.down)) (.up tree)).down

theorem holds_iff
    (predicate : ∀ environment, RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    holds presentation environment (predicate environment) tree ↔
      guardedStep presentation predicate environment tree := by
  unfold holds
  refine (signature.operator_meaning (model presentation environment) (full presentation environment)
    (fun value => .up (predicate environment value.down)) (.up tree)).trans ?_
  constructor
  · rintro ⟨⟨tag⟩, ⟨payload⟩, children, valid, equal, conditions⟩
    refine ⟨tag, payload, (fun n => (children (.up n)).down), valid,
      congrArg ULift.down equal, ?_⟩
    intro n
    exact ⟨fun present => (conditions (.up n)).1 present,
      fun absent => congrArg ULift.down ((conditions (.up n)).2 absent)⟩
  · rintro ⟨tag, payload, children, valid, equal, conditions⟩
    refine ⟨.up tag, .up payload, (fun n => .up (children n.down)), valid,
      congrArg ULift.up equal, ?_⟩
    rintro ⟨n⟩
    exact ⟨fun present => (conditions n).1 present,
      fun absent => congrArg ULift.up ((conditions n).2 absent)⟩

theorem family_fixed_point
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    holds presentation environment (FamilyValid presentation) tree ↔
      FamilyValid presentation tree :=
  (holds_iff presentation environment (fun _ tree => FamilyValid presentation tree) tree).trans
    (familyValid_iff_guardedStep presentation environment tree).symm

theorem holds_constructor
    (predicate : RecursiveSpace.Tree (RecursivePayload presentation environment) → Prop)
    (index : Index environment) (shape : presentation.polynomial.Shape environment index)
    (children : presentation.polynomial.Position shape →
      RecursiveSpace.Tree (RecursivePayload presentation environment))
    (valid : ∀ position, RecursiveValid presentation (children position)
      (presentation.polynomial.next shape position) ∧ predicate (children position)) :
    holds presentation environment predicate
      (RecursiveSpace.construct (presentation.tag shape) (some ⟨index, shape⟩)
        ((presentation.coding shape).extend RecursiveSpace.bottom children)) := by
  apply (signature.operator_meaning (model presentation environment) (full presentation environment)
    (fun value => .up (predicate value.down)) _).mpr
  refine ⟨.up (presentation.tag shape), .up (some ⟨index, shape⟩),
    (fun slot => .up ((presentation.coding shape).extend RecursiveSpace.bottom children slot.down)),
    rfl, rfl, ?_⟩
  rintro ⟨slot⟩
  constructor
  · rintro ⟨position, decoded⟩
    change edgeGuard presentation (some ⟨index, shape⟩) slot _ ∧ predicate _
    simp only [IndexedPolynomial.SlotEncoding.extend, decoded]
    exact ⟨⟨position, decoded, recursiveValid_hasRootIndex presentation _ _ (valid position).1⟩,
      (valid position).2⟩
  · intro inactive
    apply congrArg ULift.up
    apply (presentation.coding shape).extend_canonical
    cases decoded : (presentation.coding shape).decode slot with
    | none => rfl
    | some position => exact False.elim (inactive ⟨position, decoded⟩)

def member (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  (RecursiveSpacePredicate.Signature.denotes (model presentation environment)
    (PredicateFixedPoint.least signature.operator) (.up tree)).down

theorem member_iff_familyValid
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    member presentation environment tree ↔ FamilyValid presentation tree := by
  constructor
  · intro present
    exact present (fun value => .up (FamilyValid presentation value.down)) True.intro (by
      intro value _ generated
      exact (family_fixed_point presentation environment value.down).mp generated)
  · intro valid predicate _ closed
    apply familyValid_induction presentation environment
      (fun value => (predicate (.up value)).down) ?_ tree valid
    intro index shape children hypotheses
    exact closed (.up _) True.intro
      (holds_constructor presentation environment (fun value => (predicate (.up value)).down)
        index shape children hypotheses)

theorem indexed_member_iff
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (index : Index environment) :
    member presentation environment tree ∧ HasRootIndex presentation tree index ↔
      RecursiveValid presentation tree index := by
  rw [member_iff_familyValid, ← recursiveValid_iff_family_and_root]

#print axioms holds_iff
#print axioms family_fixed_point
#print axioms member_iff_familyValid
#print axioms indexed_member_iff

end Mettapedia.Logic.HOL.IndexedFamilyPredicate
