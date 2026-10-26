import Mettapedia.TypeTheory.RecursiveSpace
import Mettapedia.TypeTheory.IndexedPolynomialNaturalSlotRepresentation

/-!
# Indexed constructor families in recursive spaces

An indexed polynomial with natural-slot codes and a constructor-tag map embeds
in the countably branching bottom/constructor polynomial. Nodes retain their
constructor tag, original result index, complete shape and natural-slot child map.
First-order inventories instantiate this presentation through their source-order
finite position equivalences.
The image guard checks tags and payload presence before the existing recursive
index and canonical-padding guard. Both round trips and algebra coherence hold.

The comparison also transports to any recursive-space algebra satisfying full
predicate induction, separation and injectivity. This is a semantic theorem;
instantiating those laws from retained HOL certificates in a selected model and
qualifying executable encoders remain separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation
universe b i s p
variable {Base : Type b} {Index : Base → Type i}

-- The stored polynomial retains separate shape and position universes.
set_option linter.checkUnivs false in
structure Presentation where
  polynomial : IndexedPolynomial.{b, i, s, p} Base Index
  coding : ∀ {base index} (shape : polynomial.Shape base index), SlotEncoding (polynomial.Position shape) Nat
  tag : ∀ {base index}, polynomial.Shape base index → Nat

variable (presentation : Presentation.{b, i, s, p} (Base := Base) (Index := Index))

def positions : GuardedRaw.Positions presentation.polynomial where
  Slot := fun _ => Nat
  coding := presentation.coding

abbrev RecursivePayload (environment : Base) :=
  Option (Σ index, presentation.polynomial.Shape environment index)

noncomputable def toRecursiveSpace : ∀ {environment : Base},
    GuardedRaw.Tree presentation.polynomial (positions presentation) environment →
      RecursiveSpace.Tree (RecursivePayload presentation environment) :=
  fun {environment} source =>
    Fix.eliminate (GuardedRaw.polynomial presentation.polynomial (positions presentation))
      (fun environment _ _ => RecursiveSpace.Tree (RecursivePayload presentation environment))
      (fun _ _ shape _children encoded => match shape with
        | none => RecursiveSpace.bottom
        | some point => RecursiveSpace.construct (presentation.tag point.2) (some point) encoded)
      environment PUnit.unit source

@[simp] theorem toRecursiveSpace_absent (environment : Base) :
    toRecursiveSpace presentation (GuardedRaw.absent _ _ environment) = RecursiveSpace.bottom := rfl

@[simp] theorem toRecursiveSpace_node {environment : Base}
    (point : Σ index, presentation.polynomial.Shape environment index)
    (children : Nat → GuardedRaw.Tree presentation.polynomial (positions presentation) environment) :
    toRecursiveSpace presentation (Fix.roll (some point) children) =
      RecursiveSpace.construct (presentation.tag point.2) (some point) (fun n => toRecursiveSpace presentation (children n)) := rfl

noncomputable def RecursiveEncoded {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) : Prop :=
  Fix.eliminate (RecursiveSpace.polynomial (RecursivePayload presentation environment))
    (fun _ _ _ => Prop)
    (fun _ _ shape _children indexed => match shape with
      | none => True
      | some (tag, payload) => match payload with
        | none => False
        | some point => tag = presentation.tag point.2 ∧ ∀ n, indexed n)
    PUnit.unit PUnit.unit tree

@[simp] theorem recursiveEncoded_bottom (environment : Base) :
    RecursiveEncoded presentation (environment := environment) RecursiveSpace.bottom := True.intro

@[simp] theorem recursiveEncoded_construct {environment : Base}
    (tag : Nat) (payload : RecursivePayload presentation environment)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    RecursiveEncoded presentation (RecursiveSpace.construct tag payload children) ↔
      ∃ point, payload = some point ∧ tag = presentation.tag point.2 ∧ ∀ n, RecursiveEncoded presentation (children n) := by
  cases payload with
  | none =>
    change False ↔ _
    simp only [reduceCtorEq, false_and, exists_false]
  | some point =>
    change (tag = presentation.tag point.2 ∧ ∀ n, RecursiveEncoded presentation (children n)) ↔ _
    constructor
    · intro h; exact ⟨point, rfl, h⟩
    · rintro ⟨other, same, rest⟩
      cases Option.some.inj same
      exact rest

noncomputable def fromRecursiveSpace {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (encoded : RecursiveEncoded presentation tree) :
    GuardedRaw.Tree presentation.polynomial (positions presentation) environment := by
  have decoded : ∀ index (raw : Fix (RecursiveSpace.polynomial (RecursivePayload presentation environment)) PUnit.unit index),
      RecursiveEncoded presentation (RecursiveSpace.atUnit raw) →
      GuardedRaw.Tree presentation.polynomial (positions presentation) environment :=
    Fix.eliminate (RecursiveSpace.polynomial (RecursivePayload presentation environment))
      (fun _ _ raw => RecursiveEncoded presentation (RecursiveSpace.atUnit raw) →
        GuardedRaw.Tree presentation.polynomial (positions presentation) environment)
      (by
        intro base index shape children hypotheses valid
        cases base
        cases index
        cases shape with
        | none => exact GuardedRaw.absent _ _ environment
        | some point =>
          rcases point with ⟨tag, payload⟩
          cases payload with
          | none => exact False.elim valid
          | some original =>
            exact Fix.roll (some original) (fun n => hypotheses n (valid.2 n))) PUnit.unit
  exact decoded PUnit.unit tree encoded

theorem toRecursiveSpace_encoded {environment : Base}
    (tree : GuardedRaw.Tree presentation.polynomial (positions presentation) environment) :
    RecursiveEncoded presentation (toRecursiveSpace presentation tree) := by
  have all : ∀ rawIndex (raw : Fix (GuardedRaw.polynomial presentation.polynomial (positions presentation)) environment rawIndex),
      RecursiveEncoded presentation (toRecursiveSpace presentation (GuardedRaw.atUnit _ _ raw)) :=
    Fix.eliminate (GuardedRaw.polynomial presentation.polynomial (positions presentation))
      (fun _ _ raw => RecursiveEncoded presentation (toRecursiveSpace presentation (GuardedRaw.atUnit _ _ raw)))
      (by
        intro base index shape children hypotheses
        cases index
        cases shape with
        | none => trivial
        | some point => exact ⟨rfl, hypotheses⟩) environment
  exact all PUnit.unit tree

theorem fromRecursiveSpace_toRecursiveSpace {environment : Base}
    (tree : GuardedRaw.Tree presentation.polynomial (positions presentation) environment) :
    fromRecursiveSpace presentation (toRecursiveSpace presentation tree) (toRecursiveSpace_encoded presentation tree) = tree := by
  have all : ∀ rawIndex (raw : Fix (GuardedRaw.polynomial presentation.polynomial (positions presentation)) environment rawIndex),
      fromRecursiveSpace presentation (toRecursiveSpace presentation (GuardedRaw.atUnit _ _ raw))
        (toRecursiveSpace_encoded presentation (GuardedRaw.atUnit _ _ raw)) = GuardedRaw.atUnit _ _ raw :=
    Fix.eliminate (GuardedRaw.polynomial presentation.polynomial (positions presentation))
      (fun _ _ raw => fromRecursiveSpace presentation (toRecursiveSpace presentation (GuardedRaw.atUnit _ _ raw))
        (toRecursiveSpace_encoded presentation (GuardedRaw.atUnit _ _ raw)) = GuardedRaw.atUnit _ _ raw)
      (by
        intro base index shape children hypotheses
        cases index
        cases shape with
        | none =>
          change GuardedRaw.absent _ _ base = Fix.roll none children
          unfold GuardedRaw.absent
          apply congrArg (Fix.roll (polynomial := GuardedRaw.polynomial presentation.polynomial (positions presentation)) (base := base) (index := PUnit.unit) none)
          funext impossible
          exact PEmpty.elim impossible
        | some point =>
          change Fix.roll (polynomial := GuardedRaw.polynomial presentation.polynomial (positions presentation)) (base := base) (index := PUnit.unit) (some point) _ =
            Fix.roll (polynomial := GuardedRaw.polynomial presentation.polynomial (positions presentation)) (base := base) (index := PUnit.unit) (some point) children
          apply congrArg (Fix.roll (polynomial := GuardedRaw.polynomial presentation.polynomial (positions presentation)) (base := base) (index := PUnit.unit) (some point))
          exact funext hypotheses) environment
  exact all PUnit.unit tree

theorem toRecursiveSpace_fromRecursiveSpace {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment))
    (encoded : RecursiveEncoded presentation tree) :
    toRecursiveSpace presentation (fromRecursiveSpace presentation tree encoded) = tree := by
  apply RecursiveSpace.induction
    (fun tree => ∀ encoded : RecursiveEncoded presentation tree,
      toRecursiveSpace presentation (fromRecursiveSpace presentation tree encoded) = tree) ?_ ?_ tree encoded
  · intro valid
    rfl
  · intro tag payload children hypotheses valid
    cases payload with
    | none => exact False.elim valid
    | some point =>
      change tag = presentation.tag point.2 ∧ (∀ n, RecursiveEncoded presentation (children n)) at valid
      have tags := valid.1
      cases tags
      change RecursiveSpace.construct (presentation.tag point.2) (some point) _ = RecursiveSpace.construct (presentation.tag point.2) (some point) children
      apply congrArg (RecursiveSpace.construct (presentation.tag point.2) (some point))
      exact funext fun n => hypotheses n (valid.2 n)

noncomputable def recursiveSpaceEquivalence (environment : Base) :
    GuardedRaw.Tree presentation.polynomial (positions presentation) environment ≃
      {tree : RecursiveSpace.Tree (RecursivePayload presentation environment) // RecursiveEncoded presentation tree} where
  toFun := fun tree => ⟨toRecursiveSpace presentation tree, toRecursiveSpace_encoded presentation tree⟩
  invFun := fun tree => fromRecursiveSpace presentation tree.val tree.property
  left_inv := fromRecursiveSpace_toRecursiveSpace presentation
  right_inv := fun tree => Subtype.ext (toRecursiveSpace_fromRecursiveSpace presentation tree.val tree.property)

def RecursiveValid {environment : Base}
    (tree : RecursiveSpace.Tree (RecursivePayload presentation environment)) (index : Index environment) : Prop :=
  ∃ encoded : RecursiveEncoded presentation tree,
    GuardedRaw.Valid presentation.polynomial (positions presentation)
      (fromRecursiveSpace presentation tree encoded) index

noncomputable def recursiveGuardedEquivalence (environment : Base) (index : Index environment) :
    GuardedRaw.Family presentation.polynomial (positions presentation) environment index ≃
      {tree : RecursiveSpace.Tree (RecursivePayload presentation environment) // RecursiveValid presentation tree index} where
  toFun := fun raw => ⟨toRecursiveSpace presentation raw.val,
    ⟨toRecursiveSpace_encoded presentation raw.val, by
      rw [fromRecursiveSpace_toRecursiveSpace]
      exact raw.property⟩⟩
  invFun := fun target => ⟨fromRecursiveSpace presentation target.val target.property.choose,
    target.property.choose_spec⟩
  left_inv := fun raw => Subtype.ext (fromRecursiveSpace_toRecursiveSpace presentation raw.val)
  right_inv := fun target => Subtype.ext (toRecursiveSpace_fromRecursiveSpace presentation target.val target.property.choose)

noncomputable def recursiveSpaceRepresentation (environment : Base) (index : Index environment) :
    Fix presentation.polynomial environment index ≃
      {tree : RecursiveSpace.Tree (RecursivePayload presentation environment) // RecursiveValid presentation tree index} :=
  (GuardedRaw.representation presentation.polynomial (positions presentation) environment index).trans
    (recursiveGuardedEquivalence presentation environment index)

abbrev RecursiveFamily (environment : Base) (index : Index environment) :=
  {tree : RecursiveSpace.Tree (RecursivePayload presentation environment) // RecursiveValid presentation tree index}

noncomputable def recursiveAlgebra : Algebra presentation.polynomial (RecursiveFamily presentation) where
  act environment index layer :=
    recursiveGuardedEquivalence presentation environment index
      ((GuardedRaw.algebra presentation.polynomial (positions presentation)).act environment index
        ⟨layer.1, fun position => (recursiveGuardedEquivalence presentation environment _).symm (layer.2 position)⟩)

noncomputable def recursiveAlgebraIso :
    Algebra.Iso (GuardedRaw.algebra presentation.polynomial (positions presentation)) (recursiveAlgebra presentation) where
  toEquiv := recursiveGuardedEquivalence presentation
  commutes := by
    intro environment index layer
    apply congrArg (recursiveGuardedEquivalence presentation environment index)
    apply congrArg ((GuardedRaw.algebra presentation.polynomial (positions presentation)).act environment index)
    cases layer with
    | mk shape children =>
      apply congrArg (Sigma.mk shape)
      funext position
      exact ((recursiveGuardedEquivalence presentation environment _).symm_apply_apply (children position)).symm

noncomputable def recursiveAlgebraRepresentation : Algebra.Representation presentation.polynomial (recursiveAlgebra presentation) :=
  (GuardedRaw.algebraRepresentation presentation.polynomial (positions presentation)).trans
    (recursiveAlgebraIso presentation)

theorem recursiveValid_toRecursiveSpace_iff {environment : Base}
    (raw : GuardedRaw.Tree presentation.polynomial (positions presentation) environment) (index : Index environment) :
    RecursiveValid presentation (toRecursiveSpace presentation raw) index ↔
      GuardedRaw.Valid presentation.polynomial (positions presentation) raw index := by
  constructor
  · rintro ⟨encoded, valid⟩
    rw [fromRecursiveSpace_toRecursiveSpace] at valid
    exact valid
  · intro valid
    exact ⟨toRecursiveSpace_encoded presentation raw, by rw [fromRecursiveSpace_toRecursiveSpace]; exact valid⟩

theorem recursiveEncoded_missing_payload_refused (environment : Base) (tag : Nat)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    ¬ RecursiveEncoded presentation (RecursiveSpace.construct tag none children) := by
  exact id

theorem recursiveEncoded_wrong_tag_refused {environment : Base}
    (point : Σ index, presentation.polynomial.Shape environment index)
    (tag : Nat) (different : tag ≠ presentation.tag point.2)
    (children : Nat → RecursiveSpace.Tree (RecursivePayload presentation environment)) :
    ¬ RecursiveEncoded presentation (RecursiveSpace.construct tag (some point) children) := by
  intro encoded
  exact different encoded.1

universe v
variable {R : Type v}

noncomputable def interpretedGuardedEquivalence (environment : Base)
    (M : RecursiveSpace.Model (RecursivePayload presentation environment) R) (index : Index environment) :
    RecursiveFamily presentation environment index ≃
      {value : R // RecursiveValid presentation ((RecursiveSpace.equivalence M).symm value) index} where
  toFun := fun tree => ⟨RecursiveSpace.equivalence M tree.val, by
    rw [Equiv.symm_apply_apply]
    exact tree.property⟩
  invFun := fun value => ⟨(RecursiveSpace.equivalence M).symm value.val, value.property⟩
  left_inv := fun tree => Subtype.ext ((RecursiveSpace.equivalence M).symm_apply_apply tree.val)
  right_inv := fun value => Subtype.ext ((RecursiveSpace.equivalence M).apply_symm_apply value.val)

noncomputable def interpretedRepresentation (environment : Base)
    (M : RecursiveSpace.Model (RecursivePayload presentation environment) R) (index : Index environment) :
    Fix presentation.polynomial environment index ≃
      {value : R // RecursiveValid presentation ((RecursiveSpace.equivalence M).symm value) index} :=
  (recursiveSpaceRepresentation presentation environment index).trans
    (interpretedGuardedEquivalence presentation environment M index)

noncomputable def interpretedEncode {environment : Base}
    (M : RecursiveSpace.Model (RecursivePayload presentation environment) R) {index : Index environment}
    (source : Fix presentation.polynomial environment index) : R :=
  RecursiveSpace.fold M (toRecursiveSpace presentation
    (GuardedRaw.encode presentation.polynomial (positions presentation) source))

theorem interpretedEncode_constructor {environment : Base}
    (M : RecursiveSpace.Model (RecursivePayload presentation environment) R) {index : Index environment}
    (shape : presentation.polynomial.Shape environment index)
    (children : ∀ position, Fix presentation.polynomial environment (presentation.polynomial.next shape position)) :
    interpretedEncode presentation M (Fix.roll shape children) =
      M.construct (presentation.tag shape) (some ⟨index, shape⟩)
        (((positions presentation).coding shape).extend M.bottom (fun position => interpretedEncode presentation M (children position))) := by
  unfold interpretedEncode
  rw [GuardedRaw.encode_roll]
  change M.construct (presentation.tag shape) (some ⟨index, shape⟩)
    (fun slot => RecursiveSpace.fold M (toRecursiveSpace presentation
      (((positions presentation).coding shape).extend
        (GuardedRaw.absent presentation.polynomial (positions presentation) environment)
        (fun position => GuardedRaw.encode presentation.polynomial (positions presentation) (children position)) slot))) = _
  apply congrArg (M.construct (presentation.tag shape) (some ⟨index, shape⟩))
  funext slot
  cases decoded : ((positions presentation).coding shape).decode slot with
  | none =>
    simp only [SlotEncoding.extend, decoded, toRecursiveSpace_absent, RecursiveSpace.fold_bottom]
  | some position => simp only [SlotEncoding.extend, decoded]

#print axioms recursiveSpaceEquivalence
#print axioms recursiveGuardedEquivalence
#print axioms recursiveAlgebraRepresentation
#print axioms interpretedRepresentation
#print axioms interpretedEncode_constructor
end Mettapedia.TypeTheory.IndexedPolynomial.RecursiveSpaceRepresentation

namespace Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u
variable {I : Interface.{u}} {context : List I.SortCode}

def recursiveSpacePresentation (constructors : List (NamedConstructor I context)) :
    RecursiveSpaceRepresentation.Presentation (Base := Env I.Value context) (Index := fun _ => I.Index) where
  polynomial := inventoryPolynomial constructors
  coding := fun shape => (naturalSlots constructors).coding shape
  tag := fun shape => shape.1.val

end Mettapedia.TypeTheory.IndexedPolynomial.Description
