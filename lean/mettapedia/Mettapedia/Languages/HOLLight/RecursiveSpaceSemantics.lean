import Mettapedia.TypeTheory.RecursiveSpace
import Mettapedia.Logic.HOL.Semantics.IndexedPolynomialPredicate
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# Relational semantics of the HOL Light recursive-space construction

The numerical pairing and relational injections follow `ind_types.ml`.
The inverse functions realize its injective-pairing specifications. The bottom
filler remains a parameter, matching the unspecified value of the source
Hilbert-choice term. Its least generated relation family supplies an inhabited
subtype with abstraction/representation laws, constructor separation and
injectivity, full predicate induction and constructor recursion.

The construction instantiates the polynomial recursive-space comparison. Its
least membership predicate also agrees with the existing HOL fixed-point
syntax in a full-function-space model. Reading a retained native declaration
and proof history into that model remains a separate correspondence obligation.
No executable decoder or native implementation refinement follows here.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics
universe u

def numberPair (x y : Nat) : Nat := 2 ^ x * (2 * y + 1)

theorem numberPair_injective : Function.Injective (fun point : Nat × Nat => numberPair point.1 point.2) := by
  intro first
  rcases first with ⟨x, y⟩
  induction x generalizing y with
  | zero =>
    rintro ⟨other, z⟩ same
    cases other with
    | zero =>
      simp only [numberPair, Nat.pow_zero, Nat.one_mul] at same
      have yz : y = z := by omega
      cases yz
      rfl
    | succ other =>
      have residue := congrArg (fun value => value % 2) same
      simp [numberPair, Nat.pow_succ, Nat.mul_mod, Nat.add_mod] at residue
  | succ x hypotheses =>
    rintro ⟨other, z⟩ same
    cases other with
    | zero =>
      have residue := congrArg (fun value => value % 2) same
      simp [numberPair, Nat.pow_succ, Nat.mul_mod, Nat.add_mod] at residue
    | succ other =>
      have factors : 2 * numberPair x y = 2 * numberPair other z := by
        simpa only [numberPair, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using same
      have smaller : numberPair x y = numberPair other z := Nat.eq_of_mul_eq_mul_left (by decide) factors
      have points : (x, y) = (other, z) := hypotheses y smaller
      cases points
      rfl

def numberSum (tag : Bool) (value : Nat) : Nat := if tag then 2 * value + 1 else 2 * value

theorem numberSum_injective : Function.Injective (fun point : Bool × Nat => numberSum point.1 point.2) := by
  rintro ⟨first, x⟩ ⟨second, y⟩ same
  change numberSum first x = numberSum second y at same
  cases first <;> cases second <;> simp_all [numberSum]
  all_goals omega

noncomputable def numberUnpair : Nat → Nat × Nat :=
  Function.invFun (fun point : Nat × Nat => numberPair point.1 point.2)

noncomputable def numberUnsum : Nat → Bool × Nat :=
  Function.invFun (fun point : Bool × Nat => numberSum point.1 point.2)

@[simp] theorem numberUnpair_pair (x y : Nat) : numberUnpair (numberPair x y) = (x, y) :=
  Function.leftInverse_invFun numberPair_injective (x, y)

@[simp] theorem numberUnsum_sum (tag : Bool) (value : Nat) : numberUnsum (numberSum tag value) = (tag, value) :=
  Function.leftInverse_invFun numberSum_injective (tag, value)

abbrev Relation (A : Type u) := Nat → A → Prop

def injectNumber {A : Type u} (number : Nat) : Relation A := fun n _ => n = number

def injectPayload {A : Type u} (payload : A) : Relation A := fun _ other => other = payload

noncomputable def injectChildren {A : Type u} (children : Nat → Relation A) : Relation A :=
  fun n => children (numberUnpair n).1 (numberUnpair n).2

noncomputable def injectPair {A : Type u} (first second : Relation A) : Relation A :=
  fun n a => if (numberUnsum n).1 then first (numberUnsum n).2 a else second (numberUnsum n).2 a

@[simp] theorem injectPair_left {A : Type u} (first second : Relation A) (n : Nat) (a : A) :
    injectPair first second (numberSum true n) a = first n a := by
  simp only [injectPair, numberUnsum_sum, if_true]

@[simp] theorem injectPair_right {A : Type u} (first second : Relation A) (n : Nat) (a : A) :
    injectPair first second (numberSum false n) a = second n a := by
  simp only [injectPair, numberUnsum_sum, Bool.false_eq_true, if_false]

theorem injectPair_injective {A : Type u} (first second first' second' : Relation A) :
    injectPair first second = injectPair first' second' ↔ first = first' ∧ second = second' := by
  constructor
  · intro same
    constructor
    · funext n a
      simpa only [injectPair_left] using congrFun (congrFun same (numberSum true n)) a
    · funext n a
      simpa only [injectPair_right] using congrFun (congrFun same (numberSum false n)) a
  · rintro ⟨rfl, rfl⟩
    rfl

theorem injectChildren_injective {A : Type u} : Function.Injective (@injectChildren A) := by
  intro first second same
  funext n m a
  simpa only [injectChildren, numberUnpair_pair] using congrFun (congrFun same (numberPair n m)) a

theorem injectNumber_injective {A : Type u} [Nonempty A] : Function.Injective (@injectNumber A) := by
  intro first second same
  let a : A := Classical.choice inferInstance
  have present := congrFun (congrFun same first) a
  change (first = first) = (first = second) at present
  exact present ▸ rfl

theorem injectPayload_injective {A : Type u} : Function.Injective (@injectPayload A) := by
  intro first second same
  have present := congrFun (congrFun same 0) first
  change (first = first) = (first = second) at present
  exact present ▸ rfl

noncomputable def rawBottom {A : Type u} (filler : Relation A) : Relation A := injectPair (injectNumber 0) filler

noncomputable def rawConstruct {A : Type u} (tag : Nat) (payload : A) (children : Nat → Relation A) : Relation A :=
  injectPair (injectNumber (tag + 1)) (injectPair (injectPayload payload) (injectChildren children))

theorem rawConstruct_ne_bottom {A : Type u} [Nonempty A] (filler : Relation A) (tag : Nat) (payload : A) (children : Nat → Relation A) :
    rawConstruct tag payload children ≠ rawBottom filler := by
  intro same
  have numbers := (injectPair_injective _ _ _ _).mp same |>.1
  have impossible := injectNumber_injective numbers
  omega

theorem rawConstruct_injective {A : Type u} [Nonempty A]
    (tag : Nat) (payload : A) (children : Nat → Relation A)
    (tag' : Nat) (payload' : A) (children' : Nat → Relation A) :
    rawConstruct tag payload children = rawConstruct tag' payload' children' ↔
      tag = tag' ∧ payload = payload' ∧ children = children' := by
  constructor
  · intro same
    obtain ⟨numbers, pairs⟩ := (injectPair_injective _ _ _ _).mp same
    obtain ⟨data, recursive⟩ := (injectPair_injective _ _ _ _).mp pairs
    exact ⟨Nat.add_right_cancel (injectNumber_injective numbers),
      injectPayload_injective data, injectChildren_injective recursive⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The least relation family generated by the literal bottom and constructor
operations. The filler is the value chosen by the source Hilbert-choice term. -/
inductive RawMember {A : Type u} (filler : Relation A) : Relation A → Prop where
  | bottom : RawMember filler (rawBottom filler)
  | construct (tag : Nat) (payload : A) (children : Nat → Relation A)
      (members : ∀ n, RawMember filler (children n)) :
      RawMember filler (rawConstruct tag payload children)

abbrev Carrier {A : Type u} (filler : Relation A) := {relation : Relation A // RawMember filler relation}

def bottom {A : Type u} (filler : Relation A) : Carrier filler := ⟨rawBottom filler, .bottom⟩

noncomputable def construct {A : Type u} (filler : Relation A)
    (tag : Nat) (payload : A) (children : Nat → Carrier filler) : Carrier filler :=
  ⟨rawConstruct tag payload (fun n => (children n).val),
    .construct tag payload _ (fun n => (children n).property)⟩

noncomputable def abstract {A : Type u} (filler : Relation A) (relation : Relation A) : Carrier filler := by
  classical
  exact if member : RawMember filler relation then ⟨relation, member⟩ else bottom filler

@[simp] theorem abstract_represent {A : Type u} (filler : Relation A) (value : Carrier filler) :
    abstract filler value.val = value := by
  simp only [abstract, dif_pos value.property]

@[simp] theorem represent_abstract {A : Type u} (filler : Relation A) (relation : Relation A) :
    (abstract filler relation).val = relation ↔ RawMember filler relation := by
  classical
  unfold abstract
  split
  · rename_i member
    exact ⟨fun _ => member, fun _ => rfl⟩
  · rename_i absent
    constructor
    · intro same
      exact False.elim (absent (same ▸ RawMember.bottom))
    · exact fun member => False.elim (absent member)

theorem construct_ne_bottom {A : Type u} [Nonempty A] (filler : Relation A)
    (tag : Nat) (payload : A) (children : Nat → Carrier filler) :
    construct filler tag payload children ≠ bottom filler := by
  intro same
  exact rawConstruct_ne_bottom filler tag payload _ (congrArg Subtype.val same)

theorem construct_injective {A : Type u} [Nonempty A] (filler : Relation A)
    (tag : Nat) (payload : A) (children : Nat → Carrier filler)
    (tag' : Nat) (payload' : A) (children' : Nat → Carrier filler) :
    construct filler tag payload children = construct filler tag' payload' children' ↔
      tag = tag' ∧ payload = payload' ∧ children = children' := by
  constructor
  · intro same
    obtain ⟨tags, payloads, recursive⟩ := (rawConstruct_injective _ _ _ _ _ _).mp (congrArg Subtype.val same)
    exact ⟨tags, payloads, funext fun n => Subtype.ext (congrFun recursive n)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem induction {A : Type u} (filler : Relation A) (property : Carrier filler → Prop)
    (at_bottom : property (bottom filler))
    (at_construct : ∀ tag payload children,
      (∀ n, property (children n)) → property (construct filler tag payload children))
    (value : Carrier filler) : property value := by
  rcases value with ⟨relation, member⟩
  induction member with
  | bottom => exact at_bottom
  | construct tag payload children members hypotheses =>
    exact at_construct tag payload (fun n => ⟨children n, members n⟩) hypotheses

noncomputable def model {A : Type u} [Nonempty A] (filler : Relation A) :
    Mettapedia.TypeTheory.RecursiveSpace.Model A (Carrier filler) where
  bottom := bottom filler
  construct := construct filler
  construct_ne_bottom := construct_ne_bottom filler
  construct_injective := construct_injective filler
  induction := fun property at_bottom at_construct value => induction filler property at_bottom at_construct value

noncomputable def representation {A : Type u} [Nonempty A] (filler : Relation A) :
    Mettapedia.TypeTheory.RecursiveSpace.Tree A ≃ Carrier filler :=
  Mettapedia.TypeTheory.RecursiveSpace.equivalence (model filler)

universe v

theorem constructor_recursion {A : Type u} [Nonempty A] (filler : Relation A)
    {B : Type v} [Nonempty B]
    (method : Nat → A → (Nat → Carrier filler) → (Nat → B) → B) :
    ∃ computation : Carrier filler → B, ∀ tag payload children,
      computation (construct filler tag payload children) =
        method tag payload children (fun n => computation (children n)) := by
  exact ⟨Mettapedia.TypeTheory.RecursiveSpace.recurse (model filler) (Classical.choice inferInstance) method,
    Mettapedia.TypeTheory.RecursiveSpace.recurse_construct (model filler) _ method⟩

theorem rawMember_iff_closed {A : Type u} (filler : Relation A) (relation : Relation A) :
    RawMember filler relation ↔ ∀ property : Relation A → Prop,
      property (rawBottom filler) →
      (∀ tag payload children, (∀ n, property (children n)) → property (rawConstruct tag payload children)) →
      property relation := by
  constructor
  · intro present property at_bottom at_construct
    induction present with
    | bottom => exact at_bottom
    | construct tag payload children members hypotheses => exact at_construct tag payload children hypotheses
  · intro present
    exact present (RawMember filler) .bottom (fun tag payload children members => .construct tag payload children members)

def step {A : Type u} (filler : Relation A) (property : Relation A → Prop) (relation : Relation A) : Prop :=
  relation = rawBottom filler ∨ ∃ tag payload children,
    relation = rawConstruct tag payload children ∧ ∀ n, property (children n)

theorem step_monotone {A : Type u} (filler : Relation A) (first second : Relation A → Prop)
    (inclusion : ∀ relation, first relation → second relation) (relation : Relation A) :
    step filler first relation → step filler second relation := by
  rintro (bottom | ⟨tag, payload, children, same, members⟩)
  · exact .inl bottom
  · exact .inr ⟨tag, payload, children, same, fun n => inclusion _ (members n)⟩

open Mettapedia.Logic.HOL
open PolynomialPredicate

def predicateModel {A : Type u} (filler : Relation A) : HenkinModel.{0, 0, u} Unit OperatorSignature.Const :=
  .standard (fun _ => ULift.{1} (Relation A)) (fun symbol => match symbol with
    | .operator => fun property relation => .up (step filler (fun child => (property (.up child)).down) relation.down))

def predicateEmptyValuation {A : Type u} (filler : Relation A) : (predicateModel filler).Valuation [] :=
  fun impossible => nomatch impossible

def predicateMember {A : Type u} (filler : Relation A) (relation : Relation A) : Prop :=
  ((predicateModel filler).denote (PredicateFixedPoint.least (.const .operator))
    (predicateEmptyValuation filler) (.up relation)).down

theorem predicateMember_iff_closed {A : Type u} (filler : Relation A) (relation : Relation A) :
    predicateMember filler relation ↔ ∀ property : Relation A → Prop,
      (∀ candidate, step filler property candidate → property candidate) → property relation := by
  constructor
  · intro member property closed
    have result := member (fun candidate => .up (property candidate.down)) trivial (by
      intro candidate _ generated
      change step filler property candidate.down at generated
      change property candidate.down
      exact closed candidate.down generated)
    exact result
  · intro present property _ closed
    change (property (.up relation)).down
    apply present (fun raw => (property (.up raw)).down)
    intro candidate generated
    exact closed (.up candidate) trivial generated

theorem predicateMember_iff_rawMember {A : Type u} (filler : Relation A) (relation : Relation A) :
    predicateMember filler relation ↔ RawMember filler relation := by
  rw [predicateMember_iff_closed]
  constructor
  · intro present
    apply present (RawMember filler)
    intro candidate generated
    rcases generated with bottom | ⟨tag, payload, children, same, members⟩
    · rw [bottom]
      exact RawMember.bottom
    · rw [same]
      exact RawMember.construct tag payload children members
  · intro member property closed
    induction member with
    | bottom => exact closed _ (.inl rfl)
    | construct tag payload children members hypotheses =>
      exact closed _ (.inr ⟨tag, payload, children, rfl, hypotheses⟩)

namespace Controls

def filler : Relation Bool := fun _ _ => False

noncomputable def sample : Carrier filler := construct filler 3 true (fun _ => bottom filler)

noncomputable def sampleRepresentation := representation filler

theorem sample_roundtrip : sampleRepresentation (sampleRepresentation.symm sample) = sample :=
  sampleRepresentation.apply_symm_apply sample

theorem sample_member : predicateMember filler sample.val :=
  (predicateMember_iff_rawMember filler sample.val).mpr sample.property

theorem sample_abstract_represent : abstract filler sample.val = sample := abstract_represent filler sample

theorem sample_not_bottom : sample ≠ bottom filler := construct_ne_bottom filler 3 true _

theorem changed_payload_refused :
    construct filler 3 true (fun _ => bottom filler) ≠ construct filler 3 false (fun _ => bottom filler) := by
  intro same
  have impossible := ((construct_injective filler _ _ _ _ _ _).mp same).2.1
  cases impossible

end Controls
#print axioms numberPair_injective
#print axioms rawConstruct_injective
#print axioms represent_abstract
#print axioms induction
#print axioms model
#print axioms representation
#print axioms constructor_recursion
#print axioms rawMember_iff_closed
#print axioms predicateMember_iff_rawMember
end Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics
