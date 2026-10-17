import Mettapedia.Logic.HostingStyles.JudgmentsAsTypes
import Mettapedia.Logic.HostingStyles.Universality
import Mettapedia.Logic.HostingStyles.ProofNodes
import Mettapedia.Logic.HostingStyles.TermsAloneHosting
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Tactic.DeriveCountable

/-!
# Proof systems whose derivations are numbered, and what hosts them on terms

A calculus hosts a proof system only where the images of derivations have no
step.  On terms alone that is all it needs: a family of inert data
(`ContextTheory.InertData`) indexed by the natural numbers hosts

* the derivations of each judgment of a finitary proof system whose rule
  instances are numbered (`RuleSignature.Numbering`), kept apart
  (`hostsEvery_numberedDerivations_of_inertData`); the number of a derivation is
  `Finitary.proofCode`, and different derivations of a judgment have
  different numbers (`Finitary.proofCode_injective`);
* the terms of the type of each judgment in the framework with the rules of
  such a system as constants, up to its conversion
  (`hostsEvery_numberedFrameworkJudgments_of_inertData`): a term is sent to the
  number of the derivation it stands for, and two terms have one number
  exactly when they are convertible (`frameworkCode_eq_iff`).

The second statement is the framework side of the comparison, on terms alone
and at the types of judgments.  At the other types no derivation is read
back, and the terms are numbered through their syntax: over a countable
signature the closed terms of each type are countably many (`Tm.countable`,
by forgetting the typing of a term, `Tm.erase`), so their conversion classes
are numbered (`exists_conversionCode`), and inert data indexed by the natural
numbers host the terms of every type of the framework over every countable
signature (`hostsEvery_countableFrameworkTerms_of_inertData`).

With all contexts none of the three holds for a host whose contexts have a
linear size or that has no context of two holes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Framework

namespace RuleSignature

variable {J : Type} {P : RuleSignature J}

/-- **A numbering of the rule instances** of a signature: a number for each
rule instance, different for different instances with one conclusion. -/
structure Numbering (P : RuleSignature J) where
  /-- The number of a rule instance. -/
  code : {j : J} → P.Shape PUnit.unit j → Nat
  injective : ∀ {j : J} {first second : P.Shape PUnit.unit j},
    code first = code second → first = second

/-- **The number of a derivation**: the pair of the number of its last rule
instance and the code of the list of the numbers of its immediate
subderivations. -/
noncomputable def Finitary.proofCode (finitary : P.Finitary) (numbering : P.Numbering) {j : J}
    (proof : P.Proof j) : Nat :=
  Fix.fold P (carrier := fun _ _ => Nat)
    (fun _ _ layer =>
      Nat.pair (numbering.code layer.1)
        (Encodable.encode ((finitary.positions layer.1).map layer.2)))
    PUnit.unit j proof

@[simp] theorem Finitary.proofCode_node (finitary : P.Finitary) (numbering : P.Numbering) {j : J}
    (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    finitary.proofCode numbering (P.node shape children) =
      Nat.pair (numbering.code shape)
        (Encodable.encode ((finitary.positions shape).map fun position =>
          finitary.proofCode numbering (children position))) :=
  rfl

/-- **Different derivations of one judgment have different numbers.** -/
theorem Finitary.proofCode_injective (finitary : P.Finitary) (numbering : P.Numbering) {j : J}
    (first : P.Proof j) :
    ∀ second : P.Proof j,
      finitary.proofCode numbering first = finitary.proofCode numbering second → first = second := by
  induction first using Proof.induction with
  | node shape children ih =>
      intro second same
      obtain ⟨otherShape, otherChildren, rfl⟩ := RuleSignature.Proof.exists_node _ second
      have unfolded : Nat.pair (numbering.code shape)
          (Encodable.encode ((finitary.positions shape).map fun position =>
            finitary.proofCode numbering (children position))) =
          Nat.pair (numbering.code otherShape)
            (Encodable.encode ((finitary.positions otherShape).map fun position =>
              finitary.proofCode numbering (otherChildren position))) := same
      obtain ⟨shapeSame, listSame⟩ := Nat.pair_eq_pair.mp unfolded
      obtain rfl := numbering.injective shapeSame
      have pointwise := List.map_inj_left.mp (Encodable.encode_injective listSame)
      have childrenSame : children = otherChildren := funext fun position =>
        ih position _ (pointwise position (finitary.complete shape position))
      rw [childrenSame]

end RuleSignature

open RuleSignature

/-! ## The two classes of sources -/

/-- **The finitary proof systems whose rule instances are numbered**, each
with its derivations kept apart. -/
def NumberedProofSystem (source : ContextTheory.{0}) : Prop :=
  ∃ (J : Type) (P : RuleSignature J) (_ : P.Finitary) (_ : P.Numbering),
    source = P.proofTheory (ProofCongruence.identity P)

/-- The derivations of one judgment of such a system, as a theory given by
its terms alone. -/
def NumberedDerivations (source : ContextTheory.{0}) : Prop :=
  ∃ (J : Type) (P : RuleSignature J) (_ : P.Finitary) (_ : P.Numbering) (j : J),
    source = ((P.proofTheory (ProofCongruence.identity P)).gslt j).termsAlone

/-- The terms of the type of one judgment in the framework with the rules of
such a system as constants, up to its conversion, as a theory given by its
terms alone. -/
def NumberedFrameworkJudgments (source : ContextTheory.{0}) : Prop :=
  ∃ (J : Type) (P : RuleSignature J) (finitary : P.Finitary) (_ : P.Numbering) (j : J),
    source = ((frameworkTheory finitary.signature).gslt (.base j)).termsAlone

/-! ## The number of a term of the framework -/

section Framework

variable {J : Type} {P : RuleSignature J} (finitary : P.Finitary) (numbering : P.Numbering)

/-- The number of a closed term of the type of a judgment: the number of the
derivation it stands for. -/
noncomputable def frameworkCode {j : J} (term : Closed finitary.signature (.base j)) : Nat :=
  finitary.proofCode numbering (finitary.readback term)

/-- **Two terms of the type of a judgment have one number exactly when they
are convertible.** -/
theorem frameworkCode_eq_iff {j : J} (first second : Closed finitary.signature (.base j)) :
    frameworkCode finitary numbering first = frameworkCode finitary numbering second ↔
      Conv first second := by
  constructor
  · intro same
    have derivations : finitary.readback first = finitary.readback second :=
      finitary.proofCode_injective numbering _ _ same
    have left := finitary.conv_encodeTerm_readback first
    have right := finitary.conv_encodeTerm_readback second
    rw [derivations] at left
    exact .trans _ _ _ left (.symm _ _ right)
  · intro convertible
    exact congrArg (finitary.proofCode numbering)
      (finitary.proofReading.readback_conv convertible)

end Framework

/-! ## Inert data indexed by the numbers host both -/

section Hosts

variable {theory : ContextTheory.{0}}

/-- **Inert data indexed by the natural numbers host the derivations of every
judgment of every numbered finitary proof system**, kept apart. -/
theorem hostsEvery_numberedDerivations_of_inertData (data : theory.InertData Nat) :
    HostsEvery theory NumberedDerivations := by
  rintro source ⟨J, P, finitary, numbering, j, rfl⟩
  exact ⟨data.codeMap (source := (P.proofTheory (ProofCongruence.identity P)).gslt j)
      (finitary.proofCode numbering) (fun same => congrArg _ same),
    data.codeMap_hosting (source := (P.proofTheory (ProofCongruence.identity P)).gslt j)
      (finitary.proofCode numbering) (fun same => congrArg _ same)
      (fun first second same => finitary.proofCode_injective numbering first second same)
      (fun _ _ step => step)⟩

/-- **Inert data indexed by the natural numbers host the terms of the type of
every judgment in the framework over such a system**, up to its
conversion. -/
theorem hostsEvery_numberedFrameworkJudgments_of_inertData (data : theory.InertData Nat) :
    HostsEvery theory NumberedFrameworkJudgments := by
  rintro source ⟨J, P, finitary, numbering, j, rfl⟩
  exact ⟨data.codeMap (source := (frameworkTheory finitary.signature).gslt (.base j))
      (frameworkCode finitary numbering)
      (fun convertible => (frameworkCode_eq_iff finitary numbering _ _).mpr convertible),
    data.codeMap_hosting (source := (frameworkTheory finitary.signature).gslt (.base j))
      (frameworkCode finitary numbering)
      (fun convertible => (frameworkCode_eq_iff finitary numbering _ _).mpr convertible)
      (fun first second same => (frameworkCode_eq_iff finitary numbering first second).mp same)
      (fun _ _ step => step)⟩

end Hosts

/-! ## The framework over a countable signature, at every type -/

deriving instance Countable for Framework.Ty

namespace Framework

variable {B : Type} {signature : Signature B} {Hole : Type} {holes : Hole → Ty B}

/-- The position of a variable in its context. -/
def Var.index : {context : List (Ty B)} → {type : Ty B} → Var context type → Nat
  | _, _, .zero => 0
  | _, _, .succ name => name.index + 1

/-- Two variables of one type at one position are one variable. -/
theorem Var.index_injective :
    ∀ {context : List (Ty B)} {type : Ty B} (first second : Var context type),
      first.index = second.index → first = second
  | _, _, .zero, .zero, _ => rfl
  | _, _, .zero, .succ _, same => by simp [Var.index] at same
  | _, _, .succ _, .zero, same => by simp [Var.index] at same
  | _, _, .succ first, .succ second, same => by
      rw [Var.index_injective first second (by simpa [Var.index] using same)]

/-- **The terms of the framework without their typing**: what is left of a
term when its types are forgotten, except the type of the argument at each
application. -/
inductive RawTm (Const Hole B : Type) : Type where
  | var : Nat → RawTm Const Hole B
  | con : Const → RawTm Const Hole B
  | hole : Hole → RawTm Const Hole B
  | lam : RawTm Const Hole B → RawTm Const Hole B
  | app : Ty B → RawTm Const Hole B → RawTm Const Hole B → RawTm Const Hole B
  deriving Countable

/-- A term without its typing. -/
def Tm.erase : {context : List (Ty B)} → {type : Ty B} → Tm signature holes context type →
    RawTm signature.Const Hole B
  | _, _, .var name => .var name.index
  | _, _, .con constant => .con constant
  | _, _, .hole slot => .hole slot
  | _, _, .lam body => .lam body.erase
  | _, _, .app (domain := domain) function argument =>
      .app domain function.erase argument.erase

/-- Two terms of one context whose types agree and whose typing is forgotten
to the same tree are one term. -/
theorem Tm.erase_heq {context : List (Ty B)} {type : Ty B}
    (first : Tm signature holes context type) :
    ∀ {other : Ty B} (second : Tm signature holes context other),
      type = other → first.erase = second.erase → HEq first second := by
  induction first with
  | var name =>
      intro other second types same
      cases second with
      | var otherName =>
          subst types
          have indices : name.index = otherName.index := by simpa [Tm.erase] using same
          rw [Var.index_injective name otherName indices]
      | con _ => simp [Tm.erase] at same
      | hole _ => simp [Tm.erase] at same
      | lam _ => simp [Tm.erase] at same
      | app _ _ => simp [Tm.erase] at same
  | con constant =>
      intro other second types same
      cases second with
      | con otherConstant =>
          have constants : constant = otherConstant := by simpa [Tm.erase] using same
          subst constants
          rfl
      | var _ => simp [Tm.erase] at same
      | hole _ => simp [Tm.erase] at same
      | lam _ => simp [Tm.erase] at same
      | app _ _ => simp [Tm.erase] at same
  | hole slot =>
      intro other second types same
      cases second with
      | hole otherSlot =>
          have slots : slot = otherSlot := by simpa [Tm.erase] using same
          subst slots
          rfl
      | var _ => simp [Tm.erase] at same
      | con _ => simp [Tm.erase] at same
      | lam _ => simp [Tm.erase] at same
      | app _ _ => simp [Tm.erase] at same
  | lam body ih =>
      intro other second types same
      cases second with
      | lam otherBody =>
          cases types
          have bodies : body.erase = otherBody.erase := by simpa [Tm.erase] using same
          rw [eq_of_heq (ih otherBody rfl bodies)]
      | var _ => simp [Tm.erase] at same
      | con _ => simp [Tm.erase] at same
      | hole _ => simp [Tm.erase] at same
      | app _ _ => simp [Tm.erase] at same
  | app function argument ihFunction ihArgument =>
      intro other second types same
      cases second with
      | app otherFunction otherArgument =>
          subst types
          simp only [Tm.erase, RawTm.app.injEq] at same
          obtain ⟨domains, functions, arguments⟩ := same
          subst domains
          rw [eq_of_heq (ihFunction otherFunction rfl functions),
            eq_of_heq (ihArgument otherArgument rfl arguments)]
      | var _ => simp [Tm.erase] at same
      | con _ => simp [Tm.erase] at same
      | hole _ => simp [Tm.erase] at same
      | lam _ => simp [Tm.erase] at same

/-- **Forgetting the typing loses no term of a type.** -/
theorem Tm.erase_injective {context : List (Ty B)} {type : Ty B} :
    Function.Injective
      (Tm.erase (signature := signature) (holes := holes) (context := context) (type := type)) :=
  fun first second same => eq_of_heq (Tm.erase_heq first second rfl same)

/-- **The terms of one type over a countable signature are countably many.** -/
theorem Tm.countable [Countable B] [Countable signature.Const] [Countable Hole]
    (context : List (Ty B)) (type : Ty B) : Countable (Tm signature holes context type) :=
  Tm.erase_injective.countable

/-- **Over a countable signature the conversion classes of the closed terms
of each type are numbered**: a number for each closed term, the same for two
terms exactly when they are convertible. -/
theorem exists_conversionCode [Countable B] (signature : Signature B)
    [Countable signature.Const] (type : Ty B) :
    ∃ code : Closed signature type → Nat,
      ∀ first second : Closed signature type, code first = code second ↔ Conv first second := by
  have : Countable (Closed signature type) := Tm.countable [] type
  let classes : Setoid (Closed signature type) := ⟨Conv, Relation.EqvGen.is_equivalence _⟩
  obtain ⟨number, injective⟩ := exists_injective_nat (Quotient classes)
  exact ⟨fun term => number (Quotient.mk classes term), fun first second =>
    ⟨fun same => Quotient.exact (injective same),
      fun convertible => congrArg number (Quotient.sound convertible)⟩⟩

end Framework

/-- **The frameworks over the countable signatures**: countably many base
types and countably many constants. -/
def CountableFramework (source : ContextTheory.{0}) : Prop :=
  ∃ (B : Type) (_ : Countable B) (signature : Signature B) (_ : Countable signature.Const),
    source = frameworkTheory signature

/-- The terms of one type of such a framework, up to its conversion, as a
theory given by its terms alone. -/
def CountableFrameworkTerms (source : ContextTheory.{0}) : Prop :=
  ∃ (B : Type) (_ : Countable B) (signature : Signature B) (_ : Countable signature.Const)
    (type : Ty B), source = ((frameworkTheory signature).gslt type).termsAlone

/-- Every interface of a framework over a countable signature has countably
many terms. -/
theorem CountableFramework.countable_term {source : ContextTheory.{0}}
    (countable : CountableFramework source) (interface : source.Interface) :
    Countable (source.Term interface) := by
  obtain ⟨B, _, signature, _, rfl⟩ := countable
  exact Tm.countable [] interface

/-- **Inert data indexed by the natural numbers host the terms of every type
of the framework over every countable signature**, up to its conversion. -/
theorem hostsEvery_countableFrameworkTerms_of_inertData {theory : ContextTheory.{0}}
    (data : theory.InertData Nat) : HostsEvery theory CountableFrameworkTerms := by
  rintro source ⟨B, countable, signature, constants, type, rfl⟩
  obtain ⟨code, spec⟩ := exists_conversionCode signature type
  exact ⟨data.codeMap (source := (frameworkTheory signature).gslt type) code
      (fun convertible => (spec _ _).mpr convertible),
    data.codeMap_hosting (source := (frameworkTheory signature).gslt type) code
      (fun convertible => (spec _ _).mpr convertible)
      (fun first second same => (spec first second).mp same)
      (fun _ _ step => step)⟩

/-! ## Examples -/

/-- One judgment and two axioms for it. -/
def twoAxioms : RuleSignature Unit where
  Shape := fun _ _ => Bool
  Position := fun _ => Empty
  next := fun _ position => position.elim

/-- The axioms have no premise. -/
def twoAxiomsFinitary : twoAxioms.Finitary where
  arity := fun _ => 0
  position := fun _ => ⟨fun index => index.elim0, fun position => position.elim,
    fun index => index.elim0, fun position => position.elim⟩

/-- **Positive**: the two axioms are numbered zero and one. -/
def twoAxiomsNumbering : twoAxioms.Numbering where
  code := fun {_} (shape : Bool) => shape.toNat
  injective := fun {_} {first second : Bool} same => by
    cases first <;> cases second <;> first | rfl | cases same

/-- The derivation by one of the two axioms. -/
def chosenAxiom (choice : Bool) : twoAxioms.Proof () :=
  twoAxioms.node (j := ()) choice fun position => position.elim

/-- The two derivations of the judgment are kept apart by their numbers. -/
theorem chosenAxiom_code_ne :
    twoAxiomsFinitary.proofCode twoAxiomsNumbering (chosenAxiom true) ≠
      twoAxiomsFinitary.proofCode twoAxiomsNumbering (chosenAxiom false) := by
  intro same
  have equal := twoAxiomsFinitary.proofCode_injective twoAxiomsNumbering _ _ same
  have shapes : true = false := by
    cases equal
  cases shapes

theorem twoAxioms_numberedProofSystem :
    NumberedProofSystem (twoAxioms.proofTheory (ProofCongruence.identity twoAxioms)) :=
  ⟨Unit, twoAxioms, twoAxiomsFinitary, twoAxiomsNumbering, rfl⟩

/-- One judgment and an axiom for each set of natural numbers. -/
def continuumAxioms : RuleSignature Unit where
  Shape := fun _ _ => Set Nat
  Position := fun _ => Empty
  next := fun _ position => position.elim

/-- **Negative**: a signature with an axiom for each set of natural numbers
has no numbering. -/
theorem continuumAxioms_not_numbering : IsEmpty continuumAxioms.Numbering :=
  ⟨fun numbering => Function.cantor_injective (fun shape : Set Nat => numbering.code (j := ()) shape)
    fun _ _ same => numbering.injective same⟩

/-- **Positive**: the framework over the two axioms is a framework over a
countable signature. -/
theorem twoAxioms_countableFramework :
    CountableFramework (frameworkTheory twoAxiomsFinitary.signature) :=
  ⟨Unit, inferInstance, twoAxiomsFinitary.signature,
    inferInstanceAs (Countable (Σ _ : Unit, Bool)), rfl⟩

/-- One base type and a constant of it for each set of natural numbers. -/
def continuumSignature : Signature Unit where
  Const := Set Nat
  arity := fun _ => 0
  argument := fun _ index => index.elim0
  result := fun _ => ()

/-- **Negative**: the framework over a constant for each set of natural
numbers is not a framework over a countable signature. -/
theorem continuumSignature_not_countableFramework :
    ¬ CountableFramework (frameworkTheory continuumSignature) := by
  intro countable
  have := countable.countable_term (Ty.base ())
  obtain ⟨number, injective⟩ :=
    exists_injective_nat ((frameworkTheory continuumSignature).Term (Ty.base ()))
  refine Function.cantor_injective (fun constant : Set Nat =>
    number (Tm.con (signature := continuumSignature) (holes := noHoles) (context := []) constant :
      Closed continuumSignature (Ty.base ()))) ?_
  intro first second same
  have erased : RawTm.con (Hole := Empty) (B := Unit) first = RawTm.con second :=
    congrArg Tm.erase (injective same)
  exact RawTm.con.inj erased

#print axioms RuleSignature.Finitary.proofCode_injective
#print axioms frameworkCode_eq_iff
#print axioms hostsEvery_numberedDerivations_of_inertData
#print axioms hostsEvery_numberedFrameworkJudgments_of_inertData
#print axioms chosenAxiom_code_ne
#print axioms continuumAxioms_not_numbering
#print axioms Framework.Tm.erase_injective
#print axioms Framework.Tm.countable
#print axioms Framework.exists_conversionCode
#print axioms hostsEvery_countableFrameworkTerms_of_inertData
#print axioms twoAxioms_countableFramework
#print axioms continuumSignature_not_countableFramework

end Mettapedia.Logic.HostingStyles
