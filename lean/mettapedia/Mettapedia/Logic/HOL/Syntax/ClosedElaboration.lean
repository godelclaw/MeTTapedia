import Mettapedia.Logic.HOL.Syntax.NamedElaboration
import Mathlib.Data.List.Forall2

/-!
# Closed elaboration of constants and curried applications

`Elaborates signature term type` says that `NamedElaboration.infer`, run on a
closed named term, returns an intrinsic term of the given type.  This module
characterizes it on constants and curried application spines, for an
arbitrary constant signature.

On *applicative* terms (constants and applications only) elaboration is the
ordinary typing relation `ApplicativeTyped` read off the types the signature
assigns to names (`elaborates_iff_applicativeTyped`).  Since that relation
sees only those types, elaboration is invariant under any renaming of
constants that preserves them (`elaborates_mapConst_iff`): two signatures
with different name spaces type the same applicative terms exactly when they
agree on the types of corresponding names.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.NamedElaboration

open Mettapedia.Logic.HOL

variable {Base : Type} [DecidableEq Base]
variable {ConstName : Type} {Const : Ty Base → Type}

/-- Closed elaboration of a named HOL term at one HOL type. -/
def Elaborates (signature : Signature ConstName Const)
    (term : NamedTerm Base String ConstName) (type : Ty Base) : Prop :=
  ∃ intrinsic : Term Const [] type,
    infer signature (BinderNames.nil : BinderNames Base String []) term =
      .ok ⟨type, intrinsic⟩

omit [DecidableEq Base] in
private theorem ok_someTerm_iff {error : Type}
    {left right : Ty Base} (term : Term Const [] left) :
    (∃ other : Term Const [] right,
      (Except.ok ⟨left, term⟩ : Except error (SomeTerm Const [])) =
        .ok ⟨right, other⟩) ↔ left = right := by
  constructor
  · rintro ⟨other, equal⟩
    have := congrArg (fun result : Except error (SomeTerm Const []) =>
      match result with
      | .ok value => some value.type
      | .error _ => none) equal
    simpa using this
  · rintro rfl
    exact ⟨term, rfl⟩

/-- A curried application elaborates at `ρ` exactly when its function
elaborates at some `σ ⇒ ρ` and its argument at `σ`. -/
theorem elaborates_app_iff {signature : Signature ConstName Const}
    {function argument : NamedTerm Base String ConstName} {result : Ty Base} :
    Elaborates signature (.app function argument) result ↔
      ∃ domain, Elaborates signature function (.arr domain result) ∧
        Elaborates signature argument domain := by
  constructor
  · rintro ⟨intrinsic, inferred⟩
    cases functionInferred : infer signature
        (BinderNames.nil : BinderNames Base String []) function with
    | error failure =>
        simp [infer, functionInferred] at inferred
    | ok functionResult =>
        obtain ⟨functionType, functionTerm⟩ := functionResult
        cases functionType with
        | prop => simp [infer, functionInferred] at inferred
        | base name => simp [infer, functionInferred] at inferred
        | arr domain codomain =>
            cases argumentInferred : infer signature
                (BinderNames.nil : BinderNames Base String []) argument with
            | error failure =>
                simp [infer, functionInferred, argumentInferred] at inferred
            | ok argumentResult =>
                obtain ⟨argumentType, argumentTerm⟩ := argumentResult
                by_cases sameType : argumentType = domain
                · subst sameType
                  simp [infer, functionInferred, argumentInferred, expectType] at inferred
                  obtain ⟨codomainEq, _⟩ := inferred
                  subst codomainEq
                  exact ⟨argumentType, ⟨functionTerm, functionInferred⟩,
                    ⟨argumentTerm, argumentInferred⟩⟩
                · simp [infer, functionInferred, argumentInferred, expectType,
                    sameType] at inferred
  · rintro ⟨domain, ⟨functionTerm, functionInferred⟩,
      ⟨argumentTerm, argumentInferred⟩⟩
    refine ⟨.app functionTerm argumentTerm, ?_⟩
    simp [infer, functionInferred, argumentInferred, expectType]

/-- A constant elaborates exactly at the type its signature assigns. -/
theorem elaborates_constant_iff {signature : Signature ConstName Const}
    {name : ConstName} {type : Ty Base} :
    Elaborates signature (.constant name) type ↔
      ∃ constant : Const type, signature name = some ⟨type, constant⟩ := by
  constructor
  · rintro ⟨intrinsic, inferred⟩
    cases lookup : signature name with
    | none => simp [infer, lookup] at inferred
    | some resolved =>
        obtain ⟨resolvedType, constant⟩ := resolved
        simp only [infer, lookup] at inferred
        have typeEq : resolvedType = type :=
          (ok_someTerm_iff (error := Error Base String ConstName) _).mp
            ⟨intrinsic, inferred⟩
        subst typeEq
        exact ⟨constant, rfl⟩
  · rintro ⟨constant, lookup⟩
    refine ⟨.const constant, ?_⟩
    simp [infer, lookup]

/-- Elaboration of a left-nested spine of curried applications. -/
theorem elaborates_foldl_app_iff {signature : Signature ConstName Const}
    {α : Type} (translate : α → NamedTerm Base String ConstName) :
    ∀ (function : NamedTerm Base String ConstName) (arguments : List α)
      (result : Ty Base),
      Elaborates signature
          (arguments.foldl (fun accumulated argument =>
            .app accumulated (translate argument)) function) result ↔
        ∃ argumentTypes : List (Ty Base),
          Elaborates signature function (argumentTypes.foldr Ty.arr result) ∧
            List.Forall₂ (fun argument type =>
              Elaborates signature (translate argument) type)
              arguments argumentTypes
  | function, [], result => by
      constructor
      · intro elaborated
        exact ⟨[], elaborated, .nil⟩
      · rintro ⟨argumentTypes, elaborated, arguments⟩
        cases arguments
        exact elaborated
  | function, argument :: arguments, result => by
      rw [List.foldl_cons, elaborates_foldl_app_iff translate]
      constructor
      · rintro ⟨argumentTypes, applied, rest⟩
        obtain ⟨domain, functionElaborates, argumentElaborates⟩ :=
          elaborates_app_iff.mp applied
        exact ⟨domain :: argumentTypes, functionElaborates,
          .cons argumentElaborates rest⟩
      · rintro ⟨argumentTypes, functionElaborates, all⟩
        cases all with
        | cons argumentElaborates rest =>
            exact ⟨_, elaborates_app_iff.mpr
              ⟨_, functionElaborates, argumentElaborates⟩, rest⟩

omit [DecidableEq Base] in
/-- Curried arrows of equal length are equal only componentwise. -/
theorem foldr_arr_injective :
    ∀ {left right : List (Ty Base)} {leftResult rightResult : Ty Base},
      left.length = right.length →
      left.foldr Ty.arr leftResult = right.foldr Ty.arr rightResult →
      left = right ∧ leftResult = rightResult
  | [], [], _, _, _, equal => ⟨rfl, equal⟩
  | [], _ :: _, _, _, lengths, _ => by simp at lengths
  | _ :: _, [], _, _, lengths, _ => by simp at lengths
  | leftHead :: leftTail, rightHead :: rightTail, _, _, lengths, equal => by
      simp only [List.foldr_cons] at equal
      obtain ⟨heads, tails⟩ := Ty.arr.inj equal
      obtain ⟨tailsEqual, results⟩ :=
        foldr_arr_injective (by simpa using lengths) tails
      exact ⟨by rw [heads, tailsEqual], results⟩

/-! ## Applicative terms -/

/-- The type a signature assigns to a constant name. -/
def signatureType (signature : Signature ConstName Const) (name : ConstName) :
    Option (Ty Base) :=
  (signature name).map Sigma.fst

omit [DecidableEq Base] in
theorem signatureType_eq_some_iff {signature : Signature ConstName Const}
    {name : ConstName} {type : Ty Base} :
    signatureType signature name = some type ↔
      ∃ constant : Const type, signature name = some ⟨type, constant⟩ := by
  unfold signatureType
  constructor
  · intro lookup
    cases found : signature name with
    | none => simp [found] at lookup
    | some resolved =>
        obtain ⟨resolvedType, constant⟩ := resolved
        simp only [found, Option.map_some, Option.some.injEq] at lookup
        subst lookup
        exact ⟨constant, rfl⟩
  · rintro ⟨constant, found⟩
    simp [found]

/-- Terms built from constants by application. -/
inductive Applicative : NamedTerm Base String ConstName → Prop where
  | constant (name : ConstName) : Applicative (.constant name)
  | app {function argument : NamedTerm Base String ConstName} :
      Applicative function → Applicative argument → Applicative (.app function argument)

/-- Typing of applicative terms, read off the types assigned to names. -/
inductive ApplicativeTyped (typeOf : ConstName → Option (Ty Base)) :
    NamedTerm Base String ConstName → Ty Base → Prop where
  | constant {name : ConstName} {type : Ty Base} :
      typeOf name = some type → ApplicativeTyped typeOf (.constant name) type
  | app {function argument : NamedTerm Base String ConstName} {domain result : Ty Base} :
      ApplicativeTyped typeOf function (.arr domain result) →
      ApplicativeTyped typeOf argument domain →
      ApplicativeTyped typeOf (.app function argument) result

/-- On applicative terms, elaboration is applicative typing over the types
the signature assigns. -/
theorem elaborates_iff_applicativeTyped {signature : Signature ConstName Const}
    {term : NamedTerm Base String ConstName} (applicative : Applicative term) :
    ∀ {type : Ty Base},
      Elaborates signature term type ↔
        ApplicativeTyped (signatureType signature) term type := by
  induction applicative with
  | constant name =>
      intro type
      rw [elaborates_constant_iff, ← signatureType_eq_some_iff]
      constructor
      · exact .constant
      · intro typed
        cases typed with
        | constant lookup => exact lookup
  | app _ _ functionIH argumentIH =>
      intro type
      rw [elaborates_app_iff]
      constructor
      · rintro ⟨domain, functionElaborates, argumentElaborates⟩
        exact .app (functionIH.mp functionElaborates) (argumentIH.mp argumentElaborates)
      · intro typed
        cases typed with
        | app functionTyped argumentTyped =>
            exact ⟨_, functionIH.mpr functionTyped, argumentIH.mpr argumentTyped⟩

omit [DecidableEq Base] in
/-- Applicative typing is functional. -/
theorem ApplicativeTyped.unique {typeOf : ConstName → Option (Ty Base)}
    {term : NamedTerm Base String ConstName} {left right : Ty Base}
    (leftTyped : ApplicativeTyped typeOf term left)
    (rightTyped : ApplicativeTyped typeOf term right) : left = right := by
  induction leftTyped generalizing right with
  | constant lookup =>
      cases rightTyped with
      | constant lookup' =>
          rw [lookup] at lookup'
          exact Option.some.inj lookup'
  | app _ _ functionIH _ =>
      cases rightTyped with
      | app functionTyped _ =>
          exact (Ty.arr.inj (functionIH functionTyped)).2

omit [DecidableEq Base] in
/-- Applicative typing of a left-nested spine of applications. -/
theorem applicativeTyped_foldl_iff {typeOf : ConstName → Option (Ty Base)} :
    ∀ (function : NamedTerm Base String ConstName)
      (arguments : List (NamedTerm Base String ConstName)) (result : Ty Base),
      ApplicativeTyped typeOf (arguments.foldl .app function) result ↔
        ∃ argumentTypes : List (Ty Base),
          ApplicativeTyped typeOf function (argumentTypes.foldr Ty.arr result) ∧
            List.Forall₂ (ApplicativeTyped typeOf) arguments argumentTypes
  | function, [], result => by
      constructor
      · intro typed
        exact ⟨[], typed, .nil⟩
      · rintro ⟨argumentTypes, typed, all⟩
        cases all
        exact typed
  | function, argument :: arguments, result => by
      rw [List.foldl_cons, applicativeTyped_foldl_iff]
      constructor
      · rintro ⟨argumentTypes, applied, rest⟩
        cases applied with
        | app functionTyped argumentTyped =>
            exact ⟨_ :: argumentTypes, functionTyped, .cons argumentTyped rest⟩
      · rintro ⟨argumentTypes, functionTyped, all⟩
        cases all with
        | cons argumentTyped rest => exact ⟨_, .app functionTyped argumentTyped, rest⟩

omit [DecidableEq Base] in
theorem Applicative.foldl {function : NamedTerm Base String ConstName}
    (functionApplicative : Applicative function) :
    ∀ {arguments : List (NamedTerm Base String ConstName)},
      (∀ argument ∈ arguments, Applicative argument) →
        Applicative (arguments.foldl .app function)
  | [], _ => functionApplicative
  | argument :: arguments, all => by
      rw [List.foldl_cons]
      exact Applicative.foldl (.app functionApplicative (all argument (by simp)))
        (fun other member => all other (List.mem_cons_of_mem _ member))

/-! ## Renaming constants -/

/-- Rename the constants of a named term. -/
def NamedTerm.mapConst {Source Target : Type} (rename : Source → Target) :
    NamedTerm Base String Source → NamedTerm Base String Target
  | .variable name => .variable name
  | .constant name => .constant (rename name)
  | .app function argument => .app (mapConst rename function) (mapConst rename argument)
  | .lam binder domain body => .lam binder domain (mapConst rename body)
  | .top => .top
  | .bottom => .bottom
  | .and left right => .and (mapConst rename left) (mapConst rename right)
  | .or left right => .or (mapConst rename left) (mapConst rename right)
  | .imp antecedent consequent =>
      .imp (mapConst rename antecedent) (mapConst rename consequent)
  | .not body => .not (mapConst rename body)
  | .equal left right => .equal (mapConst rename left) (mapConst rename right)
  | .forallE binder domain body => .forallE binder domain (mapConst rename body)
  | .existsE binder domain body => .existsE binder domain (mapConst rename body)

omit [DecidableEq Base] in
theorem Applicative.mapConst {Source Target : Type} (rename : Source → Target)
    {term : NamedTerm Base String Source} (applicative : Applicative term) :
    Applicative (term.mapConst rename) := by
  induction applicative with
  | constant name => exact .constant (rename name)
  | app _ _ functionIH argumentIH => exact .app functionIH argumentIH

omit [DecidableEq Base] in
theorem NamedTerm.mapConst_foldl {Source Target : Type} (rename : Source → Target) :
    ∀ (function : NamedTerm Base String Source) (arguments : List (NamedTerm Base String Source)),
      (arguments.foldl .app function).mapConst rename =
        (arguments.map (NamedTerm.mapConst rename)).foldl .app (function.mapConst rename)
  | _, [] => rfl
  | function, argument :: arguments => by
      simp only [List.foldl_cons, List.map_cons]
      exact NamedTerm.mapConst_foldl rename (.app function argument) arguments

omit [DecidableEq Base] in
/-- Applicative typing sees a renamed term through the renaming. -/
theorem applicativeTyped_mapConst_iff {Source Target : Type} (rename : Source → Target)
    {typeOf : Target → Option (Ty Base)} {term : NamedTerm Base String Source}
    (applicative : Applicative term) :
    ∀ {type : Ty Base},
      ApplicativeTyped typeOf (term.mapConst rename) type ↔
        ApplicativeTyped (typeOf ∘ rename) term type := by
  induction applicative with
  | constant name =>
      intro type
      constructor
      · intro typed
        cases typed with
        | constant lookup => exact .constant lookup
      · intro typed
        cases typed with
        | constant lookup => exact .constant lookup
  | app _ _ functionIH argumentIH =>
      intro type
      constructor
      · intro typed
        cases typed with
        | app functionTyped argumentTyped =>
            exact .app (functionIH.mp functionTyped) (argumentIH.mp argumentTyped)
      · intro typed
        cases typed with
        | app functionTyped argumentTyped =>
            exact .app (functionIH.mpr functionTyped) (argumentIH.mpr argumentTyped)

/-- **Elaboration is invariant under type-preserving renaming of
constants.**  An applicative term elaborates in one signature exactly when
its renaming elaborates in another signature that assigns every renamed name
the type of its source. -/
theorem elaborates_mapConst_iff {Source Target : Type}
    {SourceConst TargetConst : Ty Base → Type}
    {source : Signature Source SourceConst} {target : Signature Target TargetConst}
    (rename : Source → Target)
    (agree : ∀ name, signatureType target (rename name) = signatureType source name)
    {term : NamedTerm Base String Source} (applicative : Applicative term)
    {type : Ty Base} :
    Elaborates target (term.mapConst rename) type ↔ Elaborates source term type := by
  rw [elaborates_iff_applicativeTyped (applicative.mapConst rename),
    elaborates_iff_applicativeTyped applicative, applicativeTyped_mapConst_iff rename applicative]
  have equal : (signatureType target ∘ rename) = signatureType source := funext agree
  rw [equal]

#print axioms elaborates_iff_applicativeTyped
#print axioms elaborates_mapConst_iff
#print axioms applicativeTyped_foldl_iff

end Mettapedia.Logic.HOL.NamedElaboration
