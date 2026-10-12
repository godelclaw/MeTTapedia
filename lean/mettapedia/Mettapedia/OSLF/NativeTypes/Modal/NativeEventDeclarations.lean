import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.NativeTypes.Certificates.NativeEnumeration
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-!
# Finite native event declarations from authored modal schemas

Every declaration index comes from the generated schema catalogue. Event
families depend on a complete focus/assignment input. Their source and specified
contractum projections consume that input and the whole event value. Headers
are formed by the full native dependent rules, with checked earlier ranks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable (plan : Plan)

abbrev Index := Fin (schemas plan).length

def schema (index : Index plan) : Rules.Schema plan := (schemas plan)[index]

inductive Carrier where
  | input
  | pattern
  deriving DecidableEq, Encodable

inductive TypeSymbol where
  | carrier (carrier : Carrier)
  | event (index : Index plan)
  deriving DecidableEq, Encodable

inductive TermSymbol where
  | source (index : Index plan)
  | target (index : Index plan)
  deriving DecidableEq, Encodable

abbrev symbols : Symbols where
  TypeSymbol := TypeSymbol plan
  TermSymbol := TermSymbol plan
  PredicateSymbol := Empty
  typeArity := fun symbol => match symbol with
    | .carrier _ => 0
    | .event _ => 1
  termArity _ := 2
  predicateArity symbol := nomatch symbol

variable {plan}

def carrierType (carrier : Carrier) (n : Nat) : TypeExpr (symbols plan) n :=
  .family (.carrier carrier) Fin.elim0

def inputContext : ContextExpr (symbols plan) 1 :=
  .snoc .nil (carrierType .input 0)

def singletonArgument {n : Nat} (value : TermExpr (symbols plan) n) :
    Substitution (symbols plan) 1 n := extendSubstitution Fin.elim0 value

def eventType (index : Index plan) {n : Nat} (input : TermExpr (symbols plan) n) :
    TypeExpr (symbols plan) n :=
  .family (.event index) (singletonArgument input)

def eventContext (index : Index plan) : ContextExpr (symbols plan) 2 :=
  .snoc inputContext (eventType index (.var 0))

def signature (plan : Plan) : Signature (symbols plan) where
  typeRank := fun symbol => match symbol with
    | .carrier _ => 0
    | .event _ => 1
  termRank _ := 2
  predicateRank symbol := nomatch symbol
  typeParameters := fun symbol => match symbol with
    | .carrier _ => .nil
    | .event _ => inputContext
  termParameters := fun symbol => match symbol with
    | .source index | .target index => eventContext index
  predicateParameters symbol := nomatch symbol
  termResult _ := carrierType .pattern 2
  typeParameters_before := by
    intro symbol
    cases symbol with
    | carrier => trivial
    | event => exact ⟨True.intro, Nat.zero_lt_succ 0, fun position => Fin.elim0 position⟩
  termParameters_before := by
    intro symbol
    cases symbol <;> exact ⟨⟨True.intro, Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩,
      Nat.lt_succ_self 1, fun position => by
        cases position using Fin.cases with
        | zero => trivial
        | succ impossible => exact Fin.elim0 impossible⟩
  predicateParameters_before symbol := nomatch symbol
  termResult_before _ := ⟨Nat.zero_lt_succ 1, fun position => Fin.elim0 position⟩

@[simp] theorem carrierType_rename (carrier : Carrier) {n m : Nat} (mapping : Renaming n m) :
    (carrierType (plan := plan) carrier n).rename mapping = carrierType carrier m := by
  apply congrArg (TypeExpr.family (S := symbols plan) (.carrier carrier))
  funext position
  exact Fin.elim0 position

@[simp] theorem carrierType_substitute (carrier : Carrier) {n m : Nat}
    (substitution : Substitution (symbols plan) n m) :
    (carrierType carrier n).substitute substitution = carrierType carrier m := by
  apply congrArg (TypeExpr.family (S := symbols plan) (.carrier carrier))
  funext position
  exact Fin.elim0 position

def emptyFormed : Derivation (signature plan) (.context .nil) :=
  deriveList .contextNil .nil

def carrierFormed (carrier : Carrier) {n : Nat} {context : ContextExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context)) :
    Derivation (signature plan) (.type context (carrierType carrier n)) :=
  deriveList (.typeFamily context (.carrier carrier) Fin.elim0)
    (.cons formed (.cons emptyFormed
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

def inputContextFormed : Derivation (signature plan) (.context inputContext) :=
  deriveList (.contextExtend .nil (carrierType .input 0))
    (.cons emptyFormed (.cons (carrierFormed .input emptyFormed) .nil))

theorem emptyFormed_before (bound : Nat) :
    (emptyFormed (plan := plan)).before bound :=
  deriveList_before .contextNil .nil bound True.intro True.intro

theorem carrierFormed_before (carrier : Carrier) {n : Nat} {context : ContextExpr (symbols plan) n}
    (formed : Derivation (signature plan) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 0 < bound) :
    (carrierFormed carrier formed).before bound := by
  have contextOrder := formed.before_judgment ordered
  have emptySubstitutionOrder :
      (deriveList (.substitutionNil context) (.cons formed .nil)).before bound :=
    deriveList_before (.substitutionNil context) (.cons formed .nil) bound
      ⟨contextOrder, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩
  exact deriveList_before (.typeFamily context (.carrier carrier) Fin.elim0) _ bound
    ⟨contextOrder, positive, fun position => Fin.elim0 position⟩
    ⟨ordered, emptyFormed_before bound, emptySubstitutionOrder, True.intro⟩

theorem inputContextFormed_before (bound : Nat) (positive : 0 < bound) :
    (inputContextFormed (plan := plan)).before bound :=
  deriveList_before (.contextExtend .nil (carrierType .input 0)) _ bound
    ⟨True.intro, positive, fun position => Fin.elim0 position⟩
    ⟨emptyFormed_before bound,
      carrierFormed_before .input emptyFormed bound (emptyFormed_before bound) positive, True.intro⟩

def inputArguments {n : Nat} {context : ContextExpr (symbols plan) n}
    {value : TermExpr (symbols plan) n} (formed : Derivation (signature plan) (.context context))
    (typed : Derivation (signature plan) (.term context value (carrierType .input n))) :
    Derivation (signature plan) (.substitution context inputContext (singletonArgument value)) := by
  have valueTree : Derivation (signature plan)
      (.term context value ((carrierType .input 0).substitute Fin.elim0)) := by
    exact (congrArg (Judgment.term context value)
      (carrierType_substitute .input (Fin.elim0 : Substitution (symbols plan) 0 n))).symm ▸ typed
  exact deriveList (.substitutionExtend context .nil (carrierType .input 0) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (carrierFormed .input emptyFormed) (.cons valueTree .nil)))

def inputVariableFormed :
    Derivation (signature plan) (.term inputContext (.var 0) (carrierType .input 1)) := by
  have equal :
      (.term inputContext (.var 0) (inputContext.lookup 0) : Judgment (symbols plan)) =
      .term inputContext (.var 0) (carrierType .input 1) := by
    simp only [inputContext, ContextExpr.lookup_zero, carrierType_rename]
  exact equal ▸ deriveList (.variable inputContext 0) (.cons inputContextFormed .nil)

@[simp] theorem before_cast {first second : Judgment (symbols plan)}
    (equal : first = second) (tree : Derivation (signature plan) first) (bound : Nat) :
    (equal ▸ tree).before bound ↔ tree.before bound := by
  cases equal
  rfl

def eventFormation (index : Index plan) :
    Derivation (signature plan) (.type inputContext (eventType index (.var 0))) :=
  deriveList (.typeFamily inputContext (.event index) (singletonArgument (.var 0)))
    (.cons inputContextFormed (.cons inputContextFormed
      (.cons (inputArguments inputContextFormed inputVariableFormed) .nil)))

def eventContextFormed (index : Index plan) :
    Derivation (signature plan) (.context (eventContext index)) :=
  deriveList (.contextExtend inputContext (eventType index (.var 0)))
    (.cons inputContextFormed (.cons (eventFormation index) .nil))

theorem inputVariableFormed_before (bound : Nat) (positive : 0 < bound) :
    (inputVariableFormed (plan := plan)).before bound := by
  have treeOrder := deriveList_before (.variable inputContext 0)
    (.cons inputContextFormed .nil) bound
    (show (RuleCode.variable (D := signature plan) inputContext 0).conclusion.before
      (signature plan) bound from
      ⟨⟨True.intro, positive, fun position => Fin.elim0 position⟩,
        True.intro, positive, fun position => Fin.elim0 position⟩)
    ⟨inputContextFormed_before bound positive, True.intro⟩
  have equal :
      (.term inputContext (.var 0) (inputContext.lookup 0) : Judgment (symbols plan)) =
      .term inputContext (.var 0) (carrierType .input 1) := by
    simp only [inputContext, ContextExpr.lookup_zero, carrierType_rename]
  exact (before_cast equal
    (deriveList (.variable inputContext 0) (.cons inputContextFormed .nil)) bound).mpr treeOrder

theorem eventFormation_before (index : Index plan) (bound : Nat) (positive : 1 < bound) :
    (eventFormation index).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (Nat.zero_lt_succ 0) positive
  have inputOrder := inputContextFormed_before (plan := plan) bound zeroPositive
  have emptyOrder := emptyFormed_before (plan := plan) bound
  have argumentOrder :
      (inputArguments (plan := plan) inputContextFormed inputVariableFormed).before bound := by
    unfold inputArguments
    exact deriveList_before
      (.substitutionExtend inputContext .nil (carrierType .input 0) Fin.elim0 (.var 0)) _ bound
      ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
        ⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
        fun p => by
          cases p using Fin.cases with
          | zero => trivial
          | succ impossible => exact Fin.elim0 impossible⟩
      ⟨deriveList_before (.substitutionNil inputContext) _ bound
          ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
            True.intro, fun p => Fin.elim0 p⟩ ⟨inputOrder, True.intro⟩,
        carrierFormed_before .input emptyFormed bound emptyOrder zeroPositive,
        by simpa only [before_cast] using inputVariableFormed_before (plan := plan) bound zeroPositive,
        True.intro⟩
  exact deriveList_before
    (.typeFamily inputContext (.event index) (singletonArgument (.var 0))) _ bound
    ⟨⟨True.intro, zeroPositive, fun p => Fin.elim0 p⟩,
      positive, fun p => by
        cases p using Fin.cases with
        | zero => trivial
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨inputOrder, inputOrder, argumentOrder, True.intro⟩

theorem eventContextFormed_before (index : Index plan) (bound : Nat) (positive : 1 < bound) :
    (eventContextFormed index).before bound :=
  deriveList_before (.contextExtend inputContext (eventType index (.var 0))) _ bound
    ⟨⟨True.intro, Nat.lt_trans (Nat.zero_lt_succ 0) positive, fun p => Fin.elim0 p⟩,
      positive, fun p => by
        cases p using Fin.cases with
        | zero => trivial
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨inputContextFormed_before bound (Nat.lt_trans (Nat.zero_lt_succ 0) positive),
      eventFormation_before index bound positive, True.intro⟩

def headers (plan : Plan) : HeaderFormation (signature plan) where
  typeHeader := fun symbol => match symbol with
    | .carrier _ => emptyFormed
    | .event _ => inputContextFormed
  typeHeader_before := by
    intro symbol
    cases symbol with
    | carrier => exact emptyFormed_before 0
    | event => exact inputContextFormed_before 1 (by decide)
  termHeader := fun symbol => match symbol with
    | .source index | .target index => eventContextFormed index
  termHeader_before := by
    intro symbol
    cases symbol <;> exact eventContextFormed_before _ 2 (by decide)
  termResult := fun symbol => match symbol with
    | .source index | .target index => carrierFormed .pattern (eventContextFormed index)
  termResult_before := by
    intro symbol
    cases symbol <;> exact carrierFormed_before .pattern _ 2
      (eventContextFormed_before _ 2 (by decide)) (by decide)
  predicateHeader symbol := nomatch symbol
  predicateHeader_before symbol := nomatch symbol

def certificate (index : Index plan) : Certificates.Refinement.Certificate (signature plan) :=
  Certificates.Refinement.erase (eventFormation index)

theorem certificate_checked (index : Index plan) :
    Certificates.Refinement.check (certificate index)
      (.type inputContext (eventType index (.var 0))) = true :=
  Certificates.Refinement.check_erase (eventFormation index)

/-- Ordered indices select the actual generated schema, retaining duplicate
origins even when two schemas happen to have the same interpreted endpoint. -/
theorem schema_member (index : Index plan) : schema plan index ∈ schemas plan :=
  List.getElem_mem index.isLt

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventDeclarations
