import Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalCounter

/-!
# Typed admission of the authored natural eliminator rows

The concrete module's zero and successor rows are checked against the existing
strictly positive natural-family candidate. A partial interpretation of the
parsed rule patterns binds their endpoints to the candidate's canonical typed
iota schemas. Typed context substitution and explicit result-type adjustment
then reconstruct receipts at the caller's displayed type.

This is a concrete declaration binding, not a generic inductive elaborator or a
new type checker. Raw root execution alone still grants no typing authority;
the complete raw signature is not claimed to be `IndexedFamily.Authorized`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.IndexedFamily
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId


inductive Branch where
  | zero
  | succ
deriving DecidableEq, Repr

abbrev Branch.arity : Branch → Nat
  | .zero => 3
  | .succ => 4

def Branch.constructor : Branch → ConstructorSpec NativeNaturalVectorFamilies.rawSignature NativeNaturalVectorFamilies.natName 0
  | .zero => NativeNaturalVectorFamilies.zeroConstructorSpec
  | .succ => NativeNaturalVectorFamilies.succConstructorSpec

def Branch.schema (branch : Branch) :
    IotaSchema Tower.rules NativeNaturalVectorFamilies.rawSignature NativeNaturalVectorFamilies.proofRelevantIotaComputation branch.arity :=
  match branch with
  | .zero => NativeNaturalVectorFamilies.natZeroIotaSchema
  | .succ => NativeNaturalVectorFamilies.natSuccIotaSchema

def Branch.rowName : Branch → String
  | .zero => "NatZero"
  | .succ => "NatSucc"

def Branch.environment (branch : Branch) : String → Option (Tower.Tm branch.arity) :=
  match branch with
  | .zero => fun atom =>
      if atom == "p" then some (.var 2)
      else if atom == "z" then some (.var 1)
      else if atom == "s" then some (.var 0)
      else none
  | .succ => fun atom =>
      if atom == "p" then some (.var 3)
      else if atom == "z" then some (.var 2)
      else if atom == "s" then some (.var 1)
      else if atom == "n" then some (.var 0)
      else none

/-- Interpretation of already parsed, binder-free rule patterns. `Embed` is the
source grammar's inclusion of natural data into its general expression sort. -/
def lowerPattern {scope : Nat} (environment : String → Option (Tower.Tm scope)) :
    Pattern → Option (Tower.Tm scope)
  | .fvar atom => environment atom
  | .apply "NZero" [] => some NativeNaturalVectorFamilies.zeroTm
  | .apply "NSucc" [arg] => (lowerPattern environment arg).map NativeNaturalVectorFamilies.succApp
  | .apply "Embed" [arg] => lowerPattern environment arg
  | .apply "Apply" [fn, arg] => do
      return .app (← lowerPattern environment fn) (← lowerPattern environment arg)
  | .apply "NatEliminate" [motive, zeroCase, succCase, arg] => do
      return NativeNaturalVectorFamilies.natEliminateApp (← lowerPattern environment motive)
        (← lowerPattern environment zeroCase) (← lowerPattern environment succCase)
        (← lowerPattern environment arg)
  | _ => none

/-- Only the declared argument sorts are relevant here, not printing notation. -/
def declarationShape (label category : String) (parameters : List TermParam) : Bool :=
  Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.terms.any fun row =>
    row.label == label && row.category == category && row.params == parameters &&
      row.algebra?.isNone

def signatureMatches : Bool :=
  declarationShape "NZero" "Nat" [] &&
  declarationShape "NSucc" "Nat" [.simple "n" (.base "Nat")] &&
  declarationShape "Embed" "Term" [.simple "n" (.base "Nat")] &&
  declarationShape "Apply" "Term" [.simple "f" (.base "Term"), .simple "a" (.base "Term")] &&
  declarationShape "NatEliminate" "Term"
    [.simple "p" (.base "Term"), .simple "z" (.base "Term"),
      .simple "s" (.base "Term"), .simple "n" (.base "Nat")]

/-- The finite checks bind the requested declaration identities and actual
source endpoints. They do not ask for either endpoint's typing as an input. -/
def Matches (branch : Branch) (row : RewriteRule)
    (constructor eliminator : DeclName) : Prop :=
  signatureMatches = true ∧
  constructor = branch.constructor.name ∧
  eliminator = NativeNaturalVectorFamilies.natEliminatorSpec.name ∧
  row.name = branch.rowName ∧
  row.typeContext.isEmpty = true ∧ row.premises.isEmpty = true ∧ row.bindings.isNone = true ∧
  lowerPattern branch.environment row.left = some branch.schema.left ∧
  lowerPattern branch.environment row.right = some branch.schema.right

instance (branch : Branch) (row : RewriteRule) (constructor eliminator : DeclName) :
    Decidable (Matches branch row constructor eliminator) := by
  unfold Matches
  infer_instance

structure Admission (branch : Branch) where
  index : Fin Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites.length
  constructor : DeclName
  eliminator : DeclName
  accepted : Matches branch Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites[index] constructor eliminator

def admit? (branch : Branch) (index : Fin Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites.length)
    (constructor eliminator : DeclName) : Option (Admission branch) :=
  if accepted : Matches branch Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites[index] constructor eliminator then
    some ⟨index, constructor, eliminator, accepted⟩
  else none

theorem admit?_isSome_iff (branch : Branch)
    (index : Fin Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites.length)
    (constructor eliminator : DeclName) :
    (admit? branch index constructor eliminator).isSome = true ↔
      Matches branch Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites[index]
        constructor eliminator := by
  unfold admit?
  split
  · rename_i accepted
    exact ⟨fun _ => accepted, fun _ => rfl⟩
  · rename_i rejected
    exact ⟨fun impossible => Bool.noConfusion impossible, fun accepted => False.elim (rejected accepted)⟩

def Admission.row {branch : Branch} (admission : Admission branch) : RewriteRule :=
  Mettapedia.GSLT.LanguageDef.Examples.NativeNaturalCounter.language.rewrites[admission.index]

def Admission.left {branch : Branch} (admission : Admission branch) : Tower.Tm branch.arity :=
  (lowerPattern branch.environment admission.row.left).getD NativeNaturalVectorFamilies.zeroTm

def Admission.right {branch : Branch} (admission : Admission branch) : Tower.Tm branch.arity :=
  (lowerPattern branch.environment admission.row.right).getD NativeNaturalVectorFamilies.zeroTm

theorem Admission.lower_left {branch : Branch} (admission : Admission branch) :
    lowerPattern branch.environment admission.row.left = some branch.schema.left :=
  admission.accepted.2.2.2.2.2.2.2.1

theorem Admission.lower_right {branch : Branch} (admission : Admission branch) :
    lowerPattern branch.environment admission.row.right = some branch.schema.right :=
  admission.accepted.2.2.2.2.2.2.2.2

@[simp] theorem Admission.left_eq {branch : Branch} (admission : Admission branch) :
    admission.left = branch.schema.left := by
  simp [Admission.left, admission.lower_left]

@[simp] theorem Admission.right_eq {branch : Branch} (admission : Admission branch) :
    admission.right = branch.schema.right := by
  simp [Admission.right, admission.lower_right]

/-- The constructor linked by admission is already declared and strictly
positive in the existing candidate; no positivity test is inferred from an
untyped rewrite's operational success. -/
theorem Admission.constructor_declared {branch : Branch} (admission : Admission branch) :
    NativeNaturalVectorFamilies.rawSignature.typeOf? admission.constructor = some branch.constructor.type := by
  rw [admission.accepted.2.1]
  exact branch.constructor.declared

def constructor_positive (branch : Branch) :
    ConstructorType NativeNaturalVectorFamilies.natName 0 branch.constructor.type :=
  branch.constructor.positive

theorem Admission.eliminator_declared {branch : Branch} (admission : Admission branch) :
    NativeNaturalVectorFamilies.rawSignature.typeOf? admission.eliminator = some NativeNaturalVectorFamilies.natEliminatorSpec.type := by
  rw [admission.accepted.2.2.1]
  exact NativeNaturalVectorFamilies.natEliminatorSpec.declared

theorem constructor_in_candidate (branch : Branch) :
    branch.constructor ∈ NativeNaturalVectorFamilies.natCandidate.constructors := by
  cases branch with
  | zero => exact List.mem_cons_self
  | succ => exact List.mem_cons_of_mem _ List.mem_cons_self

private def substitutedInstance {scope : Nat} (branch : Branch)
    (context : Tower.Ctx scope) (substitution : Sub Tower.Head branch.arity scope)
    (typed : CtxMor NativeNaturalVectorFamilies.rules branch.schema.context context substitution) :
    NativeNaturalVectorFamilies.TypedIotaInstance context
      (subst substitution branch.schema.left) (subst substitution branch.schema.right)
      (subst substitution branch.schema.type) := by
  cases branch with
  | zero => exact .natZero ⟨substitution, typed, rfl, rfl, rfl⟩
  | succ => exact .natSucc ⟨substitution, typed, rfl, rfl, rfl⟩

/-- Reconstruct the exact typed schema instance at the original displayed type.
The only typing input is the existing context-morphism judgment. -/
def Admission.instantiate {scope : Nat} {branch : Branch} (admission : Admission branch)
    (context : Tower.Ctx scope) (substitution : Sub Tower.Head branch.arity scope)
    (typed : CtxMor NativeNaturalVectorFamilies.rules branch.schema.context context substitution)
    (displayedType : Tower.Tm scope)
    (adjustment : TypeAdjustment NativeNaturalVectorFamilies.rules (subst substitution branch.schema.type) displayedType) :
    NativeNaturalVectorFamilies.TypedIotaInstance.Adjusted context
      (subst substitution admission.left) (subst substitution admission.right) displayedType where
  principalType := subst substitution branch.schema.type
  principal := by
    simpa only [Admission.left_eq, Admission.right_eq] using
      substitutedInstance branch context substitution typed
  adjustment := adjustment

def Admission.typedReceipt {scope : Nat} {branch : Branch} (admission : Admission branch)
    (context : Tower.Ctx scope) (substitution : Sub Tower.Head branch.arity scope)
    (typed : CtxMor NativeNaturalVectorFamilies.rules branch.schema.context context substitution)
    (displayedType : Tower.Tm scope)
    (adjustment : TypeAdjustment NativeNaturalVectorFamilies.rules (subst substitution branch.schema.type) displayedType) :
    NativeNaturalVectorFamilies.TypedIotaReceipt context
      (subst substitution admission.left) (subst substitution admission.right) displayedType :=
  (admission.instantiate context substitution typed displayedType adjustment).toReceipt

theorem Admission.endpoints_typed {scope : Nat} {branch : Branch} (admission : Admission branch)
    (context : Tower.Ctx scope) (substitution : Sub Tower.Head branch.arity scope)
    (typed : CtxMor NativeNaturalVectorFamilies.rules branch.schema.context context substitution)
    (displayedType : Tower.Tm scope)
    (adjustment : TypeAdjustment NativeNaturalVectorFamilies.rules (subst substitution branch.schema.type) displayedType) :
    NativeNaturalVectorFamilies.HasType context (subst substitution admission.left) displayedType ∧
    NativeNaturalVectorFamilies.HasType context (subst substitution admission.right) displayedType :=
  let receipt := admission.typedReceipt context substitution typed displayedType adjustment
  ⟨receipt.sourceTyping, receipt.targetTyping⟩

/-- Computation is witnessed by the retained iota evidence, separately from
the typings at the displayed type. -/
theorem Admission.computation {scope : Nat} {branch : Branch} (admission : Admission branch)
    (context : Tower.Ctx scope) (substitution : Sub Tower.Head branch.arity scope)
    (typed : CtxMor NativeNaturalVectorFamilies.rules branch.schema.context context substitution)
    (displayedType : Tower.Tm scope)
    (adjustment : TypeAdjustment NativeNaturalVectorFamilies.rules
      (subst substitution branch.schema.type) displayedType) :
    NativeNaturalVectorFamilies.rawSignature.computation.step
      (subst substitution admission.left) (subst substitution admission.right) :=
  ⟨(admission.typedReceipt context substitution typed displayedType adjustment).evidence⟩

def zeroAdmission : Admission .zero where
  index := ⟨1, by decide +kernel⟩
  constructor := NativeNaturalVectorFamilies.zeroName
  eliminator := NativeNaturalVectorFamilies.natEliminateName
  accepted := by decide +kernel

def succAdmission : Admission .succ where
  index := ⟨2, by decide +kernel⟩
  constructor := NativeNaturalVectorFamilies.succName
  eliminator := NativeNaturalVectorFamilies.natEliminateName
  accepted := by decide +kernel

end Mettapedia.OSLF.Bridges.TypeTheory.AuthoredNaturalAdmission
