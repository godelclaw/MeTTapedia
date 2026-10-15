import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations
import Mettapedia.OSLF.NativeTypes.Generation.NativeLogicFragment
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalFormation
import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout

/-!
# One authored installation for dependent syntax and scoped execution

The generator retains the supplied presentation, provider snapshot and three
selection inputs. Native declaration installation and structural-recursion
admission are checked computationally. Operational receipts come from actual
retained matcher and premise work. Finite negative readouts require drained
work; an empty unfinished receipt list asserts no absence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open GeneralPremise
open Mettapedia.TypeTheory.Calculi.NativeDependent

structure Logic where
  observations : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment
  native : NativeLogic.Fragment

def plan (generated : Generated) : Plan := StructuralDescent.Plan.refine generated.plan

def environment (generated : Generated) : GeneralPremise.Environment :=
  GeneralPlanEnvironment.environment (plan generated)

inductive GenerationIssue where
  | constructorOrigins
  | nativeDeclaration
  | nativeMeaning (issues : List BindingSemanticAdmission.Issue)
  | constructorLabels
  | nativeModalDeclarations
  | operational (pending : List Obligation)
  | equations
  | structuralDescent
  | contextualSites
  deriving DecidableEq, Repr

structure Installed where
  authored : LanguageDef
  generated : Generated
  selectedTerms : (selectedConstructors authored generated.languageFragment).map Prod.fst =
    (plan generated).snapshot.language.terms
  logic : NativeLogic.Fragment
  declarations : NativeSignature.Installation (plan generated).snapshot.language
  nativeMeanings : BindingSemanticAdmission.check (plan generated).snapshot.language = true
  distinctLabels : ((plan generated).snapshot.language.terms.map (·.label)).Nodup
  modal : List (NativeModalHeaders.Header (plan generated))
  modalDecoded : NativeModalHeaders.decodeAll? (plan generated) = some modal
  operational : (plan generated).complete = true
  equationFree : (plan generated).equations = []
  structural : StructuralDescent.checkEnvironment (environment generated) = true
  rootRules : generated.languageFragment.operational.sites = GeneralTypedSites.OperationalPermissions.rootOnly

/-- Root rules and their authored recursive premises determine execution
contexts. Generic contextual closure is not silently added to a presentation. -/
def installGenerated (authored : LanguageDef) (generated : Generated) (logic : NativeLogic.Fragment) :
    Except GenerationIssue Installed := do
  if origins : (selectedConstructors authored generated.languageFragment).map Prod.fst =
      (plan generated).snapshot.language.terms then
    let declarations ← match NativeSignature.install? (plan generated).snapshot.language with
      | none => .error .nativeDeclaration
      | some installed => .ok installed
    if rootRules : generated.languageFragment.operational.sites = GeneralTypedSites.OperationalPermissions.rootOnly then
      if operational : (plan generated).complete = true then
        if equationFree : (plan generated).equations = [] then
          if structural : StructuralDescent.checkEnvironment (environment generated) = true then
            if meanings : BindingSemanticAdmission.check (plan generated).snapshot.language = true then
              if labels : ((plan generated).snapshot.language.terms.map (·.label)).Nodup then
                match modalDecoded : NativeModalHeaders.decodeAll? (plan generated) with
                | none => .error .nativeModalDeclarations
                | some modal => .ok ⟨authored, generated, origins, logic, declarations, meanings, labels, modal, modalDecoded,
                    operational, equationFree, structural, rootRules⟩
              else .error .constructorLabels
            else .error (.nativeMeaning (BindingSemanticAdmission.issues (plan generated).snapshot.language))
          else .error .structuralDescent
        else .error .equations
      else .error (.operational (plan generated).obligations)
    else .error .contextualSites
  else .error .constructorOrigins

def generate (snapshot : Snapshot) (language : LanguageFragment) (logic : Logic)
    (vertex : SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language) :
    Except GenerationIssue Installed :=
  installGenerated snapshot.language (Generation.generate snapshot language logic.observations vertex) logic.native

namespace Installed

variable (installed : Installed)

abbrev signature := NativeModalSignature.signature (plan installed.generated) installed.declarations installed.modal
abbrev symbols := NativeModalSignature.symbols (plan installed.generated) installed.declarations installed.modal

def formation : Refinement.HeaderFormation installed.signature :=
  NativeModalSignature.headers (plan installed.generated) installed.declarations installed.modal

def constructorDerivation {judgment : Refinement.Judgment installed.declarations.symbols}
    (tree : Refinement.Derivation installed.declarations.signature judgment) :
    Refinement.Derivation installed.signature (Refinement.SignatureSum.judgmentLeft judgment) :=
  NativeModalSignature.constructorDerivation (plan installed.generated) installed.declarations installed.modal tree

theorem nativeMeaning_admitted : BindingSemanticAdmission.Admitted (plan installed.generated).snapshot.language :=
  (BindingSemanticAdmission.check_exact _).mp installed.nativeMeanings

theorem modal_count : installed.modal.length = (schemas (plan installed.generated)).length :=
  NativeModalHeaders.decodeAll_length _ installed.modalDecoded

def check (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Refinement.Judgment installed.symbols) : NativeLogic.CheckResult :=
  NativeLogic.check installed.logic certificate judgment

theorem check_exact (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Refinement.Judgment installed.symbols) :
    installed.check certificate judgment = .accepted ↔
      installed.logic.permits judgment ∧ NativeLogic.CertificatePermitted installed.logic certificate ∧
        ∃ derivation : Refinement.Derivation installed.signature judgment,
          Certificates.Refinement.erase derivation = certificate := NativeLogic.check_exact _ _ _

abbrev Environment := environment installed.generated

structure Source where
  bound : List TypeExpr
  type : TypeExpr
  term : Pattern
  deriving Repr

abbrev ExecutionState (source : Source) :=
  StructuralDescent.Scheduled.Snapshot installed.Environment source.bound source.type source.term

def begin (source : Source) : installed.ExecutionState source :=
  StructuralDescent.Scheduled.begin installed.Environment source.bound source.type source.term

def resume (source : Source) (budget : Nat) (state : installed.ExecutionState source) :
    installed.ExecutionState source :=
  StructuralDescent.Scheduled.resume installed.Environment source.bound source.type source.term budget state

def receipts {source : Source} (state : installed.ExecutionState source) :=
  StructuralDescent.Scheduled.receipts state

def finish (source : Source) : installed.ExecutionState source :=
  StructuralDescent.Scheduled.finishSource installed.Environment source.bound source.type source.term

theorem resume_add (source : Source) (first second : Nat) (state : installed.ExecutionState source) :
    installed.resume source (first + second) state =
      installed.resume source second (installed.resume source first state) :=
  StructuralDescent.Scheduled.resume_add _ _ _ _ _ _ _

theorem receipts_preserved (source : Source) (fuel : Nat) (state : installed.ExecutionState source) :
    Scheduler.Prefix (installed.receipts state) (installed.receipts (installed.resume source fuel state)) :=
  StructuralDescent.Scheduled.receipts_preserved _ _ _ _ _ _

def HasSuccessor (source : Source) (target : Pattern) : Prop :=
  ∃ index trace captured completed history,
    GeneralPremise.RootFiring installed.Environment source.bound source.type source.term
      index trace captured completed history target

theorem receipt_sound (source : Source)
    (receipt : StructuralDescent.Execution.RootAnswer installed.Environment source.bound source.type source.term) :
    installed.HasSuccessor source receipt.target :=
  ⟨receipt.index, receipt.trace, receipt.captured, receipt.completed, receipt.history, receipt.valid⟩

theorem drained_successors (source : Source) (budget : Nat)
    (drained : (installed.resume source budget (installed.begin source)).agenda = []) (target : Pattern) :
    target ∈ (installed.receipts (installed.resume source budget (installed.begin source))).map (·.target) ↔
      installed.HasSuccessor source target := by
  constructor
  · intro found
    obtain ⟨receipt, _, equal⟩ := List.mem_map.mp found
    cases equal
    exact installed.receipt_sound source receipt
  · rintro ⟨index, trace, captured, completed, history, valid⟩
    let receipt : StructuralDescent.Execution.RootAnswer installed.Environment source.bound source.type source.term :=
      ⟨index, trace, captured, completed, history, target, valid⟩
    have covered := StructuralDescent.Scheduled.drained_receipts_complete installed.Environment
      installed.structural source.bound source.type source.term budget drained receipt
    exact List.mem_map.mpr ⟨receipt, covered, rfl⟩

inductive Answer where
  | proved
  | refuted
  | unknown
  deriving DecidableEq, Repr

/-- Positive possibilities may stop as soon as a matching receipt is emitted.
Negative possibilities require complete actual pending work. -/
def possibility (source : Source) (predicate : Pattern → Bool)
    (state : installed.ExecutionState source) : Answer :=
  if (installed.receipts state).any (fun receipt => predicate receipt.target) then .proved
  else if Scheduler.complete state then .refuted else .unknown

/-- This is the outgoing universal, not OSLF's incoming adjoint box. -/
def outgoingAll (source : Source) (predicate : Pattern → Bool)
    (state : installed.ExecutionState source) : Answer :=
  if (installed.receipts state).any (fun receipt => !predicate receipt.target) then .refuted
  else if Scheduler.complete state then .proved else .unknown

end Installed

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline
