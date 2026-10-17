import Mettapedia.OSLF.Syntax.RhoScopedInstanceReadout
import Mettapedia.OSLF.Syntax.BindingEqualityWire
import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

/-!
# Independent services for the intrinsic scoped rho source

Terms, contexts and binding spines are those of RhoSchema.sig. Equality is
original EqClosure rhoSourceE: parallel ACU and name QuoteDrop. Directed
COMM and process Drop keep their original quotient-event observer and
parallel-only evaluation contexts. No target type calculus is imported.

This source profile is distinct from the raw Pattern 33-rule kernel.
The optional declared-calculus comparison has a twelve-rule tree presentation
of this source equality. Source equality here reuses the original generic
binding-equality certificates rather than relabelling their constructors
as twelve primitive rho rules. Substitution replay and physical
execution costs retain their own qualification boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices

open Mettapedia.OSLF.Binding RhoSchema
open Mettapedia.OSLF.Binding.RhoScopedInstanceReadout
open Mettapedia.OSLF.Binding.RhoIntrinsicReadback
open Mettapedia.OSLF.Binding.RhoQuotationClassFibres
open Mettapedia.OSLF.Binding.RhoScopedParallelPathReadout
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef KernelAuthority SemanticEvidence

private instance (sort : Srt) : DecidableEq (Op sort) := by
  intro first second
  cases first <;> cases second
  all_goals first | exact isTrue rfl | exact isFalse (by intro same; cases same)

private def putSort : Srt → Nat | .nm => 0 | .pr => 1
private def getSort : Nat → Option Srt | 0 => some .nm | 1 => some .pr | _ => none

def sorts : Codec Srt := Codec.nat.mapped putSort getSort (fun sort => by cases sort <;> rfl)

private def putOperator : (Σ sort : Srt, Op sort) → Nat
  | ⟨_, .nil⟩ => 0 | ⟨_, .par⟩ => 1 | ⟨_, .out⟩ => 2
  | ⟨_, .inp⟩ => 3 | ⟨_, .quo⟩ => 4 | ⟨_, .drp⟩ => 5

private def getOperator : Nat → Option (Σ sort : Srt, Op sort)
  | 0 => some ⟨.pr, .nil⟩ | 1 => some ⟨.pr, .par⟩ | 2 => some ⟨.pr, .out⟩
  | 3 => some ⟨.pr, .inp⟩ | 4 => some ⟨.nm, .quo⟩ | 5 => some ⟨.pr, .drp⟩ | _ => none

def operators : Codec (Σ sort : Srt, Op sort) :=
  Codec.nat.mapped putOperator getOperator (fun ⟨_, operator⟩ => by cases operator <;> rfl)

def sourceTerm (context : Ctx sig) (sort : Srt) : Codec (Term sig context sort) :=
  WireCodec.term operators context sort

def equality (context : Ctx sig) (sort : Srt) :=
  EqualityCertificates.Wire.certificate sorts operators rhoSourceE context sort

def checkEquation {context : Ctx sig} {sort : Srt} (raw : Data)
    (first second : Term sig context sort) : Bool :=
  EqualityCertificates.Wire.check sorts operators rhoSourceE raw first second

theorem checkEquation_sound {context : Ctx sig} {sort : Srt} (raw : Data)
    (first second : Term sig context sort) (accepted : checkEquation raw first second = true) :
    EqClosure rhoSourceE first second := by
  change EqualityCertificates.Wire.check (S := sig) sorts operators rhoSourceE raw first second = true at accepted
  exact EqualityCertificates.Wire.check_sound (S := sig) sorts operators rhoSourceE raw first second accepted

theorem checkEquation_complete {context : Ctx sig} {sort : Srt}
    (first second : Term sig context sort) :
    EqClosure rhoSourceE first second ↔ ∃ raw : Data, checkEquation raw first second = true := by
  change EqClosure rhoSourceE first second ↔ ∃ raw : Data,
    EqualityCertificates.Wire.check (S := sig) sorts operators rhoSourceE raw first second = true
  exact EqualityCertificates.Wire.check_complete (S := sig) sorts operators rhoSourceE first second

abbrev SourceStep {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Mettapedia.OSLF.Binding.Term sig context Srt.pr) :=
  Mettapedia.OSLF.Binding.RhoScopedParallelEvents.Step
    (rules := Mettapedia.OSLF.Binding.RhoScopedParallelEvents.sourceRules)
    (admitted := Mettapedia.OSLF.Binding.RhoScopedParallelEvents.withReflection)
    (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project first)
    (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project second)

theorem source_root_step {context : Mettapedia.OSLF.Binding.Ctx sig}
    (root : Mettapedia.OSLF.Binding.RhoScopedParallelEvents.Root
      Mettapedia.OSLF.Binding.RhoScopedParallelEvents.sourceRules
      Mettapedia.OSLF.Binding.RhoScopedParallelEvents.withReflection context) :
    SourceStep root.2.source root.2.target := by
  apply (Mettapedia.OSLF.Binding.RhoScopedParallelEvents.step_iff_root_surrounding _ _).mpr
  exact ⟨root, zero context, (join_zero_right _).symm, (join_zero_right _).symm⟩

theorem communication_source_step {context : Mettapedia.OSLF.Binding.Ctx sig}
    (channel : Mettapedia.OSLF.Binding.Term sig context Srt.nm)
    (payload : Mettapedia.OSLF.Binding.Term sig context Srt.pr)
    (body : Mettapedia.OSLF.Binding.Term sig (Srt.nm :: context) Srt.pr) :
    SourceStep
      (.op .par (.cons (.op .out (.cons channel (.cons payload .nil)))
        (.cons (.op .inp (.cons channel (.cons body .nil))) .nil)))
      (Mettapedia.OSLF.Binding.bind (receiveRaw (quoteRaw payload)) body) := by
  let root := communication channel payload body
  have step := source_root_step ⟨⟨.communication, trivial⟩, root⟩
  change SourceStep (root.source : Mettapedia.OSLF.Binding.Term sig context Srt.pr)
    (root.target : Mettapedia.OSLF.Binding.Term sig context Srt.pr) at step
  rw [Communication.source_readout root, Communication.target_readout root] at step
  simpa only [root, communication_channel, communication_payload, communication_continuation,
    Mettapedia.OSLF.Binding.RhoEquationConstructorControls.parallel,
    Mettapedia.OSLF.Binding.RhoIntrinsicReadback.outputRaw,
    Mettapedia.OSLF.Binding.RhoIntrinsicReadback.inputRaw] using step

theorem reflection_source_step {context : Mettapedia.OSLF.Binding.Ctx sig}
    (payload : Mettapedia.OSLF.Binding.Term sig context Srt.pr) :
    SourceStep (.op .drp (.cons (.op .quo (.cons payload .nil)) .nil)) payload := by
  exact source_root_step ⟨⟨.reflection, trivial⟩, reflection payload (.op .nil .nil)⟩


theorem source_parallel_left {context : Mettapedia.OSLF.Binding.Ctx sig}
    {first second : Mettapedia.OSLF.Binding.Term sig context Srt.pr}
    (step : SourceStep first second)
    (other : Mettapedia.OSLF.Binding.Term sig context Srt.pr) :
    SourceStep (.op .par (.cons first (.cons other .nil)))
      (.op .par (.cons second (.cons other .nil))) := by
  exact Mettapedia.OSLF.Binding.RhoScopedParallelEvents.step_join step
    (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project other)

theorem source_parallel_right {context : Mettapedia.OSLF.Binding.Ctx sig}
    {first second : Mettapedia.OSLF.Binding.Term sig context Srt.pr}
    (step : SourceStep first second)
    (other : Mettapedia.OSLF.Binding.Term sig context Srt.pr) :
    SourceStep (.op .par (.cons other (.cons first .nil)))
      (.op .par (.cons other (.cons second .nil))) := by
  have under := source_parallel_left step other
  change Mettapedia.OSLF.Binding.RhoScopedParallelEvents.Step
    (rules := Mettapedia.OSLF.Binding.RhoScopedParallelEvents.sourceRules)
    (admitted := Mettapedia.OSLF.Binding.RhoScopedParallelEvents.withReflection)
    (join (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project other)
      (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project first))
    (join (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project other)
      (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project second))
  rw [Mettapedia.OSLF.Binding.RhoQuotationClassFibres.join_commutes
    (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project other),
    Mettapedia.OSLF.Binding.RhoQuotationClassFibres.join_commutes
      (Mettapedia.OSLF.Binding.RhoEquationConstructorControls.project other)]
  exact under


/-- Only an input on the literal output channel is a selected COMM root. -/
private def communicationResult? {context : Ctx sig}
    (channel : Term sig context .nm) (payload : Term sig context .pr) :
    (input : Term sig context .pr) → Option {target : Term sig context .pr //
      SourceStep (.op .par (.cons (.op .out (.cons channel (.cons payload .nil)))
        (.cons input .nil))) target}
  | .var _ => none
  | .op .nil .nil => none
  | .op .par (.cons _ (.cons _ .nil)) => none
  | .op .out (.cons _ (.cons _ .nil)) => none
  | .op .inp (.cons other (.cons body .nil)) =>
      if same : channel = other then by
        subst other
        exact some ⟨bind (receiveRaw (quoteRaw payload)) body, communication_source_step channel payload body⟩
      else none
  | .op .drp (.cons _ .nil) => none

/-- One selected source root performs the original received-name substitution.
The proof is constructed from the existing source rule and erased at execution. -/
private def rootResult? {context : Ctx sig} : (source : Term sig context .pr) →
    Option {target : Term sig context .pr // SourceStep source target}
  | .var _ => none
  | .op .nil .nil => none
  | .op .par (.cons left (.cons right .nil)) => match left with
    | .var _ => none
    | .op .nil .nil => none
    | .op .par (.cons _ (.cons _ .nil)) => none
    | .op .out (.cons channel (.cons payload .nil)) => communicationResult? channel payload right
    | .op .inp (.cons _ (.cons _ .nil)) => none
    | .op .drp (.cons _ .nil) => none
  | .op .out (.cons _ (.cons _ .nil)) => none
  | .op .inp (.cons _ (.cons _ .nil)) => none
  | .op .drp (.cons name .nil) => match name with
    | .var _ => none
    | .op .quo (.cons payload .nil) => some ⟨payload, reflection_source_step payload⟩

def root? {context : Ctx sig} (source : Term sig context .pr) : Option (Term sig context .pr) :=
  (rootResult? source).map Subtype.val

theorem root?_sound {context : Ctx sig} (source target : Term sig context .pr)
    (accepted : root? source = some target) : SourceStep source target := by
  obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp accepted
  exact same ▸ result.property

/-- Addresses select only source parallel children. No source computation
context enters an input, output, drop or quotation. -/
private def executeResult? {context : Ctx sig} (source : Term sig context .pr) :
    List Bool → Option {target : Term sig context .pr // SourceStep source target}
  | [] => rootResult? source
  | first :: rest => match source with
    | .var _ => none
    | .op .nil .nil => none
    | .op .par (.cons left (.cons right .nil)) =>
      if first then do
        let result ← executeResult? right rest
        some ⟨.op .par (.cons left (.cons result.val .nil)), source_parallel_right result.property left⟩
      else do
        let result ← executeResult? left rest
        some ⟨.op .par (.cons result.val (.cons right .nil)), source_parallel_left result.property right⟩
    | .op .out (.cons _ (.cons _ .nil)) => none
    | .op .inp (.cons _ (.cons _ .nil)) => none
    | .op .drp (.cons _ .nil) => none

def execute? {context : Ctx sig} (source : Term sig context .pr) (address : List Bool) :
    Option (Term sig context .pr) := (executeResult? source address).map Subtype.val

theorem execute?_sound {context : Ctx sig} (source target : Term sig context .pr) (address : List Bool)
    (accepted : execute? source address = some target) : SourceStep source target := by
  obtain ⟨result, _, same⟩ := Option.map_eq_some_iff.mp accepted
  exact same ▸ result.property

theorem root?_instance {context : Ctx sig}
    (root : RhoScopedParallelEvents.Root RhoScopedParallelEvents.sourceRules
      RhoScopedParallelEvents.withReflection context) :
    root? root.2.source = some root.2.target := by
  rcases root with ⟨⟨index, admitted⟩, firing⟩
  cases index with
  | communication =>
    change Communication context at firing
    change root? firing.source = some firing.target
    rw [Communication.source_readout firing, Communication.target_readout firing]
    simp only [root?, rootResult?, communicationResult?, RhoEquationConstructorControls.parallel, outputRaw, inputRaw,
      dite_true, Option.map_some]
    rfl
  | reflection =>
    change Reflection context at firing
    change root? firing.source = some firing.target
    rw [Reflection.source_readout firing, Reflection.target_readout firing]
    rfl

theorem execute?_parallel_left {context : Ctx sig}
    (first second : Term sig context .pr) (address : List Bool) :
    execute? (.op .par (.cons first (.cons second .nil))) (false :: address) =
      (execute? first address).map (fun result => .op .par (.cons result (.cons second .nil))) := by
  simp only [execute?, executeResult?, Bool.false_eq_true, ↓reduceIte, Bind.bind, Option.bind]
  cases executeResult? first address <;> rfl

def checkExecution {context : Ctx sig} (source target : Term sig context .pr) (address : List Bool) : Bool :=
  match execute? source address with | none => false | some result => decide (result = target)

theorem checkExecution_exact {context : Ctx sig} (source target : Term sig context .pr) (address : List Bool) :
    checkExecution source target address = true ↔ execute? source address = some target := by
  cases computed : execute? source address <;> simp [checkExecution, computed]

/-- Equation witnesses retain the original source observation; the selected
computation stays directed and uses only original parallel contexts. -/
structure StepEvidence (context : Ctx sig) where
  before : Term sig context .pr
  after : Term sig context .pr
  address : List Bool
  beforeEquation : Data
  afterEquation : Data

def checkStep {context : Ctx sig} (source target : Term sig context .pr) (evidence : StepEvidence context) : Bool :=
  checkEquation evidence.beforeEquation source evidence.before &&
    checkExecution evidence.before evidence.after evidence.address &&
    checkEquation evidence.afterEquation evidence.after target

theorem checkStep_sound {context : Ctx sig} (source target : Term sig context .pr)
    (evidence : StepEvidence context) (accepted : checkStep source target evidence = true) :
    SourceStep source target := by
  simp only [checkStep, Bool.and_eq_true] at accepted
  have beforeEq := checkEquation_sound _ _ _ accepted.1.1
  have core := execute?_sound evidence.before evidence.after evidence.address
    ((checkExecution_exact _ _ _).mp accepted.1.2)
  have afterEq := checkEquation_sound _ _ _ accepted.2
  have sourceAt : RhoEquationConstructorControls.project source =
      RhoEquationConstructorControls.project evidence.before := Quotient.sound beforeEq
  have targetAt : RhoEquationConstructorControls.project evidence.after =
      RhoEquationConstructorControls.project target := Quotient.sound afterEq
  change RhoScopedParallelEvents.Step
    (rules := RhoScopedParallelEvents.sourceRules) (admitted := RhoScopedParallelEvents.withReflection) _ _
  rw [sourceAt, ← targetAt]
  exact core

theorem checkStep_complete {context : Ctx sig} (source target : Term sig context .pr) :
    SourceStep source target ↔ ∃ evidence : StepEvidence context, checkStep source target evidence = true := by
  constructor
  · intro held
    obtain ⟨root, surrounding, sourceAt, targetAt⟩ :=
      (RhoScopedParallelEvents.step_iff_root_surrounding _ _).mp held
    obtain ⟨surrounding, rfl⟩ := Quotient.exists_rep surrounding
    let rootSource : Term sig context .pr := root.2.source
    let rootTarget : Term sig context .pr := root.2.target
    have rootFires : root? rootSource = some rootTarget := root?_instance root
    let before := RhoEquationConstructorControls.parallel rootSource surrounding
    let after := RhoEquationConstructorControls.parallel rootTarget surrounding
    have first : EqClosure rhoSourceE source before := Quotient.exact sourceAt
    have last : EqClosure rhoSourceE after target := Quotient.exact targetAt.symm
    obtain ⟨beforeProof, beforeChecked⟩ := (checkEquation_complete source before).mp first
    obtain ⟨afterProof, afterChecked⟩ := (checkEquation_complete after target).mp last
    have execution : execute? before [false] = some after := by
      change execute? (.op .par (.cons rootSource (.cons surrounding .nil))) (false :: []) = some after
      rw [execute?_parallel_left]
      change (root? rootSource).map _ = some after
      rw [rootFires]
      rfl
    refine ⟨⟨before, after, [false], beforeProof, afterProof⟩, ?_⟩
    simp only [checkStep, beforeChecked, afterChecked,
      (checkExecution_exact before after [false]).mpr execution, Bool.and_self]
  · rintro ⟨evidence, accepted⟩
    exact checkStep_sound source target evidence accepted

def equationTarget (context : Ctx sig) (sort : Srt) : AdmissionObject where
  Carrier := Term sig context sort × Term sig context sort
  Meaning claim := EqClosure rhoSourceE claim.1 claim.2

def equationChecker (context : Ctx sig) (sort : Srt) : Checker (Term sig context sort × Term sig context sort) Data :=
  ⟨fun claim evidence => checkEquation evidence claim.1 claim.2⟩

theorem equationAuthority (context : Ctx sig) (sort : Srt) :
    (equationChecker context sort).Authority (equationTarget context sort).Meaning where
  sound claim evidence accepted := checkEquation_sound evidence claim.1 claim.2 accepted
  complete claim meaningful := (checkEquation_complete claim.1 claim.2).mp meaningful

def equationService (context : Ctx sig) (sort : Srt) : SemanticService.Service (equationTarget context sort) :=
  .certificateBoundary Data (equationChecker context sort) (equationAuthority context sort)

def stepTarget (context : Ctx sig) : AdmissionObject where
  Carrier := Term sig context .pr × Term sig context .pr
  Meaning claim := SourceStep claim.1 claim.2

def stepChecker (context : Ctx sig) : Checker (Term sig context .pr × Term sig context .pr) (StepEvidence context) :=
  ⟨fun claim evidence => checkStep claim.1 claim.2 evidence⟩

theorem stepAuthority (context : Ctx sig) : (stepChecker context).Authority (stepTarget context).Meaning where
  sound claim evidence accepted := checkStep_sound claim.1 claim.2 evidence accepted
  complete claim meaningful := (checkStep_complete claim.1 claim.2).mp meaningful

def stepService (context : Ctx sig) : SemanticService.Service (stepTarget context) :=
  .certificateBoundary (StepEvidence context) (stepChecker context) (stepAuthority context)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedNativeServices
