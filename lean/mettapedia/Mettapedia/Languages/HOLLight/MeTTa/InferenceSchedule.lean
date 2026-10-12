import Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory
import Mettapedia.Languages.HOLLight.MeTTa.SourceReplay

/-!
# All primitive inference invocations share the actual source-event boundary

An invocation contains source operands, cache selections and the primitive
rule's side conditions. It contains no assumed result derivation or cache
preservation interface. The execution theorem constructs both from the
existing rule-specific authored execution laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.InferenceSchedule

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization Eval
open Effects (State)

/-- A fixed registered source context. Definition extensions require their
own transport; they are not silently identified with this fixed-context frame. -/
structure Frame where
  policy : AxiomPolicy
  world : TheoryContext
  table : DeclarationTable.Table world
  origins : TypeOp → Atom
  constants : Const → Atom
  identified : DeclarationTable.Identifies world constants
  equalityIdentity : constants Const.equality = DeclarationTable.primitiveIdentity Const.equality
  functionArity : world.signature.typeOperators TypeOp.function = some 2
  equalityParameter : Name
  equalityRegistered : world.signature.constants Const.equality = some (Ty.equality (.var equalityParameter))
  booleanFormed : TypeFormed world.signature Ty.bool
  axioms : Atom

def Frame.operators (frame : Frame) : Atom := OperatorTable.tableAtom frame.table.operators frame.origins
def Frame.declarations (frame : Frame) : Atom := DeclarationTable.tableAtom frame.table frame.constants
def Frame.source (frame : Frame) (cache : Cache) (receipts : List ReceiptKeys.Entry) : Atom :=
  ProofLookup.sourceState frame.operators frame.declarations frame.axioms
    (ReceiptKeys.table receipts) (entries frame.constants cache)

/-- Admission records actual cache addresses and exact primitive side
conditions. Logical authority is subsequently earned by execution. -/
inductive Invocation (frame : Frame) (cache : Cache) : Type
  | refl (source : CheckedSourceTerm)
      (resolved : TermReading.SourceResolved frame.world.signature source.source)
      (annotations : AnnotationsFormed frame.world.signature source.canonical.term)
      (equalityType : TypeFormed frame.world.signature (Ty.equality source.ty))
      (equalityInstance : ConstantInstance frame.world.signature Const.equality (Ty.equality source.ty))
  | assume (source : CheckedSourceTerm)
      (resolved : TermReading.SourceResolved frame.world.signature source.source)
      (annotations : AnnotationsFormed frame.world.signature source.canonical.term)
      (formed : TypeFormed frame.world.signature source.ty) (isBool : source.canonical.IsBool)
  | beta (needle : SourceVar) (body : CheckedSourceTerm)
      (resolved : TermReading.SourceResolved frame.world.signature (Beta.redex needle body.source))
      (annotations : AnnotationsFormed frame.world.signature ((Beta.redex needle body.source).toDB []))
  | trans (first second : Atom) (left right : Record)
      (firstSelected : cache.lookup first = some left) (secondSelected : cache.lookup second = some right)
      (initial middle final : CanonicalTerm)
      (leftView : CanonicalTerm.EqualityViewSemantics left.conclusion initial middle)
      (rightView : CanonicalTerm.EqualityViewSemantics right.conclusion middle final)
  | mkComb (first second : Atom) (functions arguments : Record)
      (firstSelected : cache.lookup first = some functions) (secondSelected : cache.lookup second = some arguments)
      (functionLeft functionRight argumentLeft argumentRight : CanonicalTerm) (domain codomain : Ty)
      (functionView : CanonicalTerm.EqualityViewSemantics functions.conclusion functionLeft functionRight)
      (argumentView : CanonicalTerm.EqualityViewSemantics arguments.conclusion argumentLeft argumentRight)
      (functionType : functionLeft.ty = .function domain codomain) (argumentType : argumentLeft.ty = domain)
  | eqMp (first second : Atom) (equality premise : Record)
      (firstSelected : cache.lookup first = some equality) (secondSelected : cache.lookup second = some premise)
      (target : CanonicalTerm)
      (view : CanonicalTerm.EqualityViewSemantics equality.conclusion premise.conclusion target)
  | deduct (first second : Atom) (left right : Record)
      (firstSelected : cache.lookup first = some left) (secondSelected : cache.lookup second = some right)
  | abs (needle : SourceVar) (input : Atom) (premise : Record)
      (needleFormed : TypeFormed frame.world.signature needle.ty)
      (resolved : TermReading.SourceResolved frame.world.signature (.var needle.name needle.ty))
      (selected : cache.lookup input = some premise) (left right : CanonicalTerm)
      (view : CanonicalTerm.EqualityViewSemantics premise.conclusion left right)
      (fresh : ¬ FreeInHypotheses needle premise.fact.sequent.hyp)
  | instType (maplets : List (Ty × Ty)) (input : Atom) (premise : Record)
      (resolved : ∀ entry ∈ maplets, TypeFormation.Resolved frame.world.signature entry.1 ∧
        TypeFormation.Resolved frame.world.signature entry.2)
      (formed : ∀ entry ∈ maplets, TypeFormed frame.world.signature entry.1 ∧
        TypeFormed frame.world.signature entry.2)
      (selected : cache.lookup input = some premise)
  | inst (maplets : List TermMapletReading.Entry) (input : Atom) (premise : Record)
      (admitted : TermMapletReading.admittedB maplets = true)
      (formed : ∀ entry ∈ maplets, TermMapletReading.EntryFormed frame.world.signature entry)
      (selected : cache.lookup input = some premise)

def Invocation.kind {frame : Frame} {cache : Cache} : Invocation frame cache → InferenceKind
  | .refl .. => .refl
  | .assume .. => .assume
  | .beta .. => .beta
  | .trans .. => .trans
  | .mkComb .. => .mkComb
  | .eqMp .. => .eqMp
  | .deduct .. => .deductAntisym
  | .abs .. => .abs
  | .instType .. => .instType
  | .inst .. => .inst

def Invocation.payload {frame : Frame} {cache : Cache} : Invocation frame cache → Atom
  | .refl source .. => TermReading.sourceAtom source.source
  | .assume source .. => TermReading.sourceAtom source.source
  | .beta needle body .. => TermReading.sourceAtom (Beta.redex needle body.source)
  | .trans .. => .symbol "None"
  | .mkComb .. => .symbol "None"
  | .eqMp .. => .symbol "None"
  | .deduct .. => .symbol "None"
  | .abs needle .. => TermReading.sourceAtom (.var needle.name needle.ty)
  | .instType maplets .. => TypeSubstitution.maplets Representation.registeredOperatorAtom maplets
  | .inst maplets .. => TermMapletReading.sourceAtom maplets

def Invocation.first {frame : Frame} {cache : Cache} : Invocation frame cache → Atom
  | .refl .. => .symbol "None"
  | .assume .. => .symbol "None"
  | .beta .. => .symbol "None"
  | .trans first .. => first
  | .mkComb first .. => first
  | .eqMp first .. => first
  | .deduct first .. => first
  | .abs _ input .. => input
  | .instType _ input .. => input
  | .inst _ input .. => input

def Invocation.second {frame : Frame} {cache : Cache} : Invocation frame cache → Atom
  | .refl .. => .symbol "None"
  | .assume .. => .symbol "None"
  | .beta .. => .symbol "None"
  | .trans _ second .. => second
  | .mkComb _ second .. => second
  | .eqMp _ second .. => second
  | .deduct _ second .. => second
  | .abs .. => .symbol "None"
  | .instType .. => .symbol "None"
  | .inst .. => .symbol "None"

def Invocation.request {frame : Frame} {cache : Cache} (invocation : Invocation frame cache) : Atom :=
  Premises.request invocation.kind invocation.payload invocation.first invocation.second

def Invocation.occurrences {frame : Frame} {cache : Cache} (invocation : Invocation frame cache) : List Atom :=
  Premises.occurrences invocation.kind invocation.first invocation.second

def Invocation.receipt {frame : Frame} {cache : Cache} (invocation : Invocation frame cache)
    (key : Atom) : ReceiptKeys.Entry := ⟨key, invocation.request, invocation.occurrences⟩

def Invocation.command {frame : Frame} {cache : Cache} (invocation : Invocation frame cache)
    (key : Atom) : SourceReplay.Command := ⟨key, invocation.request⟩

/-- The rule's independent logical result relation, using the existing
calculus. The source origin and ordered metadata remain in the full record. -/
def Invocation.LogicalResult {frame : Frame} {cache : Cache}
    (invocation : Invocation frame cache) (next : Record) : Prop :=
  match invocation with
  | .refl source .. => InferenceRequest.Semantics (.refl source.canonical) next.fact
  | .assume source .. => InferenceRequest.Semantics (.assume source.canonical) next.fact
  | .beta needle body .. => ∃ source : CheckedSourceTerm,
      source.source = Beta.redex needle body.source ∧ InferenceRequest.Semantics (.beta source) next.fact
  | .trans _ _ left right .. => InferenceRequest.Semantics (.trans left.fact right.fact) next.fact
  | .mkComb _ _ functions arguments .. => InferenceRequest.Semantics (.mkComb functions.fact arguments.fact) next.fact
  | .eqMp _ _ equality premise .. => InferenceRequest.Semantics (.eqMp equality.fact premise.fact) next.fact
  | .deduct _ _ left right .. => InferenceRequest.Semantics (.deductAntisym left.fact right.fact) next.fact
  | .abs needle _ premise .. => InferenceRequest.Semantics (.abs needle premise.fact) next.fact
  | .instType maplets _ premise .. => InferenceRequest.Semantics (.instType maplets premise.fact) next.fact
  | .inst maplets _ premise .. =>
      InferenceRequest.Semantics (.inst (TermMapletReading.sourceEntries maplets) premise.fact) next.fact

/-- Every primitive invocation constructs the authorized result by executing
the quoted source dispatcher and publisher, in the same registered calculus. -/
theorem executes (frame : Frame) (cache : Cache) (valid : Valid frame.policy frame.world cache)
    (receipts : List ReceiptKeys.Entry) (key : Atom) (invocation : Invocation frame cache)
    (receiptFresh : ReceiptKeys.presentB key receipts = false)
    (cacheFresh : (entries frame.constants cache).lookup key = none) (state : State) :
    ∃ next : Record, TheoryDerives frame.policy frame.world next.fact ∧
      Valid frame.policy frame.world ((key, next) :: cache) ∧
      invocation.LogicalResult next ∧
      PureReturns program (SourceReplay.stepEnvironment (frame.source cache receipts) (invocation.command key))
        state (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"]) state
        (.expression [.symbol "Some", frame.source ((key, next) :: cache) (invocation.receipt key :: receipts)]) := by
  let bindings := SourceReplay.stepEnvironment (frame.source cache receipts) (invocation.command key)
  cases invocation with
  | refl source resolved annotations equalityType equalityInstance =>
      obtain ⟨next, derived, retained, _, _, _, semantics, returned⟩ :=
        authored_refl_preserves_valid frame.policy frame.world frame.table frame.origins frame.constants
          frame.equalityIdentity source resolved annotations equalityType equalityInstance cache valid receipts
          key frame.axioms receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source, Frame.operators, Frame.declarations] using returned⟩
  | assume source resolved annotations formed isBool =>
      obtain ⟨next, derived, retained, _, _, _, semantics, returned⟩ :=
        authored_assume_preserves_valid frame.policy frame.world frame.table frame.origins frame.constants
          source resolved annotations formed frame.booleanFormed isBool cache valid receipts key frame.axioms
          receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source, Frame.operators, Frame.declarations] using returned⟩
  | beta needle body resolved annotations =>
      obtain ⟨source, next, sourceSame, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_beta_preserves_valid frame.policy frame.world frame.table frame.origins
          frame.constants frame.equalityIdentity frame.functionArity frame.equalityParameter frame.equalityRegistered
          frame.booleanFormed needle body resolved annotations cache valid receipts key frame.axioms
          receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, ⟨source, sourceSame, semantics⟩, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source, Frame.operators, Frame.declarations] using returned⟩
  | trans first second left right firstSelected secondSelected initial middle final leftView rightView =>
      obtain ⟨next, _, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_trans_preserves_valid frame.policy frame.world frame.constants frame.identified
          frame.equalityIdentity cache valid left right first second firstSelected secondSelected initial middle final
          leftView rightView receipts frame.operators frame.declarations frame.axioms key receiptFresh cacheFresh
          bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source] using returned⟩
  | mkComb first second functions arguments firstSelected secondSelected functionLeft functionRight
      argumentLeft argumentRight domain codomain functionView argumentView functionType argumentType =>
      obtain ⟨next, _, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_mk_comb_preserves_valid frame.policy frame.world frame.constants frame.identified
          frame.equalityIdentity frame.functionArity frame.equalityParameter frame.equalityRegistered
          cache valid functions arguments first second firstSelected secondSelected functionLeft functionRight
          argumentLeft argumentRight domain codomain functionView argumentView functionType argumentType
          receipts frame.operators frame.declarations frame.axioms key receiptFresh cacheFresh bindings state
          "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source] using returned⟩
  | eqMp first second equality premise firstSelected secondSelected target view =>
      obtain ⟨next, _, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_eq_mp_preserves_valid frame.policy frame.world frame.constants frame.identified
          frame.equalityIdentity frame.functionArity cache valid equality premise first second firstSelected
          secondSelected target view receipts frame.operators frame.declarations frame.axioms key receiptFresh
          cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source] using returned⟩
  | deduct first second left right firstSelected secondSelected =>
      obtain ⟨next, _, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_deduct_preserves_valid frame.policy frame.world frame.constants frame.identified
          frame.equalityIdentity frame.functionArity frame.equalityParameter frame.equalityRegistered
          cache valid left right first second firstSelected secondSelected receipts frame.operators
          frame.declarations frame.axioms key receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source] using returned⟩
  | abs needle input premise needleFormed resolved selected left right view fresh =>
      obtain ⟨next, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_abs_preserves_valid frame.policy frame.world frame.table frame.origins
          frame.constants frame.equalityIdentity frame.functionArity frame.equalityParameter frame.equalityRegistered
          needle needleFormed resolved cache valid premise input selected left right view fresh receipts key
          frame.axioms receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source, Frame.operators, Frame.declarations] using returned⟩
  | instType maplets input premise resolved formed selected =>
      obtain ⟨next, _, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_inst_type_preserves_valid frame.policy frame.world frame.table frame.origins
          frame.constants frame.identified maplets resolved formed cache valid premise input selected
          receipts key frame.axioms receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source, Frame.operators, Frame.declarations] using returned⟩
  | inst maplets input premise admitted formed selected =>
      obtain ⟨next, _, _, _, _, semantics, derived, retained, returned⟩ :=
        InferenceHistory.authored_inst_preserves_valid frame.policy frame.world frame.table frame.origins
          frame.constants frame.identified maplets admitted formed cache valid premise input selected receipts
          key frame.axioms receiptFresh cacheFresh bindings state "state" "key" "request" rfl rfl rfl
      exact ⟨next, derived, retained, semantics, by simpa [bindings, Invocation.receipt, Invocation.command, Invocation.request,
        Invocation.kind, Invocation.payload, Invocation.first, Invocation.second, Invocation.occurrences,
        Premises.request, Premises.occurrences, Frame.source, Frame.operators, Frame.declarations] using returned⟩

/-- A finite admitted plan can use the result of an earlier event. Its
continuation receives the result relation proved by the primitive execution;
it does not supply the derivation invariant used by the next event. This is
an authoring interface for admitted histories, not a raw-closure validator. -/
inductive Plan (frame : Frame) : Cache → List ReceiptKeys.Entry → Nat → Type
  | stop (cache : Cache) (receipts : List ReceiptKeys.Entry) : Plan frame cache receipts 0
  | event {cache : Cache} {receipts : List ReceiptKeys.Entry} {length : Nat}
      (key : Atom) (invocation : Invocation frame cache)
      (receiptFresh : ReceiptKeys.presentB key receipts = false)
      (cacheFresh : (entries frame.constants cache).lookup key = none)
      (next : ∀ record : Record, invocation.LogicalResult record →
        Plan frame ((key, record) :: cache) (invocation.receipt key :: receipts) length) :
      Plan frame cache receipts (length + 1)

/-- Arbitrary finite mixtures of the admitted primitive commands construct
actual source-event paths and an authorized final cache. The command count
and receipt count are exact; no event disappears during composition. -/
theorem plan_trace (frame : Frame) {cache : Cache} {receipts : List ReceiptKeys.Entry} {length : Nat}
    (plan : Plan frame cache receipts length) (valid : Valid frame.policy frame.world cache) (state : State) :
    ∃ (afterCache : Cache) (afterReceipts : List ReceiptKeys.Entry) (commands : List SourceReplay.Command),
      commands.length = length ∧ afterReceipts.length = receipts.length + length ∧
      Valid frame.policy frame.world afterCache ∧
      SourceReplay.Trace state (frame.source cache receipts) commands (frame.source afterCache afterReceipts) := by
  induction plan with
  | stop cache receipts =>
      exact ⟨cache, receipts, [], rfl, by simp, valid, .nil _⟩
  | @event cache receipts length key invocation receiptFresh cacheFresh next ih =>
      obtain ⟨record, _, retained, logical, executed⟩ := executes frame cache valid receipts key invocation
        receiptFresh cacheFresh state
      obtain ⟨afterCache, afterReceipts, commands, count, receiptCount, afterValid, trace⟩ :=
        ih record logical retained
      exact ⟨afterCache, afterReceipts, invocation.command key :: commands, by simp [count],
        by simp only [List.length_cons] at receiptCount; omega, afterValid, .cons executed trace⟩

/-- The whole quoted replay loop, rather than only individually checked
events, executes the constructed finite admitted history. -/
theorem authored_plan_returns (frame : Frame) {cache : Cache} {receipts : List ReceiptKeys.Entry} {length : Nat}
    (plan : Plan frame cache receipts length) (valid : Valid frame.policy frame.world cache) (state : State) :
    ∃ (afterCache : Cache) (afterReceipts : List ReceiptKeys.Entry) (commands : List SourceReplay.Command),
      commands.length = length ∧ afterReceipts.length = receipts.length + length ∧
      Valid frame.policy frame.world afterCache ∧
      PureReturns program (SourceReplay.environment (frame.source cache receipts) commands) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", frame.source afterCache afterReceipts]) := by
  obtain ⟨afterCache, afterReceipts, commands, count, receiptCount, authorized, trace⟩ :=
    plan_trace frame plan valid state
  exact ⟨afterCache, afterReceipts, commands, count, receiptCount, authorized,
    SourceReplay.authored_run_from trace _ "state" "commands" rfl rfl⟩

end Mettapedia.Languages.HOLLight.MeTTa.InferenceSchedule
