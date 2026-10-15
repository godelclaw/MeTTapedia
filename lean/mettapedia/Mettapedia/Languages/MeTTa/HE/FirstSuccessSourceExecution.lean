import Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafEvaluation
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceScan
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlHistory

/-!
# Ordered nonleaf source derivations through retained first-success execution

The admitted read-only profile uses independently checked closed type casts
and argument domains. Recursive derivations retain the ordered accepted type
paths and every resulting occurrence. They construct paths in the existing
first-success worker; they do not install a second expression evaluator.

Equation bodies, polymorphic type matching and host operations have separate
correspondence obligations. Absence of equations is checked from the actual
space. Retained caller bindings and arbitrary raw syntax remain data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Type Spec.Type.Presentation
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessRawExecution
open FirstSuccessLeafEvaluation FirstSuccessSourceApplicability FirstSuccessSourceScan
open Mettapedia.GSLT.Distinction.ProductiveBlocks

attribute [local simp] Atom.atomType Atom.undefinedType Atom.symbolType Atom.variableType
  Atom.groundedType Atom.expressionType

/-- This profile has no host operations. That restriction is independent of
whether a syntax value is executable in any other runtime profile. -/
def noHost : Spec.Eval.GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- The space itself contains no equation declarations. -/
def EquationFree (space : Space) : Prop :=
  ∀ left right, .expression [.symbol "=", left, right] ∉ space.atoms

theorem no_source_equations (space : Space) (free : EquationFree space)
    (value : Atom) (fuel : Nat) : queryEquations space value fuel = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result member
  obtain ⟨left, right, index, declared, _, _⟩ := queryEquations_matchAtoms_witness member
  exact free left right (List.fst_mem_of_mem_zipIdx declared)

theorem no_independent_equations (space : Space) (free : EquationFree space)
    (live : List Atom) (value : Atom) (bindings : Bindings) :
    Spec.Eval.Steps.EquationQueryNoMatchRel space live value bindings := by
  intro freshLeft freshRight matched rule
  obtain ⟨left, right, declared, _⟩ := rule
  exact free left right declared

/-- Ordered replies with one unchanged binding frame. The list retains
occurrences even when their values and bindings coincide. -/
def replies (bindings : Bindings) (values : List Atom) : ResultSet :=
  values.map fun value => (value, bindings)

def packets (bindings : Bindings) (values : List (List Atom)) : ResultSet :=
  replies bindings (values.map argumentPacket)

/-- The exact arrow supplied by a checked argument/return presentation. -/
def arrow (domains : List Atom) (returned : Atom) : Atom :=
  .expression (.symbol "->" :: (domains ++ [returned]))

def selectedPolicy (domains : List Atom) (returned : Atom) : SelectedTypePolicy :=
  ⟨arrow domains returned, domains, returned, rfl⟩

/-- One admitted source application. Every type-side field is syntax,
lookup or an independently checked rejection/fit condition. No machine
correspondence or evaluator result is assumed. -/
structure ApplicationTyping (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (fuel : Nat) where
  domains : List Atom
  returned : Atom
  before : List Atom
  after : List Atom
  declined : List NativeSelectedTypeScan.Candidate
  sourceTypes : getAtomTypes space (.symbol name) = before ++ arrow domains returned :: after
  rejected : RejectedPrefix space fuel (.symbol name) expected arguments before declined
  argumentChecks : List.Forall₂ (fun argument domain =>
    ArgumentDomainEvidence space argument domain fuel) arguments domains
  argumentPaths : 0 < admittedPathCount space arguments domains
  expectedClosed : TypeSubst.typeVars expected = []
  returnedClosed : TypeSubst.typeVars returned = []
  returnedFits : ClosedTypeFits expected returned
  returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel
  earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = []
  earlierHeadRejects : ∀ candidate ∈ before, ¬ClosedTypeFits (arrow domains returned) candidate
  headClosed : TypeSubst.typeVars (arrow domains returned) = []
  headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel
  demandNotRaw : expected ≠ Atom.atomType
  demandNotExpression : expected ≠ Atom.expressionType
  nonemptyOperator : name ≠ "Empty"
  cleanOperator : name ≠ "Error"
  ordinaryOperator : name ≠ "unify" ∧ name ≠ "switch-minimal"

mutual
/-- A derivation carries exact ordered occurrences in addition to the
published singular evaluator judgment. Recursive children are source
derivations; callers cannot supply an assumed worker realization. -/
inductive AtomDerivation (space : Space) (bindings : Bindings) :
    Atom → Atom → Nat → List Atom → Prop where
  | leaf (value expected : Atom) (fuel : Nat) :
      LeafRel value expected → AtomDerivation space bindings value expected (fuel + 1) [value]
  | symbolCast (name : String) (expected : Atom) (fuel : Nat)
      (before after : List Atom) (actual : Atom) :
      name ≠ "Empty" → expected ≠ Atom.atomType → expected ≠ Atom.symbolType →
      getAtomTypes space (.symbol name) = before ++ actual :: after →
      TypeSubst.typeVars expected = [] → TypeSubst.typeVars actual = [] →
      (∀ candidate ∈ before, TypeSubst.typeVars candidate = []) →
      (∀ candidate ∈ before, ¬ClosedTypeFits expected candidate) →
      ClosedTypeFits expected actual → sizeOf expected + sizeOf actual + 2 ≤ fuel →
      AtomDerivation space bindings (.symbol name) expected (fuel + 1) [.symbol name]
  | application (name : String) (arguments : List Atom) (expected : Atom) (fuel : Nat)
      (typing : ApplicationTyping space name arguments expected fuel) (values : List (List Atom)) :
      ArgsDerivation space bindings arguments typing.domains fuel values →
      AtomDerivation space bindings (.expression (.symbol name :: arguments)) expected (fuel + 3)
        ((List.replicate (admittedPathCount space arguments typing.domains)
          (values.map fun packet => .expression (.symbol name :: packet))).flatten)

inductive ArgsDerivation (space : Space) (bindings : Bindings) :
    List Atom → List Atom → Nat → List (List Atom) → Prop where
  | nil (fuel : Nat) : ArgsDerivation space bindings [] [] (fuel + 1) [[]]
  | cons (value expected : Atom) (values types : List Atom) (fuel : Nat)
      (heads : List Atom) (tails : List (List Atom)) :
      AtomDerivation space bindings value expected fuel heads →
      ArgsDerivation space bindings values types fuel tails →
      ArgsDerivation space bindings (value :: values) (expected :: types) (fuel + 1)
        (heads.flatMap fun head => tails.map fun tail => head :: tail)
end

abbrev Realizes (space : Space) (task : Task) (results : ResultSet) : Prop :=
  ∀ stack emitted, SilentPath HE.GroundedDispatch.none
    ⟨space, .work task, stack, emitted⟩ ⟨space, .returning results, stack, emitted⟩

theorem append_results (space : Space) (remaining : Task) (first second : ResultSet)
    (tail : Realizes space remaining second) (stack : List Frame) (emitted : ResultSet) :
    SilentPath HE.GroundedDispatch.none
      ⟨space, .returning first, .append remaining :: stack, emitted⟩
      ⟨space, .returning (first ++ second), stack, emitted⟩ := by
  have begin := consume_continuation space HE.GroundedDispatch.none (.append remaining) first stack emitted
  have endPath := consume_continuation space HE.GroundedDispatch.none (.prepend first) second stack emitted
  exact begin.trans (by
    simpa only [RecursiveMachine.resume, List.cons_append, List.nil_append] using
      (tail (.prepend first :: stack) emitted).trans endPath)


theorem call_unreduced (space : Space) (free : EquationFree space)
    (name : String) (ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal")
    (clean : name ≠ "Error") (arguments : List Atom) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected bindings (fuel + 1))
      [(.expression (.symbol name :: arguments), bindings)] := by
  intro stack emitted
  have entered : FirstSuccessRecursiveStrategy.enter space HE.GroundedDispatch.none
      (.call (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)) =
        (.returning [(.expression (.symbol name :: arguments), bindings)], []) := by
    simp [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isErrorAtom,
      ordinary.1, ordinary.2, clean, no_source_equations space free, HE.GroundedDispatch.none]
  simpa only [entered, List.nil_append] using
    enter_request space HE.GroundedDispatch.none
      (.call (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)) stack emitted

theorem calls_unreduced (space : Space) (free : EquationFree space)
    (name : String) (ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal")
    (clean : name ≠ "Error") (values : List (List Atom)) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) :
    Realizes space (.calls expected (fuel + 1)
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))))
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  induction values with
  | nil =>
      intro stack emitted
      simpa [replies, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
        enter_request space HE.GroundedDispatch.none (.calls expected (fuel + 1) []) stack emitted
  | cons value values ih =>
      intro stack emitted
      let rest := Task.calls expected (fuel + 1)
        (replies bindings (values.map fun packet => .expression (.symbol name :: packet)))
      have begin := enter_request space HE.GroundedDispatch.none
        (.calls expected (fuel + 1)
          (replies bindings ((value :: values).map fun packet => .expression (.symbol name :: packet))))
        stack emitted
      have head := call_unreduced space free name ordinary clean value expected bindings fuel
        (.append rest :: stack) emitted
      have remaining := append_results space rest
        [(.expression (.symbol name :: value), bindings)]
        (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) ih stack emitted
      exact begin.trans (by
        simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, replies, rest] using
          head.trans remaining)

theorem argument_heads (space : Space) (original : Atom) (remaining types : List Atom)
    (bindings : Bindings) (fuel : Nat) (heads : List Atom) (tails : List (List Atom))
    (safe : ∀ head ∈ heads, head = original ∨ isEmptyOrError head = false)
    (tail : Realizes space (.args remaining types bindings fuel) (packets bindings tails)) :
    Realizes space (.argumentHeads original remaining types fuel (replies bindings heads))
      (packets bindings (heads.flatMap fun head => tails.map fun values => head :: values)) := by
  induction heads with
  | nil =>
      intro stack emitted
      simpa [replies, packets, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
        enter_request space HE.GroundedDispatch.none
          (.argumentHeads original remaining types fuel []) stack emitted
  | cons head heads ih =>
      have safeHead := safe head (by simp)
      have safeTail : ∀ value ∈ heads, value = original ∨ isEmptyOrError value = false := by
        intro value member; exact safe value (by simp [member])
      intro stack emitted
      let rest := Task.argumentHeads original remaining types fuel (replies bindings heads)
      have begin := enter_request space HE.GroundedDispatch.none
        (.argumentHeads original remaining types fuel (replies bindings (head :: heads))) stack emitted
      have guard : (head != original && isEmptyOrError head) = false := by
        rcases safeHead with rfl | clean
        · simp
        · simp [clean]
      have middle := tail (.argumentTail head :: .append rest :: stack) emitted
      have collect := consume_continuation space HE.GroundedDispatch.none (.argumentTail head)
        (packets bindings tails) (.append rest :: stack) emitted
      have mapped : RecursiveTasks.argumentTail head (packets bindings tails) =
          packets bindings (tails.map fun values => head :: values) := by
        simp [packets, replies, RecursiveTasks.argumentTail, List.map_map, Function.comp_def]
      have finish := append_results space rest
        (packets bindings (tails.map fun values => head :: values))
        (packets bindings (heads.flatMap fun value => tails.map fun values => value :: values))
        (ih safeTail) stack emitted
      have collected : SilentPath HE.GroundedDispatch.none
          ⟨space, .returning (packets bindings tails), .argumentTail head :: .append rest :: stack, emitted⟩
          ⟨space, .returning (packets bindings (tails.map fun values => head :: values)),
            .append rest :: stack, emitted⟩ := by
        simpa only [RecursiveMachine.resume, mapped, List.nil_append] using collect
      exact begin.trans (by
        simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, replies, rest, guard,
          packets, List.map_append] using middle.trans (collected.trans finish))

theorem function_head (space : Space) (name : String) (domains : List Atom) (returned : Atom)
    (bindings : Bindings) (fuel : Nat) (values : List (List Atom)) (arguments : List Atom)
    (clean : name ≠ "Empty")
    (tail : Realizes space (.args arguments domains bindings fuel) (packets bindings values)) :
    Realizes space (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)])
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  intro stack emitted
  let rest := Task.heads (arrow domains returned) arguments fuel []
  have begin := enter_request space HE.GroundedDispatch.none
    (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)]) stack emitted
  have middle := tail (.functionTail (.symbol name) :: .append rest :: stack) emitted
  have collect := consume_continuation space HE.GroundedDispatch.none (.functionTail (.symbol name))
    (packets bindings values) (.append rest :: stack) emitted
  have mapped : RecursiveTasks.functionTail (.symbol name) (packets bindings values) =
      replies bindings (values.map fun packet => .expression (.symbol name :: packet)) := by
    simp [packets, replies, RecursiveTasks.functionTail, List.map_map, Function.comp_def]
  have emptyRest : Realizes space rest [] := by
    intro saved prior
    simpa [rest, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
      enter_request space HE.GroundedDispatch.none rest saved prior
  have finish := append_results space rest
    (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) []
    emptyRest stack emitted
  have collected : SilentPath HE.GroundedDispatch.none
      ⟨space, .returning (packets bindings values), .functionTail (.symbol name) :: .append rest :: stack, emitted⟩
      ⟨space, .returning (replies bindings (values.map fun packet => .expression (.symbol name :: packet))),
        .append rest :: stack, emitted⟩ := by
    simpa only [RecursiveMachine.resume, mapped, List.nil_append] using collect
  exact begin.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, isErrorAtom, clean, arrow, getFunctionArgTypes, rest] using
        middle.trans (collected.trans finish))


theorem symbol_cast_realizes (space : Space) (name : String) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty")
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    Realizes space (.atom (.symbol name) expected bindings (fuel + 1)) [(.symbol name, bindings)] := by
  intro stack emitted
  have cast := (closed_cast_reply space (.symbol name) expected bindings fuel before actual after
    types expectedClosed earlierClosed earlierRejects actualClosed fits enough).1
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
    isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, notEmpty, cast] using
      enter_request space HE.GroundedDispatch.none
        (.atom (.symbol name) expected bindings (fuel + 1)) stack emitted

theorem symbol_cast_spec (space : Space) (name : String) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel)
    (live : List Atom) (scope : List String) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.symbol name) expected bindings (.symbol name, bindings) := by
  apply EvalAtomRawRel.cast (.symbol name) expected Atom.symbolType bindings (.symbol name, bindings)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
  · exact .symbol name
  · rintro (raw | intrinsic | impossible)
    · exact notRaw raw
    · exact notMeta intrinsic
    · simp at impossible
  · exact Or.inl ⟨name, rfl⟩
  · exact (closed_cast_reply space (.symbol name) expected bindings fuel before actual after
      types expectedClosed earlierClosed earlierRejects actualClosed fits enough).2

theorem application_selected {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) :
    FirstSuccessRecursiveStrategy.select space (.expression (.symbol name :: arguments)) expected bindings
      (fuel + 1) (getAtomTypes space (.symbol name)) =
        .selected (selectedPolicy typing.domains typing.returned)
          (List.replicate (admittedPathCount space arguments typing.domains) bindings) ∧
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel space
      (.expression (.symbol name :: arguments)) expected bindings
      (getAtomTypes space (.symbol name))
      (.success (selectedPolicy typing.domains typing.returned) bindings) := by
  obtain ⟨policy, domains, returned, selected, scan⟩ := checked_prefix_selected typing.rejected
    typing.returned typing.domains bindings typing.after typing.argumentChecks typing.argumentPaths
    typing.expectedClosed typing.returnedClosed typing.returnedFits typing.returnBudget
  have same : policy = selectedPolicy typing.domains typing.returned := by
    cases policy with
    | mk functionType argumentTypes returnType isFunction =>
        dsimp at domains returned
        subst argumentTypes; subst returnType
        change functionType = arrow typing.domains typing.returned at isFunction
        subst functionType
        rfl
  subst policy
  rw [typing.sourceTypes]
  exact ⟨selected, scan⟩

theorem application_function {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (values : List (List Atom))
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel) (packets bindings values)) :
    Realizes space
      (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        bindings (fuel + 1))
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  cases fuel with
  | zero => have := typing.headBudget; omega
  | succ fuel =>
      intro stack emitted
      have cast := symbol_cast_realizes space name (arrow typing.domains typing.returned)
        bindings fuel typing.before typing.after (arrow typing.domains typing.returned)
        typing.nonemptyOperator typing.sourceTypes
        typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega)
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) :: stack) emitted
      have resumed := consume_continuation space HE.GroundedDispatch.none
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1)) [(.symbol name, bindings)] stack emitted
      have done := function_head space name typing.domains typing.returned bindings (fuel + 1) values arguments
        typing.nonemptyOperator argumentsRun stack emitted
      have continuation := resumed.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append] using done)
      have begin := enter_request space HE.GroundedDispatch.none
        (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
          bindings (fuel + 1 + 1)) stack emitted
      exact begin.trans (by
        simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          List.cons_append, List.nil_append] using cast.trans continuation)

theorem binding_alternatives {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (free : EquationFree space) (bindings : Bindings) (values : List (List Atom)) (count : Nat)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel) (packets bindings values)) :
    Realizes space
      (.bindingAlternatives (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (List.replicate count bindings))
      (replies bindings ((List.replicate count
        (values.map fun packet => .expression (.symbol name :: packet))).flatten)) := by
  induction count with
  | zero =>
      intro stack emitted
      simpa [replies, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
        enter_request space HE.GroundedDispatch.none
          (.bindingAlternatives (.expression (.symbol name :: arguments))
            (arrow typing.domains typing.returned)
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
            (fuel + 1) []) stack emitted
  | succ count ih =>
      intro stack emitted
      let callType := if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned
      let one := replies bindings (values.map fun packet => .expression (.symbol name :: packet))
      let rest := Task.bindingAlternatives (.expression (.symbol name :: arguments))
        (arrow typing.domains typing.returned) callType (fuel + 1) (List.replicate count bindings)
      have begin := enter_request space HE.GroundedDispatch.none
        (.bindingAlternatives (.expression (.symbol name :: arguments))
          (arrow typing.domains typing.returned) callType (fuel + 1)
          (List.replicate (count + 1) bindings)) stack emitted
      have function := application_function typing bindings values argumentsRun
        (.calls callType (fuel + 1) :: .append rest :: stack) emitted
      have transfer := consume_continuation space HE.GroundedDispatch.none (.calls callType (fuel + 1)) one
        (.append rest :: stack) emitted
      have calls := calls_unreduced space free name typing.ordinaryOperator typing.cleanOperator values
        callType bindings fuel (.append rest :: stack) emitted
      have remainder := append_results space rest one
        (replies bindings ((List.replicate count
          (values.map fun packet => .expression (.symbol name :: packet))).flatten)) ih stack emitted
      have collected := transfer.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append, one] using calls.trans remainder)
      exact begin.trans (by
        simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.replicate_succ,
          callType, one, rest, replies, List.map_append] using function.trans collected)


theorem clean_application (name : String) (values : List Atom) (clean : name ≠ "Error") :
    ¬IsEmptyOrErrorRel (.expression (.symbol name :: values)) ∧
    isEmptyOrError (.expression (.symbol name :: values)) = false := by
  simp [IsEmptyOrErrorRel, IsErrorRel, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty, clean]

theorem application_spec {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (free : EquationFree space) (bindings : Bindings) (values : List Atom)
    (argumentDerivation : InterpretArgsRel space noHost [] arguments typing.domains bindings
      (argumentPacket values, bindings)) (scope : List String) :
    EvalAtomRawRel space noHost [] (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected bindings
      (.expression (.symbol name :: values), bindings) := by
  have cleanInput := (clean_application name arguments typing.cleanOperator).1
  have cleanOutput := (clean_application name values typing.cleanOperator).1
  have interpreted : InterpretExpressionRel space noHost []
      (.expression (.symbol name :: arguments)) expected bindings
      (.expression (.symbol name :: values), bindings) := by
    apply InterpretExpressionRel.functionPath _ _ (.symbol name) arguments
      (getAtomTypes space (.symbol name)) (selectedPolicy typing.domains typing.returned)
      (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
      bindings bindings (.expression (.symbol name :: values), bindings)
      (.expression (.symbol name :: values), bindings) rfl (FirstSuccessSourceReplies.source_types space (.symbol name))
      (application_selected typing bindings).2 rfl
    · have head : EvalAtomRawRel space noHost []
          (protectedScope := expectedApplicationScope (.expression (.symbol name :: arguments)) expected)
          (.symbol name) (arrow typing.domains typing.returned) bindings (.symbol name, bindings) :=
        symbol_cast_spec space name (arrow typing.domains typing.returned) bindings (fuel - 1)
          typing.before typing.after (arrow typing.domains typing.returned)
          typing.nonemptyOperator (by simp [arrow]) (by simp [arrow]) typing.sourceTypes
          typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega) [] _
      simpa only [selectedPolicy, argumentValues_packet] using (InterpretFunctionRel.success
        (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned) expected (.symbol name)
        typing.returned arguments typing.domains bindings (.symbol name, bindings)
        (argumentPacket values, bindings) rfl (show FunctionTypeRel (arrow typing.domains typing.returned)
          typing.domains typing.returned from rfl) head
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, typing.nonemptyOperator]) argumentDerivation
        ⟨values, rfl⟩)
    · apply CallRel.noEquation
      · exact fun error => cleanOutput (Or.inr error)
      · simp [NonGroundedCallRel, noHost, typing.ordinaryOperator.1, typing.ordinaryOperator.2]
      · exact no_independent_equations space free [] _ bindings
  apply EvalAtomRawRel.interpretSuccess _ _ Atom.expressionType bindings _ cleanInput
    (.expression (.symbol name :: arguments)) _ ⟨.symbol name, arguments, rfl⟩ interpreted
    (fun error => cleanOutput (Or.inr error))
  rintro (raw | intrinsic | impossible)
  · exact typing.demandNotRaw raw
  · exact typing.demandNotExpression intrinsic
  · simp at impossible

theorem success_priority_clean (bindings : Bindings) (values : List Atom)
    (clean : ∀ value ∈ values, isErrorAtom value = false) :
    successPriority (replies bindings values) = replies bindings values := by
  have all : (replies bindings values).filter (fun result => !isErrorAtom result.1) =
      replies bindings values := by
    apply List.filter_eq_self.mpr
    intro result member
    obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
    simp [clean value valueMember]
  rw [successPriority, all]
  cases values with
  | nil => simp [replies]
  | cons value values => simp [replies]

theorem application_realizes {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (free : EquationFree space) (bindings : Bindings) (values : List (List Atom))
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel) (packets bindings values)) :
    Realizes space (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3))
      (replies bindings ((List.replicate (admittedPathCount space arguments typing.domains)
        (values.map fun packet => .expression (.symbol name :: packet))).flatten)) := by
  intro stack emitted
  let resultValues := (List.replicate (admittedPathCount space arguments typing.domains)
    (values.map fun packet => Atom.expression (.symbol name :: packet))).flatten
  have atom := enter_request space HE.GroundedDispatch.none
    (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3)) stack emitted
  have expression := enter_request space HE.GroundedDispatch.none
    (.expression (.expression (.symbol name :: arguments)) expected bindings (fuel + 2)) (.filter :: stack) emitted
  have selection := enter_request space HE.GroundedDispatch.none
    (.functions (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)
      (getAtomTypes space (.symbol name))) (.filter :: stack) emitted
  have alternatives := binding_alternatives typing free bindings values (admittedPathCount space arguments typing.domains)
    argumentsRun (.filter :: stack) emitted
  have filtered := consume_continuation space HE.GroundedDispatch.none .filter (replies bindings resultValues)
    stack emitted
  have selected := (application_selected typing bindings).1
  have priority : successPriority (replies bindings resultValues) = replies bindings resultValues := by
    apply success_priority_clean
    intro value member
    rcases List.mem_flatten.mp member with ⟨row, rowMember, valueMember⟩
    have rowSame := List.mem_replicate.mp rowMember |>.2
    subst row
    obtain ⟨packet, _, rfl⟩ := List.mem_map.mp valueMember
    simp [isErrorAtom, typing.cleanOperator]
  have done := alternatives.trans (by
    simpa only [RecursiveMachine.resume, priority, List.nil_append, resultValues] using filtered)
  have stepSelection := selection.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, selected, selectedPolicy] using done)
  have stepExpression := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, List.nil_append] using stepSelection)
  have notRaw : expected ≠ .symbol "Atom" := typing.demandNotRaw
  have notExpression : expected ≠ .symbol "Expression" := typing.demandNotExpression
  exact atom.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, Atom.unit, isErrorAtom, getMetaType, notRaw,
      notExpression, typing.cleanOperator, Nat.add_assoc] using stepExpression)


private abbrev AtomLaw (space : Space) (bindings : Bindings) (value expected : Atom)
    (fuel : Nat) (heads : List Atom) : Prop :=
  Realizes space (.atom value expected bindings fuel) (replies bindings heads) ∧
    (∀ head ∈ heads, ∀ scope : List String, EvalAtomRawRel space noHost []
      (protectedScope := scope) value expected bindings (head, bindings)) ∧
    (∀ head ∈ heads, head = value ∨ isEmptyOrError head = false)

private abbrev ArgsLaw (space : Space) (bindings : Bindings) (values types : List Atom)
    (fuel : Nat) (results : List (List Atom)) : Prop :=
  Realizes space (.args values types bindings fuel) (packets bindings results) ∧
    ∀ result ∈ results, InterpretArgsRel space noHost [] values types bindings
      (argumentPacket result, bindings)

private theorem leaf_law (space : Space) (bindings : Bindings) (value expected : Atom)
    (fuel : Nat) (leaf : LeafRel value expected) :
    AtomLaw space bindings value expected (fuel + 1) [value] := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [replies, List.map_cons, List.map_nil] using
      retained_leaf space HE.GroundedDispatch.none value expected bindings fuel leaf
  · intro head member scope
    have same := List.mem_singleton.mp member
    subst head
    exact leaf_evidence space noHost [] publishedTypeService scope value expected bindings leaf
  · intro head member
    exact Or.inl (List.mem_singleton.mp member)

private theorem cast_law (space : Space) (bindings : Bindings) (name : String)
    (expected : Atom) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType) (notMeta : expected ≠ Atom.symbolType)
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    AtomLaw space bindings (.symbol name) expected (fuel + 1) [.symbol name] := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [replies, List.map_cons, List.map_nil] using
      symbol_cast_realizes space name expected bindings fuel before after actual notEmpty types
        expectedClosed actualClosed earlierClosed earlierRejects fits enough
  · intro head member scope
    obtain rfl := List.mem_singleton.mp member
    exact symbol_cast_spec space name expected bindings fuel before after actual notEmpty notRaw notMeta types
      expectedClosed actualClosed earlierClosed earlierRejects fits enough [] scope
  · intro head member
    exact Or.inl (List.mem_singleton.mp member)

private theorem application_law (space : Space) (free : EquationFree space) (bindings : Bindings)
    (name : String) (arguments : List Atom) (expected : Atom) (fuel : Nat)
    (typing : ApplicationTyping space name arguments expected fuel) (values : List (List Atom))
    (tail : ArgsLaw space bindings arguments typing.domains fuel values) :
    AtomLaw space bindings (.expression (.symbol name :: arguments)) expected (fuel + 3)
      ((List.replicate (admittedPathCount space arguments typing.domains)
        (values.map fun packet => .expression (.symbol name :: packet))).flatten) := by
  refine ⟨application_realizes typing free bindings values tail.1, ?_, ?_⟩
  · intro result member scope
    rcases List.mem_flatten.mp member with ⟨row, rowMember, resultMember⟩
    have rowSame := List.mem_replicate.mp rowMember |>.2
    subst row
    obtain ⟨packet, packetMember, rfl⟩ := List.mem_map.mp resultMember
    exact application_spec typing free bindings packet (tail.2 packet packetMember) scope
  · intro result member
    rcases List.mem_flatten.mp member with ⟨row, rowMember, resultMember⟩
    have rowSame := List.mem_replicate.mp rowMember |>.2
    subst row
    obtain ⟨packet, _, rfl⟩ := List.mem_map.mp resultMember
    exact Or.inr (clean_application name packet typing.cleanOperator).2

private theorem arguments_nil_law (space : Space) (bindings : Bindings) (fuel : Nat) :
    ArgsLaw space bindings [] [] (fuel + 1) [[]] := by
  refine ⟨?_, ?_⟩
  · intro stack emitted
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, packets, replies] using
      enter_request space HE.GroundedDispatch.none (.args [] [] bindings (fuel + 1)) stack emitted
  · intro result member
    obtain rfl := List.mem_singleton.mp member
    exact .nil bindings

private theorem arguments_cons_law (space : Space) (bindings : Bindings) (value expected : Atom)
    (values types : List Atom) (fuel : Nat) (heads : List Atom) (tails : List (List Atom))
    (headLaw : AtomLaw space bindings value expected fuel heads)
    (tailLaw : ArgsLaw space bindings values types fuel tails) :
    ArgsLaw space bindings (value :: values) (expected :: types) (fuel + 1)
      (heads.flatMap fun head => tails.map fun tail => head :: tail) := by
  refine ⟨?_, ?_⟩
  · intro stack emitted
    have begin := enter_request space HE.GroundedDispatch.none
      (.args (value :: values) (expected :: types) bindings (fuel + 1)) stack emitted
    have head := headLaw.1 (.argumentHeads value values types fuel :: stack) emitted
    have transfer := consume_continuation space HE.GroundedDispatch.none
      (.argumentHeads value values types fuel) (replies bindings heads) stack emitted
    have tail := argument_heads space value values types bindings fuel heads tails headLaw.2.2 tailLaw.1 stack emitted
    have combined := head.trans (transfer.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append] using tail))
    exact begin.trans (by
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
        List.cons_append, List.nil_append] using combined)
  · intro result member
    obtain ⟨head, headMember, resultMember⟩ := List.mem_flatMap.mp member
    obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp resultMember
    have safe : ¬IsEmptyOrErrorRel head ∨ head = value := by
      rcases headLaw.2.2 head headMember with equal | clean
      · exact Or.inr equal
      · exact Or.inl (by
          intro error
          have failed := (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError head).mp error
          simp [clean] at failed)
    simpa only [argumentValues_packet] using InterpretArgsRel.success value values expected types bindings
      (head, bindings) (argumentPacket tail, bindings) (headLaw.2.1 head headMember []) safe
      (tailLaw.2 tail tailMember) ⟨tail, rfl⟩

private theorem atom_law {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) :
    AtomLaw space bindings value expected fuel heads := by
  exact AtomDerivation.rec
    (motive_1 := fun value expected fuel heads _ => AtomLaw space bindings value expected fuel heads)
    (motive_2 := fun values types fuel results _ => ArgsLaw space bindings values types fuel results)
    (leaf_law space bindings) (cast_law space bindings)
    (fun name arguments expected fuel typing values _ tail =>
      application_law space free bindings name arguments expected fuel typing values tail)
    (arguments_nil_law space bindings)
    (fun value expected values types fuel heads tails _ _ headLaw tailLaw =>
      arguments_cons_law space bindings value expected values types fuel heads tails headLaw tailLaw) derivation

private theorem args_law {space : Space} (free : EquationFree space) {bindings : Bindings}
    {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ArgsDerivation space bindings values types fuel results) :
    ArgsLaw space bindings values types fuel results := by
  exact ArgsDerivation.rec
    (motive_1 := fun value expected fuel heads _ => AtomLaw space bindings value expected fuel heads)
    (motive_2 := fun values types fuel results _ => ArgsLaw space bindings values types fuel results)
    (leaf_law space bindings) (cast_law space bindings)
    (fun name arguments expected fuel typing values _ tail =>
      application_law space free bindings name arguments expected fuel typing values tail)
    (arguments_nil_law space bindings)
    (fun value expected values types fuel heads tails _ _ headLaw tailLaw =>
      arguments_cons_law space bindings value expected values types fuel heads tails headLaw tailLaw) derivation

/-- Every admitted recursive source derivation realizes its full ordered
reply under arbitrary retained caller continuations and prior observations. -/
theorem AtomDerivation.realizes {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) :
    Realizes space (.atom value expected bindings fuel) (replies bindings heads) :=
  (atom_law free derivation).1

/-- Each occurrence in the constructed ordered reply is earned by the
independent, fuel-free first-success evaluator rules. -/
theorem AtomDerivation.sound {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads)
    (head : Atom) (member : head ∈ heads) (scope : List String) :
    EvalAtomRawRel space noHost [] (protectedScope := scope) value expected bindings (head, bindings) :=
  (atom_law free derivation).2.1 head member scope

theorem ArgsDerivation.realizes {space : Space} (free : EquationFree space) {bindings : Bindings}
    {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ArgsDerivation space bindings values types fuel results) :
    Realizes space (.args values types bindings fuel) (packets bindings results) :=
  (args_law free derivation).1

theorem ArgsDerivation.sound {space : Space} (free : EquationFree space) {bindings : Bindings}
    {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ArgsDerivation space bindings values types fuel results)
    (result : List Atom) (member : result ∈ results) :
    InterpretArgsRel space noHost [] values types bindings (argumentPacket result, bindings) :=
  (args_law free derivation).2 result member


/-- The existing worker drains every ordered occurrence and retains the
whole history; padding the budget after completion produces no new results. -/
theorem drain_returning (space : Space) (results emitted : ResultSet) (later : Nat) :
    (machine HE.GroundedDispatch.none).run (results.length + 1 + later)
      ⟨space, .returning results, [], emitted⟩ =
      (results, .finished ⟨space, .returning [], [], emitted ++ results⟩) := by
  induction results generalizing emitted with
  | nil =>
      have stepped : (machine HE.GroundedDispatch.none).step
          ⟨space, .returning [], [], emitted⟩ = some (.finish ⟨space, .returning [], [], emitted⟩) := rfl
      rw [show ([] : ResultSet).length + 1 + later = later + 1 by simp; omega]
      simpa only [List.append_nil] using
        (machine HE.GroundedDispatch.none).run_succ_finish (fuel := later) stepped
  | cons result results ih =>
      have stepped : (machine HE.GroundedDispatch.none).step
          ⟨space, .returning (result :: results), [], emitted⟩ =
            some (.publish [result] ⟨space, .returning results, [], emitted ++ [result]⟩) := rfl
      rw [show (result :: results).length + 1 + later = (results.length + 1 + later) + 1 by simp; omega,
        (machine HE.GroundedDispatch.none).run_succ_publish stepped, ih]
      simp only [List.singleton_append, List.append_assoc]

/-- Completion is derived from the actual source continuations. The bound
is per derivation; it is not a uniform latency claim for arbitrary programs. -/
theorem AtomDerivation.completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) (earned : ResultSet) :
    ∃ budget, ∀ later, (machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ =
      (replies bindings heads, .finished
        ⟨space, .returning [], [], earned ++ replies bindings heads⟩) := by
  obtain ⟨administrative, realized⟩ := (machine HE.GroundedDispatch.none).silent_run
    (derivation.realizes free [] earned)
  refine ⟨administrative + (replies bindings heads).length + 1, fun later => ?_⟩
  rw [show administrative + (replies bindings heads).length + 1 + later =
    administrative + ((replies bindings heads).length + 1 + later) by omega,
    realized ((replies bindings heads).length + 1 + later)]
  exact drain_returning space (replies bindings heads) earned later

theorem AtomDerivation.encoded_completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) (earned : ResultSet) :
    ∃ budget, ∀ later, (dataMachine HE.GroundedDispatch.none).run (budget + later)
      (RecursiveEncoding.configurationData
        ⟨space, .work (.atom value expected bindings fuel), [], earned⟩) =
      (replies bindings heads, .finished
        ⟨space, .returning [], [], earned ++ replies bindings heads⟩) := by
  obtain ⟨budget, complete⟩ := derivation.completed free earned
  refine ⟨budget, fun later => ?_⟩
  rw [run_representation, complete later]
  rfl

/-- Any finished run from the admitted request has the whole ordered reply
and the same complete final history, regardless of its supplied work budget. -/
theorem AtomDerivation.completed_unique {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads)
    (earned actual : ResultSet) (budget : Nat) (finished : RecursiveTasks.Configuration)
    (ran : (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ = (actual, .finished finished)) :
    actual = replies bindings heads ∧
      finished = ⟨space, .returning [], [], earned ++ replies bindings heads⟩ := by
  obtain ⟨bound, complete⟩ := derivation.completed free earned
  have stable := (machine HE.GroundedDispatch.none).run_stable budget bound
    ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ (by
      intro residual impossible
      rw [ran] at impossible
      cases impossible)
  have same := complete budget
  rw [Nat.add_comm bound budget, stable, ran] at same
  have endpoints := Prod.mk.inj same
  exact ⟨endpoints.1, Outcome.finished.inj endpoints.2⟩

/-- A previously observed prefix and the complete saved worker determine the
remaining occurrence list. Its continuation reuses the saved work and never
restarts evaluation of the original expression. -/
theorem AtomDerivation.resumed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads)
    (earned observedPrefix : ResultSet) (first : Nat) (saved : RecursiveTasks.Configuration)
    (paused : (machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ = (observedPrefix, .exhausted saved)) :
    ∃ remainingBudget remaining,
      (machine HE.GroundedDispatch.none).run remainingBudget saved =
        (remaining, .finished ⟨space, .returning [], [], earned ++ replies bindings heads⟩) ∧
      observedPrefix ++ remaining = replies bindings heads := by
  obtain ⟨budget, completed⟩ := derivation.completed free earned
  have resume := (machine HE.GroundedDispatch.none).established_and_pending first budget
    ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ saved observedPrefix paused
  have finished := completed first
  rw [Nat.add_comm budget first, resume] at finished
  have pieces := Prod.mk.inj finished
  refine ⟨budget, ((machine HE.GroundedDispatch.none).run budget saved).1, ?_, pieces.1⟩
  exact Prod.ext rfl pieces.2

/-- Executable source-service collection observes only a finished worker.
Exhaustion remains pending and cannot be converted into an earned empty reply. -/
def collectReply (space : Space) (value expected : Atom) (bindings : Bindings)
    (evaluatorFuel workBudget : Nat) : Option ResultSet :=
  let result := (machine HE.GroundedDispatch.none).run workBudget
    ⟨space, .work (.atom value expected bindings evaluatorFuel), [], []⟩
  match result.2 with
  | .finished _ => some result.1
  | _ => none

theorem AtomDerivation.collect {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) :
    ∃ budget, ∀ later, collectReply space value expected bindings fuel (budget + later) =
      some (replies bindings heads) := by
  obtain ⟨budget, complete⟩ := derivation.completed free []
  exact ⟨budget, fun later => by simp only [collectReply, complete later]⟩

/-- A collector cannot return a shorter support-only list or a different
history once the admitted source request has completed. -/
theorem AtomDerivation.collect_exact {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads)
    (budget : Nat) (actual : ResultSet)
    (collected : collectReply space value expected bindings fuel budget = some actual) :
    actual = replies bindings heads := by
  cases ran : (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel), [], []⟩ with
  | mk events outcome =>
      cases outcome with
      | finished finished =>
          have equal : events = actual := by
            simpa only [collectReply, ran, Option.some.injEq] using collected
          exact equal.symm.trans (derivation.completed_unique free [] events budget finished ran).1
      | exhausted saved => simp only [collectReply, ran, reduceCtorEq] at collected
      | faulted => simp only [collectReply, ran, reduceCtorEq] at collected
      | suspended request saved => simp only [collectReply, ran, reduceCtorEq] at collected
      | stuck saved => simp only [collectReply, ran, reduceCtorEq] at collected

/-- Actual finite binding preparation and recursive evaluation compose at
the resolved endpoint. Neither an original variable nor its unresolved type
is silently substituted for the checked prepared request. -/
theorem prepared_nonleaf_collect {space : Space} (free : EquationFree space)
    {substitution : TypeSubst} (normal : substitution.Normal)
    (argument : TypedApplyState) (policy : NativeArgumentControlPolicy.Policy) (preparationFuel : Nat)
    (imported : argument.env = FirstSuccessPreparedArguments.presentedBindings substitution)
    (domainBudget : LeaTTaBridge.atomDepth (NativeArgumentControl.originalDomain argument) + 2 ≤ preparationFuel)
    (argumentBudget : LeaTTaBridge.atomDepth (NativeArgumentControl.original argument) + 2 ≤ preparationFuel)
    (fuel : Nat) (heads : List Atom)
    (derivation : AtomDerivation space argument.env
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).bound
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).domain fuel heads) :
    FirstSuccessPreparedArguments.PreparationRel substitution argument policy
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel) ∧
    ∃ budget, ∀ later, collectReply space
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).bound
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).domain
      argument.env fuel (budget + later) = some (replies argument.env heads) :=
  ⟨FirstSuccessPreparedArguments.preparation_sound normal argument policy preparationFuel
    imported domainBudget argumentBudget, derivation.collect free⟩

/-- The actual finite source result, the independent delivery relation and
history preservation agree at the complete saved evaluation endpoint. -/
theorem deliver_nonleaf {space : Space} (free : EquationFree space)
    (configuration : NativeArgumentControl.Configuration)
    (history : NativeArgumentControlHistory.HistoryInv configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : AtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    ∃ budget after,
      collectReply space prepared.bound prepared.domain argument.env fuel budget = some (replies argument.env heads) ∧
      NativeArgumentControl.DeliveryRel configuration
        ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
          .evaluated (replies argument.env heads), charge⟩ after ∧
      NativeArgumentControlHistory.HistoryInv after ∧
      NativeArgumentControlEncoding.resumeInteractionData
        (NativeArgumentControlMachine.interactionData (.active configuration))
        (.returned (NativeArgumentControlEncoding.replyData
          ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
            .evaluated (replies argument.env heads), charge⟩)) =
          NativeArgumentControlMachine.interactionData (.active after) ∧
      (∀ result ∈ replies argument.env heads,
        EvalAtomRawRel space noHost [] prepared.bound prepared.domain argument.env result) := by
  obtain ⟨budget, collected⟩ := derivation.collect free
  let reply : NativeArgumentControl.Reply :=
    ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
      .evaluated (replies argument.env heads), charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      (replies argument.env heads) charge pending
  have delivery := (NativeArgumentControl.deliver_iff configuration reply after).mp accepted
  refine ⟨budget, after, by simpa using collected 0, delivery,
    NativeArgumentControlHistory.delivery_preserves_history history accepted,
    (NativeArgumentControlEncoding.represented_reply_accepted_iff configuration after reply).mpr delivery, ?_⟩
  intro result member
  obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
  exact derivation.sound free value valueMember []


section OwnedReplies

open Mettapedia.Machines
open NativeArgumentControlHistory.OwnedReplyBoundary

/-- An independently earned nonleaf source reply crosses the issued boundary
only in the source world it actually consulted. The dependency retains the
complete source atoms, including order and duplicate declarations. This is
the admitted read-only source profile, not a native callback correspondence. -/
theorem deliver_nonleaf_owned {Key : Type} [DecidableEq Key]
    {space : Space} (free : EquationFree space)
    (registry : Registry) (capture : Capture Key (List Atom)) (handle : Handle)
    (world : RevisionEnvironment Key (List Atom)) (sourceKey : Key)
    (sourceRead : capture.view.captured.current sourceKey = space.atoms)
    (consulted : sourceKey ∈ capture.view.consulted)
    (matchesOwner : Matches capture handle) (current : capture.view.CanPublish world)
    (authorized : Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated registry handle)
    (history : NativeArgumentControlHistory.HistoryInv capture.capture)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : capture.capture.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : AtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    ∃ budget after next,
      world.current sourceKey = space.atoms ∧
      collectReply space prepared.bound prepared.domain argument.env fuel budget = some (replies argument.env heads) ∧
      (deliverChecked registry world capture handle
        ⟨(NativeArgumentControl.request capture.capture (.evaluate argument prepared) ticket).endpoint,
          .evaluated (replies argument.env heads), charge⟩).1 = .ok (after, next) ∧
      NativeArgumentControlHistory.HistoryInv after ∧
      (∀ result ∈ replies argument.env heads,
        EvalAtomRawRel space noHost [] prepared.bound prepared.domain argument.env result) := by
  obtain ⟨budget, after, collected, delivered, retained, _, sound⟩ :=
    deliver_nonleaf free capture.capture history argument prepared ticket rest pending fuel charge heads derivation
  obtain ⟨next, cleared, released⟩ :=
    (Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_exists_iff registry handle).mpr authorized
  have sameSource := (CapturedReadView.valid_dependencies_iff capture.view world).mp current.2.2
    sourceKey (List.mem_toFinset.mpr consulted)
  exact ⟨budget, after, next, sameSource.trans sourceRead, collected,
    (deliverChecked_iff _ _ _ _ _ _ _).mpr ⟨matchesOwner, current, delivered, cleared, released⟩,
    retained, sound⟩

end OwnedReplies

/-- Operational child occurrences, including their exact bindings. These
receipts are not committed external effects or native ownership authority. -/
def sourceEvent (result : ResultPair) : Atom :=
  .expression [.symbol "he-source-result", result.1, TypedApplyEncoding.bindingsData result.2]

/-- Read the exact value and binding frame of an operational child receipt. -/
def readSourceEvent : Atom → Option ResultPair
  | .expression [.symbol "he-source-result", value, bindings] => do
      return (value, ← TypedApplyEncoding.readBindings bindings)
  | _ => none

@[simp] theorem readSourceEvent_sourceEvent (result : ResultPair) :
    readSourceEvent (sourceEvent result) = some result := by
  rcases result with ⟨value, bindings⟩
  simp [sourceEvent, readSourceEvent]

theorem sourceEvent_injective : Function.Injective sourceEvent := by
  intro left right equal
  have decoded := congrArg readSourceEvent equal
  simpa only [readSourceEvent_sourceEvent, Option.some.injEq] using decoded

/-- Decoding the ordered service log recovers every original occurrence,
including duplicates and every binding equality. -/
theorem read_sourceEvents (results : ResultSet) :
    (results.map sourceEvent).mapM readSourceEvent = some results := by
  induction results with
  | nil => rfl
  | cons result results ih => simp [ih]

def evaluationReply (endpoint : Atom) (charge : Nat) (finished : RecursiveTasks.Configuration) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Reply Atom Atom :=
  .returned (NativeArgumentControlEncoding.replyData
    ⟨endpoint, .evaluated finished.emitted, charge⟩)

/-- The service is the existing worker with event/verdict labels adapted to
the callback protocol. Its state and every transition kind remain unchanged. -/
def evaluationService (endpoint : Atom) (charge : Nat) :
    Machine RecursiveTasks.Configuration Atom
      (Mettapedia.GSLT.Distinction.ProductiveBlocks.Reply Atom Atom) Empty :=
  (machine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

/-- Event adaptation changes neither the saved worker nor its transition
charges. It does not account for internal native or external service work. -/
theorem evaluationService_spent (endpoint : Atom) (charge : Nat)
    (price : RecursiveTasks.Configuration → Nat) (budget : Nat) (initial : RecursiveTasks.Configuration) :
    (evaluationService endpoint charge).spent price budget initial =
      (machine HE.GroundedDispatch.none).spent price budget initial :=
  (machine HE.GroundedDispatch.none).spent_relabel sourceEvent (evaluationReply endpoint charge) id
    price budget initial

/-- The service protocol uses the already constructed lossless worker codec.
Both simulations retain actual represented residuals; the verdict adaptation
does not install an assumed source/native correspondence. -/
theorem evaluationService_forward (endpoint : Atom) (charge : Nat) :
    CostSimulation (evaluationService endpoint charge)
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      Represents 1 :=
  (forwardSimulation HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

theorem evaluationService_backward (endpoint : Atom) (charge : Nat) :
    CostSimulation
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      (evaluationService endpoint charge) (fun represented actual => Represents actual represented) 1 :=
  (backwardSimulation HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

theorem AtomDerivation.service_completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later, (evaluationService endpoint charge).run (budget + later)
      ⟨space, .work (.atom value expected bindings fuel), [], []⟩ =
      ((replies bindings heads).map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated (replies bindings heads), charge⟩))) := by
  obtain ⟨budget, complete⟩ := derivation.completed free []
  refine ⟨budget, fun later => ?_⟩
  rw [evaluationService, Machine.run_relabel, complete later]
  rfl

theorem AtomDerivation.encoded_service_completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : AtomDerivation space bindings value expected fuel heads) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later,
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id).run
        (budget + later) (RecursiveEncoding.configurationData
          ⟨space, .work (.atom value expected bindings fuel), [], []⟩) =
      ((replies bindings heads).map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated (replies bindings heads), charge⟩))) := by
  obtain ⟨budget, complete⟩ := derivation.encoded_completed free []
  refine ⟨budget, fun later => ?_⟩
  rw [Machine.run_relabel, complete later]
  rfl

/-- An earned nonleaf evaluation composes with the existing retained caller
through the common resumable handler. The bound is derived for this input,
and includes call, worker occurrences and reply. The caller returns at the
accepted endpoint with its actual saved continuation intact. -/
theorem handled_nonleaf {space : Space} (free : EquationFree space)
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : AtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated (replies argument.env heads), charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel), [], []⟩
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations policy).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)).run
        budget (.running (.active configuration)) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        (replies argument.env heads).map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) := by
  dsimp only
  let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
  let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated (replies argument.env heads), charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
  let initial : RecursiveTasks.Configuration :=
    ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel), [], []⟩
  have call : (NativeArgumentControlMachine.interactionMachine operations policy).step (.active configuration) =
      some (.call endpoint (.active configuration)) := by
    simp only [NativeArgumentControlMachine.interactionMachine,
      NativeArgumentControlMachine.inspectInteraction,
      NativeArgumentControlMachine.awaiting_preserves operations configuration (.evaluate argument prepared)
        ticket rest pending, NativeArgumentControlMachine.interactionAdvance, endpoint]
  obtain ⟨bound, completed⟩ := derivation.service_completed free endpoint charge
  have answered : (evaluationService endpoint charge).run bound initial =
      ((replies argument.env heads).map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData reply))) := by
    simpa only [Nat.add_zero, initial, reply] using completed 0
  obtain ⟨used, _, ran⟩ := (NativeArgumentControlMachine.interactionMachine operations policy).handle_call_run
    NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)
    (.active configuration) (.active configuration) endpoint call bound
    ((replies argument.env heads).map sourceEvent) (.returned (NativeArgumentControlEncoding.replyData reply)) answered
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      (replies argument.env heads) charge pending
  exact ⟨used, by simpa only [NativeArgumentControlEncoding.interactionCallback,
    NativeArgumentControlEncoding.resumeInteraction, NativeArgumentControlEncoding.readReply_replyData,
    accepted] using ran⟩

/-- Both sides of the actual interaction are represented here: the saved
caller uses its checked packet interface, and the service uses the existing
recursive configuration codec. The ordered source reply still comes from
the independently earned derivation, rather than a packet fixture. -/
theorem handled_nonleaf_encoded {space : Space} (free : EquationFree space)
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : AtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated (replies argument.env heads), charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel), [], []⟩
    ∃ budget, ((NativeArgumentControlEncoding.interactionDataMachine operations policy).handle
      NativeArgumentControlEncoding.representedCallback
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      (fun _ => RecursiveEncoding.configurationData initial)).run budget
        (.running (NativeArgumentControlMachine.interactionData (.active configuration))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        (replies argument.env heads).map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (NativeArgumentControlMachine.interactionData (.active after)))) := by
  dsimp only
  let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
  let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated (replies argument.env heads), charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
  let initial : RecursiveTasks.Configuration :=
    ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel), [], []⟩
  have call : (NativeArgumentControlMachine.interactionMachine operations policy).step (.active configuration) =
      some (.call endpoint (.active configuration)) := by
    simp only [NativeArgumentControlMachine.interactionMachine,
      NativeArgumentControlMachine.inspectInteraction,
      NativeArgumentControlMachine.awaiting_preserves operations configuration (.evaluate argument prepared)
        ticket rest pending, NativeArgumentControlMachine.interactionAdvance, endpoint]
  have encodedCall : (NativeArgumentControlEncoding.interactionDataMachine operations policy).step
      (NativeArgumentControlMachine.interactionData (.active configuration)) =
      some (.call endpoint (NativeArgumentControlMachine.interactionData (.active configuration))) := by
    rw [NativeArgumentControlEncoding.interaction_step_encoded, call]
    rfl
  obtain ⟨bound, completed⟩ := derivation.encoded_service_completed free endpoint charge
  have answered :
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id).run
        bound (RecursiveEncoding.configurationData initial) =
      ((replies argument.env heads).map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData reply))) := by
    simpa only [Nat.add_zero, initial, reply] using completed 0
  obtain ⟨used, _, ran⟩ := (NativeArgumentControlEncoding.interactionDataMachine operations policy).handle_call_run
    NativeArgumentControlEncoding.representedCallback
    ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
    (fun _ => RecursiveEncoding.configurationData initial)
    (NativeArgumentControlMachine.interactionData (.active configuration))
    (NativeArgumentControlMachine.interactionData (.active configuration)) endpoint encodedCall bound
    ((replies argument.env heads).map sourceEvent) (.returned (NativeArgumentControlEncoding.replyData reply)) answered
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      (replies argument.env heads) charge pending
  have represented := (NativeArgumentControlEncoding.represented_reply_accepted_iff configuration after reply).mpr
    ((NativeArgumentControl.deliver_iff configuration reply after).mp accepted)
  exact ⟨used, by simpa only [NativeArgumentControlEncoding.representedCallback, represented] using ran⟩


section Controls

private def heldSyntax : Atom :=
  .expression [.symbol "quote", .expression [.symbol "Pair", .var "shared", .var "shared"]]
private def innerSyntax : Atom := .expression [.symbol "inner", heldSyntax]
private def outerSyntax : Atom := .expression [.symbol "outer", innerSyntax]
private def numberType : Atom := .symbol "Number"
private def booleanType : Atom := .symbol "Bool"
private def textType : Atom := .symbol "Text"
private def sourceSpace : Space := ⟨[
  .expression [.symbol ":", .symbol "inner", arrow [Atom.atomType] numberType],
  .expression [.symbol ":", .symbol "outer", arrow [textType] numberType],
  .expression [.symbol ":", .symbol "outer", arrow [numberType] booleanType],
  .expression [.symbol ":", .symbol "outer", arrow [numberType] numberType],
  .expression [.symbol ":", heldSyntax, numberType],
  .expression [.symbol ":", heldSyntax, booleanType],
  .expression [.symbol ":", innerSyntax, numberType],
  .expression [.symbol ":", innerSyntax, numberType],
  .expression [.symbol ":", innerSyntax, booleanType]]⟩

private theorem source_free : EquationFree sourceSpace := by
  intro left right
  simp [sourceSpace]

private def controlFuel : Nat := 4096

private theorem inner_type_occurrences :
    getAtomTypes sourceSpace innerSyntax = [numberType, numberType, booleanType] := by decide

private theorem control_argument_checked (domain : Atom)
    (closed : TypeSubst.typeVars domain = [])
    (numberBudget : sizeOf domain + sizeOf numberType + 2 ≤ controlFuel + 6)
    (booleanBudget : sizeOf domain + sizeOf booleanType + 2 ≤ controlFuel + 6) :
    ArgumentDomainEvidence sourceSpace innerSyntax domain (controlFuel + 6) := by
  refine .closed closed ?_ ?_
  · intro actual member
    rw [inner_type_occurrences] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro actual member
    rw [inner_type_occurrences] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact numberBudget
    · exact numberBudget
    · exact booleanBudget

private def innerTyping : ApplicationTyping sourceSpace "inner" [heldSyntax] numberType (controlFuel + 2) where
  domains := [Atom.atomType]
  returned := numberType
  before := []
  after := []
  declined := []
  sourceTypes := by decide
  rejected := .nil
  argumentChecks := .cons (.wildcard (Or.inl rfl)) .nil
  argumentPaths := by decide
  expectedClosed := rfl
  returnedClosed := rfl
  returnedFits := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  returnBudget := by decide
  earlierClosed := by simp
  earlierHeadRejects := by simp
  headClosed := rfl
  headBudget := by decide
  demandNotRaw := by decide
  demandNotExpression := by decide
  nonemptyOperator := by decide
  cleanOperator := by decide
  ordinaryOperator := by decide

private def outerTyping : ApplicationTyping sourceSpace "outer" [innerSyntax] numberType (controlFuel + 6) where
  domains := [numberType]
  returned := numberType
  before := [arrow [textType] numberType, arrow [numberType] booleanType]
  after := []
  declined := [⟨arrow [textType] numberType,
    .error [mkError outerSyntax (.badArgType 1 textType numberType)]⟩,
    ⟨arrow [numberType] booleanType,
    .error [mkError outerSyntax (.badType numberType booleanType)]⟩]
  sourceTypes := by decide
  rejected := .badArguments (.cons (control_argument_checked textType rfl (by decide) (by decide)) .nil)
    (by decide) (by decide)
    (.badReturn (.cons (control_argument_checked numberType rfl (by decide) (by decide)) .nil)
      (by decide) rfl rfl (by decide) .nil)
  argumentChecks := .cons (control_argument_checked numberType rfl (by decide) (by decide)) .nil
  argumentPaths := by decide
  expectedClosed := rfl
  returnedClosed := rfl
  returnedFits := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  returnBudget := by decide
  earlierClosed := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  earlierHeadRejects := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  headClosed := rfl
  headBudget := by decide
  demandNotRaw := by decide
  demandNotExpression := by decide
  nonemptyOperator := by decide
  cleanOperator := by decide
  ordinaryOperator := by decide

/-- The two repeated quote variables remain raw syntax under Atom demand,
for any retained binding frame. -/
theorem source_quote_is_held (bindings : Bindings) :
    AtomDerivation sourceSpace bindings heldSyntax Atom.atomType (controlFuel + 1) [heldSyntax] :=
  .leaf heldSyntax Atom.atomType controlFuel (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩)

private theorem inner_derivation (bindings : Bindings) :
    AtomDerivation sourceSpace bindings innerSyntax numberType (controlFuel + 5) [innerSyntax, innerSyntax] := by
  have arguments : ArgsDerivation sourceSpace bindings [heldSyntax] [Atom.atomType] (controlFuel + 2) [[heldSyntax]] := by
    simpa using ArgsDerivation.cons heldSyntax Atom.atomType [] [] (controlFuel + 1) [heldSyntax] [[]]
      (source_quote_is_held bindings) (.nil controlFuel)
  have derived := AtomDerivation.application "inner" [heldSyntax] numberType (controlFuel + 2) innerTyping
    [[heldSyntax]] arguments
  have count : admittedPathCount sourceSpace [heldSyntax] innerTyping.domains = 2 := by decide
  simpa only [count, List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
    List.map_cons, List.map_nil, List.append_nil, List.singleton_append, Nat.add_assoc, innerSyntax] using derived

/-- Four interpreted occurrences are earned by nested source evaluation.
The outer argument rejects its Bool occurrence and retains both Number
occurrences. Earlier Text-domain and Bool-return candidates are independently
declined before the Number arrow is selected. Quoted fields remain raw. -/
theorem nested_nonleaf_derivation (bindings : Bindings) :
    AtomDerivation sourceSpace bindings outerSyntax numberType (controlFuel + 9)
      [outerSyntax, outerSyntax, outerSyntax, outerSyntax] := by
  have arguments : ArgsDerivation sourceSpace bindings [innerSyntax] [numberType] (controlFuel + 6)
      [[innerSyntax], [innerSyntax]] := by
    simpa using ArgsDerivation.cons innerSyntax numberType [] [] (controlFuel + 5)
      [innerSyntax, innerSyntax] [[]] (inner_derivation bindings) (.nil (controlFuel + 4))
  have derived := AtomDerivation.application "outer" [innerSyntax] numberType (controlFuel + 6) outerTyping
    [[innerSyntax], [innerSyntax]] arguments
  have count : admittedPathCount sourceSpace [innerSyntax] outerTyping.domains = 2 := by decide
  simpa only [count, List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
    List.map_cons, List.map_nil, List.append_nil, List.singleton_append, List.cons_append, List.nil_append, Nat.add_assoc, outerSyntax] using derived

theorem earlier_typed_candidate_rejected (bindings output : Bindings) :
    ¬ApplicationSuccessRel sourceSpace outerSyntax (arrow [numberType] booleanType)
      numberType bindings output :=
  closed_return_excludes_success sourceSpace (.symbol "outer") numberType booleanType [innerSyntax]
    [numberType] bindings output rfl rfl (by decide)

theorem earlier_argument_candidate_rejected (bindings output : Bindings) :
    ¬ApplicationSuccessRel sourceSpace outerSyntax (arrow [textType] numberType)
      numberType bindings output :=
  checked_arguments_exclude_success sourceSpace (.symbol "outer") numberType numberType [innerSyntax]
    [textType] bindings output (controlFuel + 6)
    (.cons (control_argument_checked textType rfl (by decide) (by decide)) .nil) (by decide)

theorem checked_duplicate_paths_are_retained (bindings : Bindings) :
    getAtomTypes sourceSpace innerSyntax = [numberType, numberType, booleanType] ∧
    acceptedTypes sourceSpace innerSyntax numberType = [numberType, numberType] ∧
    checkIfFunctionTypeIsApplicable outerSyntax (arrow [numberType] numberType) numberType
      sourceSpace bindings (controlFuel + 7) = .inr [bindings, bindings] := by
  refine ⟨inner_type_occurrences, by decide, ?_⟩
  have checked := checked_applicability_success sourceSpace (.symbol "outer") numberType numberType
    [innerSyntax] [numberType] bindings (controlFuel + 6)
    (.cons (control_argument_checked numberType rfl (by decide) (by decide)) .nil)
    (by decide) rfl rfl (by decide) (by decide)
  have count : admittedPathCount sourceSpace [innerSyntax] [numberType] = 2 := by decide
  simpa only [count, List.replicate_succ, List.replicate_zero, outerSyntax, arrow, Nat.add_assoc] using checked

theorem rejected_argument_errors_keep_duplicates (bindings : Bindings) :
    checkIfFunctionTypeIsApplicable outerSyntax (arrow [textType] numberType) numberType
      sourceSpace bindings (controlFuel + 7) = .inl [
        mkError outerSyntax (.badArgType 1 textType numberType),
        mkError outerSyntax (.badArgType 1 textType numberType),
        mkError outerSyntax (.badArgType 1 textType booleanType)] := by
  have checked := checked_applicability_argument_failure sourceSpace (.symbol "outer") numberType numberType
    [innerSyntax] [textType] bindings (controlFuel + 6)
    (.cons (control_argument_checked textType rfl (by decide) (by decide)) .nil) (by decide)
  have errors : argumentErrorBlocks sourceSpace outerSyntax [innerSyntax] [textType] 1 1 = [
      mkError outerSyntax (.badArgType 1 textType numberType),
      mkError outerSyntax (.badArgType 1 textType numberType),
      mkError outerSyntax (.badArgType 1 textType booleanType)] := by decide
  change checkIfFunctionTypeIsApplicable outerSyntax (arrow [textType] numberType) numberType
    sourceSpace bindings (controlFuel + 6 + 1) =
      .inl (argumentErrorBlocks sourceSpace outerSyntax [innerSyntax] [textType] 1 1) at checked
  rw [errors] at checked
  simpa only [Nat.add_assoc] using checked

/-- Errors from an earlier mixed argument precede the later argument's
errors. The two surviving Number paths repeat the second argument's whole
error block, with its original one-based position. Each occurrence has an
independent rejection derivation. -/
theorem argument_errors_follow_surviving_paths (bindings : Bindings) :
    let expression : Atom := .expression [.symbol "outer", innerSyntax, heldSyntax]
    let errors := [mkError expression (.badArgType 1 numberType booleanType),
      mkError expression (.badArgType 2 textType numberType),
      mkError expression (.badArgType 2 textType booleanType),
      mkError expression (.badArgType 2 textType numberType),
      mkError expression (.badArgType 2 textType booleanType)]
    checkIfFunctionTypeIsApplicable expression (arrow [numberType, textType] numberType) numberType
      sourceSpace bindings (controlFuel + 7) = .inl errors ∧
    ∀ error ∈ errors, ApplicabilityRel sourceSpace expression (arrow [numberType, textType] numberType)
      numberType bindings (.error error) := by
  let expression : Atom := .expression [.symbol "outer", innerSyntax, heldSyntax]
  let errors := [mkError expression (.badArgType 1 numberType booleanType),
    mkError expression (.badArgType 2 textType numberType),
    mkError expression (.badArgType 2 textType booleanType),
    mkError expression (.badArgType 2 textType numberType),
    mkError expression (.badArgType 2 textType booleanType)]
  have heldTypes : getAtomTypes sourceSpace heldSyntax = [numberType, booleanType] := by decide
  have heldChecked : ArgumentDomainEvidence sourceSpace heldSyntax textType (controlFuel + 6) := by
    refine .closed rfl ?_ ?_
    · intro actual member
      rw [heldTypes] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    · intro actual member
      rw [heldTypes] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide
  have checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence sourceSpace argument domain (controlFuel + 6))
      [innerSyntax, heldSyntax] [numberType, textType] :=
    .cons (control_argument_checked numberType rfl (by decide) (by decide)) (.cons heldChecked .nil)
  have exhausted : admittedPathCount sourceSpace [innerSyntax, heldSyntax] [numberType, textType] = 0 := by decide
  have orderedErrors : argumentErrorBlocks sourceSpace expression [innerSyntax, heldSyntax]
      [numberType, textType] 1 1 = errors := by decide
  constructor
  · have result := checked_applicability_argument_failure sourceSpace (.symbol "outer") numberType numberType
      [innerSyntax, heldSyntax] [numberType, textType] bindings (controlFuel + 6) checked exhausted
    change checkIfFunctionTypeIsApplicable expression (arrow [numberType, textType] numberType) numberType
      sourceSpace bindings (controlFuel + 6 + 1) =
        .inl (argumentErrorBlocks sourceSpace expression [innerSyntax, heldSyntax] [numberType, textType] 1 1) at result
    rw [orderedErrors] at result
    simpa only [Nat.add_assoc] using result
  · intro error member
    have noSuccess : ∀ output, ¬ApplicationSuccessRel sourceSpace expression
        (arrow [numberType, textType] numberType) numberType bindings output :=
      fun output => checked_arguments_exclude_success sourceSpace (.symbol "outer") numberType numberType
        [innerSyntax, heldSyntax] [numberType, textType] bindings output (controlFuel + 6) checked exhausted
    exact checked_argument_errors_sound sourceSpace (.symbol "outer") numberType numberType
      [innerSyntax, heldSyntax] [numberType, textType] bindings (controlFuel + 6) checked noSuccess error
      (orderedErrors ▸ member)

theorem nested_source_collects_four (bindings : Bindings) :
    ∃ budget, collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget =
      some [(outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings)] := by
  obtain ⟨budget, complete⟩ := (nested_nonleaf_derivation bindings).collect source_free
  exact ⟨budget, by simpa only [Nat.add_zero, replies, List.map_cons, List.map_nil] using complete 0⟩

theorem nested_independent_result (bindings : Bindings) :
    EvalAtomRawRel sourceSpace noHost [] outerSyntax numberType bindings (outerSyntax, bindings) :=
  (nested_nonleaf_derivation bindings).sound source_free outerSyntax (by simp) []

private def requestSubstitution : TypeSubst := [("request", outerSyntax)]
private def unresolvedArgument : TypedApplyState :=
  ⟨.symbol "caller", [.var "request"], [numberType], 0, [],
    FirstSuccessPreparedArguments.presentedBindings requestSubstitution⟩
private def resolvedArgument : NativeArgumentControl.Prepared :=
  ⟨numberType, outerSyntax, {dialect := .he}⟩

/-- A stored nested argument is resolved from an actual normal substitution
before interpretation. Its still-unassigned raw quote variables and original
source argument remain in the retained state. -/
theorem stored_nested_argument_is_prepared :
    FirstSuccessPreparedArguments.prepareSource unresolvedArgument {dialect := .he} 8 = resolvedArgument ∧
    FirstSuccessPreparedArguments.PreparationRel requestSubstitution unresolvedArgument {dialect := .he}
      resolvedArgument ∧
    ∃ budget, collectReply sourceSpace outerSyntax numberType unresolvedArgument.env
      (controlFuel + 9) budget =
        some (replies unresolvedArgument.env [outerSyntax, outerSyntax, outerSyntax, outerSyntax]) := by
  have normal : requestSubstitution.Normal := by
    simp [requestSubstitution, TypeSubst.Normal, TypeSubst.keys, TypeSubst.typeVars,
      TypeSubst.typeVarsList, outerSyntax, innerSyntax, heldSyntax]
  have prepared : FirstSuccessPreparedArguments.prepareSource unresolvedArgument {dialect := .he} 8 =
      resolvedArgument := rfl
  have independent := FirstSuccessPreparedArguments.preparation_sound normal unresolvedArgument {dialect := .he}
    8 rfl (by decide) (by decide)
  rw [prepared] at independent
  obtain ⟨budget, collected⟩ := (nested_nonleaf_derivation unresolvedArgument.env).collect source_free
  exact ⟨prepared, independent, budget, by simpa only [Nat.add_zero] using collected 0⟩

/-- A support-only collector loses three earned occurrences. -/
theorem collapsed_reply_is_incomplete (bindings : Bindings) :
    replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax] ≠ [(outerSyntax, bindings)] := by
  intro same
  have lengths := congrArg List.length same
  simp [replies] at lengths

/-- The actual collector never certifies the collapsed support-only reply at
any work budget, including budgets that end before source completion. -/
theorem collector_cannot_collapse (bindings : Bindings) (budget : Nat) :
    collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget ≠
      some [(outerSyntax, bindings)] := by
  intro collapsed
  exact collapsed_reply_is_incomplete bindings
    ((nested_nonleaf_derivation bindings).collect_exact source_free budget [(outerSyntax, bindings)] collapsed).symm

/-- Demand changes the interpretation boundary. The same nested value under
Atom demand returns one held occurrence instead of four interpreted ones. -/
theorem raw_demand_is_different (bindings : Bindings) :
    AtomDerivation sourceSpace bindings outerSyntax Atom.atomType (controlFuel + 9) [outerSyntax] ∧
      replies bindings [outerSyntax] ≠ replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax] := by
  refine ⟨.leaf outerSyntax Atom.atomType (controlFuel + 8) (Or.inr
    ⟨Atom.expressionType, .expression _, Or.inl rfl⟩), ?_⟩
  intro same
  have lengths := congrArg List.length same
  simp [replies] at lengths

/-- Budget exhaustion is retained, not an earned empty or singleton reply. -/
theorem zero_budget_is_pending (bindings : Bindings) :
    collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) 0 = none := rfl

/-- A pause after the first duplicate resumes exactly the remaining three.
The complete saved worker includes its already published first occurrence. -/
theorem duplicate_prefix_resumes (bindings : Bindings) :
    ∃ firstBudget remainingBudget saved,
      (machine HE.GroundedDispatch.none).run firstBudget
        ⟨sourceSpace, .work (.atom outerSyntax numberType bindings (controlFuel + 9)), [], []⟩ =
        ([(outerSyntax, bindings)], .exhausted saved) ∧
      (machine HE.GroundedDispatch.none).run remainingBudget saved =
        ([(outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings)],
          .finished ⟨sourceSpace, .returning [], [],
            [(outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings)]⟩) := by
  obtain ⟨administrative, realized⟩ := (machine HE.GroundedDispatch.none).silent_run
    ((nested_nonleaf_derivation bindings).realizes source_free [] [])
  let saved : RecursiveTasks.Configuration := ⟨sourceSpace,
    .returning [(outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings)], [], [(outerSyntax, bindings)]⟩
  refine ⟨administrative + 1, 4, saved, ?_, ?_⟩
  · rw [realized 1]
    rfl
  · simpa only [List.length_cons, List.length_nil, List.append_assoc, List.singleton_append] using
      drain_returning sourceSpace
        [(outerSyntax, bindings), (outerSyntax, bindings), (outerSyntax, bindings)] [(outerSyntax, bindings)] 0


private def callerArgument (bindings : Bindings) : TypedApplyState :=
  ⟨.symbol "caller", [outerSyntax], [numberType], 0, [], bindings⟩
private def callerPrepared : NativeArgumentControl.Prepared :=
  ⟨numberType, outerSyntax, {dialect := .he}⟩
private def callerWaiting (bindings : Bindings) : NativeArgumentControl.Configuration :=
  NativeArgumentControl.issue ⟨[], [], 17, 0, [], 0⟩ []
    (.evaluate (callerArgument bindings) callerPrepared)

private theorem caller_history (bindings : Bindings) :
    NativeArgumentControlHistory.HistoryInv (callerWaiting bindings) :=
  NativeArgumentControlHistory.issue_history
    (NativeArgumentControlHistory.history_empty [] (by simp [NativeArgumentControlHistory.PlainFrames]) 17)
    [] (by simp [NativeArgumentControlHistory.PlainFrames]) _

/-- The complete nonleaf reply is earned by source rules before the endpoint
checker accepts it. Acceptance retains all four occurrences in the original
argument snapshot and preserves the serial/history invariant. -/
theorem earned_nonleaf_callback (bindings : Bindings) :
    ∃ budget after,
      collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget =
        some (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]) ∧
      NativeArgumentControl.DeliveryRel (callerWaiting bindings)
        ⟨(NativeArgumentControl.request (callerWaiting bindings)
          (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint,
          .evaluated (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]), 0⟩ after ∧
      NativeArgumentControlHistory.HistoryInv after := by
  obtain ⟨budget, after, collected, delivered, history, _, _⟩ :=
    deliver_nonleaf source_free (callerWaiting bindings) (caller_history bindings)
      (callerArgument bindings) callerPrepared 0 [] rfl (controlFuel + 9) 0
      [outerSyntax, outerSyntax, outerSyntax, outerSyntax] (nested_nonleaf_derivation bindings)
  exact ⟨budget, after, collected, delivered, history⟩

/-- The shared handler executes the real nested worker and resumes the exact
parent after its ordered four-occurrence service log. No fixture provider is
used to produce the duplicate replies. -/
theorem earned_nonleaf_handler (bindings : Bindings)
    (operations : NativeArgumentControl.Operations) :
    let endpoint := (NativeArgumentControl.request (callerWaiting bindings)
      (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint
    let reply : NativeArgumentControl.Reply :=
      ⟨endpoint, .evaluated (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]), 0⟩
    let after := NativeArgumentControl.replied (callerWaiting bindings) [] reply
      [.iterate (NativeArgumentControl.selectedSnapshot (callerArgument bindings) callerPrepared
        (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax])) callerPrepared]
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations .stop).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint 0)
      (fun _ => (⟨sourceSpace, .work (.atom outerSyntax numberType bindings (controlFuel + 9)), [], []⟩ :
        RecursiveTasks.Configuration))).run budget (.running (.active (callerWaiting bindings))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]).map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) :=
  handled_nonleaf source_free operations .stop (callerWaiting bindings) (callerArgument bindings)
    callerPrepared 0 [] rfl (controlFuel + 9) 0
    [outerSyntax, outerSyntax, outerSyntax, outerSyntax] (nested_nonleaf_derivation bindings)

private def capturedSourceWorld : Mettapedia.Machines.RevisionEnvironment Nat (List Atom) :=
  ⟨fun _ => sourceSpace.atoms⟩
private def capturedCaller (bindings : Bindings) :
    NativeArgumentControlHistory.OwnedReplyBoundary.Capture Nat (List Atom) :=
  ⟨5, (Mettapedia.Machines.CapturedReadView.admit capturedSourceWorld).consult capturedSourceWorld 0,
    callerWaiting bindings⟩
private def issuedCaller (bindings : Bindings) : NativeArgumentControlHistory.OwnedReplyBoundary.Handle :=
  ⟨19, 17, ⟨1, 11, NativeArgumentControl.configurationData (callerWaiting bindings), 5⟩⟩
private def callerRegistry (bindings : Bindings) : NativeArgumentControlHistory.OwnedReplyBoundary.Registry :=
  ⟨19, [(issuedCaller bindings).row]⟩

/-- The existing nested worker earns all four occurrences before the issued
reply boundary checks its complete source dependency and consumes its token. -/
theorem earned_nonleaf_owned_reply (bindings : Bindings) :
    ∃ budget after next,
      collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget =
        some (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]) ∧
      (NativeArgumentControlHistory.OwnedReplyBoundary.deliverChecked (callerRegistry bindings)
        capturedSourceWorld (capturedCaller bindings) (issuedCaller bindings)
        ⟨(NativeArgumentControl.request (callerWaiting bindings)
          (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint,
          .evaluated (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]), 0⟩).1 =
          .ok (after, next) ∧ NativeArgumentControlHistory.HistoryInv after := by
  have current : (capturedCaller bindings).view.CanPublish capturedSourceWorld := by
    refine ⟨rfl, rfl, ?_⟩
    apply (Mettapedia.Machines.CapturedReadView.valid_dependencies_iff _ _).mpr
    intro key _
    rfl
  have authority : Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated
      (callerRegistry bindings) (issuedCaller bindings) := by
    simp [Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated,
      callerRegistry, issuedCaller]
  obtain ⟨budget, after, next, _, collected, accepted, history, _⟩ :=
    deliver_nonleaf_owned source_free (callerRegistry bindings) (capturedCaller bindings)
      (issuedCaller bindings) capturedSourceWorld 0 rfl (by simp [capturedCaller,
        Mettapedia.Machines.CapturedReadView.consult, Mettapedia.Machines.CapturedReadView.admit])
      ⟨rfl, rfl, rfl⟩ current authority (caller_history bindings)
      (callerArgument bindings) callerPrepared 0 [] rfl (controlFuel + 9) 0
      [outerSyntax, outerSyntax, outerSyntax, outerSyntax] (nested_nonleaf_derivation bindings)
  exact ⟨budget, after, next, collected, accepted, history⟩

/-- An edited source cannot authorize the reply earned from the old admitted
source, even though that old reply remains a valid source derivation. -/
theorem edited_source_refuses_issued_nonleaf_reply (bindings : Bindings) :
    let changed : Mettapedia.Machines.RevisionEnvironment Nat (List Atom) :=
      ⟨fun _ => sourceSpace.atoms ++ [.symbol "added-declaration"]⟩
    (NativeArgumentControlHistory.OwnedReplyBoundary.deliverChecked (callerRegistry bindings)
      changed (capturedCaller bindings) (issuedCaller bindings)
      ⟨(NativeArgumentControl.request (callerWaiting bindings)
        (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint,
        .evaluated (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]), 0⟩).1 =
          .error .staleDependencies := by
  apply NativeArgumentControlHistory.OwnedReplyBoundary.stale_refused
  · exact ⟨rfl, rfl, rfl⟩
  · intro allowed
    have reads := (Mettapedia.Machines.CapturedReadView.valid_dependencies_iff _ _).mp allowed.2.2
      0 (by simp [capturedCaller, Mettapedia.Machines.CapturedReadView.consult,
        Mettapedia.Machines.CapturedReadView.admit])
    have impossible := congrArg List.length reads
    simp [capturedCaller, capturedSourceWorld, Mettapedia.Machines.CapturedReadView.consult,
      Mettapedia.Machines.CapturedReadView.admit] at impossible

private def mismatchedPrepared : NativeArgumentControl.Prepared :=
  ⟨booleanType, outerSyntax, {dialect := .he}⟩
private def mismatchedReply (bindings : Bindings) : NativeArgumentControl.Reply :=
  ⟨(NativeArgumentControl.request (callerWaiting bindings)
      (.evaluate (callerArgument bindings) mismatchedPrepared) 0).endpoint,
    .evaluated (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]), 7⟩

/-- Results earned at a different resolved demand cannot be spliced into the
saved request, even though their represented values coincide. -/
theorem mismatched_domain_refused (bindings : Bindings) :
    NativeArgumentControl.deliver (callerWaiting bindings) (mismatchedReply bindings) =
      .rejected .endpointMismatch := by
  have different : (mismatchedReply bindings).endpoint ≠
      (NativeArgumentControl.request (callerWaiting bindings)
        (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint := by
    intro same
    simp [mismatchedReply, NativeArgumentControl.request, NativeArgumentControl.waitingData,
      NativeArgumentControl.preparedData, callerPrepared, mismatchedPrepared, numberType, booleanType] at same
  simp only [NativeArgumentControl.deliver,
    show (callerWaiting bindings).frames =
      .waiting (.evaluate (callerArgument bindings) callerPrepared) 0 :: [] from rfl]
  rw [if_pos different]

/-- Refusal retains the entire controller and does not consume the forged
charge, fresh serial or reply history. -/
theorem mismatched_callback_retains_state (bindings : Bindings) :
    NativeArgumentControlEncoding.resumeInteraction
      (.active (callerWaiting bindings))
      (.returned (NativeArgumentControlEncoding.replyData (mismatchedReply bindings))) =
      .refused .endpointMismatch (callerWaiting bindings)
        (NativeArgumentControlEncoding.replyData (mismatchedReply bindings)) :=
  (NativeArgumentControlEncoding.rejected_reply_retains_saved
    (callerWaiting bindings) (mismatchedReply bindings) .endpointMismatch
    (mismatched_domain_refused bindings)).1

end Controls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
