import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.ProofRunExecution
import Mettapedia.Languages.MM0.MeTTa.Kernel.Proof

/-!
# Binary theorem resolution and instantiated premise checking

The binary frontend uses the existing MMU theorem resolver and original MM0
proof checker. This module earns those source operations under the loaded MMB
program. Lookup retains its preceding binding history; proof checking validates
every supplied witness and each instantiated premise in its original order.

The complete `proof-theorem` branch additionally needs binary signature
construction, stack consumption, structural matching and chronological proof
recording. A stored `MMBProved` constructor does not by itself supply the
witness-validation premises of these laws.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)
open Store (natural)
open ListAccess (listValue optionValue)
open Kernel (Context Preterm ProofWitness TheoremDecl TheoremInstance)
open Presentation.ComputationalTyping (signatureOf)

abbrev program := MMBProofRunExecution.program

/-- The original resolver state, retaining every namespace and counter. -/
def resolverValue (published sorts terms : Atom) (theorems : List MMUResolution.Binding)
    (nextSort nextTerm nextTheorem : Nat) (images : Atom) : Atom :=
  .expression [.symbol "MM0:MMUState", published, sorts, terms, MMUResolution.bindingsValue theorems,
    natural nextSort, natural nextTerm, natural nextTheorem, images]

private def resolverHead (head : String) : Bool :=
  (MMUResolution.checkerHead head && !head.startsWith "mm0:mmb:") ||
    head == "mm0:mmu:lookup" || head == "mm0:mmu:theorem"

private theorem resolver_closed : ProgramClosed resolverHead MMUResolution.program := by
  constructor
  · decide
  · intro equation member supported
    have checked : MMUResolution.program.equations.all (fun equation =>
        !resolverHead equation.head || codeWithin resolverHead equation.body) = true := by
      decide +kernel
    have body := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using body

private theorem resolver_agreement :
    ProgramAgreementOn resolverHead MMUResolution.program program := by
  change ProgramAgreementOn resolverHead MMUResolution.program
    (MMUResolution.program.append MMBExecution.binarySource.program)
  apply appended_program_agreement
  · intro equation member
    have checked : MMBExecution.binarySource.program.equations.all
        (fun equation => !resolverHead equation.head) = true := by decide +kernel
    have fresh := List.all_eq_true.mp checked equation member
    cases result : resolverHead equation.head <;> simp_all
  · intro head types member
    have checked : MMBExecution.binarySource.program.declarations.all
        (fun declaration => match declaration with
          | .expression [.symbol ":", .symbol name, .expression (.symbol "->" :: _)] =>
              !resolverHead name
          | _ => true) = true := by decide +kernel
    have fresh := List.all_eq_true.mp checked _ member
    cases result : resolverHead head <;> simp_all

private theorem resolver_path {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin resolverHead code = true)
    (returned : PureReturns MMUResolution.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement resolver_closed resolver_agreement ⟨supported, rfl⟩ returned

private def equation : SpaceSemantics.Equation :=
  ((MMUResolution.resolverSource.program.equations.filter (·.head == "mm0:mmu:theorem")).head?).getD
    ⟨"", [], .symbol "None"⟩
private def environment (published sorts terms : Atom) (theorems : List MMUResolution.Binding)
    (nextSort nextTerm nextTheorem : Nat) (images key : Atom) : Subst :=
  [("name", key), ("images", images), ("nh", natural nextTheorem), ("nt", natural nextTerm),
    ("ns", natural nextSort), ("theorems", MMUResolution.bindingsValue theorems),
    ("terms", terms), ("sorts", sorts), ("public", published)]
private theorem unique : program.equations.filter (·.head == "mm0:mmu:theorem") = [equation] := by decide +kernel
private theorem formals : equation.arguments =
    [.expression [.symbol "MM0:MMUState", .var "public", .var "sorts", .var "terms", .var "theorems",
      .var "ns", .var "nt", .var "nh", .var "images"], .var "name"] := by decide
private theorem body_shape : equation.body =
    .expression [.symbol "mm0:mmu:lookup", .var "theorems", .var "name"] := by decide
private theorem clause (published sorts terms : Atom) (theorems : List MMUResolution.Binding)
    (nextSort nextTerm nextTheorem : Nat) (images key : Atom) :
    clauses program "mm0:mmu:theorem"
      [resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images, key] =
      [.evaluate (environment published sorts terms theorems nextSort nextTerm nextTheorem images key) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    Subst.lookup, resolverValue, environment]

/-- The actual resolver uses its supplied chronological bindings. Captured
published metadata cannot expose a name absent from that history. -/
theorem theorem_lookup_returns (bindings : Subst) (state : State) (published sorts terms : Atom)
    (theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (images key : Atom) (resolverName keyName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (keyCaptured : applySubst bindings (.var keyName) = key) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:theorem", .var resolverName, .var keyName]) state
      (optionValue (MMUResolution.lookup theorems key)) := by
  let inner := environment published sorts terms theorems nextSort nextTerm nextTheorem images key
  have returned : PureReturns program inner state equation.body state
      (optionValue (MMUResolution.lookup theorems key)) := by
    rw [body_shape]
    apply resolver_path (by decide +kernel)
    apply MMUResolution.lookup_captured_returns inner state theorems key "theorems" "name"
    all_goals simp [inner, environment, applySubst, Subst.lookup]
  apply authored_variable_call_returns program bindings inner state state "mm0:mmu:theorem"
    [resolverName, keyName] equation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    _ returned (by decide)
  simpa [resolverCaptured, keyCaptured] using clause published sorts terms theorems nextSort nextTerm nextTheorem images key

/-- The original lookup is also exact when a selected name is unavailable. -/
theorem theorem_lookup_missing_returns (bindings : Subst) (state : State) (published sorts terms : Atom)
    (theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat)
    (images key : Atom) (resolverName keyName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (missing : MMUResolution.lookup theorems key = none) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:mmu:theorem", .var resolverName, .var keyName]) state (.symbol "None") := by
  simpa [missing, optionValue] using theorem_lookup_returns bindings state published sorts terms theorems
    nextSort nextTerm nextTheorem images key resolverName keyName resolverCaptured keyCaptured

/-- Checking complete witness trees under the loaded binary frontend retains
the existing concrete table and cache readiness and its exact frame law. -/
theorem proof_returns (tables : Proof.Tables) (context : Context) (witness : ProofWitness)
    (before : State) (ready : Proof.Ready tables before)
    (bindings : Subst) (termsName definitionsName theoremsName contextName hypothesesName witnessName : String)
    (termsCaptured : applySubst bindings (.var termsName) = TableAccess.tableValue tables.terms)
    (definitionsCaptured : applySubst bindings (.var definitionsName) = TableAccess.tableValue tables.definitions)
    (theoremsCaptured : applySubst bindings (.var theoremsName) = TableAccess.tableValue tables.theorems)
    (contextCaptured : applySubst bindings (.var contextName) = Data.context context)
    (hypothesesCaptured : applySubst bindings (.var hypothesesName) = Proof.hypothesesValue tables)
    (witnessCaptured : applySubst bindings (.var witnessName) = Proof.witnessValue witness) :
    ∃ after bound,
      PureReturns program bindings before
        (.expression [.symbol "mm0:proof", .var termsName, .var definitionsName, .var theoremsName,
          .var contextName, .var hypothesesName, .var witnessName]) after
        (ProofResults.resultValue (ProofWitness.proof? (signatureOf tables.entries)
          (Unfolding.definitionSignature tables.bodies) (Proof.theoremSignature tables.declarations)
          context tables.values witness)) ∧
      Proof.Ready tables after ∧
      InferenceCache.Frame tables.cache (TableAccess.tableValue tables.terms) bound before after := by
  obtain ⟨after, bound, returned, readyAfter, frame⟩ := Proof.returns tables context witness before ready
  refine ⟨after, bound, ?_, readyAfter, frame⟩
  apply MMBProofRunExecution.checker_returns (by
    simp only [codeWithin, atomsWithin, expressionHeadWithin]
    decide +kernel)
  exact returned bindings termsName definitionsName theoremsName contextName hypothesesName witnessName
    termsCaptured definitionsCaptured theoremsCaptured contextCaptured hypothesesCaptured witnessCaptured

/-- All ordered premise witnesses are actually checked. A missing or invalid
child yields the original completed `None`; a constructor tag is insufficient. -/
theorem children_returns (tables : Proof.Tables) (context : Context) (children : List ProofWitness)
    (before : State) (ready : Proof.Ready tables before)
    (bindings : Subst) (termsName definitionsName theoremsName contextName hypothesesName childrenName : String)
    (termsCaptured : applySubst bindings (.var termsName) = TableAccess.tableValue tables.terms)
    (definitionsCaptured : applySubst bindings (.var definitionsName) = TableAccess.tableValue tables.definitions)
    (theoremsCaptured : applySubst bindings (.var theoremsName) = TableAccess.tableValue tables.theorems)
    (contextCaptured : applySubst bindings (.var contextName) = Data.context context)
    (hypothesesCaptured : applySubst bindings (.var hypothesesName) = Proof.hypothesesValue tables)
    (childrenCaptured : applySubst bindings (.var childrenName) = listValue (children.map Proof.witnessValue)) :
    ∃ after bound,
      PureReturns program bindings before
        (.expression [.symbol "mm0:proof-children", .var termsName, .var definitionsName, .var theoremsName,
          .var contextName, .var hypothesesName, .var childrenName]) after
        (ListSubstitution.resultValue (ProofWitness.children? (signatureOf tables.entries)
          (Unfolding.definitionSignature tables.bodies) (Proof.theoremSignature tables.declarations)
          context tables.values children)) ∧
      Proof.Ready tables after ∧
      InferenceCache.Frame tables.cache (TableAccess.tableValue tables.terms) bound before after := by
  obtain ⟨after, bound, returned, readyAfter, frame⟩ := Proof.children_returns tables context children before ready
  refine ⟨after, bound, ?_, readyAfter, frame⟩
  apply MMBProofRunExecution.checker_returns (by
    simp only [codeWithin, atomsWithin, expressionHeadWithin]
    decide +kernel)
  exact returned bindings termsName definitionsName theoremsName contextName hypothesesName childrenName
    termsCaptured definitionsCaptured theoremsCaptured contextCaptured hypothesesCaptured childrenCaptured


private def kernelEnvironment (tables : Proof.Tables) (context : Context) (witness : ProofWitness) : Subst :=
  [("witness", Proof.witnessValue witness), ("hypotheses", Proof.hypothesesValue tables),
    ("context", Data.context context), ("theorems", TableAccess.tableValue tables.theorems),
    ("definitions", TableAccess.tableValue tables.definitions), ("table", TableAccess.tableValue tables.terms)]

private theorem kernel_request_shape (state : State) (tables : Proof.Tables)
    (context : Context) (witness : ProofWitness) :
    Proof.requestConfiguration state tables context witness =
      { state, control := .evaluate (kernelEnvironment tables context witness) (.expression [.symbol "mm0:proof", .var "table", .var "definitions", .var "theorems",
          .var "context", .var "hypotheses", .var "witness"]) } := rfl

/-- Exact finite execution of the original kernel request under the loaded
binary program, including cache changes and the other-store frame law. -/
theorem kernel_result_sufficient_fuel (tables : Proof.Tables) (context : Context)
    (witness : ProofWitness) (state : State) (ready : Proof.Ready tables state) :
    ∃ after bound fuel,
      (∀ extra, Eval.run program (fuel + extra) (Proof.requestConfiguration state tables context witness) =
        .complete after [ProofResults.resultValue (ProofWitness.proof? (signatureOf tables.entries)
          (Unfolding.definitionSignature tables.bodies) (Proof.theoremSignature tables.declarations)
          context tables.values witness)] [] []) ∧
      Proof.Ready tables after ∧
      InferenceCache.Frame tables.cache (TableAccess.tableValue tables.terms) bound state after := by
  let bindings := kernelEnvironment tables context witness
  obtain ⟨after, bound, returned, readyAfter, frame⟩ :=
    proof_returns tables context witness state ready bindings "table" "definitions" "theorems" "context" "hypotheses" "witness"
      (by simp [bindings, kernelEnvironment, applySubst, Subst.lookup])
      (by simp [bindings, kernelEnvironment, applySubst, Subst.lookup])
      (by simp [bindings, kernelEnvironment, applySubst, Subst.lookup])
      (by simp [bindings, kernelEnvironment, applySubst, Subst.lookup])
      (by simp [bindings, kernelEnvironment, applySubst, Subst.lookup])
      (by simp [bindings, kernelEnvironment, applySubst, Subst.lookup])
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program bindings state after _ _ returned
  refine ⟨after, bound, fuel, ?_, readyAfter, frame⟩
  intro extra
  rw [kernel_request_shape]
  exact completed_run_more_fuel program fuel extra _ after _ [] [] completed

/-- The loaded binary frontend preserves and reflects each original kernel
result. Logical refusal remains a completed `None`, not an exhausted run. -/
theorem kernel_result_iff (tables : Proof.Tables) (context : Context) (witness : ProofWitness)
    (state : State) (ready : Proof.Ready tables state) (answer : Option Preterm) :
    ProofWitness.proof? (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values witness = answer ↔
      ∃ after fuel, Eval.run program fuel (Proof.requestConfiguration state tables context witness) =
        .complete after [ProofResults.resultValue answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ :=
    kernel_result_sufficient_fuel tables context witness state ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, computed⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] []
      referenceCompleted computed
    exact ProofResults.resultValue_injective (List.singleton_inj.mp same.2.1)

theorem kernel_checked_iff (tables : Proof.Tables) (context : Context) (witness : ProofWitness)
    (state : State) (ready : Proof.Ready tables state) (claim : Preterm) :
    ProofWitness.check (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values witness claim = true ↔
      ∃ after fuel, Eval.run program fuel (Proof.requestConfiguration state tables context witness) =
        .complete after [ProofResults.resultValue (some claim)] [] [] := by
  simp only [ProofWitness.check, decide_eq_true_eq]
  exact kernel_result_iff tables context witness state ready (some claim)

/-- A completed accepted theorem application exposes its actual declaration,
admissible simultaneous instance and checked ordered children. It cannot rely
on the source stack's unvalidated claim labels. -/
theorem application_exact (tables : Proof.Tables) (context : Context) (index : Nat)
    (arguments : List Preterm) (children : List ProofWitness) (state : State)
    (ready : Proof.Ready tables state) (claim : Preterm) :
    (∃ after fuel, Eval.run program fuel
      (Proof.requestConfiguration state tables context (.theoremApp index arguments children)) =
        .complete after [ProofResults.resultValue (some claim)] [] []) ↔
    ∃ declaration instantiation,
      Proof.theoremSignature tables.declarations index = some declaration ∧
      TheoremDecl.Instantiates (signatureOf tables.entries) context declaration arguments instantiation ∧
      ProofWitness.ChecksList (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
        (Proof.theoremSignature tables.declarations) context tables.values children instantiation.hypotheses ∧
      instantiation.conclusion = claim := by
  rw [← kernel_checked_iff tables context (.theoremApp index arguments children) state ready claim,
    ProofWitness.check_iff]
  constructor
  · intro checked
    cases checked with
    | @theoremApp _ declaration _ _ instantiation available instantiated premises =>
        exact ⟨declaration, instantiation, available, instantiated, premises, rfl⟩
  · rintro ⟨declaration, instantiation, available, instantiated, premises, same⟩
    rw [← same]
    exact .theoremApp available instantiated premises

/-- A source-accepted application yields an original kernel derivation. All
concrete lookup/cache readiness is retained; declaration admission is separate. -/
theorem application_derives (tables : Proof.Tables) (context : Context) (index : Nat)
    (arguments : List Preterm) (children : List ProofWitness) (state : State)
    (ready : Proof.Ready tables state) (claim : Preterm) (after : State) (fuel : Nat)
    (accepted : Eval.run program fuel
      (Proof.requestConfiguration state tables context (.theoremApp index arguments children)) =
        .complete after [ProofResults.resultValue (some claim)] [] []) :
    Kernel.Derives (signatureOf tables.entries) (Unfolding.definitionSignature tables.bodies)
      (Proof.theoremSignature tables.declarations) context tables.values claim := by
  apply ProofWitness.check_sound
  exact (kernel_checked_iff tables context (.theoremApp index arguments children) state ready claim).mpr
    ⟨after, fuel, accepted⟩


/-- The actual recorder prepends its saved row; submission later reverses
that physical list to check every initializer in chronological order. -/
def recordResult (saved : List Atom) (hypothesisCount : Nat) (expected witness : Atom) : Atom :=
  optionValue (some (.expression [.symbol "MM0:MMUProof",
    listValue (.expression [.symbol "MM0:Saved", expected, witness] :: saved),
    Hypothesis.witness (hypothesisCount + saved.length)]))

private def recordEquation : SpaceSemantics.Equation :=
  ((MMUResolution.resolverSource.program.equations.filter (·.head == "mm0:mmu:record-proof")).head?).getD
    ⟨"", [], .symbol "None"⟩
private def recordEnvironment (saved : List Atom) (hypothesisCount : Nat) (expected witness : Atom) : Subst :=
  [("witness", witness), ("expected", expected), ("hypothesisCount", natural hypothesisCount),
    ("saved", .expression saved)]
private theorem record_unique : program.equations.filter (·.head == "mm0:mmu:record-proof") =
    [recordEquation] := by decide +kernel
private theorem record_formals : recordEquation.arguments =
    [.expression [.symbol "MM0:L", .var "saved"], .var "hypothesisCount", .var "expected", .var "witness"] := by decide
private theorem record_shape : recordEquation.body =
    .expression [.symbol "let*", .expression [
      .expression [.var "index", .expression [.symbol "+", .var "hypothesisCount",
        .expression [.symbol "size-atom", .var "saved"]]],
      .expression [.var "next", .expression [.symbol "cons", .expression [.symbol "MM0:Saved", .var "expected", .var "witness"], .var "saved"]]],
      .expression [.symbol "Some", .expression [.symbol "MM0:MMUProof", .expression [.symbol "MM0:L", .var "next"],
        .expression [.symbol "MM0:L", .expression [.symbol "MM0:Hyp", .var "index"]]]]] := by decide
private theorem record_clause (saved : List Atom) (hypothesisCount : Nat) (expected witness : Atom) :
    clauses program "mm0:mmu:record-proof" [listValue saved, natural hypothesisCount, expected, witness] =
      [.evaluate (recordEnvironment saved hypothesisCount expected witness) recordEquation.body] := by
  rw [clauses_use_only_the_named_equations, record_unique]
  simp [record_formals, listValue, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, recordEnvironment]

private theorem record_body_returns (state : State) (saved : List Atom) (hypothesisCount : Nat)
    (expected witness : Atom) :
    PureReturns program (recordEnvironment saved hypothesisCount expected witness) state recordEquation.body state
      (recordResult saved hypothesisCount expected witness) := by
  let bindings := recordEnvironment saved hypothesisCount expected witness
  let index := hypothesisCount + saved.length
  let entry := Atom.expression [Atom.symbol "MM0:Saved", expected, witness]
  let indexed := ("index", natural index) :: bindings
  let appended := ("next", .expression (entry :: saved)) :: indexed
  rw [record_shape]
  apply let_star_returns program bindings state state _ _ _ _ rfl
  apply let_returns program bindings indexed state state state (.var "index") _ _ (natural index) _
  · apply native_binary_call_returns program bindings state state state state "+" (.var "hypothesisCount")
      (.expression [.symbol "size-atom", .var "saved"]) (natural hypothesisCount) (natural saved.length) (natural index)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact variable_returns program bindings state "hypothesisCount"
    · apply native_variable_call_returns program bindings state state "size-atom" ["saved"] _
        (by decide) (by decide) _ (by decide)
      simp [bindings, recordEnvironment, applySubst, Subst.lookup, natural]
    · simp [index, natural]
  · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, indexed, bindings, recordEnvironment]
  · apply let_returns program indexed appended state state state (.var "next") _ _ (.expression (entry :: saved)) _
    · apply native_binary_call_returns program indexed state state state state "cons"
        (.expression [.symbol "MM0:Saved", .var "expected", .var "witness"]) (.var "saved") entry (.expression saved)
        (.expression (entry :: saved)) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
        _ _ _ (by decide)
      · simpa [entry, indexed, bindings, recordEnvironment, applySubst, Subst.lookup] using
          constructor_variables_return program indexed state "MM0:Saved" ["expected", "witness"]
            (by decide +kernel) (by decide)
      · exact variable_returns program indexed state "saved"
      · rfl
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, appended, indexed, bindings, recordEnvironment]
    · apply unary_constructor_of_returns program appended state state "Some" _ _ (by decide +kernel) (by decide)
      apply binary_constructor_returns program appended state state state "MM0:MMUProof" _ _ _ _
        (by decide +kernel) (by decide)
      · simpa [appended, applySubst, Subst.lookup, recordResult, listValue, entry] using
          unary_constructor_returns program appended state "MM0:L" "next" (by decide +kernel) (by decide)
      · apply unary_constructor_of_returns program appended state state "MM0:L" _ _ (by decide +kernel) (by decide)
        simpa [appended, indexed, bindings, recordEnvironment, applySubst, Subst.lookup, recordResult,
          index, Hypothesis.witness, listValue] using
          constructor_variables_return program appended state "MM0:Hyp" ["index"] (by decide +kernel) (by decide)

/-- Original chronological recording, preserving even unchecked supplied
witness data. Recording itself grants no logical authority. -/
theorem record_proof_returns (bindings : Subst) (state : State) (saved : List Atom)
    (hypothesisCount : Nat) (expected witness : Atom) (savedName countName expectedName witnessName : String)
    (savedCaptured : applySubst bindings (.var savedName) = listValue saved)
    (countCaptured : applySubst bindings (.var countName) = natural hypothesisCount)
    (expectedCaptured : applySubst bindings (.var expectedName) = expected)
    (witnessCaptured : applySubst bindings (.var witnessName) = witness) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmu:record-proof", .var savedName,
      .var countName, .var expectedName, .var witnessName]) state
      (recordResult saved hypothesisCount expected witness) := by
  apply authored_variable_call_returns program bindings (recordEnvironment saved hypothesisCount expected witness)
    state state "mm0:mmu:record-proof" [savedName, countName, expectedName, witnessName]
    recordEquation.body _ (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (record_body_returns state saved hypothesisCount expected witness) (by decide)
  simpa [savedCaptured, countCaptured, expectedCaptured, witnessCaptured] using
    record_clause saved hypothesisCount expected witness

/-- Reversing the physical recorder output retains every old row, then the
new initializer. Equal or unused rows are not removed. -/
theorem recorded_chronology (saved : List Atom) (expected witness : Atom) :
    (.expression [.symbol "MM0:Saved", expected, witness] :: saved).reverse =
      saved.reverse ++ [.expression [.symbol "MM0:Saved", expected, witness]] := by simp

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremExecution
