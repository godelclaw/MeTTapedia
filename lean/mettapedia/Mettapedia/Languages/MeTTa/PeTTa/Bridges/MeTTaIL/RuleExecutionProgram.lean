import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataProgram

/-!
# Retained rule operations and conservative matcher composition

Rule execution extends the retained matching program with distinct authored
function names. Existing matcher paths transport through the ordinary PeTTa
program-agreement theorem: dispatch, argument demand and selected bodies are
checked against both loaded sources. Captured values remain data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open Eval
open Effects (State)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/gslt_rule_execution.metta"
    sha256 "d5da4012ee1bc3858d85462e50e48f2bd8abc58a9d02b271e522565688c5dd5a"

/-- Shared operations used by the existing ordered premise dispatcher. -/
def premiseSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/gslt_premise_operations.metta"
    sha256 "c52fb422a6eddee21458ca6a560c55cc468d4b33ac34f65418ea80df1af9616f"

def program : Program :=
  MatchAutomataProgram.program.append (source.program.append premiseSource.program)

/-- Lookup is by the authored function name, independently of file position. -/
def equations (head : String) : List Equation :=
  program.equations.filter (fun equation => equation.head == head)

/-- The extension's namespace and dynamic evaluation are outside the retained
matcher's static code support. Captured values are not scanned as code. -/
def matcherHead (head : String) : Bool :=
  head != "eval" && !(head.startsWith "gslt:rule:") && !(head.startsWith "gslt:premise:")

theorem matcher_bodies_within :
    MatchAutomataProgram.program.equations.all (fun equation =>
      !matcherHead equation.head || codeWithin matcherHead equation.body) = true := by
  decide +kernel

theorem matcher_program_closed : ProgramClosed matcherHead MatchAutomataProgram.program := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked := List.all_eq_true.mp matcher_bodies_within equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using checked

theorem extension_equations_fresh :
    (source.program.append premiseSource.program).equations.all (fun equation => !matcherHead equation.head) = true := by
  decide +kernel

theorem extension_declarations_fresh :
    (source.program.append premiseSource.program).declarations.all (fun declaration => match declaration with
      | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
          !matcherHead head
      | _ => true) = true := by
  decide +kernel

theorem matcher_program_agreement :
    ProgramAgreementOn matcherHead MatchAutomataProgram.program program := by
  apply appended_program_agreement
  · intro equation member
    have checked := List.all_eq_true.mp extension_equations_fresh equation member
    cases result : matcherHead equation.head with
    | false => rfl
    | true => simp [result] at checked
  · intro name types member
    have checked := List.all_eq_true.mp extension_declarations_fresh
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases result : matcherHead name with
    | false => rfl
    | true => simp [result] at checked

/-- Every supported existing matcher computation keeps its store, answer and
I/O after the actual rule-operation source is loaded. -/
theorem automata_captured_returns {bindings : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin matcherHead code = true)
    (checked : PureReturns MatchAutomataProgram.program bindings before code after answer) :
    PureReturns program bindings before code after answer :=
  path_of_closed_agreement matcher_program_closed matcher_program_agreement
    ⟨supported, rfl⟩ checked

theorem no_initializers : source.program.initializers = [] := by decide +kernel

theorem equation_heads_unique : (program.equations.map (·.head)).Nodup := by decide +kernel

#print axioms matcher_program_agreement
#print axioms automata_captured_returns

/-- Complete scoped conditional operations, including final receipt readout.
The quoted artifact is independent of the source execution judgments. -/
def scopedSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/lib/gslt_scoped_execution.metta"
    sha256 "fc5299ce7c11b012277e07aff675758bb7fbd9f42ac9c9d487a6f887d074de57"

def scopedProgram : Program := scopedSource.program

/-- A call fragment retains the ordered equations and arrow declarations for
its operation family. It carries no initializers or facts. Its canonical layout
places those equations before those declarations. -/
def callFragmentWhere (owns : String → Bool) (source : Program := scopedProgram) : Program :=
  let equations := source.equations.filter (fun equation => owns equation.head)
  let declarations := source.declarations.filter (retainedCallDeclaration owns)
  { equations, declarations
    layout := List.replicate equations.length .equation ++
      List.replicate declarations.length .declaration }

def callFragment (heads : List String) (source : Program := scopedProgram) : Program :=
  callFragmentWhere heads.contains source

def scopedMachineProgram : Program :=
  callFragmentWhere fun head =>
    head != "gslt:rule:site-replacement-represented" && head != "gslt:rule:job-finish-root"

def premiseAssignmentProgram : Program :=
  callFragment ["gslt:premise:type-context-lookup", "gslt:premise:check-assignment"]

def premiseAdministrationProgram : Program :=
  callFragment ["gslt:premise:context-next", "gslt:premise:context-quantified", "gslt:premise:machine-deliver", "gslt:premise:machine-evaluate", "gslt:premise:machine-expand"]

def premiseEnvironmentProgram : Program :=
  callFragment ["gslt:premise:constructor-declarations", "gslt:premise:source-type", "gslt:premise:specification", "gslt:premise:signature-candidates", "gslt:premise:signature", "gslt:premise:check-values", "gslt:premise:check-row"]

def premiseGroundProgram : Program :=
  callFragment ["gslt:premise:ground-at", "gslt:premise:ground-list-at"]

def premiseReflectionSelectionProgram : Program :=
  callFragment ["gslt:premise:reflective-rules", "gslt:premise:reflective-presentations", "gslt:premise:presentation-named", "gslt:premise:substitution-presentation"]

def premiseQueryProgram : Program :=
  callFragment ["gslt:premise:query-site", "gslt:premise:query-matching-request", "gslt:premise:query-expand-in"]

def premiseAdmissionProgram : Program :=
  callFragment ["gslt:premise:admission-keys", "gslt:premise:admission-occurrence-keys", "gslt:premise:admission-nodup", "gslt:premise:admission-context-covered", "gslt:premise:admission-occurrences", "gslt:premise:binding-admitted"]

def premiseFullEnvironmentProgram : Program :=
  callFragment ["gslt:premise:query-obligations", "gslt:premise:machine-deliver-in", "gslt:premise:machine-evaluate-in", "gslt:premise:machine-expand-in"]

def matcherEraseProgram : Program :=
  callFragment ["gslt:rule:scope-match-erase-at"]

def scopedInstantiationProgram : Program :=
  callFragment ["gslt:rule:scope-binder-operation", "gslt:rule:scope-instantiate-slot", "gslt:rule:scope-instantiate-at", "gslt:rule:scope-instantiate-args-at", "gslt:rule:scope-reduct"]

def scopedReflectionProgram : Program :=
  callFragment ["gslt:rule:scope-reflective-normalize", "gslt:rule:scope-reflective-normalize-list", "gslt:rule:scope-reflective-normalize-finish", "gslt:rule:scope-reflective-replacement", "gslt:rule:scope-reflective-normalized-mark", "gslt:rule:scope-reflective-name-mark", "gslt:rule:scope-reflective-unmark", "gslt:rule:scope-reflective-drop-finish", "gslt:rule:scope-reflective-instantiate-at", "gslt:rule:scope-reflective-instantiate-list-at", "gslt:rule:scope-reflective-instantiate-apply", "gslt:rule:scope-reflective-instantiate-unary", "gslt:rule:scope-reflective-binder-operation"]

def scopedMatcherProgram : Program :=
  callFragment ["gslt:rule:scope-matcher-capture", "gslt:rule:scope-matcher-captured-work", "gslt:rule:scope-matcher-split-at", "gslt:rule:scope-matcher-start", "gslt:rule:scope-matcher-complete", "gslt:rule:scope-matcher-expand-tree", "gslt:rule:scope-matcher-expand", "gslt:rule:scope-matcher-advance-branches", "gslt:rule:scope-matcher-advance", "gslt:rule:scope-matcher-tick", "gslt:rule:scope-matcher-run"]

def premiseSchedulerProgram : Program :=
  callFragment ["gslt:premise:machine-commit", "gslt:premise:machine-complete"]

def premiseMachineRunProgram : Program :=
  callFragment ["gslt:premise:machine-start", "gslt:premise:machine-tick", "gslt:premise:machine-run"]

def premiseMatchingProgram : Program :=
  callFragment ["gslt:premise:root-match-expand-in", "gslt:premise:target-match-expand-in", "gslt:premise:root-body-deliver-in", "gslt:premise:stepped-deliver-in"]

def ruleJobReadoutProgram : Program :=
  callFragment ["gslt:rule:site-replacement-represented", "gslt:rule:job-finish-root"]

theorem scoped_equation_count : scopedProgram.equations.length = 220 := by rfl
set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
theorem scoped_machine_equation_count : scopedMachineProgram.equations.length = 218 := by rfl
theorem scoped_no_initializers : scopedProgram.initializers = [] := by rfl
theorem scoped_no_facts : scopedProgram.facts = [] := by rfl
theorem callFragmentWhere_balanced (owns : String → Bool) (source : Program) :
    SpaceSemantics.Balanced (callFragmentWhere owns source) := by
  simp [callFragmentWhere, SpaceSemantics.Balanced, List.count_replicate]

theorem callFragment_balanced (heads : List String) (source : Program) :
    SpaceSemantics.Balanced (callFragment heads source) :=
  callFragmentWhere_balanced heads.contains source

theorem premiseAssignmentProgram_equation_count : premiseAssignmentProgram.equations.length = 2 := by rfl

theorem premiseAdministrationProgram_equation_count : premiseAdministrationProgram.equations.length = 5 := by rfl

theorem premiseEnvironmentProgram_equation_count : premiseEnvironmentProgram.equations.length = 7 := by rfl

theorem premiseGroundProgram_equation_count : premiseGroundProgram.equations.length = 2 := by rfl

theorem premiseReflectionSelectionProgram_equation_count : premiseReflectionSelectionProgram.equations.length = 4 := by rfl

theorem premiseQueryProgram_equation_count : premiseQueryProgram.equations.length = 3 := by rfl

theorem premiseAdmissionProgram_equation_count : premiseAdmissionProgram.equations.length = 6 := by rfl

theorem premiseFullEnvironmentProgram_equation_count : premiseFullEnvironmentProgram.equations.length = 4 := by rfl

theorem matcherEraseProgram_equation_count : matcherEraseProgram.equations.length = 1 := by rfl

theorem scopedInstantiationProgram_equation_count : scopedInstantiationProgram.equations.length = 5 := by rfl

theorem scopedReflectionProgram_equation_count : scopedReflectionProgram.equations.length = 13 := by rfl

theorem scopedMatcherProgram_equation_count : scopedMatcherProgram.equations.length = 11 := by rfl

theorem premiseSchedulerProgram_equation_count : premiseSchedulerProgram.equations.length = 2 := by rfl

theorem premiseMachineRunProgram_equation_count : premiseMachineRunProgram.equations.length = 3 := by rfl

#print axioms scoped_equation_count
#print axioms scoped_machine_equation_count
#print axioms scoped_no_initializers
#print axioms scoped_no_facts
#print axioms callFragment_balanced

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
