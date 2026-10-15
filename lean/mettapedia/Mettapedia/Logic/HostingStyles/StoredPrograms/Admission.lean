import Mettapedia.Logic.HostingStyles.StoredPrograms.LargerHost
import Mettapedia.Logic.HostingStyles.StoredPrograms.Replay
import Mettapedia.Languages.MM0.Presentation.AdmissionControls

/-!
# The admission of a development, run by the candidate

MM0's kernel admits a development one declaration after the other, from the
empty theory: a sort, a term, a definition with its body, an axiom, a theorem
with its proof (`Theory.run?`).  Each is checked against the theory admitted
so far, and a theorem is admitted only when the kernel checks its proof.  The
admission is authored as one equation program
(`ComputationalAdmission.admissionProgram`): 372 equations under the larger
host, which compute what the kernel's function returns
(`ComputationalAdmission.start_computes`).

Its head `mm0:admission-start` reaches 188 heads and 369 of the equations
(`admissionHeads`, `admissionHeads_closed`).  One head is ordered, the checked
argument of a conversion; the program has no other overlapping pair
(`admission_overlaps`), no special form, and calls seven primitives
(`admission_primitives`).  The table (`admissionTable`): the 367 rules of the
equations of the other heads, the six ordered rules, and the eighty rules of
the library.  **453 stored rules, the same for every development**
(`admission_size`).  It stores the part of the program (`admission_stores`)
and is a stored table, hence orthogonal (`admission_stored`).

**The candidate runs the kernel on a whole development.**

* The run of the admission of a list of declarations reaches the run of an
  encoded result exactly when the kernel's function returns that result: the
  admitted theory, or nothing (`admission_run_iff`).
* Every run without transition that it reaches is the run of what the
  kernel's function returns (`admission_run_unique`).
* It reaches the run of an encoded theory exactly when the kernel admits the
  list, from the empty theory, to that theory (`admission_run_admits_iff`).

**One development is checked by replaying its trace in the table**
(`restatedDevelopment`): a provable sort, a constant, an axiom asserting the
constant, and a theorem restating the axiom, proved by applying it.  343
steps take the call of its admission to the reading of its encoded theory
(`admission_instance_replays`): the kernel, run by the stored rules, admits
four declarations and checks a proof.  So the candidate reaches that run
(`admission_instance_admitted`), and the kernel's function returns that theory
(`restatedDevelopment_admitted`).  Negative: a term whose sort is not declared
is refused, in twenty-six steps (`admission_refusal_replays`,
`admission_instance_refused`, `admission_instance_not_admitted`).

The general fact used here and for the verification against a specification
is `Stores.run_result_iff`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies natural boolean encodeNaturalTable
    encodeLookupResult)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Languages.MM0.Kernel (Admission)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (admissionProgram encodeAdmissions encodeAdmission encodeTheory encodeTheoryResult
    encodeTheoryResult_injective start_computes)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom program_reaches)

namespace Stores

variable {N : Spelling} {rules : List RewriteRule} {program : Program} {host : Host}
  {primitives : List String}

/-- **A call that the engine answers with the encoding of what a function
returns**: the run of the call reaches the run of an encoded result exactly
when the function returns that result, for an encoding that identifies no two
results. -/
theorem run_result_iff (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {Result : Type} {encodeResult : Result → EngineTerm}
    (encodeInjective : Function.Injective encodeResult) {head : String}
    {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true) {returned : Result}
    (applies : Applies program host head arguments (encodeResult returned)) (result : Result) :
    atomsReduceTheory.Reaches (callRun N rules head arguments)
        (valueRun N rules (encodeResult result)) ↔
      returned = result := by
  constructor
  · intro reaches
    exact (encodeInjective (valueRun_injective injective rules
      (stores.run_unique orthogonal defined applies reaches (stores.run_value_normal _)))).symm
  · rintro rfl
    exact stores.run_reaches defined applies

end Stores

/-- **The heads that the admission of a development reaches.** -/
def admissionHeads : List String :=
  ["mm0:admission-start", "mm0:admission-run", "mm0:admission-run-view", "mm0:admission-run-next",
    "mm0:admission-step", "mm0:admission-checked", "mm0:admission-check", "mm0:admission-fresh",
    "mm0:form-and", "mm0:form-term", "mm0:form-body", "mm0:form-theorem", "mm0:form-dummies",
    "mm0:admission-proof", "mm0:admission-publish", "mm0:form-term-context", "mm0:form-context",
    "mm0:form-dummies-view", "mm0:form-theorem-context", "mm0:body-dummies",
    "mm0:admission-missing", "nik:nat-table-get", "mm0:check-proof", "nik:list-append",
    "mm0:dummy-context", "nik:append-view", "nik:table-view", "mm0:proof",
    "mm0:form-context-from", "mm0:form-term-result", "mm0:form-sort", "mm0:form-dummies-next",
    "mm0:form-statements", "mm0:form-statement", "mm0:dummy-context-view", "mm0:body-context",
    "nik:table-equal", "mm0:data-at", "mm0:proof-declaration", "mm0:proof-converted",
    "mm0:conversion", "mm0:form-sort-info", "mm0:form-context-view", "mm0:form-bound-indices",
    "mm0:form-statement-type", "mm0:infer", "mm0:form-statements-view", "mm0:body-typed",
    "mm0:at-view", "mm0:infer-binder", "mm0:infer-declaration", "mm0:declaration",
    "mm0:infer-function", "mm0:conversion-refl-type", "mm0:conversion-swap",
    "mm0:conversion-first", "mm0:conversion-declaration", "mm0:conversion-unfold-declaration",
    "mm0:proof-instance", "mm0:instantiate-theorem", "mm0:proof-left", "mm0:form-bound-view",
    "mm0:form-not", "mm0:form-context-next", "mm0:form-binder", "mm0:form-statement-saturated",
    "mm0:form-statements-next", "mm0:body-free", "mm0:free-variables", "mm0:at-zero",
    "mm0:declaration-view", "mm0:infer-arguments", "mm0:conversion-refl-saturated",
    "mm0:conversion-join", "mm0:conversion-congruent", "mm0:conversion-arguments",
    "mm0:conversion-unfold-result", "mm0:unfold", "mm0:theorem-admissible",
    "mm0:check-admissible", "mm0:proof-premises", "mm0:proof-children",
    "mm0:proof-conversion-matched", "mm0:form-bound-next", "mm0:form-bound-index",
    "mm0:form-binder-deps", "mm0:free-spine", "mm0:body-free-view", "nik:nat-difference",
    "mm0:declaration-equal", "mm0:infer-bound-sort", "mm0:bound-sort", "mm0:infer-regular-type",
    "mm0:admissible-typed", "mm0:check-arguments", "mm0:unfold-declaration",
    "mm0:conversion-joined", "mm0:apply-args", "mm0:conversion-unfold-typed",
    "mm0:conversion-arguments-view", "mm0:theorem-prepared", "mm0:substitution-values",
    "mm0:proof-matched", "mm0:proof-children-view", "mm0:form-bound-item", "nik:difference-view",
    "mm0:free-variable-spine", "mm0:free-head", "mm0:free-argument", "mm0:bound-binder",
    "mm0:infer-sort-equal", "mm0:infer-saturated", "mm0:check-arguments-view",
    "mm0:admissible-entries", "mm0:entries", "mm0:substitution-values-view", "mm0:unfold-body",
    "mm0:apply-args-view", "mm0:conversion-argument", "mm0:theorem-hypotheses", "mm0:subst-list",
    "mm0:proof-child", "nik:difference-keep", "nik:nat-member", "mm0:support", "mm0:free-typed",
    "mm0:support-binder", "mm0:support-function", "nik:member-view", "mm0:check-arguments-next",
    "mm0:check-binder", "mm0:entries-view", "mm0:check-rows", "mm0:unfold-arguments",
    "mm0:conversion-argument-checked", "mm0:conversion-binder-sort", "mm0:subst-list-view",
    "mm0:theorem-conclusion", "mm0:subst", "mm0:proof-tail", "mm0:free-contributed",
    "mm0:free-contributions", "mm0:support-argument", "nik:member-equal", "mm0:check-sort",
    "mm0:check-type", "mm0:rows-view", "mm0:lookup", "mm0:subst-function", "mm0:unfold-dummies",
    "mm0:check-dummies", "mm0:conversion-argument-tail", "mm0:subst-list-head",
    "mm0:free-contributions-view", "mm0:free-contribution-tail", "mm0:free-images",
    "mm0:check-saturated", "mm0:rows-next", "mm0:check-row", "mm0:subst-argument",
    "mm0:lookup-zero", "mm0:dummies-view", "mm0:variable-images", "mm0:subst-list-tail",
    "mm0:free-images-view", "mm0:free-contribution-bound", "mm0:check-pairs", "mm0:dummy-sort",
    "mm0:variable-images-view", "mm0:free-images-first", "mm0:free-image", "mm0:pairs-view",
    "mm0:dummy-fresh", "mm0:fresh-all", "mm0:free-image-formal", "mm0:free-images-tail",
    "mm0:pairs-next", "mm0:check-pair", "mm0:fresh-all-view", "mm0:free-image-argument",
    "mm0:pair-depends", "mm0:depends", "mm0:fresh-all-next", "mm0:fresh-for",
    "mm0:free-image-target", "mm0:support-disjoint", "mm0:free-image-equal", "mm0:dependency-not"]

/-- **The head whose equations are tried in order.** -/
def admissionOrdered : List String := ["mm0:conversion-argument-checked"]

/-- **The table that runs the admission**: 453 rules, the same for every
development. -/
abbrev admissionTable : List RewriteRule :=
  partTable admissionProgram admissionHeads admissionOrdered

set_option maxRecDepth 100000 in
/-- The text of the admission program is of the class. -/
theorem admission_text : storableText admissionProgram = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- It calls only what the library computes. -/
theorem admission_calls :
    callsOnly admissionProgram dataEqualityHandled largerPrimitives = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The heads are closed under the calls of the program. -/
theorem admissionHeads_closed : closedUnderCalls admissionProgram admissionHeads = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The equations of the other heads are separated.** -/
theorem admission_separated :
    Separated (admissionProgram.filter fun equation =>
      !admissionOrdered.contains equation.head) :=
  separated_of_no_overlappingPairs (by decide +kernel)

set_option maxRecDepth 100000 in
/-- No equation has a primitive as its head. -/
theorem admission_noPrimitive : ∀ equation ∈ admissionProgram,
    equation.head ∉ largerPrimitives := by
  have checked : (admissionProgram.all fun equation =>
      !largerPrimitives.contains equation.head) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp checked equation member

set_option maxRecDepth 100000 in
/-- The six ordered rules are a stored table. -/
theorem admission_ordered_stored : StoredTable (orderedPart admissionProgram admissionOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem admission_stored : StoredTable admissionTable :=
  storedTable_partTable admission_text admission_separated admission_noPrimitive
    admission_ordered_stored

set_option maxRecDepth 100000 in
/-- **The table stores the part of the program.** -/
theorem admission_stores :
    Stores letterSpelling admissionTable (partAt admissionProgram admissionHeads)
      dataEqualityHost largerPrimitives :=
  stores_partTable admission_text admission_calls admissionHeads_closed (by decide +kernel)
    admission_stored

set_option maxRecDepth 100000 in
/-- 188 heads, 369 of the 372 equations, 453 rules. -/
theorem admission_size :
    admissionHeads.length = 188 ∧ (partAt admissionProgram admissionHeads).length = 369 ∧
      admissionProgram.length = 372 ∧ admissionTable.length = 453 := by
  have counted : ((partAt admissionProgram admissionHeads).filter fun equation =>
      !admissionOrdered.contains equation.head).length = 367 ∧
      (orderedPart admissionProgram admissionOrdered).length = 6 ∧
      (partAt admissionProgram admissionHeads).length = 369 ∧
      admissionProgram.length = 372 := by decide +kernel
  refine ⟨by decide, counted.2.2.1, counted.2.2.2, ?_⟩
  rw [partTable_length, counted.1, counted.2.1]

set_option maxRecDepth 100000 in
/-- **The primitives that the admission program calls**: seven, the equality
of data among them. -/
theorem admission_primitives :
    calledPrimitives admissionProgram dataEqualityHandled =
      ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
        "nik:nat-add", "nik:data-eq"] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Its overlapping pairs**: one, at the ordered head. -/
theorem admission_overlaps :
    overlappingPairs admissionProgram =
      [("conversion-argument-checked", "conversion-argument-refused")] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem admission_defined :
    admissionProgram.definesAt "mm0:admission-start" 1 = true ∧
      "mm0:admission-start" ∈ admissionHeads := by
  decide +kernel

/-- A call of the admission has one argument: the list of the declarations. -/
theorem admission_defined_at (admissions : List Admission) :
    admissionProgram.definesAt "mm0:admission-start" [encodeAdmissions admissions].length =
      true := by
  rw [List.length_singleton]
  exact admission_defined.1

theorem admissionPart_defined (admissions : List Admission) :
    (partAt admissionProgram admissionHeads).definesAt "mm0:admission-start"
      [encodeAdmissions admissions].length = true :=
  (definesAt_partAt admission_defined.2 _).trans (admission_defined_at admissions)

/-- What the part returns is what the program returns. -/
theorem admissionPart_applies_iff (admissions : List Admission) (result : EngineTerm) :
    Applies (partAt admissionProgram admissionHeads) dataEqualityHost "mm0:admission-start"
        [encodeAdmissions admissions] result ↔
      Applies admissionProgram dataEqualityHost "mm0:admission-start"
        [encodeAdmissions admissions] result :=
  applies_partAt_iff admissionHeads_closed dataEqualityHost admission_defined.2 _
    (admission_defined_at admissions) _

/-- **The run of the admission** of a list of declarations, from the empty
theory. -/
def admissionRun (admissions : List Admission) : Contexts.Term atomsReduce closedAtom :=
  callRun letterSpelling admissionTable "mm0:admission-start" [encodeAdmissions admissions]

/-- **The run of a result of the admission**: an encoded theory, or the
refusal. -/
def admittedRun (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    Contexts.Term atomsReduce closedAtom :=
  valueRun letterSpelling admissionTable (encodeTheoryResult result)

/-- **The candidate runs the kernel on a whole development**: the run of the
admission of a list of declarations reaches the run of an encoded result
exactly when the kernel's function returns that result. -/
theorem admission_run_iff (admissions : List Admission)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    atomsReduceTheory.Reaches (admissionRun admissions) (admittedRun result) ↔
      Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions = result :=
  admission_stores.run_result_iff admission_stored.orthogonal letterSpelling_injective
    encodeTheoryResult_injective (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) result

/-- **Every run without transition that the run of the admission reaches is
the run of what the kernel's function returns.** -/
theorem admission_run_unique (admissions : List Admission)
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (admissionRun admissions) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    target = admittedRun (Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions) :=
  admission_stores.run_unique admission_stored.orthogonal (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) reaches normal

/-- The run of the admission reaches the run of an encoded theory exactly when
the kernel admits the list of declarations, from the empty theory, to that
theory. -/
theorem admission_run_admits_iff (admissions : List Admission)
    (after : Mettapedia.Languages.MM0.Kernel.Theory) :
    atomsReduceTheory.Reaches (admissionRun admissions) (admittedRun (some after)) ↔
      Mettapedia.Languages.MM0.Kernel.Theory.Runs {} admissions after :=
  (admission_run_iff admissions (some after)).trans
    (Mettapedia.Languages.MM0.Kernel.Theory.run_eq_some_iff {} after admissions)

/-! ## One development admitted and one refused, by replaying their traces -/

/-- A development: a provable sort, a constant of it, an axiom asserting the
constant, and a theorem restating the axiom, proved by applying it. -/
def restatedDevelopment : List Admission :=
  [.sort 0 { provable := true }, .term 0 ⟨[], 0, ∅⟩, .axiomDecl 0 ⟨[], [], .term 0⟩,
    .theoremDecl 1 ⟨[], [], .term 0⟩ [] (.theoremApp 0 [] [])]

/-- The theory that the development declares. -/
def restatedTheory : Mettapedia.Languages.MM0.Kernel.Theory :=
  { sorts := [(0, { provable := true })]
    terms := [(0, ⟨[], 0, ∅⟩)]
    theorems := [(1, ⟨[], [], .term 0⟩), (0, ⟨[], [], .term 0⟩)] }

/-- The declarations of the development as data, written out. -/
theorem restatedDevelopment_data :
    encodeAdmissions restatedDevelopment =
      .list [.list [.sym "MM0:AdmitSort", natural 0,
          .list [.sym "MM0:Sort", .sym "False", .sym "False", .sym "True", .sym "False"]],
        .list [.sym "MM0:AdmitTerm", natural 0,
          .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]],
        .list [.sym "MM0:AdmitAxiom", natural 0,
          .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]]],
        .list [.sym "MM0:AdmitTheorem", natural 1,
          .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]],
          .list [], .list [.sym "MM0:TheoremApp", natural 0, .list [], .list []]]] := by
  simp [restatedDevelopment, encodeAdmissions, encodeAdmission, boolean,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSort,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeProof,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

/-- The theory as data, written out. -/
theorem restatedTheory_data :
    encodeTheoryResult (some restatedTheory) =
      .expr [.sym "Some", .list [.sym "MM0:Theory",
        .list [.list [natural 0,
          .list [.sym "MM0:Sort", .sym "False", .sym "False", .sym "True", .sym "False"]]],
        .list [.list [natural 0, .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]]],
        .list [],
        .list [.list [natural 1,
            .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]]],
          .list [natural 0,
            .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]]]]]] := by
  simp [restatedTheory, encodeTheoryResult, encodeTheory, encodeLookupResult, encodeNaturalTable,
    boolean,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSort,
    Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.encodeSorts,
    Mettapedia.Languages.MM0.Presentation.ComputationalTyping.encodeTable,
    Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions.encodeDefinitions,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorems,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

/-- The one declaration of a term as data, written out. -/
theorem undeclaredSort_data :
    encodeAdmissions [.term 0 ⟨[], 0, ∅⟩] =
      .list [.list [.sym "MM0:AdmitTerm", natural 0,
        .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]]] := by
  simp [encodeAdmissions, encodeAdmission,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals]

/-- **The trace of the admission of the development**: 343 steps, each the
code of its path and the index of its rule in the table. -/
def admissionTrace : List (Nat × Nat) :=
  [(1, 366), (1, 361), (13, 374), (1, 363), (13, 353), (109, 347), (109, 344), (877, 130),
    (7021, 373), (877, 131), (109, 345), (13, 355), (13, 356), (3549, 375), (1, 365), (1, 361),
    (13, 374), (1, 363), (13, 353), (109, 348), (877, 344), (7021, 130), (56173, 373), (7021,
    131), (877, 345), (1773, 258), (14061, 257), (14061, 252), (112365, 373), (14061, 253),
    (1773, 260), (14061, 241), (112365, 130), (898797, 374), (112365, 132), (898797, 380),
    (898797, 381), (112365, 133), (14061, 245), (14061, 229), (1773, 262), (1773, 236), (14061,
    373), (1773, 237), (109, 230), (13, 355), (13, 357), (7133, 375), (1, 365), (1, 361), (13,
    374), (1, 363), (13, 353), (109, 350), (877, 344), (7021, 130), (56173, 373), (7021, 131),
    (877, 345), (1773, 278), (14061, 257), (14061, 252), (112365, 373), (14061, 253), (1773,
    280), (14061, 273), (112365, 373), (14061, 274), (28397, 268), (225005, 11), (1797869, 5),
    (14380781, 374), (1797869, 7), (14380781, 380), (14380781, 381), (1797869, 8), (225005, 17),
    (28397, 270), (225005, 373), (28397, 271), (28397, 241), (225005, 130), (1797869, 374),
    (225005, 132), (1797869, 380), (1797869, 381), (225005, 133), (28397, 246), (1773, 230),
    (109, 230), (13, 355), (13, 359), (28637, 375), (1, 365), (1, 361), (13, 374), (1, 363),
    (13, 353), (109, 351), (56173, 344), (449389, 130), (3595117, 374), (449389, 132), (3595117,
    380), (3595117, 383), (449389, 134), (449389, 130), (3595117, 373), (449389, 131), (56173,
    345), (113517, 278), (899949, 257), (899949, 252), (7191405, 373), (899949, 253), (113517,
    280), (899949, 273), (7191405, 373), (899949, 274), (1817453, 268), (14400365, 11),
    (115063661, 5), (920370029, 374), (115063661, 7), (920370029, 380), (920370029, 381),
    (115063661, 8), (14400365, 17), (1817453, 270), (14400365, 373), (1817453, 271), (1817453,
    241), (14400365, 130), (115063661, 374), (14400365, 132), (115063661, 380), (115063661,
    381), (14400365, 133), (1817453, 246), (113517, 230), (7021, 230), (14189, 263), (112493,
    373), (14189, 264), (877, 230), (1773, 352), (1818349, 331), (14401261, 373), (1818349,
    332), (114413, 37), (900845, 373), (114413, 38), (1773, 227), (14061, 204), (112365, 130),
    (898797, 374), (112365, 132), (898797, 380), (898797, 381), (112365, 133), (14061, 207),
    (112365, 195), (898797, 97), (7190253, 72), (57521901, 373), (116242157, 373), (7190253,
    73), (898797, 99), (14530285, 79), (115193581, 373), (232634093, 373), (14530285, 80),
    (898797, 100), (898797, 92), (7190253, 373), (898797, 93), (112365, 197), (3651309, 112),
    (28817133, 373), (3651309, 113), (112365, 198), (898797, 188), (7190253, 373), (898797,
    189), (112365, 200), (898797, 102), (112365, 202), (14061, 209), (112365, 220), (898797,
    373), (112365, 221), (14061, 211), (112365, 392), (112365, 397), (112365, 400), (14061,
    213), (1773, 392), (1773, 396), (1773, 403), (14061, 393), (14061, 441), (112365, 448),
    (112365, 448), (112365, 447), (112365, 447), (112365, 448), (112365, 447), (112365, 448),
    (112365, 442), (227053, 441), (1799917, 448), (1799917, 448), (1799917, 448), (1799917,
    448), (1799917, 447), (1799917, 448), (1799917, 448), (1799917, 442), (3634925, 441),
    (28800749, 448), (28800749, 447), (28800749, 448), (28800749, 448), (28800749, 447),
    (28800749, 448), (28800749, 448), (28800749, 442), (58160877, 441), (460814061, 448),
    (460814061, 447), (460814061, 448), (460814061, 447), (460814061, 447), (460814061, 448),
    (460814061, 448), (460814061, 442), (930576109, 438), (58160877, 451), (3634925, 451),
    (227053, 451), (14061, 451), (28397, 403), (225005, 396), (225005, 403), (1797869, 393),
    (1797869, 441), (14380781, 448), (14380781, 447), (14380781, 448), (14380781, 448),
    (14380781, 447), (14380781, 447), (14380781, 448), (14380781, 442), (29060845, 441),
    (230387437, 448), (230387437, 447), (230387437, 448), (230387437, 448), (230387437, 447),
    (230387437, 447), (230387437, 448), (230387437, 442), (465268461, 441), (3686493933, 447),
    (3686493933, 447), (3686493933, 447), (3686493933, 447), (3686493933, 448), (3686493933,
    448), (3686493933, 442), (7444590317, 441), (58984197869, 447), (58984197869, 448),
    (58984197869, 447), (58984197869, 448), (58984197869, 448), (58984197869, 448),
    (58984197869, 442), (119113740013, 441), (943747460845, 447), (943747460845, 447),
    (943747460845, 448), (943747460845, 447), (943747460845, 448), (943747460845, 447),
    (943747460845, 448), (943747460845, 442), (1905820135149, 441), (15099959668461, 448),
    (15099959668461, 447), (15099959668461, 448), (15099959668461, 447), (15099959668461, 447),
    (15099959668461, 448), (15099959668461, 448), (15099959668461, 442), (30493122457325, 441),
    (241599354990317, 447), (241599354990317, 448), (241599354990317, 447), (241599354990317,
    447), (241599354990317, 448), (241599354990317, 448), (241599354990317, 448),
    (241599354990317, 442), (487889959612141, 441), (3865589680140013, 448), (3865589680140013,
    447), (3865589680140013, 448), (3865589680140013, 448), (3865589680140013, 447),
    (3865589680140013, 448), (3865589680140013, 448), (3865589680140013, 442),
    (7806239354089197, 438), (487889959612141, 451), (30493122457325, 451), (1905820135149,
    451), (119113740013, 451), (7444590317, 451), (465268461, 451), (29060845, 451), (1797869,
    451), (3632877, 403), (28798701, 395), (230125293, 381), (465006317, 434), (28798701, 451),
    (58158829, 400), (3632877, 451), (225005, 451), (454381, 400), (28397, 451), (1773, 451),
    (109, 230), (13, 355), (13, 360), (28637, 375), (1, 365), (1, 361), (13, 373), (1, 362)]

/-- The trace of the refused admission: twenty-six steps. -/
def refusalAdmissionTrace : List (Nat × Nat) :=
  [(1, 366), (1, 361), (13, 374), (1, 363), (13, 353), (109, 348), (877, 344), (7021, 130),
    (56173, 373), (7021, 131), (877, 345), (1773, 258), (14061, 257), (14061, 252), (112365,
    373), (14061, 253), (1773, 260), (14061, 241), (112365, 130), (898797, 373), (112365, 131),
    (14061, 242), (1773, 261), (109, 230), (13, 354), (1, 364)]

set_option maxRecDepth 100000 in
/-- **Replaying the trace in the table**: 343 steps take the call of the
admission of the development to the reading of its encoded theory. -/
theorem admission_instance_replays :
    replayCoded admissionTable admissionTrace
        (callTerm "mm0:admission-start"
          (data letterSpelling [encodeAdmissions restatedDevelopment])) =
      some (datum letterSpelling (encodeTheoryResult (some restatedTheory))) := by
  rw [restatedDevelopment_data, restatedTheory_data]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Negative**: twenty-six steps take the call of the admission of a term
whose sort is not declared to the reading of the refusal. -/
theorem admission_refusal_replays :
    replayCoded admissionTable refusalAdmissionTrace
        (callTerm "mm0:admission-start"
          (data letterSpelling [encodeAdmissions [.term 0 ⟨[], 0, ∅⟩]])) =
      some (datum letterSpelling (encodeTheoryResult none)) := by
  rw [undeclaredSort_data]
  decide +kernel

/-- **Positive**: so the run of the admission of the development reaches the
run of its theory, by the replayed reduction and without the general
theorem. -/
theorem admission_instance_admitted :
    atomsReduceTheory.Reaches (admissionRun restatedDevelopment)
      (admittedRun (some restatedTheory)) :=
  program_reaches admission_stores.runnable
    (admission_stored.replayCoded_reduces admission_instance_replays)

/-- So the kernel's function returns that theory. -/
theorem restatedDevelopment_admitted :
    Mettapedia.Languages.MM0.Kernel.Theory.run? {} restatedDevelopment = some restatedTheory :=
  (admission_run_iff restatedDevelopment (some restatedTheory)).mp admission_instance_admitted

/-- **Negative**: a term whose sort is not declared is refused: the run of its
admission reaches the run of the refusal, by the replayed reduction. -/
theorem admission_instance_refused :
    atomsReduceTheory.Reaches (admissionRun [.term 0 ⟨[], 0, ∅⟩]) (admittedRun none) :=
  program_reaches admission_stores.runnable
    (admission_stored.replayCoded_reduces admission_refusal_replays)

/-- **Negative**: and it does not reach the run of any theory. -/
theorem admission_instance_not_admitted (after : Mettapedia.Languages.MM0.Kernel.Theory) :
    ¬ atomsReduceTheory.Reaches (admissionRun [.term 0 ⟨[], 0, ∅⟩]) (admittedRun (some after)) := by
  intro reaches
  have refused := (admission_run_iff [.term 0 ⟨[], 0, ∅⟩] none).mp admission_instance_refused
  have admitted := (admission_run_iff [.term 0 ⟨[], 0, ∅⟩] (some after)).mp reaches
  rw [refused] at admitted
  cases admitted

#print axioms Stores.run_result_iff
#print axioms admissionHeads_closed
#print axioms admission_separated
#print axioms admission_ordered_stored
#print axioms admission_stored
#print axioms admission_stores
#print axioms admission_size
#print axioms admission_primitives
#print axioms admission_overlaps
#print axioms admission_run_iff
#print axioms admission_run_unique
#print axioms admission_run_admits_iff
#print axioms admission_instance_replays
#print axioms admission_refusal_replays
#print axioms admission_instance_admitted
#print axioms restatedDevelopment_admitted
#print axioms admission_instance_refused
#print axioms admission_instance_not_admitted

end Mettapedia.Logic.HostingStyles.StoredPrograms
