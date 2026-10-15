import Mettapedia.Logic.HostingStyles.StoredPrograms.Admission
import Mettapedia.Languages.MM0.Presentation.SpecificationControls

/-!
# The verification of a development against a specification, run by the candidate

The public entry of MM0's kernel takes a specification and the declarations
of a development with their proofs (`SpecificationAdmission.verify?`).  It
starts from the empty theory, admits the declarations in order, each checked
against the theory admitted so far, lets a public declaration consume the
next entry of the specification only when it matches it, allows as local
declarations only definitions and proved theorems, and accepts only when the
whole specification is consumed.  It is authored as one equation program
(`ComputationalSpecification.specificationProgram`): 404 equations under the
larger host, which compute what the kernel's function returns
(`ComputationalSpecification.verify_computes`).

Its head `mm0:spec-verify` reaches 199 heads and 395 of the equations
(`verificationHeads`, `verificationHeads_closed`).  Three heads are ordered:
the checked argument of a conversion, the match of a declaration with an
entry of the specification, and the test for an auxiliary declaration, each
with an equation that refuses in every other case; the program has no other
overlapping pair (`verification_overlaps`), no special form, and calls seven
primitives (`verification_primitives`).  The table
(`verificationTable`): the 384 rules of the equations of the other heads, the
33 ordered rules, and the eighty rules of the library.  **497 stored rules,
the same for every specification and every development**
(`verification_size`).  It stores the part of the program
(`verification_stores`) and is a stored table, hence orthogonal
(`verification_stored`).

**The candidate verifies a development against a specification.**

* The run of the verification reaches the run of an encoded result exactly
  when the kernel's function returns that result: the verified theory, or
  nothing (`verification_run_iff`).
* Every run without transition that it reaches is the run of what the
  kernel's function returns (`verification_run_unique`).
* It reaches the run of an encoded theory exactly when the kernel admits the
  declarations, from the empty theory and the specification, to that theory
  with nothing of the specification left (`verification_run_accepts_iff`).

Positive: the development of `restatedDevelopment`, all public, is verified
against the specification that states its sort, constant, axiom and theorem
(`verification_instance_verified`).  Negative: a development that declares the
statement of the theorem as a second axiom is refused against the
specification without it (`verification_instance_refused`), though the
admission alone admits it (`secondAxiom_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Languages.MM0.Kernel (Admission SpecificationEntry ProofDeclaration)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (encodeTheoryResult encodeTheoryResult_injective)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
  (specificationProgram encodeEntries encodeProofDeclarations verify_computes)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom)

/-- **The heads that the verification reaches.** -/
def verificationHeads : List String :=
  ["mm0:spec-verify", "mm0:spec-finish", "mm0:spec-run", "mm0:spec-run-view", "mm0:spec-finished",
    "mm0:spec-run-next", "mm0:spec-step", "mm0:spec-permitted", "mm0:spec-pending",
    "mm0:spec-guard", "mm0:spec-auxiliary", "mm0:spec-public", "mm0:spec-admitted",
    "mm0:admission-step", "mm0:admission-checked", "mm0:admission-check", "mm0:spec-match",
    "mm0:admission-fresh", "mm0:form-and", "mm0:form-term", "mm0:form-body", "mm0:form-theorem",
    "mm0:form-dummies", "mm0:admission-proof", "mm0:admission-publish", "mm0:spec-body",
    "mm0:form-term-context", "mm0:form-context", "mm0:form-dummies-view",
    "mm0:form-theorem-context", "mm0:body-dummies", "mm0:admission-missing", "nik:nat-table-get",
    "mm0:check-proof", "nik:list-append", "mm0:dummy-context", "nik:append-view",
    "nik:table-view", "mm0:proof", "mm0:form-context-from", "mm0:form-term-result",
    "mm0:form-sort", "mm0:form-dummies-next", "mm0:form-statements", "mm0:form-statement",
    "mm0:dummy-context-view", "mm0:body-context", "nik:table-equal", "mm0:data-at",
    "mm0:proof-declaration", "mm0:proof-converted", "mm0:conversion", "mm0:form-sort-info",
    "mm0:form-context-view", "mm0:form-bound-indices", "mm0:form-statement-type", "mm0:infer",
    "mm0:form-statements-view", "mm0:body-typed", "mm0:at-view", "mm0:infer-binder",
    "mm0:infer-declaration", "mm0:declaration", "mm0:infer-function", "mm0:conversion-refl-type",
    "mm0:conversion-swap", "mm0:conversion-first", "mm0:conversion-declaration",
    "mm0:conversion-unfold-declaration", "mm0:proof-instance", "mm0:instantiate-theorem",
    "mm0:proof-left", "mm0:form-bound-view", "mm0:form-not", "mm0:form-context-next",
    "mm0:form-binder", "mm0:form-statement-saturated", "mm0:form-statements-next",
    "mm0:body-free", "mm0:free-variables", "mm0:at-zero", "mm0:declaration-view",
    "mm0:infer-arguments", "mm0:conversion-refl-saturated", "mm0:conversion-join",
    "mm0:conversion-congruent", "mm0:conversion-arguments", "mm0:conversion-unfold-result",
    "mm0:unfold", "mm0:theorem-admissible", "mm0:check-admissible", "mm0:proof-premises",
    "mm0:proof-children", "mm0:proof-conversion-matched", "mm0:form-bound-next",
    "mm0:form-bound-index", "mm0:form-binder-deps", "mm0:free-spine", "mm0:body-free-view",
    "nik:nat-difference", "mm0:declaration-equal", "mm0:infer-bound-sort", "mm0:bound-sort",
    "mm0:infer-regular-type", "mm0:admissible-typed", "mm0:check-arguments",
    "mm0:unfold-declaration", "mm0:conversion-joined", "mm0:apply-args",
    "mm0:conversion-unfold-typed", "mm0:conversion-arguments-view", "mm0:theorem-prepared",
    "mm0:substitution-values", "mm0:proof-matched", "mm0:proof-children-view",
    "mm0:form-bound-item", "nik:difference-view", "mm0:free-variable-spine", "mm0:free-head",
    "mm0:free-argument", "mm0:bound-binder", "mm0:infer-sort-equal", "mm0:infer-saturated",
    "mm0:check-arguments-view", "mm0:admissible-entries", "mm0:entries",
    "mm0:substitution-values-view", "mm0:unfold-body", "mm0:apply-args-view",
    "mm0:conversion-argument", "mm0:theorem-hypotheses", "mm0:subst-list", "mm0:proof-child",
    "nik:difference-keep", "nik:nat-member", "mm0:support", "mm0:free-typed",
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

/-- **The heads whose equations are tried in order.** -/
def verificationOrdered : List String :=
  ["mm0:conversion-argument-checked", "mm0:spec-match", "mm0:spec-auxiliary"]

/-- **The table that runs the verification**: 497 rules, the same for every
specification and every development. -/
abbrev verificationTable : List RewriteRule :=
  partTable specificationProgram verificationHeads verificationOrdered

set_option maxRecDepth 100000 in
/-- The text of the specification program is of the class. -/
theorem verification_text : storableText specificationProgram = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- It calls only what the library computes. -/
theorem verification_calls :
    callsOnly specificationProgram dataEqualityHandled largerPrimitives = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The heads are closed under the calls of the program. -/
theorem verificationHeads_closed :
    closedUnderCalls specificationProgram verificationHeads = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The equations of the other heads are separated.** -/
theorem verification_separated :
    Separated (specificationProgram.filter fun equation =>
      !verificationOrdered.contains equation.head) :=
  separated_of_no_overlappingPairs (by decide +kernel)

set_option maxRecDepth 100000 in
/-- No equation has a primitive as its head. -/
theorem verification_noPrimitive : ∀ equation ∈ specificationProgram,
    equation.head ∉ largerPrimitives := by
  have checked : (specificationProgram.all fun equation =>
      !largerPrimitives.contains equation.head) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp checked equation member

set_option maxRecDepth 100000 in
/-- The ordered rules of the three heads are a stored table. -/
theorem verification_ordered_stored :
    StoredTable (orderedPart specificationProgram verificationOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem verification_stored : StoredTable verificationTable :=
  storedTable_partTable verification_text verification_separated verification_noPrimitive
    verification_ordered_stored

set_option maxRecDepth 100000 in
/-- **The table stores the part of the program.** -/
theorem verification_stores :
    Stores letterSpelling verificationTable (partAt specificationProgram verificationHeads)
      dataEqualityHost largerPrimitives :=
  stores_partTable verification_text verification_calls verificationHeads_closed
    (by decide +kernel) verification_stored

set_option maxRecDepth 100000 in
/-- 199 heads, 395 of the 404 equations, 497 rules. -/
theorem verification_size :
    verificationHeads.length = 199 ∧
      (partAt specificationProgram verificationHeads).length = 395 ∧
      specificationProgram.length = 404 ∧ verificationTable.length = 497 := by
  have counted : ((partAt specificationProgram verificationHeads).filter fun equation =>
      !verificationOrdered.contains equation.head).length = 384 ∧
      (orderedPart specificationProgram verificationOrdered).length = 33 ∧
      (partAt specificationProgram verificationHeads).length = 395 ∧
      specificationProgram.length = 404 := by decide +kernel
  refine ⟨by decide, counted.2.2.1, counted.2.2.2, ?_⟩
  rw [partTable_length, counted.1, counted.2.1]

set_option maxRecDepth 100000 in
/-- **The primitives that the specification program calls**: seven, the
equality of data among them. -/
theorem verification_primitives :
    calledPrimitives specificationProgram dataEqualityHandled =
      ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
        "nik:nat-add", "nik:data-eq"] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Its overlapping pairs**: eight, at the three ordered heads.  Each is an
equation with the equation that refuses in every other case. -/
theorem verification_overlaps :
    overlappingPairs specificationProgram =
      [("conversion-argument-checked", "conversion-argument-refused"),
        ("spec-match-sort", "spec-match-kind-refuse"),
        ("spec-match-term", "spec-match-kind-refuse"),
        ("spec-match-definition", "spec-match-kind-refuse"),
        ("spec-match-axiom", "spec-match-kind-refuse"),
        ("spec-match-theorem", "spec-match-kind-refuse"),
        ("spec-aux-definition", "spec-aux-refuse"), ("spec-aux-theorem", "spec-aux-refuse")] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem verification_defined :
    specificationProgram.definesAt "mm0:spec-verify" 2 = true ∧
      "mm0:spec-verify" ∈ verificationHeads := by
  decide +kernel

/-- A call of the verification has two arguments: the specification and the
declarations. -/
theorem verification_defined_at (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    specificationProgram.definesAt "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations].length = true := by
  have length :
      [encodeEntries specification, encodeProofDeclarations declarations].length = 2 := rfl
  rw [length]
  exact verification_defined.1

theorem verificationPart_defined (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    (partAt specificationProgram verificationHeads).definesAt "mm0:spec-verify"
      [encodeEntries specification, encodeProofDeclarations declarations].length = true :=
  (definesAt_partAt verification_defined.2 _).trans
    (verification_defined_at specification declarations)

/-- What the part returns is what the program returns. -/
theorem verificationPart_applies_iff (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) (result : EngineTerm) :
    Applies (partAt specificationProgram verificationHeads) dataEqualityHost "mm0:spec-verify"
        [encodeEntries specification, encodeProofDeclarations declarations] result ↔
      Applies specificationProgram dataEqualityHost "mm0:spec-verify"
        [encodeEntries specification, encodeProofDeclarations declarations] result :=
  applies_partAt_iff verificationHeads_closed dataEqualityHost verification_defined.2 _
    (verification_defined_at specification declarations) _

/-- **The run of the verification** of the declarations of a development
against a specification. -/
def verificationRun (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) : Contexts.Term atomsReduce closedAtom :=
  callRun letterSpelling verificationTable "mm0:spec-verify"
    [encodeEntries specification, encodeProofDeclarations declarations]

/-- **The run of a result of the verification**: an encoded theory, or the
refusal. -/
def verifiedRun (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    Contexts.Term atomsReduce closedAtom :=
  valueRun letterSpelling verificationTable (encodeTheoryResult result)

/-- **The candidate verifies a development against a specification**: the run
of the verification reaches the run of an encoded result exactly when the
kernel's function returns that result. -/
theorem verification_run_iff (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    atomsReduceTheory.Reaches (verificationRun specification declarations) (verifiedRun result) ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification declarations =
        result :=
  verification_stores.run_result_iff verification_stored.orthogonal letterSpelling_injective
    encodeTheoryResult_injective (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) result

/-- **Every run without transition that the run of the verification reaches
is the run of what the kernel's function returns.** -/
theorem verification_run_unique (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (verificationRun specification declarations) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    target = verifiedRun
      (Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification
        declarations) :=
  verification_stores.run_unique verification_stored.orthogonal
    (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) reaches normal

/-- The run of the verification reaches the run of an encoded theory exactly
when the kernel admits the declarations, from the empty theory and the
specification, to that theory with nothing of the specification left. -/
theorem verification_run_accepts_iff (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) (theory : Mettapedia.Languages.MM0.Kernel.Theory) :
    atomsReduceTheory.Reaches (verificationRun specification declarations)
        (verifiedRun (some theory)) ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩
        declarations ⟨theory, []⟩ :=
  (verification_run_iff specification declarations (some theory)).trans
    (Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify_eq_some_iff specification
      declarations theory)

/-! ## One development verified, one refused -/

/-- A specification: a provable sort, a constant of it, an axiom asserting the
constant, and a theorem restating the axiom. -/
def restatedSpecification : List SpecificationEntry :=
  [.sort 0 { provable := true }, .term 0 ⟨[], 0, ∅⟩, .axiomDecl 0 ⟨[], [], .term 0⟩,
    .theoremDecl 1 ⟨[], [], .term 0⟩]

/-- The specification without the theorem. -/
def axiomSpecification : List SpecificationEntry :=
  [.sort 0 { provable := true }, .term 0 ⟨[], 0, ∅⟩, .axiomDecl 0 ⟨[], [], .term 0⟩]

/-- The declarations of `restatedDevelopment`, all public. -/
def restatedDeclarations : List ProofDeclaration :=
  restatedDevelopment.map fun admission => ⟨admission, false⟩

/-- Declarations that state the theorem as a second axiom. -/
def secondAxiomDeclarations : List ProofDeclaration :=
  [⟨.sort 0 { provable := true }, false⟩, ⟨.term 0 ⟨[], 0, ∅⟩, false⟩,
    ⟨.axiomDecl 0 ⟨[], [], .term 0⟩, false⟩, ⟨.axiomDecl 1 ⟨[], [], .term 0⟩, false⟩]

/-- **Positive**: the run of the verification of the development against its
specification reaches the run of its theory. -/
theorem verification_instance_verified :
    atomsReduceTheory.Reaches (verificationRun restatedSpecification restatedDeclarations)
      (verifiedRun (some restatedTheory)) :=
  verification_stores.run_reaches
    (verificationPart_defined restatedSpecification restatedDeclarations)
    ((verificationPart_applies_iff restatedSpecification restatedDeclarations _).mpr
      Mettapedia.Languages.MM0.Presentation.ComputationalSpecification.Controls.public_theorem_has_checked_proof)

/-- **Negative**: the second axiom is not in the specification: the run of the
verification reaches the run of the refusal. -/
theorem verification_instance_refused :
    atomsReduceTheory.Reaches (verificationRun axiomSpecification secondAxiomDeclarations)
      (verifiedRun none) :=
  verification_stores.run_reaches
    (verificationPart_defined axiomSpecification secondAxiomDeclarations)
    ((verificationPart_applies_iff axiomSpecification secondAxiomDeclarations _).mpr
      Mettapedia.Languages.MM0.Presentation.ComputationalSpecification.Controls.specification_rejects_that_extra_axiom)

/-- **Negative**: and it reaches the run of no theory. -/
theorem verification_instance_not_verified (theory : Mettapedia.Languages.MM0.Kernel.Theory) :
    ¬ atomsReduceTheory.Reaches (verificationRun axiomSpecification secondAxiomDeclarations)
      (verifiedRun (some theory)) := by
  intro reaches
  have refused := (verification_run_iff axiomSpecification secondAxiomDeclarations none).mp
    verification_instance_refused
  have verified := (verification_run_iff axiomSpecification secondAxiomDeclarations
    (some theory)).mp reaches
  rw [refused] at verified
  cases verified

/-- The admission alone admits those declarations: the second axiom is
refused by the specification, not by the checks of the kernel. -/
theorem secondAxiom_admitted :
    atomsReduceTheory.Reaches
      (admissionRun (secondAxiomDeclarations.map fun declaration => declaration.admission))
      (admittedRun (some restatedTheory)) :=
  (admission_run_iff _ _).mpr
    Mettapedia.Languages.MM0.Presentation.ComputationalSpecification.Controls.extra_axiom_can_pass_logical_admission

#print axioms verificationHeads_closed
#print axioms verification_separated
#print axioms verification_ordered_stored
#print axioms verification_stored
#print axioms verification_stores
#print axioms verification_size
#print axioms verification_primitives
#print axioms verification_overlaps
#print axioms verification_run_iff
#print axioms verification_run_unique
#print axioms verification_run_accepts_iff
#print axioms verification_instance_verified
#print axioms verification_instance_refused
#print axioms verification_instance_not_verified
#print axioms secondAxiom_admitted

end Mettapedia.Logic.HostingStyles.StoredPrograms
