import Mettapedia.Logic.HostingStyles.StoredPrograms.LargerHost
import Mettapedia.Languages.MM0.Presentation.CalculusProgramContract
import Mettapedia.Languages.MM0.Presentation.CalculusControls

/-!
# The whole check as one stored table

The check of a certificate of the MM0 calculus is authored as one equation
program (`ComputationalCalculus.calculusProgram`): its equations read a goal
and a certificate as data, instantiate the kernel rule that a node names,
compare its conclusion with the goal, check the children against the
premises, and at a computed leaf call the lookup, the instantiation or the
conversion on the theory.  The kernel rules are equations of that program,
generated from the rules of the presentation, and the leaves are calls of the
three operations.

Its head `mm0:certificate` reaches 119 heads and 252 of the 280 equations
(`certificateHeads`, `certificateHeads_closed`).  Six heads have overlapping
equations and are ordered (`certificateOrdered`): the instantiation of a rule
by its name, with its refusal of an unknown name; two readings of pattern
data; the validity of an argument; the walk through premises and children;
and the checked argument of a conversion.

The table (`checkTable`): the 223 rules of the equations of the other heads,
the 87 ordered rules of the six, and the eighty rules of the library.  **390
stored rules, the same for every theory, every goal and every certificate**
(`check_size`).  It stores the part of the program (`check_stores`) and is a
stored table, hence orthogonal (`check_stored`).

**The candidate runs the check.**

* The run of the check of a certificate for a goal reaches the accepting run
  exactly when the specified checker accepts the certificate once its leaves
  name enough fuel (`check_run_accepts_iff`).
* It reaches the run of exactly one verdict, and every run without transition
  that it reaches is that one (`check_run_unique`).
* **Some certificate's check reaches the accepting run exactly when MM0's
  kernel derives the judgment** (`check_run_iff_derives`).
* A submitted kernel witness is checked to the accepting run, through its
  translation, exactly when the kernel checks it (`witness_run_iff`).

Positive: in the control theory, which declares an axiom, the check of the
witness that applies the axiom reaches the accepting run
(`check_axiom_accepted`).  Negative: in the theory without the axiom no
certificate of the statement is checked to the accepting run
(`check_without_axiom_refused`), and the check of that witness reaches the
refusing run (`check_missing_axiom_refused`).

The theory, the goal and the certificate are data in the call; the rules are
data in the space; the candidate's own reduction does the rest: matching the
left side of a rule, by its evaluator, at any position.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies boolean)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.MM0.Kernel (Context Preterm ProofWitness)
open Mettapedia.Languages.MM0.Presentation.Calculus (family derivesJ kernelCalculus)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
  (calculusProgram request certificate_computes certificate_accepts_iff derives_of_returned
    returned_of_derives witness_accepted_iff mapLeaves refuel settledEvaluate)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom)

/-- **The heads that the check of a certificate reaches.** -/
def certificateHeads : List String :=
  ["mm0:certificate", "mm0:certificate-valid", "mm0:pattern-valid-all", "mm0:certificate-leaf",
    "nik:nat-table-get", "mm0:instantiate-theorem", "mm0:conversion", "nik:table-view",
    "mm0:conversion-refl-type", "mm0:infer", "mm0:conversion-swap", "mm0:conversion-first",
    "mm0:conversion-declaration", "mm0:declaration", "mm0:conversion-unfold-declaration",
    "mm0:theorem-admissible", "mm0:check-admissible", "mm0:pattern-valid-view",
    "mm0:certificate-rule", "mm0:rule-instance", "mm0:declaration-view", "mm0:infer-binder",
    "mm0:data-at", "mm0:infer-declaration", "mm0:infer-function", "mm0:admissible-typed",
    "mm0:check-arguments", "nik:table-equal", "mm0:conversion-refl-saturated",
    "mm0:conversion-join", "mm0:conversion-congruent", "mm0:conversion-arguments",
    "mm0:conversion-unfold-result", "mm0:unfold", "mm0:theorem-prepared", "mm0:substitution-values",
    "mm0:pattern-list", "mm0:pattern-cons", "mm0:pattern-both", "mm0:pattern-valid",
    "mm0:certificate-conclusion", "mm0:at-view", "mm0:declaration-equal", "mm0:infer-arguments",
    "mm0:check-arguments-view", "mm0:admissible-entries", "mm0:entries",
    "mm0:substitution-values-view", "mm0:unfold-declaration", "mm0:conversion-joined",
    "mm0:apply-args", "mm0:conversion-unfold-typed", "mm0:conversion-arguments-view",
    "mm0:theorem-hypotheses", "mm0:subst-list", "mm0:certificate-children", "mm0:at-zero",
    "mm0:infer-bound-sort", "mm0:bound-sort", "mm0:infer-regular-type", "mm0:check-arguments-next",
    "mm0:check-binder", "mm0:entries-view", "mm0:check-rows", "mm0:unfold-body",
    "mm0:apply-args-view", "mm0:conversion-argument", "mm0:subst-list-view",
    "mm0:theorem-conclusion", "mm0:subst", "mm0:certificate-children-view", "mm0:bound-binder",
    "mm0:infer-sort-equal", "mm0:infer-saturated", "mm0:check-sort", "mm0:check-type",
    "mm0:rows-view", "mm0:lookup", "mm0:subst-function", "mm0:unfold-arguments",
    "mm0:conversion-argument-checked", "mm0:conversion-binder-sort", "mm0:subst-list-head",
    "mm0:certificate-rest", "mm0:check-saturated", "mm0:rows-next", "mm0:check-row",
    "mm0:subst-argument", "mm0:lookup-zero", "mm0:unfold-dummies", "mm0:check-dummies",
    "mm0:conversion-argument-tail", "mm0:subst-list-tail", "mm0:check-pairs", "mm0:dummies-view",
    "nik:list-append", "mm0:variable-images", "nik:append-view", "mm0:pairs-view", "mm0:dummy-sort",
    "mm0:variable-images-view", "mm0:pairs-next", "mm0:check-pair", "mm0:dummy-fresh",
    "mm0:fresh-all", "mm0:pair-depends", "mm0:depends", "mm0:fresh-all-view", "nik:nat-member",
    "mm0:support-disjoint", "mm0:support", "mm0:fresh-all-next", "mm0:fresh-for",
    "mm0:support-binder", "mm0:support-function", "nik:member-view", "mm0:dependency-not",
    "mm0:support-argument", "nik:member-equal"]

/-- **The heads whose equations are tried in order.** -/
def certificateOrdered : List String :=
  ["mm0:conversion-argument-checked", "mm0:rule-instance", "mm0:pattern-cons", "mm0:pattern-list",
    "mm0:pattern-valid", "mm0:certificate-children-view"]

/-- **The table that runs the check**: 390 rules. -/
abbrev checkTable : List RewriteRule :=
  partTable calculusProgram certificateHeads certificateOrdered

set_option maxRecDepth 100000 in
/-- The text of the program of the check is of the class. -/
theorem check_text : storableText calculusProgram = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- It calls only what the library computes. -/
theorem check_calls : callsOnly calculusProgram dataEqualityHandled largerPrimitives = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The heads are closed under the calls of the program. -/
theorem certificateHeads_closed : closedUnderCalls calculusProgram certificateHeads = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The equations of the other heads are separated.** -/
theorem check_separated :
    Separated (calculusProgram.filter fun equation =>
      !certificateOrdered.contains equation.head) :=
  separated_of_no_overlappingPairs (by decide +kernel)

set_option maxRecDepth 100000 in
/-- No equation has a primitive as its head. -/
theorem check_noPrimitive : ∀ equation ∈ calculusProgram, equation.head ∉ largerPrimitives := by
  have checked : (calculusProgram.all fun equation =>
      !largerPrimitives.contains equation.head) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp checked equation member

set_option maxRecDepth 100000 in
/-- The ordered rules of the six heads are a stored table. -/
theorem check_ordered_stored : StoredTable (orderedPart calculusProgram certificateOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem check_stored : StoredTable checkTable :=
  storedTable_partTable check_text check_separated check_noPrimitive check_ordered_stored

/-- **The table stores the part of the program.** -/
theorem check_stores :
    Stores letterSpelling checkTable (partAt calculusProgram certificateHeads) dataEqualityHost
      largerPrimitives :=
  stores_partTable check_text check_calls certificateHeads_closed (by decide) check_stored

set_option maxRecDepth 100000 in
/-- 119 heads, 252 of the 280 equations, 390 rules. -/
theorem check_size :
    certificateHeads.length = 119 ∧ (partAt calculusProgram certificateHeads).length = 252 ∧
      checkTable.length = 390 := by
  have counted : ((partAt calculusProgram certificateHeads).filter fun equation =>
      !certificateOrdered.contains equation.head).length = 223 ∧
      (orderedPart calculusProgram certificateOrdered).length = 87 ∧
      (partAt calculusProgram certificateHeads).length = 252 := by decide +kernel
  refine ⟨by decide, counted.2.2, ?_⟩
  rw [partTable_length, counted.1, counted.2.1]

set_option maxRecDepth 100000 in
/-- **What the part needs**: eight primitives, no special form, fifteen
overlapping pairs. -/
theorem checkPart_inventory :
    calledPrimitives (partAt calculusProgram certificateHeads) dataEqualityHandled =
        ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
          "nik:nat-add", "nik:data-eq", "nik:nat-lt"] ∧
      specialForms (partAt calculusProgram certificateHeads) = [] ∧
      (overlappingPairs (partAt calculusProgram certificateHeads)).length = 15 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem check_defined :
    calculusProgram.definesAt "mm0:certificate" 5 = true ∧ "mm0:certificate" ∈ certificateHeads := by
  decide +kernel

/-- A request has five arguments: the three tables of the theory, the goal and
the certificate. -/
theorem request_length (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) : (request T goal proof).length = 5 := by
  simp [request, Mettapedia.Languages.MM0.Presentation.ComputationalCalculus.theoryArguments]

theorem check_defined_at (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    calculusProgram.definesAt "mm0:certificate" (request T goal proof).length = true := by
  rw [request_length]
  exact check_defined.1

theorem checkPart_defined (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    (partAt calculusProgram certificateHeads).definesAt "mm0:certificate"
      (request T goal proof).length = true :=
  (definesAt_partAt check_defined.2 _).trans (check_defined_at T goal proof)

/-- **The run of the check** of a certificate for a goal, in a theory. -/
def checkRun (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) : Contexts.Term atomsReduce closedAtom :=
  callRun letterSpelling checkTable "mm0:certificate" (request T goal proof)

/-- **The run of a verdict**: the accepting run for `true`, the refusing run
for `false`. -/
def verdictRun (verdict : Bool) : Contexts.Term atomsReduce closedAtom :=
  valueRun letterSpelling checkTable (boolean verdict)

/-- **Negative**: the accepting run is not the refusing run. -/
theorem verdictRun_injective : Function.Injective verdictRun := by
  intro first second same
  have terms := valueRun_injective letterSpelling_injective checkTable same
  cases first <;> cases second <;> first | rfl | simp [boolean] at terms

/-- What the part returns is what the program returns. -/
theorem checkPart_applies_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) (result : EngineTerm) :
    Applies (partAt calculusProgram certificateHeads) dataEqualityHost "mm0:certificate"
        (request T goal proof) result ↔
      Applies calculusProgram dataEqualityHost "mm0:certificate" (request T goal proof) result :=
  applies_partAt_iff certificateHeads_closed dataEqualityHost check_defined.2 _
    (check_defined_at T goal proof) _

/-- **The run of the check reaches the run of the verdict of the checker**,
and every run without transition that it reaches is that one. -/
theorem check_run_unique (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    atomsReduceTheory.Reaches (checkRun T goal proof)
        (verdictRun (check kernelCalculus (settledEvaluate T) goal proof)) ∧
      ∀ target : Contexts.Term atomsReduce closedAtom,
        atomsReduceTheory.Reaches (checkRun T goal proof) target →
        (∀ next, ¬ atomsReduceTheory.rewrites target next) →
          target = verdictRun (check kernelCalculus (settledEvaluate T) goal proof) := by
  have applies := (checkPart_applies_iff T goal proof _).mpr (certificate_computes T goal proof)
  exact ⟨check_stores.run_reaches (checkPart_defined T goal proof) applies,
    fun target reaches normal => check_stores.run_unique check_stored.orthogonal
      (checkPart_defined T goal proof) applies reaches normal⟩

/-- **The run of the check reaches the accepting run exactly when the
specified checker accepts the certificate**, once its leaves name enough
fuel. -/
theorem check_run_accepts_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    atomsReduceTheory.Reaches (checkRun T goal proof) (verdictRun true) ↔
      ∃ fuel, check kernelCalculus (family T).evaluate goal (mapLeaves (refuel T fuel) proof) =
        true := by
  have total : ∃ value, Applies (partAt calculusProgram certificateHeads) dataEqualityHost
      "mm0:certificate" (request T goal proof) value :=
    ⟨_, (checkPart_applies_iff T goal proof _).mpr (certificate_computes T goal proof)⟩
  exact ((check_stores.run_reaches_iff check_stored.orthogonal letterSpelling_injective
    (checkPart_defined T goal proof) total (boolean true)).trans
    (checkPart_applies_iff T goal proof _)).trans (certificate_accepts_iff T goal proof)

/-- **The candidate checks MM0 proofs.**  For some certificate, the run of its
check for the judgment reaches the accepting run, exactly when MM0's kernel
derives the judgment in the theory. -/
theorem check_run_iff_derives (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (hypotheses : List Preterm) (expression : Preterm) :
    (∃ proof, atomsReduceTheory.Reaches
        (checkRun T (derivesJ context hypotheses expression) proof) (verdictRun true)) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  have total : ∀ proof, ∃ value, Applies (partAt calculusProgram certificateHeads)
      dataEqualityHost "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) value :=
    fun proof => ⟨_, (checkPart_applies_iff T _ proof _).mpr (certificate_computes T _ proof)⟩
  constructor
  · rintro ⟨proof, reaches⟩
    exact derives_of_returned T ((checkPart_applies_iff T _ proof _).mp
      ((check_stores.run_reaches_iff check_stored.orthogonal letterSpelling_injective
        (checkPart_defined T _ proof) (total proof) (boolean true)).mp reaches))
  · intro derived
    obtain ⟨proof, returned⟩ := returned_of_derives T derived
    exact ⟨proof, check_stores.run_reaches (checkPart_defined T _ proof)
      ((checkPart_applies_iff T _ proof _).mpr returned)⟩

/-- **A submitted kernel witness is checked to the accepting run, through its
translation at any fuel, exactly when the kernel checks it.** -/
theorem witness_run_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (fuel : Nat)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness)
    (expression : Preterm) :
    ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature context
        hypotheses witness expression ↔
      atomsReduceTheory.Reaches
        (checkRun T (derivesJ context hypotheses expression)
          (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate T fuel context
            hypotheses witness))
        (verdictRun true) := by
  have total : ∃ value, Applies (partAt calculusProgram certificateHeads) dataEqualityHost
      "mm0:certificate" (request T (derivesJ context hypotheses expression)
        (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate T fuel context
          hypotheses witness)) value :=
    ⟨_, (checkPart_applies_iff T _ _ _).mpr (certificate_computes T _ _)⟩
  exact (witness_accepted_iff T fuel context hypotheses witness expression).trans
    (((check_stores.run_reaches_iff check_stored.orthogonal letterSpelling_injective
      (checkPart_defined T _ _) total (boolean true)).trans (checkPart_applies_iff T _ _ _)).symm)

/-! ## One check accepted, one refused -/

open Mettapedia.Languages.MM0.Presentation.Calculus.Controls
  (withAxiom withoutAxiom axiomDecl constant axiom_instance nothing_derivable) in
/-- **Positive**: in the control theory, the check of the witness that
applies the axiom reaches the accepting run. -/
theorem check_axiom_accepted :
    atomsReduceTheory.Reaches
      (checkRun withAxiom (derivesJ [] [] constant)
        (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate withAxiom 1 [] []
          (.theoremApp 0 [] [])))
      (verdictRun true) :=
  (witness_run_iff withAxiom 1 [] [] (.theoremApp 0 [] []) constant).mp
    (.theoremApp (index := 0) (declaration := axiomDecl) (arguments := [])
      (instantiation := ⟨[], constant⟩) rfl axiom_instance .nil)

open Mettapedia.Languages.MM0.Presentation.Calculus.Controls
  (withoutAxiom constant nothing_derivable) in
/-- **Negative**: in the theory without the axiom, no certificate of the
statement is checked to the accepting run. -/
theorem check_without_axiom_refused :
    ¬ ∃ proof, atomsReduceTheory.Reaches
      (checkRun withoutAxiom (derivesJ [] [] constant) proof) (verdictRun true) :=
  fun accepted =>
    nothing_derivable ((check_run_iff_derives withoutAxiom [] [] constant).mp accepted)

open Mettapedia.Languages.MM0.Presentation.Calculus.Controls (withoutAxiom constant) in
/-- **Negative**: there, the check of the witness that applies the
missing axiom reaches the refusing run. -/
theorem check_missing_axiom_refused :
    atomsReduceTheory.Reaches
      (checkRun withoutAxiom (derivesJ [] [] constant)
        (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate withoutAxiom 1 [] []
          (.theoremApp 0 [] [])))
      (verdictRun false) := by
  have unique := (check_run_unique withoutAxiom (derivesJ [] [] constant)
    (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate withoutAxiom 1 [] []
      (.theoremApp 0 [] []))).1
  cases verdict : check kernelCalculus (settledEvaluate withoutAxiom) (derivesJ [] [] constant)
      (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate withoutAxiom 1 [] []
        (.theoremApp 0 [] [])) with
  | false =>
      rw [verdict] at unique
      exact unique
  | true =>
      rw [verdict] at unique
      exact absurd ⟨_, unique⟩ check_without_axiom_refused

#print axioms certificateHeads_closed
#print axioms check_separated
#print axioms check_ordered_stored
#print axioms check_stored
#print axioms check_stores
#print axioms check_size
#print axioms checkPart_inventory
#print axioms verdictRun_injective
#print axioms check_run_unique
#print axioms check_run_accepts_iff
#print axioms check_run_iff_derives
#print axioms witness_run_iff
#print axioms check_axiom_accepted
#print axioms check_without_axiom_refused
#print axioms check_missing_axiom_refused

end Mettapedia.Logic.HostingStyles.StoredPrograms
