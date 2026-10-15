import Mettapedia.Logic.HostingStyles.NameEquality.RunningNames
import Mettapedia.Logic.HostingStyles.StoredPrograms.Check

/-!
# The check of an MM0 certificate, with names as constants

The check of a certificate of the MM0 calculus is the equation program
`calculusProgram`.  With names in letters its table has 390 rules, and it
compares the names of a request letter by letter.  Here the same program is
read with **every name one constant**, over the test of names.

The table (`checkTableNames`): the 223 rules of the equations of the unordered
heads, the 87 ordered rules of the six ordered heads, and the library of
sixty-seven rules.  **377 stored rules** (`checkNames_partSizes`,
`checkNames_size`), a stored table (`checkNames_stored`), which stores the
part of the program over the test (`checkNames_stores`).  The facts about the
program are those of the table with letters: its text is of the class, its
heads are closed, the equations of the unordered heads are separated.  Only
the ordered rules are tested again.

**In the theory of the table with the family of the equality of names:**

* the check of a certificate reduces to the verdict of the checker, and every
  normal form that it reaches is that verdict (`checkNames_reduces_unique`);
* **some certificate's check reduces to `True` exactly when MM0's kernel
  derives the judgment** (`checkNames_reduces_iff_derives`).

**The candidate runs it**, in the space that stores the table and the rules of
the family for the names of the request (`checkRunNames`): the run of the
check reaches the run of the verdict, and every run without transition that it
reaches is that one (`checkNames_run_unique`); for some certificate the run of
its check reaches the accepting run exactly when the kernel derives the
judgment (`checkNames_run_iff_derives`).

Positive: in the control theory, which declares an axiom, the check of the
witness that applies the axiom reaches the accepting run
(`checkNames_axiom_accepted`).  Negative: in the theory without the axiom no
certificate of the statement does (`checkNames_without_axiom_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies boolean)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.MM0.Kernel (Context Preterm ProofWitness)
open Mettapedia.Languages.MM0.Presentation.Calculus (family derivesJ kernelCalculus)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
  (calculusProgram request certificate_computes derives_of_returned returned_of_derives
    witness_accepted_iff settledEvaluate)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-- **The table that runs the check with names as constants**: 377 rules. -/
abbrev checkTableNames : List RewriteRule :=
  partTableIn constantSpelling calculusProgram certificateHeads certificateOrdered

set_option maxRecDepth 100000 in
/-- The ordered rules of the six heads, with names as constants, are a stored
table. -/
theorem checkNames_ordered_stored :
    StoredTable (orderedPartIn constantSpelling calculusProgram certificateOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem checkNames_stored : StoredTable checkTableNames :=
  storedTable_partTableIn constantSpelling_apart check_text check_separated check_noPrimitive
    checkNames_ordered_stored libraryConstants_fit

/-- **The table stores the part of the program over the test of names.** -/
theorem checkNames_stores :
    StoresWithNames checkTableNames (partAt calculusProgram certificateHeads) dataEqualityHost
      largerPrimitives :=
  storesWithNames_partTable check_text check_calls certificateHeads_closed (by decide)
    checkNames_stored

set_option maxRecDepth 100000 in
/-- **The sizes of the first two parts of the table**: 223 rules of equations
of the unordered heads and 87 ordered rules.  The other two parts are those of
every such table: the nineteen rules of the shared host and the forty-eight
that compare data. -/
theorem checkNames_partSizes :
    (partRules constantSpelling calculusProgram certificateHeads certificateOrdered
        .equations).length = 223 ∧
      (partRules constantSpelling calculusProgram certificateHeads certificateOrdered
        .ordered).length = 87 := by
  refine ⟨?_, ?_⟩
  · rw [partRules, List.length_map]
    decide +kernel
  · decide +kernel

/-- 223 rules of equations, 87 ordered rules and the sixty-seven of the
library: 377 rules, beside the 390 with names in letters. -/
theorem checkNames_size : checkTableNames.length = 377 := by
  have sizes := checkNames_partSizes
  simp only [partRules, List.length_map] at sizes
  rw [partTableIn_length, sizes.1, sizes.2]

/-! ## In the theory with the family -/

/-- **The check of a certificate for a goal, as a term**: the call of the
checker on the request, with names as constants. -/
def checkCall (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) : LF.Term :=
  callTerm "mm0:certificate" (data constantSpelling (request T goal proof))

/-- **A verdict, as a term**: `True` or `False`. -/
def verdictTerm (verdict : Bool) : LF.Term := datum constantSpelling (boolean verdict)

/-- **Negative**: the two verdicts are two terms. -/
theorem verdictTerm_injective : Function.Injective verdictTerm := by
  intro first second same
  have terms := datum_injective constantSpelling_injective same
  cases first <;> cases second <;> first | rfl | simp [boolean] at terms

/-- **The check reduces to the verdict of the checker, and every normal form
that it reaches is that verdict.** -/
theorem checkNames_reduces_unique (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    Reduces (withNames checkTableNames) (checkCall T goal proof)
        (verdictTerm (check kernelCalculus (settledEvaluate T) goal proof)) ∧
      ∀ normalForm : LF.Term,
        Reduces (withNames checkTableNames) (checkCall T goal proof) normalForm →
        IsNormal (Step (withNames checkTableNames)) normalForm →
          normalForm = verdictTerm (check kernelCalculus (settledEvaluate T) goal proof) := by
  have applies := (checkPart_applies_iff T goal proof _).mpr (certificate_computes T goal proof)
  exact ⟨checkNames_stores.reduces (checkPart_defined T goal proof) applies,
    fun normalForm reaches normal => checkNames_stores.normalForm_unique
      checkNames_stored.orthogonal (checkPart_defined T goal proof) applies reaches normal⟩

/-- **With names as constants and the test of names as steps, the check
decides MM0 proofs.**  For some certificate, its check for the judgment
reduces to `True`, exactly when MM0's kernel derives the judgment in the
theory. -/
theorem checkNames_reduces_iff_derives (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (context : Context) (hypotheses : List Preterm) (expression : Preterm) :
    (∃ proof, Reduces (withNames checkTableNames)
        (checkCall T (derivesJ context hypotheses expression) proof) (verdictTerm true)) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  have total : ∀ proof, ∃ value, Applies (partAt calculusProgram certificateHeads)
      dataEqualityHost "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) value :=
    fun proof => ⟨_, (checkPart_applies_iff T _ proof _).mpr (certificate_computes T _ proof)⟩
  constructor
  · rintro ⟨proof, reaches⟩
    exact derives_of_returned T ((checkPart_applies_iff T _ proof _).mp
      ((checkNames_stores.reduces_iff checkNames_stored.orthogonal (checkPart_defined T _ proof)
        (total proof) (boolean true)).mp reaches))
  · intro derived
    obtain ⟨proof, returned⟩ := returned_of_derives T derived
    exact ⟨proof, checkNames_stores.reduces (checkPart_defined T _ proof)
      ((checkPart_applies_iff T _ proof _).mpr returned)⟩

/-! ## Run by the candidate, in the space of the names of the request -/

/-- **The names of a check**: those of the request, with the fixed names of
the theory of the table with the family. -/
def checkNames (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) : List String :=
  namesFor checkTableNames (checkCall T goal proof)

/-- **The run of the check** of a certificate for a goal, in the space that
stores the table and the rules of the family for the names of the check. -/
def checkRunNames (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) : Contexts.Term atomsReduce closedAtom :=
  localRun checkTableNames (checkNames T goal proof) (checkCall T goal proof)

/-- **The run of a verdict**, in the space of a check. -/
def verdictRunNames (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) (verdict : Bool) :
    Contexts.Term atomsReduce closedAtom :=
  localRun checkTableNames (checkNames T goal proof) (verdictTerm verdict)

/-- **Negative**: in the space of a check the accepting run is not the
refusing run. -/
theorem verdictRunNames_injective (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    Function.Injective (verdictRunNames T goal proof) :=
  fun _ _ same => verdictTerm_injective (localRun_injective _ _ same)

/-- **The run of the check reaches the run of the verdict of the checker**,
and every run without transition that it reaches is that one. -/
theorem checkNames_run_unique (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) :
    atomsReduceTheory.Reaches (checkRunNames T goal proof)
        (verdictRunNames T goal proof (check kernelCalculus (settledEvaluate T) goal proof)) ∧
      ∀ target : Contexts.Term atomsReduce closedAtom,
        atomsReduceTheory.Reaches (checkRunNames T goal proof) target →
        (∀ next, ¬ atomsReduceTheory.rewrites target next) →
          target = verdictRunNames T goal proof
            (check kernelCalculus (settledEvaluate T) goal proof) := by
  have applies := (checkPart_applies_iff T goal proof _).mpr (certificate_computes T goal proof)
  exact ⟨checkNames_stores.run_reaches (namesFor_covers _ _) (namesFor_within _ _)
      (checkPart_defined T goal proof) applies,
    fun target reaches normal => checkNames_stores.run_unique checkNames_stored.orthogonal
      (namesFor_covers _ _) (namesFor_within _ _) (checkPart_defined T goal proof) applies reaches
      normal⟩

/-- **The candidate checks MM0 proofs with names as constants.**  For some
certificate, the run of its check for the judgment reaches the accepting run,
exactly when MM0's kernel derives the judgment in the theory. -/
theorem checkNames_run_iff_derives (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (context : Context) (hypotheses : List Preterm) (expression : Preterm) :
    (∃ proof, atomsReduceTheory.Reaches
        (checkRunNames T (derivesJ context hypotheses expression) proof)
        (verdictRunNames T (derivesJ context hypotheses expression) proof true)) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  have total : ∀ proof, ∃ value, Applies (partAt calculusProgram certificateHeads)
      dataEqualityHost "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) value :=
    fun proof => ⟨_, (checkPart_applies_iff T _ proof _).mpr (certificate_computes T _ proof)⟩
  constructor
  · rintro ⟨proof, reaches⟩
    exact derives_of_returned T ((checkPart_applies_iff T _ proof _).mp
      ((checkNames_stores.run_reaches_iff checkNames_stored.orthogonal (namesFor_covers _ _)
        (namesFor_within _ _) (checkPart_defined T _ proof) (total proof) (boolean true)).mp
        reaches))
  · intro derived
    obtain ⟨proof, returned⟩ := returned_of_derives T derived
    exact ⟨proof, checkNames_stores.run_reaches (namesFor_covers _ _) (namesFor_within _ _)
      (checkPart_defined T _ proof) ((checkPart_applies_iff T _ proof _).mpr returned)⟩

/-- **A submitted kernel witness is checked to the accepting run, through its
translation at any fuel, exactly when the kernel checks it.** -/
theorem witnessNames_run_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (fuel : Nat)
    (context : Context) (hypotheses : List Preterm) (witness : ProofWitness)
    (expression : Preterm) :
    ProofWitness.Checks T.termSignature T.definitionSignature T.theoremSignature context
        hypotheses witness expression ↔
      atomsReduceTheory.Reaches
        (checkRunNames T (derivesJ context hypotheses expression)
          (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate T fuel context
            hypotheses witness))
        (verdictRunNames T (derivesJ context hypotheses expression)
          (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate T fuel context
            hypotheses witness) true) := by
  have total : ∃ value, Applies (partAt calculusProgram certificateHeads) dataEqualityHost
      "mm0:certificate" (request T (derivesJ context hypotheses expression)
        (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate T fuel context
          hypotheses witness)) value :=
    ⟨_, (checkPart_applies_iff T _ _ _).mpr (certificate_computes T _ _)⟩
  exact (witness_accepted_iff T fuel context hypotheses witness expression).trans
    (((checkNames_stores.run_reaches_iff checkNames_stored.orthogonal (namesFor_covers _ _)
      (namesFor_within _ _) (checkPart_defined T _ _) total (boolean true)).trans
      (checkPart_applies_iff T _ _ _)).symm)

/-! ## One check accepted, one refused -/

open Mettapedia.Languages.MM0.Presentation.Calculus.Controls
  (withAxiom axiomDecl constant axiom_instance) in
/-- **Positive**: in the control theory, the check of the witness that applies
the axiom reaches the accepting run. -/
theorem checkNames_axiom_accepted :
    atomsReduceTheory.Reaches
      (checkRunNames withAxiom (derivesJ [] [] constant)
        (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate withAxiom 1 [] []
          (.theoremApp 0 [] [])))
      (verdictRunNames withAxiom (derivesJ [] [] constant)
        (Mettapedia.Languages.MM0.Presentation.Calculus.Witness.translate withAxiom 1 [] []
          (.theoremApp 0 [] [])) true) :=
  (witnessNames_run_iff withAxiom 1 [] [] (.theoremApp 0 [] []) constant).mp
    (.theoremApp (index := 0) (declaration := axiomDecl) (arguments := [])
      (instantiation := ⟨[], constant⟩) rfl axiom_instance .nil)

open Mettapedia.Languages.MM0.Presentation.Calculus.Controls
  (withoutAxiom constant nothing_derivable) in
/-- **Negative**: in the theory without the axiom, no certificate of the
statement is checked to the accepting run. -/
theorem checkNames_without_axiom_refused :
    ¬ ∃ proof, atomsReduceTheory.Reaches
      (checkRunNames withoutAxiom (derivesJ [] [] constant) proof)
      (verdictRunNames withoutAxiom (derivesJ [] [] constant) proof true) :=
  fun accepted =>
    nothing_derivable ((checkNames_run_iff_derives withoutAxiom [] [] constant).mp accepted)

#print axioms checkNames_ordered_stored
#print axioms checkNames_stored
#print axioms checkNames_stores
#print axioms checkNames_partSizes
#print axioms checkNames_size
#print axioms checkNames_reduces_unique
#print axioms checkNames_reduces_iff_derives
#print axioms checkNames_run_unique
#print axioms checkNames_run_iff_derives
#print axioms witnessNames_run_iff
#print axioms checkNames_axiom_accepted
#print axioms checkNames_without_axiom_refused

end Mettapedia.Logic.HostingStyles.NameEquality
