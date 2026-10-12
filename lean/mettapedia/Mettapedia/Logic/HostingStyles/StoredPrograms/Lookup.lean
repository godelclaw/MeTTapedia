import Mettapedia.Logic.HostingStyles.StoredPrograms.SmallPrograms
import Mettapedia.Logic.HostingStyles.StoredPrograms.Running
import Mettapedia.Languages.MM0.Presentation.Calculus

/-!
# One kernel operation, end to end: the theorem declared at an index

MM0's kernel has three operations (`Calculus.family`).  The smallest is the
lookup of the theorem declared at an index (`Calculus.lookupComputation`): the
table-lookup program of five equations, under the shared host, on the list of
the theorems of the theory and the index.  It calls two primitives, the list
view and the equality of numbers, has no `let`, and its equations do not
overlap (`Inventory.lean`).

Its table (`lookupTable`) is the five rules of its equations and the nineteen
rules of the shared host: twenty-four stored rules, orthogonal
(`lookup_orthogonal`).

**The candidate runs the operation.**  The run of the lookup of an index, in
the space of the table, reaches the run of the encoded declaration exactly
when the kernel's function returns that declaration
(`theoremLookup_run_iff`), and reaches the run of the refusal exactly when the
kernel's function returns none (`theoremLookup_run_refuses_iff`).  Every run
without transition that it reaches is the run of what the kernel's function
returns (`theoremLookup_run_unique`).  The theory is data: its theorems are an
argument of the call, and the same twenty-four rules serve every theory.

One instance is checked by running the table (`twoTheorems`): the lookup of
index five in a theory with theorems at three and five takes twenty steps of
the function `run`, and no fewer (`lookup_instance_nineteen`), and gives the
encoded second declaration (`lookup_instance_runs`), which the kernel's
function returns (`lookup_instance_kernel`); the lookup of index four gives
the refusal in twenty-two steps (`lookup_instance_refuses`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host natural boolean computationalHost naturalLookupProgram encodeNaturalTable
    encodeLookupResult Applies)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces orthogonalCheck)
open Mettapedia.Languages.MM0.Kernel (TheoremDecl)
open Mettapedia.Languages.MM0.Presentation.Calculus (lookupComputation)
open Mettapedia.Languages.MM0.Presentation.ComputationalProof (encodeTheorem)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom program_reaches)

/-- **The table that runs the lookup of a theorem**: twenty-four rules, the
same for every theory. -/
abbrev lookupTable : List RewriteRule := sharedTable constantSpelling naturalLookupProgram

/-- **The run of the lookup of an index** in the theorems of a theory. -/
def theoremLookupRun (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat) :
    Contexts.Term atomsReduce closedAtom :=
  callRun constantSpelling lookupTable (lookupComputation T).head
    ((lookupComputation T).encodeQuery index)

/-- **The run of an answer of the lookup**: an encoded declaration, or the
refusal. -/
def theoremAnswerRun (T : Mettapedia.Languages.MM0.Kernel.Theory) (answer : Option TheoremDecl) :
    Contexts.Term atomsReduce closedAtom :=
  valueRun constantSpelling lookupTable ((lookupComputation T).encodeAnswer answer)

theorem theoremLookup_defined (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat) :
    (lookupComputation T).program.definesAt (lookupComputation T).head
      ((lookupComputation T).encodeQuery index).length = true := rfl

/-- **The candidate runs the lookup of a theorem**: the run of the lookup of
an index reaches the run of an encoded declaration exactly when the theory
declares that theorem at the index. -/
theorem theoremLookup_run_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat)
    (declaration : TheoremDecl) :
    atomsReduceTheory.Reaches (theoremLookupRun T index) (theoremAnswerRun T (some declaration)) ↔
      T.theoremSignature index = some declaration :=
  lookup_stores.authored_run_iff (lookupComputation T) (programTheory_orthogonal lookup_orthogonal)
    constantSpelling_injective index (theoremLookup_defined T index) declaration

/-- The run of the lookup reaches the run of the refusal exactly when the
theory declares no theorem at the index. -/
theorem theoremLookup_run_refuses_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat) :
    atomsReduceTheory.Reaches (theoremLookupRun T index) (theoremAnswerRun T none) ↔
      T.theoremSignature index = none := by
  refine (lookup_stores.authored_run_refuses_iff (lookupComputation T)
    (programTheory_orthogonal lookup_orthogonal) constantSpelling_injective index
    (theoremLookup_defined T index)).trans ?_
  constructor
  · intro absent
    cases found : T.theoremSignature index with
    | none => rfl
    | some declaration => exact absurd ⟨declaration, found⟩ absent
  · rintro absent ⟨declaration, found⟩
    have declared : T.theoremSignature index = some declaration := found
    rw [absent] at declared
    cases declared

/-- **Every run without transition that the run of the lookup reaches is the
run of what the kernel's function returns.** -/
theorem theoremLookup_run_unique (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat)
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (theoremLookupRun T index) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    target = theoremAnswerRun T (T.theoremSignature index) :=
  (lookup_run encodeTheorem T.theorems index).2.2 target reaches normal

/-! ## One instance, checked by running the table -/

/-- A theory with two theorems, declared at three and at five. -/
def twoTheorems : Mettapedia.Languages.MM0.Kernel.Theory :=
  { theorems := [(3, ⟨[], [], .term 0⟩), (5, ⟨[], [.term 0], .term 1⟩)] }

/-- **The kernel's function** returns the second declaration at five, and
nothing at four. -/
theorem lookup_instance_kernel :
    twoTheorems.theoremSignature 5 = some ⟨[], [.term 0], .term 1⟩ ∧
      twoTheorems.theoremSignature 4 = none := by
  decide

/-- **Running the table**: the function `run` takes the call of the lookup of
five to the reading of the encoded second declaration. -/
theorem lookup_instance_runs :
    run lookupTable 20
        (callTerm "nik:nat-table-get"
          (data constantSpelling ((lookupComputation twoTheorems).encodeQuery 5))) =
      datum constantSpelling
        ((lookupComputation twoTheorems).encodeAnswer (some ⟨[], [.term 0], .term 1⟩)) := by
  decide +kernel

/-- Nineteen steps do not suffice. -/
theorem lookup_instance_nineteen :
    run lookupTable 19
        (callTerm "nik:nat-table-get"
          (data constantSpelling ((lookupComputation twoTheorems).encodeQuery 5))) ≠
      datum constantSpelling
        ((lookupComputation twoTheorems).encodeAnswer (some ⟨[], [.term 0], .term 1⟩)) := by
  decide +kernel

/-- **Running the table** on the lookup of four gives the refusal. -/
theorem lookup_instance_refuses :
    run lookupTable 22
        (callTerm "nik:nat-table-get"
          (data constantSpelling ((lookupComputation twoTheorems).encodeQuery 4))) =
      datum constantSpelling ((lookupComputation twoTheorems).encodeAnswer none) := by
  decide +kernel

/-- **So the candidate reaches that run**, by the computed reduction and
without the general theorem. -/
theorem lookup_instance_reaches :
    atomsReduceTheory.Reaches (theoremLookupRun twoTheorems 5)
      (theoremAnswerRun twoTheorems (some ⟨[], [.term 0], .term 1⟩)) :=
  program_reaches lookup_stores.runnable (reduces_of_run lookup_instance_runs)

/-- **Negative**: the run of the lookup of five does not reach the run of the
first declaration. -/
theorem lookup_instance_not_first :
    ¬ atomsReduceTheory.Reaches (theoremLookupRun twoTheorems 5)
      (theoremAnswerRun twoTheorems (some ⟨[], [], .term 0⟩)) := by
  intro reaches
  have found := (theoremLookup_run_iff twoTheorems 5 _).mp reaches
  revert found
  decide

#print axioms theoremLookup_run_iff
#print axioms theoremLookup_run_refuses_iff
#print axioms theoremLookup_run_unique
#print axioms lookup_instance_kernel
#print axioms lookup_instance_runs
#print axioms lookup_instance_nineteen
#print axioms lookup_instance_refuses
#print axioms lookup_instance_reaches
#print axioms lookup_instance_not_first

end Mettapedia.Logic.HostingStyles.StoredPrograms
