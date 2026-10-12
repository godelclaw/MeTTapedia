import Mettapedia.Logic.HostingStyles.StoredPrograms.SharedHost
import Mettapedia.Logic.HostingStyles.StoredPrograms.Candidate
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalDifferenceProgram
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalLookupProgram

/-!
# The small programs of the engine, run by the candidate

The engine's directory has four small programs with a proved result: list
append, membership in a list of numbers, lookup in a table keyed by numbers,
and removal of the numbers of one list from another.

**None of them is in the class without primitives**: each calls the list view
of the shared host (`smallPrograms_not_hostFree`).  Each is in the class with
the seven primitives that rules compute, and its table, the rules of its
equations followed by the nineteen rules of the shared host, stores it and is
orthogonal:

| program | equations | stored rules | stored | orthogonal |
|---|---|---|---|---|
| `listAppendProgram` | 3 | 22 | `listAppend_stores` | `listAppend_orthogonal` |
| `naturalMembershipProgram` | 5 | 24 | `membership_stores` | `membership_orthogonal` |
| `naturalLookupProgram` | 5 | 24 | `lookup_stores` | `lookup_orthogonal` |
| `naturalDifferenceProgram` | 10 | 29 | `difference_stores` | `difference_orthogonal` |

So the candidate runs each: the run of the call reaches the run of the
result that the engine's theorem states, and every run without transition
that it reaches is that one (`listAppend_run`, `membership_run`,
`lookup_run`, `difference_run`).  Names are written as constants.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host natural boolean computationalHost listAppendProgram
    naturalMembershipProgram naturalLookupProgram naturalDifferenceProgram encodeNaturalTable
    encodeLookupResult Applies)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces orthogonalCheck)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom)

/-- **None of the four is in the class without primitives**: each calls the
list view of the shared host. -/
theorem smallPrograms_not_hostFree :
    ¬ HostFree listAppendProgram computationalHost ∧
      ¬ HostFree naturalMembershipProgram computationalHost ∧
      ¬ HostFree naturalLookupProgram computationalHost ∧
      ¬ HostFree naturalDifferenceProgram computationalHost := by
  refine ⟨listAppend_not_hostFree, ?_, ?_, ?_⟩ <;> intro hostFree
  · cases hostFree "nik:list-view" (by decide) (by decide) [.list []]
  · cases hostFree "nik:list-view" (by decide) (by decide) [.list []]
  · cases hostFree "nik:list-view" (by decide) (by decide) [.list []]

/-- **What the candidate does with a call that a stored table answers**: the
run of the call reaches the run of the value, which has no transition, and
every run without transition that the run of the call reaches is that one. -/
def RunsTo (rules : List RewriteRule) (head : String) (arguments : List EngineTerm)
    (value : EngineTerm) : Prop :=
  atomsReduceTheory.Reaches (callRun constantSpelling rules head arguments)
      (valueRun constantSpelling rules value) ∧
    (∀ target, ¬ atomsReduceTheory.rewrites (valueRun constantSpelling rules value) target) ∧
    ∀ target : Contexts.Term atomsReduce closedAtom,
      atomsReduceTheory.Reaches (callRun constantSpelling rules head arguments) target →
      (∀ next, ¬ atomsReduceTheory.rewrites target next) →
        target = valueRun constantSpelling rules value

/-- A call that the engine answers runs to its value, in an orthogonal table
that stores the program. -/
theorem Stores.runsTo {rules : List RewriteRule} {program : Program} {host : Host}
    {primitives : List String} (stores : Stores constantSpelling rules program host primitives)
    (checked : orthogonalCheck rules = true) {head : String} {arguments : List EngineTerm}
    {value : EngineTerm} (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments value) : RunsTo rules head arguments value :=
  ⟨stores.run_reaches defined applies, stores.run_value_normal value,
    fun _ reaches normal =>
      stores.run_unique (programTheory_orthogonal checked) defined applies reaches normal⟩

/-- **Negative**: a call does not run to two values. -/
theorem RunsTo.unique {rules : List RewriteRule} {head : String} {arguments : List EngineTerm}
    {first second : EngineTerm} (toFirst : RunsTo rules head arguments first)
    (toSecond : RunsTo rules head arguments second) : first = second :=
  valueRun_injective constantSpelling_injective rules
    (toSecond.2.2 _ toFirst.1 toFirst.2.1)

/-! ## List append -/

theorem listAppend_stores :
    Stores constantSpelling (sharedTable constantSpelling listAppendProgram) listAppendProgram
      computationalHost sharedPrimitives :=
  stores_shared constantSpelling (by decide) (by decide) sharedRules_runnable
    sharedRules_rewriteCalls

theorem listAppend_orthogonal :
    orthogonalCheck (sharedTable constantSpelling listAppendProgram) = true := by
  decide

/-- **The candidate appends two lists**, for all lists of data. -/
theorem listAppend_run (left right : List EngineTerm) :
    RunsTo (sharedTable constantSpelling listAppendProgram) "nik:list-append"
      [.list left, .list right] (.list (left ++ right)) :=
  listAppend_stores.runsTo listAppend_orthogonal (by simp [Program.definesAt, listAppendProgram])
    (DeterministicEquations.list_append_computes left right)

/-! ## Membership in a list of numbers -/

theorem membership_stores :
    Stores constantSpelling (sharedTable constantSpelling naturalMembershipProgram)
      naturalMembershipProgram computationalHost sharedPrimitives :=
  stores_shared constantSpelling (by decide) (by decide) sharedRules_runnable
    sharedRules_rewriteCalls

theorem membership_orthogonal :
    orthogonalCheck (sharedTable constantSpelling naturalMembershipProgram) = true := by
  decide

/-- **The candidate decides membership in a list of numbers.** -/
theorem membership_run (index : Nat) (values : List Nat) :
    RunsTo (sharedTable constantSpelling naturalMembershipProgram) "nik:nat-member"
      [natural index, .list (values.map natural)] (boolean (decide (index ∈ values))) :=
  membership_stores.runsTo membership_orthogonal (by simp [Program.definesAt, naturalMembershipProgram])
    (DeterministicEquations.natural_membership_computes index values)

/-! ## Lookup in a table keyed by numbers -/

theorem lookup_stores :
    Stores constantSpelling (sharedTable constantSpelling naturalLookupProgram)
      naturalLookupProgram computationalHost sharedPrimitives :=
  stores_shared constantSpelling (by decide) (by decide) sharedRules_runnable
    sharedRules_rewriteCalls

theorem lookup_orthogonal :
    orthogonalCheck (sharedTable constantSpelling naturalLookupProgram) = true := by
  decide

/-- **The candidate looks a key up in a table**, for every encoding of the
stored values. -/
theorem lookup_run {α : Type} (encode : α → EngineTerm) (entries : List (Nat × α)) (key : Nat) :
    RunsTo (sharedTable constantSpelling naturalLookupProgram) "nik:nat-table-get"
      [encodeNaturalTable encode entries, natural key]
      (encodeLookupResult ((entries.lookup key).map encode)) :=
  lookup_stores.runsTo lookup_orthogonal (by simp [Program.definesAt, naturalLookupProgram])
    (DeterministicEquations.natural_lookup_computes encode entries key)

/-! ## Removal of the numbers of a list -/

theorem difference_stores :
    Stores constantSpelling (sharedTable constantSpelling naturalDifferenceProgram)
      naturalDifferenceProgram computationalHost sharedPrimitives :=
  stores_shared constantSpelling (by decide) (by decide) sharedRules_runnable
    sharedRules_rewriteCalls

theorem difference_orthogonal :
    orthogonalCheck (sharedTable constantSpelling naturalDifferenceProgram) = true := by
  decide

/-- **The candidate removes from a list of numbers those of another list.** -/
theorem difference_run (source removed : List Nat) :
    RunsTo (sharedTable constantSpelling naturalDifferenceProgram) "nik:nat-difference"
      [.list (source.map natural), .list (removed.map natural)]
      (.list ((source.filter fun index => !removed.contains index).map natural)) :=
  difference_stores.runsTo difference_orthogonal
    (by simp [Program.definesAt, naturalDifferenceProgram, naturalMembershipProgram,
      DeterministicEquations.naturalDifferenceEquations])
    (DeterministicEquations.natural_difference_computes source removed)

/-- The numbers of stored rules. -/
theorem smallPrograms_ruleCounts :
    (sharedTable constantSpelling listAppendProgram).length = 22 ∧
      (sharedTable constantSpelling naturalMembershipProgram).length = 24 ∧
      (sharedTable constantSpelling naturalLookupProgram).length = 24 ∧
      (sharedTable constantSpelling naturalDifferenceProgram).length = 29 := by
  simp [sharedTable, programRules, sharedRules_length, listAppendProgram, naturalMembershipProgram,
    naturalLookupProgram, naturalDifferenceProgram, DeterministicEquations.naturalDifferenceEquations]

#print axioms smallPrograms_not_hostFree
#print axioms Stores.runsTo
#print axioms RunsTo.unique
#print axioms listAppend_stores
#print axioms listAppend_orthogonal
#print axioms listAppend_run
#print axioms membership_run
#print axioms lookup_run
#print axioms difference_run
#print axioms smallPrograms_ruleCounts

end Mettapedia.Logic.HostingStyles.StoredPrograms
