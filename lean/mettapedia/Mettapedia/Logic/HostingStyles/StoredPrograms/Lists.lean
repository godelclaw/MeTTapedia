import Mettapedia.Logic.HostingStyles.StoredPrograms.Naturals

/-!
# Lists as cells, with the list view and the list former as rules

A list value of the engine is read as the kind `list` on the cells of its
items (`datum`).  The shared host has two primitives on list values.

* `nik:list-view` exposes the first item and the rest: the symbol `List:Nil`
  for the empty list, and the expression `(List:Cons first rest)` otherwise,
  where `rest` is again a list value.  Two rules (`listViewRules`).
* `nik:list-cons` forms the list value of a first item and a list value.  One
  rule (`listConsRules`).

Each agrees with the host on all data (`lists_realized`).  The three rules
are orthogonal (`listRules_orthogonal`).  Negative: the list former on a tail
that is no list value has no step, where the host faults (`listCons_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Host natural natural? boolean computationalHost listView PrimitiveResult)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst orthogonalCheck)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

namespace ListView

def empty (N : Spelling) : RewriteRule :=
  ⟨callTerm "nik:list-view" [tag "list" (.con "nil")], tag "sym" (N.write "List:Nil")⟩

def cell (N : Spelling) : RewriteRule :=
  ⟨callTerm "nik:list-view" [tag "list" (.app (.app (.con "cons") (.var 0)) (.var 1))],
    tag "expr" (cells [tag "sym" (N.write "List:Cons"), .var 0, tag "list" (.var 1)])⟩

end ListView

/-- **The rules of `nik:list-view`.** -/
def listViewRules (N : Spelling) : List RewriteRule := [ListView.empty N, ListView.cell N]

/-- **The rule of `nik:list-cons`.** -/
def listFormer : RewriteRule :=
  ⟨callTerm "nik:list-cons" [.var 0, tag "list" (.var 1)],
    tag "list" (.app (.app (.con "cons") (.var 0)) (.var 1))⟩

def listConsRules : List RewriteRule := [listFormer]

/-- **Lists as cells, with their view and their former, as rules**: three
rules. -/
def listRules (N : Spelling) : List RewriteRule := listViewRules N ++ listConsRules

/-- The primitives that these rules compute. -/
def listPrimitives : List String := ["nik:list-view", "nik:list-cons"]

/-- **The view of a list value**, by the rules: the reading of what the host
returns. -/
theorem listView_reduces (N : Spelling) {theory : Theory} (holds : Holds theory (listViewRules N))
    (values : List EngineTerm) :
    Reduces theory (callTerm "nik:list-view" [datum N (.list values)])
      (datum N (listView values)) := by
  cases values with
  | nil =>
      exact fires (rule := ListView.empty N) (holds _ (by simp [listViewRules])) []
        (by simp only [ListView.empty]; instances; rfl)
        (by simp only [ListView.empty]; instances; rfl)
  | cons first rest =>
      exact fires (rule := ListView.cell N) (holds _ (by simp [listViewRules]))
        [datum N first, cells (data N rest)]
        (by simp only [ListView.cell]; instances; rfl)
        (by simp only [ListView.cell]; instances; rfl)

/-- **The list of a first item and a list value**, by the rule. -/
theorem listCons_reduces (N : Spelling) {theory : Theory} (holds : Holds theory listConsRules)
    (first : EngineTerm) (rest : List EngineTerm) :
    Reduces theory (callTerm "nik:list-cons" [datum N first, datum N (.list rest)])
      (datum N (.list (first :: rest))) :=
  fires (rule := listFormer) (holds _ (by simp [listConsRules]))
    [datum N first, cells (data N rest)]
    (by simp only [listFormer]; instances; rfl) (by simp only [listFormer]; instances; rfl)

theorem listView_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:list-view" arguments =
      (match arguments with
        | [.list values] => .value (listView values)
        | _ => .fault) := rfl

theorem listCons_unfold (arguments : List EngineTerm) :
    computationalHost.primitive "nik:list-cons" arguments =
      (match arguments with
        | [first, .list rest] => .value (.list (first :: rest))
        | _ => .fault) := rfl

/-- **The list rules agree with the shared host**: when the host returns a
value for the list view or the list former on data, the call on the readings
of the data reduces to the reading of that value. -/
theorem lists_realized (N : Spelling) {theory : Theory} (holds : Holds theory (listRules N)) :
    RealizesPrimitives N theory computationalHost listPrimitives := by
  intro head member arguments result returned
  simp only [listPrimitives, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [listView_unfold] at returned
    split at returned
    · next values =>
      obtain rfl := (PrimitiveResult.value.inj returned)
      exact listView_reduces N holds.left values
    · cases returned
  · rw [listCons_unfold] at returned
    split at returned
    · next first rest =>
      obtain rfl := (PrimitiveResult.value.inj returned)
      exact listCons_reduces N holds.right first rest
    · cases returned

/-- The host handles both list primitives. -/
theorem lists_handled : ∀ head ∈ listPrimitives, ∀ arguments : List EngineTerm,
    computationalHost.primitive head arguments ≠ .unhandled := by
  intro head member arguments
  simp only [listPrimitives, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [listView_unfold]; split <;> simp
  · rw [listCons_unfold]; split <;> simp

/-! ## With names written as constants -/

/-- **The three rules are orthogonal.** -/
theorem listRules_orthogonal : orthogonalCheck (listRules constantSpelling) = true := by
  decide

/-- **Positive**: the view of the list of `a` and `b`. -/
theorem listView_example :
    Reduces (programTheory (listRules constantSpelling))
      (callTerm "nik:list-view" [datum constantSpelling (.list [.sym "a", .sym "b"])])
      (datum constantSpelling (.expr [.sym "List:Cons", .sym "a", .list [.sym "b"]])) :=
  listView_reduces constantSpelling (holds_programTheory _).left [.sym "a", .sym "b"]

/-- **Negative**: the list former on a tail that is no list value has no
step, where the host faults. -/
theorem listCons_stuck :
    computationalHost.primitive "nik:list-cons" [.sym "a", .sym "b"] = .fault ∧
      IsNormal (Step (programTheory (listRules constantSpelling)))
        (callTerm "nik:list-cons" (data constantSpelling [.sym "a", .sym "b"])) :=
  ⟨rfl, Dedukti.normal_of_normalTest
    (Mettapedia.Logic.HostingStyles.AtomsReduce.programCover (listRules constantSpelling)) _
    (by decide)⟩

#print axioms listView_reduces
#print axioms listCons_reduces
#print axioms lists_realized
#print axioms lists_handled
#print axioms listRules_orthogonal
#print axioms listView_example
#print axioms listCons_stuck

end Mettapedia.Logic.HostingStyles.StoredPrograms
