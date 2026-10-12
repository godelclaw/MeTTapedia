import Mettapedia.Logic.HostingStyles.StoredPrograms.Overlap
import Mettapedia.GSLT.LanguageDef.AuthoredComputation

/-!
# The part of a program that a call reaches

A kernel operation is a head of a larger program: the program of the
instantiation of a theorem is the whole proof program, of which the
operation's head reaches a part.  What a table has to store is that part.

* `partAt program heads` keeps the equations whose head is in the list.
* `closedUnderCalls program heads` tests that the equations of these heads
  call only heads of the list, or heads that the program does not define.
* `reachableHeads program rounds heads` adds, round by round, the defined
  heads that the equations of the list call.

**A call of a head of a closed list has the same outcome in the part as in the
program, at every fuel** (`apply_partAt`), so it returns the same values
(`applies_partAt_iff`).  An authored computation whose head is in a closed
list is an authored computation of the part, with the same relation
(`restrictComputation`).

Positive: in `detour`, the head `keep` reaches itself alone
(`detour_keep_closed`).  Negative: `main` alone is not closed, it calls `keep`
and `loop` (`detour_main_not_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored (AuthoredComputation)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env matchTerms Applies DispatchAgreement CallsWithin)

/-- **The part of a program at a list of heads**: the equations whose head is
in the list, in their order. -/
def partAt (program : Program) (heads : List String) : Program :=
  program.filter fun equation => heads.contains equation.head

/-- **Whether a list of heads is closed under the calls of a program**: an
equation whose head is in the list calls only heads of the list or heads that
the program does not define. -/
def closedUnderCalls (program : Program) (heads : List String) : Bool :=
  program.all fun equation =>
    !heads.contains equation.head ||
      (DeterministicEquations.calledHeads equation.body).all fun head =>
        !program.defines head || heads.contains head

/-- One round: the heads of a list, and the defined heads that their
equations call. -/
def calledFrom (program : Program) (heads : List String) : List String :=
  (heads ++ (partAt program heads).flatMap fun equation =>
    (DeterministicEquations.calledHeads equation.body).filter fun head => program.defines head).eraseDups

/-- **The heads that a list of heads reaches** in a number of rounds. -/
def reachableHeads (program : Program) : Nat → List String → List String
  | 0, heads => heads
  | rounds + 1, heads => reachableHeads program rounds (calledFrom program heads)

theorem mem_partAt {program : Program} {heads : List String} {equation : Equation} :
    equation ∈ partAt program heads ↔ equation ∈ program ∧ equation.head ∈ heads := by
  simp [partAt]

/-- A search that answers nothing outside a filter finds the same in the
filtered list. -/
theorem findSome?_filter_of_none {α β : Type} (keep : α → Bool) (answer : α → Option β)
    (silent : ∀ item, keep item = false → answer item = none) :
    ∀ items : List α, (items.filter keep).findSome? answer = items.findSome? answer
  | [] => rfl
  | first :: rest => by
      cases kept : keep first with
      | true =>
          rw [List.filter_cons_of_pos (by simpa using kept), List.findSome?_cons, List.findSome?_cons,
            findSome?_filter_of_none keep answer silent rest]
      | false =>
          rw [List.filter_cons_of_neg (by simp [kept]), List.findSome?_cons, silent first kept,
            findSome?_filter_of_none keep answer silent rest]

theorem defines_partAt {program : Program} {heads : List String} {head : String}
    (inHeads : head ∈ heads) : (partAt program heads).defines head = program.defines head := by
  rw [Bool.eq_iff_iff]
  simp only [Program.defines, List.any_eq_true, beq_iff_eq, mem_partAt]
  exact ⟨fun ⟨equation, member, same⟩ => ⟨equation, member.1, same⟩,
    fun ⟨equation, member, same⟩ => ⟨equation, ⟨member, same ▸ inHeads⟩, same⟩⟩

theorem definesAt_partAt {program : Program} {heads : List String} {head : String}
    (inHeads : head ∈ heads) (arity : Nat) :
    (partAt program heads).definesAt head arity = program.definesAt head arity := by
  rw [Bool.eq_iff_iff]
  simp only [Program.definesAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, mem_partAt]
  exact ⟨fun ⟨equation, member, same⟩ => ⟨equation, member.1, same⟩,
    fun ⟨equation, member, same⟩ => ⟨equation, ⟨member, same.1 ▸ inHeads⟩, same⟩⟩

theorem select_partAt {program : Program} {heads : List String} {head : String}
    (inHeads : head ∈ heads) (arguments : List EngineTerm) :
    (partAt program heads).select head arguments = program.select head arguments := by
  unfold Program.select partAt
  refine findSome?_filter_of_none _ _ (fun equation dropped => ?_) program
  have other : equation.head ≠ head := by
    intro same
    rw [same] at dropped
    simp [inHeads] at dropped
  simp [other]

theorem defines_partAt_false {program : Program} {heads : List String} {head : String}
    (undefined : program.defines head = false) : (partAt program heads).defines head = false := by
  simp only [Program.defines, List.any_eq_false, beq_iff_eq] at undefined ⊢
  exact fun equation member => undefined equation (mem_partAt.mp member).1

/-- A head that the part mentions is a head of the list, or a head that the
program does not define. -/
theorem mem_calledHeads_partAt {program : Program} {heads : List String}
    (closed : closedUnderCalls program heads = true) {head : String}
    (used : head ∈ (partAt program heads).calledHeads) :
    head ∈ heads ∨ program.defines head = false := by
  obtain ⟨equation, member, found⟩ := List.mem_flatMap.mp used
  obtain ⟨inProgram, inHeads⟩ := mem_partAt.mp member
  rcases List.mem_cons.mp found with rfl | called
  · exact .inl inHeads
  · have checked := List.all_eq_true.mp closed equation inProgram
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem, List.all_eq_true,
      ← Bool.not_eq_true] at checked
    rcases checked with absent | each
    · exact absurd inHeads absent
    · rcases each head called with undefined | inside
      · exact .inr (by simpa using undefined)
      · exact .inl inside

/-- **The part and the program dispatch alike** on every head that the part
mentions, when the list of heads is closed. -/
theorem dispatchAgreement_partAt {program : Program} {heads : List String}
    (closed : closedUnderCalls program heads = true) :
    DispatchAgreement (partAt program heads) program (partAt program heads).calledHeads where
  definesAt := by
    intro head used arity
    rcases mem_calledHeads_partAt closed used with inHeads | undefined
    · exact definesAt_partAt inHeads arity
    · rw [DeterministicEquations.Program.definesAt_false_of_defines_false undefined,
        DeterministicEquations.Program.definesAt_false_of_defines_false
          (defines_partAt_false undefined)]
  defines := by
    intro head used
    rcases mem_calledHeads_partAt closed used with inHeads | undefined
    · exact defines_partAt inHeads
    · rw [undefined, defines_partAt_false undefined]
  select := by
    intro head used arguments
    rcases mem_calledHeads_partAt closed used with inHeads | undefined
    · exact select_partAt inHeads arguments
    · rw [DeterministicEquations.Program.select_none_of_undefined undefined,
        DeterministicEquations.Program.select_none_of_undefined (defines_partAt_false undefined)]

/-- A head of the list that the program defines at an arity is a head that the
part mentions. -/
theorem mem_calledHeads_of_definesAt {program : Program} {heads : List String} {head : String}
    (inHeads : head ∈ heads) {arity : Nat} (defined : program.definesAt head arity = true) :
    head ∈ (partAt program heads).calledHeads := by
  simp only [Program.definesAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at defined
  obtain ⟨equation, member, same, -⟩ := defined
  exact same ▸ DeterministicEquations.Program.calledHeads_head
    (mem_partAt.mpr ⟨member, same ▸ inHeads⟩)

/-- **A call of a head of a closed list has the same outcome in the part as in
the program**, at every fuel. -/
theorem apply_partAt {program : Program} {heads : List String}
    (closed : closedUnderCalls program heads = true) (host : Host) {head : String}
    (inHeads : head ∈ heads) (arguments : List EngineTerm)
    (defined : program.definesAt head arguments.length = true) (fuel : Nat) :
    DeterministicEquations.apply (partAt program heads) host fuel head arguments =
      DeterministicEquations.apply program host fuel head arguments :=
  DeterministicEquations.apply_dispatch_eq host (dispatchAgreement_partAt closed)
    (fun _ member => DeterministicEquations.Program.calledHeads_body member) fuel head
    (mem_calledHeads_of_definesAt inHeads defined) arguments

/-- **The part returns the values that the program returns**, for a call of a
head of a closed list. -/
theorem applies_partAt_iff {program : Program} {heads : List String}
    (closed : closedUnderCalls program heads = true) (host : Host) {head : String}
    (inHeads : head ∈ heads) (arguments : List EngineTerm)
    (defined : program.definesAt head arguments.length = true) (result : EngineTerm) :
    Applies (partAt program heads) host head arguments result ↔
      Applies program host head arguments result := by
  unfold Applies
  simp only [apply_partAt closed host inHeads arguments defined]

/-- **An authored computation, with the part of its program that its head
reaches**: the same host, head, encodings and relation. -/
def restrictComputation {Query Answer : Type} (C : AuthoredComputation Query Answer)
    (heads : List String) (closed : closedUnderCalls C.program heads = true)
    (inHeads : C.head ∈ heads)
    (defined : ∀ query, C.program.definesAt C.head (C.encodeQuery query).length = true) :
    AuthoredComputation Query Answer where
  relation := C.relation
  program := partAt C.program heads
  host := C.host
  head := C.head
  encodeQuery := C.encodeQuery
  encodeAnswer := C.encodeAnswer
  accepts := fun query answer =>
    (applies_partAt_iff closed C.host inHeads _ (defined query) _).trans (C.accepts query answer)
  refuses := fun query =>
    (applies_partAt_iff closed C.host inHeads _ (defined query) _).trans (C.refuses query)

/-- **Positive**: in `detour` the head `keep` reaches itself alone. -/
theorem detour_keep_closed :
    reachableHeads detour 3 ["keep"] = ["keep"] ∧ closedUnderCalls detour ["keep"] = true ∧
      (partAt detour ["keep"]).length = 1 := by
  decide

/-- **Negative**: the head `main` alone is not closed, and it reaches the
three heads. -/
theorem detour_main_not_closed :
    closedUnderCalls detour ["main"] = false ∧
      reachableHeads detour 3 ["main"] = ["main", "keep", "loop"] := by
  decide

#print axioms dispatchAgreement_partAt
#print axioms apply_partAt
#print axioms applies_partAt_iff
#print axioms restrictComputation
#print axioms detour_keep_closed
#print axioms detour_main_not_closed

end Mettapedia.Logic.HostingStyles.StoredPrograms
