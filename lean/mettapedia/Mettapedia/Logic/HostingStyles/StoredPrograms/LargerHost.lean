import Mettapedia.Logic.HostingStyles.StoredPrograms.Sequential
import Mettapedia.Logic.HostingStyles.StoredPrograms.Candidate

/-!
# The table of a program that calls the larger host

The programs of MM0's conversion and of the check of a certificate call the
equality of data, and some of their heads have overlapping equations.  Their
table, with names written in letters, has three parts (`partTable`):

* the rule of each equation of the part of the program that the operation
  reaches, for the heads whose equations do not overlap;
* the ordered rules of the other heads (`Sequential.lean`);
* the **library**, the same eighty rules for every program
  (`libraryRules`): the nineteen rules of the shared host and the sixty-one
  rules that compare data.

**The table stores the part of the program** (`stores_partTable`), and it is
a stored table, hence orthogonal (`storedTable_partTable`), when

* the text of the program is of the class and it calls only what the table
  computes (`storableText`, `callsOnly`);
* the heads of the part are closed under calls (`closedUnderCalls`);
* the equations of the unordered heads are separated (`Separated`);
* no equation has a primitive as its head;
* the ordered rules pass the test for stored tables.

All five are computed on the program, and none on the rules of the unordered
heads: those are a stored table because their equations are separated
(`storedTable_rules`).  The library is a stored table once and for all
(`libraryRules_stored`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env LeftLinear dataEqualityHost Applies)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst clashes)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-- **The primitives that the library computes**: the equality of data and
the seven primitives of the shared host. -/
def largerPrimitives : List String := "nik:data-eq" :: sharedPrimitives

/-- **The library**: the rules of the shared host and the rules that compare
data, with names in letters.  Eighty rules, the same for every program. -/
def libraryRules : List RewriteRule := sharedRules letterSpelling ++ comparisonRules

theorem libraryRules_length : libraryRules.length = 80 := by
  simp [libraryRules, sharedRules_length, comparisonRules_length]

set_option maxRecDepth 100000 in
/-- **The library is a stored table.** -/
theorem libraryRules_stored : StoredTable libraryRules :=
  storedTable_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The calls that the library rewrites are calls of the primitives, and none
of its helpers is a trial or a firing. -/
theorem libraryRules_roots : ∀ rule ∈ libraryRules,
    ((rootOf rule).1 = "call" → (rootOf rule).2 ∈ largerPrimitives) ∧
      rootOf rule ≠ ("lib", "select") ∧ rootOf rule ≠ ("lib", "fire") := by
  decide +kernel

/-- The rules that compare numbers are rules of the shared host. -/
theorem equalNumbers_in_shared (N : Spelling) : ∀ rule ∈ equalNumbersRules N, rule ∈ sharedRules N := by
  intro rule member
  simp [sharedRules, naturalRules, member]

/-- The library realizes the eight primitives of the larger host. -/
theorem library_realized {theory : Theory} (holds : Holds theory libraryRules) :
    RealizesPrimitives letterSpelling theory dataEqualityHost largerPrimitives :=
  RealizesPrimitives.append (first := ["nik:data-eq"])
    (dataEquality_realized holds.right fun rule member =>
      holds.left rule (equalNumbers_in_shared letterSpelling rule member))
    (shared_realized_larger letterSpelling holds.left)

theorem larger_handled : ∀ head ∈ largerPrimitives, ∀ arguments : List EngineTerm,
    dataEqualityHost.primitive head arguments ≠ .unhandled := by
  intro head member arguments
  rcases List.mem_cons.mp member with rfl | shared
  · exact dataEquality_handled arguments
  · exact shared_handled_larger head shared arguments

/-- **The class, read off the program**, for the larger host and its eight
primitives. -/
theorem storable_larger {program : Program} (text : storableText program = true)
    (calls : callsOnly program dataEqualityHandled largerPrimitives = true) :
    Storable program dataEqualityHost largerPrimitives where
  leftLinear := ((storableText_iff program).mp text).1
  ordinary := ((storableText_iff program).mp text).2.1
  bound := ((storableText_iff program).mp text).2.2
  handled := larger_handled
  constructs := by
    intro head called undefined absent arguments
    have checked := List.all_eq_true.mp calls head called
    simp only [undefined, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', ← Bool.not_eq_true] at checked
    rcases checked with isPrimitive | unhandled
    · exact absurd isPrimitive absent
    · exact dataEqualityHost_unhandled_of_not_mem unhandled arguments

/-- The heads that a part mentions are heads that the program mentions. -/
theorem calledHeads_partAt_subset {program : Program} {heads : List String} {head : String}
    (used : head ∈ (partAt program heads).calledHeads) : head ∈ program.calledHeads := by
  obtain ⟨equation, member, found⟩ := List.mem_flatMap.mp used
  exact List.mem_flatMap.mpr ⟨equation, (mem_partAt.mp member).1, found⟩

/-- **The part of a program of the class at closed heads is of the class.** -/
theorem Storable.partAt {program : Program} {host : Host} {primitives : List String}
    (storable : Storable program host primitives) {heads : List String}
    (closed : closedUnderCalls program heads = true) :
    Storable (partAt program heads) host primitives where
  leftLinear := fun equation member => storable.leftLinear equation (mem_partAt.mp member).1
  ordinary := fun equation member => storable.ordinary equation (mem_partAt.mp member).1
  bound := fun equation member => storable.bound equation (mem_partAt.mp member).1
  handled := storable.handled
  constructs := by
    intro head used undefined absent arguments
    have inProgram := calledHeads_partAt_subset used
    rcases mem_calledHeads_partAt closed used with inHeads | notDefined
    · rw [defines_partAt inHeads] at undefined
      exact storable.constructs head inProgram undefined absent arguments
    · exact storable.constructs head inProgram notDefined absent arguments

/-- What is called in the part is what is called in the program, on the heads
that the part mentions. -/
theorem isCalled_partAt {program : Program} {heads : List String}
    (closed : closedUnderCalls program heads = true) (primitives : List String) :
    ∀ head ∈ (partAt program heads).calledHeads,
      isCalled (partAt program heads) primitives head = isCalled program primitives head := by
  intro head used
  rcases mem_calledHeads_partAt closed used with inHeads | undefined
  · simp [isCalled, defines_partAt inHeads]
  · simp [isCalled, undefined, defines_partAt_false undefined]

/-- **The ordered rules of a list of heads.** -/
def orderedPart (program : Program) (ordered : List String) : List RewriteRule :=
  ordered.flatMap (orderedRules (isCalled program largerPrimitives) program)

/-- **The table of the part of a program at a list of heads**, with some of
them ordered: the rules of the equations of the other heads, the ordered
rules, and the library. -/
def partTable (program : Program) (heads ordered : List String) : List RewriteRule :=
  ((partAt program heads).filter fun equation => !ordered.contains equation.head).map
      (ruleOf letterSpelling (isCalled program largerPrimitives)) ++
    (orderedPart program ordered ++ libraryRules)

/-- **The table stores the part of the program.** -/
theorem stores_partTable {program : Program} {heads ordered : List String}
    (text : storableText program = true)
    (calls : callsOnly program dataEqualityHandled largerPrimitives = true)
    (closed : closedUnderCalls program heads = true) (orderedIn : ∀ head ∈ ordered, head ∈ heads)
    (stored : StoredTable (partTable program heads ordered)) :
    Stores letterSpelling (partTable program heads ordered) (partAt program heads) dataEqualityHost
      largerPrimitives := by
  have storable := (storable_larger text calls).partAt closed
  have library : Holds (programTheory (partTable program heads ordered)) libraryRules :=
    fun rule member => List.mem_append_right _ (List.mem_append_right _ member)
  refine
    { storable := storable
      dispatches := dispatches_of_tables (isCalled program largerPrimitives) ?_ storable.leftLinear
        ordered program (fun head inOrdered values => select_partAt (orderedIn head inOrdered) values)
        ?_ ?_ (holdsComparison_of_holds library.right fun rule member =>
          library.left rule (equalNumbers_in_shared letterSpelling rule member))
      realizes := library_realized library
      runnable := stored.runnable
      rooted := stored.rewriteCalls }
  · intro equation member
    exact body_congr letterSpelling (isCalled_partAt closed largerPrimitives) _ _
      (DeterministicEquations.Program.calledHeads_body member)
  · intro equation member unordered
    exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_filter.mpr
      ⟨member, by simpa using unordered⟩))
  · intro head inOrdered rule member
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨head, inOrdered, member⟩))

/-! ## The table is a stored table -/

theorem rootOf_chainRules (called : String → Bool) (head : String) :
    ∀ (equations : List Equation) (position : Nat), ∀ rule ∈ chainRules called head position equations,
      rootOf rule = ("lib", "select") ∨ rootOf rule = ("lib", "fire")
  | [], _ => by simp [chainRules]
  | [equation], position => by
      intro rule member
      simp only [chainRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
  | equation :: next :: rest, position => by
      intro rule member
      simp only [chainRules, List.mem_cons] at member
      rcases member with rfl | rfl | rfl | later
      · exact .inl rfl
      · exact .inr rfl
      · exact .inl rfl
      · exact rootOf_chainRules called head (next :: rest) (position + 1) rule later

/-- The roots of the ordered rules of a head: the call of the head, which
then has an equation in the program, or a trial, or a firing. -/
theorem rootOf_orderedRules (called : String → Bool) (program : Program) (head : String) :
    ∀ rule ∈ orderedRules called program head,
      (rootOf rule = ("call", head) ∧ ∃ equation ∈ program, equation.head = head) ∨
        rootOf rule = ("lib", "select") ∨ rootOf rule = ("lib", "fire") := by
  intro rule member
  unfold orderedRules at member
  cases listed : equationsOf program head with
  | nil =>
      rw [listed] at member
      cases member
  | cons first rest =>
      rw [listed] at member
      rcases List.mem_cons.mp member with rfl | inChain
      · have inFilter : first ∈ equationsOf program head := listed ▸ List.mem_cons_self ..
        obtain ⟨inProgram, isHead⟩ := List.mem_filter.mp inFilter
        exact .inl ⟨rfl, first, inProgram, by simpa using isHead⟩
      · exact .inr (rootOf_chainRules called head _ 0 rule inChain)

/-- **The table is a stored table**, when the equations of the unordered
heads are separated, no equation has a primitive as its head, and the ordered
rules are a stored table. -/
theorem storedTable_partTable {program : Program} {heads ordered : List String}
    (text : storableText program = true)
    (separated : Separated (program.filter fun equation => !ordered.contains equation.head))
    (noPrimitive : ∀ equation ∈ program, equation.head ∉ largerPrimitives)
    (orderedStored : StoredTable (orderedPart program ordered)) :
    StoredTable (partTable program heads ordered) := by
  obtain ⟨leftLinear, -, bound⟩ := (storableText_iff program).mp text
  have direct : StoredTable (((partAt program heads).filter fun equation =>
      !ordered.contains equation.head).map
        (ruleOf letterSpelling (isCalled program largerPrimitives))) :=
    storedTable_rules letterSpelling letterSpelling_apart _
      (fun equation member =>
        leftLinear equation (mem_partAt.mp (List.mem_filter.mp member).1).1)
      (fun equation member => bound equation (mem_partAt.mp (List.mem_filter.mp member).1).1)
      (List.Pairwise.sublist (List.Sublist.filter _ List.filter_sublist) separated)
  have fixed : StoredTable (orderedPart program ordered ++ libraryRules) := by
    refine orderedStored.append libraryRules_stored
      (cross_of_roots orderedStored libraryRules_stored ?_)
    intro rule member other otherMember same
    obtain ⟨head, inOrdered, inRules⟩ := List.mem_flatMap.mp member
    obtain ⟨callsPrimitive, notSelect, notFire⟩ := libraryRules_roots other otherMember
    rcases rootOf_orderedRules _ program head rule inRules with
      ⟨isCall, equation, inProgram, isHead⟩ | isSelect | isFire
    · have primitive := callsPrimitive (by rw [← same, isCall])
      rw [← same, isCall] at primitive
      exact noPrimitive equation inProgram (isHead ▸ primitive)
    · exact notSelect (same ▸ isSelect)
    · exact notFire (same ▸ isFire)
  refine direct.append fixed (cross_of_roots direct fixed ?_)
  intro rule member other otherMember same
  obtain ⟨equation, inFilter, rfl⟩ := List.mem_map.mp member
  obtain ⟨inPart, unordered⟩ := List.mem_filter.mp inFilter
  have unorderedHead : equation.head ∉ ordered := by simpa using unordered
  have inProgram := (mem_partAt.mp inPart).1
  have root : rootOf (ruleOf letterSpelling (isCalled program largerPrimitives) equation) =
      ("call", equation.head) := rfl
  rw [root] at same
  rcases List.mem_append.mp otherMember with inOrderedPart | inLibrary
  · obtain ⟨head, inOrdered, inRules⟩ := List.mem_flatMap.mp inOrderedPart
    rcases rootOf_orderedRules _ program head other inRules with ⟨isCall, -⟩ | isSelect | isFire
    · rw [isCall] at same
      exact unorderedHead ((Prod.mk.inj same).2 ▸ inOrdered)
    · rw [isSelect] at same
      exact absurd (Prod.mk.inj same).1 (by decide)
    · rw [isFire] at same
      exact absurd (Prod.mk.inj same).1 (by decide)
  · have primitive := (libraryRules_roots other inLibrary).1 (by rw [← same])
    rw [← same] at primitive
    exact noPrimitive equation inProgram primitive

/-- The number of rules of the table. -/
theorem partTable_length (program : Program) (heads ordered : List String) :
    (partTable program heads ordered).length =
      ((partAt program heads).filter fun equation => !ordered.contains equation.head).length +
        (orderedPart program ordered).length + 80 := by
  simp only [partTable, List.length_append, List.length_map, libraryRules_length]
  omega

#print axioms libraryRules_stored
#print axioms libraryRules_roots
#print axioms library_realized
#print axioms Storable.partAt
#print axioms stores_partTable
#print axioms rootOf_orderedRules
#print axioms storedTable_partTable

end Mettapedia.Logic.HostingStyles.StoredPrograms
