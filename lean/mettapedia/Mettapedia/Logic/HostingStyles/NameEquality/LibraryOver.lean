import Mettapedia.Logic.HostingStyles.NameEquality.SequentialOver
import Mettapedia.Logic.HostingStyles.StoredPrograms.LargerHost

/-!
# The table of a program that calls the larger host, for every spelling

The table of a program that calls the equality of data has three parts: the
rule of each equation of the heads whose equations do not overlap, the ordered
rules of the other heads, and a library that computes the primitives of the
host.  This module states the table for an arbitrary spelling of names
(`partTableIn`), with the library without the rules that compare names
(`libraryRulesOver`): the nineteen rules of the shared host and the
forty-eight that compare data, **sixty-seven rules beside the eighty with
names in letters** (`libraryRulesOver_length`).

* A theory that holds the library and compares written names computes the
  eight primitives as the host does (`library_realized_over`).
* A theory that holds the table and compares written names dispatches the
  part of the program (`dispatches_partTable_in`).
* The table is a stored table, hence orthogonal, when the equations of the
  unordered heads are separated, no equation has a primitive as its head, the
  ordered rules are a stored table, and so is the library, with the roots of
  its rules among the primitives and its helpers
  (`storedTable_partTableIn`).  None of its rules then has the root of the
  test of names (`partTableIn_roots`).

With names as constants the library fits (`libraryConstants_fit`).  Negative:
with a spelling that writes all names alike it does not
(`blankSpelling_not_fit`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env LeftLinear dataEqualityHost Applies)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst clashes)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The library -/

/-- **The library without the rules that compare names**: the rules of the
shared host and the rules that compare data, for a spelling. -/
def libraryRulesOver (N : Spelling) : List RewriteRule := sharedRules N ++ structuralRules N

/-- Sixty-seven rules. -/
theorem libraryRulesOver_length (N : Spelling) : (libraryRulesOver N).length = 67 := by
  simp [libraryRulesOver, sharedRules_length, structuralRules_length]

/-- **A theory that holds the library and compares written names computes the
eight primitives of the larger host.** -/
theorem library_realized_over (N : Spelling) {theory : Theory}
    (holds : Holds theory (libraryRulesOver N)) (names : ComparesNames N theory) :
    RealizesPrimitives N theory dataEqualityHost largerPrimitives :=
  RealizesPrimitives.append (first := ["nik:data-eq"])
    (dataEquality_realized_over N holds.right
      (fun rule member => holds.left rule (equalNumbers_in_shared N rule member)) names)
    (shared_realized_larger N holds.left)

/-- The parts of the comparison that a theory holding the library holds. -/
theorem holdsStructural_of_library {N : Spelling} {theory : Theory}
    (holds : Holds theory (libraryRulesOver N)) (names : ComparesNames N theory) :
    HoldsStructural N theory :=
  holdsStructural_of_holds holds.right
    (fun rule member => holds.left rule (equalNumbers_in_shared N rule member)) names

/-! ## The table -/

/-- **The ordered rules of a list of heads**, for a spelling. -/
def orderedPartIn (N : Spelling) (program : Program) (ordered : List String) : List RewriteRule :=
  ordered.flatMap (orderedRulesIn N (isCalled program largerPrimitives) program)

/-- **The table of the part of a program at a list of heads**, with some of
them ordered, for a spelling: the rules of the equations of the other heads,
the ordered rules, and the library without the rules that compare names. -/
def partTableIn (N : Spelling) (program : Program) (heads ordered : List String) :
    List RewriteRule :=
  ((partAt program heads).filter fun equation => !ordered.contains equation.head).map
      (ruleOf N (isCalled program largerPrimitives)) ++
    (orderedPartIn N program ordered ++ libraryRulesOver N)

/-- The number of rules of the table. -/
theorem partTableIn_length (N : Spelling) (program : Program) (heads ordered : List String) :
    (partTableIn N program heads ordered).length =
      ((partAt program heads).filter fun equation => !ordered.contains equation.head).length +
        (orderedPartIn N program ordered).length + 67 := by
  simp only [partTableIn, List.length_append, List.length_map, libraryRulesOver_length]
  omega

/-- A theory that holds the table holds its library. -/
theorem holds_library_of_partTableIn {N : Spelling} {theory : Theory} {program : Program}
    {heads ordered : List String} (holds : Holds theory (partTableIn N program heads ordered)) :
    Holds theory (libraryRulesOver N) :=
  fun rule member => holds rule (List.mem_append_right _ (List.mem_append_right _ member))

/-- **A theory that holds the table and compares written names dispatches the
part of the program.** -/
theorem dispatches_partTable_in (N : Spelling) {theory : Theory} {program : Program}
    {heads ordered : List String} (text : storableText program = true)
    (calls : callsOnly program dataEqualityHandled largerPrimitives = true)
    (closed : closedUnderCalls program heads = true) (orderedIn : ∀ head ∈ ordered, head ∈ heads)
    (holds : Holds theory (partTableIn N program heads ordered))
    (names : ComparesNames N theory) :
    Dispatches N theory (partAt program heads) largerPrimitives := by
  have storable := (storable_larger text calls).partAt closed
  refine dispatches_of_tables_in N (isCalled program largerPrimitives) ?_ storable.leftLinear
    ordered program (fun head inOrdered values => select_partAt (orderedIn head inOrdered) values)
    ?_ ?_ (holdsStructural_of_library (holds_library_of_partTableIn holds) names)
  · intro equation member
    exact body_congr N (isCalled_partAt closed largerPrimitives) _ _
      (DeterministicEquations.Program.calledHeads_body member)
  · intro equation member unordered
    exact holds _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_filter.mpr
      ⟨member, by simpa using unordered⟩)))
  · intro head inOrdered rule member
    exact holds rule (List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨head, inOrdered, member⟩)))

/-! ## The table is a stored table -/

/-- The rules of the trials of an ordered head rewrite the two helpers of a
trial. -/
theorem rootOf_chainRulesIn (N : Spelling) (called : String → Bool) (head : String) :
    ∀ (equations : List Equation) (position : Nat),
      ∀ rule ∈ chainRulesIn N called head position equations,
        rootOf rule = ("lib", "select") ∨ rootOf rule = ("lib", "fire")
  | [], _ => by simp [chainRulesIn]
  | [equation], position => by
      intro rule member
      simp only [chainRulesIn, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
  | equation :: next :: rest, position => by
      intro rule member
      simp only [chainRulesIn, List.mem_cons] at member
      rcases member with rfl | rfl | rfl | later
      · exact .inl rfl
      · exact .inr rfl
      · exact .inl rfl
      · exact rootOf_chainRulesIn N called head (next :: rest) (position + 1) rule later

/-- The roots of the ordered rules of a head: the call of the head, which then
has an equation in the program, or a trial, or a firing. -/
theorem rootOf_orderedRulesIn (N : Spelling) (called : String → Bool) (program : Program)
    (head : String) :
    ∀ rule ∈ orderedRulesIn N called program head,
      (rootOf rule = ("call", head) ∧ ∃ equation ∈ program, equation.head = head) ∨
        rootOf rule = ("lib", "select") ∨ rootOf rule = ("lib", "fire") := by
  intro rule member
  unfold orderedRulesIn at member
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
      · exact .inr (rootOf_chainRulesIn N called head _ 0 rule inChain)

/-- **What is asked of a library**: it is a stored table, the calls that its
rules rewrite are calls of the primitives, and none of its helpers is a trial,
a firing, or the test of names. -/
structure LibraryFit (N : Spelling) : Prop where
  /-- The library is a stored table. -/
  stored : StoredTable (libraryRulesOver N)
  /-- The roots of its rules. -/
  roots : ∀ rule ∈ libraryRulesOver N,
    ((rootOf rule).1 = "call" → (rootOf rule).2 ∈ largerPrimitives) ∧
      rootOf rule ≠ ("lib", "select") ∧ rootOf rule ≠ ("lib", "fire") ∧
        rootOf rule ≠ ("lib", "same-name")

set_option maxRecDepth 100000 in
/-- **Positive**: with names as constants the library is a stored table with
the roots asked. -/
theorem libraryConstants_fit : LibraryFit constantSpelling where
  stored := storedTable_of_check (by decide +kernel)
  roots := by decide +kernel

/-- **The roots of the rules of the table**: the call of a head of the
program, a trial, a firing, or a root of the library. -/
theorem partTableIn_roots {N : Spelling} {program : Program} {heads ordered : List String}
    (fit : LibraryFit N) :
    ∀ rule ∈ partTableIn N program heads ordered, rootOf rule ≠ ("lib", "same-name") := by
  intro rule member
  rcases List.mem_append.mp member with direct | fixed
  · obtain ⟨equation, -, rfl⟩ := List.mem_map.mp direct
    exact fun same => absurd (Prod.mk.inj same).1 (by decide)
  · rcases List.mem_append.mp fixed with inOrdered | inLibrary
    · obtain ⟨head, -, inRules⟩ := List.mem_flatMap.mp inOrdered
      rcases rootOf_orderedRulesIn N _ program head rule inRules with
        ⟨isCall, -⟩ | isSelect | isFire
      · rw [isCall]
        exact fun same => absurd (Prod.mk.inj same).1 (by decide)
      · rw [isSelect]
        decide
      · rw [isFire]
        decide
    · exact (fit.roots rule inLibrary).2.2.2

/-- **The table is a stored table**, for a spelling that writes names apart,
when the equations of the unordered heads are separated, no equation has a
primitive as its head, the ordered rules are a stored table, and the library
fits. -/
theorem storedTable_partTableIn {N : Spelling} (apartN : N.Apart) {program : Program}
    {heads ordered : List String} (text : storableText program = true)
    (separated : Separated (program.filter fun equation => !ordered.contains equation.head))
    (noPrimitive : ∀ equation ∈ program, equation.head ∉ largerPrimitives)
    (orderedStored : StoredTable (orderedPartIn N program ordered)) (fit : LibraryFit N) :
    StoredTable (partTableIn N program heads ordered) := by
  obtain ⟨leftLinear, -, bound⟩ := (storableText_iff program).mp text
  have direct : StoredTable (((partAt program heads).filter fun equation =>
      !ordered.contains equation.head).map (ruleOf N (isCalled program largerPrimitives))) :=
    storedTable_rules N apartN _
      (fun equation member =>
        leftLinear equation (mem_partAt.mp (List.mem_filter.mp member).1).1)
      (fun equation member => bound equation (mem_partAt.mp (List.mem_filter.mp member).1).1)
      (List.Pairwise.sublist (List.Sublist.filter _ List.filter_sublist) separated)
  have fixed : StoredTable (orderedPartIn N program ordered ++ libraryRulesOver N) := by
    refine orderedStored.append fit.stored (cross_of_roots orderedStored fit.stored ?_)
    intro rule member other otherMember same
    obtain ⟨head, inOrdered, inRules⟩ := List.mem_flatMap.mp member
    obtain ⟨callsPrimitive, notSelect, notFire, -⟩ := fit.roots other otherMember
    rcases rootOf_orderedRulesIn N _ program head rule inRules with
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
  have root : rootOf (ruleOf N (isCalled program largerPrimitives) equation) =
      ("call", equation.head) := rfl
  rw [root] at same
  rcases List.mem_append.mp otherMember with inOrderedPart | inLibrary
  · obtain ⟨head, inOrdered, inRules⟩ := List.mem_flatMap.mp inOrderedPart
    rcases rootOf_orderedRulesIn N _ program head other inRules with ⟨isCall, -⟩ | isSelect | isFire
    · rw [isCall] at same
      exact unorderedHead ((Prod.mk.inj same).2 ▸ inOrdered)
    · rw [isSelect] at same
      exact absurd (Prod.mk.inj same).1 (by decide)
    · rw [isFire] at same
      exact absurd (Prod.mk.inj same).1 (by decide)
  · have primitive := (fit.roots other inLibrary).1 (by rw [← same])
    rw [← same] at primitive
    exact noPrimitive equation inProgram primitive

/-- A spelling that writes every name as one constant. -/
def blankSpelling : Spelling where
  write := fun _ => .con "name"
  quiet := fun _ => rfl

/-- **Negative**: with a spelling that writes all names alike the library does
not fit: the two truth values are one term, so the two rules of the
conjunction have one left side. -/
theorem blankSpelling_not_fit : ¬ LibraryFit blankSpelling := by
  intro fit
  have yesIn : Over.whenYes blankSpelling ∈ libraryRulesOver blankSpelling := by
    simp [libraryRulesOver, structuralRules, bothRulesOver]
  have noIn : Over.whenNo blankSpelling ∈ libraryRulesOver blankSpelling := by
    simp [libraryRulesOver, structuralRules, bothRulesOver]
  exact pairwise_distinct fit.stored.apart _ yesIn _ noIn (by decide) (fun index => .var index)
    (fun index => .var index) rfl

#print axioms library_realized_over
#print axioms dispatches_partTable_in
#print axioms rootOf_orderedRulesIn
#print axioms libraryConstants_fit
#print axioms partTableIn_roots
#print axioms storedTable_partTableIn
#print axioms blankSpelling_not_fit

end Mettapedia.Logic.HostingStyles.NameEquality
