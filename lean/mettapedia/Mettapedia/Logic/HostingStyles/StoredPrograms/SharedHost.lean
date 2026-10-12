import Mettapedia.Logic.HostingStyles.StoredPrograms.Lists

/-!
# The shared host as rules, and the table of a program that calls it

`sharedRules` joins the list rules and the arithmetic rules: nineteen rules
for seven primitives of the shared host (`sharedPrimitives`), which agree
with the host on all data (`shared_realized`).

The table of a program that calls these primitives is the table of its
equations followed by these rules (`sharedTable`).  It **stores** the program
(`stores_shared`) when

* the program text is of the class (`storableText`), and
* every head that a right side calls is defined by the program, or is one of
  the seven primitives, or is no primitive of the host at all (`callsOnly`).
  The host has three further primitives, the truncated difference, the
  maximum and the order `≤` (`computationalHandled`); a program that calls
  one of them is not stored by this table.

Both conditions are computed on the program.  Then the three statements of
`Candidate.lean` hold of every call that the engine answers.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host natural natural? boolean computationalHost dataEqualityHost listView
    PrimitiveResult naturalBinary? naturalProduct?)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces inst orthogonalCheck binderFree usesOnly)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-- **The shared host as rules**: lists as cells with their view and former,
and the arithmetic that the kernel uses. -/
def sharedRules (N : Spelling) : List RewriteRule := listRules N ++ naturalRules N

/-- The seven primitives that the rules compute. -/
def sharedPrimitives : List String := listPrimitives ++ naturalPrimitives

theorem sharedRules_length (N : Spelling) : (sharedRules N).length = 19 := by
  simp [sharedRules, listRules, listViewRules, listConsRules, naturalRules_length]

/-- **The rules agree with the shared host on its seven primitives.** -/
theorem shared_realized (N : Spelling) {theory : Theory} (holds : Holds theory (sharedRules N)) :
    RealizesPrimitives N theory computationalHost sharedPrimitives :=
  (lists_realized N holds.left).append (naturals_realized N holds.right)

theorem shared_handled : ∀ head ∈ sharedPrimitives, ∀ arguments : List EngineTerm,
    computationalHost.primitive head arguments ≠ .unhandled := by
  intro head member arguments
  rcases List.mem_append.mp member with isList | isNatural
  · exact lists_handled head isList arguments
  · exact naturals_handled head isNatural arguments

/-- **The heads that the shared host handles.** -/
def computationalHandled : List String :=
  ["nik:list-view", "nik:list-cons", "nik:nat-add", "nik:nat-monus", "nik:nat-max", "nik:nat-le",
    "nik:nat-lt", "nik:nat-eq", "nik:nat-zero", "nik:nat-pred"]

/-- **The shared host handles no other head.** -/
theorem computationalHost_unhandled_of_not_mem {head : String}
    (absent : head ∉ computationalHandled) (arguments : List EngineTerm) :
    computationalHost.primitive head arguments = .unhandled := by
  simp only [computationalHandled, List.mem_cons, List.not_mem_nil, or_false, not_or] at absent
  obtain ⟨notView, notCons, notAdd, notMonus, notMax, notLe, notLt, notEq, notZero, notPred⟩ :=
    absent
  refine DeterministicEquations.computationalHost_unhandled head arguments notView notCons ?_
    notZero notPred
  unfold naturalBinary?
  split <;> first | rfl | contradiction

/-- **The heads that the larger host handles**: those of the shared host, the
product, quotient and remainder, and the equality of data. -/
def dataEqualityHandled : List String :=
  "nik:data-eq" :: "nik:nat-mul" :: "nik:nat-div" :: "nik:nat-mod" :: computationalHandled

/-- **The larger host handles no other head.** -/
theorem dataEqualityHost_unhandled_of_not_mem {head : String}
    (absent : head ∉ dataEqualityHandled) (arguments : List EngineTerm) :
    dataEqualityHost.primitive head arguments = .unhandled := by
  simp only [dataEqualityHandled, List.mem_cons, not_or] at absent
  obtain ⟨notEqual, notMul, notDiv, notMod, rest⟩ := absent
  rw [DeterministicEquations.dataEqualityHost_prior head arguments notEqual,
    DeterministicEquations.productDivisionHost_prior head arguments ?_]
  · exact computationalHost_unhandled_of_not_mem rest arguments
  · unfold naturalProduct?
    split <;> first | rfl | contradiction

/-- The larger host returns what the shared host returns on the seven
primitives. -/
theorem dataEqualityHost_agrees_shared : ∀ head ∈ sharedPrimitives, ∀ arguments : List EngineTerm,
    dataEqualityHost.primitive head arguments = computationalHost.primitive head arguments := by
  intro head member arguments
  simp only [sharedPrimitives, listPrimitives, naturalPrimitives, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The rules agree with the larger host on the seven primitives.** -/
theorem shared_realized_larger (N : Spelling) {theory : Theory}
    (holds : Holds theory (sharedRules N)) :
    RealizesPrimitives N theory dataEqualityHost sharedPrimitives :=
  (shared_realized N holds).of_agrees dataEqualityHost_agrees_shared

/-- **Whether a program calls only what a table computes**: every head that a
right side calls is defined by the program, or is one of the given
primitives, or is none of the heads that the host handles. -/
def callsOnly (program : Program) (handled primitives : List String) : Bool :=
  program.calledHeads.all fun head =>
    program.defines head || primitives.contains head || !handled.contains head

/-- **The class, read off the program**, for the shared host and its seven
primitives. -/
theorem storable_shared {program : Program} (text : storableText program = true)
    (calls : callsOnly program computationalHandled sharedPrimitives = true) :
    Storable program computationalHost sharedPrimitives where
  leftLinear := ((storableText_iff program).mp text).1
  ordinary := ((storableText_iff program).mp text).2.1
  bound := ((storableText_iff program).mp text).2.2
  handled := shared_handled
  constructs := by
    intro head called undefined absent arguments
    have checked := List.all_eq_true.mp calls head called
    simp only [undefined, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', ← Bool.not_eq_true] at checked
    rcases checked with isPrimitive | unhandled
    · exact absurd isPrimitive absent
    · exact computationalHost_unhandled_of_not_mem unhandled arguments

/-- **The table of a program that calls the shared host**: the rules of its
equations, then the rules of the host. -/
def sharedTable (N : Spelling) (program : Program) : List RewriteRule :=
  programRules N program sharedPrimitives ++ sharedRules N

/-- Two tables of first-order rules with bound right sides, one after the
other. -/
theorem runnable_append {first second : List RewriteRule} (left : RunnableEquations first)
    (right : RunnableEquations second) : RunnableEquations (first ++ second) := by
  constructor
  · intro rule member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact left.1 rule inFirst
    · exact right.1 rule inSecond
  · intro rule member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact left.2 rule inFirst
    · exact right.2 rule inSecond

/-- **The table of a program that calls the shared host stores it**, when
the program text is of the class and the program calls only what the table
computes. -/
theorem stores_shared (N : Spelling) {program : Program} (text : storableText program = true)
    (calls : callsOnly program computationalHandled sharedPrimitives = true)
    (runnable : RunnableEquations (sharedRules N))
    (rooted : ∀ rule ∈ sharedRules N, rewritesCall rule = true) :
    Stores N (sharedTable N program) program computationalHost sharedPrimitives where
  storable := storable_shared text calls
  dispatches := dispatches_of_rules N (storable_shared text calls).leftLinear
    fun _ member => List.mem_append_left _ (ruleOf_mem member)
  realizes := shared_realized N fun _ member => List.mem_append_right _ member
  runnable := runnable_append (programRules_runnable N _ (storable_shared text calls).bound) runnable
  rooted := by
    intro rule member
    rcases List.mem_append.mp member with inProgram | inShared
    · exact programRules_rewriteCalls N program sharedPrimitives rule inProgram
    · exact rooted rule inShared

/-- The larger host handles each of the seven primitives. -/
theorem shared_handled_larger : ∀ head ∈ sharedPrimitives, ∀ arguments : List EngineTerm,
    dataEqualityHost.primitive head arguments ≠ .unhandled := by
  intro head member arguments
  rw [dataEqualityHost_agrees_shared head member arguments]
  exact shared_handled head member arguments

/-- **The class, read off the program**, for the larger host and the seven
primitives of the shared host. -/
theorem storable_sharedLarger {program : Program} (text : storableText program = true)
    (calls : callsOnly program dataEqualityHandled sharedPrimitives = true) :
    Storable program dataEqualityHost sharedPrimitives where
  leftLinear := ((storableText_iff program).mp text).1
  ordinary := ((storableText_iff program).mp text).2.1
  bound := ((storableText_iff program).mp text).2.2
  handled := shared_handled_larger
  constructs := by
    intro head called undefined absent arguments
    have checked := List.all_eq_true.mp calls head called
    simp only [undefined, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', ← Bool.not_eq_true] at checked
    rcases checked with isPrimitive | unhandled
    · exact absurd isPrimitive absent
    · exact dataEqualityHost_unhandled_of_not_mem unhandled arguments

/-- **The table of a program that calls the seven primitives stores it under
the larger host too**, when the program calls none of the further primitives
of that host. -/
theorem stores_sharedLarger (N : Spelling) {program : Program}
    (text : storableText program = true)
    (calls : callsOnly program dataEqualityHandled sharedPrimitives = true)
    (runnable : RunnableEquations (sharedRules N))
    (rooted : ∀ rule ∈ sharedRules N, rewritesCall rule = true) :
    Stores N (sharedTable N program) program dataEqualityHost sharedPrimitives where
  storable := storable_sharedLarger text calls
  dispatches := dispatches_of_rules N (storable_sharedLarger text calls).leftLinear
    fun _ member => List.mem_append_left _ (ruleOf_mem member)
  realizes := shared_realized_larger N fun _ member => List.mem_append_right _ member
  runnable :=
    runnable_append (programRules_runnable N _ (storable_sharedLarger text calls).bound) runnable
  rooted := by
    intro rule member
    rcases List.mem_append.mp member with inProgram | inShared
    · exact programRules_rewriteCalls N program sharedPrimitives rule inProgram
    · exact rooted rule inShared

/-! ## With names written as constants -/

/-- **The nineteen rules are orthogonal.** -/
theorem sharedRules_orthogonal : orthogonalCheck (sharedRules constantSpelling) = true := by
  decide

/-- They are first-order rules with bound right sides. -/
theorem sharedRules_runnable : RunnableEquations (sharedRules constantSpelling) := by
  constructor <;> decide

/-- Each rewrites a call. -/
theorem sharedRules_rewriteCalls :
    ∀ rule ∈ sharedRules constantSpelling, rewritesCall rule = true := by
  decide

/-- **Negative**: a program that calls the order `≤` is not stored by this
table: the host handles that head and the rules do not compute it. -/
theorem order_not_storable :
    ¬ Storable [⟨"at-most", "at-most", [.var "x", .var "y"],
        .expr [.sym "nik:nat-le", .var "x", .var "y"]⟩] computationalHost sharedPrimitives := by
  intro storable
  have unhandled := storable.constructs "nik:nat-le" (by decide) (by decide) (by decide)
    [natural 0, natural 0]
  have handled : computationalHost.primitive "nik:nat-le" [natural 0, natural 0] =
      .value (boolean (decide (0 ≤ 0))) :=
    DeterministicEquations.computationalHost_binary (operation := .le) rfl 0 0 (by decide)
      (by decide)
  rw [handled] at unhandled
  cases unhandled

#print axioms shared_realized
#print axioms dataEqualityHost_unhandled_of_not_mem
#print axioms shared_realized_larger
#print axioms computationalHost_unhandled_of_not_mem
#print axioms storable_shared
#print axioms stores_shared
#print axioms stores_sharedLarger
#print axioms sharedRules_orthogonal
#print axioms sharedRules_runnable
#print axioms order_not_storable

end Mettapedia.Logic.HostingStyles.StoredPrograms
