import Mettapedia.OSLF.NativeTypes.Executable.Explored
import Mettapedia.OSLF.MeTTaIL.Complete.Graph
import Mettapedia.OSLF.MeTTaIL.Complete.Termination

/-!
# Exact verdicts on the explorer of a compiled language

The explorer of a compiled plan searches each state's steps modulo the plan's equations and commits
each target by a chosen function (`search`). When a settled exploration is read with an
abstraction (`Abstraction`: the committing function, an equivalence and an invariant of good
states), it is exact for the plan's steps (`exact_of_settled`), and the finite checker decides
future formulas about the plan's steps at good start states (`verdict_proved`, `verdict_refuted`).

Two uses:
- no abstraction (`Abstraction.plain`): the identity commitment and the plan's own equations,
  which always match futures (`gslt_futureMatching`). A language whose reachable classes are finite
  gets its verdicts.
- an abstraction: a committing function that returns a normal form of a coarser equivalence. The
  reachable states may then be infinite. Future matching of the coarser equivalence on the good
  states is the obligation that the abstraction loses no answer; the good states are typically the
  well-sorted ones, which every firing produces (`Receipt.target_sorted`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Complete
open Mettapedia.OSLF.MeTTaIL.Complete.Explore (Node Explorer explore)
open Mettapedia.OSLF.MeTTaIL.Complete.Settled (Stable settled)
open Mettapedia.Machines.ResumableSearchRunner (Search History)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Outcome)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- The steps of the plan modulo its equations. -/
abbrev theory : Mettapedia.GSLT.GSLT := GeneralOccurrenceSemantics.gslt plan bound expected

instance : DecidableEq (theory plan bound expected).Term := inferInstanceAs (DecidableEq Pattern)

/-- The search modulo equations, committing each target by `normal`. -/
def search (normal : Pattern → Pattern) :
    Search Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt :=
  { Classes.search plan bound expected with target := fun receipt => normal receipt.target }

theorem search_lawful (normal : Pattern → Pattern) : (search plan bound expected normal).Lawful where
  resume_run := (Classes.search_lawful plan bound expected).resume_run
  publication_prefix := (Classes.search_lawful plan bound expected).publication_prefix
  sound := (Classes.search_lawful plan bound expected).sound

theorem search_stable (normal : Pattern → Pattern) : Stable (search plan bound expected normal) :=
  fun run work complete => Settled.classes_stable plan bound expected run work complete

/-- The exploration an explorer has found: its states, and its edges without their receipts. -/
def exploration (normal : Pattern → Pattern)
    (explorer : Explorer Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt) :
    Exploration Pattern :=
  ⟨explorer.nodes.map Node.state,
    (Graph.edges (search plan bound expected normal) explorer).map fun edge => (edge.1, edge.2.2)⟩

/-- **What an abstraction must satisfy.** The committing function returns an equivalent term and
keeps good terms good; every firing's target is good; the equivalence contains the plan's equations;
steps keep good terms good; and equivalent good terms have equivalent successors. -/
structure Abstraction (normal : Pattern → Pattern) (same : Setoid Pattern) (good : Pattern → Prop) :
    Prop where
  committed : ∀ pattern, same.r (normal pattern) pattern
  normalGood : ∀ pattern, good pattern → good (normal pattern)
  targetGood : ∀ (source : Pattern) (receipt : GeneralOccurrenceSemantics.Receipt),
    receipt.Valid plan bound expected source → good receipt.target
  within : ∀ {left right : Pattern}, (theory plan bound expected).equations.r left right → same.r left right
  closed : ForwardClosed (gsltSpan (theory plan bound expected)) good
  matching : FutureMatchingOn (gsltSpan (theory plan bound expected)) same good

/-- **No abstraction**: the identity commitment, the plan's own equations, every term good. -/
theorem Abstraction.plain :
    Abstraction plan bound expected id (theory plan bound expected).equations (fun _ => True) where
  committed pattern := (theory plan bound expected).equations.refl pattern
  normalGood _ _ := trivial
  targetGood _ _ _ := trivial
  within related := related
  closed _ _ := trivial
  matching := futureMatchingOn_of_futureMatching (gslt_futureMatching _)

variable {plan bound expected}

/-- A node's state is the start, or the committed target of a valid receipt. -/
theorem state_origin {normal : Pattern → Pattern} {start : Pattern} {states : List Pattern}
    {receipts : List GeneralOccurrenceSemantics.Receipt} {state : Pattern}
    (history : History (search plan bound expected normal) states receipts)
    (first : states.head? = some state) (last : states.getLast? = some start) :
    state = start ∨ ∃ (source : Pattern) (receipt : GeneralOccurrenceSemantics.Receipt),
      receipt.Valid plan bound expected source ∧ state = normal receipt.target := by
  cases history with
  | start origin =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at first last
    exact Or.inl (first.symm.trans last)
  | commit _ valid =>
    simp only [List.head?_cons, Option.some.injEq] at first
    exact Or.inr ⟨_, _, valid, first.symm⟩

/-- **A settled exploration is exact** for the plan's steps, read with an abstraction, from a good
start. -/
theorem exact_of_settled (checked : Predecessors.equationsChecked plan = true)
    {normal : Pattern → Pattern} {same : Setoid Pattern} {good : Pattern → Prop}
    (abstraction : Abstraction plan bound expected normal same good)
    {start : Pattern} (startGood : good start) (work : Nat)
    (done : settled (search plan bound expected normal)
      (explore (search plan bound expected normal) start work) = true) :
    (exploration plan bound expected normal
      (explore (search plan bound expected normal) start work)).Exact
        (gsltSpan (theory plan bound expected)) same good := by
  have lawful := search_lawful plan bound expected normal
  have nodeGood : ∀ node ∈ (explore (search plan bound expected normal) start work).nodes,
      good node.state := by
    intro node present
    obtain ⟨history, first, last⟩ := Explore.node_chain lawful start work node present
    rcases state_origin history first last with isStart | ⟨source, receipt, valid, isTarget⟩
    · rw [isStart]; exact startGood
    · rw [isTarget]; exact abstraction.normalGood _ (abstraction.targetGood source receipt valid)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro state member
    obtain ⟨node, present, rfl⟩ := List.mem_map.mp member
    exact nodeGood node present
  · intro edge member
    obtain ⟨found, inEdges, rfl⟩ := List.mem_map.mp member
    obtain ⟨node, present, reached⟩ := Graph.edge_target lawful start work done found inEdges
    exact List.mem_map.mpr ⟨node, present, reached⟩
  · intro edge member
    obtain ⟨found, inEdges, rfl⟩ := List.mem_map.mp member
    obtain ⟨valid, target⟩ := Graph.edge_valid lawful start work found inEdges
    obtain ⟨node, present, receipt, published, sameEdge⟩ := (Graph.mem_edges _).mp inEdges
    have sourceIs : found.1 = node.state := by rw [sameEdge]
    have sourceGood : good found.1 := by rw [sourceIs]; exact nodeGood node present
    refine ⟨⟨found.1, found.2.1.target, GeneralOccurrenceSemantics.Receipt.semantic_step plan bound expected valid⟩,
      sourceGood, same.refl _, ?_⟩
    change same.r found.2.1.target found.2.2
    rw [target]
    exact same.symm (abstraction.committed _)
  · intro state member event starts
    obtain ⟨node, present, rfl⟩ := List.mem_map.mp member
    have stepped : (theory plan bound expected).Step node.state event.target := starts ▸ event.step
    obtain ⟨rounds, receipt, published, related⟩ :=
      Classes.complete_in_limit plan bound expected node.state checked stepped
    have edge := Graph.edges_complete lawful (search_stable plan bound expected normal) start work done
      node present rounds receipt published
    refine ⟨normal receipt.target, List.mem_map.mpr ⟨_, edge, rfl⟩, ?_⟩
    exact same.trans (abstraction.within (Relation.EqvGen.symm _ _ related))
      (same.symm (abstraction.committed _))

/-! ## Verdicts -/

/-- Why a question gets no verdict. -/
inductive Unknown where
  /-- The formula traverses the past; an exploration from one root covers outgoing steps only. -/
  | pastModality
  /-- A fixed point is not positive in its variable. -/
  | notPositive
  /-- The exploration has not settled within the given work. -/
  | unsettled
  /-- The start is not among the explored states. -/
  | startNotExplored
  /-- The finite checker's allowance is too small for the formula. -/
  | allowance
  deriving DecidableEq, Repr

inductive Verdict where
  | proved
  | refuted
  | unknown (reason : Unknown)
  deriving DecidableEq, Repr

/-- Read a finite outcome. -/
def readOutcome {statement : Prop} : Option (Outcome statement) → Verdict
  | some (.proved _) => .proved
  | some (.refuted _) => .refuted
  | some .unknown => .unknown .allowance
  | none => .unknown .notPositive

theorem readOutcome_proved {statement : Prop} {result : Option (Outcome statement)}
    (read : readOutcome result = .proved) : statement := by
  rcases result with _ | (proof | refutation | _) <;> simp [readOutcome] at read
  exact proof

theorem readOutcome_refuted {statement : Prop} {result : Option (Outcome statement)}
    (read : readOutcome result = .refuted) : ¬ statement := by
  rcases result with _ | (proof | refutation | _) <;> simp [readOutcome] at read
  exact refutation

/-- The position of a state among the explored states. -/
def locate (found : Exploration Pattern) (state : Pattern) : Option found.Index :=
  (List.finRange found.states.length).find? fun index => found.states.get index == state

theorem locate_some {found : Exploration Pattern} {state : Pattern} {index : found.Index}
    (located : locate found state = some index) : found.states.get index = state := by
  simpa using List.find?_some located

variable (plan bound expected) in
/-- **The verdict about a start state**: explore with the committing function, and when the
exploration settles, check the formula at the start. -/
def verdict (normal : Pattern → Pattern) {same : Setoid Pattern} (start : Pattern) (work : Nat)
    {n : Nat} (formula : Formula Traversal n) (atoms : Atoms same n) (budget : Nat) : Verdict :=
  if FutureOnly formula = true then
    if fixedPointsPositive formula = true then
      if settled (search plan bound expected normal) (explore (search plan bound expected normal) start work) = true then
        match locate (exploration plan bound expected normal (explore (search plan bound expected normal) start work)) start with
        | some index => readOutcome ((exploration plan bound expected normal
            (explore (search plan bound expected normal) start work)).check formula atoms budget index)
        | none => .unknown .startNotExplored
      else .unknown .unsettled
    else .unknown .notPositive
  else .unknown .pastModality

/-- **A proved verdict is the property of the plan's steps at the start.** -/
theorem verdict_proved (checked : Predecessors.equationsChecked plan = true)
    {normal : Pattern → Pattern} {same : Setoid Pattern} {good : Pattern → Prop}
    (abstraction : Abstraction plan bound expected normal same good)
    {start : Pattern} (startGood : good start) {work : Nat} {n : Nat} {formula : Formula Traversal n}
    {atoms : Atoms same n} {budget : Nat}
    (read : verdict plan bound expected normal start work formula atoms budget = .proved) :
    satisfies (transitionSystem (gsltSpan (theory plan bound expected))) atoms.meaning formula start := by
  unfold verdict at read
  split_ifs at read with future positive done
  split at read
  · rename_i index located
    exact (Exploration.satisfies_iff (exact_of_settled checked abstraction startGood work done)
      abstraction.closed abstraction.matching formula future positive atoms index startGood
      ((congrArg (same.r start) (locate_some located)).mpr (same.refl start))).mp
        (readOutcome_proved read)
  · cases read

/-- **A refuted verdict is the failure of the property at the start.** -/
theorem verdict_refuted (checked : Predecessors.equationsChecked plan = true)
    {normal : Pattern → Pattern} {same : Setoid Pattern} {good : Pattern → Prop}
    (abstraction : Abstraction plan bound expected normal same good)
    {start : Pattern} (startGood : good start) {work : Nat} {n : Nat} {formula : Formula Traversal n}
    {atoms : Atoms same n} {budget : Nat}
    (read : verdict plan bound expected normal start work formula atoms budget = .refuted) :
    ¬ satisfies (transitionSystem (gsltSpan (theory plan bound expected))) atoms.meaning formula start := by
  unfold verdict at read
  split_ifs at read with future positive done
  split at read
  · rename_i index located
    exact fun holds => readOutcome_refuted read
      ((Exploration.satisfies_iff (exact_of_settled checked abstraction startGood work done)
        abstraction.closed abstraction.matching formula future positive atoms index startGood
        ((congrArg (same.r start) (locate_some located)).mpr (same.refl start))).mpr holds)
  · cases read

/-! ## Equation-free plans -/

/-- Without equations every Boolean atom respects the plan's equality. -/
def equationFreeAtoms (empty : plan.equations = []) {n : Nat} (holds : Fin n → Pattern → Bool) :
    Atoms (theory plan bound expected).equations n where
  holds := holds
  invariant index _ _ related := by
    rw [Classes.equivalent_eq_of_no_equations plan bound expected empty related]

end Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled
