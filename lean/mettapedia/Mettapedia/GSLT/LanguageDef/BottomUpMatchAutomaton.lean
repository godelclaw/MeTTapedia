import Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
import Mathlib.Data.List.Dedup
import Mettapedia.GSLT.LanguageDef.SubtermMatching
import Mathlib.Data.List.Sublists

/-!
# Bottom-up automata for matching at every subterm

The compiler interns structural subpatterns, while keeping the authored root
pattern list intact. A transition reads one constructor and the states already
computed for its children. It never calls the recursive source matcher.

The state at a node is the finite set of interned patterns matching there,
represented in inventory order. State trees retain positions; a separate
ordered observation pass retains duplicate authored occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BottomUpMatchAutomaton

open OrderedPatternMatrixCompilation

universe u
variable {Head : Type u}

mutual
  /-- All subpatterns, including the root. -/
  def subpatterns : Pattern Head → List (Pattern Head)
    | .wildcard => [.wildcard]
    | .node h ps => .node h ps :: subpatternsList ps

  def subpatternsList : List (Pattern Head) → List (Pattern Head)
    | [] => []
    | p :: ps => subpatterns p ++ subpatternsList ps
end

/-- A constructor transition can look up every child pattern in the inventory. -/
def ChildClosed (patterns : List (Pattern Head)) : Prop :=
  ∀ h ps, Pattern.node h ps ∈ patterns → ∀ p ∈ ps, p ∈ patterns

@[simp] theorem mem_subpatterns_self (p : Pattern Head) : p ∈ subpatterns p := by
  cases p <;> simp [subpatterns]

theorem mem_subpatternsList_of_mem {p : Pattern Head}
    {ps : List (Pattern Head)} (hp : p ∈ ps) : p ∈ subpatternsList ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [subpatternsList]
      · simp [subpatternsList, ih hp]

mutual
  theorem subpatterns_childClosed (p : Pattern Head) : ChildClosed (subpatterns p) := by
    cases p with
    | wildcard =>
        intro h ps hp
        simp [subpatterns] at hp
    | node h ps =>
        intro k qs hq q hqmem
        simp only [subpatterns, List.mem_cons] at hq
        rcases hq with eq | hq
        · cases eq
          exact List.mem_cons_of_mem _ (mem_subpatternsList_of_mem hqmem)
        · exact List.mem_cons_of_mem _ (subpatternsList_childClosed ps k qs hq q hqmem)

  theorem subpatternsList_childClosed (ps : List (Pattern Head)) :
      ChildClosed (subpatternsList ps) := by
    cases ps with
    | nil => intro h qs hp; simp [subpatternsList] at hp
    | cons p ps =>
        intro h qs hp q hq
        simp only [subpatternsList, List.mem_append] at hp
        rcases hp with hp | hp
        · exact List.mem_append_left _ (subpatterns_childClosed p h qs hp q hq)
        · exact List.mem_append_right _ (subpatternsList_childClosed ps h qs hp q hq)
end

variable [DecidableEq Head]

/-- Compile a finite inventory; duplicate rules are not removed from the
separate authored list used by the observation pass. -/
def inventory (patterns : List (Pattern Head)) : List (Pattern Head) :=
  (subpatternsList patterns).eraseDups

theorem inventory_childClosed (patterns : List (Pattern Head)) :
    ChildClosed (inventory patterns) := by
  intro h ps hp p hmem
  simp only [inventory, List.mem_eraseDups] at hp ⊢
  exact subpatternsList_childClosed patterns h ps hp p hmem

theorem mem_inventory_of_mem {p : Pattern Head} {ps : List (Pattern Head)}
    (hp : p ∈ ps) : p ∈ inventory ps := by
  simpa [inventory] using mem_subpatternsList_of_mem hp

/-- Match a child vector using only the children's finite match states. -/
def childAccept : List (Pattern Head) → List (List (Pattern Head)) → Bool
  | [], [] => true
  | p :: ps, s :: ss => decide (p ∈ s) && childAccept ps ss
  | _, _ => false

/-- One automaton transition on one observed constructor. -/
def accepts (head : Head) (states : List (List (Pattern Head))) : Pattern Head → Bool
  | .wildcard => true
  | .node expected children => decide (expected = head) && childAccept children states

def transition (patterns : List (Pattern Head)) (head : Head)
    (states : List (List (Pattern Head))) : List (Pattern Head) :=
  patterns.filter (accepts head states)

/-- The control state and the constructor-inspection count are produced
together by the machine. -/
abbrev StateTree (Head : Type u) := Subject (List (Pattern Head) × Nat)

def state (tree : StateTree Head) : List (Pattern Head) :=
  match tree with | .node label _ => label.1

def inspections (tree : StateTree Head) : Nat :=
  match tree with | .node label _ => label.2

mutual
  /-- Bottom-up execution: child results are computed once, then shared by
  every inventory pattern inspected in the parent transition. -/
  def analyze (patterns : List (Pattern Head)) : Subject Head → StateTree Head
    | .node head children =>
        let trees := analyzeList patterns children
        .node (transition patterns head (trees.map state),
          1 + (trees.map inspections).sum) trees

  def analyzeList (patterns : List (Pattern Head)) :
      List (Subject Head) → List (StateTree Head)
    | [] => []
    | child :: children => analyze patterns child :: analyzeList patterns children
end

mutual
  def nodeCount : Subject Head → Nat
    | .node _ children => 1 + nodesCount children

  def nodesCount : List (Subject Head) → Nat
    | [] => 0
    | child :: children => nodeCount child + nodesCount children
end

mutual
  theorem inspections_analyze (patterns : List (Pattern Head)) (subject : Subject Head) :
      inspections (analyze patterns subject) = nodeCount subject := by
    cases subject with
    | node head children =>
        simp only [analyze, inspections, nodeCount]
        rw [inspections_analyzeList]

  theorem inspections_analyzeList (patterns : List (Pattern Head))
      (subjects : List (Subject Head)) :
      ((analyzeList patterns subjects).map inspections).sum = nodesCount subjects := by
    cases subjects with
    | nil => rfl
    | cons subject subjects =>
        simp only [analyzeList, List.map_cons, List.sum_cons, nodesCount]
        rw [inspections_analyze, inspections_analyzeList]
end

mutual
  /-- The machine's finite state has exactly the independently specified
  structural matches at this node. -/
  theorem state_analyze (patterns : List (Pattern Head)) (closed : ChildClosed patterns)
      (subject : Subject Head) :
      state (analyze patterns subject) = patterns.filter (fun p => structuralMatch p subject) := by
    cases subject with
    | node head children =>
        simp only [analyze, state, transition]
        apply List.filter_congr
        intro p hp
        cases p with
        | wildcard => rfl
        | node expected ps =>
            simp only [accepts, structuralMatch]
            rw [childAccept_analyzeList patterns closed ps children
              (closed expected ps hp)]

  theorem childAccept_analyzeList (patterns : List (Pattern Head))
      (closed : ChildClosed patterns) (ps : List (Pattern Head))
      (subjects : List (Subject Head)) (supported : ∀ p ∈ ps, p ∈ patterns) :
      childAccept ps ((analyzeList patterns subjects).map state) =
        structuralMatchList ps subjects := by
    cases ps with
    | nil => cases subjects <;> rfl
    | cons p ps =>
        cases subjects with
        | nil => rfl
        | cons subject subjects =>
            simp only [analyzeList, List.map_cons, childAccept, structuralMatchList]
            rw [state_analyze patterns closed subject]
            have hp : p ∈ patterns := supported p (by simp)
            simp only [List.mem_filter, hp, true_and, Bool.decide_eq_true]
            rw [childAccept_analyzeList patterns closed ps subjects
              (fun q hq => supported q (by simp [hq]))]
end

theorem state_compiled (patterns : List (Pattern Head)) (subject : Subject Head) :
    state (analyze (inventory patterns) subject) =
      (inventory patterns).filter (fun p => structuralMatch p subject) :=
  state_analyze _ (inventory_childClosed patterns) subject

open SubtermMatching

mutual
  theorem positions_analyze (patterns : List (Pattern Head)) (closed : ChildClosed patterns)
      (subject : Subject Head) :
      (positions (analyze patterns subject)).map (fun entry => (entry.1, state entry.2)) =
        (positions subject).map
          (fun entry => (entry.1, patterns.filter (fun p => structuralMatch p entry.2))) := by
    cases subject with
    | node head children =>
        simp only [analyze, positions, List.map_cons]
        congr 1
        · exact congrArg (fun s => ([], s)) (state_analyze patterns closed (.node head children))
        · exact positions_analyzeList patterns closed 0 children

  theorem positions_analyzeList (patterns : List (Pattern Head))
      (closed : ChildClosed patterns) (next : Nat) (subjects : List (Subject Head)) :
      (positionsList next (analyzeList patterns subjects)).map
          (fun entry => (entry.1, state entry.2)) =
        (positionsList next subjects).map
          (fun entry => (entry.1, patterns.filter (fun p => structuralMatch p entry.2))) := by
    cases subjects with
    | nil => rfl
    | cons subject subjects =>
        simp only [analyzeList, positionsList, List.map_append, List.map_map]
        congr 1
        · have ih := positions_analyze patterns closed subject
          have lifted := congrArg (List.map (fun (entry : Position × List (Pattern Head)) =>
            (next :: entry.1, entry.2))) ih
          simpa only [List.map_map, Function.comp_def] using lifted
        · exact positions_analyzeList patterns closed (next + 1) subjects
end

/-- Observe the finite states in source preorder and authored occurrence order. -/
def run (patterns : List (Pattern Head)) (subject : Subject Head) : List Location :=
  (positions (analyze (inventory patterns) subject)).flatMap fun entry =>
    (select (fun p => decide (p ∈ state entry.2)) 0 patterns).map
      (fun occurrence => ⟨entry.1, occurrence⟩)

/-- Exact subterm matching, including positions, order, and duplicate rows. -/
theorem run_eq_reference (patterns : List (Pattern Head)) (subject : Subject Head) :
    run patterns subject = reference patterns subject := by
  let emit := fun (entry : Position × List (Pattern Head)) =>
    (select (fun p => decide (p ∈ entry.2)) 0 patterns).map
      (fun occurrence => (⟨entry.1, occurrence⟩ : Location))
  have observations := positions_analyze (inventory patterns)
    (inventory_childClosed patterns) subject
  have equality := congrArg (List.flatMap emit) observations
  simp only [List.flatMap_map] at equality
  rw [run, equality]
  unfold reference
  apply List.flatMap_congr
  intro entry _
  dsimp only [emit]
  congr 1
  apply select_congr
  intro p hp
  have supported := mem_inventory_of_mem hp
  simp [supported]

theorem inspections_compiled (patterns : List (Pattern Head)) (subject : Subject Head) :
    inspections (analyze (inventory patterns) subject) = nodeCount subject :=
  inspections_analyze _ _

/-- Every computed control belongs to a finite, subject-independent state
universe. The executable never enumerates this exponential universe. -/
theorem state_mem_finite_controls (patterns : List (Pattern Head)) (subject : Subject Head) :
    state (analyze (inventory patterns) subject) ∈ (inventory patterns).sublists := by
  rw [state_compiled, List.mem_sublists]
  exact List.filter_sublist

#print axioms run_eq_reference
#print axioms inspections_compiled

end Mettapedia.GSLT.LanguageDef.BottomUpMatchAutomaton
