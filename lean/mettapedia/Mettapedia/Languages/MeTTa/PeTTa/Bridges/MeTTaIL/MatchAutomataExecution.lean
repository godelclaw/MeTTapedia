import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBindingExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataInventoryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataBottomExecution

/-!
# Exact observations of the retained matching drivers

The callable matcher entries compose the source lowering, structural automata
and canonical binding completion. Their observations retain the authored row
order, subterm positions, duplicate occurrences and binding lists. The state
and input/output components are included in the execution correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution

open Mettapedia.GSLT.LanguageDef
open CettaWire MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval MatchAutomataProgram
open MatchAutomataSourceExecution (listValue)
open MatchAutomataCompilationExecution (shapeTerm subjectTerm)
open MatchAutomataDerivativeExecution (positionTerm obligationTerm locationTerm goalTerm finishedTerm)
open MatchAutomataBindingExecution (matchesTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (value : Term) : Atom := CettaWireAtom.encode value
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternsValue (patterns : List PatternPlan) : Atom :=
  encoded (InferenceCettaWire.encodePatterns (erasePatterns patterns))
private abbrev patternValue (subject : PatternPlan) : Atom :=
  encoded (InferenceCettaWire.encodePattern subject.erase)

/-- The complete observable result carries bindings and explicit source counters.
These count constructor inspections and machine tests, rather than total evaluation cost. -/
def matchRunTerm (results : List MeTTaILSubtermMatchAutomata.BoundMatch)
    (reads dispatches : Nat) : Term :=
  .application "MatchRun" [matchesTerm results, .natural reads, .natural dispatches]

private inductive Driver where | top | bottom

private def Driver.head : Driver → String
  | .top => "gslt:automata:top"
  | .bottom => "gslt:automata:bottom"

private def driverEquation (driver : Driver) : SpaceSemantics.Equation :=
  (equations driver.head)[0]'(by cases driver <;> decide +kernel)

private def driverEnvironment (patterns : List PatternPlan) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject), ("patterns", patternsValue patterns)]

attribute [local simp] a v encoded number patternsValue patternValue Driver.head

private theorem driver_clause (driver : Driver) (patterns : List PatternPlan) (subject : PatternPlan) :
    clauses program driver.head [patternsValue patterns, patternValue subject] =
      [.evaluate (driverEnvironment patterns subject) (driverEquation driver).body] := by
  rw [clauses_use_only_the_named_equations]
  change (equations driver.head).filterMap _ = _
  have unique : equations driver.head = [driverEquation driver] := by cases driver <;> rfl
  have formals : (driverEquation driver).arguments = [v "patterns", v "subject"] := by
    cases driver <;> decide +kernel
  rw [unique]
  simp [formals, driverEnvironment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem driver_call (driver : Driver) (caller : Subst) (state : State)
    (patterns : List PatternPlan) (subject : PatternPlan) (arguments : List Atom) (answer : Atom)
    (captured : arguments.map (applySubst caller) = [patternsValue patterns, patternValue subject])
    (returned : PureReturns program (driverEnvironment patterns subject) state
      (driverEquation driver).body state answer) :
    PureReturns program caller state (a driver.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (driverEnvironment patterns subject) state state
    driver.head arguments (driverEquation driver).body answer
    (by cases driver <;> decide) (by cases driver <;> decide) (by cases driver <;> decide)
    (by cases driver <;> decide +kernel) _ _ returned
  · have length : arguments.length = 2 := by
      simpa only [List.length_map, List.length_cons, List.length_nil] using congrArg List.length captured
    intro index bounded
    rw [length] at bounded
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> cases driver <;> decide +kernel
  · rw [captured]
    exact driver_clause driver patterns subject

private def executeEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:execute")[0]'(by decide +kernel)

private theorem execute_captured (caller : Subst) (state : State)
    (observations : List (TopDownMatchDerivatives.Observation Term))
    (goals : List (TopDownMatchDerivatives.Goal Term)) (one two : Atom)
    (captured : [one, two].map (applySubst caller) =
      [listValue (observations.map obligationTerm), listValue (goals.map goalTerm)]) :
    PureReturns program caller state (a "gslt:automata:execute" [one, two, number 0]) state
      (encoded (finishedTerm (TopDownMatchDerivatives.executeCounted observations goals).1
        (TopDownMatchDerivatives.executeCounted observations goals).2)) := by
  let callee : Subst := [("dispatches", number 0), ("goals", listValue (goals.map goalTerm)),
    ("observations", listValue (observations.map obligationTerm))]
  apply PureData.raw_prefix_authored_call_return program caller callee state state state
    "gslt:automata:execute" [one, two]
    [listValue (observations.map obligationTerm), listValue (goals.map goalTerm)]
    (number 0) (number 0) executeEquation.body _
    (by decide) (by decide) (by decide +kernel) (by decide) _
    (by simp only [List.length_cons, List.length_nil]; decide +kernel) captured
    (grounded_returns program caller state (.int 0)) _ _
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by
      simp only [List.length_cons, List.length_nil] at bounded
      omega
    rcases small with rfl | rfl <;> decide +kernel
  · rw [clauses_use_only_the_named_equations]
    change (equations "gslt:automata:execute").filterMap _ = _
    rw [show equations "gslt:automata:execute" = [executeEquation] from rfl]
    have formals : executeEquation.arguments = [v "observations", v "goals", v "dispatches"] := by
      decide +kernel
    simp [formals, callee, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup]
  · convert MatchAutomataDerivativeExecution.execute_body_returns state observations goals 0 using 1
    all_goals first | rfl | simp

private theorem completed_captured (caller : Subst) (state : State)
    (goals : List (TopDownMatchDerivatives.Goal Term)) (argument : Atom)
    (captured : applySubst caller argument = listValue (goals.map goalTerm)) :
    PureReturns program caller state (a "gslt:automata:completed" [argument]) state
      (listValue ((TopDownMatchDerivatives.completed goals).map locationTerm)) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:automata:completed"
    [listValue (goals.map goalTerm)] [argument] _ (by decide +kernel) _ (by decide) _
    (MatchAutomataDerivativeExecution.completed_returns state goals)
  · intro index bounded
    have zero : index = 0 := by
      simp only [List.length_singleton] at bounded
      omega
    subst index
    decide +kernel
  · simp [captured]

private def structuralPatterns (patterns : List PatternPlan) :
    List (OrderedPatternMatrixCompilation.Pattern Term) :=
  patterns.map MatchAutomataInventoryExecution.patternView

private def topObservations (subject : PatternPlan) :
    List (TopDownMatchDerivatives.Observation Term) :=
  TopDownMatchDerivatives.observe (MatchAutomataInventoryExecution.subjectView subject)

private def topSeeds (patterns : List PatternPlan) (subject : PatternPlan) :
    List (TopDownMatchDerivatives.Goal Term) :=
  (topObservations subject).flatMap fun observation =>
    TopDownMatchDerivatives.seed observation.position 0
      ((structuralPatterns patterns).map TopDownMatchDerivatives.compile)

private def topExecuted (patterns : List PatternPlan) (subject : PatternPlan) :=
  TopDownMatchDerivatives.executeCounted (topObservations subject) (topSeeds patterns subject)

/-- The canonical binding observation and the independently counted derivative run. -/
def topRunTerm (patterns : List PatternPlan) (subject : PatternPlan) : Term :=
  matchRunTerm (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject)
    (topObservations subject).length (topExecuted patterns subject).2

private theorem structural_candidates (patterns : List PatternPlan) (subject : PatternPlan) :
    SubtermMatching.reference (structuralPatterns patterns)
      (MatchAutomataInventoryExecution.subjectView subject) =
    SubtermMatching.reference ((erasePatterns patterns).map MeTTaILSubtermMatchAutomata.View.lowerPattern)
      (MeTTaILSubtermMatchAutomata.View.lowerSubject subject.erase) := by
  exact MatchAutomataInventoryExecution.reference_views patterns subject

private theorem top_candidates (patterns : List PatternPlan) (subject : PatternPlan) :
    TopDownMatchDerivatives.completed (topExecuted patterns subject).1 =
      SubtermMatching.reference
        ((erasePatterns patterns).map MeTTaILSubtermMatchAutomata.View.lowerPattern)
        (MeTTaILSubtermMatchAutomata.View.lowerSubject subject.erase) := by
  rw [topExecuted, TopDownMatchDerivatives.executeCounted_result]
  change TopDownMatchDerivatives.run (structuralPatterns patterns)
    (MatchAutomataInventoryExecution.subjectView subject) = _
  rw [TopDownMatchDerivatives.run_eq_reference, structural_candidates]

private def topPairs : List (Atom × Atom) :=
  [(v "shapes", a "gslt:automata:shapes" [v "patterns"]),
   (v "tree", a "gslt:automata:subject" [v "subject"]),
   (v "programs", a "gslt:automata:programs" [v "shapes"]),
   (v "observations", a "gslt:automata:observe" [v "tree", .symbol "LNil"]),
   (v "goals", a "gslt:automata:seed-all" [v "observations", v "programs"]),
   (v "run", a "gslt:automata:execute" [v "observations", v "goals", number 0])]

private def topInnerPairs : List (Atom × Atom) :=
  [(v "locations", a "gslt:automata:completed" [v "remaining"]),
   (v "matches", a "gslt:automata:complete"
     [v "locations", v "patterns", v "subject", .symbol "LNil"]),
   (v "reads", a "gslt:automata:length" [v "observations"])]

private def runResult : Atom := a "MatchRun" [v "matches", v "reads", v "dispatches"]

private def topInner : Atom :=
  a "let*" [.expression (topInnerPairs.map fun pair => .expression [pair.1, pair.2]), runResult]

private def topCases : SpaceSemantics.Cases :=
  [(a "MFinished" [v "remaining", v "dispatches"], topInner)]

private def topCase : Atom :=
  a "case" [v "run", .expression (topCases.map fun row => .expression [row.1, row.2])]

private theorem top_shape : (driverEquation .top).body =
    a "let*" [.expression (topPairs.map fun pair => .expression [pair.1, pair.2]), topCase] := by
  decide +kernel

private theorem runResult_template : PureData.Template program runResult := by
  apply PureData.Template.constructor "MatchRun" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact .captured _

private theorem top_body_returns (state : State) (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program (driverEnvironment patterns subject) state (driverEquation .top).body state
      (encoded (topRunTerm patterns subject)) := by
  let views := structuralPatterns patterns
  let tree := MatchAutomataInventoryExecution.subjectView subject
  let programs := views.map TopDownMatchDerivatives.compile
  let observations := topObservations subject
  let goals := topSeeds patterns subject
  let executed := topExecuted patterns subject
  let candidates := TopDownMatchDerivatives.completed executed.1
  let bindings := driverEnvironment patterns subject
  let shapesBound := ("shapes", listValue (views.map shapeTerm)) :: bindings
  let treeBound := ("tree", encoded (subjectTerm tree)) :: shapesBound
  let programsBound := ("programs", listValue (programs.map (encodeList obligationTerm))) :: treeBound
  let observationsBound := ("observations", listValue (observations.map obligationTerm)) :: programsBound
  let goalsBound := ("goals", listValue (goals.map goalTerm)) :: observationsBound
  let runBound := ("run", encoded (finishedTerm executed.1 executed.2)) :: goalsBound
  let selected := ("dispatches", number executed.2) ::
    ("remaining", listValue (executed.1.map goalTerm)) :: runBound
  let locationsBound := ("locations", listValue (candidates.map locationTerm)) :: selected
  let matchesValue := encoded (matchesTerm (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject))
  let matchesBound := ("matches", matchesValue) :: locationsBound
  let readsBound := ("reads", number observations.length) :: matchesBound
  have shapesReturned : PureReturns program bindings state
      (a "gslt:automata:shapes" [v "patterns"]) state (listValue (views.map shapeTerm)) := by
    simpa only [views, structuralPatterns, List.map_map, Function.comp_def] using
      MatchAutomataInventoryExecution.shapes_captured_returns bindings state patterns (v "patterns")
        (by simp [bindings, driverEnvironment, applySubst, Subst.lookup])
  have treeReturned : PureReturns program shapesBound state
      (a "gslt:automata:subject" [v "subject"]) state (encoded (subjectTerm tree)) := by
    apply PureData.raw_capture_returns program [] shapesBound state state "gslt:automata:subject"
      [patternValue subject] [v "subject"] _ (by decide +kernel) _ (by decide) _
      (MatchAutomataInventoryExecution.subject_returns state subject)
    · intro index bounded
      have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
      subst index
      decide +kernel
    · simp [shapesBound, bindings, driverEnvironment, applySubst, Subst.lookup]
  have programsReturned : PureReturns program treeBound state
      (a "gslt:automata:programs" [v "shapes"]) state
      (listValue (programs.map (encodeList obligationTerm))) := by
    exact MatchAutomataCompilationExecution.programs_captured_returns treeBound state views (v "shapes")
      (by simp [treeBound, shapesBound, applySubst, Subst.lookup])
  have observationsReturned : PureReturns program programsBound state
      (a "gslt:automata:observe" [v "tree", .symbol "LNil"]) state
      (listValue (observations.map obligationTerm)) := by
    have shifted : TopDownMatchDerivatives.shift [] (TopDownMatchDerivatives.observe tree) =
        TopDownMatchDerivatives.observe tree := by
      change List.map id _ = _
      exact List.map_id _
    simpa only [shifted, observations, topObservations, tree] using
      MatchAutomataCompilationExecution.observe_captured_returns programsBound state tree []
        (v "tree") (.symbol "LNil")
        (by simp [programsBound, treeBound, applySubst, Subst.lookup]) rfl
  have goalsReturned : PureReturns program observationsBound state
      (a "gslt:automata:seed-all" [v "observations", v "programs"]) state
      (listValue (goals.map goalTerm)) := by
    exact MatchAutomataCompilationExecution.seed_all_captured_returns observationsBound state observations programs
      (v "observations") (v "programs")
      (by simp [observationsBound, applySubst, Subst.lookup])
      (by simp [observationsBound, programsBound, applySubst, Subst.lookup])
  have runReturned : PureReturns program goalsBound state
      (a "gslt:automata:execute" [v "observations", v "goals", number 0]) state
      (encoded (finishedTerm executed.1 executed.2)) :=
    execute_captured goalsBound state observations goals _ _
      (by simp [goalsBound, observationsBound, applySubst, Subst.lookup])
  have locationsReturned : PureReturns program selected state
      (a "gslt:automata:completed" [v "remaining"]) state (listValue (candidates.map locationTerm)) :=
    completed_captured selected state executed.1 _ (by simp [selected, applySubst, Subst.lookup])
  have matchesReturned : PureReturns program locationsBound state
      (a "gslt:automata:complete" [v "locations", v "patterns", v "subject", .symbol "LNil"]) state
      matchesValue := by
    have result := MatchAutomataBindingExecution.complete_captured_returns locationsBound state candidates
      patterns subject [v "locations", v "patterns", v "subject", .symbol "LNil"]
      (by
        simp [locationsBound, selected, runBound, goalsBound, observationsBound, programsBound, treeBound,
          shapesBound, bindings, driverEnvironment, applySubst, Subst.lookup, listValue, encodeList_map]
        rfl)
    rw [show candidates = _ from top_candidates patterns subject,
      MeTTaILSubtermMatchAutomata.complete_reference] at result
    exact result
  have readsReturned : PureReturns program matchesBound state
      (a "gslt:automata:length" [v "observations"]) state (number observations.length) := by
    simpa using MatchAutomataSourceExecution.length_captured_returns matchesBound state
      (observations.map obligationTerm) (v "observations")
      (by simp [matchesBound, locationsBound, selected, runBound, goalsBound, observationsBound,
        applySubst, Subst.lookup])
  have resultReturned : PureReturns program readsBound state runResult state (encoded (topRunTerm patterns subject)) := by
    simpa [runResult, topRunTerm, matchRunTerm, readsBound, matchesBound, locationsBound, selected,
      matchesValue, observations, executed, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      applySubst, applySubst.applySubstList, Subst.lookup] using
      PureData.template_return program readsBound state _ runResult_template
  have innerReturned : PureReturns program selected state topInner state (encoded (topRunTerm patterns subject)) := by
    apply PureData.let_bindings_return (pairs := topInnerPairs) (final := readsBound) _
      state runResult _ resultReturned
    refine .cons locationsReturned ?_ (.cons matchesReturned ?_ (.cons readsReturned ?_ (.nil readsBound state)))
    all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, readsBound, matchesBound, locationsBound,
      selected, runBound, goalsBound, observationsBound, programsBound, treeBound, shapesBound, bindings, driverEnvironment]
  have caseReturned : PureReturns program runBound state topCase state (encoded (topRunTerm patterns subject)) := by
    apply case_returns program runBound selected state state state (v "run")
      (encoded (finishedTerm executed.1 executed.2)) topInner _ _ topCases (read_cases_encoded _) _ _ innerReturned
    · simpa [runBound, applySubst, Subst.lookup] using variable_returns program runBound state "run"
    · simp [topCases, finishedTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup, selected, runBound, goalsBound, observationsBound, programsBound,
        treeBound, shapesBound, bindings, driverEnvironment]
  rw [top_shape]
  apply PureData.let_bindings_return (pairs := topPairs) (final := runBound) _ state topCase _ caseReturned
  refine .cons shapesReturned ?_ (.cons treeReturned ?_ (.cons programsReturned ?_
    (.cons observationsReturned ?_ (.cons goalsReturned ?_ (.cons runReturned ?_ (.nil runBound state))))))
  all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, runBound, goalsBound,
    observationsBound, programsBound, treeBound, shapesBound, bindings, driverEnvironment]

/-- Actual top-down source execution computes the complete canonical match list. -/
theorem top_returns (state : State) (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:top" [patternsValue patterns, patternValue subject]) state
      (encoded (topRunTerm patterns subject)) :=
  driver_call .top [] state patterns subject _ _ (by simp) (top_body_returns state patterns subject)

theorem top_captured_returns (caller : Subst) (state : State) (patterns : List PatternPlan)
    (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [patternsValue patterns, patternValue subject]) :
    PureReturns program caller state (a "gslt:automata:top" arguments) state
      (encoded (topRunTerm patterns subject)) :=
  driver_call .top caller state patterns subject arguments _ captured (top_body_returns state patterns subject)

private def bottomInventory (patterns : List PatternPlan) :=
  BottomUpMatchAutomaton.inventory (structuralPatterns patterns)

/-- Canonical bindings together with the actual bottom-up inspection and test counts. -/
def bottomRunTerm (patterns : List PatternPlan) (subject : PatternPlan) : Term :=
  let reads := BottomUpMatchAutomaton.nodeCount (MatchAutomataInventoryExecution.subjectView subject)
  matchRunTerm (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject)
    reads (reads * (bottomInventory patterns).length)

private def bottomPairs : List (Atom × Atom) :=
  [(v "shapes", a "gslt:automata:shapes" [v "patterns"]),
   (v "tree", a "gslt:automata:subject" [v "subject"]),
   (v "raw", a "gslt:automata:subpatterns-list" [v "shapes"]),
   (v "inventory", a "gslt:automata:unique" [v "raw"]),
   (v "state", a "gslt:automata:bottom-state" [v "inventory", v "tree"]),
   (v "locations", a "gslt:automata:bottom-locations" [v "shapes", v "state", .symbol "LNil"]),
   (v "matches", a "gslt:automata:complete"
     [v "locations", v "patterns", v "subject", .symbol "LNil"])]

private def bottomResult : Atom := a "MatchRun" [v "matches", v "reads", v "tests"]

private def bottomCases : SpaceSemantics.Cases :=
  [(a "MState" [v "root", v "children", v "reads", v "tests"], bottomResult)]

private def bottomCase : Atom :=
  a "case" [v "state", .expression (bottomCases.map fun row => .expression [row.1, row.2])]

private theorem bottom_shape : (driverEquation .bottom).body =
    a "let*" [.expression (bottomPairs.map fun pair => .expression [pair.1, pair.2]), bottomCase] := by
  decide +kernel

private theorem bottomResult_template : PureData.Template program bottomResult := by
  apply PureData.Template.constructor "MatchRun" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact .captured _

private theorem bottom_body_returns (state : State) (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program (driverEnvironment patterns subject) state (driverEquation .bottom).body state
      (encoded (bottomRunTerm patterns subject)) := by
  let views := structuralPatterns patterns
  let tree := MatchAutomataInventoryExecution.subjectView subject
  let inventory := bottomInventory patterns
  let raw := BottomUpMatchAutomaton.subpatternsList views
  let candidates := BottomUpMatchAutomaton.run views tree
  cases analyzed : BottomUpMatchAutomaton.analyze inventory tree with
  | node label children =>
      obtain ⟨root, reads⟩ := label
      let analyzedTree : BottomUpMatchAutomaton.StateTree Term := .node (root, reads) children
      have readsExact : reads = BottomUpMatchAutomaton.nodeCount tree := by
        have counted := BottomUpMatchAutomaton.inspections_analyze inventory tree
        rw [analyzed] at counted
        exact counted
      let bindings := driverEnvironment patterns subject
      let shapesBound := ("shapes", listValue (views.map shapeTerm)) :: bindings
      let treeBound := ("tree", encoded (subjectTerm tree)) :: shapesBound
      let rawBound := ("raw", listValue (raw.map shapeTerm)) :: treeBound
      let inventoryBound := ("inventory", listValue (inventory.map shapeTerm)) :: rawBound
      let stateValue := encoded (MatchAutomataBottomExecution.stateTerm inventory.length analyzedTree)
      let stateBound := ("state", stateValue) :: inventoryBound
      let locationsBound := ("locations", listValue (candidates.map locationTerm)) :: stateBound
      let matchesValue := encoded (matchesTerm (MeTTaILSubtermMatchAutomata.reference (erasePatterns patterns) subject))
      let matchesBound := ("matches", matchesValue) :: locationsBound
      let selected := ("tests", number (reads * inventory.length)) :: ("reads", number reads) ::
        ("children", listValue (children.map (MatchAutomataBottomExecution.stateTerm inventory.length))) ::
        ("root", listValue (root.map shapeTerm)) :: matchesBound
      have shapesReturned : PureReturns program bindings state
          (a "gslt:automata:shapes" [v "patterns"]) state (listValue (views.map shapeTerm)) := by
        simpa only [views, structuralPatterns, List.map_map, Function.comp_def] using
          MatchAutomataInventoryExecution.shapes_captured_returns bindings state patterns _
            (by simp [bindings, driverEnvironment, applySubst, Subst.lookup])
      have treeReturned : PureReturns program shapesBound state
          (a "gslt:automata:subject" [v "subject"]) state (encoded (subjectTerm tree)) := by
        exact MatchAutomataInventoryExecution.subject_captured_returns shapesBound state subject _
          (by simp [shapesBound, bindings, driverEnvironment, applySubst, Subst.lookup])
      have rawReturned : PureReturns program treeBound state
          (a "gslt:automata:subpatterns-list" [v "shapes"]) state (listValue (raw.map shapeTerm)) := by
        exact MatchAutomataInventoryExecution.subpatterns_list_captured_returns treeBound state views _
          (by simp [treeBound, shapesBound, applySubst, Subst.lookup])
      have inventoryReturned : PureReturns program rawBound state
          (a "gslt:automata:unique" [v "raw"]) state (listValue (inventory.map shapeTerm)) := by
        have computed := MatchAutomataInventoryExecution.unique_captured_returns rawBound state
          (raw.map shapeTerm) (v "raw") (by simp [rawBound, applySubst, Subst.lookup])
        change PureReturns program rawBound state (a "gslt:automata:unique" [v "raw"]) state
          (listValue (raw.eraseDups.map shapeTerm))
        simpa only [MatchAutomataInventoryExecution.eraseDups_shape_map] using computed
      have stateReturned : PureReturns program inventoryBound state
          (a "gslt:automata:bottom-state" [v "inventory", v "tree"]) state stateValue := by
        have computed := MatchAutomataBottomExecution.bottom_state_captured_returns inventoryBound state inventory tree
          (v "inventory") (v "tree")
          (by simp [inventoryBound, rawBound, treeBound, shapesBound, applySubst, Subst.lookup,
            listValue, encodeList_map])
        rw [analyzed] at computed
        exact computed
      have locationsReturned : PureReturns program stateBound state
          (a "gslt:automata:bottom-locations" [v "shapes", v "state", .symbol "LNil"]) state
          (listValue (candidates.map locationTerm)) := by
        exact MatchAutomataBottomExecution.bottom_locations_captured_returns stateBound state views tree
            (v "shapes") (v "state") (.symbol "LNil")
            (by
              change [applySubst stateBound (v "shapes"), applySubst stateBound (v "state"), .symbol "LNil"] =
                [listValue (views.map shapeTerm),
                  encoded (MatchAutomataBottomExecution.stateTerm inventory.length
                    (BottomUpMatchAutomaton.analyze inventory tree)), .symbol "LNil"]
              rw [analyzed]
              simp [stateBound, stateValue, analyzedTree, inventoryBound, rawBound, treeBound, shapesBound,
                applySubst, Subst.lookup, listValue, encodeList_map])
      have matchesReturned : PureReturns program locationsBound state
          (a "gslt:automata:complete" [v "locations", v "patterns", v "subject", .symbol "LNil"]) state
          matchesValue := by
        have computed := MatchAutomataBindingExecution.complete_captured_returns locationsBound state candidates
          patterns subject [v "locations", v "patterns", v "subject", .symbol "LNil"]
          (by
            simp [locationsBound, stateBound, inventoryBound, rawBound, treeBound, shapesBound, bindings,
              driverEnvironment, applySubst, Subst.lookup, listValue, encodeList_map]
            rfl)
        have exactCandidates : candidates =
            SubtermMatching.reference ((erasePatterns patterns).map MeTTaILSubtermMatchAutomata.View.lowerPattern)
              (MeTTaILSubtermMatchAutomata.View.lowerSubject subject.erase) := by
          change BottomUpMatchAutomaton.run views tree = _
          rw [BottomUpMatchAutomaton.run_eq_reference]
          exact structural_candidates patterns subject
        rw [exactCandidates, MeTTaILSubtermMatchAutomata.complete_reference] at computed
        exact computed
      have resultReturned : PureReturns program selected state bottomResult state
          (encoded (bottomRunTerm patterns subject)) := by
        simpa [bottomResult, bottomRunTerm, matchRunTerm, selected, matchesBound, matchesValue,
          readsExact, tree, inventory, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return program selected state _ bottomResult_template
      have caseReturned : PureReturns program matchesBound state bottomCase state
          (encoded (bottomRunTerm patterns subject)) := by
        apply case_returns program matchesBound selected state state state (v "state") stateValue
          bottomResult _ _ bottomCases (read_cases_encoded _) _ _ resultReturned
        · simpa [matchesBound, locationsBound, stateBound, applySubst, Subst.lookup] using
            variable_returns program matchesBound state "state"
        · simp [bottomCases, stateValue, analyzedTree, MatchAutomataBottomExecution.stateTerm,
            MatchAutomataBottomExecution.stateTerms_eq_map, listValue, encodeList_map,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
            selected, matchesBound, locationsBound, stateBound, inventoryBound, rawBound, treeBound,
            shapesBound, bindings, driverEnvironment]
      rw [bottom_shape]
      apply PureData.let_bindings_return (pairs := bottomPairs) (final := matchesBound) _
        state bottomCase _ caseReturned
      refine .cons shapesReturned ?_ (.cons treeReturned ?_ (.cons rawReturned ?_
        (.cons inventoryReturned ?_ (.cons stateReturned ?_ (.cons locationsReturned ?_
          (.cons matchesReturned ?_ (.nil matchesBound state)))))))
      all_goals simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, matchesBound, locationsBound,
        stateBound, inventoryBound, rawBound, treeBound, shapesBound, bindings, driverEnvironment]

/-- Actual bottom-up source execution computes the same complete canonical bindings. -/
theorem bottom_returns (state : State) (patterns : List PatternPlan) (subject : PatternPlan) :
    PureReturns program [] state
      (a "gslt:automata:bottom" [patternsValue patterns, patternValue subject]) state
      (encoded (bottomRunTerm patterns subject)) :=
  driver_call .bottom [] state patterns subject _ _ (by simp) (bottom_body_returns state patterns subject)

theorem bottom_captured_returns (caller : Subst) (state : State) (patterns : List PatternPlan)
    (subject : PatternPlan) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [patternsValue patterns, patternValue subject]) :
    PureReturns program caller state (a "gslt:automata:bottom" arguments) state
      (encoded (bottomRunTerm patterns subject)) :=
  driver_call .bottom caller state patterns subject arguments _ captured (bottom_body_returns state patterns subject)

/-- The callable top-down query uses the existing canonical pattern wire. -/
def topQuery (patterns : List PatternPlan) (subject : PatternPlan) : Atom :=
  a "gslt:automata:top" [patternsValue patterns, patternValue subject]

/-- The callable bottom-up query has the same input representation. -/
def bottomQuery (patterns : List PatternPlan) (subject : PatternPlan) : Atom :=
  a "gslt:automata:bottom" [patternsValue patterns, patternValue subject]

theorem top_completed_iff (state : State) (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (topQuery patterns subject) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (top_returns state patterns subject)
    after answers input output

theorem bottom_completed_iff (state : State) (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel { state, control := .evaluate [] (bottomQuery patterns subject) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (bottomRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (bottom_returns state patterns subject)
    after answers input output

/-- Preservation and reflection concern the consolidated PeTTa whole-run judgment. -/
theorem top_derivation_iff (state : State) (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (topQuery patterns subject) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (top_returns state patterns subject)
    after answers input output

theorem bottom_derivation_iff (state : State) (patterns : List PatternPlan) (subject : PatternPlan)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program { state, control := .evaluate [] (bottomQuery patterns subject) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (bottomRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _ (bottom_returns state patterns subject)
    after answers input output

/-- Matching projection of an authored rewrite row. Supplied context and premise
fields are retained as opaque data; both patterns use the shared exact wire. -/
def rewriteRowTerm (contexts premises : RewriteRule → Term) (row : RewriteRule) : Term :=
  .application "RewriteRule" [.string row.name, contexts row, premises row,
    InferenceCettaWire.encodePattern row.left, InferenceCettaWire.encodePattern row.right]

def rewriteRowsTerm (contexts premises : RewriteRule → Term) (rows : List RewriteRule) : Term :=
  encodeList (rewriteRowTerm contexts premises) rows

/-- This five-field value is a matching-face projection with retained supplied
metadata. It is not a parser or operational admission certificate: the wire
itself has no scoped binding metadata. -/
def matchingProjectionTerm (language : LanguageDef) (types terms equations : Term)
    (contexts premises : RewriteRule → Term) : Term :=
  .application "GSLTLanguageDefWireV1" [.string language.name, types, terms, equations,
    rewriteRowsTerm contexts premises language.rewrites]

private def rewriteRowsEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:rewrite-patterns")[0]'(by decide +kernel)

private def rewriteRowsEnvironment (contexts premises : RewriteRule → Term) (rows : List RewriteRule) : Subst :=
  [("rewrites", encoded (rewriteRowsTerm contexts premises rows))]

private def rewriteRowsCons : Atom := a "let" [v "tail", a "gslt:automata:rewrite-patterns" [v "rest"],
  a "LCons" [v "left", v "tail"]]

private def rewriteRowsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
    (a "LCons" [a "RewriteRule" [v "name", v "context", v "premises", v "left", v "right"], v "rest"],
      rewriteRowsCons)]

private theorem rewriteRows_shape : rewriteRowsEquation.body =
    a "case" [v "rewrites", .expression (rewriteRowsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem rewriteRows_call (caller : Subst) (state : State)
    (contexts premises : RewriteRule → Term) (rows : List RewriteRule) (argument : Atom)
    (captured : applySubst caller argument = encoded (rewriteRowsTerm contexts premises rows))
    (computed : PureReturns program (rewriteRowsEnvironment contexts premises rows) state
      rewriteRowsEquation.body state (encoded (InferenceCettaWire.encodePatterns (rows.map (·.left))))) :
    PureReturns program caller state (a "gslt:automata:rewrite-patterns" [argument]) state
      (encoded (InferenceCettaWire.encodePatterns (rows.map (·.left)))) := by
  apply PureData.raw_authored_call_return program caller (rewriteRowsEnvironment contexts premises rows)
    state state "gslt:automata:rewrite-patterns" [argument] rewriteRowsEquation.body _
    (by decide) (by decide) (by decide) (by decide +kernel) _ _ computed
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · rw [clauses_use_only_the_named_equations]
    change (equations "gslt:automata:rewrite-patterns").filterMap _ = _
    rw [show equations "gslt:automata:rewrite-patterns" = [rewriteRowsEquation] from rfl]
    have formals : rewriteRowsEquation.arguments = [v "rewrites"] := by decide +kernel
    simp [List.filterMap, formals, captured, rewriteRowsEnvironment, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem rewriteRows_result_template :
    PureData.Template program (a "LCons" [v "left", v "tail"]) := by
  apply PureData.Template.constructor "LCons" _ (by decide +kernel) (by decide)
  intro argument member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .captured _

private theorem rewriteRows_body_returns (state : State) (contexts premises : RewriteRule → Term)
    (rows : List RewriteRule) :
    PureReturns program (rewriteRowsEnvironment contexts premises rows) state rewriteRowsEquation.body state
      (encoded (InferenceCettaWire.encodePatterns (rows.map (·.left)))) := by
  induction rows with
  | nil =>
      rw [rewriteRows_shape]
      apply case_returns program (rewriteRowsEnvironment contexts premises [])
        (rewriteRowsEnvironment contexts premises []) state state state (v "rewrites")
        (.symbol "LNil") (.symbol "LNil") _ _ rewriteRowsCases (read_cases_encoded _) _ _ _
      · simpa [rewriteRowsEnvironment, rewriteRowsTerm, encodeList, CettaWireAtom.encode,
          applySubst, Subst.lookup] using
          variable_returns program (rewriteRowsEnvironment contexts premises []) state "rewrites"
      · simp [rewriteRowsCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa only [List.map_nil, InferenceCettaWire.encodePatterns, CettaWireAtom.encode] using
          symbol_returns program (rewriteRowsEnvironment contexts premises []) state "LNil"
  | cons first rest ih =>
      let bindings := rewriteRowsEnvironment contexts premises (first :: rest)
      let selected := ("rest", encoded (rewriteRowsTerm contexts premises rest)) ::
        ("right", encoded (InferenceCettaWire.encodePattern first.right)) ::
        ("left", encoded (InferenceCettaWire.encodePattern first.left)) ::
        ("premises", encoded (premises first)) :: ("context", encoded (contexts first)) ::
        ("name", encoded (.string first.name)) :: bindings
      let tailValue := encoded (InferenceCettaWire.encodePatterns (rest.map (·.left)))
      let tailBound := ("tail", tailValue) :: selected
      have tailReturned := rewriteRows_call selected state contexts premises rest (v "rest")
        (by simp [selected, applySubst, Subst.lookup]) ih
      rw [rewriteRows_shape]
      apply case_returns program bindings selected state state state (v "rewrites")
        (encoded (rewriteRowsTerm contexts premises (first :: rest))) rewriteRowsCons _ _ rewriteRowsCases
        (read_cases_encoded _) _ _ _
      · simpa [bindings, rewriteRowsEnvironment, applySubst, Subst.lookup] using
          variable_returns program bindings state "rewrites"
      · simp [rewriteRowsCases, rewriteRowsTerm, rewriteRowTerm, encodeList,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          selected, bindings, rewriteRowsEnvironment]
      · apply let_returns program selected tailBound state state state (v "tail") _ _ _ _ tailReturned _ _
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailBound, tailValue, selected, bindings, rewriteRowsEnvironment]
        · simpa [rewriteRowsCons, tailBound, tailValue, selected, List.map_cons,
            InferenceCettaWire.encodePatterns, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program tailBound state _ rewriteRows_result_template

/-- Projection examines the actual source row list without interpreting its metadata. -/
theorem rewrite_patterns_returns (state : State) (contexts premises : RewriteRule → Term)
    (rows : List RewriteRule) :
    PureReturns program [] state
      (a "gslt:automata:rewrite-patterns" [encoded (rewriteRowsTerm contexts premises rows)]) state
      (encoded (InferenceCettaWire.encodePatterns (rows.map (·.left)))) :=
  rewriteRows_call [] state contexts premises rows _ (by simp)
    (rewriteRows_body_returns state contexts premises rows)

private def languagePatternsEquation : SpaceSemantics.Equation :=
  (equations "gslt:automata:language-patterns")[0]'(by decide +kernel)

private def languagePatternsEnvironment (language : LanguageDef) (types terms equationRows : Term)
    (contexts premises : RewriteRule → Term) : Subst :=
  [("rewrites", encoded (rewriteRowsTerm contexts premises language.rewrites)),
    ("equations", encoded equationRows), ("terms", encoded terms), ("types", encoded types),
    ("name", encoded (.string language.name))]

theorem language_patterns_returns (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term) :
    PureReturns program [] state (a "gslt:automata:language-patterns"
      [encoded (matchingProjectionTerm language types terms equationRows contexts premises)]) state
      (encoded (InferenceCettaWire.encodePatterns (MeTTaILSubtermMatchAutomata.languagePatterns language))) := by
  let callee := languagePatternsEnvironment language types terms equationRows contexts premises
  apply PureData.raw_authored_call_return program [] callee state state "gslt:automata:language-patterns"
    [encoded (matchingProjectionTerm language types terms equationRows contexts premises)]
    languagePatternsEquation.body _ (by decide) (by decide) (by decide) (by decide +kernel) _ _ _
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
    subst index
    decide +kernel
  · rw [clauses_use_only_the_named_equations]
    change (equations "gslt:automata:language-patterns").filterMap _ = _
    rw [show equations "gslt:automata:language-patterns" = [languagePatternsEquation] from rfl]
    have formals : languagePatternsEquation.arguments =
        [a "GSLTLanguageDefWireV1" [v "name", v "types", v "terms", v "equations", v "rewrites"]] := by
      decide +kernel
    simp only [List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode]
    simp [List.filterMap, formals, matchingProjectionTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      callee, languagePatternsEnvironment]
  · have shape : languagePatternsEquation.body = a "gslt:automata:rewrite-patterns" [v "rewrites"] := by
      decide +kernel
    rw [shape]
    exact rewriteRows_call callee state contexts premises language.rewrites (v "rewrites")
      (by simp [callee, languagePatternsEnvironment, applySubst, Subst.lookup])
      (rewriteRows_body_returns state contexts premises language.rewrites)

private def Driver.languageHead : Driver → String
  | .top => "gslt:automata:language-top"
  | .bottom => "gslt:automata:language-bottom"

private def languageDriverEquation (driver : Driver) : SpaceSemantics.Equation :=
  (equations driver.languageHead)[0]'(by cases driver <;> decide +kernel)

private def Driver.runTerm : Driver → List PatternPlan → PatternPlan → Term
  | .top => topRunTerm
  | .bottom => bottomRunTerm

private def languageEnvironment (wire : Term) (subject : PatternPlan) : Subst :=
  [("subject", patternValue subject), ("language", encoded wire)]

private theorem language_call (driver : Driver) (state : State) (wire : Term) (subject : PatternPlan)
    (answer : Atom)
    (returned : PureReturns program (languageEnvironment wire subject) state (languageDriverEquation driver).body
      state answer) :
    PureReturns program [] state (a driver.languageHead [encoded wire, patternValue subject]) state answer := by
  apply PureData.raw_authored_call_return program [] (languageEnvironment wire subject) state state
    driver.languageHead [encoded wire, patternValue subject] (languageDriverEquation driver).body answer
    (by cases driver <;> decide) (by cases driver <;> decide) (by cases driver <;> decide)
    (by cases driver <;> decide +kernel) _ _ returned
  · intro index bounded
    have small : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    rcases small with rfl | rfl <;> cases driver <;> decide +kernel
  · rw [clauses_use_only_the_named_equations]
    change (equations driver.languageHead).filterMap _ = _
    have unique : equations driver.languageHead = [languageDriverEquation driver] := by cases driver <;> rfl
    have formals : (languageDriverEquation driver).arguments = [v "language", v "subject"] := by
      cases driver <;> decide +kernel
    rw [unique]
    simp [formals, languageEnvironment, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem language_body_returns (driver : Driver) (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language) :
    PureReturns program (languageEnvironment
      (matchingProjectionTerm language types terms equationRows contexts premises) subject)
      state (languageDriverEquation driver).body state
      (encoded (driver.runTerm patterns subject)) := by
  let wire := matchingProjectionTerm language types terms equationRows contexts premises
  let bindings := languageEnvironment wire subject
  let bound := ("patterns", patternsValue patterns) :: bindings
  have projected : PureReturns program bindings state
      (a "gslt:automata:language-patterns" [v "language"]) state (patternsValue patterns) := by
    rw [patternsValue, admitted]
    apply PureData.raw_capture_returns program [] bindings state state "gslt:automata:language-patterns"
      [encoded wire] [v "language"] _ (by decide +kernel) _ (by decide) _
      (language_patterns_returns state language types terms equationRows contexts premises)
    · intro index bounded
      have zero : index = 0 := by simp only [List.length_singleton] at bounded; omega
      subst index
      decide +kernel
    · simp [bindings, languageEnvironment, applySubst, Subst.lookup]
  have matched : SpaceSemantics.matchBinding bindings (v "patterns") (patternsValue patterns) = some bound := by
    simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, bindings, languageEnvironment]
  have continuation : PureReturns program bound state (a driver.head [v "patterns", v "subject"]) state
      (encoded (driver.runTerm patterns subject)) := by
    cases driver with
    | top =>
        exact top_captured_returns bound state patterns subject _
          (by simp [bound, bindings, languageEnvironment, applySubst, Subst.lookup])
    | bottom =>
        exact bottom_captured_returns bound state patterns subject _
          (by simp [bound, bindings, languageEnvironment, applySubst, Subst.lookup])
  have shape : (languageDriverEquation driver).body =
      a "let" [v "patterns", a "gslt:automata:language-patterns" [v "language"],
        a driver.head [v "patterns", v "subject"]] := by
    cases driver <;> decide +kernel
  rw [shape]
  exact let_returns program bindings bound state state state (v "patterns") _ _ _ _ projected matched continuation

/-- The matching face of an authored language composes with the retained top driver.
The premise admits its exact ordered LHS list, without an operational metadata claim. -/
theorem language_top_returns (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language) :
    PureReturns program [] state (a "gslt:automata:language-top"
      [encoded (matchingProjectionTerm language types terms equationRows contexts premises), patternValue subject])
      state (encoded (topRunTerm patterns subject)) :=
  language_call .top state _ subject _
    (language_body_returns .top state language types terms equationRows contexts premises patterns subject admitted)

theorem language_bottom_returns (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language) :
    PureReturns program [] state (a "gslt:automata:language-bottom"
      [encoded (matchingProjectionTerm language types terms equationRows contexts premises), patternValue subject])
      state (encoded (bottomRunTerm patterns subject)) :=
  language_call .bottom state _ subject _
    (language_body_returns .bottom state language types terms equationRows contexts premises patterns subject admitted)

/-- The language matching query retains the supplied five-field projection. -/
def languageTopQuery (language : LanguageDef) (types terms equationRows : Term)
    (contexts premises : RewriteRule → Term) (subject : PatternPlan) : Atom :=
  a "gslt:automata:language-top"
    [encoded (matchingProjectionTerm language types terms equationRows contexts premises), patternValue subject]

def languageBottomQuery (language : LanguageDef) (types terms equationRows : Term)
    (contexts premises : RewriteRule → Term) (subject : PatternPlan) : Atom :=
  a "gslt:automata:language-bottom"
    [encoded (matchingProjectionTerm language types terms equationRows contexts premises), patternValue subject]

theorem language_top_completed_iff (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (languageTopQuery language types terms equationRows contexts premises subject) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_top_returns state language types terms equationRows contexts premises patterns subject admitted)
    after answers input output

theorem language_bottom_completed_iff (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (after : State) (answers input output : List Atom) :
    (∃ fuel, run program fuel
      { state, control := .evaluate [] (languageBottomQuery language types terms equationRows contexts premises subject) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (bottomRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _
    (language_bottom_returns state language types terms equationRows contexts premises patterns subject admitted)
    after answers input output

theorem language_top_derivation_iff (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (languageTopQuery language types terms equationRows contexts premises subject) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (topRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_top_returns state language types terms equationRows contexts premises patterns subject admitted)
    after answers input output

theorem language_bottom_derivation_iff (state : State) (language : LanguageDef)
    (types terms equationRows : Term) (contexts premises : RewriteRule → Term)
    (patterns : List PatternPlan) (subject : PatternPlan)
    (admitted : erasePatterns patterns = MeTTaILSubtermMatchAutomata.languagePatterns language)
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs program
      { state, control := .evaluate [] (languageBottomQuery language types terms equationRows contexts premises subject) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (bottomRunTerm patterns subject)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff program [] state state _ _
    (language_bottom_returns state language types terms equationRows contexts premises patterns subject admitted)
    after answers input output

section Controls

private def paired : PatternPlan :=
  .application "Pair" [.metavariable "x", .metavariable "x"]

private def agreeing : PatternPlan :=
  .application "Pair" [.application "Value" [], .application "Value" []]

private def conflicting : PatternPlan :=
  .application "Pair" [.application "Value" [], .application "Other" []]

private def duplicateResults : List MeTTaILSubtermMatchAutomata.BoundMatch :=
  [⟨⟨[], 0⟩, [("x", .apply "Value" [])]⟩, ⟨⟨[], 1⟩, [("x", .apply "Value" [])]⟩]

/-- Interning structural controls retains duplicate authored rule occurrences. -/
theorem duplicate_occurrences_retained (state : State) :
    PureReturns program [] state (topQuery [paired, paired] agreeing) state
      (encoded (matchRunTerm duplicateResults 3 16)) ∧
    PureReturns program [] state (bottomQuery [paired, paired] agreeing) state
      (encoded (matchRunTerm duplicateResults 3 6)) := by
  have topExact : topRunTerm [paired, paired] agreeing = matchRunTerm duplicateResults 3 16 := by
    unfold topRunTerm
    congr 1 <;>
      simp only [topObservations, topExecuted, topSeeds, structuralPatterns, paired, agreeing,
        MatchAutomataInventoryExecution.patternView_application,
        MatchAutomataInventoryExecution.patternView_metavariable,
        MatchAutomataInventoryExecution.subjectView_application, List.map_cons, List.map_nil] <;>
      decide +kernel
  have bottomExact : bottomRunTerm [paired, paired] agreeing = matchRunTerm duplicateResults 3 6 := by
    unfold bottomRunTerm
    dsimp only
    congr 1 <;>
      simp only [bottomInventory, structuralPatterns, paired, agreeing,
        MatchAutomataInventoryExecution.patternView_application,
        MatchAutomataInventoryExecution.patternView_metavariable,
        MatchAutomataInventoryExecution.subjectView_application, List.map_cons, List.map_nil] <;>
      decide +kernel
  constructor
  · simpa only [topQuery, topExact] using top_returns state [paired, paired] agreeing
  · simpa only [bottomQuery, bottomExact] using bottom_returns state [paired, paired] agreeing

/-- A structural wildcard candidate cannot bypass repeated-binding agreement. -/
theorem repeated_binding_conflict_refused (state : State) :
    PureReturns program [] state (topQuery [paired, paired] conflicting) state
      (encoded (matchRunTerm [] 3 16)) ∧
    PureReturns program [] state (bottomQuery [paired, paired] conflicting) state
      (encoded (matchRunTerm [] 3 6)) := by
  have topExact : topRunTerm [paired, paired] conflicting = matchRunTerm [] 3 16 := by
    unfold topRunTerm
    congr 1 <;>
      simp only [topObservations, topExecuted, topSeeds, structuralPatterns, paired, conflicting,
        MatchAutomataInventoryExecution.patternView_application,
        MatchAutomataInventoryExecution.patternView_metavariable,
        MatchAutomataInventoryExecution.subjectView_application, List.map_cons, List.map_nil] <;>
      decide +kernel
  have bottomExact : bottomRunTerm [paired, paired] conflicting = matchRunTerm [] 3 6 := by
    unfold bottomRunTerm
    dsimp only
    congr 1 <;>
      simp only [bottomInventory, structuralPatterns, paired, conflicting,
        MatchAutomataInventoryExecution.patternView_application,
        MatchAutomataInventoryExecution.patternView_metavariable,
        MatchAutomataInventoryExecution.subjectView_application, List.map_cons, List.map_nil] <;>
      decide +kernel
  constructor
  · simpa only [topQuery, topExact] using top_returns state [paired, paired] conflicting
  · simpa only [bottomQuery, bottomExact] using bottom_returns state [paired, paired] conflicting

end Controls

#print axioms top_returns
#print axioms bottom_returns
#print axioms top_derivation_iff
#print axioms bottom_derivation_iff
#print axioms language_patterns_returns
#print axioms language_top_returns
#print axioms language_bottom_returns
#print axioms language_top_completed_iff
#print axioms language_bottom_completed_iff
#print axioms language_top_derivation_iff
#print axioms language_bottom_derivation_iff
#print axioms duplicate_occurrences_retained
#print axioms repeated_binding_conflict_refused

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.MatchAutomataExecution
