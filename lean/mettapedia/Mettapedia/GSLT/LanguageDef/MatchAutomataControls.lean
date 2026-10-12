import Mettapedia.GSLT.LanguageDef.MeTTaILMatchAutomataExecution
import Mettapedia.GSLT.LanguageDef.CettaWireEquality

/-!
# Subterm-automaton controls

The same authored patterns and subjects are exported to the MeTTa controls.
These examples check occurrence multiplicity, positions, binding consistency,
arity refusal, literal bound indices, and the empty family.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchAutomataControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open MeTTaILFirstOrderRuleCompilation
open MeTTaILSubtermMatchAutomata

def atom (name : String) : PatternPlan := .application name []
def app (name : String) (children : List PatternPlan) : PatternPlan := .application name children
def pat (name : String) (children : List Pattern) : Pattern := .apply name children

structure Control where
  name : String
  patterns : List Pattern
  subject : PatternPlan

def repeated : Pattern := pat "pair" [.fvar "x", .fvar "x"]
def overlapA : Pattern := pat "f" [pat "g" [.fvar "x"], pat "a" []]
def overlapB : Pattern := pat "f" [pat "g" [.fvar "y"], pat "b" []]

def controls : List Control :=
  [⟨"overlap-a", [overlapA, overlapB], app "f" [app "g" [atom "z"], atom "a"]⟩,
   ⟨"overlap-b", [overlapA, overlapB], app "f" [app "g" [atom "z"], atom "b"]⟩,
   ⟨"overlap-refused", [overlapA, overlapB], app "f" [app "g" [atom "z"], atom "c"]⟩,
   ⟨"duplicate-rows", [overlapA, overlapA], app "f" [app "g" [atom "z"], atom "a"]⟩,
   ⟨"wildcard", [.fvar "whole"], app "wrap" [atom "a", atom "b"]⟩,
   ⟨"nested", [pat "g" [.fvar "x"]], app "wrap" [app "g" [app "g" [atom "a"]]]⟩,
   ⟨"repeated-equal", [repeated], app "pair" [atom "a", atom "a"]⟩,
   ⟨"repeated-unequal", [repeated], app "pair" [atom "a", atom "b"]⟩,
   ⟨"repeated-deep-equal", [repeated], app "pair" [app "g" [atom "a"], app "g" [atom "a"]]⟩,
   ⟨"repeated-deep-unequal", [repeated], app "pair" [app "g" [atom "a"], app "g" [atom "b"]]⟩,
   ⟨"arity-refused", [repeated], app "pair" [atom "a"]⟩,
   ⟨"constructor-refused", [repeated], app "other" [atom "a", atom "a"]⟩,
   ⟨"literal-nullary", [pat "a" []], app "wrap" [atom "a", app "a" [atom "z"]]⟩,
   ⟨"bound-index", [.bvar 3], app "wrap" [.bound 3, .bound 4]⟩,
   ⟨"free-subject", [.fvar "capture"], .metavariable "subject"⟩,
   ⟨"literal-versus-free", [pat "a" []], .metavariable "a"⟩,
   ⟨"empty-family", [], app "wrap" [atom "a"]⟩,
   ⟨"mixed-binding-order", [pat "tri" [.fvar "x", .fvar "y", .fvar "z"]],
      app "tri" [atom "a", atom "b", atom "c"]⟩,
   ⟨"mixed-family", [overlapA, overlapB, overlapA, .fvar "all", repeated, .bvar 3],
      app "wrap" [app "f" [app "g" [atom "z"], atom "a"],
        app "f" [app "g" [atom "z"], atom "b"], app "pair" [atom "a", atom "b"], .bound 3]⟩]

theorem repeated_equal :
    bottomUp [repeated] (app "pair" [atom "a", atom "a"]) =
      [⟨⟨[], 0⟩, [("x", .apply "a" [])]⟩] := by
  rw [bottomUp_eq_reference]
  decide +kernel

theorem repeated_unequal :
    bottomUp [repeated] (app "pair" [atom "a", atom "b"]) = [] := by
  rw [bottomUp_eq_reference]
  decide +kernel

theorem duplicate_rows :
    (bottomUp [overlapA, overlapA] (app "f" [app "g" [atom "z"], atom "a"])).map
      (fun match_ => match_.location.occurrence) = [0, 1] := by
  rw [bottomUp_eq_reference]
  decide +kernel

theorem nested_positions :
    (topDown [pat "g" [.fvar "x"]] (app "wrap" [app "g" [app "g" [atom "a"]]])).map
      (fun match_ => match_.location.position) = [[0], [0, 0]] := by
  rw [topDown_eq_reference]
  decide +kernel

theorem all_controls_exact : ∀ control ∈ controls,
    bottomUp control.patterns control.subject = reference control.patterns control.subject ∧
      topDown control.patterns control.subject = reference control.patterns control.subject := by
  intro control _
  exact ⟨bottomUp_eq_reference _ _, topDown_eq_reference _ _⟩

def bottomCounts (control : Control) : Nat × Nat :=
  let shapes := control.patterns.map View.lowerPattern
  let view := View.lowerSubject control.subject.erase
  let reads := BottomUpMatchAutomaton.inspections
    (BottomUpMatchAutomaton.analyze (BottomUpMatchAutomaton.inventory shapes) view)
  (reads, reads * (BottomUpMatchAutomaton.inventory shapes).length)

def topCounts (control : Control) : Nat × Nat :=
  let shapes := control.patterns.map View.lowerPattern
  let view := View.lowerSubject control.subject.erase
  let observations := TopDownMatchDerivatives.observe view
  let programs := shapes.map TopDownMatchDerivatives.compile
  let goals := observations.flatMap (fun o => TopDownMatchDerivatives.seed o.position 0 programs)
  (observations.length, (TopDownMatchDerivatives.executeCounted observations goals).2)

#print axioms repeated_equal
#print axioms repeated_unequal
#print axioms duplicate_rows
#print axioms nested_positions

namespace Execution

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open MeTTaILMatchAutomataExecution

def rule (name : String) (left right : Pattern) (premises : List Premise := []) : RewriteRule :=
  { name, typeContext := [], premises, left, right }

def language (rules : List RewriteRule) : LanguageDef :=
  { name := "MatchAutomataExecutionControl", types := [], terms := [], equations := [], rewrites := rules }

def replaceA : RewriteRule := rule "replace-a" (pat "a" []) (pat "b" [])

theorem duplicate_reducts (strategy : Strategy) :
    runAt strategy (engineBasePremises RelationEnv.empty) (language [replaceA, replaceA]) 1 (atom "a") =
      [pat "b" [], pat "b" []] := by
  rw [runAt_exact]
  decide +kernel

/-- A successful non-root match grants no implicit reduction of its parent. -/
theorem no_implicit_child_rewrite (strategy : Strategy) :
    runAt strategy (engineBasePremises RelationEnv.empty) (language [replaceA]) 1
      (app "wrap" [atom "a"]) = [] := by
  rw [runAt_exact]
  decide +kernel

def guarded : RewriteRule :=
  rule "guarded" (pat "a" []) (pat "b" []) [.relationQuery "permit" []]

theorem missing_guard_refuses (strategy : Strategy) :
    runAt strategy (engineBasePremises RelationEnv.empty) (language [guarded]) 1 (atom "a") = [] := by
  rw [runAt_exact]
  decide +kernel

def permissions : RelationEnv := { tuples := fun name _ => if name = "permit" then [[], []] else [] }

/-- Two premise witnesses remain two results, even for the same reduct. -/
theorem guard_multiplicity (strategy : Strategy) :
    runAt strategy (engineBasePremises permissions) (language [guarded]) 1 (atom "a") =
      [pat "b" [], pat "b" []] := by
  rw [runAt_exact]
  decide +kernel

def wrapContext : RewriteRule :=
  rule "wrap-context" (pat "wrap" [.fvar "x"]) (pat "wrap" [.fvar "y"])
    [.congruence (.fvar "x") (.fvar "y")]

theorem authorized_child_rewrite (strategy : Strategy) :
    runAt strategy (engineBasePremises RelationEnv.empty) (language [replaceA, wrapContext]) 2
      (app "wrap" [atom "a"]) = [pat "wrap" [pat "b" []]] := by
  rw [runAt_exact]
  decide +kernel

theorem insufficient_context_depth (strategy : Strategy) :
    runAt strategy (engineBasePremises RelationEnv.empty) (language [replaceA, wrapContext]) 1
      (app "wrap" [atom "a"]) = [] := by
  rw [runAt_exact]
  decide +kernel

#print axioms duplicate_reducts
#print axioms no_implicit_child_rewrite
#print axioms missing_guard_refuses
#print axioms guard_multiplicity
#print axioms authorized_child_rewrite
#print axioms insufficient_context_depth

end Execution

namespace Derivative

open CettaWire TopDownMatchDerivatives

def observation (position : SubtermMatching.Position) (head : String) (arity : Nat) : Observation Term :=
  ⟨position, ⟨.symbol head, arity⟩⟩

def candidate (position : SubtermMatching.Position) (occurrence : Nat) (pending : List (Obligation Term)) : Goal Term :=
  ⟨⟨position, occurrence⟩, pending⟩

structure StreamControl where
  name : String
  observations : List (Observation Term)
  goals : List (Goal Term)
  dispatches : Nat := 0

def streamControls : List StreamControl :=
  let root := observation [] "f" 2
  let child := observation [0] "g" 1
  let other := observation [1] "a" 0
  let executableHead : Observation Term :=
    ⟨[], ⟨.application "gslt:automata:length" [.symbol "LNil"], 0⟩⟩
  [⟨"stream-empty", [], [candidate [] 0 [root]], 0⟩,
   ⟨"stream-consume", [root], [candidate [] 0 [root]], 0⟩,
   ⟨"stream-retain", [root], [candidate [0] 0 [child]], 0⟩,
   ⟨"stream-conflict", [root], [candidate [] 0 [observation [] "f" 1]], 0⟩,
   ⟨"stream-duplicate-obligation", [root], [candidate [] 0 [root, root]], 0⟩,
   ⟨"stream-duplicate-goals", [root],
     [candidate [] 0 [root], candidate [] 1 [root], candidate [] 2 [observation [] "wrong" 2]], 0⟩,
   ⟨"stream-permuted-positions", [other, child, root],
     [candidate [0] 4 [child], candidate [1] 2 [other], candidate [] 7 [root, child, other]], 0⟩,
   ⟨"stream-earlier-refusal", [observation [] "wrong" 2, root], [candidate [] 0 [root]], 0⟩,
   ⟨"stream-first-observation", [root, observation [] "wrong" 2], [candidate [] 0 [root]], 0⟩,
   ⟨"stream-counter-offset", [root, child], [candidate [] 0 [root, child], candidate [0] 1 [child]], 19⟩,
   ⟨"stream-interpreted-head-data", [executableHead], [candidate [] 0 [executableHead]], 0⟩]

theorem missing_observation_refuses :
    completed (execute [] [candidate [] 0 [observation [] "f" 2]]) = [] := by decide +kernel

theorem conflicting_observation_refuses :
    completed (execute [observation [] "f" 1] [candidate [] 0 [observation [] "f" 2]]) = [] := by decide +kernel

theorem duplicate_goal_occurrences :
    completed (execute [observation [] "f" 2]
      [candidate [] 0 [observation [] "f" 2], candidate [] 1 [observation [] "f" 2]]) =
      [⟨[], 0⟩, ⟨[], 1⟩] := by decide +kernel

theorem dispatch_counter :
    (executeCounted [observation [] "f" 2, observation [0] "g" 1]
      [candidate [] 0 [observation [] "f" 2], candidate [0] 1 [observation [0] "g" 1]]).2 = 4 := by
  decide +kernel

#print axioms missing_observation_refuses
#print axioms conflicting_observation_refuses
#print axioms duplicate_goal_occurrences
#print axioms dispatch_counter

end Derivative

end Mettapedia.GSLT.LanguageDef.MatchAutomataControls
