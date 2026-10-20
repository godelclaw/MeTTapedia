import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching

/-! Executable controls for collection equality with actual authored captures. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching.Controls

open Syntax RuleBinding ScopedRuleMatching

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []

def rule (kind : CollType) (schemas : List Pattern) (rest : Option String) : RewriteRule :=
  { name := "collection-control"
    typeContext := [("X", .base "Item"), ("Y", .base "Item"), ("R", .base "Items")]
    premises := []
    left := .collection kind schemas rest
    right := .fvar "X" }

def spec : RuleBindingSpec := ⟨[("X", []), ("Y", []), ("R", [])], []⟩

def evaluate (kind : CollType) (schemas : List Pattern) (rest : Option String)
    (targets : List Pattern) (initial : Assignment := []) : List Assignment :=
  run (rule kind schemas rest) spec 0 .left [] 0 0 initial schemas rest kind targets

def value (assignment : Assignment) (name : String) : Option Pattern :=
  (lookup assignment name).map (·.body)

def readings (assignments : List Assignment) : List (Option Pattern × Option Pattern × Option Pattern) :=
  assignments.map fun assignment => (value assignment "X", value assignment "Y", value assignment "R")

def twoVariables : List Pattern := [.fvar "X", .fvar "Y"]
def repeatedVariable : List Pattern := [.fvar "X", .fvar "X"]

def controls : List (String × Bool) :=
  [ ("set-reuses-single-member",
      readings (evaluate .hashSet twoVariables (some "R") [a]) ==
        [(some a, some a, some (.collection .hashSet [] none)),
         (some a, some a, some (.collection .hashSet [a] none))])
  , ("bag-cannot-reuse-single-occurrence",
      (evaluate .hashBag twoVariables (some "R") [a]).isEmpty)
  , ("bag-equal-values-retain-two-origins",
      readings (evaluate .hashBag twoVariables (some "R") [a, a]) ==
        [(some a, some a, some (.collection .hashBag [] none)),
         (some a, some a, some (.collection .hashBag [] none))])
  , ("set-repeated-variable-consistent",
      readings (evaluate .hashSet repeatedVariable none [a]) == [(some a, none, none)])
  , ("set-repeated-variable-cannot-cover-different-members",
      (evaluate .hashSet repeatedVariable none [a, b]).isEmpty)
  , ("bag-repeated-variable-cannot-use-unequal-values",
      (evaluate .hashBag repeatedVariable none [a, b]).isEmpty)
  , ("set-prior-conflicting-assignment-refused",
      (evaluate .hashSet [.fvar "X"] none [a] [("X", ⟨[], 0, b⟩)]).isEmpty)
  , ("set-prior-conflicting-context-refused",
      (evaluate .hashSet [.fvar "X"] none [a] [("X", ⟨[], 1, a⟩)]).isEmpty)
  , ("wrong-schema-path-refused",
      (run (rule .hashSet twoVariables (some "R")) spec 0 .left [9] 0 0 []
        twoVariables (some "R") .hashSet [a]).isEmpty)
  , ("missing-dependency-declaration-refused",
      (run (rule .hashSet twoVariables (some "R")) ⟨[("X", []), ("R", [])], []⟩
        0 .left [] 0 0 [] twoVariables (some "R") .hashSet [a]).isEmpty)
  , ("old-consumptive-matcher-misses-set-reuse",
      (matchRuleAt (rule .hashSet twoVariables (some "R")) spec 0
        (.collection .hashSet [a] none)).isEmpty)
  , ("empty-collection-matches-empty-schema",
      evaluate .hashSet [] none [] == [[]])
  , ("empty-schema-cannot-discard-unmatched-member",
      (evaluate .hashSet [] none [a]).isEmpty) ]

def checkControls : IO Unit := do
  for (name, passed) in controls do
    if !passed then throw (IO.userError s!"Collection scope control failed: {name}")
  IO.println s!"ScopedCollectionControls: {controls.length}/{controls.length}"

#eval checkControls

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching.Controls
