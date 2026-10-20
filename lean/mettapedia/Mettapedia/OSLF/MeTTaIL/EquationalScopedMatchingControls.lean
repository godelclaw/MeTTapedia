import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatchingControls

/-! Nested collections, vector order and binding-policy separation controls. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching.Controls

open Syntax ScopedRuleMatching CanonicalBags
open ScopedCollectionMatching.Controls (a b spec)

def x : Pattern := .fvar "X"
def y : Pattern := .fvar "Y"
def set (items : List Pattern) (rest : Option String := none) : Pattern := .collection .hashSet items rest
def bag (items : List Pattern) (rest : Option String := none) : Pattern := .collection .hashBag items rest
def vector (items : List Pattern) : Pattern := .collection .vec items none

def authored (schema : Pattern) : RewriteRule :=
  { name := "recursive-collection-control", typeContext := [("X", .base "Item"), ("Y", .base "Item"),
      ("R", .base "Items")], premises := [], left := schema, right := x }

def evaluate (schema target : Pattern) (comparison : Comparison := literalBodyComparison)
    (bindings : RuleBindingSpec := spec) : List Assignment :=
  runAt comparison (authored schema) bindings 0 .left [] 0 [] schema target

def boundSpec : RuleBindingSpec :=
  { dependencies := [("X", [.base "Item"]), ("Y", [.base "Item"])]
    occurrences :=
      [⟨"X", .left, [0, 0], [.bvar 0]⟩, ⟨"Y", .left, [0, 1], [.bvar 0]⟩] }

def controls : List (String × Bool) :=
  let nested := .apply "Packet" [set [x, y]]
  let nestedTarget := .apply "Packet" [set [a]]
  let setInsideBag := bag [set [x, y], b]
  let repeated := vector [x, x]
  let differentlyPresented := vector [bag [a, b], bag [b, a]]
  [ ("nested-set-reuses-member", (evaluate nested nestedTarget).length == 1)
  , ("set-inside-bag", (evaluate setInsideBag (bag [b, set [a]])).length == 1)
  , ("bag-inside-set-keeps-multiplicity", !(evaluate (set [bag [x, x]]) (set [bag [a, a]])).isEmpty)
  , ("bag-inside-set-cannot-invent-occurrence", (evaluate (set [bag [x, x]]) (set [bag [a]])).isEmpty)
  , ("set-duplicate-presentation-agrees",
      evaluate nested nestedTarget == evaluate nested (.apply "Packet" [set [a, a]]))
  , ("vector-order-preserved", (evaluate (vector [a, b]) (vector [b, a])).isEmpty)
  , ("nested-rest-overlap-retained", (evaluate (.apply "Packet" [set [x, y] (some "R")]) nestedTarget).length == 2)
  , ("different-constructor-refused", (evaluate nested (.apply "Other" [set [a]])).isEmpty)
  , ("literal-repeat-policy-remains-literal", (evaluate repeated differentlyPresented).isEmpty)
  , ("declared-canonical-repeat-policy", (evaluate repeated differentlyPresented canonCompare).length == 1)
  , ("binder-closed-capture", (evaluate (.lambda none (set [x, y])) (.lambda none (set [a]))).length == 1)
  , ("binder-local-capture-needs-declaration",
      (evaluate (.lambda none (set [x, y])) (.lambda none (set [.bvar 0]))).isEmpty)
  , ("binder-local-capture-with-authored-spines",
      (evaluate (.lambda none (set [x, y])) (.lambda none (set [.bvar 0]))
        literalBodyComparison boundSpec).length == 1)
  , ("wrong-binder-spine-refused",
      (evaluate (.lambda none (set [x, y])) (.lambda none (set [.bvar 0]))
        literalBodyComparison { boundSpec with occurrences :=
          [⟨"X", .left, [0, 0], [.bvar 1]⟩, ⟨"Y", .left, [0, 1], [.bvar 0]⟩] }).isEmpty) ]

def checkControls : IO Unit := do
  for (name, passed) in controls do
    if !passed then throw (IO.userError s!"Recursive collection control failed: {name}")
  IO.println s!"EquationalScopedMatchingControls: {controls.length}/{controls.length}"

#eval checkControls

end Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching.Controls
