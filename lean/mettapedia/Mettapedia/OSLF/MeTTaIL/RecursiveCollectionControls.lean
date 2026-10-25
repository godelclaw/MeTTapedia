import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionAccounting
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatchingControls

/-! Nonvacuous retained-matcher controls with explicit expected answer counts. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine.Controls

open Syntax RuleBinding ScopedRuleMatching
open EquationalScopedMatching.Controls
open ScopedCollectionMatching.Controls (a b spec)

structure Case where
  label : String
  request : Request
  expectedCount : Nat

def specimen (label : String) (schema target : Pattern) (binding : RuleBindingSpec)
    (expectedCount : Nat) : Case :=
  ⟨label, ⟨authored schema, binding, 0, .left, [], 0, [], schema, target⟩, expectedCount⟩

def cases : List Case :=
  [specimen "nested-set" (.apply "Packet" [set [x,y]]) (.apply "Packet" [set [a]]) spec 1,
   specimen "set-inside-bag" (bag [set [x,y],b]) (bag [b,set [a]]) spec 1,
   specimen "equal-bag-occurrences" (bag [x] (some "R")) (bag [a,a]) spec 2,
   specimen "nested-rest" (.apply "Packet" [set [x,y] (some "R")]) (.apply "Packet" [set [a]]) spec 2,
   specimen "missing-bag-occurrence" (set [bag [x,x]]) (set [bag [a]]) spec 0,
   specimen "bound-captures" (.lambda none (set [x,y])) (.lambda none (set [.bvar 0])) boundSpec 1,
   specimen "undeclared-bound-capture" (.lambda none (set [x,y])) (.lambda none (set [.bvar 0])) spec 0,
   specimen "vector-rest" (.collection .vec [x] (some "R")) (.collection .vec [a,b] none) spec 1,
   specimen "open-tail-target" (set [x]) (set [a] (some "R")) spec 0,
   specimen "wrong-collection-kind" (set [x]) (vector [a]) spec 0,
   specimen "wrong-constructor" (.apply "Packet" [set [x]]) (.apply "Other" [set [a]]) spec 0]

def finished (specimen : Case) : State := run specimen.request 100 (start specimen.request)

def equalBag : Case := specimen "equal-bag-occurrences" (bag [x] (some "R")) (bag [a,a]) spec 2

#guard (finished equalBag).answers.length = 2
#guard ((finished equalBag).answers.map (·.assignment)).eraseDups.length = 1
#guard ((finished equalBag).answers.map (·.trace)).eraseDups.length = 2

def checkControls : IO Unit := do
  for specimen in cases do
    let completed := finished specimen
    unless complete completed && completed.answers.length == specimen.expectedCount do
      throw (IO.userError s!"Recursive collection count failed: {specimen.label}")
    unless ((run specimen.request 3 (start specimen.request)).answers).length ≤ specimen.expectedCount do
      throw (IO.userError s!"Early publication exceeds final count: {specimen.label}")
  IO.println s!"RecursiveCollectionControls: {cases.length}/{cases.length}"

#eval checkControls

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionMachine.Controls
