import Mettapedia.OSLF.MeTTaIL.Comparisons.EnumeratingPremiseReplay
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchReplay

/-!
# A regression witness for enumerate-then-filter replay

A seven-element bag has 5,040 positional matching branches. All-equal target
values give one distinct assignment, yet enumeration still constructs those
branches before selecting one guidance stream. Direct replay follows that
stream alone. The counts are controls for these concrete inputs, not a
physical-time complexity theorem.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.EnumeratingReplay.Controls
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open ScopedRuleMatching GeneralScopedMatchMachine

def schema (count : Nat) : Pattern :=
  .collection .hashBag ((List.range count).map fun index => .fvar s!"x{index}") none

def target (count : Nat) (duplicates : Bool) : Pattern :=
  .collection .hashBag ((List.range count).map fun index =>
    .apply (if duplicates then "c" else s!"c{index}") []) none

def request (count : Nat) (duplicates : Bool) : Request where
  rule :=
    { name := "bag-choices"
      typeContext := []
      premises := []
      left := schema count
      right := schema count }
  spec := {dependencies := (List.range count).map fun index => (s!"x{index}", [])}
  ambient := 0
  site := .left
  path := []
  depth := 0
  initial := []
  schema := schema count
  target := target count duplicates

def compare (count expected : Nat) (duplicates : Bool) : List (String × Bool) :=
  let input := request count duplicates
  let fuel := matchFuel input
  let answers := (run input fuel (start input)).answers
  match answers.head? with
  | none => [("enumerating comparison construction", false)]
  | some first => [
      (s!"bag {count} positional branch count", decide (answers.length = expected)),
      (s!"bag {count} selected old trace keeps one", decide ((matchAnswers fuel input first.trace).length = 1)),
      (s!"bag {count} direct replay agrees", decide
        (GeneralScopedMatchReplay.replay input first.trace = some first.assignment)),
      (s!"bag {count} duplicate assignments counted honestly",
        if duplicates then decide ((answers.map (·.assignment)).eraseDups.length = 1) else true)]

def checks : List (String × Bool) := compare 3 6 false ++ compare 7 5040 false ++ compare 7 5040 true

#guard checks.all Prod.snd

def main : IO Unit := do
  for (label, passed) in checks do
    unless passed do throw (IO.userError label)
  IO.println s!"{checks.length}/{checks.length} enumerating replay comparison controls passed"

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.EnumeratingReplay.Controls
