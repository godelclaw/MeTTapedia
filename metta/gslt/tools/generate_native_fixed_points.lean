import Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.NaturalCounterExecution
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter

/-!
Emit existing modal fixed-point formulas and explicit finite graphs. Expected
answers come from the certified Lean strategy; MeTTa independently computes
the nested fixed points from the graph, formula and observation environment.
-/

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes

namespace NativeFixedPointGenerator

structure Example where
  name : String
  cardinal : Nat
  edges : List (Nat × Nat × Nat)
  accepting : List Nat

def Example.lts (fixture : Example) : LTS (Fin fixture.cardinal) Nat where
  trans source action target := (source.val, action, target.val) ∈ fixture.edges

def Example.model (fixture : Example) : Model fixture.lts where
  successors source action := Finset.univ.filter fun target =>
    (source.val, action, target.val) ∈ fixture.edges
  successors_exact source action target := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

def Example.environment (fixture : Example) : Environment (Fin fixture.cardinal) 1 :=
  fun _ => Finset.univ.filter fun state => state.val ∈ fixture.accepting

def Example.universe (fixture : Example) : Term :=
  encodeList Term.natural (List.range fixture.cardinal)

def Example.edgeTerm (fixture : Example) : Term :=
  encodeList (fun edge => Term.application "NativeEdge"
    [.natural edge.1, .natural edge.2.1, .natural edge.2.2]) fixture.edges

def Example.environmentTerm (fixture : Example) : Term :=
  encodeList id [encodeList Term.natural
    ((List.finRange fixture.cardinal).filter
      (fun state => state ∈ fixture.environment 0) |>.map Fin.val)]

def buchi : Formula Nat 1 :=
  .nu (.mu (.disj (.conj (.var 2) (.diamond 0 (.var 1))) (.diamond 0 (.var 0))))
def reach : Formula Nat 1 := .mu (.disj (.var 1) (.diamond 0 (.var 0)))
def infinite : Formula Nat 1 := .nu (.diamond 0 (.var 0))

/-- The same complete parity table used by the proved source-counter adapter. -/
def naturalCounter (accepting : List Nat) : Example :=
  ⟨if accepting.isEmpty then "natural-counter.empty-acceptance" else "natural-counter.even-recurrence",
    2, Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter.edges.map
      (fun edge => (edge.1.val, 0, edge.2.val)), accepting⟩

theorem naturalCounter_edges_exact (accepting : List Nat) (source target : Fin 2) :
    (naturalCounter accepting).lts.trans source 0 target ↔
      Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter.table.edge source target = true := by
  change (source.val, 0, target.val) ∈
    Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter.edges.map
      (fun edge => (edge.1.val, 0, edge.2.val)) ↔ _
  revert source target
  decide +kernel

def examples : List Example :=
  [⟨"accepting-self-loop", 1, [(0,0,0)], [0]⟩,
   ⟨"accepting-dead-end", 1, [], [0]⟩,
   ⟨"cycle-with-no-acceptance", 1, [(0,0,0)], []⟩,
   ⟨"acceptance-only-once", 2, [(0,0,1),(1,0,1)], [0]⟩,
   ⟨"two-state-cycle", 3, [(0,0,1),(1,0,0)], [1]⟩,
   ⟨"tail-to-accepting-cycle", 4, [(0,0,1),(1,0,2),(2,0,1),(3,0,3)], [2]⟩,
   ⟨"nondeterministic-good-and-bad", 4, [(0,0,1),(0,0,2),(1,0,1),(2,0,2)], [1]⟩,
   ⟨"other-action-cycle", 2, [(0,1,1),(1,1,1)], [1]⟩,
   ⟨"duplicate-edges", 2, [(0,0,1),(0,0,1),(1,0,1)], [1]⟩]

def control (name expression expected : String) : String :=
  s!"!(let $actual {expression} (NativeFixedPointControl {reprStr name} " ++
    s!"(if (== $actual {expected}) NativePass NativeFail)))\n"

def query (fixture : Example) (name : String) (formula : Formula Nat 1)
    (budget : Nat) (state : Fin fixture.cardinal) : String :=
  let expression := s!"(native:mu:check {(formulaTerm Term.natural formula).render} " ++
    s!"{fixture.universe.render} {fixture.edgeTerm.render} {fixture.environmentTerm.render} {budget} {state.val})"
  control s!"{fixture.name}.{name}.state-{state.val}" expression
    (NaturalCounterExecution.verdict (check? fixture.model formula fixture.environment budget state))

/-- Use the exact query whose complete PeTTa execution is certified. The
expected verdict still comes from the independent public finite checker. -/
def naturalQuery (accepting : List Nat) (name : String) (budget : Nat) (state : Fin 2) : String :=
  let fixture := naturalCounter accepting
  let phases := fixture.environment 0
  control s!"{fixture.name}.{name}.state-{state.val}"
    (NaturalCounterExecution.queryTerm phases budget state).render
    (NaturalCounterExecution.verdict
      (Mettapedia.OSLF.NativeTypes.Executable.Finite.check
        Mettapedia.OSLF.NativeTypes.Instances.Natural.Counter.table
        (Mettapedia.Logic.ModalMuCalculus.Formula.buchi .future)
        (fun _ => phases) budget state))

def allStates (fixture : Example) (name : String) (formula : Formula Nat 1) : String :=
  String.join ((List.finRange fixture.cardinal).map fun state =>
    query fixture name formula (requiredBudget (State := Fin fixture.cardinal) formula) state)

def setControl (fixture : Example) (name : String) (formula : Formula Nat 1) : String :=
  let expected := encodeList Term.natural
    ((List.finRange fixture.cardinal).filter
      (fun state => state ∈ evaluate fixture.model formula fixture.environment) |>.map Fin.val)
  control s!"{fixture.name}.{name}.whole-set"
    (s!"(native:mu:evaluate {(formulaTerm Term.natural formula).render} {fixture.universe.render} " ++
      s!"{fixture.edgeTerm.render} {fixture.environmentTerm.render} {fixture.cardinal})") expected.render

def generate : String := Id.run do
  let mut result := "; Independent target iteration; expected checks are generated by Lean.\n"
  for fixture in examples do
    result := result ++ allStates fixture "buchi" buchi
    result := result ++ setControl fixture "buchi" buchi
  for accepting in [[0], []] do
    let fixture := naturalCounter accepting
    for state in List.finRange 2 do
      result := result ++ naturalQuery accepting "buchi" NaturalCounterExecution.queryBudget state
    result := result ++ setControl fixture "buchi" buchi
  for state in List.finRange 2 do
    result := result ++ naturalQuery [0] "zero-budget" 0 state
  let fixture : Example := ⟨"operators", 4, [(0,0,1),(1,0,0),(2,0,3),(0,1,3)], [1]⟩
  let formulas : List (String × Formula Nat 1) :=
    [("reach",reach),("infinite",infinite),("finite-path",.neg infinite),
     ("box-bottom",.box 0 .ff),("diamond-top",.diamond 0 .tt),
     ("other-action-diamond",.diamond 1 .tt), ("other-action-box",.box 1 .ff),
     ("excluded-middle",.disj (.var 0) (.neg (.var 0))),
     ("contradiction",.conj (.var 0) (.neg (.var 0))),
     ("least-identity",.mu (.var 0)),("greatest-identity",.nu (.var 0)),
     ("double-negative",.mu (.neg (.neg (.var 0)))),
     ("negative-least-refused",.mu (.neg (.var 0))),
     ("negative-greatest-refused",.nu (.neg (.var 0))),
     ("inner-negative-refused",.nu (.mu (.neg (.var 0)))),
     ("outer-negative-under-binder-refused",.nu (.mu (.neg (.var 1))))]
  for (name, formula) in formulas do
    result := result ++ allStates fixture name formula
  let enough := requiredBudget (State := Fin fixture.cardinal) buchi
  result := result ++ query fixture "zero-budget" buchi 0 0
  result := result ++ query fixture "short-budget" buchi (enough-1) 0
  result := result ++ query fixture "extra-budget" buchi (enough+1) 0
  result := result ++ control "scope.out-of-range-variable"
    "(native:mu:check (NativeVar 1) (LCons 0 LNil) LNil (LCons LNil LNil) 10 0)" "NativeRejected"
  result := result ++ control "scope.fractional-variable"
    "(native:mu:check (NativeVar 0.5) (LCons 0 LNil) LNil (LCons LNil LNil) 10 0)" "NativeRejected"
  result := result ++ control "scope.negative-variable"
    "(native:mu:check (NativeVar -1) (LCons 0 LNil) LNil LNil 10 0)" "NativeRejected"
  result := result ++ control "graph.missing-edge-target"
    "(native:mu:check NativeTop (LCons 0 LNil) (LCons (NativeEdge 0 0 1) LNil) LNil 10 0)" "NativeRejected"
  result := result ++ control "graph.duplicate-carrier"
    "(native:mu:check NativeTop (LCons 0 (LCons 0 LNil)) LNil LNil 10 0)" "NativeRejected"
  result := result ++ control "graph.source-outside-carrier"
    "(native:mu:check NativeTop (LCons 0 LNil) LNil LNil 10 1)" "NativeRejected"
  result := result ++ control "environment.outside-carrier"
    "(native:mu:check (NativeVar 0) (LCons 0 LNil) LNil (LCons (LCons 1 LNil) LNil) 10 0)" "NativeRejected"
  result := result ++ control "empty-carrier.greatest-top"
    "(native:mu:evaluate (NativeNu NativeTop) LNil LNil LNil 0)" "LNil"
  return result

end NativeFixedPointGenerator

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [output] => IO.FS.writeFile output NativeFixedPointGenerator.generate
  | _ => throw (IO.userError "usage: generate_native_fixed_points.lean OUTPUT")
