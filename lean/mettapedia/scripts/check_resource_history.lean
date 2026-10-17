import Mettapedia.GSLT.Causality.ResourceHistoryWord
import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Lean

open Lean Mettapedia.Machines
open Mettapedia.GSLT.Causality.ResourceInteraction
open GroundBag

/-! Optional JSON-lines client for the ground-bag resource projection.

The imported source algorithm checks resource availability and constructs the
producer/reader dependency graph. A requested payload section additionally
checks the admitted ground exec word and its exact final rows. Starting-state
authentication and execution permission remain outside this protocol.
-/

set_option autoImplicit false

namespace ResourceHistoryClient

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The selected profile carries literal tokens and expression trees, not
evaluated native values. Token spelling keeps strings distinct from symbols.
Private handles and variable/registry tokens are outside this ground codec. -/
def decodeGround : Nat → Json → Option Atom
  | 0, _ => none
  | fuel + 1, json =>
    match json with
    | .str token =>
      if token.startsWith "$" || token.startsWith "&" then none
      else if token.startsWith "\"" ||
          !(token.contains '[' || token.contains ']' || token.contains ',') then
        some (.symbol token)
      else none
    | .arr items =>
      if items[0]? == some (.str "NativeHandle") ||
          items[0]? == some (.str "NeedRef") ||
          items[0]? == some (.str "StateCell") then none
      else Atom.expression <$> items.toList.mapM (decodeGround fuel)
    | _ => none

structure InputFiring where
  site : List Nat
  takes : List (List Nat)
  reads : List (List Nat)
  outputs : Nat
  deriving FromJson

structure InputNode where
  event : List Nat
  parents : List (List Nat)
  deriving FromJson

structure InputRow where
  key : List Nat
  value : Json
  deriving FromJson

structure InputPremise where
  kind : String
  key : List Nat
  value : Json
  deriving FromJson

structure PayloadFiring where
  action : Json
  inputs : List InputPremise
  produced : List InputRow
  deriving FromJson

structure PayloadRequest where
  profile : String
  initial : List Json
  word : List PayloadFiring
  final : List InputRow
  deriving FromJson

structure Request where
  schema : String
  initialCount : Nat
  word : List InputFiring
  graph : List InputNode
  costs : Option Bool := none
  payloads : Option PayloadRequest := none
  deriving FromJson

/-- One unit for each admitted ground resource firing. Depth is the longest
resource-dependency chain, separate from the native execution schedule. -/
structure ResourceCost where
  profile : String := "resource-firings-v1"
  work : Nat
  dependencyDepth : Nat
  deriving ToJson

structure Reply where
  schema : String := "prime-resource-history-word-v1"
  accepted : Bool
  resourceWord : Bool
  freshOccurrences : Bool
  dependencyGraph : Bool
  resourceCost : Option ResourceCost := none
  sourcePayload : Option Bool := none
  authority : String := "None"
  deriving ToJson

def decodeFiring (input : InputFiring) : Option ground.Entry :=
  if valid : input.site ∉ input.takes ∧ input.site ∉ input.reads ∧
      ∀ taken ∈ input.takes, taken ∉ input.reads then
    some ⟨input.site, ⟨input.takes, input.reads, input.outputs,
      valid.1, valid.2.1, valid.2.2⟩⟩
  else none

def decodeRow (input : InputRow) : Option PayloadRow := do
  return { key := input.key, value := ← decodeGround 100000 input.value }

def decodePremise (input : InputPremise) : Option DecodedPremise := do
  let kind ← match input.kind with
    | "read" => some PremiseKind.read
    | "take" => some PremiseKind.take
    | _ => none
  return { kind, key := input.key, value := ← decodeGround 100000 input.value }

def decodePayloadFiring (input : PayloadFiring) : Option PayloadClaim := do
  let action ← decodeGround 100000 input.action
  let inputs ← input.inputs.mapM decodePremise
  let produced ← input.produced.mapM decodeRow
  return { action, inputs, produced }

def checkPayloads (initialCount : Nat) (word : List ground.Entry)
    (payloads : PayloadRequest) : Bool :=
  if payloads.profile != "ground-bag-read-take-add-v1" ||
      payloads.initial.length != initialCount then false
  else match payloads.initial.mapM (decodeGround 100000),
      payloads.word.mapM decodePayloadFiring, payloads.final.mapM decodeRow with
    | some initial, some claims, some final =>
      sourcePayloadMatches (admitWord (initialRows initial) word claims) final
    | _, _, _ => false

def evaluate (request : Request) : Reply :=
  let refused : Reply := { accepted := false, resourceWord := false, freshOccurrences := false, dependencyGraph := false }
  if request.schema != "prime-resource-history-word-v1" then refused
  else match request.word.mapM decodeFiring with
  | none => refused
  | some word =>
    let sourcePayload := request.payloads.map (checkPayloads request.initialCount word)
    let payloadAccepted := sourcePayload.getD true
    let initial : Multiset Key := (List.range request.initialCount).map (fun index => [index])
    let enabled := (ground.replayWord word initial).isSome
    match project word with
    | none => { refused with resourceWord := enabled, sourcePayload }
    | some receipt =>
      let expected : CausalReceipt Key :=
        ⟨request.graph.map (fun node : InputNode => node.event), request.graph.map (fun node : InputNode => ⟨node.event, node.parents⟩)⟩
      let equalGraph := decide (receipt.dependencyView = expected.dependencyView)
      let resourceCost := if request.costs.getD false && enabled && equalGraph && payloadAccepted then
        let amount := receipt.dependencyReadout (fun _ => ⟨1, 1⟩)
        some { work := amount.work, dependencyDepth := amount.span : ResourceCost }
        else none
      { accepted := enabled && equalGraph && payloadAccepted,
        resourceWord := enabled, freshOccurrences := true,
        dependencyGraph := equalGraph, resourceCost, sourcePayload }

def run : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    if !line.isEmpty then
      match Json.parse line >>= fromJson? with
      | .error message =>
        IO.eprintln s!"invalid resource projection request: {message}"
        return 2
      | .ok (request : Request) => IO.println (toJson (evaluate request)).compress
  return 0

end ResourceHistoryClient

def main : IO UInt32 := ResourceHistoryClient.run
