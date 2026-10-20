import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner
import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntimeSource

/-!
# Complete rho query packets modulo quote-drop

The engine computes a full one-step class search at the reflective normal form
of the source. A packet retains the original source, committed source, selected
target, operational plan, commit policy, complete scheduler snapshot and receipt
readout. A missing target is refuted only after the class search reports complete.

Continuation code uses the scheduler snapshot returned by the target engine.
The output checker compares every packet field, including premise histories and
origins, with the independent Lean search before interpreting its verdict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

def spec : Spec :=
  ⟨GeneralRho.Standard.plan, [], .base "Proc", .reflective Complete.RhoQuoteDrop.presentation⟩

def zero : Pattern := .apply "PZero" []
def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name process : Pattern) : Pattern := .apply "POutput" [name, process]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def par (processes : List Pattern) : Pattern := .collection .hashBag processes none
def channel : Pattern := quote zero
def equivalentChannel : Pattern := quote (drop channel)
def differentChannel : Pattern := quote (par [])
def communication (sent : Pattern) : Pattern :=
  par [output sent zero, input channel (drop (.bvar 0))]

def committed (source : Pattern) : Pattern := Complete.Normalized.commit spec.plan spec.mode source

inductive Verdict where
  | proved
  | refuted
  | unknown
  deriving DecidableEq, Repr

def Verdict.atom : Verdict → Atom
  | .proved => .symbol "RhoProved"
  | .refuted => .symbol "RhoRefuted"
  | .unknown => .symbol "RhoUnknown"

structure Fixture where
  label : String
  source : Pattern
  target : Pattern
  work : Nat
  wanted : Verdict
  splitAt : Option Nat := none

def Fixture.state (fixture : Fixture) : Complete.Classes.State spec.plan :=
  Complete.Classes.runAt spec.plan spec.bound spec.expected (committed fixture.source) fixture.work

def verdict (target : Pattern) (snapshot : Complete.Classes.State spec.plan) : Verdict :=
  if snapshot.log.any (fun receipt => committed receipt.target == target) then .proved
  else if Complete.Classes.complete spec.plan snapshot then .refuted else .unknown

def Fixture.packet (fixture : Fixture) : Atom :=
  .expression [.symbol "RhoNativeReadout", planAtom spec, standardAtom spec,
    patternValue fixture.source, patternValue (committed fixture.source), patternValue fixture.target,
    encoded (classStateTerm spec.plan fixture.state), classReadoutValue spec.plan fixture.state,
    (verdict fixture.target fixture.state).atom]

def Fixture.paused (fixture : Fixture) (work : Nat) : Fixture :=
  { fixture with label := fixture.label ++ "-paused", work := work, wanted := .unknown, splitAt := none }

/-- A real source-language step at the normal form, with the selected normalized
result. This does not mention the computed search or its publication list. -/
def Meaning (source target : Pattern) : Prop :=
  ∃ reached, (GeneralOccurrenceSemantics.gslt spec.plan spec.bound spec.expected).Step
    (committed source) reached ∧ committed reached = target

theorem receipts_valid (fixture : Fixture) (receipt : GeneralOccurrenceSemantics.Receipt)
    (member : receipt ∈ fixture.state.log) :
    receipt.Valid spec.plan spec.bound spec.expected (committed fixture.source) :=
  Complete.Classes.sound spec.plan spec.bound spec.expected (committed fixture.source) fixture.work receipt member

private theorem equation_eq {left right : Pattern}
    (related : Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation spec.plan spec.bound spec.expected) left right) : left = right := by
  induction related with
  | rel _ _ equation => exact absurd equation (Complete.RhoPresented.noEquations _ _ _ _)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem proved_sound (fixture : Fixture)
    (positive : verdict fixture.target fixture.state = .proved) : Meaning fixture.source fixture.target := by
  unfold verdict at positive
  split at positive
  · rename_i hit
    obtain ⟨receipt, member, target⟩ := List.any_eq_true.mp hit
    exact ⟨receipt.target,
      GeneralOccurrenceSemantics.Receipt.semantic_step spec.plan spec.bound spec.expected
        (receipts_valid fixture receipt member), of_decide_eq_true target⟩
  · split at positive <;> cases positive

theorem refuted_sound (fixture : Fixture)
    (negative : verdict fixture.target fixture.state = .refuted) : ¬ Meaning fixture.source fixture.target := by
  unfold verdict at negative
  split at negative
  · cases negative
  · rename_i missed
    split at negative
    · rename_i closed
      rintro ⟨target, stepped, same⟩
      obtain ⟨receipt, member, equal⟩ := Complete.Classes.exact_of_complete
        spec.plan spec.bound spec.expected (committed fixture.source) fixture.work
        Complete.RhoPresented.checked closed stepped
      have receiptTarget : receipt.target = target := equation_eq equal
      have hit : fixture.state.log.any (fun receipt => committed receipt.target == fixture.target) = true :=
        List.any_eq_true.mpr ⟨receipt, member, by simpa [receiptTarget] using same⟩
      exact missed hit
    · cases negative

def fixtures : List Fixture := [
  ⟨"quote-drop-positive", communication equivalentChannel, par [], 200, .proved, none⟩,
  ⟨"canonical-positive", communication channel, par [], 200, .proved, none⟩,
  ⟨"different-channel", communication differentChannel, par [], 200, .refuted, none⟩,
  ⟨"different-target", communication equivalentChannel, output channel zero, 200, .refuted, none⟩,
  ⟨"duplicate-matches", par [output equivalentChannel zero, output equivalentChannel zero,
    input channel (drop (.bvar 0))], par [output channel zero], 200, .proved, none⟩,
  ⟨"zero-work", communication equivalentChannel, par [], 0, .unknown, none⟩,
  ⟨"split-positive", communication equivalentChannel, par [], 200, .proved, some 1⟩,
  ⟨"split-negative", communication differentChannel, par [], 200, .refuted, some 1⟩]

/-- The target test runs over every physical class receipt, before deduplication. -/
def helpers : String :=
  helperSource.text

private def render (atom : Atom) : IO String :=
  match ReadAfterRender.render? atom with
  | some text => pure text
  | none => throw (IO.userError "Rho query packet has no exact source rendering")

private def data (atom : Atom) : IO String := do pure ("(quote " ++ (← render atom) ++ ")")

def code (fixture : Fixture) (snapshot : Option Atom := none) (work : Option Nat := none) : IO String := do
  let plan ← render (planAtom spec)
  let standard ← render (standardAtom spec)
  let source ← render (patternValue fixture.source)
  let target ← render (patternValue fixture.target)
  let initial ← match snapshot with
    | some returned => render returned
    | none => pure "$initial"
  let body := "(let $snapshot (gslt:classes:rounds " ++ plan ++ " " ++ toString (work.getD fixture.work) ++ " " ++ initial ++ ")\n" ++
    "    (let $readout (gslt:classes:readout " ++ plan ++ " $snapshot)\n" ++
    "      (let $verdict (rho:native:verdict " ++ standard ++ " " ++ target ++ " $readout)\n" ++
    "        (quote (RhoNativeReadout " ++ plan ++ " " ++ standard ++ " " ++ source ++
      " $committed " ++ target ++ " $snapshot $readout $verdict)))))"
  pure ("(let $begun (rhonative:begin " ++ source ++ ")\n" ++
    "  (case $begun\n" ++
    "    (((ClassMachine $phase $committed $initial $states $receipts) " ++ body ++ "))))")

private def control (fixture : Fixture) (expression : String) : IO String := do
  let wanted ← data fixture.packet
  pure ("!(let $packet " ++ expression ++ "\n" ++
    "  (let $printed (println! (RhoNativePacket " ++ reprStr fixture.label ++ " $packet))\n" ++
    "    (println! (RhoNativeControl " ++ reprStr fixture.label ++ " (== $packet " ++ wanted ++ ")))))")

def generate : IO String := do
  let mut lines := [helpers]
  for fixture in fixtures do
    let initial := fixture.splitAt.map (fixture.paused) |>.getD fixture
    lines := lines ++ [← control initial (← code initial)]
  pure (String.intercalate "\n" lines ++ "\n")

def parseOutput (text : String) : IO (List (String × Atom)) := do
  let mut packets := []
  let mut controls : List String := []
  for line in text.splitOn "\n" do
    if line.startsWith "(RhoNativePacket " || line.startsWith "(RhoNativeControl " then
      match ← match SpaceSemantics.readSource line with
        | .ok atoms => pure atoms
        | .error _ => throw (IO.userError "Unreadable rho native output") with
      | [.expression [.symbol "RhoNativePacket", .grounded (.string label), packet]] =>
        if packets.any (fun item => item.1 == label) then throw (IO.userError "Duplicate rho packet")
        packets := packets ++ [(label, packet)]
      | [.expression [.symbol "RhoNativeControl", .grounded (.string label), .grounded (.bool true)]] =>
        if controls.contains label then throw (IO.userError "Duplicate rho comparison")
        controls := controls ++ [label]
      | _ => throw (IO.userError "Malformed or failing rho native output")
  if packets.length != controls.length then throw (IO.userError "Rho packet/comparison count mismatch")
  for (label, _) in packets do
    if !controls.contains label then throw (IO.userError "Rho packet lacks a complete comparison")
  pure packets

def generateResume (text : String) : IO String := do
  let packets ← parseOutput text
  let mut lines := [helpers]
  for fixture in fixtures do
    if let some first := fixture.splitAt then
      let paused := fixture.paused first
      let some (_, packet) := packets.find? (fun item => item.1 == paused.label)
        | throw (IO.userError "Missing paused rho snapshot")
      if packet != paused.packet then throw (IO.userError "Paused rho snapshot failed full validation")
      let .expression [.symbol "RhoNativeReadout", _, _, _, _, _, snapshot, _, _] := packet
        | throw (IO.userError "Paused rho envelope has no scheduler snapshot")
      lines := lines ++ [← control fixture (← code fixture (some snapshot) (some (fixture.work - first)))]
  pure (String.intercalate "\n" lines ++ "\n")

def check (text : String) : IO Unit := do
  let packets ← parseOutput text
  let paused := fixtures.filterMap fun fixture => fixture.splitAt.map (fixture.paused)
  if packets.length != fixtures.length + paused.length then throw (IO.userError "Unexpected rho packet count")
  for fixture in fixtures ++ paused do
    let some (_, packet) := packets.find? (fun item => item.1 == fixture.label)
      | throw (IO.userError ("Missing rho packet: " ++ fixture.label))
    if packet != fixture.packet then throw (IO.userError ("Changed rho receipt/context/state: " ++ fixture.label))
    let result := verdict fixture.target fixture.state
    if result != fixture.wanted then throw (IO.userError ("Unexpected rho verdict: " ++ fixture.label))
    if result == .refuted && !Complete.Classes.complete spec.plan fixture.state then
      throw (IO.userError "Rho refutation has no finite closure")
    if result == .unknown && Complete.Classes.complete spec.plan fixture.state then
      throw (IO.userError "Rho pending result unexpectedly has finite closure")
    IO.println s!"RhoNativeQuery {fixture.label} {reprStr result} receipts={fixture.state.log.length} complete={Complete.Classes.complete spec.plan fixture.state}"
  IO.println s!"RhoNativeGate {packets.length} exact packets"

def emitModule (path : String) : IO Unit := do
  match emitText? spec "rhonative" with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError "Rho reflective emitter refused the native query module")

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
