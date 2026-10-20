/-
Writes `tests/petta/emitted/rho.metta` (canonical form) and `tests/petta/emitted/rho_standard.metta`
(standard form) with `CompleteEmission.emitText?`, and prints `tests/petta/gslt_rho_module_controls.metta`.
Every expected readout is the Lean explorer's (`Complete.Explore` over `Complete.Normalized.search`).
Run from `lean/mettapedia`: `lake env lean --run ../../metta/gslt/tools/generate_rho_modules.lean`.
-/
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.OSLF.MeTTaIL.GeneralRhoStandardSites

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

def render (term : Term) : String := Term.render term
def pat (p : Pattern) : String := render (encodePattern p)

def canonicalSpec : Spec := ⟨GeneralRho.Standard.plan, [], .base "Proc", .canonical⟩
def standardSpec : Spec := ⟨GeneralRho.Standard.plan, [], .base "Proc", .standard⟩

def zero : Pattern := .apply "PZero" []
def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name process : Pattern) : Pattern := .apply "POutput" [name, process]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def par (processes : List Pattern) : Pattern := .collection .hashBag processes none

def x : Pattern := quote zero
def y : Pattern := quote (output x zero)

/-- One message and one receiver. -/
def single : Pattern := par [output x zero, input x (drop (.bvar 0))]
/-- Two equal messages and one receiver: both communications reach one state. -/
def twin : Pattern := par [output x zero, output x zero, input x (drop (.bvar 0))]
/-- Two messages, two receivers on two channels: the communications interleave. -/
def interleaved : Pattern :=
  par [output x zero, input x (drop (.bvar 0)), output y zero, input y (drop (.bvar 0))]
/-- Three messages racing for two receivers on one channel. -/
def race : Pattern :=
  par [output x zero, output x (output y zero), output x (drop y), input x (drop (.bvar 0)), input x (drop (.bvar 0))]

/-- Channels nobody receives on. -/
def u : Pattern := quote (input x (drop (.bvar 0)))
def v : Pattern := quote (output y zero)
def w : Pattern := quote (output x (output x zero))
/-- Two independent communications with distinct results: both orders reach one multiset. -/
def diamond : Pattern :=
  par [output x zero, input x (output u zero), output y zero, input y (output v zero)]
/-- Three independent communications with distinct results. -/
def triple : Pattern :=
  par [output x zero, input x (output u zero), output y zero, input y (output v zero),
    output w zero, input w (output u (output v zero))]

def states (spec : Spec) (source : Pattern) (work : Nat) : List Pattern :=
  (Complete.Explore.explore (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source) work).nodes.map (·.state)

def exploreControl (label name : String) (spec : Spec) (source : Pattern) (work : Nat) : String :=
  "!(let $s (" ++ name ++ ":explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (RhoModuleControl " ++ reprStr label ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (states spec source work)) ++ ")))))"

def emitTo (spec : Spec) (name : String) (path : String) : IO Unit := do
  match emitText? spec name with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError s!"refused: {name}")

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  emitTo canonicalSpec "rho" (dir ++ "rho.metta")
  emitTo standardSpec "rhostd" (dir ++ "rho_standard.metta")
  let work := 200
  let sources := [("single", single), ("twin", twin), ("interleaved", interleaved), ("race", race),
    ("diamond", diamond), ("triple", triple)]
  IO.println "; Controls for the emitted rho modules: canonical form (rho) and standard form (rhostd)."
  IO.println "; Every expected readout is the Lean explorer's."
  for (label, source) in sources do
    IO.println (exploreControl (label ++ "-canonical") "rho" canonicalSpec source work)
    IO.println (exploreControl (label ++ "-standard") "rhostd" standardSpec source work)
  for (label, source) in sources do
    IO.eprintln s!"{label}: canonical {(states canonicalSpec source work).length} states, standard {(states standardSpec source work).length} states"
