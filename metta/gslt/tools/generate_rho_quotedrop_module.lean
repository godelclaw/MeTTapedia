/-
Writes `tests/petta/emitted/rho_quotedrop.metta` (the canonical form of the quote-drop normal form) with
`CompleteEmission.emitText?`, and prints `tests/petta/gslt_rho_quotedrop_controls.metta`. Every expected
readout is the Lean explorer's (`Complete.Explore` over `Complete.Normalized.search`), for the module
committing quote-drop normal forms (rhoqd) and, for contrast, the canonical module (rho).
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_rho_quotedrop_module.lean`.
-/
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RhoCanonicalEmission

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

def render (term : Term) : String := Term.render term
def pat (p : Pattern) : String := render (encodePattern p)

def zero : Pattern := .apply "PZero" []
def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name process : Pattern) : Pattern := .apply "POutput" [name, process]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def par (processes : List Pattern) : Pattern := .collection .hashBag processes none

def x : Pattern := quote zero
/-- `@(*@0)`, one name with `@0` under the name equation. -/
def xd : Pattern := quote (drop x)
/-- `@{}`, a different name: the parallel laws do not identify `{}` with `0`. -/
def xe : Pattern := quote (par [])

/-- A message on `@(*@0)` and a receiver on `@0`: they communicate modulo the name equation. -/
def named : Pattern := par [output xd zero, input x (drop (.bvar 0))]
/-- The same, the other way round, with the dropped name in the payload. -/
def payload : Pattern := par [output x (output xd zero), input xd (drop (.bvar 0))]
/-- Twice dropped: `@(*@(*@0))` is still `@0`. -/
def twice : Pattern := par [output (quote (drop xd)) zero, input x (drop (.bvar 0))]
/-- A message on `@{}` and a receiver on `@0`: no communication. -/
def wrapper : Pattern := par [output xe zero, input x (drop (.bvar 0))]
/-- A received name that is dropped and quoted again: the body sees `@0`. -/
def relay : Pattern := par [output x zero, input x (output (quote (drop (.bvar 0))) zero), input x (drop (.bvar 0))]

def states (spec : Spec) (source : Pattern) (work : Nat) : List Pattern :=
  (Complete.Explore.explore (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source) work).nodes.map (·.state)

def exploreControl (label name : String) (spec : Spec) (source : Pattern) (work : Nat) : String :=
  "!(let $s (" ++ name ++ ":explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (RhoQuoteDropControl " ++ reprStr label ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (states spec source work)) ++ ")))))"

def emitTo (spec : Spec) (name : String) (path : String) : IO Unit := do
  match emitText? spec name with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError s!"refused: {name}")

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  emitTo rhoQuoteDropSpec "rhoqd" (dir ++ "rho_quotedrop.metta")
  let work := 200
  let sources := [("named", named), ("payload", payload), ("twice", twice), ("wrapper", wrapper),
    ("relay", relay)]
  IO.println "; Controls for the emitted rho module committing quote-drop normal forms (rhoqd), against the"
  IO.println "; canonical module (rho). Every expected readout is the Lean explorer's."
  for (label, source) in sources do
    IO.println (exploreControl (label ++ "-quotedrop") "rhoqd" rhoQuoteDropSpec source work)
    IO.println (exploreControl (label ++ "-canonical") "rho" rhoSpec source work)
  for (label, source) in sources do
    IO.eprintln s!"{label}: quote-drop {(states rhoQuoteDropSpec source work).length} states, canonical {(states rhoSpec source work).length} states"

#eval main
