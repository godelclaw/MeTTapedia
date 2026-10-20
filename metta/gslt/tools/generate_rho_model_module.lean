/-
Writes `tests/petta/emitted/rho_model.metta` (the canonical form of the model normal form) with
`CompleteEmission.emitText?`, and prints `tests/petta/gslt_rho_model_controls.metta`. Every expected
readout is the Lean explorer's (`Complete.Explore` over `Complete.Normalized.search`), for the module
committing model normal forms (rhomodel) and, for contrast, the module committing quote-drop normal
forms (rhoqd).
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_rho_model_module.lean`.
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
/-- `@{}`, one name with `@0` under `{} = 0`. -/
def xe : Pattern := quote (par [])
/-- `@{*@0}`: collapsing the singleton exposes a quote-drop pair, so it is `@0`. -/
def xs : Pattern := quote (par [drop x])
/-- `@{0, 0}`: the units go, and the empty composition is `0`. -/
def xz : Pattern := quote (par [zero, zero])

/-- A receiver on `@0` of a message sent on `channel`. -/
def meet (channel : Pattern) : Pattern := par [output channel zero, input x (drop (.bvar 0))]

/-- A message on `@{}` and a receiver on `@0`: they communicate under the wrapper laws. -/
def empty : Pattern := meet xe
/-- A message on `@{*@0}`: the wrapper collapse exposes the name equation. -/
def exposed : Pattern := meet xs
/-- A message on `@{0, 0}`: unit removal, then the empty composition is `0`. -/
def units : Pattern := meet xz
/-- A message on `@(*@0)`: the name equation alone, as in the quote-drop model. -/
def named : Pattern := meet xd
/-- A message whose payload is `{0}`, which is `0`. -/
def payload : Pattern := par [output x (par [zero]), input x (drop (.bvar 0))]
/-- Two copies of a message and one receiver: one copy stays, since composition is not idempotent. -/
def copies : Pattern := par [output x zero, output x zero, input x (drop (.bvar 0))]
/-- A message on `@(@0!(0))` and a receiver on `@0`: different names never communicate. -/
def apart : Pattern := meet (quote (output x zero))

def states (spec : Spec) (source : Pattern) (work : Nat) : List Pattern :=
  (Complete.Explore.explore (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source) work).nodes.map (·.state)

def exploreControl (label name : String) (spec : Spec) (source : Pattern) (work : Nat) : String :=
  "!(let $s (" ++ name ++ ":explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (RhoModelControl " ++ reprStr label ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (states spec source work)) ++ ")))))"

def emitTo (spec : Spec) (name : String) (path : String) : IO Unit := do
  match emitText? spec name with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError s!"refused: {name}")

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  emitTo rhoModelSpec "rhomodel" (dir ++ "rho_model.metta")
  let work := 200
  let sources := [("empty", empty), ("exposed", exposed), ("units", units), ("named", named),
    ("payload", payload), ("copies", copies), ("apart", apart)]
  IO.println "; Controls for the emitted rho module committing model normal forms (rhomodel), against the"
  IO.println "; module committing quote-drop normal forms (rhoqd). Every expected readout is the Lean explorer's."
  for (label, source) in sources do
    IO.println (exploreControl (label ++ "-model") "rhomodel" rhoModelSpec source work)
    IO.println (exploreControl (label ++ "-quotedrop") "rhoqd" rhoQuoteDropSpec source work)
  for (label, source) in sources do
    IO.eprintln s!"{label}: model {(states rhoModelSpec source work).length} states, quote-drop {(states rhoQuoteDropSpec source work).length} states"

#eval main
