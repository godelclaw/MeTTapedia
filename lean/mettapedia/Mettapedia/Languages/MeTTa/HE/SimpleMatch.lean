import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Machines.ReadOnlyQuery

/-!
# HE legacy one-way matcher

The coarse `simpleMatch` interface is the historical one-way matcher used by the
older HE equation-query path and several control-form helpers. It is kept as a
shared primitive so the faithful `matchAtoms` / `mergeBindings` layer can reuse
the same atom utilities without forcing a module cycle through `Space.lean`.

`simpleMatch` is deliberately **not** the authoritative HE query matcher for
equations; G3 moves that public query interface onto `matchAtoms`.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Simple one-way pattern matching: does `pattern` match `target`?
    Variables in `pattern` bind to subterms of `target`.
    Returns resulting bindings on success.
    Ref: legacy equation-query helper, still used by several control forms. -/
def simpleMatch (pattern target : Atom) (b : Bindings) (fuel : Nat) : Option Bindings :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match pattern with
    | .var v =>
      match b.lookup v with
      | some existing => if existing == target then some b else none
      | none => some (b.assign v target)
    | .symbol s =>
      match target with
      | .symbol t => if s == t then some b else none
      | _ => none
    | .grounded g =>
      match target with
      | .grounded h => if g == h then some b else none
      | _ => none
    | .expression ps =>
      match target with
      | .expression ts =>
        if ps.length != ts.length then none
        else simpleMatchList ps ts b n
      | _ => none
where
  simpleMatchList : List Atom → List Atom → Bindings → Nat → Option Bindings
    | [], [], b, _ => some b
    | p :: ps, t :: ts, b, fuel =>
      match simpleMatch p t b fuel with
      | some b' => simpleMatchList ps ts b' fuel
      | none => none
    | _, _, _, _ => none


/-! ## Depth coverage for the control-form matcher -/

namespace SimpleMatchDepth

abbrev Request := Atom × Atom × Bindings
abbrev Q := Mettapedia.Machines.ReadOnlyQuery.Program Request (Option Bindings)

def eval (depth : Nat) (request : Request) : Option Bindings :=
  simpleMatch request.1 request.2.1 request.2.2 depth

def listBody : List Atom → List Atom → Bindings → Q (Option Bindings)
  | [], [], b => .pure (some b)
  | p :: ps, t :: ts, b => .read (p, t, b) fun answer =>
      match answer with
      | some next => listBody ps ts next
      | none => .pure none
  | _, _, _ => .pure none

def body (request : Request) : Q (Option Bindings) :=
  let (pattern, target, b) := request
  match pattern with
  | .var v => .pure <| match b.lookup v with
      | some existing => if existing == target then some b else none
      | none => some (b.assign v target)
  | .symbol s => .pure <| match target with
      | .symbol t => if s == t then some b else none
      | _ => none
  | .grounded g => .pure <| match target with
      | .grounded h => if g == h then some b else none
      | _ => none
  | .expression ps => match target with
      | .expression ts =>
          if ps.length != ts.length then .pure none else listBody ps ts b
      | _ => .pure none

open Mettapedia.Machines.ReadOnlyQuery

theorem run_listBody (depth : Nat) (ps ts : List Atom) (b : Bindings) :
    (run (eval depth) (listBody ps ts b)).answer =
      simpleMatch.simpleMatchList ps ts b depth := by
  induction ps generalizing ts b with
  | nil => cases ts <;> rfl
  | cons p ps ih =>
      cases ts with
      | nil => rfl
      | cons t ts =>
          simp only [listBody, run, eval, simpleMatch.simpleMatchList]
          split <;> simp_all [run]

theorem unfold_eval (depth : Nat) (request : Request) :
    eval (depth + 1) request = (run (eval depth) (body request)).answer := by
  rcases request with ⟨pattern, target, b⟩
  cases pattern with
  | var v => rfl
  | symbol s => rfl
  | grounded g => rfl
  | expression ps =>
      cases target <;> try rfl
      simp only [eval, simpleMatch, body]
      split <;> simp [run, run_listBody]

end SimpleMatchDepth

def simpleMatchCovered (pattern target : Atom) (b : Bindings) (depth : Nat) : Bool :=
  Mettapedia.Machines.ReadOnlyQuery.depthCovered
    SimpleMatchDepth.body SimpleMatchDepth.eval depth (pattern, target, b)

theorem simpleMatchCovered_stable (pattern target : Atom) (b : Bindings)
    (depth extra : Nat) (covered : simpleMatchCovered pattern target b depth = true) :
    simpleMatch pattern target b (depth + extra) = simpleMatch pattern target b depth :=
  Mettapedia.Machines.ReadOnlyQuery.depthCovered_stable
    SimpleMatchDepth.body SimpleMatchDepth.eval SimpleMatchDepth.unfold_eval
    depth extra (pattern, target, b) covered

end Mettapedia.Languages.MeTTa.HE
