import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ContextualJudgmentReadback

/-! # Generated named-telescope and native query comparisons -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ContextualJudgmentExamples

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation ContextualJudgmentReadback

def level : Atom → Option Tower.Head
  | .grounded (.int (.ofNat n)) => some (.sort (.const n))
  | _ => none

def form (name : String) (arguments : List Atom) : Atom := .expression (.symbol name :: arguments)
def bind (name : String) (domain : Atom) : Atom := .expression [.symbol name, .symbol ":", domain]
def A : Atom := .symbol "A"
def x : Atom := .symbol "x"
def y : Atom := .symbol "y"
def p : Atom := .symbol "p"
def u0 : Atom := form "u" [.grounded (.int 0)]
def identityContext : Rows := [("x", A), ("A", u0)]
def pairType : Atom := form "sigma" [bind "y" A, form "id" [A, y, x]]

/-- The rows are newest first internally; the emitted MeTTa context is
oldest first. The final pair is the original subject and expected type. -/
def examples : List (Rows × Atom × Atom) := [
  (identityContext, x, A),
  (("y", A) :: identityContext, x, A),
  (("y", A) :: identityContext, y, A),
  (identityContext, form "lam" [bind "y" A, x], form "->" [bind "y" A, A]),
  (identityContext, form "pair" [x, form "refl" [x]], pairType),
  (("p", pairType) :: identityContext, form "fst" [p], A),
  (("p", pairType) :: identityContext, form "snd" [p], form "id" [A, form "fst" [p], x])]

theorem identity_readback :
    readTerm level ["x", "A"] x = some (.var 0) ∧
    readTerm level ["x", "A"] A = some (.var 1) := by
  simp [readTerm, readRaw, x, A, NativeSyntax.decode]

theorem capture_avoided :
    readTerm level ["x", "A"] (form "lam" [bind "y" A, x]) =
      some (.lamTyped (.var 1) (.var 1)) := by
  simp [readTerm, readRaw, form, bind, A, x, NativeSyntax.decode]

theorem alpha_names_agree :
    nativeClosed level identityContext x =
      nativeClosed level [("value", .symbol "Carrier"), ("Carrier", u0)] (.symbol "value") := by
  decide +kernel

theorem equal_domains_keep_positions :
    readTerm level ["y", "x", "A"] x ≠ readTerm level ["y", "x", "A"] y := by
  simp [readTerm, readRaw, x, y, NativeSyntax.decode]

theorem negative_level_refused : readTerm level [] (form "u" [.grounded (.int (-1))]) = none := by
  simp [readTerm, readRaw, form, level]

def contextData (rows : Rows) : Atom :=
  .expression (rows.reverse.map fun (name, domain) => form ":" [.symbol name, domain])

def exportExample (item : Rows × Atom × Atom) : Option String := do
  let (rows, body, type) := item
  let closedBody := closeNamed "lam" rows body
  let closedType := closeNamed "->" rows type
  let subject ← nativeClosed level rows body
  let object ← NativeDependentSourceWire.lower (← readTerm level [] closedType)
  let query := "(type:check " ++ toString closedBody ++ " " ++ toString closedType ++ ")"
  return "!(assertEqual (abstract-term " ++ toString (contextData rows) ++ " " ++ toString body ++
      ") (quote " ++ toString closedBody ++ "))\n" ++
    "!(assertEqual (abstract-type " ++ toString (contextData rows) ++ " " ++ toString type ++
      ") (quote " ++ toString closedType ++ "))\n" ++
    "!(assertEqual " ++ query ++ " True)\n" ++
    "!(let (PrimeKernelQueryV1 $judgment $route $context $levels $rules\n" ++
    "        (Subject $subject) $subject-type (Object $object) $object-type)\n" ++
    "      (type:kernel-query " ++ query ++ ")\n" ++
    "   (assertEqual (quote ($subject $object)){$subject $object}\n" ++
    "     (quote (" ++ Mettapedia.GSLT.LanguageDef.CettaWire.Term.render subject ++ " " ++
      Mettapedia.GSLT.LanguageDef.CettaWire.Term.render object ++ "))))\n"

def metta : Option String := do
  let programs ← examples.mapM exportExample
  return "; Generated from ContextualJudgmentExamples; exact named and native syntax comparisons.\n" ++
    "(hol:profile base)\n!(import! &self judgments.metta)\n" ++ String.join programs ++
    "!(assertEqual (judge (quote (|- ((: A (u 0)) (: x A) (: x A)) (: x A))))\n" ++
    "   (Unsupported duplicate-display-name))\n" ++
    "!(assertEqual (judge (quote (|- ((: A (u 0)) (: x A)) (: x (u 0))))) False)\n" ++
    "!(assertEqual (judge (quote (|- ((: A (u 0)) (: () A)) (: A (u 0)))))\n" ++
    "   (Unsupported non-symbol-binder))\n"

theorem examples_export : metta.isSome = true := by decide +kernel

def main (arguments : List String) : IO UInt32 := do
  match arguments, metta with
  | [output], some program => IO.FS.writeFile output program; pure 0
  | _, _ => IO.eprintln "usage: ContextualJudgmentExamples <output.metta>"; pure 1

#print axioms capture_avoided
#print axioms alpha_names_agree
#print axioms equal_domains_keep_positions

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ContextualJudgmentExamples

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ContextualJudgmentExamples.main arguments
