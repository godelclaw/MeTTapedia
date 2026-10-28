import Mettapedia.Languages.MeTTa.HE.TypeRuleCompilation
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Executable HE reference rule programs

Every local rule form is tested as an open program in its original premise
context. Open acceptance does not assert that those premises are provable.
A separate closed chain derives the type of a grounded integer. The native
fixture uses the existing generic checker and exports the selected source
guard descriptions for inspection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeRuleProgramExamples

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CertificateGSLT InferenceChecker InferenceCettaWire
open Spec.Type Spec.Type.RulePresentation Spec.Match.Merge
open TypeRulePrograms

private abbrev empty := Bindings.empty
private abbrev x : Atom := .symbol "x"
private abbrev int : Atom := .symbol "Int"
private abbrev bool : Atom := .symbol "Bool"
private abbrev number : Atom := .symbol "Number"
private abbrev lookup := rawTypeLookupRel Space.empty
private abbrev Entry := Instance Space.empty lookup TypeMatchRel

private def pack {premises : List Judgment} {goal : Judgment}
    (rule : Rule Space.empty lookup TypeMatchRel premises goal) : Entry :=
  ⟨premises, goal, rule⟩

private theorem mismatch (candidate : Bindings) : ¬TypeMatchRel bool int empty candidate := by
  intro matched
  obtain ⟨_, proof, _⟩ := matched.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide)
  exact symbol_mismatch_not_match (by decide) _ proof

private theorem no_application (expression expected : Atom) (candidate : Bindings) :
    ¬ApplicationSuccessRel Space.empty expression int expected empty candidate lookup := by
  rintro ⟨_, function, _, _⟩
  cases function

def examples : List Entry := [
  pack (.annotationsNil x),
  pack (.annotationsHit x int [] []),
  pack (.annotationsSkip x (.symbol "unrelated") [] [] (by intro type same; cases same)),
  pack (.intrinsicInt 7), pack (.intrinsicBool true), pack (.intrinsicString "text"),
  pack (.intrinsicCustom "External" "value"),
  pack (.occurrencesVariable "a"), pack (.occurrencesGrounded (.int 7) number),
  pack (.occurrencesSymbol "x"), pack .occurrencesUnit,
  pack (.occurrencesExpression x [int]),
  pack (.storageVariable "a"), pack (.storageGroundedKnown (.int 7) number (by decide)),
  pack (.storageGroundedUndefined (.custom "%Undefined%" "value")),
  pack (.storageSymbolKnown "x" [int, int] (by decide)),
  pack (.storageSymbolUndefined "x"), pack .storageUnit,
  pack (.storageExpressionKnown x [int] [int] (by decide)),
  pack (.storageExpressionUndefined x [int]),
  pack (.lookupQuery empty (.var "a") int [Atom.undefinedType] (StorageTypesRel.variable Space.empty "a")),
  pack (.typeOf x [int, int] 1),
  pack (.matchUndefinedLeft int empty), pack (.matchAtomLeft int empty),
  pack (.matchUndefinedRight int empty), pack (.matchAtomRight int empty),
  pack (.matchStructural int int empty empty empty
    (by decide) (by decide) (by decide) (by decide)
    (.symSym "Int" semanticLoopFree_empty)
    (.mk (by simp [constraints, Bindings.empty]) .nil)),
  pack (.matchingPolicy Atom.undefinedType int empty empty (.undefinedLeft int empty)),
  pack (.typeAt empty x int [int, int] 1),
  pack (.castSuccess x Atom.undefinedType int empty empty [] [int] (by simp)),
  pack (.castFailure x bool empty [int, int] 1 (by
    intro type member candidate
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst type
    exact mismatch candidate)),
  pack (.castBatchSuccess x Atom.undefinedType int empty empty [] [int] (by simp)),
  pack (.castBatchFailure x bool empty [int, int] (by
    intro type member candidate
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst type
    exact mismatch candidate)),
  pack (.functionType [int, bool] int), pack (.argumentsNil empty),
  pack (.argumentsCons x Atom.undefinedType int [] [] empty empty empty),
  pack (.application x (.expression [.symbol "->", int]) Atom.undefinedType int [] [] empty empty empty),
  pack (.applicable (.expression [x]) (.expression [.symbol "->", int]) Atom.undefinedType empty empty),
  pack (.wrongArity x int int int [x] [] empty (by decide)),
  pack (.badArgument x int bool int x bool int [] [] [] [] empty empty rfl mismatch
    (no_application _ _)),
  pack (.badReturn x int bool int [] [] empty empty mismatch (no_application _ _))]

theorem all_rule_forms : examples.length = 41 ∧
    (examples.map (fun entry => TypeRuleData.ruleName entry.2.2)).eraseDups.length = 41 := by
  decide +kernel

def localAccepted (entry : Entry) : Bool :=
  checkOpenRaw (definition [entry]) (entry.1.map (encode (dictionary [entry])))
    (encode (dictionary [entry]) entry.2.1) (abstractInstance [entry] 0).eraseOpen

theorem all_local_accepted : examples.all localAccepted = true := by
  apply List.all_eq_true.mpr
  intro entry _
  exact abstractInstance_checks [entry] 0

def chain : List Entry := [pack (.intrinsicInt 7),
  pack (.storageGroundedKnown (.int 7) number (by decide)),
  pack (.typeOf (.grounded (.int 7)) [number] 0)]

def closedProof : RawOpenProof := .node (call 2) [.node (call 1) [.node (call 0) []]]

theorem closed_accepted :
    checkOpenRaw (definition chain) []
      (encode (dictionary chain) (.typeOf (.grounded (.int 7)) number)) closedProof = true := by
  decide +kernel

theorem closed_source : TypeOfRel Space.empty (.grounded (.int 7)) number :=
  accepted_source (compile_valid chain) (by decide) closed_accepted

private def render := CettaTerm.render
private def command (code : String) : String := "!(assertEqual " ++ code ++ " True)\n"
private def refuse (code : String) : String := "!(assertEqual " ++ code ++ " False)\n"

def exampleText (entry : Entry) : String :=
  let language := render (encodeDefinition (compile [entry]))
  let context := render (encodePatterns (entry.1.map (encode (dictionary [entry]))))
  let goal := render (encodePattern (encode (dictionary [entry]) entry.2.1))
  let proof := render (encodeOpenProof (abstractInstance [entry] 0).eraseOpen)
  "; " ++ TypeRuleData.ruleName entry.2.2 ++ "\n" ++
  command ("(gic-language-valid " ++ language ++ ")") ++
  command ("(gor-check " ++ language ++ " " ++ context ++ " " ++ goal ++ " " ++ proof ++ ")") ++
  refuse ("(gor-check " ++ language ++ " " ++ context ++ " (PApp \"forged\" LNil) " ++ proof ++ ")") ++
  refuse ("(gor-check " ++ language ++ " " ++ context ++ " " ++ goal ++
    " (GOpenHyp " ++ toString entry.1.length ++ "))")

def text : String :=
  "; Generated from HE.TypeRuleProgramExamples. Open cases supply premise holes.\n" ++
  "!(import! &self ../../../../Mettapedia/MettaKernel/kernel/generic_open_rule_programs.metta)\n" ++
  String.join (examples.map exampleText) ++
  let language := render (encodeDefinition (compile chain))
  let goal := render (encodePattern (encode (dictionary chain) (.typeOf (.grounded (.int 7)) number)))
  let proof := render (encodeOpenProof closedProof)
  command ("(gor-check " ++ language ++ " LNil " ++ goal ++ " " ++ proof ++ ")") ++
  refuse ("(gor-check " ++ language ++ " LNil " ++ goal ++
    " (GProof (GRuleInst \"unknown\" LNil) PrNil))")

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] => IO.FS.writeFile output text; pure 0
  | _ => IO.eprintln "usage: TypeRuleProgramExamples <output.metta>"; pure 1

#print axioms all_rule_forms
#print axioms all_local_accepted
#print axioms closed_source

end Mettapedia.Languages.MeTTa.HE.TypeRuleProgramExamples

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.HE.TypeRuleProgramExamples.main arguments
