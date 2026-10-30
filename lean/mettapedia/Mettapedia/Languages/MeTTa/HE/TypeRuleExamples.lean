import Mettapedia.Languages.MeTTa.HE.TypeRuleData
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact

/-! # Source-backed lookup and application examples for the rule interface -/

namespace Mettapedia.Languages.MeTTa.HE.TypeRuleExamples

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RulePresentation

def number : Atom := .symbol "Number"
def x : Atom := .symbol "x"
def declared : Space := Space.ofList
  [.expression [.symbol ":", x, number], .expression [.symbol ":", x, number]]

theorem duplicate_lookup : StorageTypesRel declared x [number, number] := by
  apply StorageTypesRel.symbolKnown
  · exact .hit (.hit .nil)
  · simp

theorem duplicate_lookup_data : getAtomTypes declared x = [number, number] :=
  Conformance.typesOfRel_eq_getAtomTypes duplicate_lookup

theorem duplicate_lookup_tree :
    Nonempty (Tree declared (rawTypeLookupRel declared) TypeMatchRel (.storage x [number, number])) :=
  storage_complete duplicate_lookup

theorem missing_lookup : StorageTypesRel declared (.symbol "missing") [Atom.undefinedType] := by
  apply StorageTypesRel.symbolUndefined
  exact .skip (by simp [x]) (.skip (by simp [x]) .nil)

theorem grounded_lookup : StorageTypesRel declared (.grounded (.int 7)) [number] :=
  .groundedKnown (.int 7) (by decide)

/-- This is the source's application example with independent annotation
variables. Reusing a spelling must not identify their private scopes. -/
def applicationSpace : Space := Space.ofList [
  .expression [.symbol ":", .symbol "g", .expression [.symbol "->", .var "t", .symbol "A", .symbol "R"]],
  .expression [.symbol ":", .symbol "b", .symbol "B"],
  .expression [.symbol ":", .symbol "k", .var "t"]]

def application : Atom := .expression [.symbol "g", .symbol "b", .symbol "k"]

theorem independently_scoped_application :
    ∃ packages, Presentation.Exact.RuntimeTypePackagesRel applicationSpace application packages ∧
      Presentation.Exact.observedTypes packages = [.symbol "R"] :=
  ⟨_, Presentation.Exact.independent_annotation_variables_infer_return, by
    simp [Presentation.Exact.observedTypes, Presentation.Exact.inferredPackage,
      Presentation.TypeSubst.apply]⟩

def declarationCommand (spaceName : String) (row : Atom) : Atom :=
  .expression [.symbol "add-atom", .symbol spaceName, row]

def lookupCheck (spaceName : String) (subject : Atom) (expected : List Atom) : Atom :=
  .expression [.symbol "assertEqual",
    .expression [.symbol "collapse", .expression [.symbol "get-type", subject, .symbol spaceName]],
    .expression expected]

def metta : String :=
  "; Generated from HE.TypeRuleExamples; run with the HE reference dialect.\n" ++
  "; Declaration occurrences and independent annotation scopes are observable.\n" ++
  "!(bind! &he-reference (new-space))\n" ++
  String.join (declared.atoms.map fun row => "!" ++ toString (declarationCommand "&he-reference" row) ++ "\n") ++
  String.join ([x, .symbol "missing", .grounded (.int 7)].map fun subject =>
    "!" ++ toString (lookupCheck "&he-reference" subject (getAtomTypes declared subject)) ++ "\n") ++
  "!(bind! &he-application (new-space))\n" ++
  String.join (applicationSpace.atoms.map fun row =>
    "!" ++ toString (declarationCommand "&he-application" row) ++ "\n") ++
  "!" ++ toString (lookupCheck "&he-application" application [.symbol "R"]) ++ "\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [output] => IO.FS.writeFile output metta; pure 0
  | _ => IO.eprintln "usage: TypeRuleExamples <output.metta>"; pure 1

#print axioms duplicate_lookup_tree
#print axioms independently_scoped_application

end Mettapedia.Languages.MeTTa.HE.TypeRuleExamples

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.HE.TypeRuleExamples.main arguments
