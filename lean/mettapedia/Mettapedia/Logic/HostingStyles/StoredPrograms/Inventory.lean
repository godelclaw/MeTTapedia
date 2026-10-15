import Mettapedia.Logic.HostingStyles.StoredPrograms.Restriction
import Mettapedia.Languages.MM0.Presentation.CalculusProgram

/-!
# What MM0's kernel operations need

The three operations of MM0's kernel (`Calculus.family`) are heads of
equation programs, and the whole check of a certificate is a head of a fourth
(`ComputationalCalculus.calculusProgram`).  This module reads off each
program, by computation on its text (`inventory`), the three things that
separate an equation program from a rule table: the primitives of the host
that it calls, the special forms that it uses, and the pairs of equations of
one head whose left sides overlap.

## The programs of the operations

| operation | head | program | equations | primitives | `let` | overlapping pairs |
|---|---|---|---|---|---|---|
| theorem at an index | `nik:nat-table-get` | `naturalLookupProgram` | 5 | list view, equality of numbers | none | none |
| conversion by a witness | `mm0:conversion` | `conversionProgram` | 193 | the seven below | none | 1 |
| instance of a theorem | `mm0:instantiate-theorem` | `proofProgram` | 233 | the seven below | none | 1 |
| check of a certificate | `mm0:certificate` | `calculusProgram` | 280 | the seven below and the strict order | none | 15 |

(`lookup_inventory`, `conversion_inventory`, `proof_inventory`,
`calculus_inventory`.)  The seven: the list view, the list former, the zero
test, the predecessor, the equality of numbers, the sum, and the equality of
data.

## The parts that the programs assemble

The proof program is fourteen lists of equations, one after the other
(`proofProgram_assembled`); the conversion program is the first thirteen.

| part | equations | primitives | overlapping pairs |
|---|---|---|---|
| typing | 37 | list view, zero test, predecessor, equality of numbers | none |
| list append | 3 | list view, list former | none |
| support | 10 | none | none |
| membership | 5 | list view, equality of numbers | none |
| dependency | 9 | equality of numbers | none |
| argument checks | 15 | equality of numbers, list view | none |
| admissible substitution | 22 | list view, list former, sum | none |
| substitution | 11 | zero test, predecessor | none |
| instantiation | 6 | list view | none |
| fresh dummies | 15 | list view, list former | none |
| table lookup | 5 | list view, equality of numbers | none |
| unfolding | 12 | list view, list former | none |
| conversion | 43 | list view, **equality of data**, list former | **1**: `conversion-argument-checked`, `conversion-argument-refused` |
| proof | 40 | list view, list former, **equality of data** | none |
| calculus (the check) | 47 | list former, strict order, sum, list view, **equality of data** | **14** |

(`kernelParts_inventory`.)  **No part uses `let` or `metta-nullary`.**  The
equality of data is called by the last three parts only, and all overlapping
pairs are in two of them: one equation that refuses when the three checks of
a converted argument are not all true, and the catch-all equations of the
check of a certificate.

What an operation reaches in its program can be less than the program: the
instance of a theorem reaches 130 of the 233 equations, none of which calls
the equality of data or overlaps another (`Instantiation.lean`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation listAppendProgram naturalMembershipProgram naturalLookupProgram)
open Mettapedia.Languages.MM0.Presentation
open Mettapedia.Languages.MM0.Presentation.ComputationalTyping (typingProgram)
open Mettapedia.Languages.MM0.Presentation.ComputationalSupport (supportEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalDependency (dependencyEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalArguments (argumentEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmissible (admissibleEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation (instantiationEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalFreshDummies (freshEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions (unfoldingEquations)
open Mettapedia.Languages.MM0.Presentation.ComputationalConversion
  (conversionEquations conversionProgram)
open Mettapedia.Languages.MM0.Presentation.ComputationalProof (proofEquations proofProgram)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus (calculusEquations calculusProgram)

/-- **What is read off a program**: the number of its equations, the
primitives of the host that it calls, the special forms that it uses, and
its overlapping pairs. -/
structure ProgramInventory where
  equations : Nat
  primitives : List String
  specialForms : List String
  overlaps : List (String × String)
  deriving DecidableEq, Repr

/-- **The inventory of a program**, for the heads that its host handles. -/
def inventory (program : Program) (handled : List String) : ProgramInventory :=
  ⟨program.length, calledPrimitives program handled, specialForms program, overlappingPairs program⟩

/-- **The parts that the proof program assembles**, in order, and the
equations of the check. -/
def kernelParts : List (String × Program) :=
  [("typing", typingProgram), ("list append", listAppendProgram), ("support", supportEquations),
    ("membership", naturalMembershipProgram), ("dependency", dependencyEquations),
    ("argument checks", argumentEquations), ("admissible substitution", admissibleEquations),
    ("substitution", substitutionProgram), ("instantiation", instantiationEquations),
    ("fresh dummies", freshEquations), ("table lookup", naturalLookupProgram),
    ("unfolding", unfoldingEquations), ("conversion", conversionEquations),
    ("proof", proofEquations), ("calculus", calculusEquations)]

/-- **The programs are their parts, one after the other.** -/
theorem proofProgram_assembled :
    conversionProgram = ((kernelParts.take 13).map Prod.snd).flatten ∧
      proofProgram = ((kernelParts.take 14).map Prod.snd).flatten ∧
      calculusProgram = (kernelParts.map Prod.snd).flatten := by
  simp [kernelParts, calculusProgram, proofProgram, conversionProgram,
    ComputationalDefinitions.unfoldingProgram, ComputationalInstantiation.instantiationProgram,
    ComputationalAdmissible.admissibleProgram, ComputationalArguments.argumentProgram,
    ComputationalDependency.dependencyProgram, ComputationalSupport.supportProgram]

set_option maxRecDepth 100000 in
/-- **The inventory of the parts**, under the larger host. -/
theorem kernelParts_inventory :
    kernelParts.map (fun part => (part.1, inventory part.2 dataEqualityHandled)) =
      [("typing", ⟨37, ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq"], [], []⟩),
        ("list append", ⟨3, ["nik:list-view", "nik:list-cons"], [], []⟩),
        ("support", ⟨10, [], [], []⟩),
        ("membership", ⟨5, ["nik:list-view", "nik:nat-eq"], [], []⟩),
        ("dependency", ⟨9, ["nik:nat-eq"], [], []⟩),
        ("argument checks", ⟨15, ["nik:nat-eq", "nik:list-view"], [], []⟩),
        ("admissible substitution", ⟨22, ["nik:list-view", "nik:list-cons", "nik:nat-add"], [], []⟩),
        ("substitution", ⟨11, ["nik:nat-zero", "nik:nat-pred"], [], []⟩),
        ("instantiation", ⟨6, ["nik:list-view"], [], []⟩),
        ("fresh dummies", ⟨15, ["nik:list-view", "nik:list-cons"], [], []⟩),
        ("table lookup", ⟨5, ["nik:list-view", "nik:nat-eq"], [], []⟩),
        ("unfolding", ⟨12, ["nik:list-view", "nik:list-cons"], [], []⟩),
        ("conversion", ⟨43, ["nik:list-view", "nik:data-eq", "nik:list-cons"], [],
          [("conversion-argument-checked", "conversion-argument-refused")]⟩),
        ("proof", ⟨40, ["nik:list-view", "nik:list-cons", "nik:data-eq"], [], []⟩),
        ("calculus", ⟨47, ["nik:list-cons", "nik:nat-lt", "nik:nat-add", "nik:list-view", "nik:data-eq"],
          [],
          [("mm0-hypothesis-here", "rule-unknown"), ("mm0-hypothesis-there", "rule-unknown"),
            ("mm0-hypothesis", "rule-unknown"), ("mm0-theorem", "rule-unknown"),
            ("mm0-conversion", "rule-unknown"), ("mm0-all-nil", "rule-unknown"),
            ("mm0-all-cons", "rule-unknown"), ("pattern-cons-items", "pattern-cons"),
            ("pattern-list-items", "pattern-list"), ("valid-lambda", "valid-lambda-named"),
            ("valid-multi-lambda", "valid-multi-lambda-named"),
            ("valid-collection", "valid-collection-rest"), ("children-done", "children-mismatch"),
            ("children-next", "children-mismatch")]⟩)] := by
  decide +kernel

/-- **The lookup of a theorem**: two primitives of the shared host, no special
form, no overlapping pair. -/
theorem lookup_inventory :
    inventory naturalLookupProgram computationalHandled =
      ⟨5, ["nik:list-view", "nik:nat-eq"], [], []⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The conversion program**: seven primitives, no special form, one
overlapping pair. -/
theorem conversion_inventory :
    inventory conversionProgram dataEqualityHandled =
      ⟨193, ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
          "nik:nat-add", "nik:data-eq"], [],
        [("conversion-argument-checked", "conversion-argument-refused")]⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The proof program**, whose head `mm0:instantiate-theorem` is the
instance of a theorem: the same seven primitives and the same pair. -/
theorem proof_inventory :
    inventory proofProgram dataEqualityHandled =
      ⟨233, ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
          "nik:nat-add", "nik:data-eq"], [],
        [("conversion-argument-checked", "conversion-argument-refused")]⟩ := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The program of the check of a certificate**: eight primitives, no
special form, fifteen overlapping pairs. -/
theorem calculus_inventory :
    (inventory calculusProgram dataEqualityHandled).equations = 280 ∧
      (inventory calculusProgram dataEqualityHandled).primitives =
        ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
          "nik:nat-add", "nik:data-eq", "nik:nat-lt"] ∧
      (inventory calculusProgram dataEqualityHandled).specialForms = [] ∧
      (inventory calculusProgram dataEqualityHandled).overlaps.length = 15 := by
  decide +kernel

/-- Ten arguments on which both equations for a checked argument match: three
times `True`, and seven further data. -/
def checkedArguments : List EngineTerm :=
  [.sym "True", .sym "True", .sym "True", .sym "t", .sym "d", .sym "c", .sym "h", .sym "b",
    .sym "l", .sym "r"]

/-- The equation that refuses a converted argument, as the conversion program
writes it. -/
def refusingEquation : Equation :=
  ⟨"conversion-argument-refused", "mm0:conversion-argument-checked",
    [.var "sort-ok", .var "left-ok", .var "right-ok", .var "table", .var "definitions",
      .var "context", .var "children", .var "binders", .var "left", .var "right"], .sym "None"⟩

set_option maxRecDepth 100000 in
/-- **Negative**: the equations of the conversion are not separated.  On
three times `True` both equations for a checked argument match; the engine
takes the first, and in a separated program it would take each. -/
theorem conversionEquations_not_separated : ¬ Separated conversionEquations := by
  intro separated
  have listed : conversionEquations[40]? = some refusingEquation := rfl
  have selected := separated.select_of_matches (List.mem_of_getElem? listed)
    (head := "mm0:conversion-argument-checked") (arguments := checkedArguments) rfl rfl
  have first : (conversionEquations.select "mm0:conversion-argument-checked"
      checkedArguments).map (·.1.name) = some "conversion-argument-checked" := by decide +kernel
  rw [selected] at first
  simp [refusingEquation] at first

#print axioms proofProgram_assembled
#print axioms kernelParts_inventory
#print axioms lookup_inventory
#print axioms conversion_inventory
#print axioms proof_inventory
#print axioms calculus_inventory
#print axioms conversionEquations_not_separated

end Mettapedia.Logic.HostingStyles.StoredPrograms
