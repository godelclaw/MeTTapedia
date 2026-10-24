import Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentation
import Mettapedia.GSLT.LanguageDef.ModuleSource.FixedArityCollectionControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-! # Independent operations over the same collection carrier

The two monoid operations have different units and a natural-number model
that distinguishes them. Their named collection replacements retain all
source equations. Anonymous bags cannot acquire their result sort.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.OSLF.MeTTaIL.Syntax
#module_file "../../../../../../metta/gslt/module/CollectionIndependentMonoids.module"
#module_file "../../../../../../metta/gslt/module/CollectionNamedSets.module"

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls

open Mettapedia.OSLF.MeTTaIL
open WellSorted

def language : LanguageDef := CollectionIndependentMonoids.language.toOption.getD (LanguageDef.empty "")
def core : LanguageDef := (language.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

#guard CollectionIndependentMonoids.language.isOk
#guard language.toCore.isOk
#guard language.equations.length == 8
#guard language.terms.filterMap (fun row => if row.collectionRepresentation == .wrapped then some row.label else none) == ["Sum", "Product"]
#guard core.rewrites.map (fun row => row.left == row.right) == [false]
#guard (CoreReduction.bareLabels core).isEmpty

def zero : Pattern := .apply "Zero" []
def one : Pattern := .apply "One" []
def payload : Pattern := .collection .hashBag [zero, one] none
def resultSort : TypeExpr := .base "Number"

def queries : List (String × Pattern × Bool) :=
  [("sum", .apply "Sum" [payload], true),
   ("product", .apply "Product" [payload], true),
   ("anonymous-bag", payload, false),
   ("wrong-kind", .apply "Sum" [.collection .hashSet [zero, one] none], false),
   ("wrong-wrapper", .apply "Other" [payload], false),
   ("wrong-arity", .apply "Sum" [zero, one], false)]

#guard queries.all fun (_, term, expected) =>
  checkHasType core (fun _ => none) [] term resultSort == expected

namespace NamedSets

def language : LanguageDef := CollectionNamedSets.language.toOption.getD (LanguageDef.empty "")
def core : LanguageDef := (language.toCore.toOption.map (·.language)).getD (LanguageDef.empty "")
def nodes : List Pattern := [.apply "A" [], .apply "B" []]
def resultSort : TypeExpr := .base "Graph"
def queries : List (String × Pattern × Bool) :=
  [("reach", .apply "Reach" [.collection .hashSet nodes none], true),
   ("seen", .apply "Seen" [.collection .hashSet nodes none], true),
   ("anonymous-set", .collection .hashSet nodes none, false),
   ("bag-in-set-wrapper", .apply "Reach" [.collection .hashBag nodes none], false)]

#guard CollectionNamedSets.language.isOk
#guard language.toCore.isOk
#guard (CoreReduction.bareLabels core).isEmpty
#guard core.rewrites.map (·.left) == [.apply "Reach" [.collection .hashSet nodes none]]
#guard core.rewrites.map (·.right) == [.apply "Seen" [.collection .hashSet nodes none]]
#guard queries.all fun (_, term, expected) =>
  checkHasType core (fun _ => none) [] term resultSort == expected

end NamedSets

namespace IndependentMonoids
open Mettapedia.GSLT.LanguageDef.ModuleSource
open AlgebraInterpretation

def original : Value :=
  ((applyTheory CollectionIndependentMonoids.library CollectionIndependentMonoids.module ["Operations"] []).toOption.map
    Prod.snd).getD { entries := [] }

def v (label : String) : Pattern := .fvar label

def op (label : String) (first second : Pattern) : Pattern := .apply label [first,second]

def unit (label : String) : Pattern := .apply label []

def laws (label neutral : String) : List (Pattern × Pattern) :=
  [(op label (op label (v "x") (v "y")) (v "z"), op label (v "x") (op label (v "y") (v "z"))),
   (op label (v "x") (v "y"), op label (v "y") (v "x")),
   (op label (v "x") (unit neutral), v "x"),
   (op label (unit neutral) (v "x"), v "x")]

theorem inventory :
    (flattenRaw "" original).equations.map (fun row => (row.left,row.right)) =
      laws "Add" "Zero" ++ laws "Mul" "One" := by decide

def numeric : String → List Nat → Nat
  | "Add", [first,second] => first + second
  | "Mul", [first,second] => first * second
  | "One", [] => 1
  | _, _ => 0

theorem actual_source_numeric_model : SourceEquationsHold numeric original := by
  intro item member row body _
  have declared : row ∈ (flattenRaw "" original).equations :=
    List.mem_filterMap.mpr ⟨item, member, by simp [body]⟩
  have pair := List.mem_map_of_mem (f := fun row : Equation => (row.left,row.right)) declared
  rw [inventory] at pair
  simp only [laws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at pair
  rcases pair with ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ |
      ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ | ⟨left,right⟩ <;>
    rw [left,right] <;>
    simp [EquationHolds, read?, numeric, op, unit, v] <;> intro assignment <;> ac_rfl

end IndependentMonoids

end Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionRepresentationControls
