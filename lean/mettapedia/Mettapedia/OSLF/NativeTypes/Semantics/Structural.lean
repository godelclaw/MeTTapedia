import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction
import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeTransport
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

open Mettapedia.OSLF.Framework

/-!
# Generated structural outputs in the native equation quotient

The output predicate is the quotient image of typed constructor introductions
with ordered interpreted inputs. Its dependent family retains those actual
introductions. Comparison with the generated code follows from the model's
primitive equation law; it is not an interpretation field.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated StructuralInputs structuralDeclaration structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes (Model)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction (EquationsInterpreted OperationClosed equation_sort_transport)
open GSLTTypeSynthesis
open ModalHypercube (HSort)

def theory (generated : Generated) (bound : List TypeExpr) (carrier : TypeExpr) :=
  GeneralOccurrenceSemantics.gslt generated.plan bound carrier

/-- The actual sort subobject is a canonical native predicate after the model
has interpreted the primitive equation generators. -/
def sortPredicate {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (carrier : TypeExpr) (sort : HSort) : EquationPredicate (theory generated bound carrier) where
  val := (model bound).sortDomain carrier sort
  property := by
    intro first second related
    exact equation_sort_transport equations bound carrier sort related

/-- These certificates concern the constructor introduction itself, before
passing to equation classes or reading a generated type code. -/
structure Introduction {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) where
  value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
    (structuralDeclaration generated index)
  output : (model bound).sortDomain (.base (structuralDeclaration generated index).category)
    (structuralOutputSort generated index) value.pattern
  arguments : ∀ position,
    (model bound).sortDomain (structuralDeclaration generated index).params[position].typeExpr
      (structuralInputSort generated index position)
      (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt)) ∧
    (inputs position).meaning
      (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))

def quotientImage {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (semanticTerm : Quotient (theory generated bound (.base (structuralDeclaration generated index).category)).equations) :
    Prop :=
  ∃ introduction : Introduction model bound index inputs,
    semanticTerm = Quotient.mk _ introduction.value.pattern

def predicate {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) :
    EquationPredicate (theory generated bound (.base (structuralDeclaration generated index).category)) :=
  liftPredicate _ (quotientImage model bound index inputs)

def nativeType {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) :
    GSLTNativeType (theory generated bound (.base (structuralDeclaration generated index).category)) where
  sort := ()
  pred := predicate model bound index inputs

/-- Full structural support retains the typed constructor and each ordered
input certificate, together with its equality to the requested equation class. -/
def Family {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) : Type :=
  { introduction : Introduction model bound index inputs //
    Quotient.mk (theory generated bound (.base (structuralDeclaration generated index).category)).equations term =
      Quotient.mk _ introduction.value.pattern }

def Comprehension {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index) : Type :=
  (term : Pattern) × Family model bound index inputs term

theorem family_support {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) : Nonempty (Family model bound index inputs term) ↔
      predicate model bound index inputs term := by
  constructor
  · rintro ⟨⟨introduction, equal⟩⟩
    exact ⟨introduction, equal⟩
  · rintro ⟨introduction, equal⟩
    exact ⟨⟨introduction, equal⟩⟩

theorem quotient_membership {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) :
    descendPredicate _ (predicate model bound index inputs) (Quotient.mk _ term) ↔
      quotientImage model bound index inputs (Quotient.mk _ term) := Iff.rfl

theorem native_bounded {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} {inputs : StructuralInputs generated bound index}
    {term : Pattern} (inhabited : predicate model bound index inputs term) :
    (model bound).sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) term := by
  obtain ⟨introduction, equal⟩ := inhabited
  exact (equation_sort_transport equations bound _ _ (Quotient.exact equal)).mpr introduction.output

theorem native_carrier_bounded {generated : Generated} {model : Model generated}
    (equations : EquationsInterpreted model) {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length} {inputs : StructuralInputs generated bound index}
    {term : Pattern} (inhabited : predicate model bound index inputs term) :
    HasType generated.snapshot.language generated.snapshot.free bound term
      (.base (structuralDeclaration generated index).category) :=
  (model bound).carrierBounded _ _ _ (native_bounded equations inhabited)

theorem generated_native_comparison {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model bound) index inputs).meaning term ↔
      predicate model bound index inputs term := by
  rw [Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structural_image_exact]
  constructor
  · rintro ⟨output, _, value, related, arguments⟩
    exact ⟨⟨value, (equation_sort_transport equations bound _ _ related).mp output, arguments⟩,
      Quotient.sound related⟩
  · rintro ⟨introduction, equal⟩
    have related := Quotient.exact equal
    have output := (equation_sort_transport equations bound _ _ related).mpr introduction.output
    exact ⟨output, (model bound).carrierBounded _ _ _ output, introduction.value, related,
      introduction.arguments⟩

theorem generated_family_comparison {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model bound) index inputs).meaning term ↔
      Nonempty (Family model bound index inputs term) :=
  (generated_native_comparison model equations bound index inputs term).trans
    (family_support model bound index inputs term).symm

theorem native_satisfaction {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) :
    (gsltOSLF (theory generated bound (.base (structuralDeclaration generated index).category))).satisfies
      (S := ()) term (nativeType model bound index inputs).pred ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode (model bound) index inputs).meaning term :=
  (generated_native_comparison model equations bound index inputs term).symm

/-- A successfully emitted constructor code is compared at its actual computed
output slot. The generator's admission and catalogue checks remain premises. -/
theorem compiled_structural_native_comparison {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    {emitted : (sort : HSort) × Mettapedia.OSLF.NativeTypes.Modal.Rules.TypeCode generated.plan bound
      (.base (structuralDeclaration generated index).category) sort}
    (compiled : generated.structuralFormer? bound index
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictStructuralInputs (model bound) inputs) = some emitted)
    (term : Pattern) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictCode (model bound) emitted.2).meaning term ↔
      predicate model bound index inputs term := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.structuralFormer? at compiled
  split at compiled
  · cases compiled
    exact generated_native_comparison model equations bound index inputs term
  · cases compiled

theorem compiled_structural_family_comparison {generated : Generated} (model : Model generated)
    (equations : EquationsInterpreted model) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    {emitted : (sort : HSort) × Mettapedia.OSLF.NativeTypes.Modal.Rules.TypeCode generated.plan bound
      (.base (structuralDeclaration generated index).category) sort}
    (compiled : generated.structuralFormer? bound index
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictStructuralInputs (model bound) inputs) = some emitted)
    (term : Pattern) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictCode (model bound) emitted.2).meaning term ↔
      Nonempty (Family model bound index inputs term) :=
  (compiled_structural_native_comparison model equations bound index inputs compiled term).trans
    (family_support model bound index inputs term).symm

theorem comprehension_exact {generated : Generated} (model : Model generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (term : Pattern) :
    (∃ inhabitant : Comprehension model bound index inputs, inhabitant.1 = term) ↔
      predicate model bound index inputs term := by
  constructor
  · rintro ⟨⟨source, family⟩, equal⟩
    change source = term at equal
    subst source
    exact (family_support model bound index inputs term).mp ⟨family⟩
  · intro inhabited
    obtain ⟨family⟩ := (family_support model bound index inputs term).mpr inhabited
    exact ⟨⟨term, family⟩, rfl⟩

def introduce {generated : Generated} {model : Model generated} (closed : OperationClosed model)
    {bound : List TypeExpr} (index : Fin generated.snapshot.language.terms.length)
    (inputs : StructuralInputs generated bound index)
    (value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index))
    (arguments : ∀ position,
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictCode (model bound) (inputs position)).meaning
        (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))) :
    Family model bound index inputs value.pattern :=
  ⟨⟨value, closed bound index value (fun position => (arguments position).1), arguments⟩, rfl⟩

theorem introduction_retains_value {generated : Generated} {model : Model generated}
    (closed : OperationClosed model) {bound : List TypeExpr}
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index))
    (arguments : ∀ position,
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.restrictCode (model bound) (inputs position)).meaning
        (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))) :
    (introduce closed index inputs value arguments).val.value = value := rfl

#print axioms generated_native_comparison
#print axioms generated_family_comparison
#print axioms native_satisfaction
#print axioms native_carrier_bounded
#print axioms compiled_structural_native_comparison
#print axioms comprehension_exact

end Mettapedia.OSLF.NativeTypes.Semantics.Structural
