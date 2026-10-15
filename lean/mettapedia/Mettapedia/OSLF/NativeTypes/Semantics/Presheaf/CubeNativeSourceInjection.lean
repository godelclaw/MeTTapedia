import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceExtension
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticVectors

/-!
# Executing the common native source-to-code operation preserves its value

The supplied old-carrier section gives the actual primitive substitution.
The original native evaluator reads the injection as the freely adjoined code
of that exact section, at every world and through restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceInjection

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeSemanticFamilies CubeNativeSemanticOperations CubeNativeSemanticArguments
open CubeNativeSourceExtension

universe u
variable {S : Symbols} {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable {bound : Nat} (source : Signature S)
    (carriers : CubeNativeExtension.SourceCarriers source D bound)
    (sourceModel : ModelData S W) (realized : SignatureRealization sourceModel source)
    (vertex : CubeEnrichment.Vertex D)

noncomputable section

abbrev sourceAt (carrier : D.Carrier) (P : Wᵒᵖ ⥤ Type u) :=
  (CubeNativeSourceCarriers.carrierType source carriers sourceModel realized carrier).reindex ((NativeModel W).toEmpty P)

def inputMap {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (sourceAt source carriers sourceModel realized carrier P).decoded.sections) :
    P ⟶ (CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier).1 where
  app world := TypeCat.ofHom fun argument => ⟨PUnit.unit,value.val ⟨world,argument⟩⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro argument
    change (⟨PUnit.unit,value.val ⟨second,P.map arrow argument⟩⟩ :
      (CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier).1.obj second) =
      ⟨PUnit.unit,(CubeNativeSourceCarriers.carrierType source carriers sourceModel realized carrier).decoded.map
        ((CubeNativeSourceCarriers.emptyElements (W := W)).map arrow)
        (value.val ⟨first,argument⟩)⟩
    exact congrArg (fun datum => (⟨PUnit.unit,datum⟩ :
      (CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier).1.obj second))
      (@value.property ⟨first,argument⟩ ⟨second,P.map arrow argument⟩ ⟨arrow,rfl⟩).symm

theorem input_component {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (sourceAt source carriers sourceModel realized carrier P).decoded.sections) (position : Fin 1) :
    (CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier).2.components
      (inputMap source carriers sourceModel realized carrier value) position =
      (⟨sourceAt source carriers sourceModel realized carrier P,value⟩ : NativeValue P) := by
  have last : position = 0 := Fin.eq_zero position
  cases last
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · rfl

def sourceValueName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (sourceAt source carriers sourceModel realized carrier P).decoded.sections) :
    P ⟶ sourceOperational source carriers sourceModel realized carrier :=
  inputMap source carriers sourceModel realized carrier value ≫
    CubeNativeSourceCarriers.sourceName source carriers sourceModel realized carrier

theorem sourceValueName_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (sourceAt source carriers sourceModel realized carrier P).decoded.sections)
    (world : Wᵒᵖ) (argument : P.obj world) :
    (sourceValueName source carriers sourceModel realized carrier value).app world argument =
      value.val ⟨world,argument⟩ := rfl

def injectedValueName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (sourceAt source carriers sourceModel realized carrier P).decoded.sections) :
    P ⟶ CubePresheafCode.presheaf (sourceOperational source carriers sourceModel realized) carrier :=
  sourceValueName source carriers sourceModel realized carrier value ≫
    CubePresheafCode.injection (sourceOperational source carriers sourceModel realized) carrier

theorem injectedValueName_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (sourceAt source carriers sourceModel realized carrier P).decoded.sections)
    (world : Wᵒᵖ) (argument : P.obj world) :
    (injectedValueName source carriers sourceModel realized carrier value).app world argument =
      .operational (value.val ⟨world,argument⟩) := rfl

/-- The actual common-grammar primitive uses the checked old-carrier section
as its argument and returns its exact operational generator code. -/
theorem evaluate_inject {n : Nat} (context : Scope W n) (carrier : D.Carrier)
    (term : TermExpr (CubeNativeExtension.symbols S D) n)
    (value : (sourceAt source carriers sourceModel realized carrier context.1).decoded.sections)
    (termRead : (model source carriers sourceModel realized vertex).evaluateTerm context term =
      some ⟨sourceAt source carriers sourceModel realized carrier context.1,value⟩) :
    (model source carriers sourceModel realized vertex).evaluateTerm context
      (CubeNativeExtension.inject carrier term) =
      some (codeValue (sourceOperational source carriers sourceModel realized) carrier
        (injectedValueName source carriers sourceModel realized carrier value)) := by
  have read := (model source carriers sourceModel realized vertex).evaluate_primitive context (.inr carrier)
    (fun _ => term) (inputMap source carriers sourceModel realized carrier value)
    (fun position => termRead.trans (congrArg some
      (input_component source carriers sourceModel realized carrier value position).symm))
  have substitution := CubeNativeSemanticVectors.codeValue_substitution
    (sourceOperational source carriers sourceModel realized) carrier
    (CubeNativeSourceCarriers.injectionName source carriers sourceModel realized carrier)
    (inputMap source carriers sourceModel realized carrier value)
  exact read.trans (congrArg some substitution)

/-- Any term interpreted by the original source evaluator can be injected
without changing its value or using a second source interpretation. -/
theorem evaluate_source_inject {n : Nat} (context : Scope W n) (carrier : D.Carrier)
    (term : TermExpr S n)
    (value : (sourceAt source carriers sourceModel realized carrier context.1).decoded.sections)
    (termRead : sourceModel.evaluateTerm context term =
      some ⟨sourceAt source carriers sourceModel realized carrier context.1,value⟩) :
    (model source carriers sourceModel realized vertex).evaluateTerm context
      (CubeNativeExtension.inject carrier
        (SignatureSum.termLeft (SignatureSum.termLeft term))) =
      some (codeValue (sourceOperational source carriers sourceModel realized) carrier
        (injectedValueName source carriers sourceModel realized carrier value)) :=
  evaluate_inject source carriers sourceModel realized vertex context carrier _ value
    ((source_term_read source carriers sourceModel realized vertex context term).trans termRead)

/-- The free injection preserves distinction between complete native source
sections, including at every generalized parameter and world. -/
theorem injectedValueName_injective {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) :
    Function.Injective (injectedValueName source carriers sourceModel realized carrier (P := P)) := by
  intro first second same
  apply (Functor.sections_ext_iff).mpr
  rintro ⟨world,argument⟩
  have read := ConcreteCategory.congr_hom (NatTrans.congr_app same world) argument
  exact CubeEnrichment.Code.operational_injective read

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceInjection
