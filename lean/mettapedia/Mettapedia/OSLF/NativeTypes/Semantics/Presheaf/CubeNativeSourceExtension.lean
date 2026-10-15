import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceCarriers

/-!
# Source-preserving native cube model with an actual operational injection

The old source model, the independent free code/kinding model and source-to-code
injections use one native alphabet and one base category. Every generated raw
header and result is compared with the common native interpreter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceExtension

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeSemanticFamilies CubeNativeSemanticOperations CubeNativeSemanticArguments

universe u
variable {S : Symbols} {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable {bound : Nat} (source : Signature S)
    (carriers : CubeNativeExtension.SourceCarriers source D bound)
    (sourceModel : ModelData S W) (realized : SignatureRealization sourceModel source)
    (vertex : CubeEnrichment.Vertex D)

noncomputable section

abbrev sourceOperational := CubeNativeSourceCarriers.operational source carriers sourceModel realized

def injectionModel : ModelData (CubeNativeExtension.injectionSymbols D) W where
  typeParameters symbol := nomatch symbol
  typeFamily symbol := nomatch symbol
  termParameters carrier := CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier
  termType carrier := codeAt (sourceOperational source carriers sourceModel realized) carrier
    (CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier).1
  termValue carrier := codeSection (sourceOperational source carriers sourceModel realized) carrier
    (CubeNativeSourceCarriers.injectionName source carriers sourceModel realized carrier)
  predicateParameters symbol := nomatch symbol
  predicateValue symbol := nomatch symbol

abbrev cubeModel := CubeNativePresheafModel.model (sourceOperational source carriers sourceModel realized) vertex

abbrev coreModel := NativeModelSum.model sourceModel (cubeModel source carriers sourceModel realized vertex)

def model : ModelData (CubeNativeExtension.symbols S D) W :=
  NativeModelSum.model (coreModel source carriers sourceModel realized vertex)
    (injectionModel source carriers sourceModel realized)

theorem core_realization : SignatureRealization (coreModel source carriers sourceModel realized vertex)
    (CubeNativeExtension.core source vertex) :=
  NativeModelSum.realization sourceModel (cubeModel source carriers sourceModel realized vertex)
    source (CubeNativeDeclarations.signature vertex) realized
    (CubeNativePresheafRealization.realization (sourceOperational source carriers sourceModel realized) vertex)

theorem source_type_read {n : Nat} (context : Scope W n) (expression : TypeExpr S n) :
    (model source carriers sourceModel realized vertex).evaluateType context
      (SignatureSum.typeLeft (SignatureSum.typeLeft expression)) = sourceModel.evaluateType context expression :=
  (NativeModelSum.type_left (coreModel source carriers sourceModel realized vertex)
    (injectionModel source carriers sourceModel realized) context _).trans
      (NativeModelSum.type_left sourceModel (cubeModel source carriers sourceModel realized vertex) context expression)

theorem source_term_read {n : Nat} (context : Scope W n) (expression : TermExpr S n) :
    (model source carriers sourceModel realized vertex).evaluateTerm context
      (SignatureSum.termLeft (SignatureSum.termLeft expression)) = sourceModel.evaluateTerm context expression :=
  (NativeModelSum.term_left (coreModel source carriers sourceModel realized vertex)
    (injectionModel source carriers sourceModel realized) context _).trans
      (NativeModelSum.term_left sourceModel (cubeModel source carriers sourceModel realized vertex) context expression)

theorem cube_type_read {n : Nat} (context : Scope W n)
    (expression : TypeExpr (CubeNativeDeclarations.symbols D) n) :
    (model source carriers sourceModel realized vertex).evaluateType context
      (SignatureSum.typeLeft (SignatureSum.typeRight expression)) =
      (cubeModel source carriers sourceModel realized vertex).evaluateType context expression :=
  (NativeModelSum.type_left (coreModel source carriers sourceModel realized vertex)
    (injectionModel source carriers sourceModel realized) context _).trans
      (NativeModelSum.type_right sourceModel (cubeModel source carriers sourceModel realized vertex) context expression)

theorem cube_term_read {n : Nat} (context : Scope W n)
    (expression : TermExpr (CubeNativeDeclarations.symbols D) n) :
    (model source carriers sourceModel realized vertex).evaluateTerm context
      (SignatureSum.termLeft (SignatureSum.termRight expression)) =
      (cubeModel source carriers sourceModel realized vertex).evaluateTerm context expression :=
  (NativeModelSum.term_left (coreModel source carriers sourceModel realized vertex)
    (injectionModel source carriers sourceModel realized) context _).trans
      (NativeModelSum.term_right sourceModel (cubeModel source carriers sourceModel realized vertex) context expression)

theorem sourceCarrier_read (carrier : D.Carrier) :
    (model source carriers sourceModel realized vertex).evaluateType CubeNativeSemanticFamilies.emptyScope
      (CubeNativeExtension.sourceType source bound carriers carrier) =
      some (CubeNativeSourceCarriers.carrierType source carriers sourceModel realized carrier) :=
  (source_type_read source carriers sourceModel realized vertex _ _).trans
    (CubeNativeSourceCarriers.carrierType_read source carriers sourceModel realized carrier)

theorem injectionContext_read (carrier : D.Carrier) :
    (model source carriers sourceModel realized vertex).evaluateContext
      (CubeNativeExtension.injectionContext source bound carriers carrier) =
      some (CubeNativeSourceCarriers.injectionScope source carriers sourceModel realized carrier) :=
  (model source carriers sourceModel realized vertex).evaluateContext_snoc .nil _ _ _ rfl
    (sourceCarrier_read source carriers sourceModel realized vertex carrier)

theorem enrichedCode_read {n : Nat} (context : Scope W n) (carrier : D.Carrier) :
    (model source carriers sourceModel realized vertex).evaluateType context
      (CubeNativeExtension.codeType S D carrier n) =
      some (codeAt (sourceOperational source carriers sourceModel realized) carrier context.1) :=
  (cube_type_read source carriers sourceModel realized vertex context (CubeNativeDeclarations.codeType carrier n)).trans
    (CubeNativePresheafReadout.code_read (sourceOperational source carriers sourceModel realized) vertex context carrier)

/-- The injected old-carrier term is interpreted by the natural free-code
injection; every source declaration and every generated cube rule remains. -/
theorem realization (positive : 0 < bound) :
    SignatureRealization (model source carriers sourceModel realized vertex)
      (CubeNativeExtension.signature source vertex bound carriers positive) where
  typeHeader symbol := by
    cases symbol with
    | inl symbol =>
        exact (NativeModelSum.context_left (coreModel source carriers sourceModel realized vertex)
          (injectionModel source carriers sourceModel realized) _).trans
            ((core_realization source carriers sourceModel realized vertex).typeHeader symbol)
    | inr impossible => exact nomatch impossible
  termHeader symbol := by
    cases symbol with
    | inl symbol =>
        exact (NativeModelSum.context_left (coreModel source carriers sourceModel realized vertex)
          (injectionModel source carriers sourceModel realized) _).trans
            ((core_realization source carriers sourceModel realized vertex).termHeader symbol)
    | inr carrier => exact injectionContext_read source carriers sourceModel realized vertex carrier
  predicateHeader symbol := by
    cases symbol with
    | inl symbol =>
        exact (NativeModelSum.context_left (coreModel source carriers sourceModel realized vertex)
          (injectionModel source carriers sourceModel realized) _).trans
            ((core_realization source carriers sourceModel realized vertex).predicateHeader symbol)
    | inr impossible => exact nomatch impossible
  termResult symbol := by
    cases symbol with
    | inl symbol =>
        exact (NativeModelSum.type_left (coreModel source carriers sourceModel realized vertex)
          (injectionModel source carriers sourceModel realized) _ _).trans
            ((core_realization source carriers sourceModel realized vertex).termResult symbol)
    | inr carrier => exact enrichedCode_read source carriers sourceModel realized vertex _ carrier

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceExtension
