import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeConstructorReadout
import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingAuthoredReceipts

/-!
# Actual native fibres and independently typed authored source terms

The evaluator's sort and binding-parameter families are compared with their
original typed source inhabitants at every context and semantic point.
Finite distinct-name free contexts are closed and reopened with exact name
readback. Authored binder display metadata remains separate from the alpha
representative used by the semantic family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf BindingSemanticAdmission
open BindingCarrierSemantics (FreeDeclarations)
open Mettapedia.TypeTheory
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {language : LanguageDef}

noncomputable def nativeCarrierFibreEquiv (P : Base (algebra language) ⥤ Type)
    (carrier : NativeSignature.Carrier language) (point : P.Elements) :
    (carrierNativeType P carrier).decoded.obj point ≃ (meaning carrier).obj point.1 :=
  ((carrierDecodedIso P carrier).app point).toEquiv

/-- This uses the actual native decoding, not a second hand-written type
interpreter. Every source inhabitant and native inhabitant is retained. -/
noncomputable def nativeSortSourceEquiv (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    (P : Base (algebra language) ⥤ Type) (position : Fin language.types.length)
    (context : List String)
    (point : P.obj (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    (carrierNativeType P (.sort position)).decoded.obj
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context), point⟩ ≃
      Source language context language.types[position.val].name :=
  (nativeCarrierFibreEquiv P (.sort position) _).trans
    ((programsAtEquiv (algebra language) language.types[position.val].name _).trans
      (sourceEquiv admitted labels context language.types[position.val].name))

noncomputable def nativeSortNamedSourceEquiv (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    (declarations : FreeDeclarations) (distinct : (declarations.map Prod.fst).Nodup)
    (P : Base (algebra language) ⥤ Type) (position : Fin language.types.length)
    (context : List String)
    (point : P.obj (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone
      (context ++ declarations.map Prod.snd)))) :
    (carrierNativeType P (.sort position)).decoded.obj
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone
          (context ++ declarations.map Prod.snd)), point⟩ ≃
      NamedSource language declarations context language.types[position.val].name :=
  (nativeCarrierFibreEquiv P (.sort position) _).trans
    ((programsAtEquiv (algebra language) language.types[position.val].name _).trans
      (namedSourceEquiv admitted labels declarations distinct context language.types[position.val].name))

noncomputable def nativeParameterSourceEquiv (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup)
    (P : Base (algebra language) ⥤ Type)
    {parameter : TermParam} {scope : List String} {result : String}
    (parameterMeaning : ParameterMeaning parameter scope result)
    (carrier : NativeSignature.Carrier language)
    (decoded : NativeSignature.decodeParameter? language parameter = some carrier)
    (context : List String)
    (point : P.obj (Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context))) :
    (carrierNativeType P carrier).decoded.obj
        ⟨Opposite.op (ContextObject.ofList (algebra language).substitution.toClone context), point⟩ ≃
      Source language (scope ++ context) result :=
  (nativeCarrierFibreEquiv P carrier _).trans
    (nativeParameterBodyEquiv admitted labels parameterMeaning carrier decoded context)

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
