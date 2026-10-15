import Mettapedia.OSLF.NativeTypes.Generation.BindingNativeSearch
import Mettapedia.OSLF.NativeTypes.Generation.ConstructorOrigins
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalContinuation
import Mettapedia.OSLF.NativeTypes.Certificates.Display

/-!
# Authored native types and their checked declaration certificates

This view prints the common dependent grammar consumed by native checking.
Constructor labels, scoped argument types and modal parameter names come from
the installed declarations. Certificate acceptance denotes formation of the
printed judgment; it does not assert that an arbitrary type is inhabited.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable (installed : BindingPipeline.Installed)

def modalName (index : Fin installed.modal.length) : String :=
  let schema := (installed.modal[index]).origin
  let authored := Modal.NativeEventDeclarations.schema (plan installed.generated) schema
  authored.declaration.rule.name ++ "#" ++ toString authored.declaration.declarationIndex ++
    "@" ++ reprStr authored.position

def nativeNames : NativeDisplay.Names installed.symbols where
  type := fun symbol => match symbol with
    | .inl position => (plan installed.generated).snapshot.language.types[position.val].name
    | .inr (.input index) => "Input[" ++ installed.modalName index ++ "]"
    | .inr (.event index) => "Event[" ++ installed.modalName index ++ "]"
  term := fun symbol => match symbol with
    | .inl position =>
        (plan installed.generated).snapshot.language.terms[(installed.declarations.origin position).val].label
    | .inr (.source index) => "source[" ++ installed.modalName index ++ "]"
    | .inr (.target index) => "target[" ++ installed.modalName index ++ "]"
    | .inr (.focus index) => "focus[" ++ installed.modalName index ++ "]"
    | .inr (.rely index position) =>
        "rely[" ++ installed.modalName index ++ ":" ++ installed.modal[index].rely[position].slot.name ++ "]"
    | .inr (.matched index position) =>
        "matched[" ++ installed.modalName index ++ ":" ++ installed.modal[index].matched[position].slot.name ++ "]"
  predicate symbol := match symbol with
    | .inl impossible => nomatch impossible
    | .inr impossible => nomatch impossible

def renderNative (judgment : Judgment installed.symbols) : String :=
  NativeDisplay.judgment installed.nativeNames judgment

def renderConstructor (constructor : installed.declarations.Constructor) : String :=
  let symbol := Sum.inl constructor
  let judgment := Judgment.type (installed.signature.termParameters symbol)
    (installed.signature.termResult symbol)
  let certificate := Certificates.Refinement.erase (installed.formation.termResult symbol)
  installed.nativeNames.term symbol ++ "#" ++ toString (installed.constructorOrigin constructor).2 ++
    " : " ++ installed.renderNative judgment ++
    "; formation certificate=" ++ reprStr (installed.check certificate judgment)

def renderProjection (projection : NativeModalSignature.Projection (plan installed.generated) installed.modal) : String :=
  let judgment := Judgment.term
    (NativeModalSignature.eventContext (plan installed.generated) installed.declarations installed.modal projection.index)
    (NativeModalSignature.projection (plan installed.generated) installed.declarations installed.modal projection)
    (NativeModalSignature.authoredType (plan installed.generated) installed.declarations installed.modal
      (NativeModalSignature.projectionCarrier (plan installed.generated) installed.modal projection) 2)
  let certificate := NativeModalSignature.projectionCertificate
    (plan installed.generated) installed.declarations installed.modal projection
  installed.renderNative judgment ++ "; certificate=" ++ reprStr (installed.check certificate judgment)

/-- The continuation is an ordinary native function to Prop. Its guard reads
the specified target projection of the complete dependent event. -/
def renderResponse (index : Fin installed.modal.length) : String :=
  let response := NativeModalContinuation.responseType
    (plan installed.generated) installed.declarations installed.modal index
    (TermExpr.var (n := 2) 1) (TermExpr.var (n := 2) 0)
  let context := NativeModalContinuation.responseContext
    (plan installed.generated) installed.declarations installed.modal index
  let certificate := Certificates.Refinement.erase
    (NativeModalContinuation.genericResponseFormation
      (plan installed.generated) installed.declarations installed.modal index)
  let judgment := Judgment.type context response
  installed.renderNative judgment ++ "; formation certificate=" ++ reprStr (installed.check certificate judgment)

def renderGenerated : String :=
  let constructors := (List.finRange installed.declarations.headers.length).map installed.renderConstructor
  let projections := (NativeModalSignature.projections (plan installed.generated) installed.modal).map installed.renderProjection
  let responses := (List.finRange installed.modal.length).map installed.renderResponse
  "Language " ++ (plan installed.generated).snapshot.language.name ++ "\n" ++
    String.intercalate "\n" (constructors ++ projections ++ responses)

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed
