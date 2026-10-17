import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeSearch
import Mettapedia.OSLF.NativeTypes.Generation.BindingNativeDisplay

/-!
# Generated structural, dependent and cube types with native evidence

The renderer traverses the shared checked grammar. It exposes the original
constructor parameters, specified modal targets, dependent continuations and
the selected cube's formation contexts. Printed certificates certify the
displayed judgment, and do not assert closed inhabitation of an event family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : AuthoredPipeline.Installed)

def evidenceNodes {P : Presentation} : Tree P → Nat
  | .node rule children => 1 +
      ((List.finRange (P.premises rule).length).map fun position => evidenceNodes (children position)).sum

def carrierName (carrier : (NativeCubeProfile.signature installed.operational).Carrier) : String :=
  NativeDisplay.type installed.operational.nativeNames
    (NativeModalSignature.authoredType (BindingPipeline.plan installed.operational.generated)
      installed.operational.declarations installed.operational.modal carrier 0)

def formerName : NativeCubeProfile.Former installed.operational → String
  | .inl constructor => installed.operational.nativeNames.term (.inl constructor) ++ "#" ++
      toString (installed.operational.constructorOrigin constructor).2
  | .inr index => installed.operational.modalName index

def nativeNames : NativeDisplay.Names installed.symbols where
  type := fun symbol => match symbol with
    | .inl (.inl symbol) => installed.operational.nativeNames.type symbol
    | .inl (.inr (.code carrier)) => "Code[" ++ installed.carrierName carrier ++ "]"
    | .inl (.inr (.typing carrier)) => "Typing[" ++ installed.carrierName carrier ++ "]"
    | .inr impossible => nomatch impossible
  term := fun symbol => match symbol with
    | .inl (.inl symbol) => installed.operational.nativeNames.term symbol
    | .inl (.inr (.sort carrier kind)) => toString kind ++ "[" ++ installed.carrierName carrier ++ "]"
    | .inl (.inr (.former former)) => "former[" ++ installed.formerName former ++ "]"
    | .inl (.inr (.formation former)) => "formation[" ++ installed.formerName former ++ "]"
    | .inl (.inr (.starBox carrier)) => "star-is-box[" ++ installed.carrierName carrier ++ "]"
    | .inr carrier => "inject[" ++ installed.carrierName carrier ++ "]"
  predicate symbol := match symbol with
    | .inl (.inl symbol) => installed.operational.nativeNames.predicate symbol
    | .inl (.inr impossible) => nomatch impossible
    | .inr impossible => nomatch impossible

def renderNative (judgment : Judgment installed.symbols) : String :=
  NativeDisplay.judgment installed.nativeNames judgment

def renderEvidence {judgment : Judgment installed.symbols}
    (tree : Derivation installed.signature judgment) : String :=
  let certificate := Certificates.Refinement.erase tree
  installed.renderNative judgment ++ "; certificate=" ++ reprStr (installed.check certificate judgment) ++
    "; certificate nodes=" ++ toString (evidenceNodes certificate)

def structuralEvidence (constructor : installed.operational.declarations.Constructor) :=
  installed.operationalDerivation (installed.operational.constructorDerivation
    (installed.operational.declarations.structuralFormation constructor))

def responseEvidence (index : Fin installed.operational.modal.length) :=
  installed.operationalDerivation (NativeModalContinuation.genericResponseFormation
    (BindingPipeline.plan installed.operational.generated)
    installed.operational.declarations installed.operational.modal index)

def renderStructural (constructor : installed.operational.declarations.Constructor) : String :=
  "Structural " ++ installed.formerName (.inl constructor) ++ " : " ++
    installed.renderEvidence (installed.structuralEvidence constructor)

def renderResponse (index : Fin installed.operational.modal.length) : String :=
  "Response " ++ installed.formerName (.inr index) ++ " : " ++
    installed.renderEvidence (installed.responseEvidence index)

def renderProjection (projection : NativeModalSignature.Projection
    (BindingPipeline.plan installed.operational.generated) installed.operational.modal) : String :=
  installed.renderEvidence (installed.operationalDerivation
    (NativeModalSignature.projectionFormation (BindingPipeline.plan installed.operational.generated)
      installed.operational.declarations installed.operational.modal projection))

def renderCube (former : NativeCubeProfile.Former installed.operational) : String :=
  "Cube " ++ installed.formerName former ++ " : " ++
    installed.renderEvidence (installed.cubeDerivation
      (CubeNativeClosedFormation.primitiveFormation installed.vertex (.formation former)))

def formerList : List (NativeCubeProfile.Former installed.operational) :=
  (List.finRange installed.operational.declarations.headers.length).map Sum.inl ++
    (List.finRange installed.operational.modal.length).map Sum.inr

def renderGenerated : String :=
  let constructors := (List.finRange installed.operational.declarations.headers.length).map installed.renderStructural
  let responses := (List.finRange installed.operational.modal.length).map installed.renderResponse
  let projections := (NativeModalSignature.projections
    (BindingPipeline.plan installed.operational.generated) installed.operational.modal).map installed.renderProjection
  let cube := installed.formerList.map installed.renderCube
  "Language " ++ installed.operational.authored.name ++ "\n" ++
    String.intercalate "\n" (constructors ++ responses ++ projections ++ cube)

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed
