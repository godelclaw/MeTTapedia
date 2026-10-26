import Mettapedia.TypeTheory.IndexedPolynomialConstructorData
import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpaceRepresentation

/-!
# Uniform constructor-data payloads for recursive-space interpretations

Each indexed shape is exchanged for its fixed constructor-data tuple through
the proved inventory equivalence. The same target recursive-space algebra is
therefore usable at every parameter environment. Constructor equations retain
the source occurrence, data fields and the complete natural-slot child map.
Result and child indices remain computed by the original description.

These are semantic interpretations. Typed native expression reading, declaration
formation certificates and executable adapters retain their own obligations.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPolynomial.Description.DataRepresentation
open IndexedPolynomial.RecursiveSpaceRepresentation
universe u v
variable {I : Interface.{u}} {context : List I.SortCode}
variable (constructors : List (NamedConstructor I context))

abbrev Payload := Option (InventoryData constructors)

def payloadEquivalence (environment : Env I.Value context) :
    RecursivePayload (recursiveSpacePresentation constructors) environment ≃ Payload constructors :=
  Equiv.optionCongr (inventoryDataEquiv constructors environment)

variable {R : Type v}

def modelAt (M : Mettapedia.TypeTheory.RecursiveSpace.Model (Payload constructors) R)
    (environment : Env I.Value context) :
    Mettapedia.TypeTheory.RecursiveSpace.Model (RecursivePayload (recursiveSpacePresentation constructors) environment) R :=
  M.changePayload (payloadEquivalence constructors environment)

noncomputable def representation (M : Mettapedia.TypeTheory.RecursiveSpace.Model (Payload constructors) R)
    (environment : Env I.Value context) (index : I.Index) :
    Fix (inventoryPolynomial constructors) environment index ≃
      {value : R // RecursiveValid (recursiveSpacePresentation constructors)
        ((Mettapedia.TypeTheory.RecursiveSpace.equivalence (modelAt constructors M environment)).symm value) index} :=
  interpretedRepresentation (recursiveSpacePresentation constructors) environment (modelAt constructors M environment) index

noncomputable def encode (M : Mettapedia.TypeTheory.RecursiveSpace.Model (Payload constructors) R)
    {environment : Env I.Value context} {index : I.Index}
    (source : Fix (inventoryPolynomial constructors) environment index) : R :=
  interpretedEncode (recursiveSpacePresentation constructors) (modelAt constructors M environment) source

theorem encode_constructor (M : Mettapedia.TypeTheory.RecursiveSpace.Model (Payload constructors) R)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (inventoryPolynomial constructors).Shape environment index)
    (children : ∀ position, Fix (inventoryPolynomial constructors) environment ((inventoryPolynomial constructors).next shape position)) :
    encode constructors M (Fix.roll shape children) =
      M.construct shape.1.val (some ⟨shape.1, dataFromShape (constructors.get shape.1).body shape.2⟩)
        (((positions (recursiveSpacePresentation constructors)).coding shape).extend M.bottom
          (fun position => encode constructors M (children position))) :=
  interpretedEncode_constructor (recursiveSpacePresentation constructors) (modelAt constructors M environment) shape children

#print axioms payloadEquivalence
#print axioms modelAt
#print axioms representation
#print axioms encode_constructor
end Mettapedia.TypeTheory.IndexedPolynomial.Description.DataRepresentation
