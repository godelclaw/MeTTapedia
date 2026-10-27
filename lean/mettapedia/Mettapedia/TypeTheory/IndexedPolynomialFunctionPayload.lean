import Mettapedia.TypeTheory.FiniteConstructorEncoding
import Mettapedia.TypeTheory.IndexedPolynomialDataRepresentation
import Mettapedia.TypeTheory.RecursiveSpacePayloadMap

/-!
# Function payloads for indexed constructor inventories

The constructor-data equivalence feeds the finite handler encoding. The map
retains constructor occurrences and all data fields, and extends injectively
to the absent payload marker. These are semantic maps; native type-instance
reading and complete source guard generation remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.Description.FunctionPayload

universe u
variable {I : Interface.{u}} {context : List I.SortCode}
variable (constructors : List (NamedConstructor I context))

def signature : List (List I.SortCode) := constructors.map (fun constructor => dataSorts constructor.body)

def occurrenceEquivalence : Fin constructors.length ≃ Fin (signature constructors).length :=
  finCongr (by simp only [signature, List.length_map])

def dataEquivalence : InventoryData constructors ≃
    FiniteConstructorEncoding.Data I.Value (signature constructors) :=
  Equiv.sigmaCongr (occurrenceEquivalence constructors) (fun occurrence =>
    Equiv.cast (by
      change Env I.Value (dataSorts (constructors.get occurrence).body) =
        Env I.Value ((signature constructors).get (occurrenceEquivalence constructors occurrence))
      apply congrArg (Env I.Value)
      simp [signature, occurrenceEquivalence, finCongr]
      rfl))

theorem occurrence_preserved (data : InventoryData constructors) :
    (dataEquivalence constructors data).1.val = data.1.val := rfl

abbrev Payload := FiniteConstructorEncoding.Payload I.Value (signature constructors)

def encode (data : InventoryData constructors) : Payload constructors :=
  FiniteConstructorEncoding.encode I.Value (signature constructors) (dataEquivalence constructors data)

theorem encode_injective : Function.Injective (encode constructors) :=
  (FiniteConstructorEncoding.encode_injective I.Value (signature constructors)).comp
    (dataEquivalence constructors).injective

def encodeOption (data : Option (InventoryData constructors)) : Payload constructors :=
  FiniteConstructorEncoding.encodeOption I.Value (signature constructors)
    ((Equiv.optionCongr (dataEquivalence constructors)) data)

theorem encodeOption_injective : Function.Injective (encodeOption constructors) :=
  (FiniteConstructorEncoding.encodeOption_injective I.Value (signature constructors)).comp
    (Equiv.optionCongr (dataEquivalence constructors)).injective

def encodeShape (environment : Env I.Value context)
    (payload : RecursiveSpaceRepresentation.RecursivePayload
      (recursiveSpacePresentation constructors) environment) : Payload constructors :=
  encodeOption constructors (DataRepresentation.payloadEquivalence constructors environment payload)

theorem encodeShape_injective (environment : Env I.Value context) :
    Function.Injective (encodeShape constructors environment) :=
  (encodeOption_injective constructors).comp
    (DataRepresentation.payloadEquivalence constructors environment).injective

noncomputable def representation : InventoryData constructors ≃
    {payload : Payload constructors //
      FiniteConstructorEncoding.Valid I.Value (signature constructors) payload} :=
  (dataEquivalence constructors).trans
    (FiniteConstructorEncoding.representation I.Value (signature constructors))

def Family (environment : Env I.Value context) (index : I.Index) :=
  {target : RecursiveSpace.Tree (Payload constructors) //
    ∃ original, RecursiveSpaceRepresentation.RecursiveValid
      (recursiveSpacePresentation constructors) original index ∧
      RecursiveSpace.mapPayload (encodeShape constructors environment) original = target}

noncomputable def familyEquivalence (environment : Env I.Value context) (index : I.Index) :
    RecursiveSpaceRepresentation.RecursiveFamily (recursiveSpacePresentation constructors) environment index ≃
      Family constructors environment index :=
  Equiv.ofBijective (fun original =>
    ⟨RecursiveSpace.mapPayload (encodeShape constructors environment) original.val,
      original.val, original.property, rfl⟩)
    ⟨fun first second same => Subtype.ext
      (RecursiveSpace.mapPayload_injective (encodeShape constructors environment)
        (encodeShape_injective constructors environment) (congrArg Subtype.val same)), by
      intro target
      obtain ⟨original, valid, same⟩ := target.property
      exact ⟨⟨original, valid⟩, Subtype.ext same⟩⟩

noncomputable def familyRepresentation (environment : Env I.Value context) (index : I.Index) :
    Fix (inventoryPolynomial constructors) environment index ≃ Family constructors environment index :=
  (RecursiveSpaceRepresentation.recursiveSpaceRepresentation
    (recursiveSpacePresentation constructors) environment index).trans
    (familyEquivalence constructors environment index)

#print axioms dataEquivalence
#print axioms encodeShape_injective
#print axioms representation
#print axioms familyRepresentation

end Mettapedia.TypeTheory.IndexedPolynomial.Description.FunctionPayload
