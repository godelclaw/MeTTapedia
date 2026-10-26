import Mettapedia.TypeTheory.IndexedPolynomialDataRepresentation
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
import Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

/-!
# Constructor-data and parameter-context controls

The actual Vector description retains its length and head, computes the
successor result index and recovers the original child index. A wrong result
index is refused. A parameter-indexed Boolean family uses one fixed target
algebra across two environments; its data tuple agrees while the required
index changes. The context remains part of the validity contract.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.ConstructorDataControls
open Mettapedia.TypeTheory
open IndexedPolynomial Description IndexedInductiveNatVec

noncomputable def consData (length : Natural.Carrier) (head : Bool) : ConstructorData (Vectors.consCode Bool) :=
  (length, head, PUnit.unit)

theorem cons_data_index (length : Natural.Carrier) (head : Bool) :
    dataResultIndex (Vectors.consCode Bool) PUnit.unit (consData length head) = Natural.succ length := rfl

theorem cons_child_index (length : Natural.Carrier) (head : Bool) :
    dataRecursiveIndexAt (Vectors.consCode Bool) PUnit.unit (consData length head) (0 : Fin 1) = length := rfl

theorem cons_data_roundtrip (length : Natural.Carrier) (head : Bool) :
    constructorDataEquiv (Vectors.consCode Bool) PUnit.unit
      ((constructorDataEquiv (Vectors.consCode Bool) PUnit.unit).symm (consData length head)) = consData length head :=
  (constructorDataEquiv (Vectors.consCode Bool) PUnit.unit).apply_symm_apply _

theorem wrong_cons_index_refused :
    ¬ ∃ shape : Shape (Vectors.consCode Bool) PUnit.unit Natural.zero,
      dataFromShape (Vectors.consCode Bool) shape = consData Natural.zero true := by
  intro present
  exact Natural.succ_ne_zero Natural.zero ((realizes_data_iff _ _ _ _).mp present)

noncomputable abbrev vectorDataPayload := DataRepresentation.Payload (Vectors.constructors Bool)
noncomputable def vectorFiller : Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.Relation vectorDataPayload := fun _ _ => False
noncomputable def vectorModel := Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.model vectorFiller
noncomputable def vectorRepresentation := DataRepresentation.representation (Vectors.constructors Bool) vectorModel PUnit.unit (Natural.succ Natural.zero)
noncomputable def singleton := Vectors.cons true Vectors.nil

theorem singleton_roundtrip : vectorRepresentation.symm (vectorRepresentation singleton) = singleton :=
  vectorRepresentation.symm_apply_apply singleton

/- A nonrecursive parameter-indexed Boolean family uses the actual Vector
index-expression interpreter. Its payload type is fixed while its valid
result index changes with the parameter environment. -/
noncomputable def parameterCode : Code (Vectors.interface Bool) [.length] :=
  .data .payload (.result (.variable (.there .here)))

noncomputable def parameterConstructors : List (NamedConstructor (Vectors.interface Bool) [.length]) :=
  [⟨"ParameterValue", parameterCode⟩]

noncomputable def parameterEnvironment (length : Natural.Carrier) : Env (Vectors.interface Bool).Value [.length] :=
  (length, PUnit.unit)

noncomputable def parameterData : ConstructorData parameterCode := (true, PUnit.unit)

theorem parameter_index (length : Natural.Carrier) :
    dataResultIndex parameterCode (parameterEnvironment length) parameterData = length := rfl

theorem changed_parameter_changes_index :
    dataResultIndex parameterCode (parameterEnvironment Natural.zero) parameterData ≠
      dataResultIndex parameterCode (parameterEnvironment (Natural.succ Natural.zero)) parameterData := by
  exact fun same => Natural.succ_ne_zero Natural.zero same.symm

theorem wrong_parameter_index_refused :
    ¬ ∃ shape : Shape parameterCode (parameterEnvironment (Natural.succ Natural.zero)) Natural.zero,
      dataFromShape parameterCode shape = parameterData := by
  intro present
  exact Natural.succ_ne_zero Natural.zero ((realizes_data_iff _ _ _ _).mp present)

noncomputable def parameterFiller : Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.Relation (DataRepresentation.Payload parameterConstructors) :=
  fun _ _ => True
noncomputable def parameterModel := Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.model parameterFiller

noncomputable def modelAtZero := DataRepresentation.modelAt parameterConstructors parameterModel (parameterEnvironment Natural.zero)
noncomputable def modelAtOne := DataRepresentation.modelAt parameterConstructors parameterModel (parameterEnvironment (Natural.succ Natural.zero))

theorem both_models_retain_bottom : modelAtZero.bottom = parameterModel.bottom ∧ modelAtOne.bottom = parameterModel.bottom :=
  ⟨rfl, rfl⟩

noncomputable def sharedData : DataRepresentation.Payload parameterConstructors :=
  some ⟨⟨0, by decide⟩, parameterData⟩

theorem shared_native_constructor :
    modelAtZero.construct 0
      ((DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment Natural.zero)).symm sharedData)
      (fun _ => parameterModel.bottom) =
    modelAtOne.construct 0
      ((DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment (Natural.succ Natural.zero))).symm sharedData)
      (fun _ => parameterModel.bottom) := by
  change parameterModel.construct 0
    ((DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment Natural.zero))
      ((DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment Natural.zero)).symm sharedData)) _ =
    parameterModel.construct 0
    ((DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment (Natural.succ Natural.zero)))
      ((DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment (Natural.succ Natural.zero))).symm sharedData)) _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem closed_recursive_data_coherence :
    dataRecursiveIndexAt (Vectors.consCode Bool) PUnit.unit
      (dataFromShape (Vectors.consCode Bool)
        (shapeFromData (Vectors.consCode Bool) PUnit.unit (consData Natural.zero true))) (0 : Fin 1) =
    recursiveIndexAt (Vectors.consCode Bool)
      (shapeFromData (Vectors.consCode Bool) PUnit.unit (consData Natural.zero true)) (0 : Fin 1) :=
  recursive_index_from_data (Vectors.consCode Bool) _ _

noncomputable def payloadModelWitness :=
  Mettapedia.TypeTheory.RecursiveSpace.Model.changePayload parameterModel
    (DataRepresentation.payloadEquivalence parameterConstructors (parameterEnvironment Natural.zero))

#print axioms cons_data_roundtrip
#print axioms wrong_cons_index_refused
#print axioms singleton_roundtrip
#print axioms changed_parameter_changes_index
#print axioms wrong_parameter_index_refused
end Mettapedia.GSLT.LanguageDef.IndexedInductive.ConstructorDataControls

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.ConstructorDataControls
open Mettapedia.TypeTheory
open IndexedPolynomial Description IndexedInductiveNatVec

noncomputable def consShape :
    (inventoryPolynomial (Vectors.constructors Bool)).Shape PUnit.unit (Natural.succ Natural.zero) :=
  ⟨⟨1, by decide⟩, shapeFromData (Vectors.consCode Bool) PUnit.unit (consData Natural.zero true)⟩

noncomputable def oneChild : ∀ position,
    Fix (inventoryPolynomial (Vectors.constructors Bool)) PUnit.unit
      ((inventoryPolynomial (Vectors.constructors Bool)).next consShape position) := by
  intro position
  change Option PEmpty at position
  cases position with
  | none => exact Vectors.nil
  | some impossible => exact PEmpty.elim impossible

theorem data_constructor_clause :
    DataRepresentation.encode (Vectors.constructors Bool) vectorModel (Fix.roll consShape oneChild) =
      vectorModel.construct 1 (some ⟨⟨1, by decide⟩, consData Natural.zero true⟩)
        (((IndexedPolynomial.RecursiveSpaceRepresentation.positions (recursiveSpacePresentation (Vectors.constructors Bool))).coding consShape).extend
          vectorModel.bottom (fun position => DataRepresentation.encode (Vectors.constructors Bool) vectorModel (oneChild position))) :=
  DataRepresentation.encode_constructor (Vectors.constructors Bool) vectorModel consShape oneChild

#print axioms data_constructor_clause
end Mettapedia.GSLT.LanguageDef.IndexedInductive.ConstructorDataControls
