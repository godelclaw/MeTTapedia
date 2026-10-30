import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaPackage
import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaDataControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackageControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Nat/Vec package observations against an independent declaration library

The authored vector generates its declarations, eliminator and both complete
computation judgments. The comparison includes their contexts and result
types. The executable packet uses the existing Pattern and CeTTa codecs;
inspection is data processing, not native iota admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaPackageControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedInductive IndexedInductive.Guest
open Declaration Declaration.IndexedFamily
open InductiveMeTTaData InductiveMeTTaPackage IndexedNatVecSourceControls

noncomputable def vectorGenerated := generated (TypedControls.indexSyntax Bool)
  (DeclarationControls.vectorParameters Bool) DeclarationControls.vectorNames
  (IndexedInductiveNatVec.Vectors.admitted Bool)

def vectorReference :=
  (NativeNaturalVectorFamilies.declarations.drop 4,
    Data.schemaRows (NativeNaturalVectorFamilies.Checking.schemas.drop 2))

/-- The independent library has the same family, constructor, eliminator,
context and result-type data. Receipt proof identity is not compared. -/
theorem vector_generated_reference : vectorGenerated = vectorReference := by
  apply Prod.ext
  · exact DeclarationControls.vector_entries_reference Bool
  · decide +kernel

theorem builder_reference :
    fromBuilder Bool names (TypedControls.indexSyntax Bool)
      (DeclarationControls.vectorParameters Bool) DeclarationControls.vectorNames
      (familyData natural) (familyData (vec "n" "head" "tail")) = some vectorReference := by
  simp only [fromBuilder, InductiveMeTTaDataControls.builder_admits_vector,
    Bind.bind, Option.bind, pure]
  exact congrArg some vector_generated_reference

theorem block_reference :
    fromBlock Bool names (TypedControls.indexSyntax Bool)
      (DeclarationControls.vectorParameters Bool) DeclarationControls.vectorNames
      (blockData natural) (blockData (vec "n" "head" "tail")) = some vectorReference := by
  rw [authoring_forms_agree]
  exact builder_reference

theorem renamed_block_reference :
    fromBlock Bool names (TypedControls.indexSyntax Bool)
      (DeclarationControls.vectorParameters Bool) DeclarationControls.vectorNames
      (blockData natural) (blockData (vec "length" "element" "tail")) = some vectorReference := by
  unfold fromBlock
  rw [InductiveMeTTaDataControls.alpha_renaming_preserves_admission,
    InductiveMeTTaDataControls.builder_admits_vector]
  exact congrArg some vector_generated_reference

theorem capture_refused :
    fromBlock Bool names (TypedControls.indexSyntax Bool)
      (DeclarationControls.vectorParameters Bool) DeclarationControls.vectorNames
      (blockData natural) (blockData (vec "n" "n" "tail")) = none := by
  simp only [fromBlock, InductiveMeTTaDataControls.captured_index_refused, Bind.bind, Option.bind]

theorem vector_receipts {row : Data.Row Tower.Head} (member : row ∈ vectorGenerated.2) :
    Nonempty (ComputationAuthority.ProofRelevantStepReceipt Tower.rules
      (Package.signature (TypedControls.indexSyntax Bool) (DeclarationControls.vectorParameters Bool)
        DeclarationControls.vectorNames (IndexedInductiveNatVec.Vectors.admitted Bool) PackageControls.vectorPrior)
      (Package.computation (TypedControls.indexSyntax Bool) (DeclarationControls.vectorParameters Bool)
        DeclarationControls.vectorNames (IndexedInductiveNatVec.Vectors.admitted Bool))
      row.2.1 row.2.2.1 row.2.2.2.1 row.2.2.2.2) :=
  generated_row_has_receipt _ _ _ _ _ _ _ _ _ PackageControls.vector_rows member

def naturalReference :=
  (NativeNaturalVectorFamilies.declarations.take 4,
    Data.schemaRows (NativeNaturalVectorFamilies.Checking.schemas.take 2))

def scalars := Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.binaryScalars
def heads := Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec.WithScalars.towerHeadCodec scalars

def vectorPacket := Data.packageData scalars heads vectorReference.1 vectorReference.2
def naturalPacket := Data.packageData scalars heads naturalReference.1 naturalReference.2

theorem vector_packet_readback :
    Data.readPackage scalars heads vectorPacket = some vectorGenerated := by
  rw [vector_generated_reference]
  exact Data.readPackage_packageData scalars heads _ _

theorem declaration_inventory :
    vectorReference.1.map Prod.fst =
      [NativeNaturalVectorFamilies.vecName, NativeNaturalVectorFamilies.vnilName,
       NativeNaturalVectorFamilies.vconsName, NativeNaturalVectorFamilies.vecEliminateName] := rfl

theorem context_arities :
    naturalReference.2.map Sigma.fst = [3, 4] ∧ vectorReference.2.map Sigma.fst = [4, 7] := by
  exact ⟨rfl, rfl⟩

theorem changed_row_packet_distinct {rows : List (Data.Row Tower.Head)}
    (changed : rows ≠ vectorReference.2) :
    Data.packageData scalars heads vectorReference.1 rows ≠ vectorPacket := by
  intro same
  exact changed (Data.packageData_injective scalars heads same).2

/-- Removing the last row is visible even though the remaining row is valid. -/
theorem missing_constructor_row_distinct :
    Data.packageData scalars heads vectorReference.1 (vectorReference.2.take 1) ≠ vectorPacket := by
  apply changed_row_packet_distinct
  intro same
  have lengths := congrArg List.length same
  change 1 = 2 at lengths
  omega

#print axioms vector_generated_reference
#print axioms builder_reference
#print axioms block_reference
#print axioms vector_receipts
#print axioms vector_packet_readback
#print axioms missing_constructor_row_distinct

end Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaPackageControls
