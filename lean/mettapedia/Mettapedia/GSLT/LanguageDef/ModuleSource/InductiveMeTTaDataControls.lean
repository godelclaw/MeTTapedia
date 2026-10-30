import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSourceControls

/-! # Declaration-data controls through the existing indexed interpretation -/

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaDataControls

open InductiveMeTTaData IndexedNatVecSourceControls IndexedInductiveNatVec
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- These are the actual parameter, field and result-index data used by the
MeTTa builder experiment, admitted by the existing Nat/Vec interpretation. -/
theorem builder_admits_vector (A : Type) :
    admitBuilder A names (familyData natural) (familyData (vec "n" "head" "tail")) =
      some (Vectors.admitted A) := by
  simp only [admitBuilder, readFamily_familyData]
  rfl

theorem block_admits_vector (A : Type) :
    admitBlock A names (blockData natural) (blockData (vec "n" "head" "tail")) =
      some (Vectors.admitted A) := by
  rw [two_forms_same_admission]
  exact builder_admits_vector A

/-- Renaming the three bound constructor fields preserves their indexed
meaning after actual name resolution, in either authoring form. -/
theorem alpha_renaming_preserves_admission (A : Type) :
    admitBlock A names (blockData natural) (blockData (vec "length" "element" "tail")) =
      admitBuilder A names (familyData natural) (familyData (vec "n" "head" "tail")) := by
  rw [admitted_block_is_existing_admission, alpha_renamed_admitted, builder_admits_vector]

theorem captured_index_refused (A : Type) :
    admitBlock A names (blockData natural) (blockData (vec "n" "n" "tail")) = none := by
  rw [admitted_block_is_existing_admission]
  rfl

theorem recursive_name_capture_refused (A : Type) :
    admitBuilder A names (familyData natural) (familyData (vec "n" "head" "n")) = none := by
  simp only [admitBuilder, readFamily_familyData]
  rfl

theorem negative_recursive_field_refused (A : Type) :
    admitBlock A names (blockData natural) (blockData negativeField) = none := by
  rw [admitted_block_is_existing_admission]
  rfl

/-- A formed generated library is already available for this admitted
package. This theorem supplies formation, not a new automatic conversion law. -/
theorem block_vector_guest_formed (A : Type) :
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.Signature.ofList
      (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.declarations.take 4 ++
        IndexedInductive.Guest.Declarations.entries (IndexedInductive.Guest.TypedControls.indexSyntax A)
          (IndexedInductive.Guest.DeclarationControls.vectorParameters A)
          IndexedInductive.Guest.DeclarationControls.vectorNames (Vectors.admitted A))).Formed
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.rules :=
  text_guest_formed A (Vectors.admitted A) (text_admitted A)

def differentNameBlock : Atom :=
  .expression [.symbol "Declarations",
    .expression [.symbol ":", .expression [.symbol "Family", .symbol "Nat",
      .expression [.symbol "parameters", .expression []],
      .expression [.symbol "indices", .expression []]], .symbol "Type"],
    .expression [.symbol "=", .symbol "Other", .expression [.symbol "data", .expression []]]]

theorem mismatched_completion_refused : readBlock differentNameBlock = none := by
  decide +kernel

#print axioms builder_admits_vector
#print axioms alpha_renaming_preserves_admission
#print axioms captured_index_refused
#print axioms block_vector_guest_formed

end Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaDataControls
