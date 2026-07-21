import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf321 :
    entryBoolean 320 = true := by
  rfl

theorem classicalConfigurationProvenance_cf322 :
    entryBoolean 321 = true := by
  rfl

theorem classicalConfigurationProvenance_cf323 :
    entryBoolean 322 = true := by
  rfl

theorem classicalConfigurationProvenance_cf324 :
    entryBoolean 323 = true := by
  rfl

theorem classicalConfigurationProvenance_cf325 :
    entryBoolean 324 = true := by
  rfl

theorem classicalConfigurationProvenance_cf326 :
    entryBoolean 325 = true := by
  rfl

theorem classicalConfigurationProvenance_cf327 :
    entryBoolean 326 = true := by
  rfl

theorem classicalConfigurationProvenance_cf328 :
    entryBoolean 327 = true := by
  rfl

theorem classicalConfigurationProvenance_cf329 :
    entryBoolean 328 = true := by
  rfl

theorem classicalConfigurationProvenance_cf330 :
    entryBoolean 329 = true := by
  rfl

theorem classicalConfigurationProvenance_cf331 :
    entryBoolean 330 = true := by
  rfl

theorem classicalConfigurationProvenance_cf332 :
    entryBoolean 331 = true := by
  rfl

theorem classicalConfigurationProvenance_cf333 :
    entryBoolean 332 = true := by
  rfl

theorem classicalConfigurationProvenance_cf334 :
    entryBoolean 333 = true := by
  rfl

theorem classicalConfigurationProvenance_cf335 :
    entryBoolean 334 = true := by
  rfl

theorem classicalConfigurationProvenance_cf336 :
    entryBoolean 335 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk20_checker :
    chunkBoolean 20 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf321
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf322
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf323
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf324
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf325
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf326
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf327
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf328
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf329
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf330
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf331
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf332
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf333
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf334
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf335
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf336

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
