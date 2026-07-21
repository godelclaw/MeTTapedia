import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf337 :
    entryBoolean 336 = true := by
  rfl

theorem classicalConfigurationProvenance_cf338 :
    entryBoolean 337 = true := by
  rfl

theorem classicalConfigurationProvenance_cf339 :
    entryBoolean 338 = true := by
  rfl

theorem classicalConfigurationProvenance_cf340 :
    entryBoolean 339 = true := by
  rfl

theorem classicalConfigurationProvenance_cf341 :
    entryBoolean 340 = true := by
  rfl

theorem classicalConfigurationProvenance_cf342 :
    entryBoolean 341 = true := by
  rfl

theorem classicalConfigurationProvenance_cf343 :
    entryBoolean 342 = true := by
  rfl

theorem classicalConfigurationProvenance_cf344 :
    entryBoolean 343 = true := by
  rfl

theorem classicalConfigurationProvenance_cf345 :
    entryBoolean 344 = true := by
  rfl

theorem classicalConfigurationProvenance_cf346 :
    entryBoolean 345 = true := by
  rfl

theorem classicalConfigurationProvenance_cf347 :
    entryBoolean 346 = true := by
  rfl

theorem classicalConfigurationProvenance_cf348 :
    entryBoolean 347 = true := by
  rfl

theorem classicalConfigurationProvenance_cf349 :
    entryBoolean 348 = true := by
  rfl

theorem classicalConfigurationProvenance_cf350 :
    entryBoolean 349 = true := by
  rfl

theorem classicalConfigurationProvenance_cf351 :
    entryBoolean 350 = true := by
  rfl

theorem classicalConfigurationProvenance_cf352 :
    entryBoolean 351 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk21_checker :
    chunkBoolean 21 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf337
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf338
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf339
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf340
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf341
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf342
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf343
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf344
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf345
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf346
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf347
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf348
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf349
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf350
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf351
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf352

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
