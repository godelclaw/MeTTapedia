import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf353 :
    entryBoolean 352 = true := by
  rfl

theorem classicalConfigurationProvenance_cf354 :
    entryBoolean 353 = true := by
  rfl

theorem classicalConfigurationProvenance_cf355 :
    entryBoolean 354 = true := by
  rfl

theorem classicalConfigurationProvenance_cf356 :
    entryBoolean 355 = true := by
  rfl

theorem classicalConfigurationProvenance_cf357 :
    entryBoolean 356 = true := by
  rfl

theorem classicalConfigurationProvenance_cf358 :
    entryBoolean 357 = true := by
  rfl

theorem classicalConfigurationProvenance_cf359 :
    entryBoolean 358 = true := by
  rfl

theorem classicalConfigurationProvenance_cf360 :
    entryBoolean 359 = true := by
  rfl

theorem classicalConfigurationProvenance_cf361 :
    entryBoolean 360 = true := by
  rfl

theorem classicalConfigurationProvenance_cf362 :
    entryBoolean 361 = true := by
  rfl

theorem classicalConfigurationProvenance_cf363 :
    entryBoolean 362 = true := by
  rfl

theorem classicalConfigurationProvenance_cf364 :
    entryBoolean 363 = true := by
  rfl

theorem classicalConfigurationProvenance_cf365 :
    entryBoolean 364 = true := by
  rfl

theorem classicalConfigurationProvenance_cf366 :
    entryBoolean 365 = true := by
  rfl

theorem classicalConfigurationProvenance_cf367 :
    entryBoolean 366 = true := by
  rfl

theorem classicalConfigurationProvenance_cf368 :
    entryBoolean 367 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk22_checker :
    chunkBoolean 22 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf353
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf354
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf355
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf356
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf357
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf358
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf359
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf360
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf361
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf362
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf363
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf364
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf365
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf366
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf367
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf368

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
