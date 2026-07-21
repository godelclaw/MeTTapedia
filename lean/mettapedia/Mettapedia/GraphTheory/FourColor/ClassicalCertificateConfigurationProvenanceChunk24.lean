import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf385 :
    entryBoolean 384 = true := by
  rfl

theorem classicalConfigurationProvenance_cf386 :
    entryBoolean 385 = true := by
  rfl

theorem classicalConfigurationProvenance_cf387 :
    entryBoolean 386 = true := by
  rfl

theorem classicalConfigurationProvenance_cf388 :
    entryBoolean 387 = true := by
  rfl

theorem classicalConfigurationProvenance_cf389 :
    entryBoolean 388 = true := by
  rfl

theorem classicalConfigurationProvenance_cf390 :
    entryBoolean 389 = true := by
  rfl

theorem classicalConfigurationProvenance_cf391 :
    entryBoolean 390 = true := by
  rfl

theorem classicalConfigurationProvenance_cf392 :
    entryBoolean 391 = true := by
  rfl

theorem classicalConfigurationProvenance_cf393 :
    entryBoolean 392 = true := by
  rfl

theorem classicalConfigurationProvenance_cf394 :
    entryBoolean 393 = true := by
  rfl

theorem classicalConfigurationProvenance_cf395 :
    entryBoolean 394 = true := by
  rfl

theorem classicalConfigurationProvenance_cf396 :
    entryBoolean 395 = true := by
  rfl

theorem classicalConfigurationProvenance_cf397 :
    entryBoolean 396 = true := by
  rfl

theorem classicalConfigurationProvenance_cf398 :
    entryBoolean 397 = true := by
  rfl

theorem classicalConfigurationProvenance_cf399 :
    entryBoolean 398 = true := by
  rfl

theorem classicalConfigurationProvenance_cf400 :
    entryBoolean 399 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk24_checker :
    chunkBoolean 24 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf385
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf386
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf387
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf388
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf389
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf390
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf391
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf392
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf393
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf394
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf395
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf396
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf397
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf398
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf399
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf400

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
