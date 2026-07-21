import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf417 :
    entryBoolean 416 = true := by
  rfl

theorem classicalConfigurationProvenance_cf418 :
    entryBoolean 417 = true := by
  rfl

theorem classicalConfigurationProvenance_cf419 :
    entryBoolean 418 = true := by
  rfl

theorem classicalConfigurationProvenance_cf420 :
    entryBoolean 419 = true := by
  rfl

theorem classicalConfigurationProvenance_cf421 :
    entryBoolean 420 = true := by
  rfl

theorem classicalConfigurationProvenance_cf422 :
    entryBoolean 421 = true := by
  rfl

theorem classicalConfigurationProvenance_cf423 :
    entryBoolean 422 = true := by
  rfl

theorem classicalConfigurationProvenance_cf424 :
    entryBoolean 423 = true := by
  rfl

theorem classicalConfigurationProvenance_cf425 :
    entryBoolean 424 = true := by
  rfl

theorem classicalConfigurationProvenance_cf426 :
    entryBoolean 425 = true := by
  rfl

theorem classicalConfigurationProvenance_cf427 :
    entryBoolean 426 = true := by
  rfl

theorem classicalConfigurationProvenance_cf428 :
    entryBoolean 427 = true := by
  rfl

theorem classicalConfigurationProvenance_cf429 :
    entryBoolean 428 = true := by
  rfl

theorem classicalConfigurationProvenance_cf430 :
    entryBoolean 429 = true := by
  rfl

theorem classicalConfigurationProvenance_cf431 :
    entryBoolean 430 = true := by
  rfl

theorem classicalConfigurationProvenance_cf432 :
    entryBoolean 431 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk26_checker :
    chunkBoolean 26 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf417
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf418
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf419
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf420
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf421
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf422
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf423
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf424
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf425
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf426
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf427
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf428
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf429
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf430
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf431
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf432

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
