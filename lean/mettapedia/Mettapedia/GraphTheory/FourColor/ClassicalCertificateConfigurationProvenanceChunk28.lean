import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf449 :
    entryBoolean 448 = true := by
  rfl

theorem classicalConfigurationProvenance_cf450 :
    entryBoolean 449 = true := by
  rfl

theorem classicalConfigurationProvenance_cf451 :
    entryBoolean 450 = true := by
  rfl

theorem classicalConfigurationProvenance_cf452 :
    entryBoolean 451 = true := by
  rfl

theorem classicalConfigurationProvenance_cf453 :
    entryBoolean 452 = true := by
  rfl

theorem classicalConfigurationProvenance_cf454 :
    entryBoolean 453 = true := by
  rfl

theorem classicalConfigurationProvenance_cf455 :
    entryBoolean 454 = true := by
  rfl

theorem classicalConfigurationProvenance_cf456 :
    entryBoolean 455 = true := by
  rfl

theorem classicalConfigurationProvenance_cf457 :
    entryBoolean 456 = true := by
  rfl

theorem classicalConfigurationProvenance_cf458 :
    entryBoolean 457 = true := by
  rfl

theorem classicalConfigurationProvenance_cf459 :
    entryBoolean 458 = true := by
  rfl

theorem classicalConfigurationProvenance_cf460 :
    entryBoolean 459 = true := by
  rfl

theorem classicalConfigurationProvenance_cf461 :
    entryBoolean 460 = true := by
  rfl

theorem classicalConfigurationProvenance_cf462 :
    entryBoolean 461 = true := by
  rfl

theorem classicalConfigurationProvenance_cf463 :
    entryBoolean 462 = true := by
  rfl

theorem classicalConfigurationProvenance_cf464 :
    entryBoolean 463 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk28_checker :
    chunkBoolean 28 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf449
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf450
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf451
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf452
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf453
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf454
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf455
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf456
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf457
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf458
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf459
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf460
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf461
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf462
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf463
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf464

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
