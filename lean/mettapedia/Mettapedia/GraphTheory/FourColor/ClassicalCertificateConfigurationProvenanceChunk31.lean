import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf497 :
    entryBoolean 496 = true := by
  rfl

theorem classicalConfigurationProvenance_cf498 :
    entryBoolean 497 = true := by
  rfl

theorem classicalConfigurationProvenance_cf499 :
    entryBoolean 498 = true := by
  rfl

theorem classicalConfigurationProvenance_cf500 :
    entryBoolean 499 = true := by
  rfl

theorem classicalConfigurationProvenance_cf501 :
    entryBoolean 500 = true := by
  rfl

theorem classicalConfigurationProvenance_cf502 :
    entryBoolean 501 = true := by
  rfl

theorem classicalConfigurationProvenance_cf503 :
    entryBoolean 502 = true := by
  rfl

theorem classicalConfigurationProvenance_cf504 :
    entryBoolean 503 = true := by
  rfl

theorem classicalConfigurationProvenance_cf505 :
    entryBoolean 504 = true := by
  rfl

theorem classicalConfigurationProvenance_cf506 :
    entryBoolean 505 = true := by
  rfl

theorem classicalConfigurationProvenance_cf507 :
    entryBoolean 506 = true := by
  rfl

theorem classicalConfigurationProvenance_cf508 :
    entryBoolean 507 = true := by
  rfl

theorem classicalConfigurationProvenance_cf509 :
    entryBoolean 508 = true := by
  rfl

theorem classicalConfigurationProvenance_cf510 :
    entryBoolean 509 = true := by
  rfl

theorem classicalConfigurationProvenance_cf511 :
    entryBoolean 510 = true := by
  rfl

theorem classicalConfigurationProvenance_cf512 :
    entryBoolean 511 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk31_checker :
    chunkBoolean 31 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf497
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf498
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf499
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf500
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf501
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf502
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf503
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf504
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf505
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf506
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf507
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf508
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf509
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf510
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf511
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf512

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
