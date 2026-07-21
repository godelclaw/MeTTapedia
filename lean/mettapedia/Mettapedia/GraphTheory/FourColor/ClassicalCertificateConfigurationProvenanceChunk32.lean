import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf513 :
    entryBoolean 512 = true := by
  rfl

theorem classicalConfigurationProvenance_cf514 :
    entryBoolean 513 = true := by
  rfl

theorem classicalConfigurationProvenance_cf515 :
    entryBoolean 514 = true := by
  rfl

theorem classicalConfigurationProvenance_cf516 :
    entryBoolean 515 = true := by
  rfl

theorem classicalConfigurationProvenance_cf517 :
    entryBoolean 516 = true := by
  rfl

theorem classicalConfigurationProvenance_cf518 :
    entryBoolean 517 = true := by
  rfl

theorem classicalConfigurationProvenance_cf519 :
    entryBoolean 518 = true := by
  rfl

theorem classicalConfigurationProvenance_cf520 :
    entryBoolean 519 = true := by
  rfl

theorem classicalConfigurationProvenance_cf521 :
    entryBoolean 520 = true := by
  rfl

theorem classicalConfigurationProvenance_cf522 :
    entryBoolean 521 = true := by
  rfl

theorem classicalConfigurationProvenance_cf523 :
    entryBoolean 522 = true := by
  rfl

theorem classicalConfigurationProvenance_cf524 :
    entryBoolean 523 = true := by
  rfl

theorem classicalConfigurationProvenance_cf525 :
    entryBoolean 524 = true := by
  rfl

theorem classicalConfigurationProvenance_cf526 :
    entryBoolean 525 = true := by
  rfl

theorem classicalConfigurationProvenance_cf527 :
    entryBoolean 526 = true := by
  rfl

theorem classicalConfigurationProvenance_cf528 :
    entryBoolean 527 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk32_checker :
    chunkBoolean 32 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf513
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf514
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf515
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf516
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf517
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf518
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf519
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf520
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf521
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf522
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf523
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf524
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf525
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf526
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf527
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf528

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
