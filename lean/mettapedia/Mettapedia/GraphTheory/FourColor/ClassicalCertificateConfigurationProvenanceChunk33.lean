import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf529 :
    entryBoolean 528 = true := by
  rfl

theorem classicalConfigurationProvenance_cf530 :
    entryBoolean 529 = true := by
  rfl

theorem classicalConfigurationProvenance_cf531 :
    entryBoolean 530 = true := by
  rfl

theorem classicalConfigurationProvenance_cf532 :
    entryBoolean 531 = true := by
  rfl

theorem classicalConfigurationProvenance_cf533 :
    entryBoolean 532 = true := by
  rfl

theorem classicalConfigurationProvenance_cf534 :
    entryBoolean 533 = true := by
  rfl

theorem classicalConfigurationProvenance_cf535 :
    entryBoolean 534 = true := by
  rfl

theorem classicalConfigurationProvenance_cf536 :
    entryBoolean 535 = true := by
  rfl

theorem classicalConfigurationProvenance_cf537 :
    entryBoolean 536 = true := by
  rfl

theorem classicalConfigurationProvenance_cf538 :
    entryBoolean 537 = true := by
  rfl

theorem classicalConfigurationProvenance_cf539 :
    entryBoolean 538 = true := by
  rfl

theorem classicalConfigurationProvenance_cf540 :
    entryBoolean 539 = true := by
  rfl

theorem classicalConfigurationProvenance_cf541 :
    entryBoolean 540 = true := by
  rfl

theorem classicalConfigurationProvenance_cf542 :
    entryBoolean 541 = true := by
  rfl

theorem classicalConfigurationProvenance_cf543 :
    entryBoolean 542 = true := by
  rfl

theorem classicalConfigurationProvenance_cf544 :
    entryBoolean 543 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk33_checker :
    chunkBoolean 33 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf529
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf530
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf531
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf532
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf533
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf534
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf535
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf536
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf537
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf538
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf539
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf540
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf541
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf542
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf543
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf544

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
