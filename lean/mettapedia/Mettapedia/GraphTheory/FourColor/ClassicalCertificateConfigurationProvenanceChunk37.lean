import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf593 :
    entryBoolean 592 = true := by
  rfl

theorem classicalConfigurationProvenance_cf594 :
    entryBoolean 593 = true := by
  rfl

theorem classicalConfigurationProvenance_cf595 :
    entryBoolean 594 = true := by
  rfl

theorem classicalConfigurationProvenance_cf596 :
    entryBoolean 595 = true := by
  rfl

theorem classicalConfigurationProvenance_cf597 :
    entryBoolean 596 = true := by
  rfl

theorem classicalConfigurationProvenance_cf598 :
    entryBoolean 597 = true := by
  rfl

theorem classicalConfigurationProvenance_cf599 :
    entryBoolean 598 = true := by
  rfl

theorem classicalConfigurationProvenance_cf600 :
    entryBoolean 599 = true := by
  rfl

theorem classicalConfigurationProvenance_cf601 :
    entryBoolean 600 = true := by
  rfl

theorem classicalConfigurationProvenance_cf602 :
    entryBoolean 601 = true := by
  rfl

theorem classicalConfigurationProvenance_cf603 :
    entryBoolean 602 = true := by
  rfl

theorem classicalConfigurationProvenance_cf604 :
    entryBoolean 603 = true := by
  rfl

theorem classicalConfigurationProvenance_cf605 :
    entryBoolean 604 = true := by
  rfl

theorem classicalConfigurationProvenance_cf606 :
    entryBoolean 605 = true := by
  rfl

theorem classicalConfigurationProvenance_cf607 :
    entryBoolean 606 = true := by
  rfl

theorem classicalConfigurationProvenance_cf608 :
    entryBoolean 607 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk37_checker :
    chunkBoolean 37 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf593
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf594
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf595
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf596
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf597
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf598
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf599
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf600
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf601
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf602
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf603
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf604
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf605
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf606
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf607
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf608

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
