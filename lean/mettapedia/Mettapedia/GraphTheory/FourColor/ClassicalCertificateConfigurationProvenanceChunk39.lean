import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf625 :
    entryBoolean 624 = true := by
  rfl

theorem classicalConfigurationProvenance_cf626 :
    entryBoolean 625 = true := by
  rfl

theorem classicalConfigurationProvenance_cf627 :
    entryBoolean 626 = true := by
  rfl

theorem classicalConfigurationProvenance_cf628 :
    entryBoolean 627 = true := by
  rfl

theorem classicalConfigurationProvenance_cf629 :
    entryBoolean 628 = true := by
  rfl

theorem classicalConfigurationProvenance_cf630 :
    entryBoolean 629 = true := by
  rfl

theorem classicalConfigurationProvenance_cf631 :
    entryBoolean 630 = true := by
  rfl

theorem classicalConfigurationProvenance_cf632 :
    entryBoolean 631 = true := by
  rfl

theorem classicalConfigurationProvenance_cf633 :
    entryBoolean 632 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk39_checker :
    chunkBoolean 39 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf625
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf626
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf627
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf628
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf629
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf630
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf631
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf632
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf633
  · simp [chunkSize, catalogueCount]
  · simp [chunkSize, catalogueCount]
  · simp [chunkSize, catalogueCount]
  · simp [chunkSize, catalogueCount]
  · simp [chunkSize, catalogueCount]
  · simp [chunkSize, catalogueCount]
  · simp [chunkSize, catalogueCount]

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
