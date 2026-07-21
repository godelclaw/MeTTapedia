import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf561 :
    entryBoolean 560 = true := by
  rfl

theorem classicalConfigurationProvenance_cf562 :
    entryBoolean 561 = true := by
  rfl

theorem classicalConfigurationProvenance_cf563 :
    entryBoolean 562 = true := by
  rfl

theorem classicalConfigurationProvenance_cf564 :
    entryBoolean 563 = true := by
  rfl

theorem classicalConfigurationProvenance_cf565 :
    entryBoolean 564 = true := by
  rfl

theorem classicalConfigurationProvenance_cf566 :
    entryBoolean 565 = true := by
  rfl

theorem classicalConfigurationProvenance_cf567 :
    entryBoolean 566 = true := by
  rfl

theorem classicalConfigurationProvenance_cf568 :
    entryBoolean 567 = true := by
  rfl

theorem classicalConfigurationProvenance_cf569 :
    entryBoolean 568 = true := by
  rfl

theorem classicalConfigurationProvenance_cf570 :
    entryBoolean 569 = true := by
  rfl

theorem classicalConfigurationProvenance_cf571 :
    entryBoolean 570 = true := by
  rfl

theorem classicalConfigurationProvenance_cf572 :
    entryBoolean 571 = true := by
  rfl

theorem classicalConfigurationProvenance_cf573 :
    entryBoolean 572 = true := by
  rfl

theorem classicalConfigurationProvenance_cf574 :
    entryBoolean 573 = true := by
  rfl

theorem classicalConfigurationProvenance_cf575 :
    entryBoolean 574 = true := by
  rfl

theorem classicalConfigurationProvenance_cf576 :
    entryBoolean 575 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk35_checker :
    chunkBoolean 35 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf561
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf562
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf563
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf564
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf565
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf566
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf567
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf568
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf569
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf570
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf571
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf572
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf573
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf574
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf575
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf576

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
