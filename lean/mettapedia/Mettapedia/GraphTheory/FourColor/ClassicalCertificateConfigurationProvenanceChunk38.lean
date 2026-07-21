import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf609 :
    entryBoolean 608 = true := by
  rfl

theorem classicalConfigurationProvenance_cf610 :
    entryBoolean 609 = true := by
  rfl

theorem classicalConfigurationProvenance_cf611 :
    entryBoolean 610 = true := by
  rfl

theorem classicalConfigurationProvenance_cf612 :
    entryBoolean 611 = true := by
  rfl

theorem classicalConfigurationProvenance_cf613 :
    entryBoolean 612 = true := by
  rfl

theorem classicalConfigurationProvenance_cf614 :
    entryBoolean 613 = true := by
  rfl

theorem classicalConfigurationProvenance_cf615 :
    entryBoolean 614 = true := by
  rfl

theorem classicalConfigurationProvenance_cf616 :
    entryBoolean 615 = true := by
  rfl

theorem classicalConfigurationProvenance_cf617 :
    entryBoolean 616 = true := by
  rfl

theorem classicalConfigurationProvenance_cf618 :
    entryBoolean 617 = true := by
  rfl

theorem classicalConfigurationProvenance_cf619 :
    entryBoolean 618 = true := by
  rfl

theorem classicalConfigurationProvenance_cf620 :
    entryBoolean 619 = true := by
  rfl

theorem classicalConfigurationProvenance_cf621 :
    entryBoolean 620 = true := by
  rfl

theorem classicalConfigurationProvenance_cf622 :
    entryBoolean 621 = true := by
  rfl

theorem classicalConfigurationProvenance_cf623 :
    entryBoolean 622 = true := by
  rfl

theorem classicalConfigurationProvenance_cf624 :
    entryBoolean 623 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk38_checker :
    chunkBoolean 38 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf609
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf610
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf611
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf612
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf613
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf614
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf615
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf616
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf617
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf618
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf619
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf620
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf621
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf622
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf623
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf624

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
