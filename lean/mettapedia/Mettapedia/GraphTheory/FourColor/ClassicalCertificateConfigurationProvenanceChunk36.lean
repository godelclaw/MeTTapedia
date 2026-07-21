import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf577 :
    entryBoolean 576 = true := by
  rfl

theorem classicalConfigurationProvenance_cf578 :
    entryBoolean 577 = true := by
  rfl

theorem classicalConfigurationProvenance_cf579 :
    entryBoolean 578 = true := by
  rfl

theorem classicalConfigurationProvenance_cf580 :
    entryBoolean 579 = true := by
  rfl

theorem classicalConfigurationProvenance_cf581 :
    entryBoolean 580 = true := by
  rfl

theorem classicalConfigurationProvenance_cf582 :
    entryBoolean 581 = true := by
  rfl

theorem classicalConfigurationProvenance_cf583 :
    entryBoolean 582 = true := by
  rfl

theorem classicalConfigurationProvenance_cf584 :
    entryBoolean 583 = true := by
  rfl

theorem classicalConfigurationProvenance_cf585 :
    entryBoolean 584 = true := by
  rfl

theorem classicalConfigurationProvenance_cf586 :
    entryBoolean 585 = true := by
  rfl

theorem classicalConfigurationProvenance_cf587 :
    entryBoolean 586 = true := by
  rfl

theorem classicalConfigurationProvenance_cf588 :
    entryBoolean 587 = true := by
  rfl

theorem classicalConfigurationProvenance_cf589 :
    entryBoolean 588 = true := by
  rfl

theorem classicalConfigurationProvenance_cf590 :
    entryBoolean 589 = true := by
  rfl

theorem classicalConfigurationProvenance_cf591 :
    entryBoolean 590 = true := by
  rfl

theorem classicalConfigurationProvenance_cf592 :
    entryBoolean 591 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk36_checker :
    chunkBoolean 36 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf577
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf578
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf579
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf580
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf581
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf582
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf583
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf584
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf585
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf586
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf587
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf588
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf589
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf590
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf591
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf592

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
