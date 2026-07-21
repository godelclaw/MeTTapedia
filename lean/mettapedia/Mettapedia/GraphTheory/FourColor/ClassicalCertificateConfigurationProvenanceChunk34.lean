import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf545 :
    entryBoolean 544 = true := by
  rfl

theorem classicalConfigurationProvenance_cf546 :
    entryBoolean 545 = true := by
  rfl

theorem classicalConfigurationProvenance_cf547 :
    entryBoolean 546 = true := by
  rfl

theorem classicalConfigurationProvenance_cf548 :
    entryBoolean 547 = true := by
  rfl

theorem classicalConfigurationProvenance_cf549 :
    entryBoolean 548 = true := by
  rfl

theorem classicalConfigurationProvenance_cf550 :
    entryBoolean 549 = true := by
  rfl

theorem classicalConfigurationProvenance_cf551 :
    entryBoolean 550 = true := by
  rfl

theorem classicalConfigurationProvenance_cf552 :
    entryBoolean 551 = true := by
  rfl

theorem classicalConfigurationProvenance_cf553 :
    entryBoolean 552 = true := by
  rfl

theorem classicalConfigurationProvenance_cf554 :
    entryBoolean 553 = true := by
  rfl

theorem classicalConfigurationProvenance_cf555 :
    entryBoolean 554 = true := by
  rfl

theorem classicalConfigurationProvenance_cf556 :
    entryBoolean 555 = true := by
  rfl

theorem classicalConfigurationProvenance_cf557 :
    entryBoolean 556 = true := by
  rfl

theorem classicalConfigurationProvenance_cf558 :
    entryBoolean 557 = true := by
  rfl

theorem classicalConfigurationProvenance_cf559 :
    entryBoolean 558 = true := by
  rfl

theorem classicalConfigurationProvenance_cf560 :
    entryBoolean 559 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk34_checker :
    chunkBoolean 34 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf545
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf546
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf547
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf548
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf549
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf550
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf551
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf552
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf553
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf554
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf555
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf556
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf557
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf558
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf559
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf560

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
