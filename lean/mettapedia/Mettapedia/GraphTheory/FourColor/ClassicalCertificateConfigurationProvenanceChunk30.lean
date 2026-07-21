import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf481 :
    entryBoolean 480 = true := by
  rfl

theorem classicalConfigurationProvenance_cf482 :
    entryBoolean 481 = true := by
  rfl

theorem classicalConfigurationProvenance_cf483 :
    entryBoolean 482 = true := by
  rfl

theorem classicalConfigurationProvenance_cf484 :
    entryBoolean 483 = true := by
  rfl

theorem classicalConfigurationProvenance_cf485 :
    entryBoolean 484 = true := by
  rfl

theorem classicalConfigurationProvenance_cf486 :
    entryBoolean 485 = true := by
  rfl

theorem classicalConfigurationProvenance_cf487 :
    entryBoolean 486 = true := by
  rfl

theorem classicalConfigurationProvenance_cf488 :
    entryBoolean 487 = true := by
  rfl

theorem classicalConfigurationProvenance_cf489 :
    entryBoolean 488 = true := by
  rfl

theorem classicalConfigurationProvenance_cf490 :
    entryBoolean 489 = true := by
  rfl

theorem classicalConfigurationProvenance_cf491 :
    entryBoolean 490 = true := by
  rfl

theorem classicalConfigurationProvenance_cf492 :
    entryBoolean 491 = true := by
  rfl

theorem classicalConfigurationProvenance_cf493 :
    entryBoolean 492 = true := by
  rfl

theorem classicalConfigurationProvenance_cf494 :
    entryBoolean 493 = true := by
  rfl

theorem classicalConfigurationProvenance_cf495 :
    entryBoolean 494 = true := by
  rfl

theorem classicalConfigurationProvenance_cf496 :
    entryBoolean 495 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk30_checker :
    chunkBoolean 30 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf481
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf482
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf483
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf484
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf485
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf486
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf487
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf488
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf489
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf490
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf491
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf492
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf493
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf494
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf495
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf496

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
