import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf465 :
    entryBoolean 464 = true := by
  rfl

theorem classicalConfigurationProvenance_cf466 :
    entryBoolean 465 = true := by
  rfl

theorem classicalConfigurationProvenance_cf467 :
    entryBoolean 466 = true := by
  rfl

theorem classicalConfigurationProvenance_cf468 :
    entryBoolean 467 = true := by
  rfl

theorem classicalConfigurationProvenance_cf469 :
    entryBoolean 468 = true := by
  rfl

theorem classicalConfigurationProvenance_cf470 :
    entryBoolean 469 = true := by
  rfl

theorem classicalConfigurationProvenance_cf471 :
    entryBoolean 470 = true := by
  rfl

theorem classicalConfigurationProvenance_cf472 :
    entryBoolean 471 = true := by
  rfl

theorem classicalConfigurationProvenance_cf473 :
    entryBoolean 472 = true := by
  rfl

theorem classicalConfigurationProvenance_cf474 :
    entryBoolean 473 = true := by
  rfl

theorem classicalConfigurationProvenance_cf475 :
    entryBoolean 474 = true := by
  rfl

theorem classicalConfigurationProvenance_cf476 :
    entryBoolean 475 = true := by
  rfl

theorem classicalConfigurationProvenance_cf477 :
    entryBoolean 476 = true := by
  rfl

theorem classicalConfigurationProvenance_cf478 :
    entryBoolean 477 = true := by
  rfl

theorem classicalConfigurationProvenance_cf479 :
    entryBoolean 478 = true := by
  rfl

theorem classicalConfigurationProvenance_cf480 :
    entryBoolean 479 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk29_checker :
    chunkBoolean 29 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf465
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf466
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf467
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf468
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf469
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf470
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf471
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf472
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf473
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf474
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf475
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf476
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf477
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf478
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf479
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf480

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
