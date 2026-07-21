import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf433 :
    entryBoolean 432 = true := by
  rfl

theorem classicalConfigurationProvenance_cf434 :
    entryBoolean 433 = true := by
  rfl

theorem classicalConfigurationProvenance_cf435 :
    entryBoolean 434 = true := by
  rfl

theorem classicalConfigurationProvenance_cf436 :
    entryBoolean 435 = true := by
  rfl

theorem classicalConfigurationProvenance_cf437 :
    entryBoolean 436 = true := by
  rfl

theorem classicalConfigurationProvenance_cf438 :
    entryBoolean 437 = true := by
  rfl

theorem classicalConfigurationProvenance_cf439 :
    entryBoolean 438 = true := by
  rfl

theorem classicalConfigurationProvenance_cf440 :
    entryBoolean 439 = true := by
  rfl

theorem classicalConfigurationProvenance_cf441 :
    entryBoolean 440 = true := by
  rfl

theorem classicalConfigurationProvenance_cf442 :
    entryBoolean 441 = true := by
  rfl

theorem classicalConfigurationProvenance_cf443 :
    entryBoolean 442 = true := by
  rfl

theorem classicalConfigurationProvenance_cf444 :
    entryBoolean 443 = true := by
  rfl

theorem classicalConfigurationProvenance_cf445 :
    entryBoolean 444 = true := by
  rfl

theorem classicalConfigurationProvenance_cf446 :
    entryBoolean 445 = true := by
  rfl

theorem classicalConfigurationProvenance_cf447 :
    entryBoolean 446 = true := by
  rfl

theorem classicalConfigurationProvenance_cf448 :
    entryBoolean 447 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk27_checker :
    chunkBoolean 27 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf433
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf434
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf435
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf436
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf437
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf438
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf439
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf440
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf441
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf442
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf443
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf444
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf445
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf446
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf447
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf448

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
