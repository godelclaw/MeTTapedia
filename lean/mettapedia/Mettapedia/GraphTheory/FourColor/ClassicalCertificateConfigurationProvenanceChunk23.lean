import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf369 :
    entryBoolean 368 = true := by
  rfl

theorem classicalConfigurationProvenance_cf370 :
    entryBoolean 369 = true := by
  rfl

theorem classicalConfigurationProvenance_cf371 :
    entryBoolean 370 = true := by
  rfl

theorem classicalConfigurationProvenance_cf372 :
    entryBoolean 371 = true := by
  rfl

theorem classicalConfigurationProvenance_cf373 :
    entryBoolean 372 = true := by
  rfl

theorem classicalConfigurationProvenance_cf374 :
    entryBoolean 373 = true := by
  rfl

theorem classicalConfigurationProvenance_cf375 :
    entryBoolean 374 = true := by
  rfl

theorem classicalConfigurationProvenance_cf376 :
    entryBoolean 375 = true := by
  rfl

theorem classicalConfigurationProvenance_cf377 :
    entryBoolean 376 = true := by
  rfl

theorem classicalConfigurationProvenance_cf378 :
    entryBoolean 377 = true := by
  rfl

theorem classicalConfigurationProvenance_cf379 :
    entryBoolean 378 = true := by
  rfl

theorem classicalConfigurationProvenance_cf380 :
    entryBoolean 379 = true := by
  rfl

theorem classicalConfigurationProvenance_cf381 :
    entryBoolean 380 = true := by
  rfl

theorem classicalConfigurationProvenance_cf382 :
    entryBoolean 381 = true := by
  rfl

theorem classicalConfigurationProvenance_cf383 :
    entryBoolean 382 = true := by
  rfl

theorem classicalConfigurationProvenance_cf384 :
    entryBoolean 383 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk23_checker :
    chunkBoolean 23 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf369
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf370
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf371
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf372
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf373
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf374
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf375
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf376
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf377
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf378
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf379
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf380
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf381
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf382
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf383
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf384

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
