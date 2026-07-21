import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf401 :
    entryBoolean 400 = true := by
  rfl

theorem classicalConfigurationProvenance_cf402 :
    entryBoolean 401 = true := by
  rfl

theorem classicalConfigurationProvenance_cf403 :
    entryBoolean 402 = true := by
  rfl

theorem classicalConfigurationProvenance_cf404 :
    entryBoolean 403 = true := by
  rfl

theorem classicalConfigurationProvenance_cf405 :
    entryBoolean 404 = true := by
  rfl

theorem classicalConfigurationProvenance_cf406 :
    entryBoolean 405 = true := by
  rfl

theorem classicalConfigurationProvenance_cf407 :
    entryBoolean 406 = true := by
  rfl

theorem classicalConfigurationProvenance_cf408 :
    entryBoolean 407 = true := by
  rfl

theorem classicalConfigurationProvenance_cf409 :
    entryBoolean 408 = true := by
  rfl

theorem classicalConfigurationProvenance_cf410 :
    entryBoolean 409 = true := by
  rfl

theorem classicalConfigurationProvenance_cf411 :
    entryBoolean 410 = true := by
  rfl

theorem classicalConfigurationProvenance_cf412 :
    entryBoolean 411 = true := by
  rfl

theorem classicalConfigurationProvenance_cf413 :
    entryBoolean 412 = true := by
  rfl

theorem classicalConfigurationProvenance_cf414 :
    entryBoolean 413 = true := by
  rfl

theorem classicalConfigurationProvenance_cf415 :
    entryBoolean 414 = true := by
  rfl

theorem classicalConfigurationProvenance_cf416 :
    entryBoolean 415 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk25_checker :
    chunkBoolean 25 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf401
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf402
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf403
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf404
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf405
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf406
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf407
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf408
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf409
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf410
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf411
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf412
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf413
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf414
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf415
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf416

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
