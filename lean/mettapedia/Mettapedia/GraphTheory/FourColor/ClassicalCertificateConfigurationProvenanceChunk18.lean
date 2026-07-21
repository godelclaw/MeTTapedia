import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf289 :
    entryBoolean 288 = true := by
  rfl

theorem classicalConfigurationProvenance_cf290 :
    entryBoolean 289 = true := by
  rfl

theorem classicalConfigurationProvenance_cf291 :
    entryBoolean 290 = true := by
  rfl

theorem classicalConfigurationProvenance_cf292 :
    entryBoolean 291 = true := by
  rfl

theorem classicalConfigurationProvenance_cf293 :
    entryBoolean 292 = true := by
  rfl

theorem classicalConfigurationProvenance_cf294 :
    entryBoolean 293 = true := by
  rfl

theorem classicalConfigurationProvenance_cf295 :
    entryBoolean 294 = true := by
  rfl

theorem classicalConfigurationProvenance_cf296 :
    entryBoolean 295 = true := by
  rfl

theorem classicalConfigurationProvenance_cf297 :
    entryBoolean 296 = true := by
  rfl

theorem classicalConfigurationProvenance_cf298 :
    entryBoolean 297 = true := by
  rfl

theorem classicalConfigurationProvenance_cf299 :
    entryBoolean 298 = true := by
  rfl

theorem classicalConfigurationProvenance_cf300 :
    entryBoolean 299 = true := by
  rfl

theorem classicalConfigurationProvenance_cf301 :
    entryBoolean 300 = true := by
  rfl

theorem classicalConfigurationProvenance_cf302 :
    entryBoolean 301 = true := by
  rfl

theorem classicalConfigurationProvenance_cf303 :
    entryBoolean 302 = true := by
  rfl

theorem classicalConfigurationProvenance_cf304 :
    entryBoolean 303 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk18_checker :
    chunkBoolean 18 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf289
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf290
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf291
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf292
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf293
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf294
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf295
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf296
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf297
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf298
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf299
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf300
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf301
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf302
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf303
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf304

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
