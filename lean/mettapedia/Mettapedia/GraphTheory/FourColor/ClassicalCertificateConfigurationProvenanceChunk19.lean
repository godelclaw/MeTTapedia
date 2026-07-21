import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf305 :
    entryBoolean 304 = true := by
  rfl

theorem classicalConfigurationProvenance_cf306 :
    entryBoolean 305 = true := by
  rfl

theorem classicalConfigurationProvenance_cf307 :
    entryBoolean 306 = true := by
  rfl

theorem classicalConfigurationProvenance_cf308 :
    entryBoolean 307 = true := by
  rfl

theorem classicalConfigurationProvenance_cf309 :
    entryBoolean 308 = true := by
  rfl

theorem classicalConfigurationProvenance_cf310 :
    entryBoolean 309 = true := by
  rfl

theorem classicalConfigurationProvenance_cf311 :
    entryBoolean 310 = true := by
  rfl

theorem classicalConfigurationProvenance_cf312 :
    entryBoolean 311 = true := by
  rfl

theorem classicalConfigurationProvenance_cf313 :
    entryBoolean 312 = true := by
  rfl

theorem classicalConfigurationProvenance_cf314 :
    entryBoolean 313 = true := by
  rfl

theorem classicalConfigurationProvenance_cf315 :
    entryBoolean 314 = true := by
  rfl

theorem classicalConfigurationProvenance_cf316 :
    entryBoolean 315 = true := by
  rfl

theorem classicalConfigurationProvenance_cf317 :
    entryBoolean 316 = true := by
  rfl

theorem classicalConfigurationProvenance_cf318 :
    entryBoolean 317 = true := by
  rfl

theorem classicalConfigurationProvenance_cf319 :
    entryBoolean 318 = true := by
  rfl

theorem classicalConfigurationProvenance_cf320 :
    entryBoolean 319 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk19_checker :
    chunkBoolean 19 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf305
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf306
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf307
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf308
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf309
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf310
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf311
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf312
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf313
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf314
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf315
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf316
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf317
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf318
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf319
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf320

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
