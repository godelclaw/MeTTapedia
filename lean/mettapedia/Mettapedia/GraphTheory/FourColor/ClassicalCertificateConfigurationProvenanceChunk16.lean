import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf257 :
    entryBoolean 256 = true := by
  rfl

theorem classicalConfigurationProvenance_cf258 :
    entryBoolean 257 = true := by
  rfl

theorem classicalConfigurationProvenance_cf259 :
    entryBoolean 258 = true := by
  rfl

theorem classicalConfigurationProvenance_cf260 :
    entryBoolean 259 = true := by
  rfl

theorem classicalConfigurationProvenance_cf261 :
    entryBoolean 260 = true := by
  rfl

theorem classicalConfigurationProvenance_cf262 :
    entryBoolean 261 = true := by
  rfl

theorem classicalConfigurationProvenance_cf263 :
    entryBoolean 262 = true := by
  rfl

theorem classicalConfigurationProvenance_cf264 :
    entryBoolean 263 = true := by
  rfl

theorem classicalConfigurationProvenance_cf265 :
    entryBoolean 264 = true := by
  rfl

theorem classicalConfigurationProvenance_cf266 :
    entryBoolean 265 = true := by
  rfl

theorem classicalConfigurationProvenance_cf267 :
    entryBoolean 266 = true := by
  rfl

theorem classicalConfigurationProvenance_cf268 :
    entryBoolean 267 = true := by
  rfl

theorem classicalConfigurationProvenance_cf269 :
    entryBoolean 268 = true := by
  rfl

theorem classicalConfigurationProvenance_cf270 :
    entryBoolean 269 = true := by
  rfl

theorem classicalConfigurationProvenance_cf271 :
    entryBoolean 270 = true := by
  rfl

theorem classicalConfigurationProvenance_cf272 :
    entryBoolean 271 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk16_checker :
    chunkBoolean 16 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf257
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf258
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf259
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf260
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf261
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf262
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf263
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf264
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf265
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf266
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf267
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf268
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf269
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf270
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf271
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf272

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
