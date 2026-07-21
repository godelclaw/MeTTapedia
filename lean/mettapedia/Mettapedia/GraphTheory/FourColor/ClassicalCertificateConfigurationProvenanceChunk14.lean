import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf225 :
    entryBoolean 224 = true := by
  rfl

theorem classicalConfigurationProvenance_cf226 :
    entryBoolean 225 = true := by
  rfl

theorem classicalConfigurationProvenance_cf227 :
    entryBoolean 226 = true := by
  rfl

theorem classicalConfigurationProvenance_cf228 :
    entryBoolean 227 = true := by
  rfl

theorem classicalConfigurationProvenance_cf229 :
    entryBoolean 228 = true := by
  rfl

theorem classicalConfigurationProvenance_cf230 :
    entryBoolean 229 = true := by
  rfl

theorem classicalConfigurationProvenance_cf231 :
    entryBoolean 230 = true := by
  rfl

theorem classicalConfigurationProvenance_cf232 :
    entryBoolean 231 = true := by
  rfl

theorem classicalConfigurationProvenance_cf233 :
    entryBoolean 232 = true := by
  rfl

theorem classicalConfigurationProvenance_cf234 :
    entryBoolean 233 = true := by
  rfl

theorem classicalConfigurationProvenance_cf235 :
    entryBoolean 234 = true := by
  rfl

theorem classicalConfigurationProvenance_cf236 :
    entryBoolean 235 = true := by
  rfl

theorem classicalConfigurationProvenance_cf237 :
    entryBoolean 236 = true := by
  rfl

theorem classicalConfigurationProvenance_cf238 :
    entryBoolean 237 = true := by
  rfl

theorem classicalConfigurationProvenance_cf239 :
    entryBoolean 238 = true := by
  rfl

theorem classicalConfigurationProvenance_cf240 :
    entryBoolean 239 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk14_checker :
    chunkBoolean 14 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf225
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf226
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf227
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf228
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf229
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf230
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf231
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf232
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf233
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf234
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf235
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf236
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf237
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf238
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf239
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf240

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
