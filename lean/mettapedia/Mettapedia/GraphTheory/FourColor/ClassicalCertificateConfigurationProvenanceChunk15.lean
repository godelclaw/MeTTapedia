import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf241 :
    entryBoolean 240 = true := by
  rfl

theorem classicalConfigurationProvenance_cf242 :
    entryBoolean 241 = true := by
  rfl

theorem classicalConfigurationProvenance_cf243 :
    entryBoolean 242 = true := by
  rfl

theorem classicalConfigurationProvenance_cf244 :
    entryBoolean 243 = true := by
  rfl

theorem classicalConfigurationProvenance_cf245 :
    entryBoolean 244 = true := by
  rfl

theorem classicalConfigurationProvenance_cf246 :
    entryBoolean 245 = true := by
  rfl

theorem classicalConfigurationProvenance_cf247 :
    entryBoolean 246 = true := by
  rfl

theorem classicalConfigurationProvenance_cf248 :
    entryBoolean 247 = true := by
  rfl

theorem classicalConfigurationProvenance_cf249 :
    entryBoolean 248 = true := by
  rfl

theorem classicalConfigurationProvenance_cf250 :
    entryBoolean 249 = true := by
  rfl

theorem classicalConfigurationProvenance_cf251 :
    entryBoolean 250 = true := by
  rfl

theorem classicalConfigurationProvenance_cf252 :
    entryBoolean 251 = true := by
  rfl

theorem classicalConfigurationProvenance_cf253 :
    entryBoolean 252 = true := by
  rfl

theorem classicalConfigurationProvenance_cf254 :
    entryBoolean 253 = true := by
  rfl

theorem classicalConfigurationProvenance_cf255 :
    entryBoolean 254 = true := by
  rfl

theorem classicalConfigurationProvenance_cf256 :
    entryBoolean 255 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk15_checker :
    chunkBoolean 15 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf241
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf242
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf243
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf244
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf245
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf246
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf247
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf248
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf249
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf250
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf251
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf252
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf253
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf254
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf255
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf256

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
