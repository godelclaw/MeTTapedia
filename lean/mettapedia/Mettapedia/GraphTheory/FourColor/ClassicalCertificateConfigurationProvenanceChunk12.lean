import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf193 :
    entryBoolean 192 = true := by
  rfl

theorem classicalConfigurationProvenance_cf194 :
    entryBoolean 193 = true := by
  rfl

theorem classicalConfigurationProvenance_cf195 :
    entryBoolean 194 = true := by
  rfl

theorem classicalConfigurationProvenance_cf196 :
    entryBoolean 195 = true := by
  rfl

theorem classicalConfigurationProvenance_cf197 :
    entryBoolean 196 = true := by
  rfl

theorem classicalConfigurationProvenance_cf198 :
    entryBoolean 197 = true := by
  rfl

theorem classicalConfigurationProvenance_cf199 :
    entryBoolean 198 = true := by
  rfl

theorem classicalConfigurationProvenance_cf200 :
    entryBoolean 199 = true := by
  rfl

theorem classicalConfigurationProvenance_cf201 :
    entryBoolean 200 = true := by
  rfl

theorem classicalConfigurationProvenance_cf202 :
    entryBoolean 201 = true := by
  rfl

theorem classicalConfigurationProvenance_cf203 :
    entryBoolean 202 = true := by
  rfl

theorem classicalConfigurationProvenance_cf204 :
    entryBoolean 203 = true := by
  rfl

theorem classicalConfigurationProvenance_cf205 :
    entryBoolean 204 = true := by
  rfl

theorem classicalConfigurationProvenance_cf206 :
    entryBoolean 205 = true := by
  rfl

theorem classicalConfigurationProvenance_cf207 :
    entryBoolean 206 = true := by
  rfl

theorem classicalConfigurationProvenance_cf208 :
    entryBoolean 207 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk12_checker :
    chunkBoolean 12 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf193
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf194
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf195
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf196
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf197
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf198
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf199
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf200
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf201
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf202
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf203
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf204
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf205
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf206
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf207
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf208

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
