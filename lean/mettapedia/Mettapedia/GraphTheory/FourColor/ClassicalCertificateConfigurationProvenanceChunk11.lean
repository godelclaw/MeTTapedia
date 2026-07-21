import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf177 :
    entryBoolean 176 = true := by
  rfl

theorem classicalConfigurationProvenance_cf178 :
    entryBoolean 177 = true := by
  rfl

theorem classicalConfigurationProvenance_cf179 :
    entryBoolean 178 = true := by
  rfl

theorem classicalConfigurationProvenance_cf180 :
    entryBoolean 179 = true := by
  rfl

theorem classicalConfigurationProvenance_cf181 :
    entryBoolean 180 = true := by
  rfl

theorem classicalConfigurationProvenance_cf182 :
    entryBoolean 181 = true := by
  rfl

theorem classicalConfigurationProvenance_cf183 :
    entryBoolean 182 = true := by
  rfl

theorem classicalConfigurationProvenance_cf184 :
    entryBoolean 183 = true := by
  rfl

theorem classicalConfigurationProvenance_cf185 :
    entryBoolean 184 = true := by
  rfl

theorem classicalConfigurationProvenance_cf186 :
    entryBoolean 185 = true := by
  rfl

theorem classicalConfigurationProvenance_cf187 :
    entryBoolean 186 = true := by
  rfl

theorem classicalConfigurationProvenance_cf188 :
    entryBoolean 187 = true := by
  rfl

theorem classicalConfigurationProvenance_cf189 :
    entryBoolean 188 = true := by
  rfl

theorem classicalConfigurationProvenance_cf190 :
    entryBoolean 189 = true := by
  rfl

theorem classicalConfigurationProvenance_cf191 :
    entryBoolean 190 = true := by
  rfl

theorem classicalConfigurationProvenance_cf192 :
    entryBoolean 191 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk11_checker :
    chunkBoolean 11 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf177
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf178
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf179
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf180
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf181
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf182
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf183
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf184
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf185
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf186
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf187
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf188
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf189
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf190
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf191
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf192

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
