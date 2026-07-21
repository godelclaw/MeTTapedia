import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf161 :
    entryBoolean 160 = true := by
  rfl

theorem classicalConfigurationProvenance_cf162 :
    entryBoolean 161 = true := by
  rfl

theorem classicalConfigurationProvenance_cf163 :
    entryBoolean 162 = true := by
  rfl

theorem classicalConfigurationProvenance_cf164 :
    entryBoolean 163 = true := by
  rfl

theorem classicalConfigurationProvenance_cf165 :
    entryBoolean 164 = true := by
  rfl

theorem classicalConfigurationProvenance_cf166 :
    entryBoolean 165 = true := by
  rfl

theorem classicalConfigurationProvenance_cf167 :
    entryBoolean 166 = true := by
  rfl

theorem classicalConfigurationProvenance_cf168 :
    entryBoolean 167 = true := by
  rfl

theorem classicalConfigurationProvenance_cf169 :
    entryBoolean 168 = true := by
  rfl

theorem classicalConfigurationProvenance_cf170 :
    entryBoolean 169 = true := by
  rfl

theorem classicalConfigurationProvenance_cf171 :
    entryBoolean 170 = true := by
  rfl

theorem classicalConfigurationProvenance_cf172 :
    entryBoolean 171 = true := by
  rfl

theorem classicalConfigurationProvenance_cf173 :
    entryBoolean 172 = true := by
  rfl

theorem classicalConfigurationProvenance_cf174 :
    entryBoolean 173 = true := by
  rfl

theorem classicalConfigurationProvenance_cf175 :
    entryBoolean 174 = true := by
  rfl

theorem classicalConfigurationProvenance_cf176 :
    entryBoolean 175 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk10_checker :
    chunkBoolean 10 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf161
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf162
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf163
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf164
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf165
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf166
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf167
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf168
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf169
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf170
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf171
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf172
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf173
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf174
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf175
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf176

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
