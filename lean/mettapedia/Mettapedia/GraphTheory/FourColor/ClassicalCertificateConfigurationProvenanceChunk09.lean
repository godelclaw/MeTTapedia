import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf145 :
    entryBoolean 144 = true := by
  rfl

theorem classicalConfigurationProvenance_cf146 :
    entryBoolean 145 = true := by
  rfl

theorem classicalConfigurationProvenance_cf147 :
    entryBoolean 146 = true := by
  rfl

theorem classicalConfigurationProvenance_cf148 :
    entryBoolean 147 = true := by
  rfl

theorem classicalConfigurationProvenance_cf149 :
    entryBoolean 148 = true := by
  rfl

theorem classicalConfigurationProvenance_cf150 :
    entryBoolean 149 = true := by
  rfl

theorem classicalConfigurationProvenance_cf151 :
    entryBoolean 150 = true := by
  rfl

theorem classicalConfigurationProvenance_cf152 :
    entryBoolean 151 = true := by
  rfl

theorem classicalConfigurationProvenance_cf153 :
    entryBoolean 152 = true := by
  rfl

theorem classicalConfigurationProvenance_cf154 :
    entryBoolean 153 = true := by
  rfl

theorem classicalConfigurationProvenance_cf155 :
    entryBoolean 154 = true := by
  rfl

theorem classicalConfigurationProvenance_cf156 :
    entryBoolean 155 = true := by
  rfl

theorem classicalConfigurationProvenance_cf157 :
    entryBoolean 156 = true := by
  rfl

theorem classicalConfigurationProvenance_cf158 :
    entryBoolean 157 = true := by
  rfl

theorem classicalConfigurationProvenance_cf159 :
    entryBoolean 158 = true := by
  rfl

theorem classicalConfigurationProvenance_cf160 :
    entryBoolean 159 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk09_checker :
    chunkBoolean 9 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf145
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf146
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf147
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf148
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf149
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf150
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf151
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf152
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf153
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf154
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf155
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf156
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf157
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf158
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf159
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf160

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
