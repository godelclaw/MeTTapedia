import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf209 :
    entryBoolean 208 = true := by
  rfl

theorem classicalConfigurationProvenance_cf210 :
    entryBoolean 209 = true := by
  rfl

theorem classicalConfigurationProvenance_cf211 :
    entryBoolean 210 = true := by
  rfl

theorem classicalConfigurationProvenance_cf212 :
    entryBoolean 211 = true := by
  rfl

theorem classicalConfigurationProvenance_cf213 :
    entryBoolean 212 = true := by
  rfl

theorem classicalConfigurationProvenance_cf214 :
    entryBoolean 213 = true := by
  rfl

theorem classicalConfigurationProvenance_cf215 :
    entryBoolean 214 = true := by
  rfl

theorem classicalConfigurationProvenance_cf216 :
    entryBoolean 215 = true := by
  rfl

theorem classicalConfigurationProvenance_cf217 :
    entryBoolean 216 = true := by
  rfl

theorem classicalConfigurationProvenance_cf218 :
    entryBoolean 217 = true := by
  rfl

theorem classicalConfigurationProvenance_cf219 :
    entryBoolean 218 = true := by
  rfl

theorem classicalConfigurationProvenance_cf220 :
    entryBoolean 219 = true := by
  rfl

theorem classicalConfigurationProvenance_cf221 :
    entryBoolean 220 = true := by
  rfl

theorem classicalConfigurationProvenance_cf222 :
    entryBoolean 221 = true := by
  rfl

theorem classicalConfigurationProvenance_cf223 :
    entryBoolean 222 = true := by
  rfl

theorem classicalConfigurationProvenance_cf224 :
    entryBoolean 223 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk13_checker :
    chunkBoolean 13 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf209
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf210
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf211
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf212
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf213
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf214
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf215
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf216
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf217
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf218
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf219
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf220
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf221
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf222
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf223
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf224

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
