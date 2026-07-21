import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf097 :
    entryBoolean 96 = true := by
  rfl

theorem classicalConfigurationProvenance_cf098 :
    entryBoolean 97 = true := by
  rfl

theorem classicalConfigurationProvenance_cf099 :
    entryBoolean 98 = true := by
  rfl

theorem classicalConfigurationProvenance_cf100 :
    entryBoolean 99 = true := by
  rfl

theorem classicalConfigurationProvenance_cf101 :
    entryBoolean 100 = true := by
  rfl

theorem classicalConfigurationProvenance_cf102 :
    entryBoolean 101 = true := by
  rfl

theorem classicalConfigurationProvenance_cf103 :
    entryBoolean 102 = true := by
  rfl

theorem classicalConfigurationProvenance_cf104 :
    entryBoolean 103 = true := by
  rfl

theorem classicalConfigurationProvenance_cf105 :
    entryBoolean 104 = true := by
  rfl

theorem classicalConfigurationProvenance_cf106 :
    entryBoolean 105 = true := by
  rfl

theorem classicalConfigurationProvenance_cf107 :
    entryBoolean 106 = true := by
  rfl

theorem classicalConfigurationProvenance_cf108 :
    entryBoolean 107 = true := by
  rfl

theorem classicalConfigurationProvenance_cf109 :
    entryBoolean 108 = true := by
  rfl

theorem classicalConfigurationProvenance_cf110 :
    entryBoolean 109 = true := by
  rfl

theorem classicalConfigurationProvenance_cf111 :
    entryBoolean 110 = true := by
  rfl

theorem classicalConfigurationProvenance_cf112 :
    entryBoolean 111 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk06_checker :
    chunkBoolean 6 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf097
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf098
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf099
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf100
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf101
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf102
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf103
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf104
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf105
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf106
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf107
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf108
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf109
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf110
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf111
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf112

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
