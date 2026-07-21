import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf113 :
    entryBoolean 112 = true := by
  rfl

theorem classicalConfigurationProvenance_cf114 :
    entryBoolean 113 = true := by
  rfl

theorem classicalConfigurationProvenance_cf115 :
    entryBoolean 114 = true := by
  rfl

theorem classicalConfigurationProvenance_cf116 :
    entryBoolean 115 = true := by
  rfl

theorem classicalConfigurationProvenance_cf117 :
    entryBoolean 116 = true := by
  rfl

theorem classicalConfigurationProvenance_cf118 :
    entryBoolean 117 = true := by
  rfl

theorem classicalConfigurationProvenance_cf119 :
    entryBoolean 118 = true := by
  rfl

theorem classicalConfigurationProvenance_cf120 :
    entryBoolean 119 = true := by
  rfl

theorem classicalConfigurationProvenance_cf121 :
    entryBoolean 120 = true := by
  rfl

theorem classicalConfigurationProvenance_cf122 :
    entryBoolean 121 = true := by
  rfl

theorem classicalConfigurationProvenance_cf123 :
    entryBoolean 122 = true := by
  rfl

theorem classicalConfigurationProvenance_cf124 :
    entryBoolean 123 = true := by
  rfl

theorem classicalConfigurationProvenance_cf125 :
    entryBoolean 124 = true := by
  rfl

theorem classicalConfigurationProvenance_cf126 :
    entryBoolean 125 = true := by
  rfl

theorem classicalConfigurationProvenance_cf127 :
    entryBoolean 126 = true := by
  rfl

theorem classicalConfigurationProvenance_cf128 :
    entryBoolean 127 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk07_checker :
    chunkBoolean 7 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf113
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf114
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf115
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf116
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf117
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf118
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf119
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf120
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf121
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf122
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf123
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf124
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf125
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf126
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf127
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf128

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
