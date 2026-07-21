import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf129 :
    entryBoolean 128 = true := by
  rfl

theorem classicalConfigurationProvenance_cf130 :
    entryBoolean 129 = true := by
  rfl

theorem classicalConfigurationProvenance_cf131 :
    entryBoolean 130 = true := by
  rfl

theorem classicalConfigurationProvenance_cf132 :
    entryBoolean 131 = true := by
  rfl

theorem classicalConfigurationProvenance_cf133 :
    entryBoolean 132 = true := by
  rfl

theorem classicalConfigurationProvenance_cf134 :
    entryBoolean 133 = true := by
  rfl

theorem classicalConfigurationProvenance_cf135 :
    entryBoolean 134 = true := by
  rfl

theorem classicalConfigurationProvenance_cf136 :
    entryBoolean 135 = true := by
  rfl

theorem classicalConfigurationProvenance_cf137 :
    entryBoolean 136 = true := by
  rfl

theorem classicalConfigurationProvenance_cf138 :
    entryBoolean 137 = true := by
  rfl

theorem classicalConfigurationProvenance_cf139 :
    entryBoolean 138 = true := by
  rfl

theorem classicalConfigurationProvenance_cf140 :
    entryBoolean 139 = true := by
  rfl

theorem classicalConfigurationProvenance_cf141 :
    entryBoolean 140 = true := by
  rfl

theorem classicalConfigurationProvenance_cf142 :
    entryBoolean 141 = true := by
  rfl

theorem classicalConfigurationProvenance_cf143 :
    entryBoolean 142 = true := by
  rfl

theorem classicalConfigurationProvenance_cf144 :
    entryBoolean 143 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk08_checker :
    chunkBoolean 8 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf129
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf130
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf131
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf132
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf133
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf134
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf135
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf136
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf137
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf138
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf139
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf140
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf141
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf142
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf143
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf144

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
