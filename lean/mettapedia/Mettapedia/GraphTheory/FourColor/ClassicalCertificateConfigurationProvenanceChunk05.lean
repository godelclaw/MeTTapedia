import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf081 :
    entryBoolean 80 = true := by
  rfl

theorem classicalConfigurationProvenance_cf082 :
    entryBoolean 81 = true := by
  rfl

theorem classicalConfigurationProvenance_cf083 :
    entryBoolean 82 = true := by
  rfl

theorem classicalConfigurationProvenance_cf084 :
    entryBoolean 83 = true := by
  rfl

theorem classicalConfigurationProvenance_cf085 :
    entryBoolean 84 = true := by
  rfl

theorem classicalConfigurationProvenance_cf086 :
    entryBoolean 85 = true := by
  rfl

theorem classicalConfigurationProvenance_cf087 :
    entryBoolean 86 = true := by
  rfl

theorem classicalConfigurationProvenance_cf088 :
    entryBoolean 87 = true := by
  rfl

theorem classicalConfigurationProvenance_cf089 :
    entryBoolean 88 = true := by
  rfl

theorem classicalConfigurationProvenance_cf090 :
    entryBoolean 89 = true := by
  rfl

theorem classicalConfigurationProvenance_cf091 :
    entryBoolean 90 = true := by
  rfl

theorem classicalConfigurationProvenance_cf092 :
    entryBoolean 91 = true := by
  rfl

theorem classicalConfigurationProvenance_cf093 :
    entryBoolean 92 = true := by
  rfl

theorem classicalConfigurationProvenance_cf094 :
    entryBoolean 93 = true := by
  rfl

theorem classicalConfigurationProvenance_cf095 :
    entryBoolean 94 = true := by
  rfl

theorem classicalConfigurationProvenance_cf096 :
    entryBoolean 95 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk05_checker :
    chunkBoolean 5 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf081
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf082
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf083
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf084
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf085
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf086
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf087
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf088
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf089
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf090
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf091
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf092
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf093
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf094
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf095
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf096

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
