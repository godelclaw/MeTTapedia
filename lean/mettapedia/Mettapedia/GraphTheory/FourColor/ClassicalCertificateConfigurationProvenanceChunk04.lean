import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf065 :
    entryBoolean 64 = true := by
  rfl

theorem classicalConfigurationProvenance_cf066 :
    entryBoolean 65 = true := by
  rfl

theorem classicalConfigurationProvenance_cf067 :
    entryBoolean 66 = true := by
  rfl

theorem classicalConfigurationProvenance_cf068 :
    entryBoolean 67 = true := by
  rfl

theorem classicalConfigurationProvenance_cf069 :
    entryBoolean 68 = true := by
  rfl

theorem classicalConfigurationProvenance_cf070 :
    entryBoolean 69 = true := by
  rfl

theorem classicalConfigurationProvenance_cf071 :
    entryBoolean 70 = true := by
  rfl

theorem classicalConfigurationProvenance_cf072 :
    entryBoolean 71 = true := by
  rfl

theorem classicalConfigurationProvenance_cf073 :
    entryBoolean 72 = true := by
  rfl

theorem classicalConfigurationProvenance_cf074 :
    entryBoolean 73 = true := by
  rfl

theorem classicalConfigurationProvenance_cf075 :
    entryBoolean 74 = true := by
  rfl

theorem classicalConfigurationProvenance_cf076 :
    entryBoolean 75 = true := by
  rfl

theorem classicalConfigurationProvenance_cf077 :
    entryBoolean 76 = true := by
  rfl

theorem classicalConfigurationProvenance_cf078 :
    entryBoolean 77 = true := by
  rfl

theorem classicalConfigurationProvenance_cf079 :
    entryBoolean 78 = true := by
  rfl

theorem classicalConfigurationProvenance_cf080 :
    entryBoolean 79 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk04_checker :
    chunkBoolean 4 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf065
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf066
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf067
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf068
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf069
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf070
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf071
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf072
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf073
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf074
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf075
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf076
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf077
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf078
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf079
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf080

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
