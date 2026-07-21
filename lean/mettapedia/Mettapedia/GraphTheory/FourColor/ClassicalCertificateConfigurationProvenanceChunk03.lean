import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf049 :
    entryBoolean 48 = true := by
  rfl

theorem classicalConfigurationProvenance_cf050 :
    entryBoolean 49 = true := by
  rfl

theorem classicalConfigurationProvenance_cf051 :
    entryBoolean 50 = true := by
  rfl

theorem classicalConfigurationProvenance_cf052 :
    entryBoolean 51 = true := by
  rfl

theorem classicalConfigurationProvenance_cf053 :
    entryBoolean 52 = true := by
  rfl

theorem classicalConfigurationProvenance_cf054 :
    entryBoolean 53 = true := by
  rfl

theorem classicalConfigurationProvenance_cf055 :
    entryBoolean 54 = true := by
  rfl

theorem classicalConfigurationProvenance_cf056 :
    entryBoolean 55 = true := by
  rfl

theorem classicalConfigurationProvenance_cf057 :
    entryBoolean 56 = true := by
  rfl

theorem classicalConfigurationProvenance_cf058 :
    entryBoolean 57 = true := by
  rfl

theorem classicalConfigurationProvenance_cf059 :
    entryBoolean 58 = true := by
  rfl

theorem classicalConfigurationProvenance_cf060 :
    entryBoolean 59 = true := by
  rfl

theorem classicalConfigurationProvenance_cf061 :
    entryBoolean 60 = true := by
  rfl

theorem classicalConfigurationProvenance_cf062 :
    entryBoolean 61 = true := by
  rfl

theorem classicalConfigurationProvenance_cf063 :
    entryBoolean 62 = true := by
  rfl

theorem classicalConfigurationProvenance_cf064 :
    entryBoolean 63 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk03_checker :
    chunkBoolean 3 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf049
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf050
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf051
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf052
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf053
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf054
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf055
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf056
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf057
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf058
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf059
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf060
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf061
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf062
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf063
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf064

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
