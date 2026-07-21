import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf017 :
    entryBoolean 16 = true := by
  rfl

theorem classicalConfigurationProvenance_cf018 :
    entryBoolean 17 = true := by
  rfl

theorem classicalConfigurationProvenance_cf019 :
    entryBoolean 18 = true := by
  rfl

theorem classicalConfigurationProvenance_cf020 :
    entryBoolean 19 = true := by
  rfl

theorem classicalConfigurationProvenance_cf021 :
    entryBoolean 20 = true := by
  rfl

theorem classicalConfigurationProvenance_cf022 :
    entryBoolean 21 = true := by
  rfl

theorem classicalConfigurationProvenance_cf023 :
    entryBoolean 22 = true := by
  rfl

theorem classicalConfigurationProvenance_cf024 :
    entryBoolean 23 = true := by
  rfl

theorem classicalConfigurationProvenance_cf025 :
    entryBoolean 24 = true := by
  rfl

theorem classicalConfigurationProvenance_cf026 :
    entryBoolean 25 = true := by
  rfl

theorem classicalConfigurationProvenance_cf027 :
    entryBoolean 26 = true := by
  rfl

theorem classicalConfigurationProvenance_cf028 :
    entryBoolean 27 = true := by
  rfl

theorem classicalConfigurationProvenance_cf029 :
    entryBoolean 28 = true := by
  rfl

theorem classicalConfigurationProvenance_cf030 :
    entryBoolean 29 = true := by
  rfl

theorem classicalConfigurationProvenance_cf031 :
    entryBoolean 30 = true := by
  rfl

theorem classicalConfigurationProvenance_cf032 :
    entryBoolean 31 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk01_checker :
    chunkBoolean 1 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf017
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf018
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf019
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf020
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf021
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf022
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf023
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf024
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf025
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf026
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf027
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf028
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf029
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf030
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf031
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf032

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
