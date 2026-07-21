import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf033 :
    entryBoolean 32 = true := by
  rfl

theorem classicalConfigurationProvenance_cf034 :
    entryBoolean 33 = true := by
  rfl

theorem classicalConfigurationProvenance_cf035 :
    entryBoolean 34 = true := by
  rfl

theorem classicalConfigurationProvenance_cf036 :
    entryBoolean 35 = true := by
  rfl

theorem classicalConfigurationProvenance_cf037 :
    entryBoolean 36 = true := by
  rfl

theorem classicalConfigurationProvenance_cf038 :
    entryBoolean 37 = true := by
  rfl

theorem classicalConfigurationProvenance_cf039 :
    entryBoolean 38 = true := by
  rfl

theorem classicalConfigurationProvenance_cf040 :
    entryBoolean 39 = true := by
  rfl

theorem classicalConfigurationProvenance_cf041 :
    entryBoolean 40 = true := by
  rfl

theorem classicalConfigurationProvenance_cf042 :
    entryBoolean 41 = true := by
  rfl

theorem classicalConfigurationProvenance_cf043 :
    entryBoolean 42 = true := by
  rfl

theorem classicalConfigurationProvenance_cf044 :
    entryBoolean 43 = true := by
  rfl

theorem classicalConfigurationProvenance_cf045 :
    entryBoolean 44 = true := by
  rfl

theorem classicalConfigurationProvenance_cf046 :
    entryBoolean 45 = true := by
  rfl

theorem classicalConfigurationProvenance_cf047 :
    entryBoolean 46 = true := by
  rfl

theorem classicalConfigurationProvenance_cf048 :
    entryBoolean 47 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk02_checker :
    chunkBoolean 2 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf033
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf034
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf035
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf036
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf037
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf038
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf039
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf040
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf041
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf042
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf043
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf044
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf045
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf046
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf047
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf048

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
