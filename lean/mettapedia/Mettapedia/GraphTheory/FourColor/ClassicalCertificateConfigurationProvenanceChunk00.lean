import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf001 :
    entryBoolean 0 = true := by
  rfl

theorem classicalConfigurationProvenance_cf002 :
    entryBoolean 1 = true := by
  rfl

theorem classicalConfigurationProvenance_cf003 :
    entryBoolean 2 = true := by
  rfl

theorem classicalConfigurationProvenance_cf004 :
    entryBoolean 3 = true := by
  rfl

theorem classicalConfigurationProvenance_cf005 :
    entryBoolean 4 = true := by
  rfl

theorem classicalConfigurationProvenance_cf006 :
    entryBoolean 5 = true := by
  rfl

theorem classicalConfigurationProvenance_cf007 :
    entryBoolean 6 = true := by
  rfl

theorem classicalConfigurationProvenance_cf008 :
    entryBoolean 7 = true := by
  rfl

theorem classicalConfigurationProvenance_cf009 :
    entryBoolean 8 = true := by
  rfl

theorem classicalConfigurationProvenance_cf010 :
    entryBoolean 9 = true := by
  rfl

theorem classicalConfigurationProvenance_cf011 :
    entryBoolean 10 = true := by
  rfl

theorem classicalConfigurationProvenance_cf012 :
    entryBoolean 11 = true := by
  rfl

theorem classicalConfigurationProvenance_cf013 :
    entryBoolean 12 = true := by
  rfl

theorem classicalConfigurationProvenance_cf014 :
    entryBoolean 13 = true := by
  rfl

theorem classicalConfigurationProvenance_cf015 :
    entryBoolean 14 = true := by
  rfl

theorem classicalConfigurationProvenance_cf016 :
    entryBoolean 15 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk00_checker :
    chunkBoolean 0 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf001
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf002
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf003
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf004
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf005
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf006
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf007
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf008
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf009
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf010
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf011
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf012
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf013
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf014
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf015
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf016

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
