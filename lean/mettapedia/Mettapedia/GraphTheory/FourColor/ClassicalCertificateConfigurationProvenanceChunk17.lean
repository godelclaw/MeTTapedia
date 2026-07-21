import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenance

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalConfigurationProvenance_cf273 :
    entryBoolean 272 = true := by
  rfl

theorem classicalConfigurationProvenance_cf274 :
    entryBoolean 273 = true := by
  rfl

theorem classicalConfigurationProvenance_cf275 :
    entryBoolean 274 = true := by
  rfl

theorem classicalConfigurationProvenance_cf276 :
    entryBoolean 275 = true := by
  rfl

theorem classicalConfigurationProvenance_cf277 :
    entryBoolean 276 = true := by
  rfl

theorem classicalConfigurationProvenance_cf278 :
    entryBoolean 277 = true := by
  rfl

theorem classicalConfigurationProvenance_cf279 :
    entryBoolean 278 = true := by
  rfl

theorem classicalConfigurationProvenance_cf280 :
    entryBoolean 279 = true := by
  rfl

theorem classicalConfigurationProvenance_cf281 :
    entryBoolean 280 = true := by
  rfl

theorem classicalConfigurationProvenance_cf282 :
    entryBoolean 281 = true := by
  rfl

theorem classicalConfigurationProvenance_cf283 :
    entryBoolean 282 = true := by
  rfl

theorem classicalConfigurationProvenance_cf284 :
    entryBoolean 283 = true := by
  rfl

theorem classicalConfigurationProvenance_cf285 :
    entryBoolean 284 = true := by
  rfl

theorem classicalConfigurationProvenance_cf286 :
    entryBoolean 285 = true := by
  rfl

theorem classicalConfigurationProvenance_cf287 :
    entryBoolean 286 = true := by
  rfl

theorem classicalConfigurationProvenance_cf288 :
    entryBoolean 287 = true := by
  rfl

theorem classicalConfigurationProvenanceChunk17_checker :
    chunkBoolean 17 = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hlt : offset < chunkSize := List.mem_range.1 hoffset
  simp only [chunkSize] at hlt
  interval_cases offset
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf273
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf274
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf275
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf276
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf277
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf278
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf279
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf280
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf281
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf282
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf283
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf284
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf285
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf286
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf287
  · simpa [chunkSize, catalogueCount] using classicalConfigurationProvenance_cf288

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
