import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry380_checker :
    entryBoolean 380 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry381_checker :
    entryBoolean 381 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry382_checker :
    entryBoolean 382 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry383_checker :
    entryBoolean 383 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock095_checker :
    chunkBoolean 95 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry380_checker,
      classicalReductionMetadataLinkEntry381_checker,
      classicalReductionMetadataLinkEntry382_checker,
      classicalReductionMetadataLinkEntry383_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
