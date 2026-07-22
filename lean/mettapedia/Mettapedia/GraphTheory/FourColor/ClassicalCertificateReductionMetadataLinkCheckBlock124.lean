import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry496_checker :
    entryBoolean 496 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry497_checker :
    entryBoolean 497 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry498_checker :
    entryBoolean 498 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry499_checker :
    entryBoolean 499 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock124_checker :
    chunkBoolean 124 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry496_checker,
      classicalReductionMetadataLinkEntry497_checker,
      classicalReductionMetadataLinkEntry498_checker,
      classicalReductionMetadataLinkEntry499_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
