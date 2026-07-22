import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry560_checker :
    entryBoolean 560 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry561_checker :
    entryBoolean 561 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry562_checker :
    entryBoolean 562 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry563_checker :
    entryBoolean 563 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock140_checker :
    chunkBoolean 140 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry560_checker,
      classicalReductionMetadataLinkEntry561_checker,
      classicalReductionMetadataLinkEntry562_checker,
      classicalReductionMetadataLinkEntry563_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
