import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry532_checker :
    entryBoolean 532 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry533_checker :
    entryBoolean 533 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry534_checker :
    entryBoolean 534 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry535_checker :
    entryBoolean 535 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock133_checker :
    chunkBoolean 133 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry532_checker,
      classicalReductionMetadataLinkEntry533_checker,
      classicalReductionMetadataLinkEntry534_checker,
      classicalReductionMetadataLinkEntry535_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
