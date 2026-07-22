import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry428_checker :
    entryBoolean 428 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry429_checker :
    entryBoolean 429 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry430_checker :
    entryBoolean 430 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry431_checker :
    entryBoolean 431 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock107_checker :
    chunkBoolean 107 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry428_checker,
      classicalReductionMetadataLinkEntry429_checker,
      classicalReductionMetadataLinkEntry430_checker,
      classicalReductionMetadataLinkEntry431_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
