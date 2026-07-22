import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry524_checker :
    entryBoolean 524 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry525_checker :
    entryBoolean 525 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry526_checker :
    entryBoolean 526 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry527_checker :
    entryBoolean 527 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock131_checker :
    chunkBoolean 131 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry524_checker,
      classicalReductionMetadataLinkEntry525_checker,
      classicalReductionMetadataLinkEntry526_checker,
      classicalReductionMetadataLinkEntry527_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
