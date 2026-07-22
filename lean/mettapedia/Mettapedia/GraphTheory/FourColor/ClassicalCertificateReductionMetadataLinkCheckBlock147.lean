import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry588_checker :
    entryBoolean 588 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry589_checker :
    entryBoolean 589 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry590_checker :
    entryBoolean 590 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry591_checker :
    entryBoolean 591 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock147_checker :
    chunkBoolean 147 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry588_checker,
      classicalReductionMetadataLinkEntry589_checker,
      classicalReductionMetadataLinkEntry590_checker,
      classicalReductionMetadataLinkEntry591_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
