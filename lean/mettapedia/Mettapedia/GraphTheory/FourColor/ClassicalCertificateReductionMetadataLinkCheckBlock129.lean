import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry516_checker :
    entryBoolean 516 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry517_checker :
    entryBoolean 517 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry518_checker :
    entryBoolean 518 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry519_checker :
    entryBoolean 519 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock129_checker :
    chunkBoolean 129 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry516_checker,
      classicalReductionMetadataLinkEntry517_checker,
      classicalReductionMetadataLinkEntry518_checker,
      classicalReductionMetadataLinkEntry519_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
