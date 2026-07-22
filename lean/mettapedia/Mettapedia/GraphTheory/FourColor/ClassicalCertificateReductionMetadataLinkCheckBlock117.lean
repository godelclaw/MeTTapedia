import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry468_checker :
    entryBoolean 468 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry469_checker :
    entryBoolean 469 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry470_checker :
    entryBoolean 470 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry471_checker :
    entryBoolean 471 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock117_checker :
    chunkBoolean 117 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry468_checker,
      classicalReductionMetadataLinkEntry469_checker,
      classicalReductionMetadataLinkEntry470_checker,
      classicalReductionMetadataLinkEntry471_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
