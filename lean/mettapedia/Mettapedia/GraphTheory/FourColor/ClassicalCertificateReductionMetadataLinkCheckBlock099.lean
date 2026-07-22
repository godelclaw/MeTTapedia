import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry396_checker :
    entryBoolean 396 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry397_checker :
    entryBoolean 397 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry398_checker :
    entryBoolean 398 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry399_checker :
    entryBoolean 399 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock099_checker :
    chunkBoolean 99 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry396_checker,
      classicalReductionMetadataLinkEntry397_checker,
      classicalReductionMetadataLinkEntry398_checker,
      classicalReductionMetadataLinkEntry399_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
