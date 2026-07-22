import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry376_checker :
    entryBoolean 376 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry377_checker :
    entryBoolean 377 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry378_checker :
    entryBoolean 378 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry379_checker :
    entryBoolean 379 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock094_checker :
    chunkBoolean 94 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry376_checker,
      classicalReductionMetadataLinkEntry377_checker,
      classicalReductionMetadataLinkEntry378_checker,
      classicalReductionMetadataLinkEntry379_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
