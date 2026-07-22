import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry408_checker :
    entryBoolean 408 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry409_checker :
    entryBoolean 409 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry410_checker :
    entryBoolean 410 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry411_checker :
    entryBoolean 411 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock102_checker :
    chunkBoolean 102 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry408_checker,
      classicalReductionMetadataLinkEntry409_checker,
      classicalReductionMetadataLinkEntry410_checker,
      classicalReductionMetadataLinkEntry411_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
