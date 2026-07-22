import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry452_checker :
    entryBoolean 452 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry453_checker :
    entryBoolean 453 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry454_checker :
    entryBoolean 454 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry455_checker :
    entryBoolean 455 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock113_checker :
    chunkBoolean 113 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry452_checker,
      classicalReductionMetadataLinkEntry453_checker,
      classicalReductionMetadataLinkEntry454_checker,
      classicalReductionMetadataLinkEntry455_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
