import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry440_checker :
    entryBoolean 440 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry441_checker :
    entryBoolean 441 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry442_checker :
    entryBoolean 442 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry443_checker :
    entryBoolean 443 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock110_checker :
    chunkBoolean 110 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry440_checker,
      classicalReductionMetadataLinkEntry441_checker,
      classicalReductionMetadataLinkEntry442_checker,
      classicalReductionMetadataLinkEntry443_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
