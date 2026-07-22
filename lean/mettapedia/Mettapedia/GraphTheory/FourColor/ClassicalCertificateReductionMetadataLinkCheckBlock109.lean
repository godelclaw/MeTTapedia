import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry436_checker :
    entryBoolean 436 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry437_checker :
    entryBoolean 437 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry438_checker :
    entryBoolean 438 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry439_checker :
    entryBoolean 439 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock109_checker :
    chunkBoolean 109 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry436_checker,
      classicalReductionMetadataLinkEntry437_checker,
      classicalReductionMetadataLinkEntry438_checker,
      classicalReductionMetadataLinkEntry439_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
