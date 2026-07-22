import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry340_checker :
    entryBoolean 340 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry341_checker :
    entryBoolean 341 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry342_checker :
    entryBoolean 342 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry343_checker :
    entryBoolean 343 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock085_checker :
    chunkBoolean 85 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry340_checker,
      classicalReductionMetadataLinkEntry341_checker,
      classicalReductionMetadataLinkEntry342_checker,
      classicalReductionMetadataLinkEntry343_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
