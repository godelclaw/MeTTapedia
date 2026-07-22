import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry596_checker :
    entryBoolean 596 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry597_checker :
    entryBoolean 597 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry598_checker :
    entryBoolean 598 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry599_checker :
    entryBoolean 599 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock149_checker :
    chunkBoolean 149 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry596_checker,
      classicalReductionMetadataLinkEntry597_checker,
      classicalReductionMetadataLinkEntry598_checker,
      classicalReductionMetadataLinkEntry599_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
