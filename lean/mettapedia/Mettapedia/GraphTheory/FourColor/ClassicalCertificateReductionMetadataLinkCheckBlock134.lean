import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry536_checker :
    entryBoolean 536 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry537_checker :
    entryBoolean 537 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry538_checker :
    entryBoolean 538 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry539_checker :
    entryBoolean 539 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock134_checker :
    chunkBoolean 134 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry536_checker,
      classicalReductionMetadataLinkEntry537_checker,
      classicalReductionMetadataLinkEntry538_checker,
      classicalReductionMetadataLinkEntry539_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
