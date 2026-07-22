import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry612_checker :
    entryBoolean 612 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry613_checker :
    entryBoolean 613 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry614_checker :
    entryBoolean 614 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry615_checker :
    entryBoolean 615 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock153_checker :
    chunkBoolean 153 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry612_checker,
      classicalReductionMetadataLinkEntry613_checker,
      classicalReductionMetadataLinkEntry614_checker,
      classicalReductionMetadataLinkEntry615_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
