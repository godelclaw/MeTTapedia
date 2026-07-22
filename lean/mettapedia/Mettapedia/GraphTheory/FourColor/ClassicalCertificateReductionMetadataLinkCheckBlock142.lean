import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry568_checker :
    entryBoolean 568 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry569_checker :
    entryBoolean 569 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry570_checker :
    entryBoolean 570 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry571_checker :
    entryBoolean 571 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock142_checker :
    chunkBoolean 142 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry568_checker,
      classicalReductionMetadataLinkEntry569_checker,
      classicalReductionMetadataLinkEntry570_checker,
      classicalReductionMetadataLinkEntry571_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
