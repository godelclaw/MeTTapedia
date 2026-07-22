import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry608_checker :
    entryBoolean 608 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry609_checker :
    entryBoolean 609 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry610_checker :
    entryBoolean 610 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry611_checker :
    entryBoolean 611 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock152_checker :
    chunkBoolean 152 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry608_checker,
      classicalReductionMetadataLinkEntry609_checker,
      classicalReductionMetadataLinkEntry610_checker,
      classicalReductionMetadataLinkEntry611_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
