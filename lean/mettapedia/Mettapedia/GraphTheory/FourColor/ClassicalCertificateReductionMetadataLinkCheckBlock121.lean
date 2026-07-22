import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry484_checker :
    entryBoolean 484 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry485_checker :
    entryBoolean 485 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry486_checker :
    entryBoolean 486 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry487_checker :
    entryBoolean 487 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock121_checker :
    chunkBoolean 121 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry484_checker,
      classicalReductionMetadataLinkEntry485_checker,
      classicalReductionMetadataLinkEntry486_checker,
      classicalReductionMetadataLinkEntry487_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
