import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry476_checker :
    entryBoolean 476 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry477_checker :
    entryBoolean 477 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry478_checker :
    entryBoolean 478 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry479_checker :
    entryBoolean 479 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock119_checker :
    chunkBoolean 119 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry476_checker,
      classicalReductionMetadataLinkEntry477_checker,
      classicalReductionMetadataLinkEntry478_checker,
      classicalReductionMetadataLinkEntry479_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
