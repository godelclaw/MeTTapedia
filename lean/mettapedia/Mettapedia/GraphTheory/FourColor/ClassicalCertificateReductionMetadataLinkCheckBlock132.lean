import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry528_checker :
    entryBoolean 528 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry529_checker :
    entryBoolean 529 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry530_checker :
    entryBoolean 530 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry531_checker :
    entryBoolean 531 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock132_checker :
    chunkBoolean 132 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry528_checker,
      classicalReductionMetadataLinkEntry529_checker,
      classicalReductionMetadataLinkEntry530_checker,
      classicalReductionMetadataLinkEntry531_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
