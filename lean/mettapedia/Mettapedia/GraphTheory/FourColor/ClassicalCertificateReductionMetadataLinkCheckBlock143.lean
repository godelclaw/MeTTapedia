import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry572_checker :
    entryBoolean 572 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry573_checker :
    entryBoolean 573 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry574_checker :
    entryBoolean 574 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry575_checker :
    entryBoolean 575 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock143_checker :
    chunkBoolean 143 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry572_checker,
      classicalReductionMetadataLinkEntry573_checker,
      classicalReductionMetadataLinkEntry574_checker,
      classicalReductionMetadataLinkEntry575_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
