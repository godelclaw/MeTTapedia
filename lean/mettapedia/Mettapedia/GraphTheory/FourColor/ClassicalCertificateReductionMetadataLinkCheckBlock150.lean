import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry600_checker :
    entryBoolean 600 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry601_checker :
    entryBoolean 601 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry602_checker :
    entryBoolean 602 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry603_checker :
    entryBoolean 603 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock150_checker :
    chunkBoolean 150 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry600_checker,
      classicalReductionMetadataLinkEntry601_checker,
      classicalReductionMetadataLinkEntry602_checker,
      classicalReductionMetadataLinkEntry603_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
