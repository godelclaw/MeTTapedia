import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry504_checker :
    entryBoolean 504 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry505_checker :
    entryBoolean 505 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry506_checker :
    entryBoolean 506 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry507_checker :
    entryBoolean 507 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock126_checker :
    chunkBoolean 126 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry504_checker,
      classicalReductionMetadataLinkEntry505_checker,
      classicalReductionMetadataLinkEntry506_checker,
      classicalReductionMetadataLinkEntry507_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
