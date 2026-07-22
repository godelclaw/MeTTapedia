import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry628_checker :
    entryBoolean 628 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry629_checker :
    entryBoolean 629 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry630_checker :
    entryBoolean 630 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry631_checker :
    entryBoolean 631 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock157_checker :
    chunkBoolean 157 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry628_checker,
      classicalReductionMetadataLinkEntry629_checker,
      classicalReductionMetadataLinkEntry630_checker,
      classicalReductionMetadataLinkEntry631_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
