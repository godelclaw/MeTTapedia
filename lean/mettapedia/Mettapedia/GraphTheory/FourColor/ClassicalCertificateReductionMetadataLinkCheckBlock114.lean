import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry456_checker :
    entryBoolean 456 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry457_checker :
    entryBoolean 457 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry458_checker :
    entryBoolean 458 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry459_checker :
    entryBoolean 459 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock114_checker :
    chunkBoolean 114 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry456_checker,
      classicalReductionMetadataLinkEntry457_checker,
      classicalReductionMetadataLinkEntry458_checker,
      classicalReductionMetadataLinkEntry459_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
