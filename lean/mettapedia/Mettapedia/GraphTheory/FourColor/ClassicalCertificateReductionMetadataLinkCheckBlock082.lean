import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry328_checker :
    entryBoolean 328 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry329_checker :
    entryBoolean 329 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry330_checker :
    entryBoolean 330 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry331_checker :
    entryBoolean 331 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock082_checker :
    chunkBoolean 82 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry328_checker,
      classicalReductionMetadataLinkEntry329_checker,
      classicalReductionMetadataLinkEntry330_checker,
      classicalReductionMetadataLinkEntry331_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
