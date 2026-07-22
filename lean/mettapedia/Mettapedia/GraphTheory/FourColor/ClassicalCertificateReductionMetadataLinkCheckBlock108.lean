import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry432_checker :
    entryBoolean 432 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry433_checker :
    entryBoolean 433 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry434_checker :
    entryBoolean 434 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry435_checker :
    entryBoolean 435 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock108_checker :
    chunkBoolean 108 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry432_checker,
      classicalReductionMetadataLinkEntry433_checker,
      classicalReductionMetadataLinkEntry434_checker,
      classicalReductionMetadataLinkEntry435_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
