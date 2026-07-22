import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry448_checker :
    entryBoolean 448 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry449_checker :
    entryBoolean 449 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry450_checker :
    entryBoolean 450 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry451_checker :
    entryBoolean 451 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock112_checker :
    chunkBoolean 112 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry448_checker,
      classicalReductionMetadataLinkEntry449_checker,
      classicalReductionMetadataLinkEntry450_checker,
      classicalReductionMetadataLinkEntry451_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
