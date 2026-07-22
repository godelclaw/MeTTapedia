import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry392_checker :
    entryBoolean 392 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry393_checker :
    entryBoolean 393 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry394_checker :
    entryBoolean 394 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry395_checker :
    entryBoolean 395 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock098_checker :
    chunkBoolean 98 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry392_checker,
      classicalReductionMetadataLinkEntry393_checker,
      classicalReductionMetadataLinkEntry394_checker,
      classicalReductionMetadataLinkEntry395_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
