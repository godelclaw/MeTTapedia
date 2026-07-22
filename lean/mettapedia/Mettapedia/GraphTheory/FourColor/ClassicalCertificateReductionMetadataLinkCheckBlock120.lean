import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry480_checker :
    entryBoolean 480 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry481_checker :
    entryBoolean 481 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry482_checker :
    entryBoolean 482 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry483_checker :
    entryBoolean 483 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock120_checker :
    chunkBoolean 120 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry480_checker,
      classicalReductionMetadataLinkEntry481_checker,
      classicalReductionMetadataLinkEntry482_checker,
      classicalReductionMetadataLinkEntry483_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
