import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry404_checker :
    entryBoolean 404 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry405_checker :
    entryBoolean 405 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry406_checker :
    entryBoolean 406 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry407_checker :
    entryBoolean 407 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock101_checker :
    chunkBoolean 101 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry404_checker,
      classicalReductionMetadataLinkEntry405_checker,
      classicalReductionMetadataLinkEntry406_checker,
      classicalReductionMetadataLinkEntry407_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
