import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry424_checker :
    entryBoolean 424 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry425_checker :
    entryBoolean 425 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry426_checker :
    entryBoolean 426 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry427_checker :
    entryBoolean 427 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock106_checker :
    chunkBoolean 106 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry424_checker,
      classicalReductionMetadataLinkEntry425_checker,
      classicalReductionMetadataLinkEntry426_checker,
      classicalReductionMetadataLinkEntry427_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
