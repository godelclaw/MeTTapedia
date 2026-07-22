import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry544_checker :
    entryBoolean 544 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry545_checker :
    entryBoolean 545 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry546_checker :
    entryBoolean 546 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry547_checker :
    entryBoolean 547 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock136_checker :
    chunkBoolean 136 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry544_checker,
      classicalReductionMetadataLinkEntry545_checker,
      classicalReductionMetadataLinkEntry546_checker,
      classicalReductionMetadataLinkEntry547_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
