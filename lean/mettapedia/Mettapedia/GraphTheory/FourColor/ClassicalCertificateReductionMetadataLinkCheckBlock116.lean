import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry464_checker :
    entryBoolean 464 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry465_checker :
    entryBoolean 465 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry466_checker :
    entryBoolean 466 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry467_checker :
    entryBoolean 467 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock116_checker :
    chunkBoolean 116 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry464_checker,
      classicalReductionMetadataLinkEntry465_checker,
      classicalReductionMetadataLinkEntry466_checker,
      classicalReductionMetadataLinkEntry467_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
