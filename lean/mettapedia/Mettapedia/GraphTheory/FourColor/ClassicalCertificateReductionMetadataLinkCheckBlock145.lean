import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry580_checker :
    entryBoolean 580 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry581_checker :
    entryBoolean 581 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry582_checker :
    entryBoolean 582 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry583_checker :
    entryBoolean 583 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock145_checker :
    chunkBoolean 145 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry580_checker,
      classicalReductionMetadataLinkEntry581_checker,
      classicalReductionMetadataLinkEntry582_checker,
      classicalReductionMetadataLinkEntry583_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
