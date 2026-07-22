import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry384_checker :
    entryBoolean 384 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry385_checker :
    entryBoolean 385 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry386_checker :
    entryBoolean 386 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry387_checker :
    entryBoolean 387 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock096_checker :
    chunkBoolean 96 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry384_checker,
      classicalReductionMetadataLinkEntry385_checker,
      classicalReductionMetadataLinkEntry386_checker,
      classicalReductionMetadataLinkEntry387_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
