import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry420_checker :
    entryBoolean 420 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry421_checker :
    entryBoolean 421 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry422_checker :
    entryBoolean 422 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry423_checker :
    entryBoolean 423 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock105_checker :
    chunkBoolean 105 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry420_checker,
      classicalReductionMetadataLinkEntry421_checker,
      classicalReductionMetadataLinkEntry422_checker,
      classicalReductionMetadataLinkEntry423_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
