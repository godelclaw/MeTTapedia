import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry360_checker :
    entryBoolean 360 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry361_checker :
    entryBoolean 361 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry362_checker :
    entryBoolean 362 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry363_checker :
    entryBoolean 363 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock090_checker :
    chunkBoolean 90 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry360_checker,
      classicalReductionMetadataLinkEntry361_checker,
      classicalReductionMetadataLinkEntry362_checker,
      classicalReductionMetadataLinkEntry363_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
