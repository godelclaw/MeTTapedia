import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry352_checker :
    entryBoolean 352 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry353_checker :
    entryBoolean 353 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry354_checker :
    entryBoolean 354 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry355_checker :
    entryBoolean 355 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock088_checker :
    chunkBoolean 88 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry352_checker,
      classicalReductionMetadataLinkEntry353_checker,
      classicalReductionMetadataLinkEntry354_checker,
      classicalReductionMetadataLinkEntry355_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
