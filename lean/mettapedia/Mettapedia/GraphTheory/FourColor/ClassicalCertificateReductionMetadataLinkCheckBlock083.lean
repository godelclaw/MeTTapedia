import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry332_checker :
    entryBoolean 332 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry333_checker :
    entryBoolean 333 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry334_checker :
    entryBoolean 334 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry335_checker :
    entryBoolean 335 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock083_checker :
    chunkBoolean 83 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry332_checker,
      classicalReductionMetadataLinkEntry333_checker,
      classicalReductionMetadataLinkEntry334_checker,
      classicalReductionMetadataLinkEntry335_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
