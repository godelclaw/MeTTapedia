import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry604_checker :
    entryBoolean 604 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry605_checker :
    entryBoolean 605 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry606_checker :
    entryBoolean 606 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry607_checker :
    entryBoolean 607 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock151_checker :
    chunkBoolean 151 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry604_checker,
      classicalReductionMetadataLinkEntry605_checker,
      classicalReductionMetadataLinkEntry606_checker,
      classicalReductionMetadataLinkEntry607_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
