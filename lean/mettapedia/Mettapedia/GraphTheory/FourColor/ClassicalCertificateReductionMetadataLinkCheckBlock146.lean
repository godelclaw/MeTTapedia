import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry584_checker :
    entryBoolean 584 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry585_checker :
    entryBoolean 585 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry586_checker :
    entryBoolean 586 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry587_checker :
    entryBoolean 587 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock146_checker :
    chunkBoolean 146 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry584_checker,
      classicalReductionMetadataLinkEntry585_checker,
      classicalReductionMetadataLinkEntry586_checker,
      classicalReductionMetadataLinkEntry587_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
