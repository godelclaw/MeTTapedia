import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry472_checker :
    entryBoolean 472 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry473_checker :
    entryBoolean 473 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry474_checker :
    entryBoolean 474 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry475_checker :
    entryBoolean 475 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock118_checker :
    chunkBoolean 118 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry472_checker,
      classicalReductionMetadataLinkEntry473_checker,
      classicalReductionMetadataLinkEntry474_checker,
      classicalReductionMetadataLinkEntry475_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
