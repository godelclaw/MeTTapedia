import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry512_checker :
    entryBoolean 512 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry513_checker :
    entryBoolean 513 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry514_checker :
    entryBoolean 514 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry515_checker :
    entryBoolean 515 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock128_checker :
    chunkBoolean 128 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry512_checker,
      classicalReductionMetadataLinkEntry513_checker,
      classicalReductionMetadataLinkEntry514_checker,
      classicalReductionMetadataLinkEntry515_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
