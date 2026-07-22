import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry576_checker :
    entryBoolean 576 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry577_checker :
    entryBoolean 577 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry578_checker :
    entryBoolean 578 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry579_checker :
    entryBoolean 579 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock144_checker :
    chunkBoolean 144 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry576_checker,
      classicalReductionMetadataLinkEntry577_checker,
      classicalReductionMetadataLinkEntry578_checker,
      classicalReductionMetadataLinkEntry579_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
