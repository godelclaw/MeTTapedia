import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry620_checker :
    entryBoolean 620 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry621_checker :
    entryBoolean 621 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry622_checker :
    entryBoolean 622 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry623_checker :
    entryBoolean 623 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock155_checker :
    chunkBoolean 155 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry620_checker,
      classicalReductionMetadataLinkEntry621_checker,
      classicalReductionMetadataLinkEntry622_checker,
      classicalReductionMetadataLinkEntry623_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
