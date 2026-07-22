import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry616_checker :
    entryBoolean 616 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry617_checker :
    entryBoolean 617 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry618_checker :
    entryBoolean 618 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry619_checker :
    entryBoolean 619 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock154_checker :
    chunkBoolean 154 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry616_checker,
      classicalReductionMetadataLinkEntry617_checker,
      classicalReductionMetadataLinkEntry618_checker,
      classicalReductionMetadataLinkEntry619_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
