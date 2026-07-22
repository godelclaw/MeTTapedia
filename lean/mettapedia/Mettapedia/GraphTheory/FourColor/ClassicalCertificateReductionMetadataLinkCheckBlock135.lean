import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry540_checker :
    entryBoolean 540 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry541_checker :
    entryBoolean 541 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry542_checker :
    entryBoolean 542 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry543_checker :
    entryBoolean 543 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock135_checker :
    chunkBoolean 135 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry540_checker,
      classicalReductionMetadataLinkEntry541_checker,
      classicalReductionMetadataLinkEntry542_checker,
      classicalReductionMetadataLinkEntry543_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
