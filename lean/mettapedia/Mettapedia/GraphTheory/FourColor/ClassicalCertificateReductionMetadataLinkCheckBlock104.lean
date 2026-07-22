import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataLink

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLinkCheck

open ClassicalCertificateReductionMetadataLink

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private theorem classicalReductionMetadataLinkEntry416_checker :
    entryBoolean 416 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry417_checker :
    entryBoolean 417 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry418_checker :
    entryBoolean 418 = true := by
  rfl

private theorem classicalReductionMetadataLinkEntry419_checker :
    entryBoolean 419 = true := by
  rfl

theorem classicalReductionMetadataLinkBlock104_checker :
    chunkBoolean 104 = true := by
  rw [chunkBoolean, List.all_eq_true]
  intro offset hoffset
  simp [chunkSize] at hoffset
  have hoffset' : offset ≤ 3 := by omega
  interval_cases offset <;>
    simp [chunkSize,
      classicalReductionMetadataLinkEntry416_checker,
      classicalReductionMetadataLinkEntry417_checker,
      classicalReductionMetadataLinkEntry418_checker,
      classicalReductionMetadataLinkEntry419_checker]

end ClassicalCertificateReductionMetadataLinkCheck

end Mettapedia.GraphTheory.FourColor
