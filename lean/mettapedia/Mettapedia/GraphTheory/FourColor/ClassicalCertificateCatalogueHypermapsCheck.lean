import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks00
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks04
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks08
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks12
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks16
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks20
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks24
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks28
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks32
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsChunks36

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueHypermaps

open ClassicalCertificateFastHypermapCheck
open ClassicalCertificateHypermapCatalogue

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem classicalHypermapCatalogue_valueBound :
    classicalHypermapCatalogue.valueBound = 640 := by
  rfl

/-- All 633 materialized catalogue maps satisfy the standard finite-hypermap
certificate predicate. -/
theorem classicalHypermapCatalogue_checker :
    classicalHypermapCatalogue.checker = true := by
  change
    (List.range 40).all
      (fun chunk => classicalHypermapCatalogue.chunkBoolean chunk) = true
  apply List.all_eq_true.2
  intro chunk hchunk
  have hlt : chunk < 40 := List.mem_range.1 hchunk
  interval_cases chunk <;>
    simp only [classicalHypermapCatalogueChunk00_checker,
      classicalHypermapCatalogueChunk01_checker,
      classicalHypermapCatalogueChunk02_checker,
      classicalHypermapCatalogueChunk03_checker,
      classicalHypermapCatalogueChunk04_checker,
      classicalHypermapCatalogueChunk05_checker,
      classicalHypermapCatalogueChunk06_checker,
      classicalHypermapCatalogueChunk07_checker,
      classicalHypermapCatalogueChunk08_checker,
      classicalHypermapCatalogueChunk09_checker,
      classicalHypermapCatalogueChunk10_checker,
      classicalHypermapCatalogueChunk11_checker,
      classicalHypermapCatalogueChunk12_checker,
      classicalHypermapCatalogueChunk13_checker,
      classicalHypermapCatalogueChunk14_checker,
      classicalHypermapCatalogueChunk15_checker,
      classicalHypermapCatalogueChunk16_checker,
      classicalHypermapCatalogueChunk17_checker,
      classicalHypermapCatalogueChunk18_checker,
      classicalHypermapCatalogueChunk19_checker,
      classicalHypermapCatalogueChunk20_checker,
      classicalHypermapCatalogueChunk21_checker,
      classicalHypermapCatalogueChunk22_checker,
      classicalHypermapCatalogueChunk23_checker,
      classicalHypermapCatalogueChunk24_checker,
      classicalHypermapCatalogueChunk25_checker,
      classicalHypermapCatalogueChunk26_checker,
      classicalHypermapCatalogueChunk27_checker,
      classicalHypermapCatalogueChunk28_checker,
      classicalHypermapCatalogueChunk29_checker,
      classicalHypermapCatalogueChunk30_checker,
      classicalHypermapCatalogueChunk31_checker,
      classicalHypermapCatalogueChunk32_checker,
      classicalHypermapCatalogueChunk33_checker,
      classicalHypermapCatalogueChunk34_checker,
      classicalHypermapCatalogueChunk35_checker,
      classicalHypermapCatalogueChunk36_checker,
      classicalHypermapCatalogueChunk37_checker,
      classicalHypermapCatalogueChunk38_checker,
      classicalHypermapCatalogueChunk39_checker]

/-- Every published catalogue index selects an accepted materialized
finite-hypermap certificate. -/
theorem exists_accepted_classicalHypermapCatalogue_code
    (index : Nat) (hindex : index < 633) :
    ∃ code : InverseCode,
      classicalHypermapCatalogue.codeAt? index = some code ∧
        code.hypermap.Accepted := by
  obtain ⟨code, hcode⟩ :=
    classicalHypermapCatalogue.exists_code_of_populatedPrefixBoolean 633
      classicalHypermapCatalogue_populated index hindex
  refine ⟨code, hcode, ?_⟩
  apply classicalHypermapCatalogue.accepted_of_checker_true
    classicalHypermapCatalogue_checker index
  · rw [classicalHypermapCatalogue_valueBound]
    omega
  · exact hcode

end ClassicalCertificateCatalogueHypermaps

end Mettapedia.GraphTheory.FourColor
