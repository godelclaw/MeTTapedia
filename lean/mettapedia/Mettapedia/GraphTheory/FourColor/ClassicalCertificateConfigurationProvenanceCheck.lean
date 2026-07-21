import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk00
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk01
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk02
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk03
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk04
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk05
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk06
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk07
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk08
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk09
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk10
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk11
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk12
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk13
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk14
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk15
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk16
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk17
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk18
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk19
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk20
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk21
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk22
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk23
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk24
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk25
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk26
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk27
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk28
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk29
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk30
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk31
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk32
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk33
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk34
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk35
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk36
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk37
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk38
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk39
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

open ClassicalCertificateCatalogueHypermaps
open ClassicalCertificateCataloguePrograms
open ClassicalCertificateConfiguration
open ClassicalCertificateHypermapCatalogue

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Every published construction program materializes exactly to its indexed
finite-hypermap certificate. -/
theorem classicalConfigurationProvenance_checker :
    checker = true := by
  change (List.range 40).all chunkBoolean = true
  apply List.all_eq_true.2
  intro chunk hchunk
  have hlt : chunk < 40 := List.mem_range.1 hchunk
  interval_cases chunk <;>
    simp only [
      classicalConfigurationProvenanceChunk00_checker,
      classicalConfigurationProvenanceChunk01_checker,
      classicalConfigurationProvenanceChunk02_checker,
      classicalConfigurationProvenanceChunk03_checker,
      classicalConfigurationProvenanceChunk04_checker,
      classicalConfigurationProvenanceChunk05_checker,
      classicalConfigurationProvenanceChunk06_checker,
      classicalConfigurationProvenanceChunk07_checker,
      classicalConfigurationProvenanceChunk08_checker,
      classicalConfigurationProvenanceChunk09_checker,
      classicalConfigurationProvenanceChunk10_checker,
      classicalConfigurationProvenanceChunk11_checker,
      classicalConfigurationProvenanceChunk12_checker,
      classicalConfigurationProvenanceChunk13_checker,
      classicalConfigurationProvenanceChunk14_checker,
      classicalConfigurationProvenanceChunk15_checker,
      classicalConfigurationProvenanceChunk16_checker,
      classicalConfigurationProvenanceChunk17_checker,
      classicalConfigurationProvenanceChunk18_checker,
      classicalConfigurationProvenanceChunk19_checker,
      classicalConfigurationProvenanceChunk20_checker,
      classicalConfigurationProvenanceChunk21_checker,
      classicalConfigurationProvenanceChunk22_checker,
      classicalConfigurationProvenanceChunk23_checker,
      classicalConfigurationProvenanceChunk24_checker,
      classicalConfigurationProvenanceChunk25_checker,
      classicalConfigurationProvenanceChunk26_checker,
      classicalConfigurationProvenanceChunk27_checker,
      classicalConfigurationProvenanceChunk28_checker,
      classicalConfigurationProvenanceChunk29_checker,
      classicalConfigurationProvenanceChunk30_checker,
      classicalConfigurationProvenanceChunk31_checker,
      classicalConfigurationProvenanceChunk32_checker,
      classicalConfigurationProvenanceChunk33_checker,
      classicalConfigurationProvenanceChunk34_checker,
      classicalConfigurationProvenanceChunk35_checker,
      classicalConfigurationProvenanceChunk36_checker,
      classicalConfigurationProvenanceChunk37_checker,
      classicalConfigurationProvenanceChunk38_checker,
      classicalConfigurationProvenanceChunk39_checker
    ]

/-- Every published index contains a construction program, its exact exported
map, and a proof that this map is a standard finite hypermap. -/
theorem exists_accepted_materialized_classicalConfiguration
    (index : Nat) (hindex : index < 633) :
    ∃ configuration code,
      classicalConfigurationCatalogue.programAt? index = some configuration ∧
        classicalHypermapCatalogue.codeAt? index = some code ∧
        HypermapCode.materialize configuration.compile.pointee =
          code.hypermap ∧
        code.hypermap.Accepted := by
  have hcatalogueIndex : index < catalogueCount := by
    simpa [catalogueCount] using hindex
  obtain ⟨configuration, code, hconfiguration, hcode, hmaterialize⟩ :=
    exists_materialized_eq_of_checker_true
      classicalConfigurationProvenance_checker index hcatalogueIndex
  refine ⟨configuration, code, hconfiguration, hcode, hmaterialize, ?_⟩
  apply classicalHypermapCatalogue.accepted_of_checker_true
    classicalHypermapCatalogue_checker index
  · rw [classicalHypermapCatalogue_valueBound]
    omega
  · exact hcode

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
