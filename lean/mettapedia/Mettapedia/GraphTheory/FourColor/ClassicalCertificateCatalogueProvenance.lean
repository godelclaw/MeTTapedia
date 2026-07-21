import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueProgramsData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsCheck
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwo
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFour
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueProvenance

open ClassicalCertificateCatalogueFour
open ClassicalCertificateCatalogueHypermaps
open ClassicalCertificateCataloguePrograms
open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwo
open ClassicalCertificateConfiguration

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- The indexed program table agrees with each previously certified anchor. -/
theorem classicalConfigurationCatalogue_anchorPrograms :
    classicalConfigurationCatalogue.programAt? 0 =
        some firstCatalogueSample ∧
      classicalConfigurationCatalogue.programAt? 1 =
        some secondCatalogueSample ∧
      classicalConfigurationCatalogue.programAt? 3 =
        some fourthCatalogueSample ∧
      classicalConfigurationCatalogue.programAt? 19 =
        some twentiethCatalogueSample := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The indexed hypermap table agrees exactly with the four independently
certified catalogue anchors. -/
theorem classicalHypermapCatalogue_anchorCodes :
    (classicalHypermapCatalogue.codeAt? 0).map (fun code => code.hypermap) =
        some firstCatalogueSampleCode ∧
      (classicalHypermapCatalogue.codeAt? 1).map (fun code => code.hypermap) =
        some secondCatalogueSampleCode ∧
      (classicalHypermapCatalogue.codeAt? 3).map (fun code => code.hypermap) =
        some fourthCatalogueSampleCode ∧
      (classicalHypermapCatalogue.codeAt? 19).map (fun code => code.hypermap) =
        some twentiethCatalogueSampleCode := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end ClassicalCertificateCatalogueProvenance

end Mettapedia.GraphTheory.FourColor
