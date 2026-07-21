import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchShape
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBlueZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBlueRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBlueBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBluePurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueContractSearchBlue_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .blue)
          [(twentiethCatalogueContractSearchFirstComponent, .blue)]
            twentiethCatalogueContractSearchRemaining = true := by
  change
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .blue)
          [(twentiethCatalogueContractSearchFirstComponent, .blue)]
            (twentiethCatalogueContractSearchSecondComponent ::
              twentiethCatalogueContractSearchTail) = true
  apply SearchTree.checkBy_of_isNode_and_children
  · exact twentiethCatalogueContractSearchBlue_isNode
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchBlueZero_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchBlueRed_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchBlueBlue_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchBluePurple_checker

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
