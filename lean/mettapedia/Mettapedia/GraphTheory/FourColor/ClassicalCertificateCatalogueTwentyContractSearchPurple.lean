import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchShape
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchPurpleZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchPurpleRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchPurpleBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchPurplePurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueContractSearchPurple_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .purple)
          [(twentiethCatalogueContractSearchFirstComponent, .purple)]
            twentiethCatalogueContractSearchRemaining = true := by
  change
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .purple)
          [(twentiethCatalogueContractSearchFirstComponent, .purple)]
            (twentiethCatalogueContractSearchSecondComponent ::
              twentiethCatalogueContractSearchTail) = true
  apply SearchTree.checkBy_of_isNode_and_children
  · exact twentiethCatalogueContractSearchPurple_isNode
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchPurpleZero_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchPurpleRed_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchPurpleBlue_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchPurplePurple_checker

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
