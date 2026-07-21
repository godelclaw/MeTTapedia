import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueContractSearchRedRed_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchBranch .red .red)
          [(twentiethCatalogueContractSearchSecondComponent, .red),
            (twentiethCatalogueContractSearchFirstComponent, .red)]
              twentiethCatalogueContractSearchTail = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
