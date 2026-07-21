import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueContractSearchBlueBlue_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchBranch .blue .blue)
          [(twentiethCatalogueContractSearchSecondComponent, .blue),
            (twentiethCatalogueContractSearchFirstComponent, .blue)]
              twentiethCatalogueContractSearchTail = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
