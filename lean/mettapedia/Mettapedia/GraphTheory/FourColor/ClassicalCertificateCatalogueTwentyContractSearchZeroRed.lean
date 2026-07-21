import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueContractSearchZeroRed_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchBranch .zero .red)
          [(twentiethCatalogueContractSearchSecondComponent, .red),
            (twentiethCatalogueContractSearchFirstComponent, .zero)]
              twentiethCatalogueContractSearchTail = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
