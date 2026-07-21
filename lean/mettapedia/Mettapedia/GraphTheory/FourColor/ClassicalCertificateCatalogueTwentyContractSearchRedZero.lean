import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBase

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueContractSearchRedZero_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchBranch .red .zero)
          [(twentiethCatalogueContractSearchSecondComponent, .zero),
            (twentiethCatalogueContractSearchFirstComponent, .red)]
              twentiethCatalogueContractSearchTail = true := by
  rfl

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
