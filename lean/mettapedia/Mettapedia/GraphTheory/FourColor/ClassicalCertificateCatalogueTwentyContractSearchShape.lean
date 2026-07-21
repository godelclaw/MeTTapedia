import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchBase
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractColorSearchJoin

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

theorem twentiethCatalogueContractSearch_isNode :
    twentiethCatalogueContractSearch.tree.isNode = true := by
  rfl

theorem twentiethCatalogueContractSearchZero_isNode :
    (twentiethCatalogueContractSearchFirstBranch .zero).isNode = true := by
  rfl

theorem twentiethCatalogueContractSearchRed_isNode :
    (twentiethCatalogueContractSearchFirstBranch .red).isNode = true := by
  rfl

theorem twentiethCatalogueContractSearchBlue_isNode :
    (twentiethCatalogueContractSearchFirstBranch .blue).isNode = true := by
  rfl

theorem twentiethCatalogueContractSearchPurple_isNode :
    (twentiethCatalogueContractSearchFirstBranch .purple).isNode = true := by
  rfl

theorem twentiethCatalogueContractSearch_orderComplete :
    decide twentiethCatalogueContractSearch.OrderComplete = true := by
  decide

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
