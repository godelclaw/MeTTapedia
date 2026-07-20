import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentySourceLayerOnePurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentySourceLayerOne

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateCatalogueTwentyResponseTree
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTreeRankedKempe
open ClassicalCertificateTreeIndexedLayeredKempe
open ClassicalCertificateCatalogueTwentySourceLayerOneRed
open ClassicalCertificateCatalogueTwentySourceLayerOneBlueRed
open ClassicalCertificateCatalogueTwentySourceLayerOneBlueBlue
open ClassicalCertificateCatalogueTwentySourceLayerOneBluePurple
open ClassicalCertificateCatalogueTwentySourceLayerOnePurple

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private theorem acceptedWords_succ_of_node (length : Nat)
    (code : ClassicalCertificateTraceDag.Code) (root red blue purple : Nat)
    (hnode : ClassicalCertificateTraceDag.nodeAt code root =
      ClassicalCertificateTraceDag.NodeCode.node red blue purple) :
    ClassicalCertificateTraceDag.acceptedWords (length + 1) code root =
      (ClassicalCertificateTraceDag.acceptedWords length code red).map
          (prependSymbol .red) ++
        (ClassicalCertificateTraceDag.acceptedWords length code blue).map
          (prependSymbol .blue) ++
        (ClassicalCertificateTraceDag.acceptedWords length code purple).map
          (prependSymbol .purple) := by
  simp [ClassicalCertificateTraceDag.acceptedWords, hnode]

theorem twentiethCatalogueSourceLayer01 :
    ClassicalCertificateTreeIndexedLayeredKempe.layerBoolean
      twentiethCatalogueIndexedKempeCertificate twentiethCatalogueResponseTree
        1 = true := by
  have hroot : ClassicalCertificateTraceDag.nodeAt
      twentiethCatalogueIndexedKempeCertificate.traceCode
        (twentiethCatalogueIndexedKempeCertificate.rootAt 1) =
      ClassicalCertificateTraceDag.NodeCode.node 1921 2872 3010 := by
    rfl
  have hblue : ClassicalCertificateTraceDag.nodeAt
      twentiethCatalogueIndexedKempeCertificate.traceCode 2872 =
      ClassicalCertificateTraceDag.NodeCode.node 2174 2605 2871 := by
    rfl
  unfold ClassicalCertificateTreeIndexedLayeredKempe.layerBoolean
  rw [acceptedWords_succ_of_node 11 _ _ _ _ _ hroot]
  rw [acceptedWords_succ_of_node 10 _ _ _ _ _ hblue]
  simp only [List.map_append, List.map_map, List.all_append, List.all_map,
    Function.comp_apply]
  have hred :
      (ClassicalCertificateTraceDag.acceptedWords 11
        twentiethCatalogueIndexedKempeCertificate.traceCode 1921).all
          (ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
            twentiethCatalogueIndexedKempeCertificate
              twentiethCatalogueResponseTree 1 ∘ prependSymbol .red) =
        twentiethCatalogueLayerOneRedBoolean := by rfl
  have hblueRed :
      (ClassicalCertificateTraceDag.acceptedWords 10
        twentiethCatalogueIndexedKempeCertificate.traceCode 2174).all
          (ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
              twentiethCatalogueIndexedKempeCertificate
                twentiethCatalogueResponseTree 1 ∘
            prependSymbol .blue ∘ prependSymbol .red) =
        twentiethCatalogueLayerOneBlueRedBoolean := by rfl
  have hblueBlue :
      (ClassicalCertificateTraceDag.acceptedWords 10
        twentiethCatalogueIndexedKempeCertificate.traceCode 2605).all
          (ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
              twentiethCatalogueIndexedKempeCertificate
                twentiethCatalogueResponseTree 1 ∘
            prependSymbol .blue ∘ prependSymbol .blue) =
        twentiethCatalogueLayerOneBlueBlueBoolean := by rfl
  have hbluePurple :
      (ClassicalCertificateTraceDag.acceptedWords 10
        twentiethCatalogueIndexedKempeCertificate.traceCode 2871).all
          (ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
              twentiethCatalogueIndexedKempeCertificate
                twentiethCatalogueResponseTree 1 ∘
            prependSymbol .blue ∘ prependSymbol .purple) =
        twentiethCatalogueLayerOneBluePurpleBoolean := by rfl
  have hpurple :
      (ClassicalCertificateTraceDag.acceptedWords 11
        twentiethCatalogueIndexedKempeCertificate.traceCode 3010).all
          (ClassicalCertificateTreeIndexedLayeredKempe.ruleBoolean
            twentiethCatalogueIndexedKempeCertificate
              twentiethCatalogueResponseTree 1 ∘ prependSymbol .purple) =
        twentiethCatalogueLayerOnePurpleBoolean := by rfl
  rw [hred, hblueRed, hblueBlue, hbluePurple, hpurple]
  simp [twentiethCatalogueLayerOneRed_checker,
    twentiethCatalogueLayerOneBlueRed_checker,
    twentiethCatalogueLayerOneBlueBlue_checker,
    twentiethCatalogueLayerOneBluePurple_checker,
    twentiethCatalogueLayerOnePurple_checker]

end ClassicalCertificateCatalogueTwentySourceLayerOne

end Mettapedia.GraphTheory.FourColor
