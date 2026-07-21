import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractColorSearch

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateContractColorSearch

open ClassicalCertificateConfiguration
open ClassicalCertificateContractComponents
open ClassicalCertificateFacePartition

namespace SearchTree

def isNode : SearchTree → Bool
  | .node _ _ _ _ => true
  | _ => false

/-- A four-way search node checks by composing its four independently checked
color branches. -/
theorem checkBy_of_isNode_and_children {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    {partitionValid : ClassicalCertificateFacePartition.Valid hypermap partition}
    {contract : Finset (Fin hypermap.dartCount)}
    {components : ClassicalCertificateContractComponents.Code}
    (componentsValid : ClassicalCertificateContractComponents.Valid
      partitionValid contract components)
    (ring : List (Fin hypermap.dartCount))
    (accepts : List ClassicalCertificateTraceTree.TraceSymbol → Bool)
    (tree : SearchTree)
    (assigned : List (AssignedColor components.componentCount))
    (component : Fin components.componentCount)
    (remaining : List (Fin components.componentCount))
    (hnode : tree.isNode = true)
    (hzero : checkBy componentsValid ring accepts (tree.child .zero)
      ((component, .zero) :: assigned) remaining = true)
    (hred : checkBy componentsValid ring accepts (tree.child .red)
      ((component, .red) :: assigned) remaining = true)
    (hblue : checkBy componentsValid ring accepts (tree.child .blue)
      ((component, .blue) :: assigned) remaining = true)
    (hpurple : checkBy componentsValid ring accepts (tree.child .purple)
      ((component, .purple) :: assigned) remaining = true) :
    checkBy componentsValid ring accepts tree assigned
      (component :: remaining) = true := by
  cases tree with
  | reject => simp [isNode] at hnode
  | accept => simp [isNode] at hnode
  | node zero red blue purple =>
      simp only [SearchTree.child] at hzero hred hblue hpurple
      simp [checkBy, hzero, hred, hblue, hpurple]

end SearchTree

end ClassicalCertificateContractColorSearch

end Mettapedia.GraphTheory.FourColor
