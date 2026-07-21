import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockPilot

/-!
# Regressions for the exact `SU(2)`, `b = 2` Wilson-block pilot
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2WilsonBlockPilotRegression

open MeasureTheory
open SU2WilsonBlockPilot

example : Fintype.card BlockVertex = 81 := blockVertex_count
example : Fintype.card InternalLink = 8 := internalLink_count
example : Fintype.card InternalPlaquette = 24 := internalPlaquette_count
example : internalSpanningTree.card = 1 := internalSpanningTree_count
example : Fintype.card CoTreeLink = 7 := coTreeLink_count

example : su2Haar Set.univ = 1 := su2Haar_univ

example (β : ℝ) (U : BlockLinkField) :
    wilsonAction β (treeGaugeFix U) = wilsonAction β U :=
  wilsonAction_treeGaugeFix β U

example (U : BlockLinkField) : treeGaugeFix U treeBlockLink = 1 :=
  treeGaugeFix_treeLink U

example (V : BoundaryField) (C : CoTreeField) :
    treeGaugeCoordinateField V C treeBlockLink = 1 :=
  treeGaugeCoordinateField_treeLink V C

example (V : BoundaryField) (C : CoTreeField) (e : CoTreeLink) :
    treeGaugeCoordinateField V C e.1.1 = C e :=
  treeGaugeCoordinateField_coTree V C e

example (V : BoundaryField) : blockPartition 0 V = 1 :=
  blockPartition_zero V

#print axioms su2_isCompact
#print axioms su2Haar_univ
#print axioms blockVertex_count
#print axioms internalLink_count
#print axioms internalPlaquette_count
#print axioms coTreeLink_count
#print axioms plaquetteHolonomy_gaugeAct
#print axioms wilsonAction_gaugeAct
#print axioms treeGaugeFix_treeLink
#print axioms wilsonAction_treeGaugeFix
#print axioms treeGaugeCoordinateField_boundary
#print axioms treeGaugeCoordinateField_treeLink
#print axioms treeGaugeCoordinateField_coTree
#print axioms blockPartition_zero

end SU2WilsonBlockPilotRegression
end YangMills
end QuantumTheory
end Mettapedia
