import MettapediaFourColor.NearLinearFiveBase

/-!
# One retained base supplies a five-member boundary-insertion family

Every transfer uses the same joint split and actual colouring reconstruction.
Only configuration 225 supplies a rank certificate; the four lower entries
need no independent repair certificate. These are local repair contracts,
not a new unavoidable-set or simultaneous-repair runtime theorem.
-/

namespace FourColor.NearLinearFiveRepair

open KempeBoundarySplit NearLinearFiveData

set_option maxRecDepth 32768

theorem transfer0370_0464
    (base : Repairs (GraphTrace input0464.graph boundary0464) 13) :
    Repairs (GraphTrace input0370.graph boundary0370) 12 := by
  have split : Repairs (GraphTrace
      (Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.subdivide input0370.graph 9 8 16)
      (BoundaryTriangleRepair.ports 9 8 [7, 6, 5, 4, 3, 2, 1, 0, 11, 10])) 13 :=
    BoundaryRepairTransport.repairs insert0370_0464 _ boundary0464 9
      (by decide +kernel) base
  have collapsed := BoundaryTriangleRepair.repair input0370.graph 9 8 16 [7, 6, 5, 4, 3, 2, 1, 0, 11, 10] split
  exact BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0370.graph)) boundary0370
    (9 :: 8 :: [7, 6, 5, 4, 3, 2, 1, 0, 11, 10]) 2 (by decide +kernel) collapsed

theorem transfer0370_0465
    (base : Repairs (GraphTrace input0465.graph boundary0465) 13) :
    Repairs (GraphTrace input0370.graph boundary0370) 12 := by
  have split : Repairs (GraphTrace
      (Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.subdivide input0370.graph 6 5 20)
      (BoundaryTriangleRepair.ports 6 5 [4, 3, 2, 1, 0, 11, 10, 9, 8, 7])) 13 :=
    BoundaryRepairTransport.repairs insert0370_0465 _ boundary0465 2
      (by decide +kernel) base
  have collapsed := BoundaryTriangleRepair.repair input0370.graph 6 5 20 [4, 3, 2, 1, 0, 11, 10, 9, 8, 7] split
  exact BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0370.graph)) boundary0370
    (6 :: 5 :: [4, 3, 2, 1, 0, 11, 10, 9, 8, 7]) 5 (by decide +kernel) collapsed

theorem transfer0465_0604
    (base : Repairs (GraphTrace input0604.graph boundary0604) 14) :
    Repairs (GraphTrace input0465.graph boundary0465) 13 := by
  have split : Repairs (GraphTrace
      (Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.subdivide input0465.graph 4 3 16)
      (BoundaryTriangleRepair.ports 4 3 [2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5])) 14 :=
    BoundaryRepairTransport.repairs insert0465_0604 _ boundary0604 2
      (by decide +kernel) base
  have collapsed := BoundaryTriangleRepair.repair input0465.graph 4 3 16 [2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5] split
  exact BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0465.graph)) boundary0465
    (4 :: 3 :: [2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5]) 8 (by decide +kernel) collapsed

theorem transfer0464_0604
    (base : Repairs (GraphTrace input0604.graph boundary0604) 14) :
    Repairs (GraphTrace input0464.graph boundary0464) 13 := by
  have split : Repairs (GraphTrace
      (Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.subdivide input0464.graph 4 3 16)
      (BoundaryTriangleRepair.ports 4 3 [2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5])) 14 :=
    BoundaryRepairTransport.repairs insert0464_0604 _ boundary0604 12
      (by decide +kernel) base
  have collapsed := BoundaryTriangleRepair.repair input0464.graph 4 3 16 [2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5] split
  exact BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0464.graph)) boundary0464
    (4 :: 3 :: [2, 1, 0, 12, 11, 10, 9, 8, 7, 6, 5]) 8 (by decide +kernel) collapsed

theorem transfer3202_0604
    (base : Repairs (GraphTrace input0604.graph boundary0604) 14) :
    Repairs (GraphTrace input3202.graph boundary3202) 13 := by
  have split : Repairs (GraphTrace
      (Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.subdivide input3202.graph 5 4 16)
      (BoundaryTriangleRepair.ports 5 4 [3, 2, 1, 0, 12, 11, 10, 9, 8, 7, 6])) 14 :=
    BoundaryRepairTransport.repairs insert3202_0604 _ boundary0604 0
      (by decide +kernel) base
  have collapsed := BoundaryTriangleRepair.repair input3202.graph 5 4 16 [3, 2, 1, 0, 12, 11, 10, 9, 8, 7, 6] split
  exact BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input3202.graph)) boundary3202
    (5 :: 4 :: [3, 2, 1, 0, 12, 11, 10, 9, 8, 7, 6]) 7 (by decide +kernel) collapsed

theorem repair0604 : Repairs (GraphTrace input0604.graph boundary0604) 14 :=
  NearLinearFiveBase.repair0604

theorem repair0464 : Repairs (GraphTrace input0464.graph boundary0464) 13 :=
  transfer0464_0604 repair0604

theorem repair0465 : Repairs (GraphTrace input0465.graph boundary0465) 13 :=
  transfer0465_0604 repair0604

theorem repair3202 : Repairs (GraphTrace input3202.graph boundary3202) 13 :=
  transfer3202_0604 repair0604

theorem repair0370 : Repairs (GraphTrace input0370.graph boundary0370) 12 :=
  transfer0370_0464 repair0464

/-- A second valid repair derivation; witness equality is a separate assertion. -/
theorem repair0370_alternative : Repairs (GraphTrace input0370.graph boundary0370) 12 :=
  transfer0370_0465 repair0465

end FourColor.NearLinearFiveRepair
