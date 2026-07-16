import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionBounceCircuit

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Reversing a line-graph adjacency does not change its unique common
primal endpoint. -/
theorem lineGraphCommonVertex_symm {first second : G.edgeSet}
    (hadj : G.lineGraph.Adj first second) :
    lineGraphCommonVertex hadj.symm = lineGraphCommonVertex hadj := by
  symm
  apply lineGraphCommonVertex_unique
  · exact lineGraphCommonVertex_mem_right hadj
  · exact lineGraphCommonVertex_mem_left hadj

end SimpleGraph

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The first primal junction of a reversed positive line-graph walk is the
last primal junction of the original walk. -/
theorem lineGraphJunctionAt_reverse_zero {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) (hpositive : 0 < walk.length) :
    walk.reverse.lineGraphJunctionAt
        ⟨0, by simpa only [SimpleGraph.Walk.length_reverse] using hpositive⟩ =
      walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := walk.lineGraphJunctionAt_mem_right
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩
    have hlast : walk.length - 1 + 1 = walk.length := by omega
    simpa only [SimpleGraph.Walk.getVert_reverse,
      Nat.sub_zero, hlast, SimpleGraph.Walk.getVert_length] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_left
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩
    simpa only [SimpleGraph.Walk.getVert_reverse,
      Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2
        (Nat.ne_of_gt hpositive))] using hmem

/-- The last junction of the reversed walk is the first junction of the
original walk. -/
theorem lineGraphJunctionAt_reverse_last {first last : G.edgeSet}
    (walk : G.lineGraph.Walk first last) (hpositive : 0 < walk.length) :
    walk.reverse.lineGraphJunctionAt
        ⟨walk.reverse.length - 1,
          Nat.sub_lt (by simpa only [SimpleGraph.Walk.length_reverse] using
            hpositive) Nat.zero_lt_one⟩ =
      walk.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := walk.lineGraphJunctionAt_mem_right ⟨0, hpositive⟩
    have hindex : walk.length - (walk.length - 1) = 1 := by omega
    simpa only [SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.getVert_reverse, hindex] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_left ⟨0, hpositive⟩
    have hindex : walk.length - ((walk.length - 1) + 1) = 0 := by omega
    simpa only [SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.getVert_reverse, hindex,
      SimpleGraph.Walk.getVert_zero] using hmem

/-- Open primal coherence composes across an append whenever the two
positive pieces use opposite endpoints of their common line vertex. -/
theorem IsPrimalCoherent.append
    {first middle last : G.edgeSet}
    {left : G.lineGraph.Walk first middle}
    {right : G.lineGraph.Walk middle last}
    (hleft : left.IsPrimalCoherent)
    (hright : right.IsPrimalCoherent)
    (hseam : ∀ (hleftPositive : 0 < left.length)
        (hrightPositive : 0 < right.length),
      left.lineGraphJunctionAt
          ⟨left.length - 1,
            Nat.sub_lt hleftPositive Nat.zero_lt_one⟩ ≠
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩) :
    (left.append right).IsPrimalCoherent := by
  intro position hposition
  by_cases hleftStep : position + 1 < left.length
  · let firstPosition : Fin left.length := ⟨position, by omega⟩
    let secondPosition : Fin left.length :=
      ⟨position + 1, hleftStep⟩
    have hfirst := left.lineGraphJunctionAt_append_left right firstPosition
    have hsecond := left.lineGraphJunctionAt_append_left right secondPosition
    intro hjunction
    exact hleft position hleftStep
      (hfirst.symm.trans (hjunction.trans hsecond))
  · by_cases hpositionLeft : position < left.length
    · have hleftPositive : 0 < left.length := by omega
      have hrightPositive : 0 < right.length := by
        simp only [SimpleGraph.Walk.length_append] at hposition
        omega
      have hpositionEq : position = left.length - 1 := by omega
      subst position
      let leftLast : Fin left.length :=
        ⟨left.length - 1,
          Nat.sub_lt hleftPositive Nat.zero_lt_one⟩
      let rightFirst : Fin right.length := ⟨0, hrightPositive⟩
      have hfirst := left.lineGraphJunctionAt_append_left right leftLast
      have hsecond := left.lineGraphJunctionAt_append_right right rightFirst
      intro hjunction
      have hsecondFin :
          (⟨(left.length - 1) + 1, by omega⟩ :
              Fin (left.append right).length) =
            ⟨left.length + rightFirst.val, by simp⟩ := by
        apply Fin.ext
        dsimp only [rightFirst]
        omega
      rw [hsecondFin] at hjunction
      exact hseam hleftPositive hrightPositive
        (hfirst.symm.trans (hjunction.trans hsecond))
    · let rightPosition : Fin right.length :=
        ⟨position - left.length, by
          simp only [SimpleGraph.Walk.length_append] at hposition
          omega⟩
      let rightNext : Fin right.length :=
        ⟨position - left.length + 1, by
          simp only [SimpleGraph.Walk.length_append] at hposition
          omega⟩
      have hrightStep : rightPosition.val + 1 < right.length := by
        dsimp only [rightPosition]
        simp only [SimpleGraph.Walk.length_append] at hposition
        omega
      have hfirst := left.lineGraphJunctionAt_append_right right rightPosition
      have hsecond := left.lineGraphJunctionAt_append_right right rightNext
      intro hjunction
      have hfirstFin :
          (⟨position, by omega⟩ : Fin (left.append right).length) =
            ⟨left.length + rightPosition.val, by simp⟩ := by
        apply Fin.ext
        dsimp only [rightPosition]
        omega
      have hsecondFin :
          (⟨position + 1, hposition⟩ : Fin (left.append right).length) =
            ⟨left.length + rightNext.val, by simp⟩ := by
        apply Fin.ext
        dsimp only [rightNext]
        omega
      rw [hfirstFin, hsecondFin] at hjunction
      exact hright rightPosition.val hrightStep
        (hfirst.symm.trans (hjunction.trans hsecond))

/-- The last junction of an append with a positive right part is the last
junction of that right part. -/
theorem lineGraphJunctionAt_append_last_of_right_pos
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (hrightPositive : 0 < right.length) :
    (left.append right).lineGraphJunctionAt
        ⟨(left.append right).length - 1,
          Nat.sub_lt (by simp; omega) Nat.zero_lt_one⟩ =
      right.lineGraphJunctionAt
        ⟨right.length - 1,
          Nat.sub_lt hrightPositive Nat.zero_lt_one⟩ := by
  let rightLast : Fin right.length :=
    ⟨right.length - 1,
      Nat.sub_lt hrightPositive Nat.zero_lt_one⟩
  have hmapped := left.lineGraphJunctionAt_append_right right rightLast
  have hposition :
      (⟨(left.append right).length - 1,
          Nat.sub_lt (by simp; omega) Nat.zero_lt_one⟩ :
        Fin (left.append right).length) =
      ⟨left.length + rightLast.val, by simp⟩ := by
    apply Fin.ext
    dsimp only [rightLast]
    simp only [SimpleGraph.Walk.length_append]
    omega
  rw [hposition]
  exact hmapped

/-- With a positive left part, the first junction of an append is inherited
from the left part. -/
theorem lineGraphJunctionAt_append_zero_of_left_pos
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (hleftPositive : 0 < left.length) :
    (left.append right).lineGraphJunctionAt
        ⟨0, by simp; omega⟩ =
      left.lineGraphJunctionAt ⟨0, hleftPositive⟩ := by
  exact left.lineGraphJunctionAt_append_left right ⟨0, hleftPositive⟩

/-- With a zero-length left part and positive right part, the first append
junction is inherited from the right part. -/
theorem lineGraphJunctionAt_append_zero_of_left_length_zero
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (hleftZero : left.length = 0)
    (hrightPositive : 0 < right.length) :
    (left.append right).lineGraphJunctionAt
        ⟨0, by simp; omega⟩ =
      right.lineGraphJunctionAt ⟨0, hrightPositive⟩ := by
  have hmapped := left.lineGraphJunctionAt_append_right right
    ⟨0, hrightPositive⟩
  have hposition :
      (⟨0, by simp; omega⟩ : Fin (left.append right).length) =
        ⟨left.length + 0, by
          simp only [SimpleGraph.Walk.length_append]
          omega⟩ := by
    apply Fin.ext
    simp [hleftZero]
  rw [hposition]
  exact hmapped

/-- Prepending one step to a positive walk leaves the final junction of the
tail as the final junction of the result. -/
theorem lineGraphJunctionAt_cons_last_of_pos
    {first second last : G.edgeSet}
    (hadj : G.lineGraph.Adj first second)
    (walk : G.lineGraph.Walk second last)
    (hpositive : 0 < walk.length) :
    (SimpleGraph.Walk.cons hadj walk).lineGraphJunctionAt
        ⟨(SimpleGraph.Walk.cons hadj walk).length - 1,
          Nat.sub_lt (by simp) Nat.zero_lt_one⟩ =
      walk.lineGraphJunctionAt
        ⟨walk.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ := by
  let walkLast : Fin walk.length :=
    ⟨walk.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hmapped :=
    SimpleGraph.Walk.lineGraphJunctionAt_cons_succ hadj walk walkLast
  have hposition :
      (⟨(SimpleGraph.Walk.cons hadj walk).length - 1,
          Nat.sub_lt (by simp) Nat.zero_lt_one⟩ :
        Fin (SimpleGraph.Walk.cons hadj walk).length) =
      ⟨walkLast.val + 1, by simp⟩ := by
    apply Fin.ext
    dsimp only [walkLast]
    simp only [SimpleGraph.Walk.length_cons]
    omega
  rw [hposition]
  exact hmapped

/-- A one-step line-graph walk has the same common primal junction at its
unique junction coordinate. -/
theorem lineGraphJunctionAt_cons_nil
    {first second : G.edgeSet}
    (hadj : G.lineGraph.Adj first second)
    (position : Fin (SimpleGraph.Walk.cons hadj
      (SimpleGraph.Walk.nil : G.lineGraph.Walk second second)).length) :
    (SimpleGraph.Walk.cons hadj
      (SimpleGraph.Walk.nil : G.lineGraph.Walk second second)).lineGraphJunctionAt
        position =
      SimpleGraph.lineGraphCommonVertex hadj := by
  have hposition : position = ⟨0, by simp⟩ := by
    apply Fin.ext
    have hbound := position.isLt
    simp only [SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at hbound
    show position.val = 0
    omega
  subst position
  exact SimpleGraph.Walk.lineGraphJunctionAt_cons_zero hadj
    SimpleGraph.Walk.nil

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance fusionDisjointGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

theorem EvenKempeFusionLens.bRightEdge_not_mem_cAmbientPath_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.bRoute.rightEdge.1 ∉ lens.cRoute.ambientPath.support := by
  intro hmem
  exact (lens.endpoints_not_shared hab hac).2.1
    ((lens.cRoute.mem_ambientPath_support_iff _).1 hmem)

theorem EvenKempeFusionLens.cRightEdge_not_mem_bAmbientPath_support
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) :
    lens.cRoute.rightEdge.1 ∉ lens.bRoute.ambientPath.support := by
  intro hmem
  exact (lens.endpoints_not_shared hab hac).2.2.2
    ((lens.bRoute.mem_ambientPath_support_iff _).1 hmem)

/-- At the right port, the two terminal route edges exhaust the two incident
edges, just as at the left port. -/
theorem EvenKempeFusionLens.rightTerminalEdges_eq_incidentEdgeFinset
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) :
    incidentEdgeFinset G (data.defectVertex right) =
      {lens.bRoute.rightEdge.1, lens.cRoute.rightEdge.1} := by
  have hsubset :
      {lens.bRoute.rightEdge.1, lens.cRoute.rightEdge.1} ⊆
        incidentEdgeFinset G (data.defectVertex right) := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact lens.bRoute.rightIncident
    · exact lens.cRoute.rightIncident
  have hpairEq := Finset.eq_of_subset_of_card_le hsubset (by
    rw [hdata.2.1 right, Finset.card_pair lens.rightConnector.ne])
  exact hpairEq.symm

theorem EvenKempeFusionLens.rightConnectorVertex_eq_defectVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    SimpleGraph.lineGraphCommonVertex lens.rightConnector =
      data.defectVertex right := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · simpa [incidentEdgeFinset] using lens.bRoute.rightIncident
  · simpa [incidentEdgeFinset] using lens.cRoute.rightIncident

/-- The left boundary connector uses the defect endpoint, whereas the first
step of a positive-length `b` route leaves through the other endpoint. -/
theorem EvenKempeFusionLens.leftConnectorVertex_ne_bRouteFirstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hpositive : 0 < lens.bRoute.ambientPath.length) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector ≠
      lens.bRoute.ambientPath.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  intro hjunction
  let bPath := lens.bRoute.ambientPath
  have hnextMem := bPath.lineGraphJunctionAt_mem_right ⟨0, hpositive⟩
  have hdefectMem : data.defectVertex left ∈
      ((bPath.getVert 1).1 : Sym2 V) := by
    rw [← lens.leftConnectorVertex_eq_defectVertex, hjunction]
    exact hnextMem
  have hnextIncident : bPath.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hnextIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnextIncident
  rcases hnextIncident with hbLeft | hcLeft
  · have hadj := bPath.adj_getVert_succ (i := 0) hpositive
    exact hadj.ne (by
      simpa only [bPath, SimpleGraph.Walk.getVert_zero] using hbLeft.symm)
  · apply lens.cLeftEdge_not_mem_bAmbientPath_support hab hac
    exact hcLeft ▸ bPath.getVert_mem_support 1

/-- The corresponding first `c`-route turn is also non-bouncing. -/
theorem EvenKempeFusionLens.leftConnectorVertex_ne_cRouteFirstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hpositive : 0 < lens.cRoute.ambientPath.length) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector ≠
      lens.cRoute.ambientPath.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  intro hjunction
  let cPath := lens.cRoute.ambientPath
  have hnextMem := cPath.lineGraphJunctionAt_mem_right ⟨0, hpositive⟩
  have hdefectMem : data.defectVertex left ∈
      ((cPath.getVert 1).1 : Sym2 V) := by
    rw [← lens.leftConnectorVertex_eq_defectVertex, hjunction]
    exact hnextMem
  have hnextIncident : cPath.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.leftTerminalEdges_eq_incidentEdgeFinset hdata] at hnextIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnextIncident
  rcases hnextIncident with hbLeft | hcLeft
  · apply lens.bLeftEdge_not_mem_cAmbientPath_support hab hac
    exact hbLeft ▸ cPath.getVert_mem_support 1
  · have hadj := cPath.adj_getVert_succ (i := 0) hpositive
    exact hadj.ne (by
      simpa only [cPath, SimpleGraph.Walk.getVert_zero] using hcLeft.symm)

/-- At the right port, the last internal `b`-route junction differs from the
boundary connector junction. -/
theorem EvenKempeFusionLens.bRouteLastJunction_ne_rightConnectorVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hpositive : 0 < lens.bRoute.ambientPath.length) :
    lens.bRoute.ambientPath.lineGraphJunctionAt
        ⟨lens.bRoute.ambientPath.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      SimpleGraph.lineGraphCommonVertex lens.rightConnector := by
  intro hjunction
  let bPath := lens.bRoute.ambientPath
  have hbPositive : 0 < bPath.length := by
    simpa only [bPath] using hpositive
  let lastPosition : Fin bPath.length :=
    ⟨bPath.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hpreviousMem := bPath.lineGraphJunctionAt_mem_left lastPosition
  have hdefectMem : data.defectVertex right ∈
      ((bPath.getVert (bPath.length - 1)).1 : Sym2 V) := by
    rw [← lens.rightConnectorVertex_eq_defectVertex, ← hjunction]
    exact hpreviousMem
  have hpreviousIncident : bPath.getVert (bPath.length - 1) ∈
      incidentEdgeFinset G (data.defectVertex right) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.rightTerminalEdges_eq_incidentEdgeFinset hdata] at hpreviousIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpreviousIncident
  rcases hpreviousIncident with hbRight | hcRight
  · have hadj := bPath.adj_getVert_succ
        (i := bPath.length - 1) (by omega : bPath.length - 1 < bPath.length)
    exact hadj.ne (by
      simpa only [bPath, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
        (Nat.ne_of_gt hpositive)), SimpleGraph.Walk.getVert_length] using
          hbRight)
  · apply lens.cRightEdge_not_mem_bAmbientPath_support hab hac
    exact hcRight ▸ bPath.getVert_mem_support (bPath.length - 1)

/-- The last internal `c`-route junction is likewise non-bouncing. -/
theorem EvenKempeFusionLens.cRouteLastJunction_ne_rightConnectorVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hpositive : 0 < lens.cRoute.ambientPath.length) :
    lens.cRoute.ambientPath.lineGraphJunctionAt
        ⟨lens.cRoute.ambientPath.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      SimpleGraph.lineGraphCommonVertex lens.rightConnector := by
  intro hjunction
  let cPath := lens.cRoute.ambientPath
  have hcPositive : 0 < cPath.length := by
    simpa only [cPath] using hpositive
  let lastPosition : Fin cPath.length :=
    ⟨cPath.length - 1, Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hpreviousMem := cPath.lineGraphJunctionAt_mem_left lastPosition
  have hdefectMem : data.defectVertex right ∈
      ((cPath.getVert (cPath.length - 1)).1 : Sym2 V) := by
    rw [← lens.rightConnectorVertex_eq_defectVertex, ← hjunction]
    exact hpreviousMem
  have hpreviousIncident : cPath.getVert (cPath.length - 1) ∈
      incidentEdgeFinset G (data.defectVertex right) := by
    simpa [incidentEdgeFinset] using hdefectMem
  rw [lens.rightTerminalEdges_eq_incidentEdgeFinset hdata] at hpreviousIncident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpreviousIncident
  rcases hpreviousIncident with hbRight | hcRight
  · apply lens.bRightEdge_not_mem_cAmbientPath_support hab hac
    exact hbRight ▸ cPath.getVert_mem_support (cPath.length - 1)
  · have hadj := cPath.adj_getVert_succ
        (i := cPath.length - 1) (by omega : cPath.length - 1 < cPath.length)
    exact hadj.ne (by
      simpa only [cPath, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
        (Nat.ne_of_gt hpositive)), SimpleGraph.Walk.getVert_length] using
          hcRight)

/-- Every full `(a,b)` route is internally primal-coherent. -/
theorem EvenKempeFusionLens.bAmbientPath_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.bRoute.ambientPath.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := lens.bRoute.ambientPath)
    (hpath := lens.bRoute.ambientPath_isPath)
    (hcolors := by
      intro edge hedge
      exact (lens.bRoute.mem_ambientPath_support_iff edge).1 hedge |>.1)
    (position := position) hposition

/-- The reversed `(a,c)` route is internally primal-coherent. -/
theorem EvenKempeFusionLens.cAmbientPath_reverse_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.cRoute.ambientPath.reverse.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := c)
    (walk := lens.cRoute.ambientPath.reverse)
    (hpath := lens.cRoute.ambientPath.isPath_reverse_iff.mpr
      lens.cRoute.ambientPath_isPath)
    (hcolors := by
      intro edge hedge
      have hambient : edge ∈ lens.cRoute.ambientPath.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using
          hedge
      exact (lens.cRoute.mem_ambientPath_support_iff edge).1 hambient |>.1)
    (position := position) hposition

/-- Cross the right boundary connector and return along the reversed
`(a,c)` route. -/
def EvenKempeFusionLens.rightConnectedCReturn
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    G.lineGraph.Walk lens.bRoute.rightEdge.1 lens.cRoute.leftEdge.1 :=
  SimpleGraph.Walk.cons lens.rightConnector
    lens.cRoute.ambientPath.reverse

@[simp] theorem EvenKempeFusionLens.rightConnectedCReturn_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.rightConnectedCReturn.length =
      lens.cRoute.ambientPath.length + 1 := by
  simp [EvenKempeFusionLens.rightConnectedCReturn]

theorem EvenKempeFusionLens.rightConnectedCReturn_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c) :
    lens.rightConnectedCReturn.IsPrimalCoherent := by
  rw [EvenKempeFusionLens.rightConnectedCReturn]
  apply SimpleGraph.Walk.IsPrimalCoherent.cons_of_firstJunction_ne
    lens.cAmbientPath_reverse_isPrimalCoherent lens.rightConnector
  intro hreversePositive
  have hcPositive : 0 < lens.cRoute.ambientPath.length := by
    simpa only [SimpleGraph.Walk.length_reverse] using hreversePositive
  have hreverseFirst :=
    lens.cRoute.ambientPath.lineGraphJunctionAt_reverse_zero hcPositive
  intro heq
  apply lens.cRouteLastJunction_ne_rightConnectorVertex
    hdata hab hac hcPositive
  exact hreverseFirst.symm.trans heq.symm

/-- The whole lens except for its final left connector. -/
def EvenKempeFusionLens.openLensBody
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    G.lineGraph.Walk lens.bRoute.leftEdge.1 lens.cRoute.leftEdge.1 :=
  lens.bRoute.ambientPath.append lens.rightConnectedCReturn

@[simp] theorem EvenKempeFusionLens.openLensBody_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.openLensBody.length = lens.bRoute.ambientPath.length +
      lens.cRoute.ambientPath.length + 1 := by
  simp [EvenKempeFusionLens.openLensBody]
  omega

/-- The whole lens except for its final left connector is an open coherent
line-graph walk. -/
theorem EvenKempeFusionLens.openLensBody_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c) :
    lens.openLensBody.IsPrimalCoherent := by
  rw [EvenKempeFusionLens.openLensBody]
  apply lens.bAmbientPath_isPrimalCoherent.append
    (lens.rightConnectedCReturn_isPrimalCoherent hdata hab hac)
  intro hbPositive _hrightPositive
  have hbLast := lens.bRouteLastJunction_ne_rightConnectorVertex
    hdata hab hac hbPositive
  have hrightFirst := SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
    lens.rightConnector lens.cRoute.ambientPath.reverse
  simpa only [EvenKempeFusionLens.rightConnectedCReturn,
    hrightFirst] using hbLast

/-- The final one-step connector returning from the `c` route to the `b`
route at the left port. -/
def EvenKempeFusionLens.leftClosingStep
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    G.lineGraph.Walk lens.cRoute.leftEdge.1 lens.bRoute.leftEdge.1 :=
  SimpleGraph.Walk.cons lens.leftConnector.symm SimpleGraph.Walk.nil

@[simp] theorem EvenKempeFusionLens.leftClosingStep_length
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.leftClosingStep.length = 1 := by
  simp [EvenKempeFusionLens.leftClosingStep]

/-- The original closed lens is the open body followed by its left closing
step. -/
theorem EvenKempeFusionLens.closedWalk_eq_openLensBody_append_leftClosingStep
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.closedWalk = lens.openLensBody.append lens.leftClosingStep := by
  rw [EvenKempeFusionLens.closedWalk,
    EvenKempeFusionLens.openLensBody,
    EvenKempeFusionLens.rightConnectedCReturn,
    EvenKempeFusionLens.leftClosingStep,
    ← SimpleGraph.Walk.cons_append,
    SimpleGraph.Walk.append_assoc]

/-- Distinct boundary ports give distinct primal connector junctions. -/
theorem EvenKempeFusionLens.leftConnectorVertex_ne_rightConnectorVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hleftRight : left ≠ right) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector ≠
      SimpleGraph.lineGraphCommonVertex lens.rightConnector := by
  rw [lens.leftConnectorVertex_eq_defectVertex,
    lens.rightConnectorVertex_eq_defectVertex]
  intro hvertices
  exact hleftRight (hdata.1 hvertices)

/-- Every junction coordinate of the one-step closing walk is the left
boundary connector vertex. -/
theorem EvenKempeFusionLens.leftClosingStep_junction_eq_connectorVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (position : Fin lens.leftClosingStep.length) :
    lens.leftClosingStep.lineGraphJunctionAt position =
      SimpleGraph.lineGraphCommonVertex lens.leftConnector := by
  change (SimpleGraph.Walk.cons lens.leftConnector.symm
      (SimpleGraph.Walk.nil : G.lineGraph.Walk
        lens.bRoute.leftEdge.1 lens.bRoute.leftEdge.1)).lineGraphJunctionAt
      position = SimpleGraph.lineGraphCommonVertex lens.leftConnector
  rw [SimpleGraph.Walk.lineGraphJunctionAt_cons_nil]
  exact SimpleGraph.lineGraphCommonVertex_symm lens.leftConnector

/-- The one-step closing walk is internally primal-coherent. -/
theorem EvenKempeFusionLens.leftClosingStep_isPrimalCoherent
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right) :
    lens.leftClosingStep.IsPrimalCoherent := by
  intro position hposition
  rw [lens.leftClosingStep_length] at hposition
  omega

/-- The last junction of the open lens body is not the left connector
vertex.  When the `c` route has length zero, this is exactly the distinction
between the right and left boundary ports. -/
theorem EvenKempeFusionLens.openLensBody_lastJunction_ne_leftConnectorVertex
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hleftRight : left ≠ right) :
    lens.openLensBody.lineGraphJunctionAt
        ⟨lens.openLensBody.length - 1,
          Nat.sub_lt (by rw [lens.openLensBody_length]; omega)
            Nat.zero_lt_one⟩ ≠
      SimpleGraph.lineGraphCommonVertex lens.leftConnector := by
  have hrightPositive : 0 < lens.rightConnectedCReturn.length := by
    rw [lens.rightConnectedCReturn_length]
    omega
  have hbodyLast :
      lens.openLensBody.lineGraphJunctionAt
          ⟨lens.openLensBody.length - 1,
            Nat.sub_lt (by rw [lens.openLensBody_length]; omega)
              Nat.zero_lt_one⟩ =
        lens.rightConnectedCReturn.lineGraphJunctionAt
          ⟨lens.rightConnectedCReturn.length - 1,
            Nat.sub_lt hrightPositive Nat.zero_lt_one⟩ := by
    simpa only [EvenKempeFusionLens.openLensBody] using
      SimpleGraph.Walk.lineGraphJunctionAt_append_last_of_right_pos
        lens.bRoute.ambientPath lens.rightConnectedCReturn hrightPositive
  by_cases hcPositive : 0 < lens.cRoute.ambientPath.length
  · have hcReversePositive :
        0 < lens.cRoute.ambientPath.reverse.length := by
      simpa only [SimpleGraph.Walk.length_reverse] using hcPositive
    have hreturnLast :
        lens.rightConnectedCReturn.lineGraphJunctionAt
            ⟨lens.rightConnectedCReturn.length - 1,
              Nat.sub_lt hrightPositive Nat.zero_lt_one⟩ =
          lens.cRoute.ambientPath.reverse.lineGraphJunctionAt
            ⟨lens.cRoute.ambientPath.reverse.length - 1,
              Nat.sub_lt hcReversePositive Nat.zero_lt_one⟩ := by
      simpa only [EvenKempeFusionLens.rightConnectedCReturn] using
        SimpleGraph.Walk.lineGraphJunctionAt_cons_last_of_pos
          lens.rightConnector lens.cRoute.ambientPath.reverse
            hcReversePositive
    have hreverseLast :=
      lens.cRoute.ambientPath.lineGraphJunctionAt_reverse_last hcPositive
    intro hleft
    apply lens.leftConnectorVertex_ne_cRouteFirstJunction
      hdata hab hac hcPositive
    exact hleft.symm.trans
      (hbodyLast.trans (hreturnLast.trans hreverseLast))
  · have hcZero : lens.cRoute.ambientPath.length = 0 := by omega
    have hrightLength : lens.rightConnectedCReturn.length = 1 := by
      rw [lens.rightConnectedCReturn_length, hcZero]
    have hpositions :
        (⟨lens.rightConnectedCReturn.length - 1,
            Nat.sub_lt hrightPositive Nat.zero_lt_one⟩ :
          Fin lens.rightConnectedCReturn.length) =
        ⟨0, hrightPositive⟩ := by
      apply Fin.ext
      change lens.rightConnectedCReturn.length - 1 = 0
      omega
    have hreturnFirst :
        lens.rightConnectedCReturn.lineGraphJunctionAt
            ⟨0, hrightPositive⟩ =
          SimpleGraph.lineGraphCommonVertex lens.rightConnector := by
      simpa only [EvenKempeFusionLens.rightConnectedCReturn] using
        SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
          lens.rightConnector lens.cRoute.ambientPath.reverse
    intro hleft
    apply (lens.leftConnectorVertex_ne_rightConnectorVertex
      hdata hleftRight).symm
    exact (hbodyLast.trans (by rw [hpositions]; exact hreturnFirst)).symm.trans
      hleft

/-- The left connector vertex is not the first junction of the open body.
The zero-length `b` route again reduces this to distinct boundary ports. -/
theorem EvenKempeFusionLens.leftConnectorVertex_ne_openLensBody_firstJunction
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hleftRight : left ≠ right) :
    SimpleGraph.lineGraphCommonVertex lens.leftConnector ≠
      lens.openLensBody.lineGraphJunctionAt
        ⟨0, by rw [lens.openLensBody_length]; omega⟩ := by
  have hrightPositive : 0 < lens.rightConnectedCReturn.length := by
    rw [lens.rightConnectedCReturn_length]
    omega
  by_cases hbPositive : 0 < lens.bRoute.ambientPath.length
  · have hbodyFirst :
        lens.openLensBody.lineGraphJunctionAt
            ⟨0, by rw [lens.openLensBody_length]; omega⟩ =
          lens.bRoute.ambientPath.lineGraphJunctionAt ⟨0, hbPositive⟩ := by
      simpa only [EvenKempeFusionLens.openLensBody] using
        SimpleGraph.Walk.lineGraphJunctionAt_append_zero_of_left_pos
          lens.bRoute.ambientPath lens.rightConnectedCReturn hbPositive
    intro hfirst
    apply lens.leftConnectorVertex_ne_bRouteFirstJunction
      hdata hab hac hbPositive
    exact hfirst.trans hbodyFirst
  · have hbZero : lens.bRoute.ambientPath.length = 0 := by omega
    have hbodyFirst :
        lens.openLensBody.lineGraphJunctionAt
            ⟨0, by rw [lens.openLensBody_length]; omega⟩ =
          lens.rightConnectedCReturn.lineGraphJunctionAt
            ⟨0, hrightPositive⟩ := by
      simpa only [EvenKempeFusionLens.openLensBody] using
        SimpleGraph.Walk.lineGraphJunctionAt_append_zero_of_left_length_zero
          lens.bRoute.ambientPath lens.rightConnectedCReturn
            hbZero hrightPositive
    have hreturnFirst :
        lens.rightConnectedCReturn.lineGraphJunctionAt
            ⟨0, hrightPositive⟩ =
          SimpleGraph.lineGraphCommonVertex lens.rightConnector := by
      simpa only [EvenKempeFusionLens.rightConnectedCReturn] using
        SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
          lens.rightConnector lens.cRoute.ambientPath.reverse
    intro hfirst
    apply lens.leftConnectorVertex_ne_rightConnectorVertex hdata hleftRight
    exact hfirst.trans (hbodyFirst.trans hreturnFirst)

/-- The complete two-route lens is a primal-coherent closed line-graph walk.
This includes the fusion-free base case: the only closure checks occur at
the two boundary ports, while each bicolored route is coherent internally. -/
theorem EvenKempeFusionLens.closedWalk_isPrimalCoherentClosed
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hleftRight : left ≠ right) :
    lens.closedWalk.IsPrimalCoherentClosed := by
  rw [lens.closedWalk_eq_openLensBody_append_leftClosingStep]
  have hbodyPositive : 0 < lens.openLensBody.length := by
    rw [lens.openLensBody_length]
    omega
  have hclosingPositive : 0 < lens.leftClosingStep.length := by
    rw [lens.leftClosingStep_length]
    omega
  apply SimpleGraph.Walk.IsPrimalCoherent.append_isPrimalCoherentClosed
    (lens.openLensBody_isPrimalCoherent hdata hab hac)
    lens.leftClosingStep_isPrimalCoherent
    hbodyPositive hclosingPositive
  · intro hsame
    apply lens.openLensBody_lastJunction_ne_leftConnectorVertex
      hdata hab hac hleftRight
    exact hsame.trans
      (lens.leftClosingStep_junction_eq_connectorVertex
        ⟨0, hclosingPositive⟩)
  · intro hsame
    apply lens.leftConnectorVertex_ne_openLensBody_firstJunction
      hdata hab hac hleftRight
    exact (lens.leftClosingStep_junction_eq_connectorVertex
      ⟨lens.leftClosingStep.length - 1,
        Nat.sub_lt hclosingPositive Nat.zero_lt_one⟩).symm.trans hsame

/-- Every well-formed lens between distinct boundary ports contains a
primal cycle no longer than the complete lens, independently of how often
the two bicolored routes meet. -/
theorem EvenKempeFusionLens.exists_primalCycle_length_le_closedWalk
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed) (hab : a ≠ b) (hac : a ≠ c)
    (hleftRight : left ≠ right) :
    ∃ (start : V) (cycle : G.Walk start start),
      cycle.IsCycle ∧ cycle.length ≤ lens.closedWalk.length := by
  have hpositive : 0 < lens.closedWalk.length := by
    have htwo := lens.closedWalk_two_le_length
    omega
  exact lens.closedWalk.exists_primal_isCycle_length_le_of_primalCoherentClosed
    hpositive
    (lens.closedWalk_isPrimalCoherentClosed hdata hab hac hleftRight)

/-- Fusion-chain descent has exactly two structural outcomes.  A nonempty
fusion list gives the strict bounce/return contraction; an empty list is
the coherent base lens and already contains a primal cycle. -/
theorem EvenKempeFusionLens.fusionChain_base_or_strictly_shorterCircuit
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hdata : data.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hleftRight : left ≠ right) :
    (lens.fusionSiteCount = 0 ∧
      ∃ (start : V) (cycle : G.Walk start start),
        cycle.IsCycle ∧ cycle.length ≤ lens.closedWalk.length) ∨
    (0 < lens.fusionSiteCount ∧
      ∃ (start : V) (circuit : G.Walk start start),
        circuit.IsCircuit ∧ circuit.length < lens.closedWalk.length) := by
  by_cases hzero : lens.fusionSiteCount = 0
  · exact Or.inl ⟨hzero,
      lens.exists_primalCycle_length_le_closedWalk
        hdata hab hac hleftRight⟩
  · have hpositive : 0 < lens.fusionSiteCount := Nat.pos_of_ne_zero hzero
    exact Or.inr ⟨hpositive,
      lens.exists_shorter_primalCircuit_of_fusionSiteCount_pos
        hdata hab hac hbc hpositive⟩

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
