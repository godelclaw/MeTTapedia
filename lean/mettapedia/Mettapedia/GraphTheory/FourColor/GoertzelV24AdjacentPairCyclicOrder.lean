import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairPlanarReduction
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SeamFaceArc
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cyclicOrderGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance cyclicOrderRetainedVertexSetFintype (first second : V) :
    Fintype (retainedVertexSet first second) :=
  retainedVertexSetFintype first second

local instance cyclicOrderRetainedVertexSetDecidableEq (first second : V) :
    DecidableEq (retainedVertexSet first second) :=
  retainedVertexSetDecidableEq first second

def rotationCentralDart (data : AdjacentPairData G) : G.Dart :=
  ⟨(data.firstVertex, data.secondVertex), data.centralAdjacent⟩

def rotationPortDart (graphData : Data G) (data : AdjacentPairData G) :
    Fin 4 → G.Dart
  | 0 => graphData.toRotationSystem.rho data.rotationCentralDart
  | 1 => graphData.toRotationSystem.rho
      (graphData.toRotationSystem.rho data.rotationCentralDart)
  | 2 => graphData.toRotationSystem.rho
      (graphData.toRotationSystem.alpha data.rotationCentralDart)
  | 3 => graphData.toRotationSystem.rho
      (graphData.toRotationSystem.rho
        (graphData.toRotationSystem.alpha data.rotationCentralDart))

def rotationPortVertex (graphData : Data G) (data : AdjacentPairData G)
    (port : Fin 4) : V :=
  (data.rotationPortDart graphData port).snd

theorem rho_triple_pairwise_ne
    (RS : RotationSystem V G.edgeSet)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (dart : RS.D) :
    dart ≠ RS.rho dart ∧
      dart ≠ RS.rho (RS.rho dart) ∧
      RS.rho dart ≠ RS.rho (RS.rho dart) := by
  have hdart : dart ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt]
  have hnontrivialFinset : (RS.dartsAt (RS.vertOf dart)).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hcubic (RS.vertOf dart)]
    omega
  have hnontrivial : (RS.dartsAt (RS.vertOf dart) : Set RS.D).Nontrivial := by
    simpa only [Finset.coe_sort_coe] using hnontrivialFinset
  have hstep : RS.rho dart ≠ dart :=
    (rho_isCycleOn_dartsAt RS hrotation (RS.vertOf dart)).apply_ne
      hnontrivial hdart
  have hnext : RS.rho (RS.rho dart) ≠ RS.rho dart := by
    exact fun heq => hstep (RS.rho.injective heq)
  have hfirstThird : dart ≠ RS.rho (RS.rho dart) := by
    intro heq
    have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation dart
    have hrho := congrArg RS.rho heq
    rw [hcube] at hrho
    exact hstep hrho
  exact ⟨hstep.symm, hfirstThird, hnext.symm⟩

theorem rotationPortDart_fst
    (graphData : Data G) (data : AdjacentPairData G) (port : Fin 4) :
    (data.rotationPortDart graphData port).fst =
      if port = 0 ∨ port = 1 then data.firstVertex else data.secondVertex := by
  let RS := graphData.toRotationSystem
  let central := data.rotationCentralDart
  have hcentral : RS.vertOf central = data.firstVertex := rfl
  have hopposite : RS.vertOf (RS.alpha central) = data.secondVertex := rfl
  fin_cases port
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho central).trans hcentral
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho (RS.rho central)).trans
        ((RS.vert_rho central).trans hcentral)
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho (RS.alpha central)).trans hopposite
  · simpa [rotationPortDart, RS, central] using
      (RS.vert_rho (RS.rho (RS.alpha central))).trans
        ((RS.vert_rho (RS.alpha central)).trans hopposite)

theorem rotationPortVertex_mem_originalPair
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    if port = 0 ∨ port = 1 then
      data.rotationPortVertex graphData port ∈
        ({data.portVertex 0, data.portVertex 1} : Set V)
    else
      data.rotationPortVertex graphData port ∈
        ({data.portVertex 2, data.portVertex 3} : Set V) := by
  let RS := graphData.toRotationSystem
  let central := data.rotationCentralDart
  have hfirst := rho_triple_pairwise_ne RS hcubic hrotation central
  have hsecond := rho_triple_pairwise_ne RS hcubic hrotation (RS.alpha central)
  fin_cases port
  · change data.rotationPortVertex graphData 0 = data.portVertex 0 ∨
      data.rotationPortVertex graphData 0 = data.portVertex 1
    have hadj : G.Adj data.firstVertex
        (data.rotationPortVertex graphData 0) := by
      simpa [rotationPortVertex, rotationPortDart_fst] using
        (data.rotationPortDart graphData 0).adj
    have hmem : data.rotationPortVertex graphData 0 = data.secondVertex ∨
        data.rotationPortVertex graphData 0 = data.portVertex 0 ∨
        data.rotationPortVertex graphData 0 = data.portVertex 1 := by
      have : data.rotationPortVertex graphData 0 ∈
          G.neighborSet data.firstVertex := hadj
      rw [data.firstNeighbors] at this
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hmem with hcentralEndpoint | hport
    · exfalso
      apply hfirst.1
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · have hfst : (data.rotationPortDart graphData 0).fst =
            data.firstVertex := by
          simpa using data.rotationPortDart_fst graphData (0 : Fin 4)
        exact hfst.symm
      · exact hcentralEndpoint.symm
    · exact hport
  · change data.rotationPortVertex graphData 1 = data.portVertex 0 ∨
      data.rotationPortVertex graphData 1 = data.portVertex 1
    have hadj : G.Adj data.firstVertex
        (data.rotationPortVertex graphData 1) := by
      simpa [rotationPortVertex, rotationPortDart_fst] using
        (data.rotationPortDart graphData 1).adj
    have hmem : data.rotationPortVertex graphData 1 = data.secondVertex ∨
        data.rotationPortVertex graphData 1 = data.portVertex 0 ∨
        data.rotationPortVertex graphData 1 = data.portVertex 1 := by
      have : data.rotationPortVertex graphData 1 ∈
          G.neighborSet data.firstVertex := hadj
      rw [data.firstNeighbors] at this
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hmem with hcentralEndpoint | hport
    · exfalso
      apply hfirst.2.1
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · have hfst : (data.rotationPortDart graphData 1).fst =
            data.firstVertex := by
          simpa using data.rotationPortDart_fst graphData (1 : Fin 4)
        exact hfst.symm
      · exact hcentralEndpoint.symm
    · exact hport
  · change data.rotationPortVertex graphData 2 = data.portVertex 2 ∨
      data.rotationPortVertex graphData 2 = data.portVertex 3
    have hadj : G.Adj data.secondVertex
        (data.rotationPortVertex graphData 2) := by
      simpa [rotationPortVertex, rotationPortDart_fst] using
        (data.rotationPortDart graphData 2).adj
    have hmem : data.rotationPortVertex graphData 2 = data.firstVertex ∨
        data.rotationPortVertex graphData 2 = data.portVertex 2 ∨
        data.rotationPortVertex graphData 2 = data.portVertex 3 := by
      have : data.rotationPortVertex graphData 2 ∈
          G.neighborSet data.secondVertex := hadj
      rw [data.secondNeighbors] at this
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hmem with hcentralEndpoint | hport
    · exfalso
      apply hsecond.1
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · have hfst : (data.rotationPortDart graphData 2).fst =
            data.secondVertex := by
          simpa using data.rotationPortDart_fst graphData (2 : Fin 4)
        exact hfst.symm
      · exact hcentralEndpoint.symm
    · exact hport
  · change data.rotationPortVertex graphData 3 = data.portVertex 2 ∨
      data.rotationPortVertex graphData 3 = data.portVertex 3
    have hadj : G.Adj data.secondVertex
        (data.rotationPortVertex graphData 3) := by
      simpa [rotationPortVertex, rotationPortDart_fst] using
        (data.rotationPortDart graphData 3).adj
    have hmem : data.rotationPortVertex graphData 3 = data.firstVertex ∨
        data.rotationPortVertex graphData 3 = data.portVertex 2 ∨
        data.rotationPortVertex graphData 3 = data.portVertex 3 := by
      have : data.rotationPortVertex graphData 3 ∈
          G.neighborSet data.secondVertex := hadj
      rw [data.secondNeighbors] at this
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hmem with hcentralEndpoint | hport
    · exfalso
      apply hsecond.2.1
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · have hfst : (data.rotationPortDart graphData 3).fst =
            data.secondVertex := by
          simpa using data.rotationPortDart_fst graphData (3 : Fin 4)
        exact hfst.symm
      · exact hcentralEndpoint.symm
    · exact hport

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem pair_eq_pair_of_mem_of_mem_of_ne
    {a b x y : V} (ha : a = x ∨ a = y) (hb : b = x ∨ b = y)
    (hab : a ≠ b) :
    ({a, b} : Set V) = {x, y} := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · rfl
  · ext vertex
    simp [or_comm]
  · exact False.elim (hab rfl)

theorem rotationPortVertex_zero_ne_one
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    data.rotationPortVertex graphData 0 ≠
      data.rotationPortVertex graphData 1 := by
  intro hendpoint
  have hdarts := rho_triple_pairwise_ne graphData.toRotationSystem
    hcubic hrotation data.rotationCentralDart
  apply hdarts.2.2
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact (data.rotationPortDart_fst graphData 0).trans
      (data.rotationPortDart_fst graphData 1).symm
  · exact hendpoint

theorem rotationPortVertex_two_ne_three
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    data.rotationPortVertex graphData 2 ≠
      data.rotationPortVertex graphData 3 := by
  intro hendpoint
  have hdarts := rho_triple_pairwise_ne graphData.toRotationSystem
    hcubic hrotation
      (graphData.toRotationSystem.alpha data.rotationCentralDart)
  apply hdarts.2.2
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact (data.rotationPortDart_fst graphData 2).trans
      (data.rotationPortDart_fst graphData 3).symm
  · exact hendpoint

theorem rotationFirstPortPair_eq
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    ({data.rotationPortVertex graphData 0,
        data.rotationPortVertex graphData 1} : Set V) =
      {data.portVertex 0, data.portVertex 1} := by
  apply pair_eq_pair_of_mem_of_mem_of_ne
  · simpa using data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (0 : Fin 4)
  · simpa using data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (1 : Fin 4)
  · exact data.rotationPortVertex_zero_ne_one graphData hcubic hrotation

theorem rotationSecondPortPair_eq
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    ({data.rotationPortVertex graphData 2,
        data.rotationPortVertex graphData 3} : Set V) =
      {data.portVertex 2, data.portVertex 3} := by
  apply pair_eq_pair_of_mem_of_mem_of_ne
  · simpa using data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (2 : Fin 4)
  · simpa using data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (3 : Fin 4)
  · exact data.rotationPortVertex_two_ne_three graphData hcubic hrotation

theorem rotationFirstPort_ne_rotationSecondPort
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {first second : Fin 4}
    (hfirst : first = 0 ∨ first = 1)
    (hsecond : second = 2 ∨ second = 3) :
    data.rotationPortVertex graphData first ≠
      data.rotationPortVertex graphData second := by
  have hfirstMem := data.rotationPortVertex_mem_originalPair graphData
    hcubic hrotation first
  have hsecondMem := data.rotationPortVertex_mem_originalPair graphData
    hcubic hrotation second
  rw [if_pos hfirst] at hfirstMem
  rw [if_neg (by
    rcases hsecond with rfl | rfl <;> decide)] at hsecondMem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirstMem hsecondMem
  rcases hfirstMem with hfirstZero | hfirstOne <;>
    rcases hsecondMem with hsecondTwo | hsecondThree
  · rw [hfirstZero, hsecondTwo]
    exact data.portVertex_ne (by decide)
  · rw [hfirstZero, hsecondThree]
    exact data.portVertex_ne (by decide)
  · rw [hfirstOne, hsecondTwo]
    exact data.portVertex_ne (by decide)
  · rw [hfirstOne, hsecondThree]
    exact data.portVertex_ne (by decide)

theorem rotationPortVertex_injective
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    Function.Injective (data.rotationPortVertex graphData) := by
  intro first second heq
  fin_cases first <;> fin_cases second
  · rfl
  · exact False.elim
      (data.rotationPortVertex_zero_ne_one graphData hcubic hrotation heq)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by left; rfl) (by left; rfl) heq)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by left; rfl) (by right; rfl) heq)
  · exact False.elim
      (data.rotationPortVertex_zero_ne_one graphData hcubic hrotation heq.symm)
  · rfl
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by right; rfl) (by left; rfl) heq)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by right; rfl) (by right; rfl) heq)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by left; rfl) (by left; rfl) heq.symm)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by right; rfl) (by left; rfl) heq.symm)
  · rfl
  · exact False.elim
      (data.rotationPortVertex_two_ne_three graphData hcubic hrotation heq)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by left; rfl) (by right; rfl) heq.symm)
  · exact False.elim
      (data.rotationFirstPort_ne_rotationSecondPort graphData hcubic hrotation
        (by right; rfl) (by right; rfl) heq.symm)
  · exact False.elim
      (data.rotationPortVertex_two_ne_three graphData hcubic hrotation heq.symm)
  · rfl

theorem rotationPortVertex_ne_firstVertex
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    data.rotationPortVertex graphData port ≠ data.firstVertex := by
  fin_cases port
  · change data.rotationPortVertex graphData 0 ≠ data.firstVertex
    intro heq
    apply (data.rotationPortDart graphData 0).fst_ne_snd
    exact (data.rotationPortDart_fst graphData 0).trans heq.symm
  · change data.rotationPortVertex graphData 1 ≠ data.firstVertex
    intro heq
    apply (data.rotationPortDart graphData 1).fst_ne_snd
    exact (data.rotationPortDart_fst graphData 1).trans heq.symm
  · change data.rotationPortVertex graphData 2 ≠ data.firstVertex
    have hmem := data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (2 : Fin 4)
    simp only [if_neg (by decide : ¬ ((2 : Fin 4) = 0 ∨ (2 : Fin 4) = 1)),
      Set.mem_insert_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with htwo | hthree
    · rw [htwo]
      exact data.portNeFirst 2
    · rw [hthree]
      exact data.portNeFirst 3
  · change data.rotationPortVertex graphData 3 ≠ data.firstVertex
    have hmem := data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (3 : Fin 4)
    simp only [if_neg (by decide : ¬ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 1)),
      Set.mem_insert_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with htwo | hthree
    · rw [htwo]
      exact data.portNeFirst 2
    · rw [hthree]
      exact data.portNeFirst 3

theorem rotationPortVertex_ne_secondVertex
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    data.rotationPortVertex graphData port ≠ data.secondVertex := by
  fin_cases port
  · change data.rotationPortVertex graphData 0 ≠ data.secondVertex
    have hmem := data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (0 : Fin 4)
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with hzero | hone
    · rw [hzero]
      exact data.portNeSecond 0
    · rw [hone]
      exact data.portNeSecond 1
  · change data.rotationPortVertex graphData 1 ≠ data.secondVertex
    have hmem := data.rotationPortVertex_mem_originalPair graphData
      hcubic hrotation (1 : Fin 4)
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hmem
    rcases hmem with hzero | hone
    · rw [hzero]
      exact data.portNeSecond 0
    · rw [hone]
      exact data.portNeSecond 1
  · change data.rotationPortVertex graphData 2 ≠ data.secondVertex
    intro heq
    apply (data.rotationPortDart graphData 2).fst_ne_snd
    exact (data.rotationPortDart_fst graphData 2).trans heq.symm
  · change data.rotationPortVertex graphData 3 ≠ data.secondVertex
    intro heq
    apply (data.rotationPortDart graphData 3).fst_ne_snd
    exact (data.rotationPortDart_fst graphData 3).trans heq.symm

def rotationOrderedData
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    AdjacentPairData G where
  firstVertex := data.firstVertex
  secondVertex := data.secondVertex
  portVertex := data.rotationPortVertex graphData
  centralAdjacent := data.centralAdjacent
  portInjective := data.rotationPortVertex_injective graphData hcubic hrotation
  portNeFirst := data.rotationPortVertex_ne_firstVertex graphData hcubic hrotation
  portNeSecond := data.rotationPortVertex_ne_secondVertex graphData hcubic hrotation
  firstNeighbors := by
    rw [data.firstNeighbors]
    exact congrArg (Set.insert data.secondVertex)
      (data.rotationFirstPortPair_eq graphData hcubic hrotation).symm
  secondNeighbors := by
    rw [data.secondNeighbors]
    exact congrArg (Set.insert data.firstVertex)
      (data.rotationSecondPortPair_eq graphData hcubic hrotation).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem nextHit_eq_of_hit_first_step
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root : {point // hit point}) (hnext : hit (perm root.1)) :
    nextHit perm hit root = ⟨perm root.1, hnext⟩ := by
  let returnTime := firstPositiveHitTime perm hit root.1 root.2
  have hpos : 0 < returnTime :=
    firstPositiveHitTime_pos perm hit root.1 root.2
  have hle : returnTime ≤ 1 := by
    apply firstPositiveHitTime_le_of_hit perm hit root.1 root.2
    · omega
    · simpa using hnext
  have heq : returnTime = 1 := by omega
  apply Subtype.ext
  simp [nextHit, returnTime, heq]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem nextHit_eq_of_hit_second_step
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root : {point // hit point})
    (hnotNext : ¬ hit (perm root.1))
    (hsecond : hit ((perm ^ 2) root.1)) :
    nextHit perm hit root = ⟨(perm ^ 2) root.1, hsecond⟩ := by
  let returnTime := firstPositiveHitTime perm hit root.1 root.2
  have hpos : 0 < returnTime :=
    firstPositiveHitTime_pos perm hit root.1 root.2
  have hle : returnTime ≤ 2 := by
    apply firstPositiveHitTime_le_of_hit perm hit root.1 root.2
    · omega
    · exact hsecond
  have hne : returnTime ≠ 1 := by
    intro heq
    have hhits := firstPositiveHitTime_hits perm hit root.1 root.2
    change hit ((perm ^ returnTime) root.1) at hhits
    rw [heq] at hhits
    simpa using hnotNext hhits
  have heq : returnTime = 2 := by omega
  apply Subtype.ext
  simp [nextHit, returnTime, heq]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem nextHit_eq_of_first_step_eq
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root target : {point // hit point})
    (hstep : perm root.1 = target.1) :
    nextHit perm hit root = target := by
  have hnext : hit (perm root.1) := hstep ▸ target.2
  exact (nextHit_eq_of_hit_first_step perm hit root hnext).trans
    (Subtype.ext hstep)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem nextHit_eq_of_second_step_eq
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop)
    (root target : {point // hit point})
    (hnotNext : ¬ hit (perm root.1))
    (hstep : (perm ^ 2) root.1 = target.1) :
    nextHit perm hit root = target := by
  have hsecond : hit ((perm ^ 2) root.1) := hstep ▸ target.2
  exact (nextHit_eq_of_hit_second_step perm hit root hnotNext hsecond).trans
    (Subtype.ext hstep)

def rotationDeletedBoundaryHalfDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    DeletedBoundaryHalfDart
      ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
        graphData)
      (data.rotationOrderedData graphData hcubic hrotation).deletedVertices := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  let RS := ordered.rootedRotationSystem graphData
  let dart := data.rotationPortDart graphData port
  have hbased : RS.vertOf dart ∈ ordered.deletedVertices := by
    change dart.fst ∈ ({data.firstVertex, data.secondVertex} : Finset V)
    rw [data.rotationPortDart_fst graphData port]
    fin_cases port <;> simp
  have hopposite : RS.vertOf (RS.alpha dart) ∉ ordered.deletedVertices := by
    change dart.snd ∉ ({data.firstVertex, data.secondVertex} : Finset V)
    simpa [dart, rotationPortVertex] using
      (show data.rotationPortVertex graphData port ≠ data.firstVertex ∧
          data.rotationPortVertex graphData port ≠ data.secondVertex from
        ⟨data.rotationPortVertex_ne_firstVertex graphData hcubic hrotation port,
          data.rotationPortVertex_ne_secondVertex graphData hcubic hrotation port⟩)
  exact ⟨⟨dart, hbased⟩, hopposite⟩

theorem deletedFacePerm_apply_deletedBoundaryHalfDart_val
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBoundaryHalfDart RS deleted) :
    (deletedFacePerm RS deleted dart.1).1 = RS.rho dart.1.1 := by
  rw [deletedFacePerm, Equiv.Perm.mul_apply,
    deletedAlpha_apply_boundary RS deleted dart.1 dart.2]
  rfl

theorem deletedFacePerm_apply_internal_val
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted)
    (hopposite : RS.vertOf (RS.alpha dart.1) ∈ deleted) :
    (deletedFacePerm RS deleted dart).1 =
      RS.rho (RS.alpha dart.1) := by
  rw [deletedFacePerm, Equiv.Perm.mul_apply, deletedRho_val,
    deletedAlpha_apply_internal RS deleted dart hopposite]

def rotationCentralBasedDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    DeletedBasedDart
      ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
        graphData)
      (data.rotationOrderedData graphData hcubic hrotation).deletedVertices := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  let RS := ordered.rootedRotationSystem graphData
  exact ⟨data.rotationCentralDart, by
    change data.firstVertex ∈ ({data.firstVertex, data.secondVertex} : Finset V)
    simp⟩

def rotationOppositeCentralBasedDart
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    DeletedBasedDart
      ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
        graphData)
      (data.rotationOrderedData graphData hcubic hrotation).deletedVertices := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  let RS := ordered.rootedRotationSystem graphData
  exact ⟨RS.alpha data.rotationCentralDart, by
    change data.secondVertex ∈ ({data.firstVertex, data.secondVertex} : Finset V)
    simp⟩

theorem rotationDeletedFace_zero
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    deletedFacePerm
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 0).1 =
      (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 1).1 := by
  apply Subtype.ext
  rw [deletedFacePerm_apply_deletedBoundaryHalfDart_val]
  rfl

theorem rotationDeletedFace_one
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    deletedFacePerm
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 1).1 =
      data.rotationCentralBasedDart graphData hcubic hrotation := by
  apply Subtype.ext
  rw [deletedFacePerm_apply_deletedBoundaryHalfDart_val]
  have hcube := rho_cube_apply_of_isCubic graphData.toRotationSystem
    hcubic hrotation data.rotationCentralDart
  exact hcube

theorem rotationDeletedFace_central
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    deletedFacePerm
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationCentralBasedDart graphData hcubic hrotation) =
      (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 2).1 := by
  apply Subtype.ext
  rw [deletedFacePerm_apply_internal_val]
  · rfl
  · change data.secondVertex ∈
      ({data.firstVertex, data.secondVertex} : Finset V)
    simp

theorem rotationDeletedFace_two
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    deletedFacePerm
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 2).1 =
      (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 3).1 := by
  apply Subtype.ext
  rw [deletedFacePerm_apply_deletedBoundaryHalfDart_val]
  rfl

theorem rotationDeletedFace_three
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    deletedFacePerm
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 3).1 =
      data.rotationOppositeCentralBasedDart graphData hcubic hrotation := by
  apply Subtype.ext
  rw [deletedFacePerm_apply_deletedBoundaryHalfDart_val]
  have hcube := rho_cube_apply_of_isCubic graphData.toRotationSystem
    hcubic hrotation
      (graphData.toRotationSystem.alpha data.rotationCentralDart)
  exact hcube

theorem rotationDeletedFace_oppositeCentral
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    deletedFacePerm
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationOppositeCentralBasedDart graphData hcubic hrotation) =
      (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 0).1 := by
  apply Subtype.ext
  rw [deletedFacePerm_apply_internal_val]
  · simp [rotationOppositeCentralBasedDart,
      rotationDeletedBoundaryHalfDart, rotationPortDart,
      rootedGraphData,
      GoertzelV24TwoEdgeCutCapGeometry.graphDataWithOuter]
  · change data.firstVertex ∈
      ({data.firstVertex, data.secondVertex} : Finset V)
    simp

theorem rotationBoundaryNextHit_zero
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    nextHitPerm
        (deletedFacePerm
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (IsDeletedBoundaryHalfDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 0) =
      data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 1 := by
  rw [nextHitPerm_apply]
  apply nextHit_eq_of_first_step_eq
  exact data.rotationDeletedFace_zero graphData hcubic hrotation

theorem rotationBoundaryNextHit_one
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    nextHitPerm
        (deletedFacePerm
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (IsDeletedBoundaryHalfDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 1) =
      data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 2 := by
  rw [nextHitPerm_apply]
  apply nextHit_eq_of_second_step_eq
  · rw [data.rotationDeletedFace_one graphData hcubic hrotation]
    intro hboundary
    apply hboundary
    change data.secondVertex ∈
      ({data.firstVertex, data.secondVertex} : Finset V)
    simp
  · rw [pow_two, Equiv.Perm.mul_apply,
      data.rotationDeletedFace_one graphData hcubic hrotation,
      data.rotationDeletedFace_central graphData hcubic hrotation]

theorem rotationBoundaryNextHit_two
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    nextHitPerm
        (deletedFacePerm
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (IsDeletedBoundaryHalfDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 2) =
      data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 3 := by
  rw [nextHitPerm_apply]
  apply nextHit_eq_of_first_step_eq
  exact data.rotationDeletedFace_two graphData hcubic hrotation

theorem rotationBoundaryNextHit_three
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    nextHitPerm
        (deletedFacePerm
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (IsDeletedBoundaryHalfDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 3) =
      data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation 0 := by
  rw [nextHitPerm_apply]
  apply nextHit_eq_of_second_step_eq
  · rw [data.rotationDeletedFace_three graphData hcubic hrotation]
    intro hboundary
    apply hboundary
    change data.firstVertex ∈
      ({data.firstVertex, data.secondVertex} : Finset V)
    simp
  · rw [pow_two, Equiv.Perm.mul_apply,
      data.rotationDeletedFace_three graphData hcubic hrotation,
      data.rotationDeletedFace_oppositeCentral graphData hcubic hrotation]

theorem rotationBoundarySuccessor_apply_port
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    deletedRegionBoundarySuccessor
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (deletedBoundaryHalfDartEquivBoundaryDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
          (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation port)) =
      deletedBoundaryHalfDartEquivBoundaryDart
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation
          (finRotate 4 port)) := by
  fin_cases port
  · simpa [deletedRegionBoundarySuccessor, Equiv.permCongr_apply] using
      congrArg
        (deletedBoundaryHalfDartEquivBoundaryDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationBoundaryNextHit_zero graphData hcubic hrotation)
  · simpa [deletedRegionBoundarySuccessor, Equiv.permCongr_apply] using
      congrArg
        (deletedBoundaryHalfDartEquivBoundaryDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationBoundaryNextHit_one graphData hcubic hrotation)
  · simpa [deletedRegionBoundarySuccessor, Equiv.permCongr_apply] using
      congrArg
        (deletedBoundaryHalfDartEquivBoundaryDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationBoundaryNextHit_two graphData hcubic hrotation)
  · simpa [deletedRegionBoundarySuccessor, Equiv.permCongr_apply] using
      congrArg
        (deletedBoundaryHalfDartEquivBoundaryDart
          ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
            graphData)
          (data.rotationOrderedData graphData hcubic hrotation).deletedVertices)
        (data.rotationBoundaryNextHit_three graphData hcubic hrotation)

theorem deletedBoundaryHalfDartEquivBoundaryDart_edgeOf
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBoundaryHalfDart RS deleted) :
    RS.edgeOf
        ((deletedBoundaryHalfDartEquivBoundaryDart RS deleted dart).1.1) =
      RS.edgeOf dart.1.1 := by
  exact RS.edge_alpha dart.1.1

theorem rotationBoundaryDart_edgeOf
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (port : Fin 4) :
    ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
        graphData).edgeOf
      ((deletedBoundaryHalfDartEquivBoundaryDart
        ((data.rotationOrderedData graphData hcubic hrotation).rootedRotationSystem
          graphData)
        (data.rotationOrderedData graphData hcubic hrotation).deletedVertices
        (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation port)).1.1) =
      (data.rotationOrderedData graphData hcubic hrotation).boundaryEdge port := by
  rw [deletedBoundaryHalfDartEquivBoundaryDart_edgeOf]
  fin_cases port
  · apply Subtype.ext
    simp [rotationDeletedBoundaryHalfDart, rotationPortDart,
      rotationOrderedData, boundaryEdge, rotationPortVertex,
      rotationCentralDart, SimpleGraph.Dart.edge]
    left
    apply Prod.ext
    · exact data.rotationPortDart_fst graphData 0
    · rfl
  · apply Subtype.ext
    simp [rotationDeletedBoundaryHalfDart, rotationPortDart,
      rotationOrderedData, boundaryEdge, rotationPortVertex,
      rotationCentralDart, SimpleGraph.Dart.edge]
    left
    apply Prod.ext
    · exact data.rotationPortDart_fst graphData 1
    · rfl
  · apply Subtype.ext
    simp [rotationDeletedBoundaryHalfDart, rotationPortDart,
      rotationOrderedData, boundaryEdge, rotationPortVertex,
      rotationCentralDart, SimpleGraph.Dart.edge]
    left
    apply Prod.ext
    · exact data.rotationPortDart_fst graphData 2
    · rfl
  · apply Subtype.ext
    simp [rotationDeletedBoundaryHalfDart, rotationPortDart,
      rotationOrderedData, boundaryEdge, rotationPortVertex,
      rotationCentralDart, SimpleGraph.Dart.edge]
    left
    apply Prod.ext
    · exact data.rotationPortDart_fst graphData 3
    · rfl

/-- Reading the ports from the two local cubic rotations makes their cyclic
deleted-region boundary order automatic. -/
theorem rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder
    (graphData : Data G) (data : AdjacentPairData G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    (data.rotationOrderedData graphData hcubic hrotation).PortsFollowCyclicDeletedBoundaryOrder
      graphData := by
  let ordered := data.rotationOrderedData graphData hcubic hrotation
  let RS := ordered.rootedRotationSystem graphData
  apply Equiv.ext
  intro dart
  have hedgeMem : RS.edgeOf dart.1.1 ∈
      vertexSetCrossingEdges RS ordered.deletedVertices :=
    boundaryDart_edge_mem_vertexSetCrossingEdges RS ordered.deletedVertices dart
  rw [← ordered.boundaryEdgeSet_eq_vertexSetCrossingEdges
    (ordered.rootedGraphData graphData)] at hedgeMem
  rcases Finset.mem_image.mp hedgeMem with ⟨port, _hport, hedge⟩
  let canonical := deletedBoundaryHalfDartEquivBoundaryDart
    RS ordered.deletedVertices
      (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation port)
  have hcanonicalEdge : RS.edgeOf canonical.1.1 = ordered.boundaryEdge port := by
    exact data.rotationBoundaryDart_edgeOf graphData hcubic hrotation port
  have hdart : dart = canonical := by
    apply boundaryDart_eq_of_edgeOf_eq
    exact hedge.symm.trans hcanonicalEdge.symm
  rw [hdart]
  rw [data.rotationBoundarySuccessor_apply_port graphData hcubic hrotation port]
  apply boundaryDart_eq_of_edgeOf_eq
  calc
    RS.edgeOf
        ((deletedBoundaryHalfDartEquivBoundaryDart RS ordered.deletedVertices
          (data.rotationDeletedBoundaryHalfDart graphData hcubic hrotation
            (finRotate 4 port))).1.1) =
      ordered.boundaryEdge (finRotate 4 port) :=
        data.rotationBoundaryDart_edgeOf graphData hcubic hrotation
          (finRotate 4 port)
    _ = RS.edgeOf
        ((ordered.squareExpectedBoundaryCycle graphData
          SquareReductionSide.join12_30 canonical).1.1) :=
      (ordered.squareExpectedBoundaryCycle_edgeOf graphData
        SquareReductionSide.join12_30 canonical port hcanonicalEdge).symm

/-- Every adjacent-pair configuration in a vertex-minimal counterexample can
be relabeled from its local rotations and then colored through the planar
`01|23` reduction.  No boundary-order premise remains. -/
theorem exists_cyclicallyOrdered_deletedColoring_join01_23_compatible
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G) :
    ∃ ordered : AdjacentPairData G,
      ordered.firstVertex = data.firstVertex ∧
      ordered.secondVertex = data.secondVertex ∧
      ordered.PortsFollowCyclicDeletedBoundaryOrder graphData ∧
      ∃ deletedColoring :
          (DeletedAdjacentPairGraph G ordered.firstVertex
            ordered.secondVertex).EdgeColoring Color,
        IsTaitEdgeColoring
            (DeletedAdjacentPairGraph G ordered.firstVertex ordered.secondVertex)
            deletedColoring ∧
          SquareReductionSide.join01_23.Compatible
            (ordered.degreeTwoBoundaryData.colorWord deletedColoring) := by
  let ordered := data.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  have horder : ordered.PortsFollowCyclicDeletedBoundaryOrder graphData :=
    data.rotationOrderedData_portsFollowCyclicDeletedBoundaryOrder graphData
      minimal.spherical.cubic minimal.vertexRotationCyclic
  refine ⟨ordered, rfl, rfl, horder, ?_⟩
  exact ordered.exists_deletedColoring_join01_23_compatible_of_order
    graphData minimal horder

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
