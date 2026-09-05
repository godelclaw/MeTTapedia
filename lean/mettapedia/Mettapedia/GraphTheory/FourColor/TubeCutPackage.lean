import Mettapedia.GraphTheory.FourColor.CyclicCutSaturation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionAdapter

/-!
# One connected cut of the length-4 (5,0)-tube annulus as a `ConnectedAtWidth` object

The tube annulus (cap pendants removed) is a `SimpleGraph (Fin 50)` from an
explicit edge list. The innermost five-edge cut of the sealed chain is
realized: the cut is the set of edges crossing the side (so the cut
equation holds by definition), a cycle is exhibited on each side, both
sides are connected (decided), and the width is at most 6.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.FourColor.TubeCutPackage

open SimpleGraph

def edgeList : List (Nat × Nat) := [(0, 2), (0, 4), (1, 2), (1, 9), (2, 10), (3, 4), (3, 6), (4, 13), (5, 6), (5, 8), (6, 15), (7, 8), (7, 9), (8, 17), (9, 11), (10, 12), (10, 14), (11, 12), (11, 19), (12, 20), (13, 14), (13, 16), (14, 23), (15, 16), (15, 18), (16, 25), (17, 18), (17, 19), (18, 27), (19, 21), (20, 22), (20, 24), (21, 22), (21, 29), (22, 30), (23, 24), (23, 26), (24, 33), (25, 26), (25, 28), (26, 35), (27, 28), (27, 29), (28, 37), (29, 31), (30, 32), (30, 34), (31, 32), (31, 39), (32, 40), (33, 34), (33, 36), (34, 43), (35, 36), (35, 38), (36, 45), (37, 38), (37, 39), (38, 47), (39, 41), (40, 42), (40, 44), (41, 42), (41, 49), (43, 44), (43, 46), (45, 46), (45, 48), (47, 48), (47, 49)]

def adjB (u v : Fin 50) : Bool :=
  edgeList.any fun e => (e.1 == u.val && e.2 == v.val) || (e.1 == v.val && e.2 == u.val)

def tube : SimpleGraph (Fin 50) := SimpleGraph.fromRel fun u v => adjB u v = true

instance : DecidableRel tube.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (adjB u v = true ∨ adjB v u = true)))

/-- the inner side of the innermost cut -/
def sideList : List Nat := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
def side (v : Fin 50) : Prop := sideList.contains v.val = true
instance : DecidablePred side := fun v => inferInstanceAs (Decidable (sideList.contains v.val = true))

instance : DecidablePred (EdgeCrossesVertexSide tube side) := fun e => by
  unfold EdgeCrossesVertexSide
  infer_instance

/-- the cut: exactly the edges crossing the side -/
def cutEdges : Finset tube.edgeSet := Finset.univ.filter fun e => EdgeCrossesVertexSide tube side e

theorem cutEdges_iff (e : tube.edgeSet) : e ∈ cutEdges ↔ EdgeCrossesVertexSide tube side e := by
  simp [cutEdges]

def insideCycle : tube.Walk 41 41 := Walk.cons (by decide : tube.Adj 41 49) (Walk.cons (by decide : tube.Adj 49 47) (Walk.cons (by decide : tube.Adj 47 48) (Walk.cons (by decide : tube.Adj 48 45) (Walk.cons (by decide : tube.Adj 45 46) (Walk.cons (by decide : tube.Adj 46 43) (Walk.cons (by decide : tube.Adj 43 44) (Walk.cons (by decide : tube.Adj 44 40) (Walk.cons (by decide : tube.Adj 40 42) (Walk.cons (by decide : tube.Adj 42 41) (Walk.nil))))))))))
def outsideCycle : tube.Walk 30 30 := Walk.cons (by decide : tube.Adj 30 22) (Walk.cons (by decide : tube.Adj 22 21) (Walk.cons (by decide : tube.Adj 21 29) (Walk.cons (by decide : tube.Adj 29 31) (Walk.cons (by decide : tube.Adj 31 32) (Walk.cons (by decide : tube.Adj 32 30) (Walk.nil))))))

theorem insideCycle_isCycle : insideCycle.IsCycle :=
  ⟨⟨⟨by decide⟩, by simp [insideCycle]⟩, by decide⟩
theorem outsideCycle_isCycle : outsideCycle.IsCycle :=
  ⟨⟨⟨by decide⟩, by simp [outsideCycle]⟩, by decide⟩
theorem insideCycle_support : ∀ v, v ∈ insideCycle.support → side v := by decide
theorem outsideCycle_support : ∀ v, v ∈ outsideCycle.support → ¬ side v := by decide

def realization : CyclicEdgeCutRealization tube cutEdges where
  side := side
  hcut_eq := cutEdges_iff
  hinside_cycle := ⟨41, by decide, insideCycle, insideCycle_isCycle, insideCycle_support⟩
  houtside_cycle := ⟨30, by decide, outsideCycle, outsideCycle_isCycle, outsideCycle_support⟩

def sideSet : Set (Fin 50) := fun v => side v
def coSideSet : Set (Fin 50) := fun v => ¬ side v
instance : DecidablePred (fun v : Fin 50 => v ∈ sideSet) := fun v =>
  inferInstanceAs (Decidable (side v))
instance : DecidablePred (fun v : Fin 50 => v ∈ coSideSet) := fun v =>
  inferInstanceAs (Decidable (¬ side v))
instance : DecidablePred (fun v : Fin 50 => v ∈ (show Set (Fin 50) from side)) := fun v =>
  inferInstanceAs (Decidable (side v))
instance : DecidablePred (fun v : Fin 50 => v ∈ (show Set (Fin 50) from fun v => ¬ side v)) := fun v =>
  inferInstanceAs (Decidable (¬ side v))

instance (priority := high) : Fintype {v // v ∈ (show Set (Fin 50) from side)} :=
  Subtype.fintype _
instance (priority := high) : Fintype {v // v ∈ (show Set (Fin 50) from fun v => ¬ side v)} :=
  Subtype.fintype _

instance : DecidableRel (tube.induce side).Adj := fun u v =>
  inferInstanceAs (Decidable (tube.Adj u.1 v.1))
instance : DecidableRel (tube.induce fun v => ¬ side v).Adj := fun u v =>
  inferInstanceAs (Decidable (tube.Adj u.1 v.1))

theorem side_preconnected : (tube.induce side).Preconnected := by decide
/-- a walk through every vertex of the complement (the sweep path's suffix) -/
def complementSpan : (tube.induce fun v => ¬ side v).Walk ⟨32, by decide⟩ ⟨7, by decide⟩ :=
  Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨32, by decide⟩ ⟨30, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨30, by decide⟩ ⟨34, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨34, by decide⟩ ⟨33, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨33, by decide⟩ ⟨36, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨36, by decide⟩ ⟨35, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨35, by decide⟩ ⟨38, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨38, by decide⟩ ⟨37, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨37, by decide⟩ ⟨39, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨39, by decide⟩ ⟨31, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨31, by decide⟩ ⟨29, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨29, by decide⟩ ⟨21, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨21, by decide⟩ ⟨22, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨22, by decide⟩ ⟨20, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨20, by decide⟩ ⟨24, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨24, by decide⟩ ⟨23, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨23, by decide⟩ ⟨26, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨26, by decide⟩ ⟨25, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨25, by decide⟩ ⟨28, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨28, by decide⟩ ⟨27, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨27, by decide⟩ ⟨18, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨18, by decide⟩ ⟨15, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨15, by decide⟩ ⟨16, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨16, by decide⟩ ⟨13, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨13, by decide⟩ ⟨14, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨14, by decide⟩ ⟨10, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨10, by decide⟩ ⟨12, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨12, by decide⟩ ⟨11, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨11, by decide⟩ ⟨19, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨19, by decide⟩ ⟨17, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨17, by decide⟩ ⟨8, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨8, by decide⟩ ⟨5, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨5, by decide⟩ ⟨6, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨6, by decide⟩ ⟨3, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨3, by decide⟩ ⟨4, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨4, by decide⟩ ⟨0, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨0, by decide⟩ ⟨2, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨2, by decide⟩ ⟨1, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨1, by decide⟩ ⟨9, by decide⟩) (Walk.cons (by decide : (tube.induce fun v => ¬ side v).Adj ⟨9, by decide⟩ ⟨7, by decide⟩) (Walk.nil)))))))))))))))))))))))))))))))))))))))
theorem complementSpan_support : ∀ v, v ∈ complementSpan.support := by decide
theorem complement_preconnected : (tube.induce fun v => ¬ side v).Preconnected := fun u v =>
  ((complementSpan.takeUntil u (complementSpan_support u)).reachable).symm.trans
    (complementSpan.takeUntil v (complementSpan_support v)).reachable

theorem side_connected : (tube.induce side).Connected := by
  haveI : Nonempty {v // v ∈ (show Set (Fin 50) from side)} := ⟨⟨(40 : Fin 50), by decide⟩⟩
  exact ⟨side_preconnected⟩
theorem complement_connected : (tube.induce fun v => ¬ side v).Connected := by
  haveI : Nonempty {v // v ∈ (show Set (Fin 50) from fun v => ¬ side v)} := ⟨⟨(0 : Fin 50), by decide⟩⟩
  exact ⟨complement_preconnected⟩

theorem cutEdges_card : cutEdges.card ≤ 6 := by decide

def cut0 : CyclicEdgeCutRealization.ConnectedAtWidth tube 6 where
  edgeCut := cutEdges
  realization := realization
  card_le := cutEdges_card
  side_connected := side_connected
  complement_connected := complement_connected


/-! ## A rooted branch decomposition of the tube of width 11, in the stack's type -/

open GoertzelV24ConnectedBranchDecompositionForest GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24ConnectedEdgeShoreMajority GoertzelV24SphereCutMaterial

/-- computable middle set: vertices touching an edge in the shore and one outside -/
def middleB (shore : Finset tube.edgeSet) : Finset (Fin 50) :=
  Finset.univ.filter fun v =>
    (∃ e ∈ shore, v ∈ (e : Sym2 (Fin 50))) ∧ ∃ e ∈ Finset.univ \ shore, v ∈ (e : Sym2 (Fin 50))

theorem middle_eq (shore : Finset tube.edgeSet) :
    edgeShoreMiddleVertices tube shore = middleB shore := by
  ext v
  simp [edgeShoreMiddleVertices, middleVertices, middleB]

def everyCutWidthAtMostB (bound : Nat) : EdgeLeafTree tube.edgeSet → Bool
  | .leaf e => (middleB {e}).card ≤ bound
  | .fork l r => (middleB (EdgeLeafTree.fork l r).shore).card ≤ bound &&
      everyCutWidthAtMostB bound l && everyCutWidthAtMostB bound r

theorem everyCutWidthAtMost_iff (bound : Nat) :
    ∀ t : EdgeLeafTree tube.edgeSet,
      EveryCutWidthAtMost (G := tube) bound t ↔ everyCutWidthAtMostB bound t = true
  | .leaf e => by simp [EveryCutWidthAtMost, everyCutWidthAtMostB, middle_eq]
  | .fork l r => by
      simp only [EveryCutWidthAtMost, everyCutWidthAtMostB, middle_eq, Bool.and_eq_true,
        decide_eq_true_eq, everyCutWidthAtMost_iff bound l, everyCutWidthAtMost_iff bound r]
      tauto

def decomp : RootedBranchDecomposition (G := tube) where
  rootEdge := ⟨s((30 : Fin 50), (32 : Fin 50)), by decide⟩
  left := EdgeLeafTree.leaf ⟨s((30 : Fin 50), (34 : Fin 50)), by decide⟩
  right := EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((22 : Fin 50), (30 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((31 : Fin 50), (32 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((32 : Fin 50), (40 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((31 : Fin 50), (39 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((29 : Fin 50), (31 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((33 : Fin 50), (34 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((34 : Fin 50), (43 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((33 : Fin 50), (36 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((24 : Fin 50), (33 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((35 : Fin 50), (36 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((36 : Fin 50), (45 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((35 : Fin 50), (38 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((26 : Fin 50), (35 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((37 : Fin 50), (38 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((37 : Fin 50), (39 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((38 : Fin 50), (47 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((39 : Fin 50), (41 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((28 : Fin 50), (37 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((40 : Fin 50), (42 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((41 : Fin 50), (42 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((40 : Fin 50), (44 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((43 : Fin 50), (44 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((41 : Fin 50), (49 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((47 : Fin 50), (49 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((43 : Fin 50), (46 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((45 : Fin 50), (46 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((45 : Fin 50), (48 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((47 : Fin 50), (48 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((20 : Fin 50), (22 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((20 : Fin 50), (24 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((21 : Fin 50), (22 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((21 : Fin 50), (29 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((23 : Fin 50), (24 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((23 : Fin 50), (26 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((25 : Fin 50), (26 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((25 : Fin 50), (28 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((27 : Fin 50), (28 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((27 : Fin 50), (29 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((12 : Fin 50), (20 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((14 : Fin 50), (23 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((16 : Fin 50), (25 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((18 : Fin 50), (27 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((19 : Fin 50), (21 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((10 : Fin 50), (12 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((10 : Fin 50), (14 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((11 : Fin 50), (12 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((11 : Fin 50), (19 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((13 : Fin 50), (14 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((13 : Fin 50), (16 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((15 : Fin 50), (16 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((15 : Fin 50), (18 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((17 : Fin 50), (18 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((17 : Fin 50), (19 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((2 : Fin 50), (10 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((4 : Fin 50), (13 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((6 : Fin 50), (15 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((8 : Fin 50), (17 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((9 : Fin 50), (11 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((0 : Fin 50), (2 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((0 : Fin 50), (4 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((1 : Fin 50), (2 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((1 : Fin 50), (9 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((3 : Fin 50), (4 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((3 : Fin 50), (6 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((5 : Fin 50), (6 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((5 : Fin 50), (8 : Fin 50)), by decide⟩) (EdgeLeafTree.fork (EdgeLeafTree.leaf ⟨s((7 : Fin 50), (8 : Fin 50)), by decide⟩) (EdgeLeafTree.leaf ⟨s((7 : Fin 50), (9 : Fin 50)), by decide⟩)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  leavesNodup := by decide
  leavesCover := by decide

theorem decomp_width : decomp.WidthAtMost 11 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [middle_eq]; decide
  · rw [everyCutWidthAtMost_iff]; decide
  · rw [everyCutWidthAtMost_iff]; decide

end Mettapedia.GraphTheory.FourColor.TubeCutPackage
