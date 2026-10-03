import MettapediaFourColor.FacialChainClosure
import MettapediaFourColor.SevenPairSector

/-!
# Constructing the shared seven-pair sector from an actual edge

Triangle attachment reads actual vertex rotations. The ambient degrees
close the eight remaining seams. The chart's facial hypotheses are therefore
constructed from a root dart and its degree observations; no complete
occurrence or injectivity of distant labels is assumed.
-/

namespace FourColor.SevenPairSectorRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap FacialChainClosure
open SevenPairSector (Label)

set_option linter.style.setOption false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def openFaces : Finset (Fin 31) := {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,18,20,23,25,27,28,29}

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- The facial attachments before the degree-dependent seams close. -/
structure Seed where
  vertex : Label → V
  corner : ∀ i : Fin 31, i ∈ openFaces →
    Corner rotation (vertex (SevenPairSectorData.face i).1)
      (vertex (SevenPairSectorData.face i).2.1)
      (vertex (SevenPairSectorData.face i).2.2)

variable [Finite V]

/-- Read the entire sector from one actual directed edge.
Only the root's degree is needed to perform the attachments. -/
noncomputable def develop (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (seven : G.degree d.fst = 7) : Seed rotation := by
  let v0 := d.fst
  let v1 := d.snd
  let v2 := extend rotation v0 v1 (d.adj)
  have f0 : Corner rotation v0 v1 v2 :=
    extend_corner rotation v0 v1 (d.adj)
  let v3 := extend rotation v0 v2 (f0.choose_spec.choose)
  have f2 : Corner rotation v0 v2 v3 :=
    extend_corner rotation v0 v2 (f0.choose_spec.choose)
  let v4 := extend rotation v0 v3 (f2.choose_spec.choose)
  have f4 : Corner rotation v0 v3 v4 :=
    extend_corner rotation v0 v3 (f2.choose_spec.choose)
  let v5 := extend rotation v0 v4 (f4.choose_spec.choose)
  have f6 : Corner rotation v0 v4 v5 :=
    extend_corner rotation v0 v4 (f4.choose_spec.choose)
  let v6 := extend rotation v0 v5 (f6.choose_spec.choose)
  have f8 : Corner rotation v0 v5 v6 :=
    extend_corner rotation v0 v5 (f6.choose_spec.choose)
  let v7 := extend rotation v0 v6 (f8.choose_spec.choose)
  have f10 : Corner rotation v0 v6 v7 :=
    extend_corner rotation v0 v6 (f8.choose_spec.choose)
  have f12 : Corner rotation v0 v7 v1 := by
    apply close rotation cyclic (by decide : 0 < 6) v0
      (![v1,v2,v3,v4,v5,v6,v7] : Fin 7 → V)
    · intro i
      fin_cases i
      · exact f0
      · exact f2
      · exact f4
      · exact f6
      · exact f8
      · exact f10
    · exact seven
  let v8 := extend rotation v2 v1 ((Corner.rotate rotation tri f0).choose.symm)
  have f1 : Corner rotation v2 v1 v8 :=
    extend_corner rotation v2 v1 ((Corner.rotate rotation tri f0).choose.symm)
  let v9 := extend rotation v3 v2 ((Corner.rotate rotation tri f2).choose.symm)
  have f3 : Corner rotation v3 v2 v9 :=
    extend_corner rotation v3 v2 ((Corner.rotate rotation tri f2).choose.symm)
  let v10 := extend rotation v4 v3 ((Corner.rotate rotation tri f4).choose.symm)
  have f5 : Corner rotation v4 v3 v10 :=
    extend_corner rotation v4 v3 ((Corner.rotate rotation tri f4).choose.symm)
  let v11 := extend rotation v5 v4 ((Corner.rotate rotation tri f6).choose.symm)
  have f7 : Corner rotation v5 v4 v11 :=
    extend_corner rotation v5 v4 ((Corner.rotate rotation tri f6).choose.symm)
  let v12 := extend rotation v6 v5 ((Corner.rotate rotation tri f8).choose.symm)
  have f9 : Corner rotation v6 v5 v12 :=
    extend_corner rotation v6 v5 ((Corner.rotate rotation tri f8).choose.symm)
  let v13 := extend rotation v7 v6 ((Corner.rotate rotation tri f10).choose.symm)
  have f11 : Corner rotation v7 v6 v13 :=
    extend_corner rotation v7 v6 ((Corner.rotate rotation tri f10).choose.symm)
  let v14 := extend rotation v1 v7 ((Corner.rotate rotation tri f12).choose.symm)
  have f13 : Corner rotation v1 v7 v14 :=
    extend_corner rotation v1 v7 ((Corner.rotate rotation tri f12).choose.symm)
  let v15 := extend rotation v1 v14 (f13.choose_spec.choose)
  have f14 : Corner rotation v1 v14 v15 :=
    extend_corner rotation v1 v14 (f13.choose_spec.choose)
  let v16 := extend rotation v1 v15 (f14.choose_spec.choose)
  have f15 : Corner rotation v1 v15 v16 :=
    extend_corner rotation v1 v15 (f14.choose_spec.choose)
  let v17 := extend rotation v3 v9 (f3.choose_spec.choose)
  have f18 : Corner rotation v3 v9 v17 :=
    extend_corner rotation v3 v9 (f3.choose_spec.choose)
  let v18 := extend rotation v4 v10 (f5.choose_spec.choose)
  have f20 : Corner rotation v4 v10 v18 :=
    extend_corner rotation v4 v10 (f5.choose_spec.choose)
  let v19 := extend rotation v6 v12 (f9.choose_spec.choose)
  have f23 : Corner rotation v6 v12 v19 :=
    extend_corner rotation v6 v12 (f9.choose_spec.choose)
  let v20 := extend rotation v7 v13 (f11.choose_spec.choose)
  have f25 : Corner rotation v7 v13 v20 :=
    extend_corner rotation v7 v13 (f11.choose_spec.choose)
  let v21 := extend rotation v16 v15 ((Corner.rotate rotation tri f15).choose.symm)
  have f27 : Corner rotation v16 v15 v21 :=
    extend_corner rotation v16 v15 ((Corner.rotate rotation tri f15).choose.symm)
  let v22 := extend rotation v15 v14 ((Corner.rotate rotation tri f14).choose.symm)
  have f28 : Corner rotation v15 v14 v22 :=
    extend_corner rotation v15 v14 ((Corner.rotate rotation tri f14).choose.symm)
  let v23 := extend rotation v15 v22 (f28.choose_spec.choose)
  have f29 : Corner rotation v15 v22 v23 :=
    extend_corner rotation v15 v22 (f28.choose_spec.choose)
  refine ⟨![v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,
    v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23],?_⟩
  intro i hi
  fin_cases i
  · exact f0
  · exact f1
  · exact f2
  · exact f3
  · exact f4
  · exact f5
  · exact f6
  · exact f7
  · exact f8
  · exact f9
  · exact f10
  · exact f11
  · exact f12
  · exact f13
  · exact f14
  · exact f15
  · simp [openFaces] at hi
  · simp [openFaces] at hi
  · exact f18
  · simp [openFaces] at hi
  · exact f20
  · simp [openFaces] at hi
  · simp [openFaces] at hi
  · exact f23
  · simp [openFaces] at hi
  · exact f25
  · simp [openFaces] at hi
  · exact f27
  · exact f28
  · exact f29
  · simp [openFaces] at hi

@[simp] theorem develop_first (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (seven : G.degree d.fst = 7) :
    (develop rotation tri cyclic d seven).vertex 0 = d.fst := rfl

@[simp] theorem develop_second (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (seven : G.degree d.fst = 7) :
    (develop rotation tri cyclic d seven).vertex 1 = d.snd := rfl

variable {rotation} (x : Seed rotation)

/-- The retained degree observations are queried on the generated vertices. -/
def Fits : Prop := ∀ i ∈ SevenPairSector.observed,
  G.degree (x.vertex i) = SevenPairSectorData.degree i

/-- A finite degree test on the generated vertices, with no facial input checks. -/
def check : Bool := decide (∀ i ∈ SevenPairSector.observed,
  G.degree (x.vertex i) = SevenPairSectorData.degree i)

theorem check_iff : check x = true ↔ Fits x := by
  simp only [check, decide_eq_true_eq, Fits]

/-- Degree closure supplies every omitted facial seam. -/
noncomputable def complete (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) (fits : Fits x) :
    SevenPairSector.Reading rotation := by
  have f0 : Corner rotation (x.vertex 0) (x.vertex 1) (x.vertex 2) :=
    x.corner 0 (by decide +kernel)
  have f1 : Corner rotation (x.vertex 2) (x.vertex 1) (x.vertex 8) :=
    x.corner 1 (by decide +kernel)
  have f2 : Corner rotation (x.vertex 0) (x.vertex 2) (x.vertex 3) :=
    x.corner 2 (by decide +kernel)
  have f3 : Corner rotation (x.vertex 3) (x.vertex 2) (x.vertex 9) :=
    x.corner 3 (by decide +kernel)
  have f4 : Corner rotation (x.vertex 0) (x.vertex 3) (x.vertex 4) :=
    x.corner 4 (by decide +kernel)
  have f5 : Corner rotation (x.vertex 4) (x.vertex 3) (x.vertex 10) :=
    x.corner 5 (by decide +kernel)
  have f6 : Corner rotation (x.vertex 0) (x.vertex 4) (x.vertex 5) :=
    x.corner 6 (by decide +kernel)
  have f7 : Corner rotation (x.vertex 5) (x.vertex 4) (x.vertex 11) :=
    x.corner 7 (by decide +kernel)
  have f8 : Corner rotation (x.vertex 0) (x.vertex 5) (x.vertex 6) :=
    x.corner 8 (by decide +kernel)
  have f9 : Corner rotation (x.vertex 6) (x.vertex 5) (x.vertex 12) :=
    x.corner 9 (by decide +kernel)
  have f10 : Corner rotation (x.vertex 0) (x.vertex 6) (x.vertex 7) :=
    x.corner 10 (by decide +kernel)
  have f11 : Corner rotation (x.vertex 7) (x.vertex 6) (x.vertex 13) :=
    x.corner 11 (by decide +kernel)
  have f12 : Corner rotation (x.vertex 0) (x.vertex 7) (x.vertex 1) :=
    x.corner 12 (by decide +kernel)
  have f13 : Corner rotation (x.vertex 1) (x.vertex 7) (x.vertex 14) :=
    x.corner 13 (by decide +kernel)
  have f14 : Corner rotation (x.vertex 1) (x.vertex 14) (x.vertex 15) :=
    x.corner 14 (by decide +kernel)
  have f15 : Corner rotation (x.vertex 1) (x.vertex 15) (x.vertex 16) :=
    x.corner 15 (by decide +kernel)
  have f18 : Corner rotation (x.vertex 3) (x.vertex 9) (x.vertex 17) :=
    x.corner 18 (by decide +kernel)
  have f20 : Corner rotation (x.vertex 4) (x.vertex 10) (x.vertex 18) :=
    x.corner 20 (by decide +kernel)
  have f23 : Corner rotation (x.vertex 6) (x.vertex 12) (x.vertex 19) :=
    x.corner 23 (by decide +kernel)
  have f25 : Corner rotation (x.vertex 7) (x.vertex 13) (x.vertex 20) :=
    x.corner 25 (by decide +kernel)
  have f27 : Corner rotation (x.vertex 16) (x.vertex 15) (x.vertex 21) :=
    x.corner 27 (by decide +kernel)
  have f28 : Corner rotation (x.vertex 15) (x.vertex 14) (x.vertex 22) :=
    x.corner 28 (by decide +kernel)
  have f29 : Corner rotation (x.vertex 15) (x.vertex 22) (x.vertex 23) :=
    x.corner 29 (by decide +kernel)
  have f16 : Corner rotation (x.vertex 1) (x.vertex 16) (x.vertex 8) := by
    apply close rotation cyclic (by decide : 0 < 6) (x.vertex 1)
      (![x.vertex 8,x.vertex 2,x.vertex 0,x.vertex 7,
        x.vertex 14,x.vertex 15,x.vertex 16] : Fin 7 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f1)
      · exact (Corner.rotate rotation tri f0)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f12))
      · exact f13
      · exact f14
      · exact f15
    · exact fits 1 (by decide)
  have f17 : Corner rotation (x.vertex 2) (x.vertex 8) (x.vertex 9) := by
    apply close rotation cyclic (by decide : 0 < 4) (x.vertex 2)
      (![x.vertex 9,x.vertex 3,x.vertex 0,x.vertex 1,x.vertex 8] : Fin 5 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f3)
      · exact (Corner.rotate rotation tri f2)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f0))
      · exact f1
    · exact fits 2 (by decide)
  have f19 : Corner rotation (x.vertex 3) (x.vertex 17) (x.vertex 10) := by
    apply close rotation cyclic (by decide : 0 < 5) (x.vertex 3)
      (![x.vertex 10,x.vertex 4,x.vertex 0,x.vertex 2,x.vertex 9,x.vertex 17] : Fin 6 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f5)
      · exact (Corner.rotate rotation tri f4)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f2))
      · exact f3
      · exact f18
    · exact fits 3 (by decide)
  have f21 : Corner rotation (x.vertex 4) (x.vertex 18) (x.vertex 11) := by
    apply close rotation cyclic (by decide : 0 < 5) (x.vertex 4)
      (![x.vertex 11,x.vertex 5,x.vertex 0,x.vertex 3,x.vertex 10,x.vertex 18] : Fin 6 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f7)
      · exact (Corner.rotate rotation tri f6)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f4))
      · exact f5
      · exact f20
    · exact fits 4 (by decide)
  have f22 : Corner rotation (x.vertex 5) (x.vertex 11) (x.vertex 12) := by
    apply close rotation cyclic (by decide : 0 < 4) (x.vertex 5)
      (![x.vertex 12,x.vertex 6,x.vertex 0,x.vertex 4,x.vertex 11] : Fin 5 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f9)
      · exact (Corner.rotate rotation tri f8)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f6))
      · exact f7
    · exact fits 5 (by decide)
  have f24 : Corner rotation (x.vertex 6) (x.vertex 19) (x.vertex 13) := by
    apply close rotation cyclic (by decide : 0 < 5) (x.vertex 6)
      (![x.vertex 13,x.vertex 7,x.vertex 0,x.vertex 5,x.vertex 12,x.vertex 19] : Fin 6 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f11)
      · exact (Corner.rotate rotation tri f10)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f8))
      · exact f9
      · exact f23
    · exact fits 6 (by decide)
  have f26 : Corner rotation (x.vertex 7) (x.vertex 20) (x.vertex 14) := by
    apply close rotation cyclic (by decide : 0 < 5) (x.vertex 7)
      (![x.vertex 14,x.vertex 1,x.vertex 0,x.vertex 6,x.vertex 13,x.vertex 20] : Fin 6 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f13)
      · exact (Corner.rotate rotation tri f12)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f10))
      · exact f11
      · exact f25
    · exact fits 7 (by decide)
  have f30 : Corner rotation (x.vertex 15) (x.vertex 23) (x.vertex 21) := by
    apply close rotation cyclic (by decide : 0 < 5) (x.vertex 15)
      (![x.vertex 21,x.vertex 16,x.vertex 1,x.vertex 14,x.vertex 22,x.vertex 23] : Fin 6 → V)
    · intro i
      fin_cases i
      · exact (Corner.rotate rotation tri f27)
      · exact (Corner.rotate rotation tri f15)
      · exact (Corner.rotate rotation tri (Corner.rotate rotation tri f14))
      · exact f28
      · exact f29
    · exact fits 15 (by decide)
  refine ⟨x.vertex,?_⟩
  intro i
  fin_cases i
  · exact f0
  · exact f1
  · exact f2
  · exact f3
  · exact f4
  · exact f5
  · exact f6
  · exact f7
  · exact f8
  · exact f9
  · exact f10
  · exact f11
  · exact f12
  · exact f13
  · exact f14
  · exact f15
  · exact f16
  · exact f17
  · exact f18
  · exact f19
  · exact f20
  · exact f21
  · exact f22
  · exact f23
  · exact f24
  · exact f25
  · exact f26
  · exact f27
  · exact f28
  · exact f29
  · exact f30

theorem complete_profile (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) (fits : Fits x) :
    SevenPairSector.Profile (complete x tri cyclic fits) := fits

end FourColor.SevenPairSectorRecognition

namespace FourColor.ActualSevenPairRecognition

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality LocalCoverageAssembly
open MinimalExceptionalEmbedding (graph rotation)
open SevenPairSectorRecognition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

def seed {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d) :
    Seed (rotation original minimal) :=
  develop (rotation original minimal)
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
    ⟨(p.first,p.second),p.adjacent⟩ p.first_degree

/-- The actual pair's degree readings suffice: all 31 facial correspondences
are constructed, including the eight closing seams. -/
theorem continuation {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d)
    (fits : Fits (seed original minimal p))
    (upper : OnBall (graph original minimal) d.snd 5
      (fun w => (graph original minimal).degree w ≤ 7)) :
    ∃ w, w ≠ p.first ∧ w ≠ p.second ∧ (graph original minimal).degree w = 7 ∧
      w ∈ closedBall (graph original minimal) p.second 2 ∧
      w ∈ closedBall (graph original minimal) d.snd 5 := by
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  let cyclic := MinimalExceptionalEmbedding.cyclic original minimal
  exact ActualSevenPairSector.pair_continuation original minimal
    (complete (seed original minimal p) tri cyclic fits)
    (complete_profile _ tri cyclic fits) p rfl rfl upper


/-- A successful degree test on the actual rooted development supplies continuation. -/
theorem checked_continuation {d : (graph original minimal).Dart}
    (p : RuleFanSevenCluster.Pair original minimal d)
    (checked : check (seed original minimal p) = true)
    (upper : OnBall (graph original minimal) d.snd 5
      (fun w => (graph original minimal).degree w ≤ 7)) :
    ∃ w, w ≠ p.first ∧ w ≠ p.second ∧ (graph original minimal).degree w = 7 ∧
      w ∈ closedBall (graph original minimal) p.second 2 ∧
      w ∈ closedBall (graph original minimal) d.snd 5 :=
  continuation original minimal p ((check_iff _).mp checked) upper

end
end FourColor.ActualSevenPairRecognition
