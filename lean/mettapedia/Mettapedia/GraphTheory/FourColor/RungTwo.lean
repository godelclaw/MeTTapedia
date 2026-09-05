import Mettapedia.GraphTheory.FourColor.GeneralTubeNodes

/-!
# The rung of a thin annulus of thickness 2, as a slab shape

Vertices `0..5` along a path (`c, d1, e1, d2, e2, c'`), interior edges `j`
joining `j` and `j+1`, in-ports at `0, 1, 3, 5` (the F-edge, two b-edges, the
O-edge) and out-ports at `0, 2, 4, 5`.  The rotation is given explicitly on
the 18 darts; the tangle axioms and the two-darts-per-vertex property are
decided, and path connectivity is proved by induction.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace RungTwo

open GoertzelV24OpenTangleComposition

abbrev Vt := Fin 6
abbrev It := Fin 5 × Bool
abbrev Port := Fin 4
abbrev D := It ⊕ (Port ⊕ Port)

def interiorVert : It → Vt
  | (j, false) => j.castSucc
  | (j, true) => j.succ

def leftVert : Port → Vt := ![0, 1, 3, 5]
def rightVert : Port → Vt := ![0, 2, 4, 5]

def flip : It → It := fun ⟨j, b⟩ => ⟨j, !b⟩

def interiorAlpha : Equiv.Perm It where
  toFun := flip
  invFun := flip
  left_inv := by rintro ⟨j, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨j, b⟩; cases b <;> rfl

/-- the rotation: one 3-cycle at each vertex -/
def rhoFun : D → D
  -- vertex 0 (c): in0 → e(0,false) → out0 → in0
  | Sum.inr (Sum.inl 0) => Sum.inl (0, false)
  | Sum.inl (0, false) => Sum.inr (Sum.inr 0)
  | Sum.inr (Sum.inr 0) => Sum.inr (Sum.inl 0)
  -- vertex 1 (d1): e(0,true) → e(1,false) → in1 → e(0,true)
  | Sum.inl (0, true) => Sum.inl (1, false)
  | Sum.inl (1, false) => Sum.inr (Sum.inl 1)
  | Sum.inr (Sum.inl 1) => Sum.inl (0, true)
  -- vertex 2 (e1): e(1,true) → e(2,false) → out1 → e(1,true)
  | Sum.inl (1, true) => Sum.inl (2, false)
  | Sum.inl (2, false) => Sum.inr (Sum.inr 1)
  | Sum.inr (Sum.inr 1) => Sum.inl (1, true)
  -- vertex 3 (d2): e(2,true) → e(3,false) → in2 → e(2,true)
  | Sum.inl (2, true) => Sum.inl (3, false)
  | Sum.inl (3, false) => Sum.inr (Sum.inl 2)
  | Sum.inr (Sum.inl 2) => Sum.inl (2, true)
  -- vertex 4 (e2): e(3,true) → e(4,false) → out2 → e(3,true)
  | Sum.inl (3, true) => Sum.inl (4, false)
  | Sum.inl (4, false) => Sum.inr (Sum.inr 2)
  | Sum.inr (Sum.inr 2) => Sum.inl (3, true)
  -- vertex 5 (c'): e(4,true) → in3 → out3 → e(4,true)
  | Sum.inl (4, true) => Sum.inr (Sum.inl 3)
  | Sum.inr (Sum.inl 3) => Sum.inr (Sum.inr 3)
  | Sum.inr (Sum.inr 3) => Sum.inl (4, true)

theorem rhoFun_bijective : Function.Bijective rhoFun := by decide

noncomputable def rho : Equiv.Perm D := Equiv.ofBijective rhoFun rhoFun_bijective

theorem vert_rhoFun : ∀ d : D,
    twoSidedOpenTangleVertOf interiorVert leftVert rightVert (rhoFun d) =
      twoSidedOpenTangleVertOf interiorVert leftVert rightVert d := by decide

/-- the rung tangle -/
noncomputable def rung : TwoSidedOpenTangleData Vt It Port Port where
  interiorVert := interiorVert
  leftVert := leftVert
  rightVert := rightVert
  interiorAlpha := interiorAlpha
  interiorAlpha_involutive := by rintro ⟨j, b⟩; cases b <;> rfl
  interiorAlpha_fixfree := by rintro ⟨j, b⟩; cases b <;> simp [interiorAlpha, flip]
  rho := rho
  vert_rho := fun d => by
    show twoSidedOpenTangleVertOf interiorVert leftVert rightVert (rhoFun d) = _
    exact vert_rhoFun d
  interior_no_self_loops := by decide
  outer := Sum.inr (Sum.inl 0)

/-! ## The shape check -/

theorem two_darts : ∀ v : Vt, ∃ x x' : SlabDart rung, rung.vertOf x = v ∧ rung.vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  intro v
  fin_cases v
  · exact ⟨Sum.inl (0, false), Sum.inr (Sum.inl 0), rfl, rfl, by unfold NotOut; decide, by unfold NotOut; decide, by unfold DistinctEdge; decide⟩
  · exact ⟨Sum.inl (0, true), Sum.inl (1, false), rfl, rfl, by unfold NotOut; decide, by unfold NotOut; decide, by unfold DistinctEdge; decide⟩
  · exact ⟨Sum.inl (1, true), Sum.inl (2, false), rfl, rfl, by unfold NotOut; decide, by unfold NotOut; decide, by unfold DistinctEdge; decide⟩
  · exact ⟨Sum.inl (2, true), Sum.inl (3, false), rfl, rfl, by unfold NotOut; decide, by unfold NotOut; decide, by unfold DistinctEdge; decide⟩
  · exact ⟨Sum.inl (3, true), Sum.inl (4, false), rfl, rfl, by unfold NotOut; decide, by unfold NotOut; decide, by unfold DistinctEdge; decide⟩
  · exact ⟨Sum.inl (4, true), Sum.inr (Sum.inl 3), rfl, rfl, by unfold NotOut; decide, by unfold NotOut; decide, by unfold DistinctEdge; decide⟩

theorem adj_succ (j : Fin 5) : InteriorAdj rung j.castSucc j.succ :=
  ⟨(j, false), rfl, rfl⟩

theorem adj_pred (j : Fin 5) : InteriorAdj rung j.succ j.castSucc :=
  ⟨(j, true), rfl, rfl⟩

theorem reach_zero : ∀ v : Vt, Relation.ReflTransGen (InteriorAdj rung) 0 v := by
  intro v
  fin_cases v
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (adj_succ 0)
  · exact (Relation.ReflTransGen.single (adj_succ 0)).tail (adj_succ 1)
  · exact ((Relation.ReflTransGen.single (adj_succ 0)).tail (adj_succ 1)).tail (adj_succ 2)
  · exact (((Relation.ReflTransGen.single (adj_succ 0)).tail (adj_succ 1)).tail (adj_succ 2)).tail
      (adj_succ 3)
  · exact ((((Relation.ReflTransGen.single (adj_succ 0)).tail (adj_succ 1)).tail (adj_succ 2)).tail
      (adj_succ 3)).tail (adj_succ 4)

theorem reach_zero_rev : ∀ v : Vt, Relation.ReflTransGen (InteriorAdj rung) v 0 := by
  intro v
  fin_cases v
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (adj_pred 0)
  · exact (Relation.ReflTransGen.single (adj_pred 1)).tail (adj_pred 0)
  · exact ((Relation.ReflTransGen.single (adj_pred 2)).tail (adj_pred 1)).tail (adj_pred 0)
  · exact (((Relation.ReflTransGen.single (adj_pred 3)).tail (adj_pred 2)).tail (adj_pred 1)).tail
      (adj_pred 0)
  · exact ((((Relation.ReflTransGen.single (adj_pred 4)).tail (adj_pred 3)).tail (adj_pred 2)).tail
      (adj_pred 1)).tail (adj_pred 0)

theorem connected (u v : Vt) : Relation.ReflTransGen (InteriorAdj rung) u v :=
  (reach_zero_rev u).trans (reach_zero v)

theorem shape : SlabShape rung := ⟨two_darts, connected⟩

end RungTwo
end TubeSlab
end Mettapedia.GraphTheory.FourColor
