import Mettapedia.GraphTheory.FourColor.RungPair3
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `RungPair3` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair3

open Presented Pres

theorem two_darts : ∀ v : Fin 16, ∃ x x' : SlabDart (P.toTangle valid),
    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  intro v
  fin_cases v
  · exact ⟨Sum.inr (Sum.inl 0), Sum.inl (0, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (0, true), Sum.inl (1, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (1, true), Sum.inl (2, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (2, true), Sum.inl (3, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (3, true), Sum.inl (4, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (4, true), Sum.inl (5, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (5, true), Sum.inl (6, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 4), Sum.inl (6, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inr (Sum.inl 5), Sum.inl (7, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (7, true), Sum.inl (8, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (8, true), Sum.inl (9, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (9, true), Sum.inl (10, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (10, true), Sum.inl (11, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (11, true), Sum.inl (12, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (12, true), Sum.inl (13, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 9), Sum.inl (13, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩

abbrev R := InteriorAdj (P.toTangle valid)

theorem in0_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem in0_1 : Relation.ReflTransGen R 0 1 :=
  in0_0.trans (Relation.ReflTransGen.single (P.adj valid 0))
theorem in0_2 : Relation.ReflTransGen R 0 2 :=
  in0_1.trans (Relation.ReflTransGen.single (P.adj valid 1))
theorem in0_3 : Relation.ReflTransGen R 0 3 :=
  in0_2.trans (Relation.ReflTransGen.single (P.adj valid 2))
theorem in0_4 : Relation.ReflTransGen R 0 4 :=
  in0_3.trans (Relation.ReflTransGen.single (P.adj valid 3))
theorem in0_5 : Relation.ReflTransGen R 0 5 :=
  in0_4.trans (Relation.ReflTransGen.single (P.adj valid 4))
theorem in0_6 : Relation.ReflTransGen R 0 6 :=
  in0_5.trans (Relation.ReflTransGen.single (P.adj valid 5))
theorem in0_7 : Relation.ReflTransGen R 0 7 :=
  in0_6.trans (Relation.ReflTransGen.single (P.adj valid 6))
theorem in5_8 : Relation.ReflTransGen R 8 8 := Relation.ReflTransGen.refl
theorem in5_9 : Relation.ReflTransGen R 8 9 :=
  in5_8.trans (Relation.ReflTransGen.single (P.adj valid 7))
theorem in5_10 : Relation.ReflTransGen R 8 10 :=
  in5_9.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem in5_11 : Relation.ReflTransGen R 8 11 :=
  in5_10.trans (Relation.ReflTransGen.single (P.adj valid 9))
theorem in5_12 : Relation.ReflTransGen R 8 12 :=
  in5_11.trans (Relation.ReflTransGen.single (P.adj valid 10))
theorem in5_13 : Relation.ReflTransGen R 8 13 :=
  in5_12.trans (Relation.ReflTransGen.single (P.adj valid 11))
theorem in5_14 : Relation.ReflTransGen R 8 14 :=
  in5_13.trans (Relation.ReflTransGen.single (P.adj valid 12))
theorem in5_15 : Relation.ReflTransGen R 8 15 :=
  in5_14.trans (Relation.ReflTransGen.single (P.adj valid 13))
theorem out0_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem out0_1 : Relation.ReflTransGen R 0 1 :=
  out0_0.trans (Relation.ReflTransGen.single (P.adj valid 0))
theorem out0_2 : Relation.ReflTransGen R 0 2 :=
  out0_1.trans (Relation.ReflTransGen.single (P.adj valid 1))
theorem out0_3 : Relation.ReflTransGen R 0 3 :=
  out0_2.trans (Relation.ReflTransGen.single (P.adj valid 2))
theorem out0_4 : Relation.ReflTransGen R 0 4 :=
  out0_3.trans (Relation.ReflTransGen.single (P.adj valid 3))
theorem out0_5 : Relation.ReflTransGen R 0 5 :=
  out0_4.trans (Relation.ReflTransGen.single (P.adj valid 4))
theorem out0_6 : Relation.ReflTransGen R 0 6 :=
  out0_5.trans (Relation.ReflTransGen.single (P.adj valid 5))
theorem out0_7 : Relation.ReflTransGen R 0 7 :=
  out0_6.trans (Relation.ReflTransGen.single (P.adj valid 6))
theorem out5_8 : Relation.ReflTransGen R 8 8 := Relation.ReflTransGen.refl
theorem out5_9 : Relation.ReflTransGen R 8 9 :=
  out5_8.trans (Relation.ReflTransGen.single (P.adj valid 7))
theorem out5_10 : Relation.ReflTransGen R 8 10 :=
  out5_9.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem out5_11 : Relation.ReflTransGen R 8 11 :=
  out5_10.trans (Relation.ReflTransGen.single (P.adj valid 9))
theorem out5_12 : Relation.ReflTransGen R 8 12 :=
  out5_11.trans (Relation.ReflTransGen.single (P.adj valid 10))
theorem out5_13 : Relation.ReflTransGen R 8 13 :=
  out5_12.trans (Relation.ReflTransGen.single (P.adj valid 11))
theorem out5_14 : Relation.ReflTransGen R 8 14 :=
  out5_13.trans (Relation.ReflTransGen.single (P.adj valid 12))
theorem out5_15 : Relation.ReflTransGen R 8 15 :=
  out5_14.trans (Relation.ReflTransGen.single (P.adj valid 13))

theorem reach_in : ∀ v : Fin 16, ∃ i : Fin 10,
    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inl i))) v := by
  intro v
  fin_cases v
  · exact ⟨0, in0_0⟩
  · exact ⟨0, in0_1⟩
  · exact ⟨0, in0_2⟩
  · exact ⟨0, in0_3⟩
  · exact ⟨0, in0_4⟩
  · exact ⟨0, in0_5⟩
  · exact ⟨0, in0_6⟩
  · exact ⟨0, in0_7⟩
  · exact ⟨5, in5_8⟩
  · exact ⟨5, in5_9⟩
  · exact ⟨5, in5_10⟩
  · exact ⟨5, in5_11⟩
  · exact ⟨5, in5_12⟩
  · exact ⟨5, in5_13⟩
  · exact ⟨5, in5_14⟩
  · exact ⟨5, in5_15⟩

theorem reach_out : ∀ v : Fin 16, ∃ i : Fin 10,
    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inr i))) v := by
  intro v
  fin_cases v
  · exact ⟨0, out0_0⟩
  · exact ⟨0, out0_1⟩
  · exact ⟨0, out0_2⟩
  · exact ⟨0, out0_3⟩
  · exact ⟨0, out0_4⟩
  · exact ⟨0, out0_5⟩
  · exact ⟨0, out0_6⟩
  · exact ⟨0, out0_7⟩
  · exact ⟨5, out5_8⟩
  · exact ⟨5, out5_9⟩
  · exact ⟨5, out5_10⟩
  · exact ⟨5, out5_11⟩
  · exact ⟨5, out5_12⟩
  · exact ⟨5, out5_13⟩
  · exact ⟨5, out5_14⟩
  · exact ⟨5, out5_15⟩

theorem shapeW : SlabShapeW (P.toTangle valid) := ⟨two_darts, reach_in, reach_out⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair3
