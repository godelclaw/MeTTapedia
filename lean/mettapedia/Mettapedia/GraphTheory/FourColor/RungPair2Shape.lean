import Mettapedia.GraphTheory.FourColor.RungPair2
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `RungPair2` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair2

open Presented Pres

theorem two_darts : ∀ v : Fin 12, ∃ x x' : SlabDart (P.toTangle valid),
    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  intro v
  fin_cases v
  · exact ⟨Sum.inr (Sum.inl 0), Sum.inl (0, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (0, true), Sum.inl (1, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (1, true), Sum.inl (2, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (2, true), Sum.inl (3, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (3, true), Sum.inl (4, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 3), Sum.inl (4, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inr (Sum.inl 4), Sum.inl (5, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (5, true), Sum.inl (6, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (6, true), Sum.inl (7, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (7, true), Sum.inl (8, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (8, true), Sum.inl (9, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 7), Sum.inl (9, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩

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
theorem in4_6 : Relation.ReflTransGen R 6 6 := Relation.ReflTransGen.refl
theorem in4_7 : Relation.ReflTransGen R 6 7 :=
  in4_6.trans (Relation.ReflTransGen.single (P.adj valid 5))
theorem in4_8 : Relation.ReflTransGen R 6 8 :=
  in4_7.trans (Relation.ReflTransGen.single (P.adj valid 6))
theorem in4_9 : Relation.ReflTransGen R 6 9 :=
  in4_8.trans (Relation.ReflTransGen.single (P.adj valid 7))
theorem in4_10 : Relation.ReflTransGen R 6 10 :=
  in4_9.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem in4_11 : Relation.ReflTransGen R 6 11 :=
  in4_10.trans (Relation.ReflTransGen.single (P.adj valid 9))
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
theorem out4_6 : Relation.ReflTransGen R 6 6 := Relation.ReflTransGen.refl
theorem out4_7 : Relation.ReflTransGen R 6 7 :=
  out4_6.trans (Relation.ReflTransGen.single (P.adj valid 5))
theorem out4_8 : Relation.ReflTransGen R 6 8 :=
  out4_7.trans (Relation.ReflTransGen.single (P.adj valid 6))
theorem out4_9 : Relation.ReflTransGen R 6 9 :=
  out4_8.trans (Relation.ReflTransGen.single (P.adj valid 7))
theorem out4_10 : Relation.ReflTransGen R 6 10 :=
  out4_9.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem out4_11 : Relation.ReflTransGen R 6 11 :=
  out4_10.trans (Relation.ReflTransGen.single (P.adj valid 9))

theorem reach_in : ∀ v : Fin 12, ∃ i : Fin 8,
    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inl i))) v := by
  intro v
  fin_cases v
  · exact ⟨0, in0_0⟩
  · exact ⟨0, in0_1⟩
  · exact ⟨0, in0_2⟩
  · exact ⟨0, in0_3⟩
  · exact ⟨0, in0_4⟩
  · exact ⟨0, in0_5⟩
  · exact ⟨4, in4_6⟩
  · exact ⟨4, in4_7⟩
  · exact ⟨4, in4_8⟩
  · exact ⟨4, in4_9⟩
  · exact ⟨4, in4_10⟩
  · exact ⟨4, in4_11⟩

theorem reach_out : ∀ v : Fin 12, ∃ i : Fin 8,
    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inr i))) v := by
  intro v
  fin_cases v
  · exact ⟨0, out0_0⟩
  · exact ⟨0, out0_1⟩
  · exact ⟨0, out0_2⟩
  · exact ⟨0, out0_3⟩
  · exact ⟨0, out0_4⟩
  · exact ⟨0, out0_5⟩
  · exact ⟨4, out4_6⟩
  · exact ⟨4, out4_7⟩
  · exact ⟨4, out4_8⟩
  · exact ⟨4, out4_9⟩
  · exact ⟨4, out4_10⟩
  · exact ⟨4, out4_11⟩

theorem shapeW : SlabShapeW (P.toTangle valid) := ⟨two_darts, reach_in, reach_out⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair2
