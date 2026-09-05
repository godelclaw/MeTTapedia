import Mettapedia.GraphTheory.FourColor.RungPair4
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `RungPair4` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair4

open Presented Pres

theorem two_darts : ∀ v : Fin 20, ∃ x x' : SlabDart (P.toTangle valid),
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
  · exact ⟨Sum.inl (6, true), Sum.inl (7, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (7, true), Sum.inl (8, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 5), Sum.inl (8, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inr (Sum.inl 6), Sum.inl (9, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (9, true), Sum.inl (10, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (10, true), Sum.inl (11, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (11, true), Sum.inl (12, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (12, true), Sum.inl (13, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (13, true), Sum.inl (14, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (14, true), Sum.inl (15, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (15, true), Sum.inl (16, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (16, true), Sum.inl (17, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 11), Sum.inl (17, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩

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
theorem in0_8 : Relation.ReflTransGen R 0 8 :=
  in0_7.trans (Relation.ReflTransGen.single (P.adj valid 7))
theorem in0_9 : Relation.ReflTransGen R 0 9 :=
  in0_8.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem in6_10 : Relation.ReflTransGen R 10 10 := Relation.ReflTransGen.refl
theorem in6_11 : Relation.ReflTransGen R 10 11 :=
  in6_10.trans (Relation.ReflTransGen.single (P.adj valid 9))
theorem in6_12 : Relation.ReflTransGen R 10 12 :=
  in6_11.trans (Relation.ReflTransGen.single (P.adj valid 10))
theorem in6_13 : Relation.ReflTransGen R 10 13 :=
  in6_12.trans (Relation.ReflTransGen.single (P.adj valid 11))
theorem in6_14 : Relation.ReflTransGen R 10 14 :=
  in6_13.trans (Relation.ReflTransGen.single (P.adj valid 12))
theorem in6_15 : Relation.ReflTransGen R 10 15 :=
  in6_14.trans (Relation.ReflTransGen.single (P.adj valid 13))
theorem in6_16 : Relation.ReflTransGen R 10 16 :=
  in6_15.trans (Relation.ReflTransGen.single (P.adj valid 14))
theorem in6_17 : Relation.ReflTransGen R 10 17 :=
  in6_16.trans (Relation.ReflTransGen.single (P.adj valid 15))
theorem in6_18 : Relation.ReflTransGen R 10 18 :=
  in6_17.trans (Relation.ReflTransGen.single (P.adj valid 16))
theorem in6_19 : Relation.ReflTransGen R 10 19 :=
  in6_18.trans (Relation.ReflTransGen.single (P.adj valid 17))
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
theorem out0_8 : Relation.ReflTransGen R 0 8 :=
  out0_7.trans (Relation.ReflTransGen.single (P.adj valid 7))
theorem out0_9 : Relation.ReflTransGen R 0 9 :=
  out0_8.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem out6_10 : Relation.ReflTransGen R 10 10 := Relation.ReflTransGen.refl
theorem out6_11 : Relation.ReflTransGen R 10 11 :=
  out6_10.trans (Relation.ReflTransGen.single (P.adj valid 9))
theorem out6_12 : Relation.ReflTransGen R 10 12 :=
  out6_11.trans (Relation.ReflTransGen.single (P.adj valid 10))
theorem out6_13 : Relation.ReflTransGen R 10 13 :=
  out6_12.trans (Relation.ReflTransGen.single (P.adj valid 11))
theorem out6_14 : Relation.ReflTransGen R 10 14 :=
  out6_13.trans (Relation.ReflTransGen.single (P.adj valid 12))
theorem out6_15 : Relation.ReflTransGen R 10 15 :=
  out6_14.trans (Relation.ReflTransGen.single (P.adj valid 13))
theorem out6_16 : Relation.ReflTransGen R 10 16 :=
  out6_15.trans (Relation.ReflTransGen.single (P.adj valid 14))
theorem out6_17 : Relation.ReflTransGen R 10 17 :=
  out6_16.trans (Relation.ReflTransGen.single (P.adj valid 15))
theorem out6_18 : Relation.ReflTransGen R 10 18 :=
  out6_17.trans (Relation.ReflTransGen.single (P.adj valid 16))
theorem out6_19 : Relation.ReflTransGen R 10 19 :=
  out6_18.trans (Relation.ReflTransGen.single (P.adj valid 17))

theorem reach_in : ∀ v : Fin 20, ∃ i : Fin 12,
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
  · exact ⟨0, in0_8⟩
  · exact ⟨0, in0_9⟩
  · exact ⟨6, in6_10⟩
  · exact ⟨6, in6_11⟩
  · exact ⟨6, in6_12⟩
  · exact ⟨6, in6_13⟩
  · exact ⟨6, in6_14⟩
  · exact ⟨6, in6_15⟩
  · exact ⟨6, in6_16⟩
  · exact ⟨6, in6_17⟩
  · exact ⟨6, in6_18⟩
  · exact ⟨6, in6_19⟩

theorem reach_out : ∀ v : Fin 20, ∃ i : Fin 12,
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
  · exact ⟨0, out0_8⟩
  · exact ⟨0, out0_9⟩
  · exact ⟨6, out6_10⟩
  · exact ⟨6, out6_11⟩
  · exact ⟨6, out6_12⟩
  · exact ⟨6, out6_13⟩
  · exact ⟨6, out6_14⟩
  · exact ⟨6, out6_15⟩
  · exact ⟨6, out6_16⟩
  · exact ⟨6, out6_17⟩
  · exact ⟨6, out6_18⟩
  · exact ⟨6, out6_19⟩

theorem shapeW : SlabShapeW (P.toTangle valid) := ⟨two_darts, reach_in, reach_out⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair4
