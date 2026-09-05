import Mettapedia.GraphTheory.FourColor.PentaCell
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `PentaCell` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.PentaCell

open Presented Pres

theorem two_darts : ∀ v : Fin 24, ∃ x x' : SlabDart (P.toTangle valid),
    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  intro v
  fin_cases v
  · exact ⟨Sum.inl (0, false), Sum.inl (1, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (2, false), Sum.inl (3, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (2, true), Sum.inl (4, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (5, false), Sum.inl (6, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (5, true), Sum.inl (7, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (0, true), Sum.inl (8, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (8, true), Sum.inl (9, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (1, true), Sum.inl (13, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (3, true), Sum.inl (14, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (4, true), Sum.inl (20, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (6, true), Sum.inl (21, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (7, true), Sum.inl (10, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (9, true), Sum.inl (11, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (13, true), Sum.inl (15, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (17, true), Sum.inl (18, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (20, true), Sum.inl (22, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (24, true), Sum.inl (25, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (27, true), Sum.inl (28, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (11, true), Sum.inl (28, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (12, true), Sum.inl (15, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (16, true), Sum.inl (18, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (19, true), Sum.inl (22, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (23, true), Sum.inl (25, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (26, true), Sum.inl (29, true), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩

abbrev R := InteriorAdj (P.toTangle valid)

theorem up_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem down_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem up_5 : Relation.ReflTransGen R 0 5 :=
  up_0.trans (Relation.ReflTransGen.single (P.adj valid 0))
theorem down_5 : Relation.ReflTransGen R 5 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 0)).trans down_0
theorem up_7 : Relation.ReflTransGen R 0 7 :=
  up_0.trans (Relation.ReflTransGen.single (P.adj valid 1))
theorem down_7 : Relation.ReflTransGen R 7 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 1)).trans down_0
theorem up_6 : Relation.ReflTransGen R 0 6 :=
  up_5.trans (Relation.ReflTransGen.single (P.adj valid 8))
theorem down_6 : Relation.ReflTransGen R 6 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 8)).trans down_5
theorem up_13 : Relation.ReflTransGen R 0 13 :=
  up_7.trans (Relation.ReflTransGen.single (P.adj valid 13))
theorem down_13 : Relation.ReflTransGen R 13 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 13)).trans down_7
theorem up_8 : Relation.ReflTransGen R 0 8 :=
  up_7.trans (Relation.ReflTransGen.single (P.adj valid 14))
theorem down_8 : Relation.ReflTransGen R 8 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 14)).trans down_7
theorem up_12 : Relation.ReflTransGen R 0 12 :=
  up_6.trans (Relation.ReflTransGen.single (P.adj valid 9))
theorem down_12 : Relation.ReflTransGen R 12 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 9)).trans down_6
theorem up_11 : Relation.ReflTransGen R 0 11 :=
  up_6.trans (Relation.ReflTransGen.single (P.adj valid 10))
theorem down_11 : Relation.ReflTransGen R 11 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 10)).trans down_6
theorem up_19 : Relation.ReflTransGen R 0 19 :=
  up_13.trans (Relation.ReflTransGen.single (P.adj valid 15))
theorem down_19 : Relation.ReflTransGen R 19 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 15)).trans down_13
theorem up_20 : Relation.ReflTransGen R 0 20 :=
  up_13.trans (Relation.ReflTransGen.single (P.adj valid 16))
theorem down_20 : Relation.ReflTransGen R 20 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 16)).trans down_13
theorem up_1 : Relation.ReflTransGen R 0 1 :=
  up_8.trans (Relation.ReflTransGen.single (P.adj' valid 3))
theorem down_1 : Relation.ReflTransGen R 1 0 :=
  (Relation.ReflTransGen.single (P.adj valid 3)).trans down_8
theorem up_14 : Relation.ReflTransGen R 0 14 :=
  up_8.trans (Relation.ReflTransGen.single (P.adj valid 17))
theorem down_14 : Relation.ReflTransGen R 14 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 17)).trans down_8
theorem up_18 : Relation.ReflTransGen R 0 18 :=
  up_12.trans (Relation.ReflTransGen.single (P.adj valid 11))
theorem down_18 : Relation.ReflTransGen R 18 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 11)).trans down_12
theorem up_4 : Relation.ReflTransGen R 0 4 :=
  up_11.trans (Relation.ReflTransGen.single (P.adj' valid 7))
theorem down_4 : Relation.ReflTransGen R 4 0 :=
  (Relation.ReflTransGen.single (P.adj valid 7)).trans down_11
theorem up_17 : Relation.ReflTransGen R 0 17 :=
  up_11.trans (Relation.ReflTransGen.single (P.adj valid 27))
theorem down_17 : Relation.ReflTransGen R 17 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 27)).trans down_11
theorem up_2 : Relation.ReflTransGen R 0 2 :=
  up_1.trans (Relation.ReflTransGen.single (P.adj valid 2))
theorem down_2 : Relation.ReflTransGen R 2 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 2)).trans down_1
theorem up_21 : Relation.ReflTransGen R 0 21 :=
  up_14.trans (Relation.ReflTransGen.single (P.adj valid 19))
theorem down_21 : Relation.ReflTransGen R 21 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 19)).trans down_14
theorem up_3 : Relation.ReflTransGen R 0 3 :=
  up_4.trans (Relation.ReflTransGen.single (P.adj' valid 5))
theorem down_3 : Relation.ReflTransGen R 3 0 :=
  (Relation.ReflTransGen.single (P.adj valid 5)).trans down_4
theorem up_23 : Relation.ReflTransGen R 0 23 :=
  up_17.trans (Relation.ReflTransGen.single (P.adj valid 29))
theorem down_23 : Relation.ReflTransGen R 23 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 29)).trans down_17
theorem up_9 : Relation.ReflTransGen R 0 9 :=
  up_2.trans (Relation.ReflTransGen.single (P.adj valid 4))
theorem down_9 : Relation.ReflTransGen R 9 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 4)).trans down_2
theorem up_15 : Relation.ReflTransGen R 0 15 :=
  up_21.trans (Relation.ReflTransGen.single (P.adj' valid 22))
theorem down_15 : Relation.ReflTransGen R 15 0 :=
  (Relation.ReflTransGen.single (P.adj valid 22)).trans down_21
theorem up_10 : Relation.ReflTransGen R 0 10 :=
  up_3.trans (Relation.ReflTransGen.single (P.adj valid 6))
theorem down_10 : Relation.ReflTransGen R 10 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 6)).trans down_3
theorem up_16 : Relation.ReflTransGen R 0 16 :=
  up_23.trans (Relation.ReflTransGen.single (P.adj' valid 26))
theorem down_16 : Relation.ReflTransGen R 16 0 :=
  (Relation.ReflTransGen.single (P.adj valid 26)).trans down_23
theorem up_22 : Relation.ReflTransGen R 0 22 :=
  up_15.trans (Relation.ReflTransGen.single (P.adj valid 23))
theorem down_22 : Relation.ReflTransGen R 22 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 23)).trans down_15

theorem up (v : Fin 24) : Relation.ReflTransGen R 0 v := by
  fin_cases v
  · exact up_0
  · exact up_1
  · exact up_2
  · exact up_3
  · exact up_4
  · exact up_5
  · exact up_6
  · exact up_7
  · exact up_8
  · exact up_9
  · exact up_10
  · exact up_11
  · exact up_12
  · exact up_13
  · exact up_14
  · exact up_15
  · exact up_16
  · exact up_17
  · exact up_18
  · exact up_19
  · exact up_20
  · exact up_21
  · exact up_22
  · exact up_23

theorem down (v : Fin 24) : Relation.ReflTransGen R v 0 := by
  fin_cases v
  · exact down_0
  · exact down_1
  · exact down_2
  · exact down_3
  · exact down_4
  · exact down_5
  · exact down_6
  · exact down_7
  · exact down_8
  · exact down_9
  · exact down_10
  · exact down_11
  · exact down_12
  · exact down_13
  · exact down_14
  · exact down_15
  · exact down_16
  · exact down_17
  · exact down_18
  · exact down_19
  · exact down_20
  · exact down_21
  · exact down_22
  · exact down_23

theorem connected (u v : Fin 24) : Relation.ReflTransGen R u v := (down u).trans (up v)

theorem shape : SlabShape (P.toTangle valid) := ⟨two_darts, connected⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.PentaCell
