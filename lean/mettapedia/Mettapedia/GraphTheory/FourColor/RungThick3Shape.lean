import Mettapedia.GraphTheory.FourColor.RungThick3
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `RungThick3` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick3

open Presented Pres

theorem two_darts : ∀ v : Fin 8, ∃ x x' : SlabDart (P.toTangle valid),
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

abbrev R := InteriorAdj (P.toTangle valid)

theorem up_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem down_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem up_1 : Relation.ReflTransGen R 0 1 :=
  up_0.trans (Relation.ReflTransGen.single (P.adj valid 0))
theorem down_1 : Relation.ReflTransGen R 1 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 0)).trans down_0
theorem up_2 : Relation.ReflTransGen R 0 2 :=
  up_1.trans (Relation.ReflTransGen.single (P.adj valid 1))
theorem down_2 : Relation.ReflTransGen R 2 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 1)).trans down_1
theorem up_3 : Relation.ReflTransGen R 0 3 :=
  up_2.trans (Relation.ReflTransGen.single (P.adj valid 2))
theorem down_3 : Relation.ReflTransGen R 3 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 2)).trans down_2
theorem up_4 : Relation.ReflTransGen R 0 4 :=
  up_3.trans (Relation.ReflTransGen.single (P.adj valid 3))
theorem down_4 : Relation.ReflTransGen R 4 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 3)).trans down_3
theorem up_5 : Relation.ReflTransGen R 0 5 :=
  up_4.trans (Relation.ReflTransGen.single (P.adj valid 4))
theorem down_5 : Relation.ReflTransGen R 5 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 4)).trans down_4
theorem up_6 : Relation.ReflTransGen R 0 6 :=
  up_5.trans (Relation.ReflTransGen.single (P.adj valid 5))
theorem down_6 : Relation.ReflTransGen R 6 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 5)).trans down_5
theorem up_7 : Relation.ReflTransGen R 0 7 :=
  up_6.trans (Relation.ReflTransGen.single (P.adj valid 6))
theorem down_7 : Relation.ReflTransGen R 7 0 :=
  (Relation.ReflTransGen.single (P.adj' valid 6)).trans down_6

theorem up (v : Fin 8) : Relation.ReflTransGen R 0 v := by
  fin_cases v
  · exact up_0
  · exact up_1
  · exact up_2
  · exact up_3
  · exact up_4
  · exact up_5
  · exact up_6
  · exact up_7

theorem down (v : Fin 8) : Relation.ReflTransGen R v 0 := by
  fin_cases v
  · exact down_0
  · exact down_1
  · exact down_2
  · exact down_3
  · exact down_4
  · exact down_5
  · exact down_6
  · exact down_7

theorem connected (u v : Fin 8) : Relation.ReflTransGen R u v := (down u).trans (up v)

theorem shape : SlabShape (P.toTangle valid) := ⟨two_darts, connected⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick3
