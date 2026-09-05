import Mettapedia.GraphTheory.FourColor.RungThick1
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `RungThick1` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1

open Presented Pres

theorem two_darts : ∀ v : Fin 4, ∃ x x' : SlabDart (P.toTangle valid),
    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  intro v
  fin_cases v
  · exact ⟨Sum.inr (Sum.inl 0), Sum.inl (0, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (0, true), Sum.inl (1, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (1, true), Sum.inl (2, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 2), Sum.inl (2, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩

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

theorem up (v : Fin 4) : Relation.ReflTransGen R 0 v := by
  fin_cases v
  · exact up_0
  · exact up_1
  · exact up_2
  · exact up_3

theorem down (v : Fin 4) : Relation.ReflTransGen R v 0 := by
  fin_cases v
  · exact down_0
  · exact down_1
  · exact down_2
  · exact down_3

theorem connected (u v : Fin 4) : Relation.ReflTransGen R u v := (down u).trans (up v)

theorem shape : SlabShape (P.toTangle valid) := ⟨two_darts, connected⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungThick1
