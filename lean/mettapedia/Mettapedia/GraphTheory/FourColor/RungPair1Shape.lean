import Mettapedia.GraphTheory.FourColor.RungPair1
import Mettapedia.GraphTheory.FourColor.PresentedShape

/-! `RungPair1` is a slab shape: two edge-darts per vertex and a connected interior. -/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair1

open Presented Pres

theorem two_darts : ∀ v : Fin 8, ∃ x x' : SlabDart (P.toTangle valid),
    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x' := by
  intro v
  fin_cases v
  · exact ⟨Sum.inr (Sum.inl 0), Sum.inl (0, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (0, true), Sum.inl (1, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (1, true), Sum.inl (2, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 2), Sum.inl (2, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inr (Sum.inl 3), Sum.inl (3, false), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩
  · exact ⟨Sum.inl (3, true), Sum.inl (4, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inl (4, true), Sum.inl (5, false), rfl, rfl, P.notOut_inl valid _, P.notOut_inl valid _, P.distinctEdge_inl valid (by decide)⟩
  · exact ⟨Sum.inr (Sum.inl 5), Sum.inl (5, true), rfl, rfl, P.notOut_inp valid _, P.notOut_inl valid _, P.distinctEdge_inp_inl valid _ _⟩

abbrev R := InteriorAdj (P.toTangle valid)

theorem in0_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem in0_1 : Relation.ReflTransGen R 0 1 :=
  in0_0.trans (Relation.ReflTransGen.single (P.adj valid 0))
theorem in0_2 : Relation.ReflTransGen R 0 2 :=
  in0_1.trans (Relation.ReflTransGen.single (P.adj valid 1))
theorem in0_3 : Relation.ReflTransGen R 0 3 :=
  in0_2.trans (Relation.ReflTransGen.single (P.adj valid 2))
theorem in3_4 : Relation.ReflTransGen R 4 4 := Relation.ReflTransGen.refl
theorem in3_5 : Relation.ReflTransGen R 4 5 :=
  in3_4.trans (Relation.ReflTransGen.single (P.adj valid 3))
theorem in3_6 : Relation.ReflTransGen R 4 6 :=
  in3_5.trans (Relation.ReflTransGen.single (P.adj valid 4))
theorem in3_7 : Relation.ReflTransGen R 4 7 :=
  in3_6.trans (Relation.ReflTransGen.single (P.adj valid 5))
theorem out0_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl
theorem out0_1 : Relation.ReflTransGen R 0 1 :=
  out0_0.trans (Relation.ReflTransGen.single (P.adj valid 0))
theorem out0_2 : Relation.ReflTransGen R 0 2 :=
  out0_1.trans (Relation.ReflTransGen.single (P.adj valid 1))
theorem out0_3 : Relation.ReflTransGen R 0 3 :=
  out0_2.trans (Relation.ReflTransGen.single (P.adj valid 2))
theorem out3_4 : Relation.ReflTransGen R 4 4 := Relation.ReflTransGen.refl
theorem out3_5 : Relation.ReflTransGen R 4 5 :=
  out3_4.trans (Relation.ReflTransGen.single (P.adj valid 3))
theorem out3_6 : Relation.ReflTransGen R 4 6 :=
  out3_5.trans (Relation.ReflTransGen.single (P.adj valid 4))
theorem out3_7 : Relation.ReflTransGen R 4 7 :=
  out3_6.trans (Relation.ReflTransGen.single (P.adj valid 5))

theorem reach_in : ∀ v : Fin 8, ∃ i : Fin 6,
    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inl i))) v := by
  intro v
  fin_cases v
  · exact ⟨0, in0_0⟩
  · exact ⟨0, in0_1⟩
  · exact ⟨0, in0_2⟩
  · exact ⟨0, in0_3⟩
  · exact ⟨3, in3_4⟩
  · exact ⟨3, in3_5⟩
  · exact ⟨3, in3_6⟩
  · exact ⟨3, in3_7⟩

theorem reach_out : ∀ v : Fin 8, ∃ i : Fin 6,
    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inr i))) v := by
  intro v
  fin_cases v
  · exact ⟨0, out0_0⟩
  · exact ⟨0, out0_1⟩
  · exact ⟨0, out0_2⟩
  · exact ⟨0, out0_3⟩
  · exact ⟨3, out3_4⟩
  · exact ⟨3, out3_5⟩
  · exact ⟨3, out3_6⟩
  · exact ⟨3, out3_7⟩

theorem shapeW : SlabShapeW (P.toTangle valid) := ⟨two_darts, reach_in, reach_out⟩

end Mettapedia.GraphTheory.FourColor.TubeSlab.RungPair1
