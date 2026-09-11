import Mettapedia.GraphTheory.FourColor.VertexTransfer
import Mathlib.Data.Fintype.Inv

/-!
# Exact port partitions of finite vertex codes

A valid code consumes some old ports at a cyclically ordered cubic star,
retains every other old port exactly once, and creates the remaining
star ports on the new boundary. The three coordinate equivalences below
construct this partition; no geometric realization is assumed as a field.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodePartition

open TubeSlab.VertexTransfer

variable {l r : ℕ} (a : Code l r)

/-- Complete incidence validity, independent of any colouring witness. -/
def Valid : Prop :=
  Function.Injective a.1 ∧
  (∀ j, a.2 j = none ↔ ∃ t, a.1 t = Sum.inr j) ∧
  (∀ i, (∃ t, a.1 t = Sum.inl i) ↔ ∀ j, a.2 j ≠ some i) ∧
  ∀ j k i, a.2 j = some i → a.2 k = some i → j = k

instance : Decidable (Valid a) := by unfold Valid; infer_instance

abbrev Retained := {p : Fin r × Fin l // a.2 p.1 = some p.2}
abbrev Consumed := {i : Fin l // ∃ t, a.1 t = Sum.inl i}
abbrev Fresh := {j : Fin r // a.2 j = none}

instance retainedFintype : Fintype (Retained a) := Subtype.fintype _
instance consumedFintype : Fintype (Consumed a) := Subtype.fintype _
instance freshFintype : Fintype (Fresh a) := Subtype.fintype _

def input : Retained a ⊕ Consumed a → Fin l :=
  Sum.elim (fun p => p.1.2) Subtype.val

def output : Retained a ⊕ Fresh a → Fin r :=
  Sum.elim (fun p => p.1.1) Subtype.val

def starVal : Consumed a ⊕ Fresh a → Fin l ⊕ Fin r :=
  Sum.map Subtype.val Subtype.val

theorem input_bijective (h : Valid a) : Function.Bijective (input a) := by
  constructor
  · rintro (p | i) (q | j) he <;> dsimp [input] at he
    · apply congrArg Sum.inl
      apply Subtype.ext
      exact Prod.ext (h.2.2.2 _ _ _ p.2 (he.symm ▸ q.2)) he
    · exact False.elim (((h.2.2.1 j).mp j.2 p.1.1) (he ▸ p.2))
    · exact False.elim (((h.2.2.1 i).mp i.2 q.1.1) (he.symm ▸ q.2))
    · exact congrArg Sum.inr (Subtype.ext he)
  · intro i
    by_cases hi : ∃ t, a.1 t = Sum.inl i
    · exact ⟨.inr ⟨i, hi⟩, rfl⟩
    · have hw : ∃ j, a.2 j = some i := by
        by_contra hn
        exact hi ((h.2.2.1 i).mpr (by simpa using hn))
      obtain ⟨j, hj⟩ := hw
      exact ⟨.inl ⟨(j, i), hj⟩, rfl⟩

theorem output_bijective : Function.Bijective (output a) := by
  constructor
  · rintro (p | i) (q | j) he <;> dsimp [output] at he
    · apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext he
      exact Option.some.inj (p.2.symm.trans ((congrArg a.2 he).trans q.2))
    · have := (congrArg a.2 he).trans j.2
      rw [p.2] at this
      cases this
    · have := (congrArg a.2 he).trans q.2
      rw [i.2] at this
      cases this
    · exact congrArg Sum.inr (Subtype.ext he)
  · intro j
    cases hj : a.2 j with
    | none => exact ⟨.inr ⟨j, hj⟩, rfl⟩
    | some i => exact ⟨.inl ⟨(j, i), hj⟩, rfl⟩

def starMap (h : Valid a) (t : Fin 3) : Consumed a ⊕ Fresh a :=
  match ht : a.1 t with
  | .inl i => .inl ⟨i, t, ht⟩
  | .inr j => .inr ⟨j, (h.2.1 j).mpr ⟨t, ht⟩⟩

theorem starMap_spec (h : Valid a) (t : Fin 3) :
    starVal a (starMap a h t) = a.1 t := by
  unfold starMap
  split <;> rename_i _ ht <;> exact ht.symm

theorem starVal_injective : Function.Injective (starVal a) := by
  rintro (i | j) (i' | j') he <;> simp only [starVal, Sum.map_inl, Sum.map_inr] at he
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj he))
  · cases he
  · cases he
  · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj he))

theorem starMap_bijective (h : Valid a) : Function.Bijective (starMap a h) := by
  constructor
  · intro s t he
    apply h.1
    simpa only [starMap_spec] using congrArg (starVal a) he
  · rintro (i | j)
    · obtain ⟨t, ht⟩ := i.2
      refine ⟨t, starVal_injective a ?_⟩
      rw [starMap_spec]
      exact ht
    · obtain ⟨t, ht⟩ := (h.2.1 j).mp j.2
      refine ⟨t, starVal_injective a ?_⟩
      rw [starMap_spec]
      exact ht

def finiteEquiv {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (hf : Function.Bijective f) : A ≃ B where
  toFun := f
  invFun := Fintype.bijInv hf
  left_inv := Fintype.leftInverse_bijInv hf
  right_inv := Fintype.rightInverse_bijInv hf

def inputEquiv (h : Valid a) : Retained a ⊕ Consumed a ≃ Fin l :=
  finiteEquiv (input a) (input_bijective a h)

def outputEquiv : Retained a ⊕ Fresh a ≃ Fin r :=
  finiteEquiv (output a) (output_bijective a)

/-- The code's ordered slots are interpreted as the star's cyclic order. -/
def starOrder (h : Valid a) : Fin 3 ≃ Consumed a ⊕ Fresh a :=
  finiteEquiv (starMap a h) (starMap_bijective a h)

theorem starOrder_spec (h : Valid a) (t : Fin 3) :
    starVal a (starOrder a h t) = a.1 t := starMap_spec a h t

theorem arity (h : Valid a) :
    l + 3 = r + 2 * Fintype.card (Consumed a) := by
  have hi := Fintype.card_congr (inputEquiv a h)
  have ho := Fintype.card_congr (outputEquiv a)
  have hs := Fintype.card_congr (starOrder a h)
  simp only [Fintype.card_sum, Fintype.card_fin] at hi ho hs
  omega

end Mettapedia.GraphTheory.FourColor.VertexCodePartition
