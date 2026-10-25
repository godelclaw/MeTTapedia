import Mettapedia.TypeTheory.IndexedContainer

/-!
# Induction-hypothesis bundles for registered containers

A nested recursive field contributes one induction hypothesis at every
container position, not one hypothesis for the field as a whole.  This module
states that requirement independently of any guest syntax and gives the
ordinary list implementation as a dependent list of hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedContainer

universe uOutput uElement uMotive uShape uPosition

/-- One motive witness for every element of a list, in source order. -/
inductive ListAll {Element : Type uElement} (motive : Element → Type uMotive) :
    List Element → Type (max uElement uMotive) where
  | nil : ListAll motive []
  | cons {head : Element} {tail : List Element} :
      motive head → ListAll motive tail → ListAll motive (head :: tail)

/-- A guest representation of the exact position-indexed induction
hypotheses of a container value. -/
structure InductionBundle
    {Output : Type uOutput}
    (container : IndexedContainer.{uOutput, uShape, uPosition} Output)
    (Element : Type uElement) (motive : Element → Type uMotive) where
  Bundle : {output : Output} →
    container.Extension Element output →
      Type (max uOutput uElement uMotive uShape uPosition)
  exact : ∀ {output : Output}
    (value : container.Extension Element output), Bundle value ≃
    (∀ position : container.Position value.1, motive (value.2 position))

/-- A dependent list of witnesses is exactly a witness at every finite list
position. -/
def listAllEquiv {Element : Type uElement} (motive : Element → Type uMotive) :
    ∀ (values : List Element),
      ListAll motive values ≃
        (∀ position : Fin values.length, motive (values.get position))
  | [] =>
      { toFun := fun _ position => Fin.elim0 position
        invFun := fun _ => .nil
        left_inv := fun value => by cases value; rfl
        right_inv := fun function => by funext position; exact Fin.elim0 position }
  | head :: tail =>
      { toFun := fun hypotheses position => by
          cases hypotheses with
          | cons headHypothesis tailHypotheses =>
              refine Fin.cases ?_ (fun prior => ?_) position
              · simpa using headHypothesis
              · simpa using (listAllEquiv motive tail).toFun tailHypotheses prior
        invFun := fun hypotheses =>
          ListAll.cons (by simpa using hypotheses ⟨0, by simp⟩)
            ((listAllEquiv motive tail).invFun (fun position => by
              simpa using hypotheses position.succ))
        left_inv := by
          intro hypotheses
          cases hypotheses with
          | cons headHypothesis tailHypotheses =>
              change ListAll.cons headHypothesis
                ((listAllEquiv motive tail).invFun
                  ((listAllEquiv motive tail).toFun tailHypotheses)) =
                    ListAll.cons headHypothesis tailHypotheses
              rw [(listAllEquiv motive tail).left_inv tailHypotheses]
        right_inv := by
          intro hypotheses
          funext position
          refine Fin.cases ?_ (fun prior => ?_) position
          · rfl
          · have restored := (listAllEquiv motive tail).apply_symm_apply
                (fun position : Fin tail.length => hypotheses position.succ)
            exact congrFun restored prior }

/-- Lookup retains the actual witness when a list and its evidence spine
are transported together, with the same underlying position. -/
theorem listAllEquiv_heq {Element : Type uElement} {motive : Element → Type uMotive}
    {first second : List Element} (same : first = second)
    (left : ListAll motive first) (right : ListAll motive second) (aligned : HEq left right)
    (firstPosition : Fin first.length) (secondPosition : Fin second.length)
    (positionSame : firstPosition.val = secondPosition.val) :
    HEq (listAllEquiv motive first left firstPosition)
      (listAllEquiv motive second right secondPosition) := by
  cases same
  cases aligned
  have positions : firstPosition = secondPosition := Fin.ext positionSame
  subst secondPosition
  rfl

/-- Lists implement the registered-container induction bundle by storing one
hypothesis per source element. -/
noncomputable def listInductionBundle {Element : Type uElement}
    (motive : Element → Type uMotive) :
    InductionBundle Examples.list Element motive where
  Bundle value := ListAll motive (List.ofFn value.2)
  exact value := by
    rcases value with ⟨shape, values⟩
    let lengthEq : (List.ofFn values).length = shape := List.length_ofFn
    let positions : Fin (List.ofFn values).length ≃ Fin shape :=
      { toFun := Fin.cast lengthEq
        invFun := Fin.cast lengthEq.symm
        left_inv := fun position => Fin.ext rfl
        right_inv := fun position => Fin.ext rfl }
    exact (listAllEquiv motive (List.ofFn values)).trans
      (Equiv.piCongr positions fun position =>
        Equiv.cast (congrArg motive
          ((List.get_ofFn values position).trans
            (congrArg values (Fin.ext rfl)))))

/-- The registered List bundle's exactness map and direct list lookup
preserve the same witness term, including proof-relevant witnesses. -/
theorem listInductionBundle_exact_cast {Element : Type uElement} (motive : Element → Type uMotive)
    (values : List Element) (hypotheses : ListAll motive values) (position : Fin values.length) :
    (listInductionBundle motive).exact (output := ()) ⟨values.length, values.get⟩
        (Equiv.cast (congrArg (ListAll motive) (List.ofFn_get values).symm) hypotheses) position =
      listAllEquiv motive values hypotheses position := by
  apply eq_of_heq
  let lengthEq : (List.ofFn values.get).length = values.length := List.length_ofFn
  let positions : Fin (List.ofFn values.get).length ≃ Fin values.length :=
    { toFun := Fin.cast lengthEq
      invFun := Fin.cast lengthEq.symm
      left_inv := fun index => Fin.ext rfl
      right_inv := fun index => Fin.ext rfl }
  let sourcePosition : Fin (List.ofFn values.get).length := Fin.cast lengthEq.symm position
  let valueEq (index : Fin (List.ofFn values.get).length) :
      (List.ofFn values.get).get index = values.get (positions index) :=
    (List.get_ofFn values.get index).trans (congrArg values.get (Fin.ext rfl))
  let fibres (index : Fin (List.ofFn values.get).length) := Equiv.cast (congrArg motive (valueEq index))
  let sourceBundle : ListAll motive (List.ofFn values.get) :=
    cast (congrArg (ListAll motive) (List.ofFn_get values).symm) hypotheses
  change HEq ((Equiv.piCongr
    (W := fun index : Fin (List.ofFn values.get).length => motive ((List.ofFn values.get).get index))
    (Z := fun index : Fin values.length => motive (values.get index)) positions fibres)
    (listAllEquiv motive (List.ofFn values.get) sourceBundle) (positions sourcePosition))
    (listAllEquiv motive values hypotheses position)
  have computed := Equiv.piCongr_apply_apply
    (W := fun index : Fin (List.ofFn values.get).length => motive ((List.ofFn values.get).get index))
    (Z := fun index : Fin values.length => motive (values.get index)) positions fibres
    (listAllEquiv motive (List.ofFn values.get) sourceBundle) sourcePosition
  apply (heq_of_eq computed).trans
  exact (cast_heq (congrArg motive (valueEq sourcePosition)) _).trans
    (listAllEquiv_heq (List.ofFn_get values) sourceBundle hypotheses
      (cast_heq _ hypotheses) sourcePosition position rfl)

/-- Vectors retain their output length. Their bundle is represented by a
dependent list in position order, then identified with exactly the `Fin n`
positions selected by the vector output index. -/
noncomputable def vectorInductionBundle {Element : Type uElement}
    (motive : Element → Type uMotive) :
    InductionBundle Examples.vector Element motive where
  Bundle value := ListAll motive (List.ofFn value.2)
  exact value := by
    rcases value with ⟨shape, values⟩
    cases shape
    let lengthEq : (List.ofFn values).length = _ := List.length_ofFn
    let positions : Fin (List.ofFn values).length ≃ Fin _ :=
      { toFun := Fin.cast lengthEq
        invFun := Fin.cast lengthEq.symm
        left_inv := fun position => Fin.ext rfl
        right_inv := fun position => Fin.ext rfl }
    exact (listAllEquiv motive (List.ofFn values)).trans
      (Equiv.piCongr positions fun position =>
        Equiv.cast (congrArg motive
          ((List.get_ofFn values position).trans
            (congrArg values (Fin.ext rfl)))))

def vectorShape (length : Nat) : Examples.vector.Shape length := ()

noncomputable instance vectorPositionFintype (length : Nat) :
    Fintype (Examples.vector.Position (vectorShape length)) :=
  Examples.vectorFinitary.positionFintype (vectorShape length)

theorem vector_position_card (length : Nat) :
    Fintype.card (Examples.vector.Position (vectorShape length)) = length := by
  change Fintype.card (Fin length) = length
  simp

/-- Erasing the vector output index would identify genuinely different
recursive-position fibres. -/
theorem vector_two_not_equiv_three :
    ¬ Nonempty (Examples.vector.Position (vectorShape 2) ≃
      Examples.vector.Position (vectorShape 3)) := by
  rintro ⟨equivalent⟩
  have same := Fintype.card_congr equivalent
  rw [vector_position_card, vector_position_card] at same
  omega

#print axioms listAllEquiv
#print axioms listInductionBundle
#print axioms listAllEquiv_heq
#print axioms listInductionBundle_exact_cast
#print axioms vectorInductionBundle
#print axioms vector_position_card
#print axioms vector_two_not_equiv_three

end Mettapedia.TypeTheory.IndexedContainer
