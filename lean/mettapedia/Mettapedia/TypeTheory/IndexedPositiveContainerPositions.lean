import Mettapedia.TypeTheory.OrderedPositionSegments
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace

/-!
# Structural position segments for registered indexed containers

The source constructor description produces ordered segments: a direct
recursive field contributes one slot, and a nested container contributes its
selected position count. Each segment keeps the source child-index expression.
The resulting lookup agrees with the existing natural-slot decoder, including
repeated indices, empty containers and parameter-dependent indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.IndexedPositiveContainer.Code
open IndexedPolynomial.Description IndexedPolynomial
universe u
variable {I : Interface.{u}} {registry : Registry I} {parameters : Nat}

/-- Segment boundaries follow the authored constructor order. -/
def positionSegments (ordered : registry.OrderedFinitary) :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    {environment : Env I.Value context} → {index : I.Index} →
    Shape code environment index → List (OrderedPositionSegments.Segment I.Index)
  | _, .result _, _, _, _ => []
  | _, .data _ body, _, _, shape => positionSegments ordered body shape.2
  | _, .recursive expression rest, environment, _, shape =>
      (1, I.evalIndex expression environment) :: positionSegments ordered rest shape
  | _, .nested name entry registered _ childIndex rest, environment, _, shape =>
      ((ordered.containerOrdered name entry registered).positions shape.1 |>.length,
        I.evalIndex childIndex environment) :: positionSegments ordered rest shape.2

theorem flatten_positionSegments (ordered : registry.OrderedFinitary) :
    ∀ {context : List I.SortCode} (code : Code I registry parameters context)
      {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index),
      OrderedPositionSegments.flatten (positionSegments ordered code shape) =
        (orderedPositions ordered code shape).map (next code shape)
  | _, .result _, _, _, _ => rfl
  | _, .data _ body, _, _, shape => flatten_positionSegments ordered body shape.2
  | _, .recursive expression rest, environment, _, shape => by
      simp only [positionSegments, OrderedPositionSegments.flatten_cons, List.replicate_one,
        List.singleton_append, orderedPositions, List.map_cons, List.map_map]
      change I.evalIndex expression environment :: OrderedPositionSegments.flatten (positionSegments ordered rest shape) =
        I.evalIndex expression environment :: (orderedPositions ordered rest shape).map (next rest shape)
      rw [flatten_positionSegments ordered rest shape]
  | _, .nested name entry registered output childIndex rest, environment, _, shape => by
      simp only [positionSegments, OrderedPositionSegments.flatten_cons, orderedPositions, List.map_append, List.map_map]
      change List.replicate _ (I.evalIndex childIndex environment) ++
        OrderedPositionSegments.flatten (positionSegments ordered rest shape.2) =
        ((ordered.containerOrdered name entry registered).positions shape.1).map (fun _ => I.evalIndex childIndex environment) ++
          (orderedPositions ordered rest shape.2).map (next rest shape.2)
      rw [List.map_const', flatten_positionSegments ordered rest shape.2]

/-- The selected natural slots are the positions in the source's complete
ordered traversal, rather than a deduplicated list of child indices. -/
theorem slotDecoder_eq_getElem (ordered : registry.OrderedFinitary)
    {context : List I.SortCode} (code : Code I registry parameters context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index) (slot : Nat) :
    ((RecursiveSpaceRepresentation.codePresentation ordered code).coding shape).decode slot =
      (orderedPositions ordered code shape)[slot]? := by
  change (if inside : slot < (orderedPositions ordered code shape).length then
    some ((orderedPositionEquiv ordered code shape) ⟨slot, inside⟩) else none) = _
  by_cases inside : slot < (orderedPositions ordered code shape).length
  · rw [dif_pos inside, List.getElem?_eq_getElem inside]
    rfl
  · rw [dif_neg inside, List.getElem?_eq_none (Nat.le_of_not_gt inside)]

theorem lookup_positionSegments (ordered : registry.OrderedFinitary)
    {context : List I.SortCode} (code : Code I registry parameters context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index)
    (slot : Nat) (childIndex : I.Index) :
    (OrderedPositionSegments.flatten (positionSegments ordered code shape))[slot]? = some childIndex ↔
      ∃ position, ((RecursiveSpaceRepresentation.codePresentation ordered code).coding shape).decode slot =
        some position ∧ next code shape position = childIndex := by
  rw [flatten_positionSegments, List.getElem?_map, slotDecoder_eq_getElem]
  exact Option.map_eq_some_iff

#print axioms flatten_positionSegments
#print axioms slotDecoder_eq_getElem
#print axioms lookup_positionSegments
end Mettapedia.TypeTheory.IndexedPositiveContainer.Code
