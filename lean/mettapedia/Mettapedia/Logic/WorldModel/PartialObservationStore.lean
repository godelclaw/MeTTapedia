import Mettapedia.Logic.WorldModel.Observation

/-!
# Chronological stores of partial observations

Revision gives the later store priority where it has an answer and otherwise
retains the earlier answer. This regime is monoidal and generally
noncommutative. Mapping stored values preserves the complete revision
operation and every query, without requiring additive evidence.
-/

namespace Mettapedia.Logic.WorldModel.PartialObservationStore

variable {Query Value Other : Type*}

abbrev Store (Query Value : Type*) := Query → Option Value

def revise (first second : Store Query Value) : Store Query Value :=
  fun query => (second query).or (first query)

instance : MonoidalWorldModel (Store Query Value) Query (Option Value) where
  revise := revise
  empty _ := none
  extract store query := store query
  revise_assoc first second third := by
    funext query
    dsimp only [revise]
    cases first query <;> cases second query <;> cases third query <;> rfl
  revise_empty_left first := by
    funext query
    dsimp only [revise]
    cases first query <;> rfl
  revise_empty_right first := rfl

/-- Value interpretation is a genuine revision-preserving map of stores. -/
def map (interpret : Value → Other) :
    RevisionMap (Store Query Value) Query (Option Value)
      (Store Query Other) Query (Option Other) where
  state store query := (store query).map interpret
  query := id
  value := Option.map interpret
  observe _ _ := rfl
  empty := rfl
  revise first second := by
    funext query
    change ((second query).or (first query)).map interpret =
      ((second query).map interpret).or ((first query).map interpret)
    cases first query <;> cases second query <;> rfl

theorem map_observation (interpret : Value → Other) (store : Store Query Value) (query : Query) :
    (map interpret).state store query = (store query).map interpret := rfl

theorem interpretation_preserves_chronology (interpret : Value → Other)
    (updates : List (Store Query Value)) (initial : Store Query Value) :
    (map interpret).state (updates.foldl revise initial) =
      (updates.map (map interpret).state).foldl revise ((map interpret).state initial) :=
  (map interpret).foldl_revise updates initial

namespace Controls

def first : Store Unit Nat := fun _ => some 1
def second : Store Unit Nat := fun _ => some 2

theorem chronological_revision_not_commutative :
    revise first second () ≠ revise second first () := by decide

theorem value_mapping_preserves_latest_answer :
    (map (fun n : Nat => n + 10)).state (revise first second) () = some 12 := rfl

end Controls

end Mettapedia.Logic.WorldModel.PartialObservationStore
