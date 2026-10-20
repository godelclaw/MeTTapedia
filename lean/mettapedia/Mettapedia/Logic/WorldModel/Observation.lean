import Mettapedia.Logic.WorldModel.Basic
import Mathlib.Data.List.Fold

/-!
# Observations and translations of general world models

Query semantics requires no additive extraction law. An observation map
translates states, queries and values and proves that the two ways of answering
a query agree. Preserving revision is additional structure. A value map may
forget information; injectivity is required when reflecting distinctions.
-/

namespace Mettapedia.Logic.WorldModel

universe uS uQ uV uT uR uW uU uP uX

variable {S : Type uS} {Q : Type uQ} {V : Type uV}
  {T : Type uT} {R : Type uR} {W : Type uW}
  {U : Type uU} {P : Type uP} {X : Type uX}
  [WorldModel S Q V] [WorldModel T R W] [WorldModel U P X]

/-- Query equivalence depends only on the declared observation. -/
def QueryEq (first second : Q) : Prop :=
  ∀ state : S, WorldModel.extract state first = (WorldModel.extract state second : V)

theorem QueryEq.refl (query : Q) : QueryEq (S := S) (V := V) query query := fun _ => rfl

theorem QueryEq.symm {first second : Q} (same : QueryEq (S := S) (V := V) first second) :
    QueryEq (S := S) (V := V) second first := fun state => (same state).symm

theorem QueryEq.trans {first second third : Q}
    (left : QueryEq (S := S) (V := V) first second)
    (right : QueryEq (S := S) (V := V) second third) :
    QueryEq (S := S) (V := V) first third := fun state => (left state).trans (right state)

/-- A commuting observation map; no revision laws are presumed. -/
structure ObservationMap (S : Type uS) (Q : Type uQ) (V : Type uV)
    (T : Type uT) (R : Type uR) (W : Type uW)
    [WorldModel S Q V] [WorldModel T R W] where
  state : S → T
  query : Q → R
  value : V → W
  observe : ∀ source request,
    WorldModel.extract (state source) (query request) = value (WorldModel.extract source request)

namespace ObservationMap

def id : ObservationMap S Q V S Q V where
  state := _root_.id
  query := _root_.id
  value := _root_.id
  observe _ _ := rfl

/-- Observation maps compose even when the two intermediate carriers and
their update disciplines differ. -/
def comp (first : ObservationMap S Q V T R W) (second : ObservationMap T R W U P X) :
    ObservationMap S Q V U P X where
  state := second.state ∘ first.state
  query := second.query ∘ first.query
  value := second.value ∘ first.value
  observe source request := by
    change WorldModel.extract (second.state (first.state source))
      (second.query (first.query request)) = second.value (first.value _)
    rw [second.observe, first.observe]

/-- Every value predicate transports along a commuting observation map. -/
theorem transports (map : ObservationMap S Q V T R W)
    (property : W → Prop) (source : S) (request : Q) :
    property (WorldModel.extract (map.state source) (map.query request)) ↔
      property (map.value (WorldModel.extract source request)) := by
  rw [map.observe]

/-- Injectivity of the value interpretation is precisely what allows this
map to reflect the equality of two source observations. -/
theorem reflects_distinction (map : ObservationMap S Q V T R W)
    (faithful : Function.Injective map.value) (source : S) (first second : Q) :
    WorldModel.extract (map.state source) (map.query first) =
        (WorldModel.extract (map.state source) (map.query second) : W) ↔
      WorldModel.extract source first = (WorldModel.extract source second : V) := by
  rw [map.observe, map.observe]
  exact faithful.eq_iff

/-- Query equivalence transports on all represented target states. It extends
to all target states only when the state translation is surjective. -/
theorem queryEq_of_surjective (map : ObservationMap S Q V T R W)
    (covers : Function.Surjective map.state) {first second : Q}
    (same : QueryEq (S := S) (V := V) first second) :
    QueryEq (S := T) (V := W) (map.query first) (map.query second) := by
  intro target
  obtain ⟨source, rfl⟩ := covers target
  rw [map.observe, map.observe, same source]

@[simp] theorem id_comp (map : ObservationMap S Q V T R W) : comp id map = map := by
  cases map
  rfl

@[simp] theorem comp_id (map : ObservationMap S Q V T R W) : comp map id = map := by
  cases map
  rfl

theorem comp_assoc (first : ObservationMap S Q V T R W)
    (second : ObservationMap T R W U P X)
    {A B C : Type*} [WorldModel A B C] (third : ObservationMap U P X A B C) :
    comp (comp first second) third = comp first (comp second third) := rfl

end ObservationMap

/-- A world-model translation additionally preserves the authored empty
state and revision operation; associativity and additivity are not assumed. -/
structure RevisionMap (S : Type uS) (Q : Type uQ) (V : Type uV)
    (T : Type uT) (R : Type uR) (W : Type uW)
    [WorldModel S Q V] [WorldModel T R W]
    extends ObservationMap S Q V T R W where
  empty : state (WorldModel.empty Q V) = WorldModel.empty R W
  revise : ∀ first second,
    state (WorldModel.revise Q V first second) =
      WorldModel.revise R W (state first) (state second)

namespace RevisionMap

def id : RevisionMap S Q V S Q V where
  toObservationMap := ObservationMap.id
  empty := rfl
  revise _ _ := rfl

def comp (first : RevisionMap S Q V T R W) (second : RevisionMap T R W U P X) :
    RevisionMap S Q V U P X where
  toObservationMap := first.toObservationMap.comp second.toObservationMap
  empty := by change second.state (first.state _) = _; rw [first.empty, second.empty]
  revise left right := by
    change second.state (first.state _) = _
    rw [first.revise, second.revise]
    rfl

@[simp] theorem id_comp (map : RevisionMap S Q V T R W) : comp id map = map := by
  cases map
  rfl

@[simp] theorem comp_id (map : RevisionMap S Q V T R W) : comp map id = map := by
  cases map
  rfl

theorem comp_assoc (first : RevisionMap S Q V T R W)
    (second : RevisionMap T R W U P X)
    {A B C : Type*} [WorldModel A B C] (third : RevisionMap U P X A B C) :
    comp (comp first second) third = comp first (comp second third) := rfl

/-- A revision map preserves every chronological update fold. This requires
no claim that the updates commute or associate. -/
theorem foldl_revise (map : RevisionMap S Q V T R W) (updates : List S) (initial : S) :
    map.state (updates.foldl (WorldModel.revise Q V) initial) =
      (updates.map map.state).foldl (WorldModel.revise R W) (map.state initial) := by
  induction updates generalizing initial with
  | nil => rfl
  | cons update updates ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, map.revise]

end RevisionMap

end Mettapedia.Logic.WorldModel
