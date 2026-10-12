import Mettapedia.GSLT.LanguageDef.TopDownMatchDerivatives
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Pairwise

/-!
# Partitioning and relative controls for top-down match derivatives

The dependency partition and displacement factoring follow Sections 4.3–4.4
of Erkens–Groote, *A Set Automaton to Locate All Pattern Matches in a Term*
(https://arxiv.org/abs/2106.15311). The retained derivative carrier contains
flattened constructor obligations. This module normalizes those residual
controls; it does not construct the paper's complete offline state graph.

Relative controls are shared independently of their ordered instances. An
instance retains its displacement and complete occurrence announcement.
Derivative results can be shared only for an identical control and
displacement. This preserves source order and duplicate occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TopDownMatchDerivativeNormalization

open OrderedPatternMatrixCompilation SubtermMatching TopDownMatchDerivatives

universe u v w
variable {Head : Type u}

/-- Greatest common prefix of two syntactic child paths. -/
def commonPrefix : Position → Position → Position
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

theorem commonPrefix_prefix_left (left right : Position) :
    (commonPrefix left right).IsPrefix left := by
  induction left generalizing right with
  | nil => simp [commonPrefix]
  | cons a as ih =>
      cases right with
      | nil => simp [commonPrefix]
      | cons b bs =>
          by_cases same : a = b
          · subst b
            simpa [commonPrefix] using
              (List.prefix_cons_inj a).mpr (ih bs)
          · simp [commonPrefix, same]

theorem commonPrefix_prefix_right (left right : Position) :
    (commonPrefix left right).IsPrefix right := by
  induction left generalizing right with
  | nil => simp [commonPrefix]
  | cons a as ih =>
      cases right with
      | nil => simp [commonPrefix]
      | cons b bs =>
          by_cases same : a = b
          · subst b
            simpa [commonPrefix] using
              (List.prefix_cons_inj a).mpr (ih bs)
          · simp [commonPrefix, same]

theorem commonPrefix_greatest (base left right : Position)
    (leftPrefix : base.IsPrefix left) (rightPrefix : base.IsPrefix right) :
    base.IsPrefix (commonPrefix left right) := by
  induction base generalizing left right with
  | nil => simp
  | cons a as ih =>
      cases left with
      | nil => simp at leftPrefix
      | cons b bs =>
          cases right with
          | nil => simp at rightPrefix
          | cons c cs =>
              have leftEq : a = b := by
                obtain ⟨tail, h⟩ := leftPrefix
                exact (List.cons.inj h).1
              have rightEq : a = c := by
                obtain ⟨tail, h⟩ := rightPrefix
                exact (List.cons.inj h).1
              subst b
              subst c
              simpa [commonPrefix] using
                (List.prefix_cons_inj a).mpr
                  (ih bs cs ((List.prefix_cons_inj a).mp leftPrefix)
                    ((List.prefix_cons_inj a).mp rightPrefix))

/-- Empty families use the root. Every nonempty family has its greatest
common prefix, without an arbitrary path bound. -/
def greatestCommonPrefix : List Position → Position
  | [] => []
  | first :: rest =>
      match rest with
      | [] => first
      | _ :: _ => commonPrefix first (greatestCommonPrefix rest)

theorem greatestCommonPrefix_prefix (paths : List Position) (path : Position)
    (membership : path ∈ paths) :
    (greatestCommonPrefix paths).IsPrefix path := by
  induction paths with
  | nil => simp at membership
  | cons first rest ih =>
      cases rest with
      | nil =>
          have same : path = first := by simpa using membership
          subst path
          simp [greatestCommonPrefix]
      | cons next tail =>
          simp only [List.mem_cons] at membership
          rcases membership with rfl | membership
          · exact commonPrefix_prefix_left _ _
          · exact (commonPrefix_prefix_right _ _).trans (ih (by simpa using membership))

theorem greatestCommonPrefix_greatest (paths : List Position) (base : Position)
    (nonempty : paths ≠ [])
    (basePrefixes : ∀ path ∈ paths, base.IsPrefix path) :
    base.IsPrefix (greatestCommonPrefix paths) := by
  induction paths with
  | nil => simp at nonempty
  | cons first rest ih =>
      cases rest with
      | nil => simpa [greatestCommonPrefix] using basePrefixes first (by simp)
      | cons next tail =>
          exact commonPrefix_greatest base first (greatestCommonPrefix (next :: tail))
            (basePrefixes first (by simp))
            (ih (by simp) (fun path membership => basePrefixes path (by simp [membership])))

section
variable [DecidableEq Head]
deriving instance DecidableEq for Goal
end

/-- Constructor keys may disagree while the inspection position is shared. -/
def overlaps (first second : Goal Head) : Bool :=
  first.pending.any fun left =>
    second.pending.any fun right => decide (left.position = right.position)

theorem overlaps_iff (first second : Goal Head) :
    overlaps first second ↔
      ∃ left ∈ first.pending, ∃ right ∈ second.pending,
        left.position = right.position := by
  simp [overlaps]

theorem overlaps_comm (first second : Goal Head) :
    overlaps first second = overlaps second first := by
  apply Bool.eq_iff_iff.mpr
  rw [overlaps_iff, overlaps_iff]
  constructor <;> rintro ⟨left, leftMember, right, rightMember, same⟩
  · exact ⟨right, rightMember, left, leftMember, same.symm⟩
  · exact ⟨right, rightMember, left, leftMember, same.symm⟩

def touches (goal : Goal Head) (component : List (Goal Head)) : Bool :=
  component.any (overlaps goal)

theorem touches_iff (goal : Goal Head) (component : List (Goal Head)) :
    touches goal component ↔ ∃ other ∈ component, overlaps goal other := by
  simp [touches]

/-- Inserting a goal joins every component it touches. Existing components
are already independent, so this also joins transitive dependency chains. -/
def dependencyComponents : List (Goal Head) → List (List (Goal Head))
  | [] => []
  | goal :: goals =>
      let previous := dependencyComponents goals
      (goal :: (previous.filter (touches goal)).flatten) ::
        previous.filter (fun component => !touches goal component)

/-- Partitioning neither invents nor loses an occurrence. The instance
vector, rather than this component traversal order, restores source order. -/
theorem dependencyComponents_flatten_perm (goals : List (Goal Head)) :
    (dependencyComponents goals).flatten.Perm goals := by
  induction goals with
  | nil => rfl
  | cons goal goals ih =>
      simp only [dependencyComponents, List.flatten_cons, List.cons_append]
      have divided :=
        (List.filter_append_perm (touches goal) (dependencyComponents goals)).flatten
      simpa only [List.flatten_append] using (divided.trans ih).cons goal

/-- Separate components inspect disjoint sets of pending positions. -/
def Independent (first second : List (Goal Head)) : Prop :=
  ∀ left ∈ first, ∀ right ∈ second, overlaps left right = false

instance independent_symmetric : Std.Symm (@Independent Head) where
  symm first second separated left leftMember right rightMember := by
    rw [overlaps_comm]
    exact separated right rightMember left leftMember

theorem dependencyComponents_independent (goals : List (Goal Head)) :
    (dependencyComponents goals).Pairwise Independent := by
  induction goals with
  | nil => exact List.Pairwise.nil
  | cons goal goals ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro other membership
        obtain ⟨oldMember, untouched⟩ := List.mem_filter.mp membership
        have noTouch : touches goal other = false := by simpa using untouched
        intro left leftMember right rightMember
        simp only [List.mem_cons] at leftMember
        rcases leftMember with rfl | leftMember
        · apply Bool.eq_false_iff.mpr
          intro shared
          have touching := (touches_iff left other).mpr ⟨right, rightMember, shared⟩
          simp [noTouch] at touching
        · obtain ⟨component, joined, leftMember⟩ := List.mem_flatten.mp leftMember
          obtain ⟨componentMember, touched⟩ := List.mem_filter.mp joined
          have different : component ≠ other := by
            intro same
            subst component
            simp [noTouch] at touched
          exact ih.forall componentMember oldMember different left leftMember right rightMember
      · exact ih.filter _

/-- A dependency path remains inside its component. Constructor keys are
irrelevant to this graph: contradictory keys still share an inspection. -/
def OverlapEdge (component : List (Goal Head)) (first second : Goal Head) : Prop :=
  first ∈ component ∧ second ∈ component ∧ overlaps first second

instance overlapEdge_symmetric (component : List (Goal Head)) :
    Std.Symm (OverlapEdge component) where
  symm first second edge :=
    ⟨edge.2.1, edge.1, by simpa only [overlaps_comm] using edge.2.2⟩

def Connected (component : List (Goal Head)) : Prop :=
  ∀ first ∈ component, ∀ second ∈ component,
    Relation.ReflTransGen (OverlapEdge component) first second

private theorem connected_join (goal : Goal Head) (components : List (List (Goal Head)))
    (connected : ∀ component ∈ components, Connected component) :
    Connected (goal :: (components.filter (touches goal)).flatten) := by
  let joined := goal :: (components.filter (touches goal)).flatten
  have reachable (other : Goal Head) (membership : other ∈ joined) :
      Relation.ReflTransGen (OverlapEdge joined) goal other := by
    simp only [joined, List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact .refl
    · obtain ⟨component, included, otherMember⟩ := List.mem_flatten.mp membership
      obtain ⟨componentMember, touched⟩ := List.mem_filter.mp included
      obtain ⟨witness, witnessMember, shared⟩ := (touches_iff goal component).mp touched
      have subset : ∀ item ∈ component, item ∈ joined := by
        intro item itemMember
        apply List.mem_cons_of_mem
        exact List.mem_flatten.mpr
          ⟨component, List.mem_filter.mpr ⟨componentMember, touched⟩, itemMember⟩
      have firstStep : Relation.ReflTransGen (OverlapEdge joined) goal witness :=
        .single ⟨by simp [joined], subset witness witnessMember, shared⟩
      have path := connected component componentMember witness witnessMember other otherMember
      have transported : Relation.ReflTransGen (OverlapEdge joined) witness other :=
        Relation.ReflTransGen.mono
          (fun a b (edge : OverlapEdge component a b) =>
            ⟨subset _ edge.1, subset _ edge.2.1, edge.2.2⟩) witness other path
      exact firstStep.trans transported
  intro first firstMember second secondMember
  exact (symm (reachable first firstMember)).trans (reachable second secondMember)

theorem dependencyComponents_connected (goals : List (Goal Head)) :
    ∀ component ∈ dependencyComponents goals, Connected component := by
  induction goals with
  | nil => simp [dependencyComponents]
  | cons goal goals ih =>
      intro component membership
      simp only [dependencyComponents, List.mem_cons] at membership
      rcases membership with rfl | membership
      · exact connected_join goal (dependencyComponents goals) ih
      · exact ih component (List.mem_filter.mp membership).1

theorem dependencyComponents_nonempty (goals : List (Goal Head)) :
    ∀ component ∈ dependencyComponents goals, component ≠ [] := by
  induction goals with
  | nil => simp [dependencyComponents]
  | cons goal goals ih =>
      intro component membership
      simp only [dependencyComponents, List.mem_cons] at membership
      rcases membership with rfl | membership
      · simp
      · exact ih component (List.mem_filter.mp membership).1

/-- Pick the containing component. The singleton fallback makes the
operation total even for a separately supplied component collection. -/
def componentFor [DecidableEq Head]
    (components : List (List (Goal Head))) (goal : Goal Head) : List (Goal Head) :=
  (components.find? (fun component => decide (goal ∈ component))).getD [goal]

theorem mem_componentFor [DecidableEq Head]
    (components : List (List (Goal Head))) (goal : Goal Head) :
    goal ∈ componentFor components goal := by
  cases found : components.find? (fun component => decide (goal ∈ component)) with
  | none => simp [componentFor, found]
  | some component =>
      have admitted := List.find?_some found
      simpa [componentFor, found] using admitted

theorem componentFor_mem [DecidableEq Head]
    (components : List (List (Goal Head))) (goal : Goal Head)
    (present : ∃ component ∈ components, goal ∈ component) :
    componentFor components goal ∈ components := by
  cases found : components.find? (fun component => decide (goal ∈ component)) with
  | none =>
      obtain ⟨component, componentMember, goalMember⟩ := present
      have absent := List.find?_eq_none.mp found component componentMember
      simp [goalMember] at absent
  | some component =>
      simpa [componentFor, found] using List.mem_of_find?_eq_some found

theorem componentFor_dependency_mem [DecidableEq Head]
    (goals : List (Goal Head)) (goal : Goal Head) (membership : goal ∈ goals) :
    componentFor (dependencyComponents goals) goal ∈ dependencyComponents goals := by
  apply componentFor_mem
  apply List.mem_flatten.mp
  exact (dependencyComponents_flatten_perm goals).mem_iff.mpr membership

/-- The announcement is included so completion retains its displacement
even after the final constructor obligation has been consumed. -/
def componentPositions (component : List (Goal Head)) : List Position :=
  component.flatMap fun goal =>
    goal.location.position :: goal.pending.map Obligation.position

def componentBase (component : List (Goal Head)) : Position :=
  greatestCommonPrefix (componentPositions component)

theorem componentBase_prefix_location (component : List (Goal Head))
    (goal : Goal Head) (membership : goal ∈ component) :
    (componentBase component).IsPrefix goal.location.position := by
  apply greatestCommonPrefix_prefix
  exact List.mem_flatMap.mpr ⟨goal, membership, by simp⟩

theorem componentBase_prefix_obligation (component : List (Goal Head))
    (goal : Goal Head) (membership : goal ∈ component)
    (obligation : Obligation Head) (present : obligation ∈ goal.pending) :
    (componentBase component).IsPrefix obligation.position := by
  apply greatestCommonPrefix_prefix
  exact List.mem_flatMap.mpr
    ⟨goal, membership, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨obligation, present, rfl⟩)⟩

/-- The compiled goals and every residual derivative inspect only below
their retained announcement. -/
def Descendants (goals : List (Goal Head)) : Prop :=
  ∀ goal ∈ goals, ∀ obligation ∈ goal.pending,
    goal.location.position.IsPrefix obligation.position

theorem seed_descendants (root : Position) (next : Nat)
    (programs : List (List (Obligation Head))) :
    Descendants (seed root next programs) := by
  induction programs generalizing next with
  | nil => simp [seed, Descendants]
  | cons program programs ih =>
      intro goal membership obligation present
      simp only [seed, List.mem_cons] at membership
      rcases membership with rfl | membership
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp present
        exact List.prefix_append _ _
      · exact ih (next + 1) goal membership obligation present

theorem source_goals_descendants (observations : List (Observation Head))
    (programs : List (List (Obligation Head))) :
    Descendants (observations.flatMap (fun observation => seed observation.position 0 programs)) := by
  intro goal membership obligation present
  obtain ⟨observation, _, seeded⟩ := List.mem_flatMap.mp membership
  exact seed_descendants observation.position 0 programs goal seeded obligation present

theorem deriveGoals_descendants [DecidableEq Head]
    (observation : Observation Head) (goals : List (Goal Head))
    (descendants : Descendants goals) : Descendants (deriveGoals observation goals) := by
  intro goal membership obligation present
  obtain ⟨original, originalMember, returned⟩ := List.mem_filterMap.mp membership
  cases result : derive observation original.pending with
  | none => simp [result] at returned
  | some residual =>
      simp only [result, Option.map_some, Option.some.injEq] at returned
      subst goal
      exact descendants original originalMember obligation
        ((derive_sublist observation original.pending residual result).subset present)

theorem execute_descendants [DecidableEq Head]
    (observations : List (Observation Head)) (goals : List (Goal Head))
    (descendants : Descendants goals) :
    Descendants (TopDownMatchDerivatives.execute observations goals) := by
  induction observations generalizing goals with
  | nil => exact descendants
  | cons observation observations ih =>
      exact ih _ (deriveGoals_descendants observation goals descendants)

theorem dependency_component_descendants (goals : List (Goal Head))
    (descendants : Descendants goals) (component : List (Goal Head))
    (membership : component ∈ dependencyComponents goals) : Descendants component := by
  intro goal goalMember obligation present
  have globalMember : goal ∈ goals :=
    (dependencyComponents_flatten_perm goals).mem_iff.mp
      (List.mem_flatten.mpr ⟨component, membership, goalMember⟩)
  exact descendants goal globalMember obligation present

theorem componentBase_eq_announcementPrefix (component : List (Goal Head))
    (nonempty : component ≠ []) (descendants : Descendants component) :
    componentBase component =
      greatestCommonPrefix (component.map (fun goal => goal.location.position)) := by
  let announcementBase :=
    greatestCommonPrefix (component.map (fun goal => goal.location.position))
  have announcementsNonempty :
      component.map (fun goal => goal.location.position) ≠ [] := by
    simpa using nonempty
  have announcementPrefix (goal : Goal Head) (membership : goal ∈ component) :
      announcementBase.IsPrefix goal.location.position :=
    greatestCommonPrefix_prefix _ _ (List.mem_map.mpr ⟨goal, membership, rfl⟩)
  have positionsNonempty : componentPositions component ≠ [] := by
    obtain ⟨goal, membership⟩ := List.exists_mem_of_ne_nil component nonempty
    intro empty
    have present : goal.location.position ∈ componentPositions component :=
      List.mem_flatMap.mpr ⟨goal, membership, by simp⟩
    simp [empty] at present
  have announcementBasePrefix : announcementBase.IsPrefix (componentBase component) := by
    apply greatestCommonPrefix_greatest _ _ positionsNonempty
    intro path membership
    obtain ⟨goal, goalMember, pathMember⟩ := List.mem_flatMap.mp membership
    simp only [List.mem_cons, List.mem_map] at pathMember
    rcases pathMember with rfl | ⟨obligation, obligationMember, rfl⟩
    · exact announcementPrefix goal goalMember
    · exact (announcementPrefix goal goalMember).trans
        (descendants goal goalMember obligation obligationMember)
  have componentBasePrefix : (componentBase component).IsPrefix announcementBase := by
    apply greatestCommonPrefix_greatest _ _ announcementsNonempty
    intro path membership
    obtain ⟨goal, goalMember, rfl⟩ := List.mem_map.mp membership
    exact componentBase_prefix_location component goal goalMember
  exact componentBasePrefix.eq_of_length_le announcementBasePrefix.length_le

/-- Remove the component displacement from its inspections and announcement. -/
def relativize (base : Position) (goal : Goal Head) : Goal Head :=
  ⟨⟨goal.location.position.drop base.length, goal.location.occurrence⟩,
   goal.pending.map fun obligation =>
     ⟨obligation.position.drop base.length, obligation.key⟩⟩

def restore (base : Position) (goal : Goal Head) : Goal Head :=
  ⟨⟨base ++ goal.location.position, goal.location.occurrence⟩,
    shift base goal.pending⟩

theorem restore_relativize (base : Position) (goal : Goal Head)
    (locationPrefix : base.IsPrefix goal.location.position)
    (pendingPrefix : ∀ obligation ∈ goal.pending, base.IsPrefix obligation.position) :
    restore base (relativize base goal) = goal := by
  have location := List.prefix_iff_eq_append.mp locationPrefix
  have obligations :
      shift base (goal.pending.map fun obligation =>
        ⟨obligation.position.drop base.length, obligation.key⟩) = goal.pending := by
    simp only [shift, List.map_map]
    calc
      _ = goal.pending.map id := by
        apply List.map_congr_left
        intro obligation membership
        simp only [Function.comp_apply, List.prefix_iff_eq_append.mp
          (pendingPrefix obligation membership), id_eq]
      _ = goal.pending := List.map_id _
  cases goal with
  | mk announcement pending =>
      cases announcement with
      | mk position occurrence =>
          simp only [restore, relativize, location, obligations]

def factor [DecidableEq Head] (goals : List (Goal Head)) (goal : Goal Head) :
    Position × Goal Head :=
  let component := componentFor (dependencyComponents goals) goal
  let base := componentBase component
  (base, relativize base goal)

theorem restore_factor [DecidableEq Head] (goals : List (Goal Head)) (goal : Goal Head) :
    restore (factor goals goal).1 (factor goals goal).2 = goal := by
  apply restore_relativize
  · exact componentBase_prefix_location _ _ (mem_componentFor _ _)
  · intro obligation membership
    exact componentBase_prefix_obligation _ _ (mem_componentFor _ _) obligation membership

/-- On source-generated descendant goals, factoring uses precisely the
paper's announcement-position displacement. -/
theorem factor_displacement [DecidableEq Head]
    (goals : List (Goal Head)) (goal : Goal Head) (membership : goal ∈ goals)
    (descendants : Descendants goals) :
    (factor goals goal).1 = greatestCommonPrefix
      ((componentFor (dependencyComponents goals) goal).map (fun item => item.location.position)) := by
  apply componentBase_eq_announcementPrefix
  · exact dependencyComponents_nonempty goals _
      (componentFor_dependency_mem goals goal membership)
  · exact dependency_component_descendants goals descendants _
      (componentFor_dependency_mem goals goal membership)

/-- An ordered instance holds no copy of its constructor-obligation vector. -/
structure Instance where
  displacement : Position
  announcement : Location
  control : Nat
deriving DecidableEq, Repr

structure NormalForm (Head : Type u) where
  controls : List (List (Obligation Head))
  instances : List Instance
deriving Repr

def instantiate (entry : Instance) (pending : List (Obligation Head)) : Goal Head :=
  restore entry.displacement ⟨entry.announcement, pending⟩

/-- Invalid indices have no behavior. Normalization proves every emitted
index resolves to the exact shared residual control. -/
def expand (normal : NormalForm Head) : List (Goal Head) :=
  normal.instances.filterMap fun entry =>
    normal.controls[entry.control]?.map (instantiate entry)

/-- Partition, factor displacements, and intern relative residual controls.
The instance vector follows the original goal vector exactly. -/
def normalize [DecidableEq Head] (goals : List (Goal Head)) : NormalForm Head :=
  let factors := goals.map (factor goals)
  let controls := (factors.map (fun entry => entry.2.pending)).eraseDups
  ⟨controls, factors.map fun entry =>
    ⟨entry.1, entry.2.location, controls.idxOf entry.2.pending⟩⟩

/-- Exact reconstruction includes announcement positions, source order and
every duplicate occurrence, not merely the set of completed matches. -/
theorem expand_normalize [DecidableEq Head] (goals : List (Goal Head)) :
    expand (normalize goals) = goals := by
  unfold expand normalize
  simp only [List.filterMap_map, List.map_map, Function.comp_apply]
  calc
    _ = goals.filterMap (fun goal => some goal) := by
      apply List.filterMap_congr
      intro goal membership
      have present : (factor goals goal).2.pending ∈
          ((goals.map (factor goals)).map (fun entry => entry.2.pending)).eraseDups := by
        simp only [List.mem_eraseDups, List.mem_map]
        exact ⟨factor goals goal, ⟨goal, membership, rfl⟩, rfl⟩
      have selected := List.getElem?_idxOf present
      simp only [List.map_map] at selected
      rw [selected]
      simp only [Option.map_some, Option.some.injEq]
      simpa only [instantiate] using restore_factor goals goal
    _ = goals := by simp

/-- Every emitted instance references an interned control. The partial
lookup in `expand` therefore refuses only separately supplied malformed
normal forms, never a compiled one. -/
theorem normalize_indexed [DecidableEq Head] (goals : List (Goal Head)) :
    ∀ entry ∈ (normalize goals).instances,
      ∃ pending, (normalize goals).controls[entry.control]? = some pending := by
  intro entry membership
  obtain ⟨factored, factoredMember, rfl⟩ := List.mem_map.mp membership
  refine ⟨factored.2.pending, ?_⟩
  apply List.getElem?_idxOf
  change factored.2.pending ∈
    ((goals.map (factor goals)).map (fun item => item.2.pending)).eraseDups
  simp only [List.mem_eraseDups, List.mem_map]
  exact ⟨factored, List.mem_map.mp factoredMember, rfl⟩

section
variable [DecidableEq Head]

theorem derive_shift_at (base path : Position) (observedKey : ConstructorKey Head)
    (pending : List (Obligation Head)) :
    derive ⟨base ++ path, observedKey⟩ (shift base pending) =
      (derive ⟨path, observedKey⟩ pending).map (shift base) := by
  induction pending with
  | nil => rfl
  | cons obligation pending ih =>
      change derive ⟨base ++ path, observedKey⟩
        (⟨base ++ obligation.position, obligation.key⟩ :: shift base pending) = _
      by_cases samePosition : obligation.position = path
      · by_cases sameKey : obligation.key = observedKey
        · simp only [derive, samePosition, sameKey,
            if_true]
          exact ih
        · simp [derive, samePosition, sameKey]
      · simp only [derive, List.append_cancel_left_eq, samePosition, if_false]
        rw [ih]
        cases result : derive ⟨path, observedKey⟩ pending <;> simp [shift]

theorem derive_shift_unrelated (base : Position) (observation : Observation Head)
    (pending : List (Obligation Head))
    (unrelated : ¬base.IsPrefix observation.position) :
    derive observation (shift base pending) = some (shift base pending) := by
  induction pending with
  | nil => rfl
  | cons obligation pending ih =>
      have different : base ++ obligation.position ≠ observation.position := by
        intro same
        apply unrelated
        rw [← same]
        exact List.prefix_append _ _
      change derive observation
        (⟨base ++ obligation.position, obligation.key⟩ :: shift base pending) = _
      simp only [derive, different, if_false, ih, Option.map_some]
      rfl

/-- A shared control is observed relative to its particular displacement.
An observation outside that displacement cannot change the control. -/
def relativeObservation (base : Position) (observation : Observation Head) :
    Option (Observation Head) :=
  if base.isPrefixOf observation.position then
    some ⟨observation.position.drop base.length, observation.key⟩
  else none

def relativeDerivative (base : Position) (observation : Observation Head)
    (pending : List (Obligation Head)) : Option (List (Obligation Head)) :=
  match relativeObservation base observation with
  | none => some pending
  | some relative => derive relative pending

theorem derive_shift_relative (base : Position) (observation : Observation Head)
    (pending : List (Obligation Head)) :
    (relativeDerivative base observation pending).map (shift base) =
      derive observation (shift base pending) := by
  by_cases below : base.IsPrefix observation.position
  · have reassembled := List.prefix_iff_eq_append.mp below
    have relative : relativeObservation base observation =
        some ⟨observation.position.drop base.length, observation.key⟩ := by
      simp [relativeObservation, List.isPrefixOf_iff_prefix.mpr below]
    rw [relativeDerivative, relative]
    rw [← derive_shift_at]
    rw [reassembled]
  · have relative : relativeObservation base observation = none := by
      simp [relativeObservation, List.isPrefixOf_iff_prefix, below]
    rw [relativeDerivative, relative]
    simpa using (derive_shift_unrelated base observation pending below).symm

/-- Control identity alone is insufficient: equal relative programs at
different subject displacements remain distinct derivative activations. -/
def Instance.activation (entry : Instance) : Nat × Position :=
  (entry.control, entry.displacement)

def activations (normal : NormalForm Head) : List (Nat × Position) :=
  (normal.instances.map Instance.activation).eraseDups

def activationDerivative (normal : NormalForm Head) (observation : Observation Head)
    (activation : Nat × Position) : Option (List (Obligation Head)) :=
  normal.controls[activation.1]?.bind (relativeDerivative activation.2 observation)

def derivativeCache (normal : NormalForm Head) (observation : Observation Head) :
    List ((Nat × Position) × Option (List (Obligation Head))) :=
  (activations normal).map fun activation =>
    (activation, activationDerivative normal observation activation)

def cachedDerivative
    (cache : List ((Nat × Position) × Option (List (Obligation Head))))
    (activation : Nat × Position) : Option (List (Obligation Head)) :=
  ((cache.find? (fun entry => decide (entry.1 = activation))).map Prod.snd).join

private theorem find_computed {Key : Type v} {Value : Type w} [DecidableEq Key]
    (keys : List Key) (compute : Key → Value) (key : Key) (membership : key ∈ keys) :
    ((keys.map fun current => (current, compute current)).find?
      (fun entry => decide (entry.1 = key))).map Prod.snd = some (compute key) := by
  induction keys with
  | nil => simp at membership
  | cons first rest ih =>
      by_cases same : first = key
      · subst first
        simp
      · have tail : key ∈ rest := by simpa [Ne.symm same] using membership
        simpa [same] using ih tail

theorem cachedDerivative_exact (normal : NormalForm Head)
    (observation : Observation Head) (entry : Instance)
    (membership : entry ∈ normal.instances) :
    cachedDerivative (derivativeCache normal observation) entry.activation =
      activationDerivative normal observation entry.activation := by
  have present : entry.activation ∈ activations normal := by
    simp only [activations, List.mem_eraseDups, List.mem_map]
    exact ⟨entry, membership, rfl⟩
  unfold cachedDerivative derivativeCache
  rw [find_computed (activations normal) (activationDerivative normal observation)
    entry.activation present]
  rfl

/-- Every unique activation is differentiated once. Results fan out to the
ordered instance vector; no announcement is collapsed with its control. -/
def dispatch (normal : NormalForm Head)
    (cache : List ((Nat × Position) × Option (List (Obligation Head)))) :
    List (Goal Head) :=
  normal.instances.filterMap fun entry =>
    (cachedDerivative cache entry.activation).map (instantiate entry)

def deriveShared (normal : NormalForm Head) (observation : Observation Head) :
    List (Goal Head) :=
  dispatch normal (derivativeCache normal observation)

/-- Cached dispatch computes the exact old derivative goal vector, including
refusal, without differentiating each duplicate instance independently. -/
theorem deriveShared_eq_deriveGoals (normal : NormalForm Head)
    (observation : Observation Head) :
    deriveShared normal observation = deriveGoals observation (expand normal) := by
  simp only [deriveShared, dispatch, deriveGoals, expand, List.filterMap_filterMap]
  apply List.filterMap_congr
  intro entry membership
  rw [cachedDerivative_exact normal observation entry membership]
  simp only [activationDerivative, Instance.activation]
  cases selected : normal.controls[entry.control]? with
  | none => simp
  | some pending =>
      simp only [Option.bind_some, Option.map_some]
      have derivative := derive_shift_relative entry.displacement observation pending
      change (relativeDerivative entry.displacement observation pending).map
          (instantiate entry) = _
      simp only [instantiate, restore]
      rw [← derivative]
      cases relativeDerivative entry.displacement observation pending <;> rfl

def step (normal : NormalForm Head) (observation : Observation Head) : NormalForm Head :=
  normalize (deriveShared normal observation)

theorem expand_step (normal : NormalForm Head) (observation : Observation Head) :
    expand (step normal observation) = deriveGoals observation (expand normal) := by
  rw [step, expand_normalize, deriveShared_eq_deriveGoals]

theorem step_normalize (goals : List (Goal Head)) (observation : Observation Head) :
    step (normalize goals) observation = normalize (deriveGoals observation goals) := by
  rw [step, deriveShared_eq_deriveGoals, expand_normalize]

def execute : List (Observation Head) → NormalForm Head → NormalForm Head
  | [], normal => normal
  | observation :: observations, normal => execute observations (step normal observation)

theorem expand_execute (observations : List (Observation Head)) (normal : NormalForm Head) :
    expand (execute observations normal) =
      TopDownMatchDerivatives.execute observations (expand normal) := by
  induction observations generalizing normal with
  | nil => rfl
  | cons observation observations ih =>
      rw [execute, ih, expand_step, TopDownMatchDerivatives.execute]

theorem normalized_execute_descendants (observations : List (Observation Head))
    (goals : List (Goal Head)) (descendants : Descendants goals) :
    Descendants (expand (execute observations (normalize goals))) := by
  rw [expand_execute, expand_normalize]
  exact execute_descendants observations goals descendants

private theorem eraseDups_length_le {α : Type v} [BEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.length_cons, List.length_cons]
      exact Nat.add_le_add_right
        ((eraseDups_length_le _).trans (List.length_filter_le _ rest)) 1
termination_by values.length
decreasing_by exact Nat.lt_add_one_of_le (List.length_filter_le _ _)

omit [DecidableEq Head] in
theorem activations_length_le (normal : NormalForm Head) :
    (activations normal).length ≤ normal.instances.length := by
  simpa only [activations, List.length_map] using
    eraseDups_length_le (normal.instances.map Instance.activation)

theorem normalize_instances_length (goals : List (Goal Head)) :
    (normalize goals).instances.length = goals.length := by
  simp [normalize]

/-- Count the actually computed cache entries. Each entry evaluates exactly
one relative derivative; ordered dispatch reuses that entry. These counts
exclude partitioning, prefix factoring, interning, lookup and allocation. -/
def stepCounted (normal : NormalForm Head) (observation : Observation Head) :
    NormalForm Head × Nat :=
  let cache := derivativeCache normal observation
  (normalize (dispatch normal cache), cache.length)

theorem stepCounted_result (normal : NormalForm Head) (observation : Observation Head) :
    (stepCounted normal observation).1 = step normal observation := rfl

theorem stepCounted_count (normal : NormalForm Head) (observation : Observation Head) :
    (stepCounted normal observation).2 = (activations normal).length := by
  simp [stepCounted, derivativeCache]

def executeCounted : List (Observation Head) → NormalForm Head → NormalForm Head × Nat
  | [], normal => (normal, 0)
  | observation :: observations, normal =>
      let next := stepCounted normal observation
      let after := executeCounted observations next.1
      (after.1, next.2 + after.2)

theorem executeCounted_result (observations : List (Observation Head))
    (normal : NormalForm Head) :
    (executeCounted observations normal).1 = execute observations normal := by
  induction observations generalizing normal with
  | nil => rfl
  | cons observation observations ih =>
      simp only [executeCounted, execute, ih, stepCounted_result]

/-- Normalization never increases the derivative-dispatch count relative
to the retained position-register machine. Total running time is a separate
question because normalization and cache lookup also perform work. -/
theorem executeCounted_dispatch_le (observations : List (Observation Head))
    (goals : List (Goal Head)) :
    (executeCounted observations (normalize goals)).2 ≤
      (TopDownMatchDerivatives.executeCounted observations goals).2 := by
  induction observations generalizing goals with
  | nil => exact Nat.le_refl _
  | cons observation observations ih =>
      simp only [executeCounted, TopDownMatchDerivatives.executeCounted,
        stepCounted_result, step_normalize, stepCounted_count]
      have current : (activations (normalize goals)).length ≤ goals.length := by
        simpa only [normalize_instances_length] using activations_length_le (normalize goals)
      exact Nat.add_le_add current (ih (deriveGoals observation goals))

/-- Matching executes the computed normal forms. The canonical matcher
appears only in the correctness theorem. -/
def run (patterns : List (Pattern Head)) (subject : Subject Head) : List Location :=
  let programs := patterns.map compile
  let observations := observe subject
  completed (expand (execute observations
    (normalize (observations.flatMap (fun observation => seed observation.position 0 programs)))))

theorem run_eq_topDown (patterns : List (Pattern Head)) (subject : Subject Head) :
    run patterns subject = TopDownMatchDerivatives.run patterns subject := by
  rw [run, expand_execute, expand_normalize]
  rfl

theorem run_eq_reference (patterns : List (Pattern Head)) (subject : Subject Head) :
    run patterns subject = reference patterns subject := by
  rw [run_eq_topDown, TopDownMatchDerivatives.run_eq_reference]

end

namespace Controls

/-- The first and last goals share an activation but carry distinct rule
occurrences. The middle goal shares the same relative control at a different
absolute subject position. -/
def interleaved : List (Goal Nat) :=
  [⟨⟨[1], 0⟩, [⟨[1, 0], ⟨7, 0⟩⟩, ⟨[1, 1], ⟨8, 0⟩⟩]⟩,
   ⟨⟨[2], 0⟩, [⟨[2, 0], ⟨7, 0⟩⟩, ⟨[2, 1], ⟨8, 0⟩⟩]⟩,
   ⟨⟨[1], 1⟩, [⟨[1, 0], ⟨7, 0⟩⟩, ⟨[1, 1], ⟨8, 0⟩⟩]⟩]

def inspected : List (Observation Nat) :=
  [⟨[1, 0], ⟨7, 0⟩⟩, ⟨[1, 1], ⟨8, 0⟩⟩,
   ⟨[2, 0], ⟨7, 0⟩⟩, ⟨[2, 1], ⟨8, 0⟩⟩]

theorem relative_control_shared : (normalize interleaved).controls.length = 1 := by
  decide +kernel

theorem ordered_instances_retained : (normalize interleaved).instances.length = 3 := by
  decide +kernel

theorem displaced_activations_distinct : (activations (normalize interleaved)).length = 2 := by
  decide +kernel

theorem shared_dispatch_count : (executeCounted inspected (normalize interleaved)).2 = 8 := by
  decide +kernel

theorem separate_dispatch_count :
    (TopDownMatchDerivatives.executeCounted inspected interleaved).2 = 12 := by
  decide +kernel

theorem provenance_and_order :
    completed (expand (execute inspected (normalize interleaved))) =
      [⟨[1], 0⟩, ⟨[2], 0⟩, ⟨[1], 1⟩] := by
  decide +kernel

/-- Factoring genuinely changes absolute paths into relative paths. -/
theorem nontrivial_displacement :
    (normalize interleaved).controls = [[⟨[0], ⟨7, 0⟩⟩, ⟨[1], ⟨8, 0⟩⟩]] := by
  decide +kernel

/-- Erasing occurrence provenance drops a valid duplicate derivation. -/
theorem position_dedup_loses_occurrence :
    (completed (expand (execute inspected (normalize interleaved)))).length ≠
      ((completed (expand (execute inspected (normalize interleaved)))).map
        Location.position).eraseDups.length := by
  decide +kernel

/-- Restoring relative announcements without their displacement corrupts
both legal subject positions, even though the control itself is shared. -/
theorem dropping_displacement_changes_announcements :
    (normalize interleaved).instances.map (fun entry => entry.announcement) ≠
      interleaved.map (fun goal => goal.location) := by
  decide +kernel

def dependencyChain : List (Goal Nat) :=
  [⟨⟨[], 0⟩, [⟨[0], ⟨7, 0⟩⟩]⟩,
   ⟨⟨[], 1⟩, [⟨[0], ⟨8, 0⟩⟩, ⟨[1], ⟨9, 0⟩⟩]⟩,
   ⟨⟨[], 2⟩, [⟨[1], ⟨10, 0⟩⟩]⟩]

/-- The middle goal joins a transitive chain despite conflicting keys;
the first and last goals have no direct shared inspection. -/
theorem transitive_dependency_joined :
    (dependencyComponents dependencyChain).length = 1 ∧
      overlaps dependencyChain[0] dependencyChain[2] = false := by
  decide +kernel

theorem contradictory_key_refused :
    completed (expand (execute [⟨[0], ⟨7, 0⟩⟩, ⟨[1], ⟨10, 0⟩⟩]
      (normalize dependencyChain))) = [⟨[], 0⟩, ⟨[], 2⟩] := by
  decide +kernel

def patterns : List (Pattern Nat) :=
  [.node 7 [], .wildcard, .node 7 []]

def subject : Subject Nat := .node 6 [.node 7 [], .node 8 []]

theorem compiled_nested_duplicates :
    run patterns subject =
      [⟨[], 1⟩, ⟨[0], 0⟩, ⟨[0], 1⟩, ⟨[0], 2⟩, ⟨[1], 1⟩] := by
  decide +kernel

theorem compiled_wrong_constructor_refused :
    run [.node 7 []] (.node 8 [] : Subject Nat) = [] := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.TopDownMatchDerivativeNormalization
