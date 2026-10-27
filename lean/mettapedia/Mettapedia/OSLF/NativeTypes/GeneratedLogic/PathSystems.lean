import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalAnswerFrontDoor

/-!
# Listed transition systems at the front door, by their paths

A consumer's configurations may carry proofs or functions, with no encoding as patterns. When its successors are
listed (`Listed`), the system is still asked at the front door: a configuration is reached from a root by a path of
successor positions (`reach`), and the paths are encoded as closed patterns (`pathPattern`), so the unfolding from the
root is a system on an encoded carrier (`unfolded`).

- **`◇` at a path ranges over the successors** of the configuration it reaches (`sat_possibly_iff`), and `□` likewise
  (`sat_necessarily_iff`).
- **The observations are the configuration's** (`sat_observe_iff`).
- So "some successor of the root has the observation" is `◇(inRelation name)` at the root (`sat_possibly_observe_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open RelationalAnswers (positionPattern patternPosition? patternPosition?_positionPattern isObjectPatternList_marks
  isWellScopedListAt_marks)

/-- **A transition system with listed successors** and Boolean observations. -/
structure Listed (Configuration : Type) where
  successors : Configuration → List Configuration
  observations : String → Configuration → Bool

/-! ## Paths as patterns -/

/-- A path of successor positions as a closed pattern: the vector of its positions. -/
def pathPattern (path : List ℕ) : Pattern := .collection .vec (path.map positionPattern) none

/-- The path a pattern names. -/
def patternPath? : Pattern → Option (List ℕ)
  | .collection .vec elements none => elements.mapM patternPosition?
  | _ => none

theorem mapM_positions : ∀ path : List ℕ, (path.map positionPattern).mapM patternPosition? = some path
  | [] => rfl
  | position :: path => by
    simp only [List.map_cons, List.mapM_cons, patternPosition?_positionPattern, mapM_positions path]
    rfl

theorem patternPath?_pathPattern (path : List ℕ) : patternPath? (pathPattern path) = some path :=
  mapM_positions path

theorem isObjectPattern_positionPattern (position : ℕ) : isObjectPattern (positionPattern position) = true := by
  simp [positionPattern, isObjectPattern, isObjectPatternList_marks]

theorem isWellScopedAt_positionPattern (position : ℕ) : (positionPattern position).isWellScopedAt 0 = true := by
  simp [positionPattern, Pattern.isWellScopedAt, isWellScopedListAt_marks]

theorem isObjectPatternList_positions : ∀ path : List ℕ, isObjectPatternList (path.map positionPattern) = true
  | [] => rfl
  | position :: path => by
    simp only [List.map_cons, isObjectPatternList, isObjectPattern_positionPattern, Bool.true_and]
    exact isObjectPatternList_positions path

theorem isWellScopedListAt_positions : ∀ path : List ℕ,
    Pattern.isWellScopedListAt 0 (path.map positionPattern) = true
  | [] => rfl
  | position :: path => by
    simp only [List.map_cons, Pattern.isWellScopedListAt, isWellScopedAt_positionPattern, Bool.true_and]
    exact isWellScopedListAt_positions path

theorem state_pathPattern (path : List ℕ) : IsState (pathPattern path) :=
  ⟨by simp [pathPattern, Pattern.isWellScopedAt, isWellScopedListAt_positions],
    by simp [pathPattern, IsObject, isObjectPattern, isObjectPatternList_positions]⟩

/-! ## The unfolding from a root -/

namespace Listed

variable {Configuration : Type} (system : Listed Configuration) (root : Configuration)

/-- **The configuration a path reaches** from the root, following successor positions. -/
def reach (path : List ℕ) : Option Configuration :=
  path.foldl (fun reached position => reached.bind fun configuration => (system.successors configuration)[position]?)
    (some root)

theorem reach_nil : system.reach root [] = some root := rfl

theorem reach_append (path : List ℕ) (position : ℕ) :
    system.reach root (path ++ [position]) =
      (system.reach root path).bind fun configuration => (system.successors configuration)[position]? := by
  simp [reach, List.foldl_append]

/-- The successor paths of a path: one for each successor of the configuration it reaches. -/
def pathSuccessors (path : List ℕ) : List (List ℕ) :=
  match system.reach root path with
  | some configuration => (List.range (system.successors configuration).length).map (path ++ [·])
  | none => []

/-- The observations at a path: those of the configuration it reaches. -/
def pathObservations (name : String) (path : List ℕ) : Bool :=
  match system.reach root path with
  | some configuration => system.observations name configuration
  | none => false

/-- **The unfolding from a root**, on paths encoded as patterns. -/
def unfolded : EncodedSystem (List ℕ) where
  encode := pathPattern
  decode := patternPath?
  decode_encode := patternPath?_pathPattern
  state := state_pathPattern
  successors := system.pathSuccessors root
  observations := system.pathObservations root

theorem mem_pathSuccessors {path : List ℕ} {configuration : Configuration}
    (reached : system.reach root path = some configuration) {next : List ℕ} :
    next ∈ system.pathSuccessors root path ↔
      ∃ position < (system.successors configuration).length, next = path ++ [position] := by
  simp only [pathSuccessors, reached, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨position, below, rfl⟩
    exact ⟨position, below, rfl⟩
  · rintro ⟨position, below, rfl⟩
    exact ⟨position, below, rfl⟩

/-- **`◇` at a path ranges over the successors** of the configuration it reaches. -/
theorem sat_possibly_iff {n : ℕ} (env : Env Pattern n) (formula : Formula n) {path : List ℕ}
    {configuration : Configuration} (reached : system.reach root path = some configuration) :
    (system.unfolded root).observed.reading.sat env (.possibly .any formula) (pathPattern path) ↔
      ∃ position < (system.successors configuration).length,
        (system.unfolded root).observed.reading.sat env formula (pathPattern (path ++ [position])) := by
  change (system.unfolded root).observed.reading.sat env (.possibly .any formula) ((system.unfolded root).encode path) ↔ _
  rw [EncodedSystem.sat_possibly_encode_iff]
  constructor
  · rintro ⟨next, member, holds⟩
    obtain ⟨position, below, rfl⟩ := (system.mem_pathSuccessors root reached).mp member
    exact ⟨position, below, holds⟩
  · rintro ⟨position, below, holds⟩
    exact ⟨path ++ [position], (system.mem_pathSuccessors root reached).mpr ⟨position, below, rfl⟩, holds⟩

/-- **`□` at a path ranges over the successors** of the configuration it reaches. -/
theorem sat_necessarily_iff {n : ℕ} (env : Env Pattern n) (formula : Formula n) {path : List ℕ}
    {configuration : Configuration} (reached : system.reach root path = some configuration) :
    (system.unfolded root).observed.reading.sat env (.necessarily .any formula) (pathPattern path) ↔
      ∀ position < (system.successors configuration).length,
        (system.unfolded root).observed.reading.sat env formula (pathPattern (path ++ [position])) := by
  change (system.unfolded root).observed.reading.sat env (.necessarily .any formula)
    ((system.unfolded root).encode path) ↔ _
  rw [EncodedSystem.sat_necessarily_encode_iff]
  constructor
  · intro every position below
    exact every _ ((system.mem_pathSuccessors root reached).mpr ⟨position, below, rfl⟩)
  · intro every next member
    obtain ⟨position, below, rfl⟩ := (system.mem_pathSuccessors root reached).mp member
    exact every position below

/-- **The observations at a path are the configuration's.** -/
theorem sat_observe_iff (name : String) {path : List ℕ} {configuration : Configuration}
    (reached : system.reach root path = some configuration) :
    (system.unfolded root).observed.reading.sat Env.closed (.inRelation name) (pathPattern path) ↔
      system.observations name configuration = true := by
  change (system.unfolded root).observed.reading.sat Env.closed (.inRelation name) ((system.unfolded root).encode path) ↔ _
  rw [EncodedSystem.sat_observe_encode_iff]
  change system.pathObservations root name path = true ↔ _
  simp only [pathObservations, reached]

/-- **Some successor of the root has the observation** is `◇(inRelation name)` at the root. -/
theorem sat_possibly_observe_iff (name : String) :
    (system.unfolded root).observed.reading.sat Env.closed (.possibly .any (.inRelation name)) (pathPattern []) ↔
      ∃ next ∈ system.successors root, system.observations name next = true := by
  rw [system.sat_possibly_iff root Env.closed _ (system.reach_nil root)]
  constructor
  · rintro ⟨position, below, holds⟩
    have reached : system.reach root ([] ++ [position]) = some ((system.successors root)[position]) := by
      rw [system.reach_append, system.reach_nil]
      simp [below]
    exact ⟨_, List.getElem_mem below, (system.sat_observe_iff root name reached).mp holds⟩
  · rintro ⟨next, member, observed⟩
    obtain ⟨position, below, rfl⟩ := List.getElem_of_mem member
    have reached : system.reach root ([] ++ [position]) = some ((system.successors root)[position]) := by
      rw [system.reach_append, system.reach_nil]
      simp [below]
    exact ⟨position, below, (system.sat_observe_iff root name reached).mpr observed⟩

end Listed

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems
