import Std

/-!
# Provider constraints over a captured view and a transaction overlay

The source column bindings are a prerequisite: nullable unique identities here
are complete, typed identities after affinity, not raw Python arguments. An
absent identity represents SQL NULL, whose occurrences do not conflict.

The implementation validates every planned edit before one atomic publication.
Latest overlay entries, including tombstones, shadow the captured view. These
results establish the logical invariant. Physical index completeness, CAV1
identity encoding, read-scope validation, C and filesystem behavior remain
separate obligations. The finite trace is replayed through the actual MeTTa
constraint/commit boundary and the SQLite reference.
-/

namespace Mettapedia.Machines.NativeProviderConstraints

abbrev Rows (α : Type) := Nat → Option α
abbrev Write (α : Type) := Nat × Option α

def replace {α : Type} (rows : Rows α) (key : Nat) (value : Option α) : Rows α :=
  fun other => if other = key then value else rows other

def unique {α κ : Type} (identity : α → Option κ) (rows : Rows α) : Prop :=
  ∀ first second a b tag, rows first = some a → rows second = some b →
    identity a = some tag → identity b = some tag → first = second

def noOther {α κ : Type} (identity : α → Option κ) (rows : Rows α)
    (target : Nat) (next : α) : Prop :=
  ∀ other old tag, rows other = some old → identity old = some tag →
    identity next = some tag → other = target

theorem null_identity_has_no_conflict {α κ : Type} (identity : α → Option κ)
    (rows : Rows α) (target : Nat) (next : α) (isNull : identity next = none) :
    noOther identity rows target next := by
  intro other old tag _ _ equal
  simp [isNull] at equal

theorem remove_preserves_unique {α κ : Type} (identity : α → Option κ)
    (rows : Rows α) (valid : unique identity rows) (target : Nat) :
    unique identity (replace rows target none) := by
  intro first second a b tag ha hb ia ib
  by_cases fa : first = target
  · simp [replace, fa] at ha
  by_cases sb : second = target
  · simp [replace, sb] at hb
  exact valid first second a b tag (by simpa [replace, fa] using ha)
    (by simpa [replace, sb] using hb) ia ib

theorem write_preserves_unique {α κ : Type} (identity : α → Option κ)
    (rows : Rows α) (valid : unique identity rows) (target : Nat) (next : α)
    (safe : noOther identity rows target next) :
    unique identity (replace rows target (some next)) := by
  intro first second a b tag ha hb ia ib
  by_cases fa : first = target
  · subst first
    have same : next = a := by simpa [replace] using ha
    subst a
    by_cases sb : second = target
    · exact sb.symm
    · exact (safe second b tag (by simpa [replace, sb] using hb) ib ia).symm
  · by_cases sb : second = target
    · subst second
      have same : next = b := by simpa [replace] using hb
      subst b
      exact safe first a tag (by simpa [replace, fa] using ha) ia ib
    · exact valid first second a b tag (by simpa [replace, fa] using ha)
        (by simpa [replace, sb] using hb) ia ib

def required {α : Type} (validRow : α → Prop) (rows : Rows α) : Prop :=
  ∀ key value, rows key = some value → validRow value

def replay {α : Type} : List (Write α) → Rows α → Rows α
  | [], rows => rows
  | (key, value) :: tail, rows => replay tail (replace rows key value)

def admissible {α κ : Type} (identity : α → Option κ) (validRow : α → Prop) :
    List (Write α) → Rows α → Prop
  | [], _ => True
  | (key, none) :: tail, rows => admissible identity validRow tail (replace rows key none)
  | (key, some value) :: tail, rows => validRow value ∧ noOther identity rows key value ∧
      admissible identity validRow tail (replace rows key (some value))

theorem accepted_plan_preserves_constraints {α κ : Type} (identity : α → Option κ)
    (validRow : α → Prop) (writes : List (Write α)) (rows : Rows α)
    (uniqueBefore : unique identity rows) (requiredBefore : required validRow rows)
    (checked : admissible identity validRow writes rows) :
    unique identity (replay writes rows) ∧ required validRow (replay writes rows) := by
  induction writes generalizing rows with
  | nil => exact ⟨uniqueBefore, requiredBefore⟩
  | cons entry tail ih =>
    rcases entry with ⟨key, value⟩
    cases value with
    | none =>
      apply ih (replace rows key none) (remove_preserves_unique identity rows uniqueBefore key)
      · intro other old equal
        by_cases same : other = key
        · simp [replace, same] at equal
        · exact requiredBefore other old (by simpa [replace, same] using equal)
      · exact checked
    | some next =>
      rcases checked with ⟨validNext, noDuplicate, rest⟩
      apply ih (replace rows key (some next))
        (write_preserves_unique identity rows uniqueBefore key next noDuplicate)
      · intro other old equal
        by_cases same : other = key
        · subst other
          have equalNext : next = old := by simpa [replace] using equal
          simpa [← equalNext] using validNext
        · exact requiredBefore other old (by simpa [replace, same] using equal)
      · exact rest

def overlayLookup {α : Type} : List (Write α) → Nat → Option (Option α)
  | [], _ => none
  | (key, value) :: tail, wanted => if wanted = key then some value else overlayLookup tail wanted

def effective {α : Type} (rows : Rows α) (overlay : List (Write α)) : Rows α :=
  fun key => match overlayLookup overlay key with
    | none => rows key
    | some value => value

theorem latest_overlay_write_shadows_history {α : Type} (rows : Rows α)
    (overlay : List (Write α)) (key : Nat) (value : Option α) :
    effective rows ((key, value) :: overlay) = replace (effective rows overlay) key value := by
  funext other
  by_cases same : other = key <;> simp [effective, overlayLookup, replace, same]

theorem tombstone_is_not_an_absent_observation {α : Type} (rows : Rows α)
    (overlay : List (Write α)) (key : Nat) :
    effective rows ((key, none) :: overlay) key = none := by
  simp [effective, overlayLookup]

-- The executable witness has two possible physical keys. The universal
-- preservation results above do not restrict the store to this universe.
def keys : List Nat := [1, 2]
def empty : Rows (Option Nat) := fun _ => none
def members (rows : Rows (Option Nat)) (tag : Nat) : List Nat :=
  keys.filter fun key => rows key == some (some tag)

def ready (rows : Rows (Option Nat)) (key : Nat) (identity : Option Nat) : Bool :=
  match identity with
  | none => true
  | some tag => (members rows tag).all fun other => other == key

def retained (before after : Rows (Option Nat)) (key : Nat) (identity : Option Nat) : Bool :=
  (before key == after key) && match identity with
    | none => true
    | some tag => members before tag == members after tag

def attempt (before after : Rows (Option Nat)) (key : Nat) (identity : Option Nat) : String :=
  if !ready before key identity then "duplicate"
  else if retained before after key identity then "accepted" else "conflict"

def withA := replace empty 1 (some (some 0))
def withNull := replace empty 1 (some none)

theorem invalid_intermediate_is_not_final_validation :
    ¬admissible id (fun _ => True) [(2, some (some 0)), (1, none)] withA ∧
    unique id (replay [(2, some (some 0)), (1, none)] withA) := by
  constructor
  · intro checked
    have impossible := checked.2.1 1 (some 0) 0 (by rfl) rfl rfl
    omega
  · have finalRows : replay [(2, some (some 0)), (1, none)] withA =
        replace empty 2 (some (some 0)) := by
      funext key
      by_cases first : key = 1 <;> by_cases second : key = 2 <;>
        simp [replay, replace, withA, empty, first, second]
    rw [finalRows]
    apply write_preserves_unique id empty
    · intro first second a b tag absent
      simp [empty] at absent
    · intro other old tag absent
      simp [empty] at absent

theorem retained_negative_witness :
    attempt empty empty 1 (some 0) = "accepted" ∧
    attempt empty withA 2 (some 1) = "accepted" ∧
    attempt empty withA 2 (some 0) = "conflict" ∧
    attempt withA withA 2 (some 0) = "duplicate" ∧
    attempt empty withNull 2 none = "accepted" := by decide

def trace : String :=
  s!"PROVIDER_CONSTRAINT_TRACE {attempt empty empty 1 (some 0)} {attempt empty withA 2 (some 1)} {attempt empty withA 2 (some 0)} {attempt withA withA 2 (some 0)} {attempt empty withNull 2 none}"

end Mettapedia.Machines.NativeProviderConstraints

#eval IO.println Mettapedia.Machines.NativeProviderConstraints.trace
