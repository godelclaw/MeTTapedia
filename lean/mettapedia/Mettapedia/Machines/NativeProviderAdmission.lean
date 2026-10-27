import Std

/-!
# Native provider admission deadlines

Admission is a local transition, separate from submitting an external
request. The managed profile observes a provider's transport deadline; the
upstream profile bypasses that deadline. Neither imposes a work quota.

Time is an explicit integer in one declared unit. A missing deadline is not
zero. The host clock, authorization, complete read footprints and atomic
receipt publication are separate obligations. These laws describe the pure
deadline decision; they do not prove the interpreter or native storage.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeProviderAdmission

inductive Profile where
  | managed | upstream
  deriving DecidableEq, Repr

inductive Decision where
  | eligible
  | deferred (remaining : Int)
  | invalidMaximum
  deriving DecidableEq, Repr

def decide (profile : Profile) (now : Int) (deadline : Option Int)
    (maximumOutput : Nat) : Decision :=
  if maximumOutput = 0 then .invalidMaximum
  else match profile, deadline with
    | .managed, some boundary =>
        if now < boundary then .deferred (boundary - now) else .eligible
    | _, _ => .eligible

/-- Each report is retained by its application receipt. The current deadline
holds the later boundary, independently of the order reports arrive in. -/
def extend (current : Option Int) (proposed : Int) : Int :=
  match current with
  | none => proposed
  | some boundary => max boundary proposed

theorem invalid_maximum_is_rejected (profile : Profile) (now : Int)
    (deadline : Option Int) : decide profile now deadline 0 = .invalidMaximum := by
  simp [decide]

theorem upstream_bypasses_deadline (now : Int) (deadline : Option Int)
    (maximum : Nat) (positive : maximum ≠ 0) :
    decide .upstream now deadline maximum = .eligible := by
  simp [decide, positive]

theorem absent_deadline_is_eligible (profile : Profile) (now : Int)
    (maximum : Nat) (positive : maximum ≠ 0) :
    decide profile now none maximum = .eligible := by
  cases profile <;> simp [decide, positive]

theorem managed_before_deadline_is_deferred (now boundary : Int)
    (maximum : Nat) (positive : maximum ≠ 0) (before : now < boundary) :
    decide .managed now (some boundary) maximum = .deferred (boundary - now) := by
  simp [decide, positive, before]

theorem managed_at_deadline_is_eligible (now : Int)
    (maximum : Nat) (positive : maximum ≠ 0) :
    decide .managed now (some now) maximum = .eligible := by
  simp [decide, positive]

theorem managed_after_deadline_is_eligible (now boundary : Int)
    (maximum : Nat) (positive : maximum ≠ 0) (expired : ¬ now < boundary) :
    decide .managed now (some boundary) maximum = .eligible := by
  simp [decide, positive, expired]

theorem deferred_duration_is_positive (profile : Profile) (now : Int)
    (deadline : Option Int) (maximum : Nat) (remaining : Int)
    (deferred : decide profile now deadline maximum = .deferred remaining) :
    0 < remaining := by
  by_cases maximumZero : maximum = 0
  · simp [decide, maximumZero] at deferred
  · cases profile with
    | upstream => simp [decide, maximumZero] at deferred
    | managed =>
      cases deadline with
      | none => simp [decide, maximumZero] at deferred
      | some boundary =>
        by_cases before : now < boundary
        · have same : boundary - now = remaining := by
            simpa [decide, maximumZero, before] using deferred
          omega
        · simp [decide, maximumZero, before] at deferred

theorem absent_deadline_differs_from_zero :
    decide .managed (-1) none 1 = .eligible ∧
    decide .managed (-1) (some 0) 1 = .deferred 1 := by decide

theorem deadline_does_not_impose_a_maximum_quota (profile : Profile) (now : Int)
    (deadline : Option Int) (first second : Nat)
    (firstPositive : first ≠ 0) (secondPositive : second ≠ 0) :
    decide profile now deadline first = decide profile now deadline second := by
  simp [decide, firstPositive, secondPositive]

theorem first_deadline_is_preserved (proposed : Int) : extend none proposed = proposed := rfl

theorem extension_never_shortens (current proposed : Int) :
    current ≤ extend (some current) proposed := by
  exact Int.le_max_left _ _

theorem proposed_deadline_is_covered (current : Option Int) (proposed : Int) :
    proposed ≤ extend current proposed := by
  cases current with
  | none => exact Int.le_refl _
  | some boundary => exact Int.le_max_right _ _

theorem extension_is_idempotent (current proposed : Int) :
    extend (some (extend (some current) proposed)) proposed = extend (some current) proposed := by
  simp only [extend]
  omega

theorem extensions_commute (current first second : Int) :
    extend (some (extend (some current) first)) second =
      extend (some (extend (some current) second)) first := by
  simp only [extend]
  omega

theorem earlier_report_cannot_erase_deadline (current earlier : Int) (old : earlier ≤ current) :
    extend (some current) earlier = current := by
  simp only [extend]
  omega

/-- The trace is replayed against the actual MeTTa deadline function. Large
timestamps separate exact integer comparisons from binary64 rounding. -/
def traceCases : List (Profile × Int × Option Int × Nat) :=
  [ (.managed, 10, none, 100),
    (.managed, 10, some 11, 100),
    (.managed, 11, some 11, 100),
    (.managed, 12, some 11, 100),
    (.upstream, 10, some 11, 100),
    (.upstream, 10, none, 0),
    (.managed, -1, some 0, 1),
    (.managed, -1, none, 1),
    (.managed, 100000000000000000000, some 100000000000000000001, 1),
    (.managed, 100000000000000000001, some 100000000000000000001, 1) ]

def label : Decision → String
  | .eligible => "eligible"
  | .invalidMaximum => "invalid-maximum"
  | .deferred remaining => "deferred:" ++ toString remaining

def trace : String :=
  "NATIVE_ADMISSION_DEADLINES " ++ String.intercalate " "
    (traceCases.map fun (profile, now, deadline, maximum) => label (decide profile now deadline maximum))

def inputTrace : String :=
  "NATIVE_ADMISSION_INPUTS " ++ String.intercalate " "
    (traceCases.map fun (profile, now, deadline, maximum) =>
      (match profile with | .managed => "managed" | .upstream => "upstream") ++ "," ++
      toString now ++ "," ++ (match deadline with | none => "none" | some value => toString value) ++
      "," ++ toString maximum)

def extensionCases : List Int :=
  [100, 50, 200, 200, -1, 100000000000000000001, 100000000000000000000]

def extensionLines (current : Option Int) : List Int → List String
  | [] => []
  | proposed :: rest =>
      let boundary := extend current proposed
      (toString proposed ++ ":" ++ toString boundary) :: extensionLines (some boundary) rest

def extensionTrace : String :=
  "NATIVE_ADMISSION_EXTENSIONS " ++ String.intercalate " " (extensionLines none extensionCases)

end Mettapedia.Machines.NativeProviderAdmission

#eval IO.println Mettapedia.Machines.NativeProviderAdmission.trace
#eval IO.println Mettapedia.Machines.NativeProviderAdmission.inputTrace
#eval IO.println Mettapedia.Machines.NativeProviderAdmission.extensionTrace
