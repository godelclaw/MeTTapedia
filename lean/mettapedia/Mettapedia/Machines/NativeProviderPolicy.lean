import Std

/-!
# Provider configuration without a storage dependency

The fields below are decoded configuration observations. Missing is distinct
from present-but-invalid. Profile precedence is mode > environment > file;
cooldown precedence is environment > mode > file. A malformed selected value
does not silently remove policy. No work quota is introduced.

Filesystem observation, JSON decoding and environment acquisition remain
boundary obligations. This model is a small contract for the native reader,
not a proof of those I/O implementations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeProviderPolicy

inductive Field (α : Type) where
  | absent | value (data : α) | invalid
  deriving DecidableEq, Repr

def choose {α : Type} (first second third : Field α) (fallback : α) : Field α :=
  match first with
  | .absent => match second with
    | .absent => match third with | .absent => .value fallback | other => other
    | other => other
  | other => other

structure Input where
  mode : String := "godelclaw"
  modeProfile : Field String := .absent
  envProfile : Field String := .absent
  fileProfile : Field String := .absent
  envDelay : Field Int := .absent
  modeDelay : Field Int := .absent
  fileDelay : Field Int := .absent
  validObjects : Bool := true
  deriving Repr

inductive Result where
  | policy (profile : String) (cooldownNs : Int)
  | refused
  deriving DecidableEq, Repr

def defaultProfile (mode : String) : String :=
  if mode = "iter" ∨ mode = "omega" then "upstream" else "managed"

def resolve (input : Input) : Result :=
  if !input.validObjects then .refused
  else match choose input.modeProfile input.envProfile input.fileProfile (defaultProfile input.mode),
             choose input.envDelay input.modeDelay input.fileDelay 300 with
    | .value profile, .value seconds =>
        if (profile = "managed" ∨ profile = "upstream") ∧ 0 ≤ seconds then
          .policy profile (seconds * 1000000000)
        else .refused
    | _, _ => .refused

theorem highest_priority_value_wins {α : Type} (value fallback : α) (second third : Field α) :
    choose (.value value) second third fallback = .value value := rfl

theorem invalid_selected_value_does_not_fall_back {α : Type} (fallback : α) (second third : Field α) :
    choose .invalid second third fallback = .invalid := rfl

theorem missing_fields_reach_default {α : Type} (fallback : α) :
    choose .absent .absent .absent fallback = .value fallback := rfl

theorem mode_profile_precedes_environment (input : Input) (profile : String) :
    choose (.value profile) input.envProfile input.fileProfile (defaultProfile input.mode) =
      .value profile := rfl

theorem environment_delay_precedes_mode (input : Input) (seconds : Int) :
    choose (.value seconds) input.modeDelay input.fileDelay 300 = .value seconds := rfl

theorem malformed_objects_are_refused (input : Input) :
    resolve { input with validObjects := false } = .refused := rfl

theorem invalid_mode_profile_is_refused (input : Input) :
    resolve { input with modeProfile := .invalid } = .refused := by
  simp [resolve, choose]

theorem invalid_environment_delay_is_refused (input : Input) :
    resolve { input with envDelay := .invalid } = .refused := by
  simp [resolve, choose]

theorem negative_environment_delay_is_refused (input : Input) (seconds : Int) (negative : seconds < 0) :
    resolve { input with envDelay := .value seconds } = .refused := by
  simp only [resolve, choose]
  split
  · rfl
  · split <;> simp_all

theorem successful_delay_is_nonnegative (input : Input) (profile : String) (ns : Int)
    (success : resolve input = .policy profile ns) : 0 ≤ ns := by
  unfold resolve at success
  split at success
  · cases success
  · split at success
    · split at success
      · obtain ⟨_, rfl⟩ := Result.policy.inj success
        rename_i condition
        omega
      · cases success
    · cases success

theorem default_turn_policy : resolve {} = .policy "managed" 300000000000 := by decide
theorem default_iter_policy : resolve { mode := "iter" } = .policy "upstream" 300000000000 := by decide
theorem default_omega_policy : resolve { mode := "omega" } = .policy "upstream" 300000000000 := by decide

def traceCases : List Input :=
  [ {}, { mode := "iter" }, { mode := "omega" },
    { fileProfile := .value "upstream", fileDelay := .value 7 },
    { fileProfile := .value "upstream", envProfile := .value "managed" },
    { modeProfile := .value "upstream", envProfile := .value "managed", modeDelay := .value 3 },
    { envDelay := .value 2, modeDelay := .value 3, fileDelay := .value 4 },
    { envDelay := .value 0 }, { envDelay := .value (-1) },
    { modeProfile := .invalid, envProfile := .value "managed" },
    { envProfile := .value "", fileProfile := .value "managed" },
    { validObjects := false }, { envDelay := .value 100000000000000000000 } ]

def label : Result → String
  | .refused => "refused"
  | .policy profile ns => profile ++ ":" ++ toString ns

def trace : String :=
  "NATIVE_PROVIDER_POLICY " ++ String.intercalate " " (traceCases.map (fun input => label (resolve input)))

end Mettapedia.Machines.NativeProviderPolicy

#eval IO.println Mettapedia.Machines.NativeProviderPolicy.trace
