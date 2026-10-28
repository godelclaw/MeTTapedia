import Mettapedia.Machines.ContextualCBPV

/-!
# Direct entry into a parameterized computation body

The source binds an ordered list of distinct parameter identities to ready
values. The target initializes positional slots and leaves the remaining local
slots empty. The compiler's parameter-position map reads those slots. Neither
entry manufactures a named equation or interprets a ready operand.

The environment refinement joins entry to the existing contextual CBPV machine
for every physical slice. It does not prove the complete C compiler, native
pointer ownership, source-fuel accounting or mutable-source admission.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ParameterizedBodyEntry

variable {Name Value : Type} [DecidableEq Name]

abbrev Environment (Name Value : Type) := Name → Option Value

def locate (name : Name) : List Name → Option Nat
  | [] => none
  | first :: rest => if name = first then some 0 else (locate name rest).map Nat.succ

def slots (values : List Value) (locals : Nat) : List (Option Value) :=
  values.map some ++ List.replicate locals none

def source (parameters : List Name) (values : List Value) : Environment Name Value :=
  fun name => (parameters.zip values).lookup name

def target (parameters : List Name) (values : List Value) (locals : Nat) :
    Environment Name Value :=
  fun name => (locate name parameters).bind fun index => ((slots values locals)[index]?).join

def admitted (parameters : List Name) (values : List Value) : Bool :=
  decide (parameters.Nodup ∧ parameters.length = values.length)

theorem slots_prefix (values : List Value) (locals : Nat) :
    (slots values locals).take values.length = values.map some := by
  simp [slots]

theorem source_target_read (parameters : List Name) (values : List Value)
    (locals : Nat) (lengths : parameters.length = values.length) (name : Name) :
    source parameters values name = target parameters values locals name := by
  induction parameters generalizing values with
  | nil => cases values <;> simp_all [source, target, locate]
  | cons parameter rest ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          have restLengths : rest.length = values.length := by simpa using lengths
          by_cases same : name = parameter
          · subst name
            simp [source, target, locate, slots]
          · have previous := ih values restLengths
            have different : (name == parameter) = false := beq_eq_false_iff_ne.mpr same
            simp only [source, List.zip_cons_cons, List.lookup_cons, different]
            change source rest values name = _
            rw [previous]
            cases found : locate name rest <;>
              simp [target, locate, same, slots, found]

theorem environments_refine (parameters : List Name) (values : List Value)
    (locals : Nat) (lengths : parameters.length = values.length) :
    source parameters values = target parameters values locals := by
  funext name
  exact source_target_read parameters values locals lengths name

theorem admission_lengths (parameters : List Name) (values : List Value)
    (accepted : admitted parameters values = true) :
    parameters.length = values.length := by
  exact (of_decide_eq_true accepted).2

theorem admitted_environment_refines (parameters : List Name) (values : List Value)
    (locals : Nat) (accepted : admitted parameters values = true) :
    source parameters values = target parameters values locals := by
  exact environments_refine parameters values locals (admission_lengths parameters values accepted)

section Kernel

variable {Call Effect Fault Delay Suspension World Worker : Type}

abbrev Code := ContextualCBPV.Code Value Call Effect Fault Delay Suspension

variable (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension
    (Environment Name Value) World Worker)
    (world : World) (parameters : List Name) (values : List Value) (locals : Nat)
    (elaborate : Environment Name Value → Code (Value := Value) (Call := Call)
      (Effect := Effect) (Fault := Fault) (Delay := Delay) (Suspension := Suspension))

theorem kernel_entry_refines (lengths : parameters.length = values.length) :
    ContextualCBPV.initial (Worker := Worker) world (source parameters values)
        (elaborate (source parameters values)) =
      ContextualCBPV.initial (Worker := Worker) world (target parameters values locals)
        (elaborate (target parameters values locals)) := by
  rw [environments_refine parameters values locals lengths]

theorem kernel_slice_refines (lengths : parameters.length = values.length)
    (allowance : Nat) :
    (ContextualCBPV.core sem world (source parameters values)).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world (source parameters values)
          (elaborate (source parameters values))) =
      (ContextualCBPV.core sem world (target parameters values locals)).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world (target parameters values locals)
          (elaborate (target parameters values locals))) := by
  rw [environments_refine parameters values locals lengths]

end Kernel

namespace Controls

theorem distinct_parameters_preserve_shared_values :
    target ["x", "y"] [7, 7] 4 "x" = some 7 ∧
      target ["x", "y"] [7, 7] 4 "y" = some 7 := by decide +kernel

theorem distinct_parameters_are_not_collapsed :
    target ["x", "y"] [7, 9] 4 "x" = some 7 ∧
      target ["x", "y"] [7, 9] 4 "y" = some 9 := by decide +kernel

theorem duplicate_parameters_refused :
    admitted ["x", "x"] [7, 9] = false := by decide +kernel

theorem missing_argument_refused :
    admitted ["x", "y"] [7] = false := by decide +kernel

theorem fresh_local_is_not_a_parameter :
    target ["x"] [7] 16 "unbound" = none := by decide +kernel

end Controls
end Mettapedia.Machines.ParameterizedBodyEntry
