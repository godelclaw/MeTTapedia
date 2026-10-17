import Mettapedia.Languages.HOLLight.ArgumentListRendering
import Mettapedia.Languages.HOLLight.ArgumentVectorProgram
import Mettapedia.Computability.StackMachineDispatchProgram

/-!
# Executable table for original argument-list rendering

The original list framer, scalar/vector renderer and status writer execute
through the same composition proved in `ArgumentListRendering`. Explicit
physical key equality avoids enumeration of composite finite control states.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ArgumentListRendering.Program
open Turing
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef

local instance : Fintype (ArgumentVectorRendering.machine.Γ ArgumentVectorRendering.machine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (ArgumentVectorRendering.machine.Γ ArgumentVectorRendering.machine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Fintype ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def success : successMachine.Λ → TM2.Stmt successMachine.Γ successMachine.Λ successMachine.σ :=
  StackMachineComposition.Programs.body ArgumentVectorRendering.Program.resultKey
    WordTemplateMachine.Stack.input (.emit ⟨0, by decide⟩) (none : Option Alphabet) id
    ArgumentVectorRendering.Program.body (WordTemplateMachine.program statusTemplate)

theorem success_eq : successMachine.m = success := by
  unfold success
  rw [← ArgumentVectorRendering.Program.body_eq]
  exact (StackMachineComposition.body_eq ArgumentVectorRendering.machine
    (WordTemplateMachine.machine statusTemplate) (Equiv.refl (Option Alphabet))).symm

def successInitial : successMachine.σ :=
  ((ArgumentVectorRendering.Program.initial []).var, none, none)

theorem successInitial_eq : successInitial = successMachine.initialState := by
  unfold successInitial
  rw [ArgumentVectorRendering.Program.initial_eq]
  rfl

abbrev successInput : successMachine.K := some (.inl ArgumentVectorRendering.Program.inputKey)
abbrev successResult : successMachine.K := some (.inr WordTemplateMachine.Stack.input)

def dispatch : dispatched.Λ → TM2.Stmt dispatched.Γ dispatched.Λ dispatched.σ :=
  StackMachineComposition.Dispatch.Programs.body successInput successResult successInitial
    (.inl .scan) accept [some 0] success

theorem dispatch_eq : dispatched.m = dispatch := by
  unfold dispatch
  rw [successInitial_eq, ← success_eq]
  exact StackMachineComposition.Dispatch.Programs.body_eq successMachine accept [some 0]

def body (arity : Nat) : (machine arity).Λ →
    TM2.Stmt (machine arity).Γ (machine arity).Λ (machine arity).σ :=
  StackMachineComposition.Programs.body CertificateArgumentFraming.Execution.resultKey
    successInput .read (none : Option Alphabet) id
    (CertificateArgumentFraming.Execution.machine arity).m dispatch

theorem body_eq (arity : Nat) : (machine arity).m = body arity := by
  unfold body
  rw [← dispatch_eq]
  exact (StackMachineComposition.body_eq (CertificateArgumentFraming.Execution.machine arity)
    dispatched (Equiv.refl (Option Alphabet))).symm

def keyEquality (arity : Nat) : DecidableEq (machine arity).K := by
  letI : DecidableEq ArgumentVectorRendering.machine.K := ArgumentVectorRendering.Program.keyEquality
  letI : DecidableEq successMachine.K := inferInstanceAs
    (DecidableEq (Option (ArgumentVectorRendering.machine.K ⊕ WordTemplateMachine.Stack)))
  exact inferInstanceAs (DecidableEq (Option (CertificateArgumentFraming.Execution.Key ⊕ successMachine.K)))

def step (arity : Nat) : (machine arity).Cfg → Option (machine arity).Cfg :=
  @TM2.step (machine arity).K (machine arity).Γ (machine arity).Λ (machine arity).σ
    (keyEquality arity) (body arity)

theorem step_eq (arity : Nat) : step arity = (machine arity).step := by
  unfold step
  rw [show keyEquality arity = (machine arity).kDecidableEq from Subsingleton.elim _ _, ← body_eq]
  rfl

abbrev inputKey (arity : Nat) : (machine arity).K :=
  some (.inl CertificateArgumentFraming.Execution.inputKey)
abbrev resultKey (arity : Nat) : (machine arity).K := some (.inr successResult)

def initial (arity : Nat) (word : List Alphabet) : (machine arity).Cfg where
  l := some (.inl (.spine ⟨0, Nat.zero_lt_succ _⟩))
  var := ((none, none), (successInitial, none), none)
  stk key := @dite (List ((machine arity).Γ key)) (key = inputKey arity)
    (keyEquality arity key (inputKey arity)) (fun same => same.symm ▸ word) (fun _ => [])

theorem initial_eq (arity : Nat) (word : List Alphabet) :
    initial arity word = initList (machine arity) word := by
  have keys : keyEquality arity = (machine arity).kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [keys, successInitial_eq]
  unfold initList
  congr 1
  funext key
  cases key with
  | none => simp [inputKey, machine, StackMachineComposition.machine,
      StackMachineComposition.leftKey]
  | some key => cases key with
    | inr key => simp [inputKey, machine, StackMachineComposition.machine,
        StackMachineComposition.leftKey]
    | inl key =>
        by_cases same : key = CertificateArgumentFraming.Execution.inputKey
        · subst key
          simp [inputKey, machine, StackMachineComposition.machine,
            StackMachineComposition.leftKey, CertificateArgumentFraming.Execution.machine]
        · simp [inputKey, machine, StackMachineComposition.machine,
            StackMachineComposition.leftKey, CertificateArgumentFraming.Execution.machine] at same ⊢
          simp only [dif_neg same]

end Mettapedia.Languages.HOLLight.ArgumentListRendering.Program
