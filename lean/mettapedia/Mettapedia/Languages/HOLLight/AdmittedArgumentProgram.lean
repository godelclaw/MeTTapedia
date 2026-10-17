import Mettapedia.Languages.HOLLight.AdmittedArgumentRendering
import Mettapedia.Computability.RetainedWordProgram

/-!
# Executable table of the admitted argument renderer

The command table is equal to the machine qualified in
`AdmittedArgumentRendering`. Exposing the original component programs avoids
evaluating finite control-state enumeration witnesses during native execution.
No alternative admission predicate or argument renderer is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedArgumentRendering.Program

open Turing Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary
open ArgumentRenderingMachine
open Mettapedia.GSLT.LanguageDef.PatternScopeExecution

local instance : Fintype (scopeMachine.Γ scopeMachine.k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (scopeMachine.Γ scopeMachine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (savedMachine.Γ savedMachine.k₁) :=
  inferInstanceAs (Fintype (Alphabet ⊕ Bool))
local instance : Inhabited (savedMachine.Γ savedMachine.k₁) :=
  inferInstanceAs (Inhabited (Alphabet ⊕ Bool))
local instance : Fintype (admittedMachine.Γ admittedMachine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (admittedMachine.Γ admittedMachine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def saved : savedMachine.Λ → TM2.Stmt savedMachine.Γ savedMachine.Λ savedMachine.σ :=
  RetainedWordExecution.Programs.body (Cells := scopeMachine.Γ)
    (some (.inl (some (.inl (some .input))))) (some (.inr .result))
    (OriginalAdmission.initialConfig []).var (.inl (.inl (.visit .start)))
    (0 : Alphabet) false readResult OriginalAdmission.program

theorem saved_eq : savedMachine.m = saved := by
  unfold saved
  rw [OriginalAdmission.program_eq]
  exact (RetainedWordExecution.Programs.body_eq scopeMachine readResult).symm

def admitted : admittedMachine.Λ → TM2.Stmt admittedMachine.Γ admittedMachine.Λ admittedMachine.σ :=
  StackMachineComposition.Programs.body none WordHomomorphismMachine.Stack.input
    WordHomomorphismMachine.Phase.read (default : Alphabet ⊕ Bool) id
    saved (WordHomomorphismMachine.program project)

theorem admitted_eq : admittedMachine.m = admitted := by
  unfold admitted
  rw [← saved_eq]
  exact (StackMachineComposition.body_eq savedMachine
    (WordHomomorphismMachine.machine project) (Equiv.refl _)).symm

abbrev fullInput : Full.machine.K := some (.inl (some (.inl (some (some .input)))))

def fullInitial : Full.machine.σ :=
  ((Routing.Traversal.initial, Routing.registers Routing.initial, none), Execution.initial, none)

def rendered : renderingMachine.Λ → TM2.Stmt renderingMachine.Γ renderingMachine.Λ renderingMachine.σ
  | .run label => StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run
      (Full.program label)
  | .read => pop fullInput (fun state value => (state.1, value))
      (branch (fun state => state.2.any accept)
        (load (fun state => (state.1, none))
          (goto fun _ => .run (.inl (.inl (.visit (.visit .start))))))
        (goto fun _ => .discard))
  | .discard => pop fullInput (fun state value => (state.1, value))
      (branch (fun state => state.2.isSome) (goto fun _ => .discard)
        (load (fun _ => (fullInitial, none)) halt))

private theorem dispatch_lift (statement : Full.machine.Stmt) :
    StackMachineComposition.Dispatch.lift Full.machine statement =
      StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run statement := by
  induction statement <;>
    simp_all only [StackMachineComposition.Dispatch.lift, StackMachineRegisters.extend]

theorem rendered_eq : renderingMachine.m = rendered := by
  funext phase
  cases phase with
  | read => rfl
  | discard => rfl
  | run label =>
      change StackMachineComposition.Dispatch.lift Full.machine (Full.machine.m label) = _
      rw [dispatch_lift, Full.program_eq]
      rfl

def body : machine.Λ → TM2.Stmt machine.Γ machine.Λ machine.σ :=
  StackMachineComposition.Programs.body (FirstAlphabet := admittedMachine.Γ)
    (some (.inr WordHomomorphismMachine.Stack.result))
    fullInput StackMachineComposition.Dispatch.Phase.read (0 : Alphabet) id admitted rendered

theorem body_eq : machine.m = body := by
  unfold body
  rw [← admitted_eq, ← rendered_eq]
  exact (StackMachineComposition.body_eq admittedMachine renderingMachine (Equiv.refl _)).symm

/-- Equality uses only the finite physical stack keys, not the product of
all control registers. Component instances are supplied explicitly so that
instance synthesis cannot project them from a packaged finite machine. -/
def keyEquality : DecidableEq machine.K := by
  letI : DecidableEq scopeMachine.K := OriginalAdmission.keyEquality
  letI : DecidableEq savedMachine.K :=
    inferInstanceAs (DecidableEq (Option (Option (Option scopeMachine.K))))
  letI : DecidableEq admittedMachine.K :=
    inferInstanceAs (DecidableEq (Option (savedMachine.K ⊕ WordHomomorphismMachine.Stack)))
  letI : DecidableEq Routing.Traversal.Key :=
    inferInstanceAs (DecidableEq (Option (Option
      Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.Stack)))
  letI : DecidableEq Routing.Pipeline.machine.K :=
    inferInstanceAs (DecidableEq (Option (Routing.Traversal.Key ⊕ Routing.Key)))
  letI : DecidableEq renderingMachine.K :=
    inferInstanceAs (DecidableEq (Option (Routing.Pipeline.machine.K ⊕ Execution.Key)))
  exact inferInstanceAs (DecidableEq (Option (admittedMachine.K ⊕ renderingMachine.K)))

def step : machine.Cfg → Option machine.Cfg :=
  @TM2.step machine.K machine.Γ machine.Λ machine.σ keyEquality body

theorem step_eq : step = machine.step := by
  unfold step
  rw [show keyEquality = machine.kDecidableEq from Subsingleton.elim _ _, ← body_eq]
  rfl

abbrev inputKey : machine.K :=
  some (.inl (some (.inl (some (some (some
    (some (.inl (some (.inl (some .input)))))))))))

abbrev resultKey : machine.K := some (.inr (some (.inr Execution.Key.result)))

def initial (word : List Alphabet) : machine.Cfg where
  l := some (.inl (.inl .scan))
  var := ((((OriginalAdmission.initialConfig []).var, none, none, false), (none, none), none),
    (fullInitial, none), none)
  stk key := @dite (List (machine.Γ key)) (key = inputKey) (keyEquality key inputKey)
    (fun same => same.symm ▸ word) (fun _ => [])

theorem initial_eq (word : List Alphabet) : initial word = initList machine word := by
  have keys : keyEquality = machine.kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [keys]
  unfold initList
  congr 1
  funext key
  by_cases same : key = inputKey
  · subst key; simp [show inputKey = machine.k₀ from rfl]
  · have different : key ≠ machine.k₀ := same
    simp only [same, different, dite_false]

end Mettapedia.Languages.HOLLight.AdmittedArgumentRendering.Program
