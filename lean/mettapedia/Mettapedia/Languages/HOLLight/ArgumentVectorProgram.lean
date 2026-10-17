import Mettapedia.Languages.HOLLight.ArgumentVectorRendering
import Mettapedia.Computability.FramedWordMappingProgram

/-!
# Executable table for the complete argument vector renderer

The table exposes the original framed caller and scalar renderer, with proved
equality to the qualified machine. Physical stack equality is constructed
directly, avoiding enumeration of the product of finite control registers.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ArgumentVectorRendering.Program
open Turing
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary

local instance : Fintype (AdmittedArgumentRendering.machine.Γ AdmittedArgumentRendering.machine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (AdmittedArgumentRendering.machine.Γ AdmittedArgumentRendering.machine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (AdmittedArgumentRendering.machine.Γ AdmittedArgumentRendering.machine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def body : machine.Λ → TM2.Stmt machine.Γ machine.Λ machine.σ :=
  FramedWordMapping.Programs.body
    AdmittedArgumentRendering.Program.inputKey AdmittedArgumentRendering.Program.resultKey
    (AdmittedArgumentRendering.Program.initial []).var (.inl (.inl .scan))
    (0 : Alphabet) (0 : Alphabet) AdmittedArgumentRendering.Program.body

theorem body_eq : machine.m = body := by
  unfold body
  rw [AdmittedArgumentRendering.Program.initial_eq,
    ← AdmittedArgumentRendering.Program.body_eq]
  exact (FramedWordMapping.Programs.body_eq AdmittedArgumentRendering.machine).symm

def keyEquality : DecidableEq machine.K := by
  letI : DecidableEq AdmittedArgumentRendering.machine.K :=
    AdmittedArgumentRendering.Program.keyEquality
  exact inferInstanceAs (DecidableEq (Option (Option (Option
    (Option AdmittedArgumentRendering.machine.K)))))

def step : machine.Cfg → Option machine.Cfg :=
  @TM2.step machine.K machine.Γ machine.Λ machine.σ keyEquality body

theorem step_eq : step = machine.step := by
  unfold step
  rw [show keyEquality = machine.kDecidableEq from Subsingleton.elim _ _, ← body_eq]
  rfl

abbrev inputKey : machine.K := none
abbrev resultKey : machine.K := some (some (some none))

def initial (word : List (Option Alphabet)) : machine.Cfg where
  l := some .scan
  var := ((AdmittedArgumentRendering.Program.initial []).var, none, none, none, none)
  stk key := @dite (List (machine.Γ key)) (key = inputKey) (keyEquality key inputKey)
    (fun same => same.symm ▸ word) (fun _ => [])

theorem initial_eq (word : List (Option Alphabet)) : initial word = initList machine word := by
  have keys : keyEquality = machine.kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [keys, AdmittedArgumentRendering.Program.initial_eq]
  unfold initList
  congr 1
  funext key
  cases key <;> simp [inputKey, machine, FramedWordMapping.machine, FramedWordMapping.vectorKey]

end Mettapedia.Languages.HOLLight.ArgumentVectorRendering.Program
