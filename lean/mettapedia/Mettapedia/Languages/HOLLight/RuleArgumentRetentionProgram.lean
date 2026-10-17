import Mettapedia.Languages.HOLLight.RuleArgumentProgram

/-!
# Executable caller retaining the complete original rule instance

The caller preserves both the original input and the rendered result on
physical stacks. Its instruction table, initialization and transition agree
with the retained machine whose copying and refusal costs are proved in
`RuleArgumentRendering`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.RuleArgumentRendering.RetainedProgram

open Turing Mettapedia.Computability Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Binding.WireCodec.Binary

abbrev target (definition : CalculusLanguageDef) := retainedMachine definition

def body (definition : CalculusLanguageDef) : (target definition).Λ → (target definition).Stmt :=
  RetainedWordExecution.WithOutput.Programs.statement
    (Program.inputKey definition) (Program.resultKey definition)
    (0 : Alphabet) (none : Option Alphabet)
    (Program.registers definition) (Program.mainLabel definition) (Program.body definition)

theorem body_exact (definition : CalculusLanguageDef) : body definition = (target definition).m := by
  unfold body
  rw [Program.body_exact]
  rfl

def keyEquality (definition : CalculusLanguageDef) : DecidableEq (target definition).K :=
  Program.optionEquality (Program.optionEquality (Program.optionEquality
    (Program.optionEquality (Program.keyEquality definition))))

local instance (definition : CalculusLanguageDef) : DecidableEq (target definition).K :=
  keyEquality definition

def step (definition : CalculusLanguageDef) : (target definition).Cfg → Option (target definition).Cfg :=
  @TM2.step (target definition).K (target definition).Γ (target definition).Λ
    (target definition).σ (keyEquality definition) (body definition)

theorem step_exact (definition : CalculusLanguageDef) : step definition = (target definition).step := by
  unfold step
  rw [show keyEquality definition = (target definition).kDecidableEq from Subsingleton.elim _ _, body_exact]
  rfl

abbrev inputKey (definition : CalculusLanguageDef) : (target definition).K :=
  some (some (some (some (Program.inputKey definition))))

abbrev resultKey (definition : CalculusLanguageDef) : (target definition).K := none

def initial (definition : CalculusLanguageDef) (word : List Alphabet) : (target definition).Cfg where
  l := some .scan
  var := (Program.registers definition, none, none)
  stk := Function.update (fun _ => []) (inputKey definition) word

theorem initial_exact (definition : CalculusLanguageDef) (word : List Alphabet) :
    initial definition word = initList (target definition) word := by
  simp only [initial, initList]
  congr 1
  funext key
  have address : inputKey definition = (target definition).k₀ := rfl
  simp only [Function.update, address]
  by_cases same : key = (target definition).k₀
  · subst key; simp
  · simp [same]


end Mettapedia.Languages.HOLLight.RuleArgumentRendering.RetainedProgram
