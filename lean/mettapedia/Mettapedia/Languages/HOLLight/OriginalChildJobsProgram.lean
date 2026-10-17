import Mettapedia.Languages.HOLLight.OriginalChildJobs
import Mettapedia.Languages.HOLLight.RuleArgumentProgram
import Mettapedia.Computability.FramedWordMappingProgram

/-!
# Instructions for original child-job preparation

The original list parser, authored-arity framer, framed mapper, byte lift and
ordered pairing execute through their structural instruction interfaces.
The table, transition and initial configuration equal the original machine.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true

namespace Mettapedia.Languages.HOLLight.OriginalChildJobs.Program
open Turing
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open RuleArgumentRendering.Program

attribute [local reducible] OriginalChildJobs.machine OriginalChildJobs.preparedMachine
  OriginalChildJobs.framingMachine StackMachineComposition.machine
  FramedWordMapping.machine CertificateArgumentFraming.Execution.machine
  CertificateArgumentFraming.Execution.parserBody CertificateDataTraversal.PrefixField.machine
  CertificateDataTraversal.machine WordHomomorphismMachine.machine FramedWordPairing.machine
  StackMachineComposition.leftKey StackMachineComposition.rightKey

abbrev target (arity : Nat) := OriginalChildJobs.machine arity

local instance : Inhabited PairCell := ⟨.inr false⟩
local instance (arity : Nat) : Fintype ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₀) := inferInstanceAs (Inhabited Alphabet)
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Fintype ((framingMachine arity).Γ (framingMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance (arity : Nat) : Inhabited ((framingMachine arity).Γ (framingMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option (Option Alphabet)))
local instance (arity : Nat) : Fintype ((preparedMachine arity).Γ (preparedMachine arity).k₁) :=
  inferInstanceAs (Fintype PairCell)
local instance (arity : Nat) : Inhabited ((preparedMachine arity).Γ (preparedMachine arity).k₁) :=
  inferInstanceAs (Inhabited PairCell)

def framerTable (arity : Nat) :
    { table : (CertificateArgumentFraming.Execution.machine arity).Λ →
        (CertificateArgumentFraming.Execution.machine arity).Stmt //
      table = (CertificateArgumentFraming.Execution.machine arity).m } := by
  extract_rule_program (CertificateArgumentFraming.Execution.machine arity).m

def framerBody (arity : Nat) := (framerTable arity).val

theorem framerBody_exact (arity : Nat) :
    framerBody arity = (CertificateArgumentFraming.Execution.machine arity).m :=
  (framerTable arity).property

def framingBody (arity : Nat) : (framingMachine arity).Λ → (framingMachine arity).Stmt :=
  FramedWordMapping.Programs.body
    CertificateArgumentFraming.Execution.inputKey CertificateArgumentFraming.Execution.resultKey
    (none, none) (.spine ⟨0, Nat.zero_lt_succ _⟩)
    (0 : Alphabet) (none : Option Alphabet) (framerBody arity)

theorem framingBody_exact (arity : Nat) : framingBody arity = (framingMachine arity).m := by
  unfold framingBody
  rw [framerBody_exact]
  exact FramedWordMapping.Programs.body_eq (CertificateArgumentFraming.Execution.machine arity)

def preparedBody (arity : Nat) : (preparedMachine arity).Λ → (preparedMachine arity).Stmt :=
  StackMachineComposition.Programs.body
    (some (some (some none))) WordHomomorphismMachine.Stack.input
    WordHomomorphismMachine.Phase.read (none : Option (Option Alphabet)) id
    (framingBody arity) (WordHomomorphismMachine.program liftCell)

theorem preparedBody_exact (arity : Nat) : preparedBody arity = (preparedMachine arity).m := by
  unfold preparedBody
  rw [framingBody_exact]
  exact StackMachineComposition.body_eq (framingMachine arity) liftMachine
    (Equiv.refl (Option (Option Alphabet)))

def body (arity : Nat) : (target arity).Λ → (target arity).Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (preparedMachine arity).Γ)
    (SecondAlphabet := (FramedWordPairing.machine (1 : Alphabet)).Γ)
    (some (.inr WordHomomorphismMachine.Stack.result) : (preparedMachine arity).K) FramedWordPairing.Stack.input
    (FramedWordPairing.Phase.tag false) (Sum.inr false : PairCell) id
    (preparedBody arity) (FramedWordPairing.statement (1 : Alphabet))

theorem body_exact (arity : Nat) : body arity = (target arity).m := by
  unfold body
  rw [preparedBody_exact]
  exact StackMachineComposition.body_eq (preparedMachine arity)
    (FramedWordPairing.machine (1 : Alphabet)) (Equiv.refl PairCell)

def framingEquality : DecidableEq (framingMachine 0).K :=
  optionEquality (optionEquality (optionEquality (optionEquality
    (optionEquality (optionEquality (optionEquality CertificateDataTraversal.instDecidableEqStack))))))

def preparedEquality : DecidableEq (preparedMachine 0).K :=
  optionEquality (sumEquality framingEquality WordHomomorphismMachine.instDecidableEqStack)

def keyEquality (arity : Nat) : DecidableEq (target arity).K :=
  optionEquality (sumEquality preparedEquality FramedWordPairing.instDecidableEqStack)

local instance (arity : Nat) : DecidableEq (target arity).K := keyEquality arity

def step (arity : Nat) : (target arity).Cfg → Option (target arity).Cfg :=
  @TM2.step (target arity).K (target arity).Γ (target arity).Λ (target arity).σ
    (keyEquality arity) (body arity)

theorem step_exact (arity : Nat) : step arity = (target arity).step := by
  unfold step
  rw [show keyEquality arity = (target arity).kDecidableEq from Subsingleton.elim _ _, body_exact]
  rfl

abbrev inputKey (arity : Nat) : (target arity).K := some (.inl (some (.inl none)))
abbrev resultKey (arity : Nat) : (target arity).K := some (.inr FramedWordPairing.Stack.result)

def registers (arity : Nat) : (target arity).σ :=
  ((((none, none), none, none, none, none), (none, none), none), none, none)

def initial (arity : Nat) (word : List (Option Alphabet)) : (target arity).Cfg where
  l := some (.inl (.inl FramedWordMapping.Phase.scan))
  var := registers arity
  stk key := @dite (List ((target arity).Γ key)) (key = inputKey arity)
    (keyEquality arity key (inputKey arity)) (fun same => same.symm ▸ word) (fun _ => [])

theorem initial_exact (arity : Nat) (word : List (Option Alphabet)) :
    initial arity word = initList (target arity) word := by
  have same : keyEquality arity = (target arity).kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [same]
  unfold initList
  congr 1
  funext key
  by_cases equal : key = inputKey arity
  · subst key
    simp [inputKey, StackMachineComposition.leftKey]
  · simp [inputKey, StackMachineComposition.leftKey] at equal ⊢
    simp [equal]

private def added {A : Type} (keys : List A) : List (Option A) := none :: keys.map some
private def joined {A B : Type} (first : List A) (second : List B) : List (Option (A ⊕ B)) :=
  none :: (first.map (some ∘ Sum.inl) ++ second.map (some ∘ Sum.inr))

private theorem added_all {A : Type} (keys : List A) (complete : ∀ key, key ∈ keys) :
    ∀ key, key ∈ added keys := by
  intro key
  cases key <;> simp [added, complete]

private theorem joined_all {A B : Type} (first : List A) (second : List B)
    (left : ∀ key, key ∈ first) (right : ∀ key, key ∈ second) :
    ∀ key, key ∈ joined first second := by
  intro key
  cases key with
  | none => simp [joined]
  | some key => cases key <;> simp [joined, left, right]

private def dataKeys : List CertificateDataTraversal.Stack := [.input, .frames, .output]
private def liftKeys : List WordHomomorphismMachine.Stack := [.input, .output, .result]
private def pairKeys : List FramedWordPairing.Stack :=
  [.input, .first, .second, .temporary, .accumulator, .result]

def keys (arity : Nat) : List (target arity).K :=
  joined (joined (added (added (added (added (added (added (added dataKeys))))))) liftKeys) pairKeys

theorem all_keys (arity : Nat) : ∀ key : (target arity).K, key ∈ keys arity := by
  have dataComplete : ∀ key, key ∈ dataKeys := by intro key; cases key <;> simp [dataKeys]
  have liftComplete : ∀ key, key ∈ liftKeys := by intro key; cases key <;> simp [liftKeys]
  have pairComplete : ∀ key, key ∈ pairKeys := by intro key; cases key <;> simp [pairKeys]
  exact joined_all _ _ (joined_all _ _
    (added_all _ (added_all _ (added_all _ (added_all _ (added_all _
      (added_all _ (added_all _ dataComplete))))))) liftComplete) pairComplete

private def productEquality {A B : Type} (first : DecidableEq A) (second : DecidableEq B) :
    DecidableEq (A × B) := fun x y => @instDecidableEqProd A B first second x y

def registerEquality (arity : Nat) : DecidableEq (target arity).σ :=
  let byte := inferInstanceAs (DecidableEq Alphabet)
  let one := optionEquality byte
  let two := optionEquality one
  let three := optionEquality two
  let cell := optionEquality (sumEquality two (inferInstanceAs (DecidableEq Bool)))
  productEquality
    (productEquality
      (productEquality (productEquality one two)
        (productEquality two (productEquality one (productEquality two three))))
      (productEquality (productEquality three cell) three))
    (productEquality cell cell)

end Mettapedia.Languages.HOLLight.OriginalChildJobs.Program
