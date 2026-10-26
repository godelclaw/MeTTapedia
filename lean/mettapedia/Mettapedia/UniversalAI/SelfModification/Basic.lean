import Mettapedia.UniversalAI.BayesianAgents

/-!
# Named policy modification and world-history observations

An action selects a world action and a name interpreted as the next policy.
Extended histories retain modifications; `worldPart` forgets them. A function
is modification-independent exactly when it factors through that projection.
Policies, utilities and environment weights below already consume world histories.
`Utility` is real-valued: boundedness is an additional hypothesis when needed.
Choosing a fixed name represents self-preservation only when that name actually
interprets as the policy, as required by `nonmod_policy_stable`.
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-- Names need not represent every possible policy. -/
abbrev PolicyName := ℕ

structure PolicyModAction where

  worldAction : Action

  nextPolicyName : PolicyName
  deriving DecidableEq, Repr

abbrev PolicyInterpreter := PolicyName → (History → PolicyModAction)

abbrev SelfModPolicy := History → PolicyModAction

abbrev Utility := History → ℝ

structure UtilityModAction where

  worldAction : Action

  nextUtility : Utility

inductive ExtHistElem where
  | policyAct : PolicyModAction → ExtHistElem
  | utilityAct : UtilityModAction → ExtHistElem
  | per : Percept → ExtHistElem

abbrev ExtHistory := List ExtHistElem

def ExtHistory.toHistory : ExtHistory → History
  | [] => []
  | ExtHistElem.policyAct a :: rest =>
      HistElem.act a.worldAction :: ExtHistory.toHistory rest
  | ExtHistElem.utilityAct a :: rest =>
      HistElem.act a.worldAction :: ExtHistory.toHistory rest
  | ExtHistElem.per x :: rest =>
      HistElem.per x :: ExtHistory.toHistory rest

def ExtHistory.worldPart (h : ExtHistory) : History :=
  h.toHistory

def ExtHistory.wellFormed (h : ExtHistory) : Bool :=
  h.toHistory.wellFormed

def ExtHistory.percepts : ExtHistory → List Percept
  | [] => []
  | ExtHistElem.policyAct _ :: rest => ExtHistory.percepts rest
  | ExtHistElem.utilityAct _ :: rest => ExtHistory.percepts rest
  | ExtHistElem.per x :: rest => x :: ExtHistory.percepts rest

def ExtHistory.worldActions : ExtHistory → List Action
  | [] => []
  | ExtHistElem.policyAct a :: rest => a.worldAction :: ExtHistory.worldActions rest
  | ExtHistElem.utilityAct a :: rest => a.worldAction :: ExtHistory.worldActions rest
  | ExtHistElem.per _ :: rest => ExtHistory.worldActions rest

def ExtHistory.cycles (h : ExtHistory) : ℕ :=
  h.percepts.length

/-- Constancy on fibers of the world-history projection. -/
def ModificationIndependent {α : Type*} (f : ExtHistory → α) : Prop :=
  ∀ h h' : ExtHistory, h.worldPart = h'.worldPart → f h = f h'

def toExtHistory : History → ExtHistory
  | [] => []
  | HistElem.act a :: rest => ExtHistElem.policyAct ⟨a, 0⟩ :: toExtHistory rest
  | HistElem.per x :: rest => ExtHistElem.per x :: toExtHistory rest

theorem toExtHistory_worldPart (h : History) :
    (toExtHistory h).worldPart = h := by
  induction h with
  | nil => rfl
  | cons e rest ih =>
      cases e <;> simp_all [toExtHistory, ExtHistory.worldPart, ExtHistory.toHistory]

theorem mod_independent_factors {α : Type*} (f : ExtHistory → α)
    (hf : ModificationIndependent f) :
    ∃ g : History → α, ∀ h, f h = g h.worldPart := by
  use fun wh => f (toExtHistory wh)
  intro h
  apply hf
  rw [toExtHistory_worldPart]

theorem mod_independent_comp {α β : Type*} (f : ExtHistory → α) (g : α → β)
    (hf : ModificationIndependent f) : ModificationIndependent (g ∘ f) := by
  intro h h' heq
  exact congrArg g (hf h h' heq)

def SelfModPolicy.isNonModifying (π : SelfModPolicy) (selfName : PolicyName) : Prop :=
  ∀ h : ExtHistory, (π h.toHistory).nextPolicyName = selfName

def SelfModPolicy.isModificationIndependent (π : SelfModPolicy) : Prop :=
  ∀ h h' : ExtHistory, h.worldPart = h'.worldPart →
    π h.toHistory = π h'.toHistory

theorem nonmod_policy_stable (π : SelfModPolicy) (p : PolicyName)
    (ι : PolicyInterpreter) (hι : ι p = π)
    (hnonmod : π.isNonModifying p) :
    ∀ h : ExtHistory, ι ((π h.toHistory).nextPolicyName) = π := by
  intro h
  simp [hnonmod h, hι]

structure RealisticMeasureData where

  initialPolicy : PolicyName

  interpret : PolicyInterpreter

  envProb : History → Percept → ENNReal

structure IgnorantMeasureData where

  fixedPolicy : SelfModPolicy

  envProb : History → Percept → ENNReal

def Environment.isModificationIndependent (envProb : History → Percept → ENNReal) : Prop :=
  ∀ x : Percept, ModificationIndependent (fun h => envProb h.worldPart x)

def Utility.isModificationIndependent (u : Utility) : Prop :=
  ModificationIndependent (fun h => u h.worldPart)

end Mettapedia.UniversalAI.SelfModification
