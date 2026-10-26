import Mettapedia.CogArch.CollectiveAgency.Memory
import Mettapedia.FoundationalMeaning.Autonomy
import Mettapedia.GSLT.Dynamics.InterventionalValueBoundary

/-!
# Participation, advice and visibility

Available interactions carry more information than a recorded action.
Refusal is an available alternative, not a particular output value. An agent
may respond to advice while retaining refusal; conversely, advice-independent
execution need not supply a refusal transition. The latter independence is
the distinct notion already defined in `FoundationalMeaning.Autonomy`.

Visibility, ability to suggest, and permission to enact are separate in the
finite role model. Even an identity observer acquires no intervention right.
Expanding the allowed interactions can invalidate a previously sufficient
memory despite leaving the present observation unchanged.

Motivation: https://theanarchistlibrary.org/library/hakim-bey-immediatism .
Model-relative imagination is a separate thread associated with Henri
Corbin's *Mundus Imaginalis*, not an essay by Bey. Scenario tags in `Memory`
record an interpretation scope; they establish no metaphysical claim.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.CollectiveAgency.Participation

inductive Choice where
  | work | refuse
  deriving DecidableEq

inductive State where
  | offered (menu : Finset Choice)
  | finished (result : Option Bool)
  deriving DecidableEq

inductive Interaction : State → Choice → Bool → State → Prop where
  | work (menu : Finset Choice) (advice : Bool) : Choice.work ∈ menu →
      Interaction (.offered menu) .work advice (.finished (some advice))
  | refuse (menu : Finset Choice) (advice : Bool) : Choice.refuse ∈ menu →
      Interaction (.offered menu) .refuse advice (.finished none)

def MayRefuse (source : State) : Prop := ∃ advice target, Interaction source .refuse advice target

def voluntary : State := .offered {.work, .refuse}
def forced : State := .offered {.work}

theorem voluntary_may_refuse : MayRefuse voluntary :=
  ⟨false, .finished none, Interaction.refuse _ _ (by decide)⟩

theorem forced_cannot_refuse : ¬ MayRefuse forced := by
  rintro ⟨_, _, move⟩
  cases move with
  | refuse _ _ present => simp at present

theorem same_recorded_work_different_agency (advice : Bool) :
    Interaction voluntary .work advice (.finished (some advice)) ∧
    Interaction forced .work advice (.finished (some advice)) ∧
    MayRefuse voluntary ∧ ¬ MayRefuse forced :=
  ⟨Interaction.work _ _ (by decide), Interaction.work _ _ (by decide),
    voluntary_may_refuse, forced_cannot_refuse⟩

open Mettapedia.FoundationalMeaning

def cooperative : Agent Bool Bool Bool Bool Bool Bool where
  meaning := ⟨id, id, id⟩
  execute plan advice := xor plan advice

def independent : Agent Bool Bool Bool Bool Bool Bool where
  meaning := ⟨id, id, id⟩
  execute plan _ := plan

theorem advice_independence_is_distinct :
    ¬ cooperative.Autonomous ∧ MayRefuse voluntary ∧
      independent.Autonomous ∧ ¬ MayRefuse forced := by
  refine ⟨?_, voluntary_may_refuse, ?_, forced_cannot_refuse⟩
  · intro h
    have := h false false true
    cases this
  · intro _ _ _
    rfl

inductive Role where
  | observer | adviser | participant
  deriving DecidableEq

inductive Command where
  | inspect | suggest (advice : Bool) | work | refuse
  deriving DecidableEq

def commands : Role → Finset Command
  | .observer => {.inspect}
  | .adviser => {.inspect, .suggest false, .suggest true}
  | .participant => {.inspect, .suggest false, .suggest true, .work, .refuse}

/-- Observation itself is maximally informative; authority remains elsewhere. -/
def observe (world : Bool × Bool) : Bool × Bool := world

theorem full_visibility_without_control :
    Function.Injective observe ∧ Command.work ∉ commands .observer ∧
      Command.refuse ∉ commands .observer := by
  refine ⟨fun _ _ h => h, ?_⟩
  decide

theorem influence_without_enactment :
    Command.suggest false ∈ commands .adviser ∧ Command.suggest true ∈ commands .adviser ∧
    cooperative.execute false false ≠ cooperative.execute false true ∧
    Command.work ∉ commands .adviser ∧ Command.refuse ∉ commands .adviser := by decide

theorem participation_retains_refusal :
    Command.work ∈ commands .participant ∧ Command.refuse ∈ commands .participant := by decide

/-! ## Future interaction changes the memory contract -/

open Mettapedia.GSLT.TaskRelativeMemory

def passive (s : Bool × Bool) (_ : Unit) : Bool × Bool := s
def interactive (s : Bool × Bool) (reveal : Bool) : Bool × Bool :=
  if reveal then (s.2, s.2) else s
def readNow (_ : Unit) (s : Bool × Bool) : Bool := s.1

def passiveMemory : Realization passive readNow (Prod.fst : Bool × Bool → Bool) where
  update value _ := value
  read _ value := value
  update_agrees _ _ := rfl
  read_agrees _ _ := rfl

theorem passive_forgetting_harmless (word : List Unit) :
    passiveMemory.read () (word.foldl passiveMemory.update (false, false).1) =
      readNow () (word.foldl passive (false, true)) := by
  exact (congrArg (passiveMemory.read ()) (Realization.foldl_agrees passive readNow passiveMemory word (false, true))).trans
    (passiveMemory.read_agrees () (word.foldl passive (false, true)))

theorem new_interaction_separates :
    profile interactive readNow (false, false) ≠ profile interactive readNow (false, true) := by
  intro equal
  have := congrFun (congrFun equal [true]) ()
  change false = true at this
  cases this

theorem old_readout_cannot_support_new_interaction :
    ¬ ∃ updateMemory : Bool → Bool → Bool,
      ∀ (s : Bool × Bool) (input : Bool), updateMemory s.1 input = (interactive s input).1 := by
  rintro ⟨updateMemory, agrees⟩
  have a := agrees (false, false) true
  have b := agrees (false, true) true
  have impossible : false = true := a.symm.trans b
  cases impossible

end Mettapedia.CogArch.CollectiveAgency.Participation
