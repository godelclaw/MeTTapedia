import Mettapedia.FoundationalMeaning.Basic

/-!
# The M-structure, autonomy and the situation

Thórisson and Talevi write the foundational meaning of a datum `I` to an agent
in situation `σ` as the M-structure

  `M_now(I) = Pr_t(I, σ_t, K) → G_t → Pl_t`:

predictions from the datum, the situation and prior knowledge; goals from the
predictions; plans from the goals. They define autonomy as the ability to act
on one's own knowledge without calling home, and claim that meaning and
autonomy are two sides of one coin.

Here a situation fixes the observed variables, and the datum is what is
observed now. An agent acts on the plan its M-structure generates, and also
receives an external advice channel, standing for calling home; it is
autonomous when its action never depends on the advice.

* `predictions_separate_of_autonomous_success`: if an autonomous agent succeeds
  on two data that admit no common successful action, its predictions separate
  them. This is the claim "autonomy without meaning is impossible", read as:
  autonomous success requires the agent's own predictions to carry the
  difference.
* `same_action_of_same_observation`: states that agree on the observed
  variables give every autonomous agent the same action; the situation bounds
  what can mean anything to the agent.
* `MStructure.Realized.grounded`: when causal models of the agent's knowledge
  realize each step of the M-structure above a threshold, the plan for every
  datum is grounded in that datum at that threshold.

**Controls.** An agent whose predictions ignore the datum succeeds on both data
only by calling home (`Controls.callingHome_succeeds`); acting autonomously it
fails (`Controls.blind_autonomous_fails`). Observing the distinguishing variable
makes autonomous success possible (`Controls.sighted_succeeds`), and hiding it
makes it impossible (`Controls.hidden_pedestrian_unsolvable`).

The converse slogan, "meaning generation without autonomy is pointless", is a
claim about what meaning is for, not an implication; it is not formalized.
-/

set_option autoImplicit false

namespace Mettapedia.FoundationalMeaning

universe uVar uVal uDatum uPrediction uGoal uPlan uAdvice uAction uReliability

/-- A world state assigns a value to every variable. -/
abbrev WorldState (Var : Type uVar) (Val : Type uVal) := Var → Val

/-- A situation: the variables the agent can observe now and those it can affect. -/
structure Situation (Var : Type uVar) where
  observable : Set Var
  affectable : Set Var

/-- The datum: the observed variables of the current state. -/
def Situation.datum {Var : Type uVar} {Val : Type uVal} (situation : Situation Var)
    (state : WorldState Var Val) : situation.observable → Val :=
  fun observed => state observed

/-- Predictions from the datum, goals from the predictions, a plan from the goals.
The situation and prior knowledge are fixed in the now. -/
structure MStructure (Datum : Type uDatum) (Prediction : Type uPrediction) (Goal : Type uGoal)
    (Plan : Type uPlan) where
  predict : Datum → Prediction
  goals : Prediction → Goal
  plan : Goal → Plan

namespace MStructure

variable {Datum : Type uDatum} {Prediction : Type uPrediction} {Goal : Type uGoal}
  {Plan : Type uPlan}

/-- The plan generated for a datum. -/
def generate (structure' : MStructure Datum Prediction Goal Plan) (datum : Datum) : Plan :=
  structure'.plan (structure'.goals (structure'.predict datum))

end MStructure

/-- An agent acts on the plan its M-structure generates; it also receives
external advice, standing for an intervention of a designer or teacher. -/
structure Agent (Datum : Type uDatum) (Prediction : Type uPrediction) (Goal : Type uGoal)
    (Plan : Type uPlan) (Advice : Type uAdvice) (Action : Type uAction) where
  meaning : MStructure Datum Prediction Goal Plan
  execute : Plan → Advice → Action

namespace Agent

variable {Datum : Type uDatum} {Prediction : Type uPrediction} {Goal : Type uGoal}
  {Plan : Type uPlan} {Advice : Type uAdvice} {Action : Type uAction}

/-- The action taken on a datum under some advice. -/
def act (agent : Agent Datum Prediction Goal Plan Advice Action) (datum : Datum)
    (advice : Advice) : Action :=
  agent.execute (agent.meaning.generate datum) advice

/-- Autonomy: the action never depends on the advice; the agent does not call home. -/
def Autonomous (agent : Agent Datum Prediction Goal Plan Advice Action) : Prop :=
  ∀ plan advice advice', agent.execute plan advice = agent.execute plan advice'

/-- An autonomous agent that succeeds on two data with no common successful
action generates different plans for them. -/
theorem plans_separate_of_autonomous_success
    (agent : Agent Datum Prediction Goal Plan Advice Action) (autonomous : agent.Autonomous)
    (success : Datum → Action → Prop) {first second : Datum}
    (noCommon : ∀ action, ¬ (success first action ∧ success second action))
    {firstAdvice secondAdvice : Advice}
    (firstSucceeds : success first (agent.act first firstAdvice))
    (secondSucceeds : success second (agent.act second secondAdvice)) :
    agent.meaning.generate first ≠ agent.meaning.generate second := by
  intro same
  apply noCommon (agent.act first firstAdvice)
  refine ⟨firstSucceeds, ?_⟩
  have equal : agent.act first firstAdvice = agent.act second secondAdvice := by
    unfold act
    rw [same]
    exact autonomous _ _ _
  rw [equal]
  exact secondSucceeds

/-- **Autonomy needs meaning.** The predictions of an autonomous agent that
succeeds on two data with no common successful action separate the data. -/
theorem predictions_separate_of_autonomous_success
    (agent : Agent Datum Prediction Goal Plan Advice Action) (autonomous : agent.Autonomous)
    (success : Datum → Action → Prop) {first second : Datum}
    (noCommon : ∀ action, ¬ (success first action ∧ success second action))
    {firstAdvice secondAdvice : Advice}
    (firstSucceeds : success first (agent.act first firstAdvice))
    (secondSucceeds : success second (agent.act second secondAdvice)) :
    agent.meaning.predict first ≠ agent.meaning.predict second := by
  intro same
  apply plans_separate_of_autonomous_success agent autonomous success noCommon firstSucceeds
    secondSucceeds
  unfold MStructure.generate
  rw [same]

end Agent

/-- **The situation bounds meaning.** States that agree on the observed
variables give an autonomous agent the same datum and hence the same action. -/
theorem same_action_of_same_observation {Var : Type uVar} {Val : Type uVal}
    {Prediction : Type uPrediction} {Goal : Type uGoal} {Plan : Type uPlan}
    {Advice : Type uAdvice} {Action : Type uAction} (situation : Situation Var)
    (agent : Agent (situation.observable → Val) Prediction Goal Plan Advice Action)
    (autonomous : agent.Autonomous) {first second : WorldState Var Val}
    (agree : ∀ var ∈ situation.observable, first var = second var)
    (firstAdvice secondAdvice : Advice) :
    agent.act (situation.datum first) firstAdvice = agent.act (situation.datum second) secondAdvice := by
  have sameDatum : situation.datum first = situation.datum second := by
    funext observed
    exact agree observed observed.property
  unfold Agent.act
  rw [sameDatum]
  exact autonomous _ _ _

/-! ## Realizing the M-structure by causal models -/

/-- The descriptions an M-structure passes through. -/
inductive MNode (Datum : Type uDatum) (Prediction : Type uPrediction) (Goal : Type uGoal)
    (Plan : Type uPlan) where
  | datum (value : Datum)
  | prediction (value : Prediction)
  | goal (value : Goal)
  | plan (value : Plan)

namespace MStructure

variable {Datum : Type uDatum} {Prediction : Type uPrediction} {Goal : Type uGoal}
  {Plan : Type uPlan} {R : Type uReliability} [LinearOrder R] [OrderTop R]

/-- Each step of the M-structure is a causal model of the knowledge whose
reliability meets the threshold. -/
def Realized (structure' : MStructure Datum Prediction Goal Plan)
    (knowledge : Set (CausalModel (MNode Datum Prediction Goal Plan) R)) (threshold : R) :
    Prop :=
  (∀ datum, ∃ reliability, threshold ≤ reliability ∧
    ⟨.datum datum, .prediction (structure'.predict datum), reliability⟩ ∈ knowledge) ∧
  (∀ prediction, ∃ reliability, threshold ≤ reliability ∧
    ⟨.prediction prediction, .goal (structure'.goals prediction), reliability⟩ ∈ knowledge) ∧
  (∀ goal, ∃ reliability, threshold ≤ reliability ∧
    ⟨.goal goal, .plan (structure'.plan goal), reliability⟩ ∈ knowledge)

theorem groundedAt_of_mem {knowledge : Set (CausalModel (MNode Datum Prediction Goal Plan) R)}
    {threshold reliability : R} {source target : MNode Datum Prediction Goal Plan}
    (meets : threshold ≤ reliability) (member : ⟨source, target, reliability⟩ ∈ knowledge) :
    GroundedAt knowledge threshold source target :=
  ⟨[⟨source, target, reliability⟩], .cons member (.nil _), by simpa using meets⟩

/-- A realized M-structure grounds the plan for every datum in that datum. -/
theorem Realized.grounded {structure' : MStructure Datum Prediction Goal Plan}
    {knowledge : Set (CausalModel (MNode Datum Prediction Goal Plan) R)} {threshold : R}
    (realized : structure'.Realized knowledge threshold) (datum : Datum) :
    GroundedAt knowledge threshold (.datum datum) (.plan (structure'.generate datum)) := by
  obtain ⟨predictions, goals, plans⟩ := realized
  obtain ⟨first, firstMeets, firstMember⟩ := predictions datum
  obtain ⟨second, secondMeets, secondMember⟩ := goals (structure'.predict datum)
  obtain ⟨third, thirdMeets, thirdMember⟩ := plans (structure'.goals (structure'.predict datum))
  exact ((groundedAt_of_mem firstMeets firstMember).trans
    (groundedAt_of_mem secondMeets secondMember)).trans (groundedAt_of_mem thirdMeets thirdMember)

end MStructure

/-! ## Controls -/

namespace Controls

/-- The datum says whether a pedestrian is crossing; the action is to brake or not.
Braking succeeds exactly when a pedestrian is crossing. -/
def succeeds (crossing brake : Bool) : Prop := brake = crossing

theorem no_common_action : ∀ brake, ¬ (succeeds false brake ∧ succeeds true brake) := by
  intro brake both
  exact Bool.false_ne_true (both.1.symm.trans both.2)

/-- Predictions that ignore the datum. -/
def blind : MStructure Bool Unit Unit Unit := ⟨fun _ => (), fun _ => (), fun _ => ()⟩

/-- Predictions that keep the datum. -/
def sighted : MStructure Bool Bool Bool Bool := ⟨id, id, id⟩

/-- An agent with blind predictions that asks its designer what to do. -/
def callingHome : Agent Bool Unit Unit Unit Bool Bool := ⟨blind, fun _ advice => advice⟩

/-- An agent with blind predictions that never brakes. -/
def blindAutonomous : Agent Bool Unit Unit Unit Bool Bool := ⟨blind, fun _ _ => false⟩

/-- An agent that brakes on its own prediction. -/
def sightedAutonomous : Agent Bool Bool Bool Bool Bool Bool := ⟨sighted, fun plan _ => plan⟩

/-- Calling home succeeds on both data, with predictions that ignore the datum. -/
theorem callingHome_succeeds (crossing : Bool) : succeeds crossing (callingHome.act crossing crossing) :=
  rfl

theorem callingHome_not_autonomous : ¬ callingHome.Autonomous :=
  fun autonomous => Bool.false_ne_true (autonomous () false true)

theorem blindAutonomous_autonomous : blindAutonomous.Autonomous := fun _ _ _ => rfl

/-- The same blind predictions fail when the agent acts on its own. -/
theorem blind_autonomous_fails (advice : Bool) : ¬ succeeds true (blindAutonomous.act true advice) :=
  Bool.false_ne_true

theorem sightedAutonomous_autonomous : sightedAutonomous.Autonomous := fun _ _ _ => rfl

theorem sighted_succeeds (crossing advice : Bool) :
    succeeds crossing (sightedAutonomous.act crossing advice) := rfl

/-- The sighted agent's predictions separate the two data, as they must. -/
theorem sighted_separates : sighted.predict false ≠ sighted.predict true := Bool.false_ne_true

/-- Two variables: whether a pedestrian is crossing (`true`) and the weather (`false`). -/
def weatherOnly : Situation Bool := ⟨{false}, ∅⟩

def clearRoad : WorldState Bool Bool := fun _ => false
def crossingRoad : WorldState Bool Bool := fun var => var

/-- With only the weather observed, no autonomous agent brakes exactly when a
pedestrian is crossing. -/
theorem hidden_pedestrian_unsolvable {Prediction : Type} {Goal : Type} {Plan : Type}
    (agent : Agent (weatherOnly.observable → Bool) Prediction Goal Plan Bool Bool)
    (autonomous : agent.Autonomous) (advice advice' : Bool) :
    ¬ (succeeds (clearRoad true) (agent.act (weatherOnly.datum clearRoad) advice) ∧
        succeeds (crossingRoad true) (agent.act (weatherOnly.datum crossingRoad) advice')) := by
  rintro ⟨first, second⟩
  have same := same_action_of_same_observation weatherOnly agent autonomous
    (first := clearRoad) (second := crossingRoad)
    (by intro var observed; simp [weatherOnly] at observed; subst observed; rfl) advice advice'
  rw [same] at first
  exact no_common_action _ ⟨first, second⟩

end Controls

end Mettapedia.FoundationalMeaning
