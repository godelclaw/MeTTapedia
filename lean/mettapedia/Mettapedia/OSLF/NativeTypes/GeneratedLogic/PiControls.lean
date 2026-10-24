import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: the π-calculus through the front door, modulo its laws

The tree's π-calculus (`piCalc`), asked through the front door with its canonical forms (`PiForms.forms`).
Parallel composition is a bag with the flattening algebra and inaction as its unit, and the language steps
modulo these laws. The canonical forms keep plain steps, so the questions use plain modalities. Channels are
processes; here inaction `0` serves as a free channel and a bound variable as a restricted one.

- `x(y).0 | x⟨0⟩` communicates and ends at `0` (`comm_ends`).
- The input inside a nested bag, beside an inaction: the same (`nested_comm_ends`). As written, no rule fires
  at the top bag; its canonical form is the flattened bag, where the communication fires.
- `!x(y).0 | x⟨0⟩` serves once and ends at the server alone (`server_serves_once`).
- `νx (x(y).0 | x⟨0⟩)` communicates on the restricted channel and ends at `νx. 0` (`restricted_comm_ends`).
- The replicated forwarder `!x(y).x⟨y⟩ | x⟨0⟩` runs forever (`forwarder_diverges`): its step returns to the
  same canonical process, so a closed region of one process decides it. Without the canonical forms the front
  door leaves it open (`forwarder_open_without_forms`).
- One receiver and two messages: either message is received, and both runs end at the remaining message
  (`two_messages_one_result`).
- An input and an output on different channels do not communicate (`different_channels_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc)

abbrev Pi := referenceStructure RelationEnv.empty piCalc

/-- The front door, with the canonical forms at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] piCalc 3 formula term none rounds (some (PiForms.forms 3))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : Pi.sat Env.closed formula term :=
  ask_proved answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ Pi.sat Env.closed formula term :=
  ask_refuted answered

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

/-- Every run goes on forever. -/
def forever : Formula 0 := .nu (.and (.possibly .any .top) (.necessarily .any (.var 0)))

def zero : Pattern := .apply "PiNil" []
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def input (channel body : Pattern) : Pattern := .apply "PiInp" [channel, .lambda none body]
def output (channel datum : Pattern) : Pattern := .apply "PiOut" [channel, datum]
def server (channel body : Pattern) : Pattern := .apply "PiRep" [channel, .lambda none body]
def restrict (body : Pattern) : Pattern := .apply "PiNu" [.lambda none body]

/-! ## Communication -/

theorem comm_ends_answer :
    answer (endsAt zero) (par [input zero zero, output zero zero]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`x(y).0 | x⟨0⟩` communicates and ends at `0`.** -/
theorem comm_ends : Pi.sat Env.closed (endsAt zero) (par [input zero zero, output zero zero]) :=
  answer_proved comm_ends_answer

theorem nested_comm_ends_answer :
    answer (endsAt zero) (par [par [input zero zero, zero], output zero zero]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The input inside a nested bag, beside an inaction, still communicates.** -/
theorem nested_comm_ends : Pi.sat Env.closed (endsAt zero) (par [par [input zero zero, zero], output zero zero]) :=
  answer_proved nested_comm_ends_answer

theorem server_serves_once_answer :
    answer (endsAt (server zero zero)) (par [server zero zero, output zero zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`!x(y).0 | x⟨0⟩` serves once and ends at the server alone.** -/
theorem server_serves_once : Pi.sat Env.closed (endsAt (server zero zero)) (par [server zero zero, output zero zero]) :=
  answer_proved server_serves_once_answer

theorem restricted_comm_ends_answer :
    answer (endsAt (restrict zero)) (restrict (par [input (.bvar 0) zero, output (.bvar 0) zero])) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`νx (x(y).0 | x⟨0⟩)` communicates on the restricted channel and ends at `νx. 0`.** -/
theorem restricted_comm_ends :
    Pi.sat Env.closed (endsAt (restrict zero)) (restrict (par [input (.bvar 0) zero, output (.bvar 0) zero])) :=
  answer_proved restricted_comm_ends_answer

/-! ## Divergence -/

/-- `!x(y).x⟨y⟩ | x⟨0⟩`. -/
def forwarder : Pattern := par [server zero (output zero (.bvar 0)), output zero zero]

theorem forwarder_diverges_answer : answer forever forwarder 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The replicated forwarder runs forever.** -/
theorem forwarder_diverges : Pi.sat Env.closed forever forwarder := answer_proved forwarder_diverges_answer

/-- **Without the canonical forms the front door leaves it open.** -/
theorem forwarder_open_without_forms : ask RelationEnv.empty [] piCalc 3 forever forwarder none 4 = .unknown 4 := by
  decide +kernel

/-! ## Choice and its absence -/

theorem two_messages_one_result_answer :
    answer (endsAt (output zero zero)) (par [input zero zero, output zero zero, output zero zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **One receiver and two messages: both runs end at the remaining message.** -/
theorem two_messages_one_result :
    Pi.sat Env.closed (endsAt (output zero zero)) (par [input zero zero, output zero zero, output zero zero]) :=
  answer_proved two_messages_one_result_answer

theorem different_channels_stuck_answer :
    answer steps (par [input zero zero, output (input zero zero) zero]) 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **An input and an output on different channels do not communicate.** -/
theorem different_channels_stuck : ¬ Pi.sat Env.closed steps (par [input zero zero, output (input zero zero) zero]) :=
  answer_refuted different_channels_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
