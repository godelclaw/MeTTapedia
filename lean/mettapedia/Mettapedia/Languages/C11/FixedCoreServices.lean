import Mettapedia.Languages.C11.FixedCoreStatements
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Host services of the fixed C core

A core program's external requests are answered by service machines through
the common callback protocol. One trace shows the core machine's events, each
request, the service's own events and each reply. A returned value resumes the
waiting program exactly as the core's `reply` does; a failed or cancelled
request stops the program with the fault of the service it was waiting for.

Running each service as a machine is a compilation stage from the atomic
closure in which every request is answered in one step: finite observations
agree and completed runs are reflected (`servedStage`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.FixedCore

open IntegerMemoryModel
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The events of a core program together with its services. -/
inductive Hosted (model : Model) (Foreign Failure : Type) where
  | core (event : Event model)
  | called (request : Request model)
  | foreign (event : Foreign)
  | replied (reply : Reply (Value model) Failure)

section Services

variable (model : Model) (policy : SignedConversionPolicy)
  (abi : IntegerType IntegerExtension → ObjectLayout.Layout) (program : Program model)
variable {Foreign Failure : Type}

/-- The waiting program stops with the fault of the service it waits for. A
configuration that is not waiting has no request to refuse; it is a constraint
violation of the protocol. -/
def refused (configuration : Executable model) : Executable model :=
  match configuration.status with
  | .waiting service _ => { configuration with status := .faulted (.service service) }
  | _ => { configuration with status := .faulted .constraint }

/-- Resume a waiting program with a service's reply. -/
def resume (configuration : Executable model) : Reply (Value model) Failure → Executable model
  | .returned value => (reply model policy value configuration).getD (refused model configuration)
  | .faulted _ => refused model configuration
  | .cancelled => refused model configuration

def callback : Callback (Executable model) (Hosted model Foreign Failure) (Request model) (Value model) Failure where
  callEvent := .called
  replyEvent := .replied
  resume := resume model policy

/-- The core machine with its events embedded in the hosted trace. -/
def hosted : Machine (Executable model) (Hosted model Foreign Failure) (Option (Value model)) (Request model) :=
  (machine model policy abi program).relabel .core id id

/-- A program whose requests are served by a service machine loaded from each request. -/
def served {Service External : Type}
    (service : Machine Service (Hosted model Foreign Failure) (Reply (Value model) Failure) External)
    (load : Request model → Service) :
    Machine (HandledState (Executable model) Service (Request model)) (Hosted model Foreign Failure)
      (Option (Value model)) External :=
  (hosted model policy abi program).handle (callback model policy) service load

/-- The core machine calls only from a waiting configuration, which it saves unchanged. -/
theorem call_saves_waiting (configuration saved : Executable model) (request : Request model)
    (called : (machine model policy abi program).step configuration = some (.call request saved)) :
    saved = configuration ∧ configuration.status = .waiting request.service request.arguments := by
  unfold machine at called
  cases status : configuration.status with
  | running =>
      simp only [status, Option.map_eq_some_iff] at called
      obtain ⟨_, _, impossible⟩ := called
      cases impossible
  | waiting service arguments =>
      simp only [status, Option.some.injEq, Transition.call.injEq] at called
      obtain ⟨rfl, rfl⟩ := called
      exact ⟨rfl, rfl⟩
  | finished value => simp [status] at called
  | faulted reason => simp [status] at called

theorem resume_returned (configuration next : Executable model) (value : Value model)
    (replied : reply model policy value configuration = some next) :
    resume (Failure := Failure) model policy configuration (.returned value) = next := by
  simp only [resume, replied, Option.getD_some]

theorem resume_faulted (configuration : Executable model) (service : String) (arguments : List (Value model))
    (waiting : configuration.status = .waiting service arguments) (failure : Failure) :
    resume model policy configuration (.faulted failure) =
      { configuration with status := .faulted (.service service) } := by
  simp only [resume, refused, waiting]

/-- **A served call**: the request, the service's own events and its reply are
published in order, and the program continues from the resumed configuration. -/
theorem served_call {Service External : Type}
    (service : Machine Service (Hosted model Foreign Failure) (Reply (Value model) Failure) External)
    (load : Request model → Service) (configuration saved : Executable model) (request : Request model)
    (called : (machine model policy abi program).step configuration = some (.call request saved))
    (fuel : Nat) (events : List (Hosted model Foreign Failure)) (answer : Reply (Value model) Failure)
    (answered : service.run fuel (load request) = (events, .finished answer)) :
    ∃ used ≤ fuel + 1,
      (served model policy abi program service load).run used (.running configuration) =
        (.called request :: events ++ [.replied answer],
          .exhausted (.running (resume model policy saved answer))) := by
  have lifted : (hosted (Foreign := Foreign) (Failure := Failure) model policy abi program).step configuration =
      some (.call request saved) := by
    simpa [hosted, Transition.relabel] using
      (machine model policy abi program).relabel_step (Hosted.core (Foreign := Foreign) (Failure := Failure))
        id id configuration _ called
  exact (hosted model policy abi program).handle_call_run (callback model policy) service load configuration saved
    request lifted fuel events answer answered

/-- **Serving requests by machines is a compilation stage** from the atomic
closure that answers each request in one step, whenever every loaded service
computes the atomic answer within the bound. -/
def servedStage {Service : Type}
    (service : Machine Service (Hosted model Foreign Failure) (Reply (Value model) Failure) Empty)
    (load : Request model → Service)
    (environment : Environment (Request model) (Hosted model Foreign Failure) (Value model) Failure) (bound : Nat)
    (answers : ∀ request, service.run bound (load request) =
      ((environment request).1, .finished (environment request).2)) :
    Stage ((hosted model policy abi program).close (callback model policy) environment)
      (served model policy abi program service load) :=
  Stage.ofHandler (hosted model policy abi program) (callback model policy) service load environment bound answers

end Services

end Mettapedia.Languages.C11.FixedCore
