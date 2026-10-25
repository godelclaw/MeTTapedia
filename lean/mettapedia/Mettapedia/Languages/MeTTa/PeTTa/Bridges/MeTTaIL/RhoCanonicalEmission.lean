import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution
import Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented
import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop
import Mettapedia.OSLF.MeTTaIL.Complete.RhoWrappers

/-!
# The emitted rho module explores the presented rho calculus

The rho calculus of `GeneralRho.Standard`, emitted as a complete module that commits canonical
forms and searches by classes: every process reachable from a well-sorted source by the presented GSLT (COMM modulo the
parallel laws and the order of parallel components) is, up to that equality, among the processes
the PeTTa run of the explore entry prints after some number of rounds (`rho_emitted_explores`).

Emitted as a module that commits the canonical form of the quote-drop normal form, it explores rho
modulo its parallel laws and the name equation `@(*n) = n` in the same sense
(`rho_emitted_explores_quoteDrop`). Emitted as a module that commits the canonical form of the model
normal form, it explores rho modulo its whole declared collection algebra, with `{P} = P` and `{} = 0`,
and the name equation (`rho_emitted_explores_model`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval
open WireKit

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)

/-- Rho, committing canonical forms. -/
def rhoSpec : Spec := ⟨GeneralRho.Standard.plan, [], .base "Proc", .canonical⟩

/-- **The emitted rho module explores the presented rho calculus.** -/
theorem rho_emitted_explores {name : String} {emitted : Program} (ok : emit? rhoSpec name .classes = .ok emitted)
    (state : State) (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language
      GeneralRho.Standard.plan.snapshot.free [] (.base "Proc") source)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ Complete.Footprint.declaredFootprint GeneralRho.Standard.plan) :
    ∀ target, (Complete.Presented.gslt GeneralRho.Standard.plan [] (.base "Proc")).MultiStep source target →
      ∃ work, ∃ reached ∈ (explored rhoSpec source work).nodes.map (·.state),
        Complete.Presented.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") reached target ∧
        PureReturns (runtime.append emitted) [] state
          (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
          (CompleteExecution.patternsValue ((explored rhoSpec source work).nodes.map (·.state))) := by
  have footprinted : Footprinted rhoSpec := footprinted_of_compiled (emit?_ok ok).2
  have ready : CompleteExecution.CommitReady rhoSpec.mode (table rhoSpec) source := fun _ =>
    CanonicalCompare.covered_of_wellSorted (table_for rhoSpec).constructors (table_for rhoSpec).declared sorted
  exact emitted_explores_presented ok footprinted state source inside ready rfl
    Complete.RhoPresented.extrusions_eq
    (fun target reaches => Complete.RhoPresented.rho_explores source sorted reaches)

/-- Rho, committing the canonical form of the quote-drop normal form. -/
def rhoQuoteDropSpec : Spec :=
  ⟨GeneralRho.Standard.plan, [], .base "Proc", .reflective Complete.RhoQuoteDrop.presentation⟩

/-- **The emitted rho module explores rho modulo its parallel laws and the name equation.** -/
theorem rho_emitted_explores_quoteDrop {name : String} {emitted : Program}
    (ok : emit? rhoQuoteDropSpec name = .ok emitted) (state : State) (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language
      GeneralRho.Standard.plan.snapshot.free [] (.base "Proc") source)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ Complete.Footprint.declaredFootprint GeneralRho.Standard.plan) :
    ∀ target, (Complete.QuoteDropCoherence.gslt GeneralRho.Standard.plan [] (.base "Proc")
        Complete.RhoQuoteDrop.presentation).MultiStep source target →
      ∃ work, ∃ reached ∈ (explored rhoQuoteDropSpec source work).nodes.map (·.state),
        Complete.QuoteDropCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc")
          Complete.RhoQuoteDrop.presentation reached target ∧
        PureReturns (runtime.append emitted) [] state
          (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
          (CompleteExecution.patternsValue ((explored rhoQuoteDropSpec source work).nodes.map (·.state))) := by
  have footprinted : Footprinted rhoQuoteDropSpec := footprinted_of_compiled (emit?_ok ok).2
  have ready : CompleteExecution.CommitReady rhoQuoteDropSpec.mode (table rhoQuoteDropSpec) source := fun _ =>
    CanonicalCompare.covered_of_wellSorted (table_for rhoQuoteDropSpec).constructors
      (table_for rhoQuoteDropSpec).declared sorted
  exact emitted_explores_quoteDrop ok footprinted state source inside ready rfl
    Complete.RhoPresented.extrusions_eq
    (fun target reaches => Complete.RhoQuoteDrop.rho_explores_quoteDrop source sorted reaches)

/-- Rho, committing the canonical form of the model normal form. -/
def rhoModelSpec : Spec :=
  ⟨GeneralRho.Standard.plan, [], .base "Proc", .model Complete.RhoQuoteDrop.presentation⟩

/-- **The emitted rho module explores rho modulo its declared collection algebra and the name
equation.** -/
theorem rho_emitted_explores_model {name : String} {emitted : Program}
    (ok : emit? rhoModelSpec name = .ok emitted) (state : State) (source : Pattern)
    (sorted : OpenPatternWellSorted (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language
      GeneralRho.Standard.plan.snapshot.free [] (.base "Proc") source)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ Complete.Footprint.declaredFootprint GeneralRho.Standard.plan) :
    ∀ target, (Complete.WrapperCoherence.gslt GeneralRho.Standard.plan [] (.base "Proc")
        Complete.RhoQuoteDrop.presentation).MultiStep source target →
      ∃ work, ∃ reached ∈ (explored rhoModelSpec source work).nodes.map (·.state),
        Complete.WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc")
          Complete.RhoQuoteDrop.presentation reached target ∧
        PureReturns (runtime.append emitted) [] state
          (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
          (CompleteExecution.patternsValue ((explored rhoModelSpec source work).nodes.map (·.state))) := by
  have footprinted : Footprinted rhoModelSpec := footprinted_of_compiled (emit?_ok ok).2
  have ready : CompleteExecution.CommitReady rhoModelSpec.mode (table rhoModelSpec) source := fun _ =>
    CanonicalCompare.covered_of_wellSorted (table_for rhoModelSpec).constructors
      (table_for rhoModelSpec).declared sorted
  exact emitted_explores_model ok footprinted state source inside ready rfl
    Complete.RhoPresented.extrusions_eq
    (fun target reaches => Complete.RhoWrappers.rho_explores_wrappers source reaches)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
