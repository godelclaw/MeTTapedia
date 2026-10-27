import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPresentations
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls

/-!
# Controls: the ρ-calculus through both front doors

The runtime installs the ρ driver through its canonical profile (`installed_eq`). The driver is read by steps in
ρ's native structure under its reading (`Rho.reading`: typed equations at ρ's element types under its scope policy,
steps by the reflective interpretation of the rules), so each decided runtime verdict about an admitted process is the
truth of the query's closed formula. The generated front door decides those formulas over ρ's canonical forms
(`Rho.forms`) with its presentation decider (`Rho.decider`), and the two front doors agree at every budget:

| query | process | answer |
|---|---|---|
| built by `PZero` | `0` | yes |
| built by `POutput` | `0` | no |
| built by `PPar` | `0` | yes |
| built by `PInput` | `for(y<-@0){0}` | yes |
| built by `PInput` | `@0!(0)` | no |
| built by `PPar` and some step reaches `PZero` | `for(y<-@0){0} \| @0!(0)` | yes |
| some step reaches `PZero` | `for(y<-@0){0} \| @0!(0)` | yes |
| some step reaches `PZero` | `0 \| for(y<-@0){0} \| @0!(0)` | yes |
| some step reaches `PZero` | `for(y<-@*@0){0} \| @0!(0)` | yes |
| some step reaches `PZero` | `for(y<-@0){*y} \| @0!(0)` | yes |
| some step reaches `POutput` | `for(y<-@0){0} \| @0!(0)` | no |
| every step reaches `PZero` | `for(y<-@0){0} \| @0!(0)` | yes |
| every step reaches `POutput` | `for(y<-@0){0} \| @0!(0)` | no |
| some two steps | `for(y<-@0){0} \| @0!(0)` | no |
| some step | `@0!(for(y<-@0){0} \| @0!(0))` | no |
| some step | `for(y<-@0){for(y<-@0){0} \| @0!(0)}` | no |
| some step | `@(for(y<-@0){0} \| @0!(0))!(0)` | no |
| some step | `@0!(0)` | no |
| every step reaches `⊥` | `@0!(for(y<-@0){0} \| @0!(0))` | yes |
| no step | `@0!(0)` | yes |

`0` is the empty parallel bag, so it is built by `PPar` as well as by `PZero`. A redex under an output payload, an
input guard or a quote does not step: ρ reduces only at the top of its parallel bags. Equivalent channels
communicate (`@*@0` names `@0`), and reflective substitution collapses the received drop (`*y[@0/y] = 0`).

The front door decides more than the driver's tests, modulo ρ's equations, with positive and negative controls:
the name `@0` is the quotation of `*@0` as well as of `0`, so not every presentation of it quotes `0`; a redex splits
into its input and its output but not into two outputs; `0` is the empty bag and an output is not; an input
continuation has the type of continuations and not that of processes.

Without ρ's canonical forms the front door reads the syntax theory with the reference relation, where the reflective
and equivalent-channel communications stay open.

With the runtime as its first strategy, the one front door (`FrontDoorAgreement.askThrough`) answers by the runtime
where it decides and by ρ's canonical regions elsewhere.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open FrontDoorAgreement (frontDoorWith Agrees agrees_of_frontDoorWith)

/-! ## The installed ρ driver -/

/-- The ρ driver the runtime installs. -/
abbrev installed : Installed := Mettapedia.OSLF.NativeTypes.Runtime.Profiles.rho {}

theorem installed_eq :
    Mettapedia.OSLF.NativeTypes.Executable.generate
      (.canonicalRho Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot
        Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment {}) = .ok installed :=
  Mettapedia.OSLF.NativeTypes.Executable.generate_canonicalRho {}

/-- The reading of the installed driver. -/
abbrev read := (driverReading {}).reading (kindOf := fun _ => .hashBag)

/-- ρ's canonical forms. -/
abbrev canonicalForms : CanonicalForms RelationEnv.empty rhoCalc 1 := forms RelationEnv.empty

/-- An admitted process, decoded. -/
def decoded (term : Pattern) (admitted : process term = true) : installed.native.Decoded term :=
  ⟨termOf term admitted, Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.every_carrier_admitted _,
    termOf_pattern term admitted⟩

/-- **The runtime agrees with the generated front door** about an admitted ρ process. -/
theorem agrees {query : Query} (term : Pattern) (admitted : process term = true) {rounds : ℕ} {answer : Bool}
    (answered : frontDoorWith read (decider RelationEnv.empty rounds) [] 1 query term rounds (some canonicalForms) =
      some answer) :
    Agrees installed query term answer :=
  agrees_of_frontDoorWith installed read (driverReading_covered {}) (decider RelationEnv.empty rounds)
    (decoded term admitted) trivial (by rfl) answered

/-! ## The runtime's controls -/

open Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls

theorem zero_built_by_zero : Agrees installed (.constructor "PZero") zero true :=
  agrees zero (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem zero_not_output : Agrees installed (.constructor "POutput") zero false :=
  agrees zero (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem zero_built_by_par : Agrees installed (.constructor "PPar") zero true :=
  agrees zero (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem input_built_by_input : Agrees installed (.constructor "PInput") input true :=
  agrees input (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem output_not_input : Agrees installed (.constructor "PInput") output false :=
  agrees output (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem redex_par_and_step_zero :
    Agrees installed (.conj (.constructor "PPar") (.possibility (.constructor "PZero"))) redex true :=
  agrees redex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem redex_step_zero : Agrees installed (.possibility (.constructor "PZero")) redex true :=
  agrees redex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem parallelRedex_step_zero : Agrees installed (.possibility (.constructor "PZero")) parallelRedex true :=
  agrees parallelRedex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem equivalentChannelRedex_step_zero :
    Agrees installed (.possibility (.constructor "PZero")) equivalentChannelRedex true :=
  agrees equivalentChannelRedex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem reflectiveRedex_step_zero : Agrees installed (.possibility (.constructor "PZero")) reflectiveRedex true :=
  agrees reflectiveRedex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem redex_no_step_output : Agrees installed (.possibility (.constructor "POutput")) redex false :=
  agrees redex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem redex_every_step_zero : Agrees installed (.outgoingUniversal (.constructor "PZero")) redex true :=
  agrees redex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem redex_not_every_step_output : Agrees installed (.outgoingUniversal (.constructor "POutput")) redex false :=
  agrees redex (by decide +kernel) (rounds := 5) (by decide +kernel)

theorem redex_no_two_steps : Agrees installed (.possibility (.possibility .top)) redex false :=
  agrees redex (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem payloadRedex_stuck : Agrees installed (.possibility .top) payloadRedex false :=
  agrees payloadRedex (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem guardedRedex_stuck : Agrees installed (.possibility .top) guardedRedex false :=
  agrees guardedRedex (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem quotedRedex_stuck : Agrees installed (.possibility .top) quotedRedex false :=
  agrees quotedRedex (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem stuckOutput_stuck : Agrees installed (.possibility .top) stuckOutput false :=
  agrees stuckOutput (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem payloadRedex_every_bottom : Agrees installed (.outgoingUniversal .bottom) payloadRedex true :=
  agrees payloadRedex (by decide +kernel) (rounds := 3) (by decide +kernel)

theorem stuckOutput_no_step : Agrees installed (.neg (.possibility .top)) stuckOutput true :=
  agrees stuckOutput (by decide +kernel) (rounds := 3) (by decide +kernel)

/-! ## Presentations modulo ρ's equations -/

/-- The front door in ρ's reading, with its canonical forms and its presentation decider. -/
abbrev askRho (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  askWith RelationEnv.empty [] rhoCalc 1 formula term (decider RelationEnv.empty rounds) none rounds
    (some canonicalForms)

/-- **The name `@0` is the quotation of `*@0`**: `@*@0 ≡ @0`. -/
theorem channel_quotes_drop :
    askRho (.built "NQuote" (.cons (.built "PDrop" (.cons .top .nil)) .nil)) channel 4 = .proved .decided := by
  decide +kernel

/-- It is not the quotation of an output. -/
theorem channel_not_quoted_output :
    askRho (.built "NQuote" (.cons (.built "POutput" (.cons .top (.cons .top .nil))) .nil)) channel 4 =
      .refuted .decided := by
  decide +kernel

/-- **So not every presentation of `@0` quotes `0`**: one quotes `*@0`. -/
theorem channel_not_every_quote_zero :
    askRho (.everyBuilt "NQuote" (.cons (.built "PZero" .nil) .nil)) channel 4 = .refuted .decided := by
  decide +kernel

/-- **A redex splits into its input and its output.** -/
theorem redex_splits :
    askRho (.split .hashBag (.built "PInput" (.cons .top (.cons .top .nil)))
      (.built "POutput" (.cons .top (.cons .top .nil)))) redex 4 = .proved .decided := by
  decide +kernel

/-- It does not split into two outputs. -/
theorem redex_not_two_outputs :
    askRho (.split .hashBag (.built "POutput" (.cons .top (.cons .top .nil)))
      (.built "POutput" (.cons .top (.cons .top .nil)))) redex 4 = .refuted .decided := by
  decide +kernel

/-- **`0` is the empty bag.** -/
theorem zero_empty : askRho (.empty .hashBag) zero 4 = .proved .decided := by
  decide +kernel

/-- An output is not. -/
theorem output_not_empty : askRho (.empty .hashBag) output 4 = .refuted .decided := by
  decide +kernel

/-- **An input continuation has the type of continuations.** -/
theorem input_continuation_typed :
    askRho (.built "PInput" (.cons .top (.cons (.typed (.arrow TypeExpr.name TypeExpr.proc)) .nil))) input 4 =
      .proved .decided := by
  decide +kernel

/-- It does not have the type of processes. -/
theorem input_continuation_not_process :
    askRho (.built "PInput" (.cons .top (.cons (.typed TypeExpr.proc) .nil))) input 4 = .refuted .decided := by
  decide +kernel

/-! ## Without the forms -/

/-- Whether an answer is open. -/
def isOpen : Answer → Bool
  | .unknown _ => true
  | _ => false

/-- **Without ρ's canonical forms, the reflective communication stays open**: the front door reads the syntax theory
with the reference relation, where the received drop is not collapsed. -/
theorem reflectiveRedex_open_without_forms :
    isOpen (ask RelationEnv.empty [] rhoCalc 3 (.possibly .any (.built "PZero" .nil)) reflectiveRedex none 3 none) =
      true := by
  decide +kernel

/-- **So does the communication on equivalent channels.** -/
theorem equivalentChannelRedex_open_without_forms :
    isOpen (ask RelationEnv.empty [] rhoCalc 3 (.possibly .any .top) equivalentChannelRedex none 3 none) = true := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.Controls
