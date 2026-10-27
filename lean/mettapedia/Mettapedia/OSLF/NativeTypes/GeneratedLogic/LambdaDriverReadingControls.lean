import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaDriverReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.Runtime.Controls

/-!
# Controls: the λ-calculus through both front doors

The runtime installs the λ driver at each configuration through its scoped profile (`installed_eq`). The driver is read
by steps in the reference structure of the authored λ language restricted to the selected rules
(`LambdaReading.reading`), so each decided runtime verdict about a closed term is the truth of the query's closed
formula, which the generated front door decides. The two front doors agree at every budget:

| configuration | query | term | answer |
|---|---|---|---|
| all rules | built by `Lam` | `λx. x` | yes |
| all rules | built by `App` | `λx. x` | no |
| all rules | not built by `Lam` | `λx. x` | no |
| all rules | some step reaches a `Lam` | `(λx. x) (λx. x)` | yes |
| all rules | some step reaches an `App` | `(λx. x) (λx. x)` | no |
| all rules | every step reaches a `Lam` | `(λx. x) (λx. x)` | yes |
| all rules | every step reaches an `App` | `(λx. x) (λx. x)` | no |
| all rules | some step | `λx. x` | no |
| all rules | every step reaches `⊥` | `λx. x` | yes |
| all rules | some two steps | `(λx. x) (λx. x)` | no |
| all rules | built by `App` implies some step reaches a `Lam` | `(λx. x) (λx. x)` | yes |
| without β | some step | `(λx. x) (λx. x)` | no |
| all rules | some step | `λx. (λy. y) x` | yes |
| without the binder rule | some step | `λx. (λy. y) x` | no |
| finite-limit logic | built by `Lam` | `λx. x` | yes |
| `□` sort profile | built by `Lam` | `λx. x` | no |

At budget zero the runtime suspends "some step reaches a `Lam`" at `(λx. x) (λx. x)`; the generated front door answers
yes. With the runtime as its first strategy, the one front door (`FrontDoorAgreement.askThrough`) answers by the
runtime where it decides and by its own strategies elsewhere.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaReading.Controls

open Mettapedia.OSLF.Binding LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver (Configuration)
open FrontDoorAgreement (frontDoor Agrees agrees_of_frontDoor)

/-! ## The installed λ driver -/

/-- The λ driver the runtime installs at a configuration. -/
abbrev installed (configuration : Configuration) : Installed :=
  Mettapedia.OSLF.NativeTypes.Runtime.Profiles.lambda configuration []

theorem installed_eq (configuration : Configuration) :
    Mettapedia.OSLF.NativeTypes.Executable.generate
      (Mettapedia.OSLF.NativeTypes.Runtime.Controls.lambdaRequest configuration) = .ok (installed configuration) :=
  Mettapedia.OSLF.NativeTypes.Executable.generate_scopedLambda configuration []

/-- The reading at a configuration. -/
abbrev read (configuration : Configuration) :=
  (reading configuration).reading (kindOf := fun _ => .hashBag)

/-- **The runtime agrees with the generated front door** about a closed λ-term. -/
theorem agrees (configuration : Configuration) {query : Query} (term : Term sig [] .term) {rounds : ℕ} {answer : Bool}
    (answered : frontDoor (read configuration) [] 3 query (encodeTerm term) rounds = some answer) :
    Agrees (installed configuration) query (encodeTerm term) answer :=
  agrees_of_frontDoor (installed configuration) (read configuration) (reading_covered configuration)
    ⟨term, Mettapedia.OSLF.NativeTypes.Instances.Lambda.Backend.source_admitted term, rfl⟩ trivial formsFor_none
    answered

/-! ## The runtime's controls -/

open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls (identity redex underLambda)

abbrev all : Configuration := {}
abbrev noBeta : Configuration := {rules := {beta := false}}
abbrev noBinder : Configuration := {rules := {lamCong := false}}
abbrev finiteLogic : Configuration := {logic := Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment}
abbrev boxProfile : Configuration := {vertex := (fun _ => .box, fun _ => .box)}

theorem lam_identity : Agrees (installed all) (.constructor "Lam") (encodeTerm identity) true :=
  agrees all identity (rounds := 4) (by decide +kernel)

theorem app_identity : Agrees (installed all) (.constructor "App") (encodeTerm identity) false :=
  agrees all identity (rounds := 4) (by decide +kernel)

theorem not_lam_identity : Agrees (installed all) (.neg (.constructor "Lam")) (encodeTerm identity) false :=
  agrees all identity (rounds := 4) (by decide +kernel)

theorem step_lam_redex : Agrees (installed all) (.possibility (.constructor "Lam")) (encodeTerm redex) true :=
  agrees all redex (rounds := 6) (by decide +kernel)

theorem step_app_redex : Agrees (installed all) (.possibility (.constructor "App")) (encodeTerm redex) false :=
  agrees all redex (rounds := 6) (by decide +kernel)

theorem every_lam_redex : Agrees (installed all) (.outgoingUniversal (.constructor "Lam")) (encodeTerm redex) true :=
  agrees all redex (rounds := 6) (by decide +kernel)

theorem every_app_redex : Agrees (installed all) (.outgoingUniversal (.constructor "App")) (encodeTerm redex) false :=
  agrees all redex (rounds := 6) (by decide +kernel)

theorem identity_stuck : Agrees (installed all) (.possibility .top) (encodeTerm identity) false :=
  agrees all identity (rounds := 4) (by decide +kernel)

theorem identity_every_bottom : Agrees (installed all) (.outgoingUniversal .bottom) (encodeTerm identity) true :=
  agrees all identity (rounds := 4) (by decide +kernel)

theorem redex_no_two_steps : Agrees (installed all) (.possibility (.possibility .top)) (encodeTerm redex) false :=
  agrees all redex (rounds := 6) (by decide +kernel)

theorem app_implies_lam_step :
    Agrees (installed all) (.imp (.constructor "App") (.possibility (.constructor "Lam"))) (encodeTerm redex) true :=
  agrees all redex (rounds := 6) (by decide +kernel)

theorem noBeta_stuck : Agrees (installed noBeta) (.possibility .top) (encodeTerm redex) false :=
  agrees noBeta redex (rounds := 6) (by decide +kernel)

theorem guarded_steps : Agrees (installed all) (.possibility .top) (encodeTerm underLambda) true :=
  agrees all underLambda (rounds := 8) (by decide +kernel)

theorem noBinder_guarded_stuck : Agrees (installed noBinder) (.possibility .top) (encodeTerm underLambda) false :=
  agrees noBinder underLambda (rounds := 8) (by decide +kernel)

theorem finiteLogic_lam_identity : Agrees (installed finiteLogic) (.constructor "Lam") (encodeTerm identity) true :=
  agrees finiteLogic identity (rounds := 4) (by decide +kernel)

/-- Under the `□` sort profile no closed term is built by `Lam`: the profile admits only open terms there. -/
theorem boxProfile_not_lam_identity :
    Agrees (installed boxProfile) (.constructor "Lam") (encodeTerm identity) false :=
  agrees boxProfile identity (rounds := 4) (by decide +kernel)

/-! ## One front door -/

open FrontDoorAgreement (askThrough)

/-- The generated front door with the λ runtime as its first strategy. -/
abbrev askLambda (query : Query) (term : Term sig [] .term) (budget rounds : ℕ) :=
  askThrough (installed all) (read all) (reading_covered all) (fun _ => trivial) [] 3 query
    (encodeTerm term) budget rounds

/-- Whether an answer is a proof, a refutation, or open. -/
def kind : Answer → String
  | .proved .decided => "proved by the runtime"
  | .refuted .decided => "refuted by the runtime"
  | .proved _ => "proved"
  | .refuted _ => "refuted"
  | .unknown _ => "open"

-- With budget the runtime decides; without, the generated front door's own strategies answer.
#guard kind (askLambda (.possibility (.constructor "Lam")) redex 30 6) == "proved by the runtime"
#guard kind (askLambda (.possibility (.constructor "Lam")) redex 0 6) == "proved"
#guard kind (askLambda (.possibility (.constructor "App")) redex 30 6) == "refuted by the runtime"
#guard kind (askLambda (.possibility (.constructor "App")) redex 0 6) == "refuted"
#guard kind (askLambda (.possibility .top) underLambda 30 8) == "proved by the runtime"
#guard kind (askLambda (.possibility .top) underLambda 0 0) == "open"

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaReading.Controls
