import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls

open Mettapedia.OSLF.Framework

/-!
# Shared public native-query controls

These tests resolve constructor names from the generated catalogues and
decode the supplied raw program before checking the query. The same entry
point distinguishes completed negative judgments from refusals and pauses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Executable
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open Mettapedia.OSLF.Binding LambdaScopedAuthoringComparison

def lambdaRequest (configuration : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration) : Request :=
  .scopedLambda Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
    (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment configuration) configuration []

def lambda : Request := lambdaRequest {}
def lambdaNoBeta : Request := lambdaRequest {rules := {beta := false}}
def lambdaNoBinderReduction : Request := lambdaRequest {rules := {lamCong := false}}
def lambdaFiniteLogic : Request := lambdaRequest {logic := Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment}
def lambdaBox : Request := lambdaRequest {vertex := (fun _ => .box, fun _ => .box)}
def machine : Request := .originalMachine Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment {} []

def identity : Pattern := encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.identity
def beta : Pattern := encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.redex
def guardedBeta : Pattern := encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.underLambda
def normal : Pattern := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
def halt : Pattern := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped

def observe (request : Request) (query : Query) (source : Pattern) (budget : Nat) :
    Except GenerationIssue Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout :=
  (generate request).map fun installed => (Executable.ask installed query source budget).readout

def yes : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout := .checked (.judgment (.decided true))
def no : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout := .checked (.judgment (.decided false))
def pending : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout := .checked (.judgment .unknown)

#guard observe lambda (.constructor "Lam") identity 10 == .ok yes
#guard observe lambda (.constructor "App") identity 10 == .ok no
#guard observe lambda (.neg (.constructor "Lam")) identity 10 == .ok no
#guard observe lambda (.possibility (.constructor "Lam")) beta 0 == .ok pending
#guard observe lambda (.possibility (.constructor "Lam")) beta 30 == .ok yes
#guard observe lambda (.possibility (.constructor "App")) beta 30 == .ok no
#guard observe lambda (.outgoingUniversal (.constructor "Lam")) beta 30 == .ok yes
#guard observe lambda (.outgoingUniversal (.constructor "App")) beta 30 == .ok no
#guard observe lambda (.possibility .top) identity 30 == .ok no
#guard observe lambda (.outgoingUniversal .bottom) identity 30 == .ok yes
#guard observe lambda (.possibility (.possibility .top)) beta 30 == .ok no
#guard observe lambda (.imp (.constructor "App") (.possibility (.constructor "Lam"))) beta 30 == .ok yes
#guard observe lambda (.constructor "Missing") identity 10 == .ok (.unknownConstructor "Missing")
#guard observe lambda .top (.bvar 0) 10 == .ok (.checked (.sourceRefused .illScopedOrSorted))
#guard observe lambda .top normal 10 == .ok (.checked (.sourceRefused .illScopedOrSorted))
#guard observe lambdaNoBeta (.possibility .top) beta 30 == .ok no
#guard observe lambda (.possibility .top) guardedBeta 30 == .ok yes
#guard observe lambdaNoBinderReduction (.possibility .top) guardedBeta 30 == .ok no
#guard observe lambdaFiniteLogic (.neg (.constructor "Lam")) identity 10 == .ok (.checked (.judgment (.refused .negation)))
#guard observe lambdaFiniteLogic (.constructor "Lam") identity 10 == .ok yes
#guard observe lambdaBox (.constructor "Lam") identity 10 == .ok no

#guard observe machine (.constructor "Normal") normal 10 == .ok yes
#guard observe machine (.constructor "Ret") normal 10 == .ok no
#guard observe machine (.possibility (.constructor "Ret")) normal 0 == .ok pending
#guard observe machine (.possibility (.constructor "Ret")) normal 300 == .ok yes
#guard observe machine (.possibility (.constructor "Halt")) normal 300 == .ok no
#guard observe machine (.possibility (.possibility (.constructor "Halt"))) normal 300 == .ok yes
#guard observe machine (.outgoingUniversal (.constructor "Ret")) normal 300 == .ok yes
#guard observe machine (.outgoingUniversal (.constructor "Halt")) normal 300 == .ok no
#guard observe machine (.possibility .top) halt 300 == .ok no
#guard observe machine (.outgoingUniversal .bottom) halt 300 == .ok yes
#guard observe machine (.constructor "Normal") halt 300 == .ok no
#guard observe machine .top identity 10 == .ok (.checked (.sourceRefused .illScopedOrSorted))

/-- The generic entry point admits the unchanged authored machine; there is
no branch testing its name or replacing its presentation. -/
def localMachine : Except GenerationIssue Installed :=
  generate (.authored Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.vertex [] (.base "Cfg") Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.syntaxMask)

def localObserve (query : Query) (source : Pattern) (budget : Nat) :=
  localMachine.map fun installed => (Executable.ask installed query source budget).readout

#guard localMachine.isOk
#guard localObserve (.constructor "Normal") normal 10 == .ok yes
#guard localObserve (.possibility (.constructor "Ret")) normal 300 == .ok yes
#guard localObserve (.possibility (.constructor "Halt")) normal 300 == .ok no
#guard localObserve (.outgoingUniversal (.constructor "Ret")) normal 300 == .ok yes
#guard localObserve (.possibility .top) halt 300 == .ok no
#guard localObserve (.outgoingUniversal .bottom) halt 300 == .ok yes

theorem any_displayed_positive_is_true (request : Request) (installed : Installed)
    (generated : generate request = .ok installed) (query : Query) (source : Pattern) (budget : Nat)
    (read : observe request query source budget = .ok yes) :
    Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning installed.native query source := by
  rw [observe, generated] at read
  exact ask_positive installed query source budget (Except.ok.inj read)

theorem any_displayed_negative_is_false (request : Request) (installed : Installed)
    (generated : generate request = .ok installed) (query : Query) (source : Pattern) (budget : Nat)
    (read : observe request query source budget = .ok no) :
    ¬ Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning installed.native query source := by
  rw [observe, generated] at read
  exact ask_negative installed query source budget (Except.ok.inj read)

end Mettapedia.OSLF.NativeTypes.Runtime.Controls
