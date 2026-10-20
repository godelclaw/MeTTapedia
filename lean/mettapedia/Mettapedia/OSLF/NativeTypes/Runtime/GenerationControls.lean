import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls
import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

open Mettapedia.OSLF.Framework

/-!
# One generator on original presentations and rejected substitutions

The unchanged rho, scoped lambda and partial-recursive machine presentations
enter through the same generation function. Full snapshot and fragment checks
reject altered providers, equations, grammar and operational permissions.
The generic authored profile also accepts a renamed machine presentation;
language names do not select execution semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.GenerationControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Binding LambdaScopedAuthoringComparison
open Mettapedia.OSLF.NativeTypes.Executable
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open GeneralOccurrenceFrontier.CoverageClaims (snapshotKey)

def rhoRequest : Request := .canonicalRho Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot
  Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment {}

def lambdaRequest : Request := .scopedLambda Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment {}) {} []

def machineRequest : Request := .originalMachine Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment {} []

def status (request : Request) : Except GenerationIssue Unit := (generate request).map fun _ => ()

def observe (request : Request) (query : Query) (source : Pattern) (budget : Nat) :
    Except GenerationIssue Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout :=
  (generate request).map fun driver => (Executable.ask driver query source budget).readout

def yes : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout := .checked (.judgment (.decided true))
def no : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout := .checked (.judgment (.decided false))
def pending : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout := .checked (.judgment .unknown)

#guard status rhoRequest = .ok ()
#guard status lambdaRequest = .ok ()
#guard status machineRequest = .ok ()

#guard ((generate rhoRequest).map fun driver => snapshotKey driver.native.generated.snapshot) =
  .ok (snapshotKey rhoRequest.selectedSnapshot)
#guard ((generate lambdaRequest).map fun driver => snapshotKey driver.native.generated.snapshot) =
  .ok (snapshotKey lambdaRequest.selectedSnapshot)
#guard ((generate machineRequest).map fun driver => snapshotKey driver.native.generated.snapshot) =
  .ok (snapshotKey machineRequest.selectedSnapshot)

#guard observe rhoRequest (.constructor "PZero") Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.zero 10 = .ok yes
#guard observe rhoRequest (.possibility (.constructor "PZero"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 0 = .ok pending
#guard observe rhoRequest (.possibility (.constructor "PZero"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100 = .ok yes
#guard observe rhoRequest (.possibility .top)
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.guardedRedex 100 = .ok no

#guard observe lambdaRequest (.constructor "Lam")
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.identity) 10 = .ok yes
#guard observe lambdaRequest (.possibility (.constructor "Lam"))
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.redex) 0 = .ok pending
#guard observe lambdaRequest (.possibility (.constructor "Lam"))
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.redex) 30 = .ok yes
#guard observe lambdaRequest (.outgoingUniversal (.constructor "App"))
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.redex) 30 = .ok no

#guard observe machineRequest (.constructor "Normal") Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 10 = .ok yes
#guard observe machineRequest (.possibility (.constructor "Ret"))
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 0 = .ok pending
#guard observe machineRequest (.possibility (.constructor "Ret"))
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 300 = .ok yes
#guard observe machineRequest (.outgoingUniversal .bottom)
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.stopped 300 = .ok yes

def recorded (request : Request) (query : Query) (source : Pattern) (budget : Nat) :
    Except GenerationIssue (Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout × Nat × Nat) :=
  (generate request).map fun installed =>
    let session := Executable.ask installed query source budget
    (session.readout, session.spent, session.observations.length)

def resumed (request : Request) (query : Query) (source : Pattern) (first more : Nat) :
    Except GenerationIssue (Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout × Nat × Nat) :=
  (generate request).map fun installed =>
    let session := Mettapedia.OSLF.NativeTypes.Runtime.resumeQuery more (Executable.ask installed query source first)
    (session.readout, session.spent, session.observations.length)

#guard (recorded machineRequest (.possibility (.constructor "Ret"))
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 300).map (fun record => decide (record.2.1 ≤ 300)) = .ok true
#guard resumed machineRequest (.possibility (.constructor "Ret"))
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 7 293 = recorded machineRequest
    (.possibility (.constructor "Ret")) Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 300
#guard resumed rhoRequest (.possibility (.constructor "PZero"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 3 97 = recorded rhoRequest
    (.possibility (.constructor "PZero")) Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100
#guard recorded rhoRequest (.possibility (.constructor "PZero"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 1000 = recorded rhoRequest
    (.possibility (.constructor "PZero")) Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100

def changedGrammar : Snapshot :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot with language :=
    {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot.language with terms :=
      Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot.language.terms.drop 1}}

#guard status (.canonicalRho changedGrammar Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment {}) =
  .error (.snapshotMismatch .canonicalRho)

def changedProvider : Snapshot :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot with provider :=
    ⟨[⟨"foreign", [], []⟩], [⟨"foreign", []⟩], []⟩}

#guard status (.canonicalRho changedProvider Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment {}) =
  .error (.snapshotMismatch .canonicalRho)

def omittedEquation : Snapshot :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot with language :=
    {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot.language with equations := []}}

#guard status (.canonicalRho omittedEquation Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment {}) =
  .error (.snapshotMismatch .canonicalRho)

def disabledEquations : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment with operational :=
    {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment.operational with equationIndices := some []}}

#guard status (.canonicalRho Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot disabledEquations {}) =
  .error (.fragmentMismatch .canonicalRho)

def unrestrictedContexts : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment with operational :=
    {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment.operational with sites := .all}}

#guard status (.canonicalRho Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot unrestrictedContexts {}) =
  .error (.fragmentMismatch .canonicalRho)

def selectedConstructors : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment with constructorIndices := some [0]}

#guard status (.canonicalRho Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot selectedConstructors {}) =
  .error (.fragmentMismatch .canonicalRho)

def noBeta : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration := {rules := {beta := false}}

#guard status (.scopedLambda Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment {}) noBeta []) = .error (.fragmentMismatch .scopedLambda)

def noBetaRequest : Request := .scopedLambda Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment noBeta) noBeta []

#guard status noBetaRequest = .ok ()
#guard observe noBetaRequest (.possibility .top) (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.redex) 30 = .ok no

def finiteLogic : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration :=
  {logic := Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment}

def finiteLogicRequest : Request := .scopedLambda Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment finiteLogic) finiteLogic []

#guard observe finiteLogicRequest (.constructor "Lam")
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.identity) 10 = .ok yes
#guard observe finiteLogicRequest (.neg (.constructor "Lam"))
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.identity) 10 =
    .ok (.checked (.judgment (.refused .negation)))

def boxVertex : Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.Configuration :=
  {vertex := (fun _ => .box, fun _ => .box)}

def boxVertexRequest : Request := .scopedLambda Mettapedia.OSLF.NativeTypes.Instances.Lambda.Generated.snapshot
  (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.fragment boxVertex) boxVertex []

#guard status boxVertexRequest = .ok ()
#guard observe boxVertexRequest (.constructor "Lam")
  (encodeTerm Mettapedia.OSLF.NativeTypes.Instances.Lambda.Controls.identity) 10 = .ok no

def renamedMachine : Snapshot :=
  {Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot with language :=
    {Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot.language with name := "same-rules-another-name"}}

def renamedRequest : Request := .authored renamedMachine Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment
  Mettapedia.OSLF.NativeTypes.Structural.heytingFragment (fun _ => .star, fun _ => .star)
  [] (.base "Cfg") Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver.syntaxMask

#guard status renamedRequest = .ok ()
#guard observe renamedRequest (.possibility (.constructor "Ret"))
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source 300 = .ok yes
#guard status (.originalMachine renamedMachine Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment {} []) =
  .error (.snapshotMismatch .originalMachine)

def unsupportedEquationRequest : Request := .authored Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.snapshot
  {operational := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.permissions}
  Mettapedia.OSLF.NativeTypes.Structural.heytingFragment (fun _ => .star, fun _ => .star)
  [] Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.carrier (fun _ _ _ _ => true)

#guard status unsupportedEquationRequest = .error (.authoredLocal .equationCoverageRequired)

end Mettapedia.OSLF.NativeTypes.Runtime.GenerationControls
