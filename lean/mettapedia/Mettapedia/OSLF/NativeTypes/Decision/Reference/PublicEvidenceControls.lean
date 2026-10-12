import Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence
import Mettapedia.OSLF.NativeTypes.Runtime.Atoms
import Mettapedia.OSLF.NativeTypes.Runtime.Controls

open Mettapedia.OSLF.Framework

/-!
# Reference invariant-atom and horizon-evidence controls

These controls compare the explicit horizon reference implementation with
its structural and atomic semantics. They do not measure the retained total
work machine. Recorded reference decisions expose their stopping horizon. Requesting the associated receipt view preserves
coverage status and original physical origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidenceControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Admission
open Mettapedia.OSLF.NativeTypes.Runtime.Description Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax
open Mettapedia.OSLF.Binding LambdaContextualRung LambdaScopedAuthoringComparison

def base : Driver := Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.driver {} []

/-- These total numeric tests are invariant under the equation-free source
presentation. Their truth still depends on the supplied program. -/
def sizeTest (threshold : Nat) : Test base.system base.admitted :=
  Test.ofBoolean
    ⟨fun source => Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount source ≤ threshold, by
      intro first second related
      change first = second at related
      subst second
      rfl⟩
    (fun source => decide (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier.nodeCount source ≤ threshold))
    (fun _ => decide_eq_true_iff)

def atomicAdmission : LeafAdmission Nat where
  admitted _ := True
  probe _ := .ok ()
  exact _ := ⟨fun _ => trivial, fun _ => rfl⟩

def observed : Driver := Mettapedia.OSLF.NativeTypes.Runtime.Atoms.extend base sizeTest atomicAdmission

def atomAnswer (formula : observed.Formula) (source : Pattern) (budget : Nat) :=
  (Mettapedia.OSLF.NativeTypes.Runtime.Description.search observed formula source budget).readout

def joinedAnswer : Option Mettapedia.OSLF.NativeTypes.Runtime.Description.Readout := do
  let constructor ← (elaborate base (.constructor "Lam")).toOption
  pure (atomAnswer (.conj (Mettapedia.OSLF.NativeTypes.Runtime.Atoms.structural constructor) (.atom (.inr 3)))
    Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity 20)

#guard atomAnswer (.atom (.inr 3)) Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity 20 == .judgment (.decided true)
#guard atomAnswer (.atom (.inr 1)) Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity 20 == .judgment (.decided false)
#guard atomAnswer (.atom (.inr 3)) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 20 == .judgment (.decided false)
#guard atomAnswer (.possibility (.atom (.inr 3))) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 20 == .judgment (.decided true)
#guard atomAnswer (.outgoingUniversal (.atom (.inr 1))) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 20 == .judgment (.decided false)
#guard atomAnswer (.outgoingUniversal (.atom (.inr 0))) Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity 20 == .judgment (.decided true)
#guard joinedAnswer == some (.judgment (.decided true))

def readReport (driver : Driver) (query : Query) (source : Pattern) (budget : Nat) :=
  (elaborate driver query).map fun formula =>
    let report := Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence.search driver formula source budget
    (report.readout, report.horizon)

def readCoverage (driver : Driver) (query : Query) (source : Pattern) (budget : Nat) :=
  (elaborate driver query).map fun formula =>
    let report := Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence.search driver formula source budget
    report.frontier.map fun retained => (retained.2.receipts.length, retained.2.closed)

#guard readReport base (.possibility (.constructor "Lam")) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 0 ==
  .ok (.judgment .unknown, some 0)
#guard readReport base (.possibility (.constructor "Lam")) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 100 ==
  readReport base (.possibility (.constructor "Lam")) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 1000
#guard readReport base (.outgoingUniversal .bottom) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 100 ==
  readReport base (.outgoingUniversal .bottom) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 1000
#guard readCoverage base (.possibility .top) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 100 == .ok (some (1, false))
#guard readCoverage base (.outgoingUniversal .top) Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 100 == .ok (some (1, true))
#guard readCoverage base (.possibility .top) Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity 100 == .ok (some (0, true))
#guard readReport base .top (.bvar 0) 100 == .ok (.sourceRefused .illScopedOrSorted, none)
#guard readReport (Mettapedia.OSLF.NativeTypes.Instances.Lambda.Driver.driver
    {logic := Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment} []) (.neg .top)
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity 100 == .ok (.judgment (.refused .negation), none)

theorem reported_positive (query : Query) (source : Pattern) (budget : Nat)
    (formula : base.Formula) (resolved : Resolves base query formula)
    (read : (Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence.search base formula source budget).readout =
      .judgment (.decided true)) : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning base query source :=
  ⟨formula, resolved, Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence.positive base formula source _ read⟩

theorem reported_negative (query : Query) (source : Pattern) (budget : Nat)
    (formula : base.Formula) (resolved : Resolves base query formula)
    (read : (Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence.search base formula source budget).readout =
      .judgment (.decided false)) : ¬ Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning base query source := by
  rintro ⟨other, otherResolved, holds⟩
  have same := resolution_unique resolved otherResolved
  subst other
  exact Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidence.negative base formula source _ read holds

end Mettapedia.OSLF.NativeTypes.Decision.Reference.PublicEvidenceControls
