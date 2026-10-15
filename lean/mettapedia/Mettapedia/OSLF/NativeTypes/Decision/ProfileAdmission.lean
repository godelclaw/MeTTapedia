import Mettapedia.OSLF.NativeTypes.Decision.Admission
import Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph

open Mettapedia.OSLF.Framework

/-!
# Explicit profile admission for native decisions

The original uniform equation-formation diagnostic and the finite displayed
profile contract are different judgments. This interface takes the computed
status of the chosen contract explicitly. It shares the existing connective
checker and semantic decision engine; the original generator record remains
available with its unchanged diagnostics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission

open Mettapedia.GSLT
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Admission

universe u v w

inductive Contract where
  | uniformEquationFormation
  | displayedProfile
  deriving DecidableEq, Repr

/-- Admission is computed from the selected contract. A displayed profile
must project to the actual generated vertex; callers cannot supply an
unrelated successful status. -/
inductive Choice (generated : Generated) where
  | uniform
  | displayed
      (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.Vertex generated.snapshot.language)
      (matching : List (Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.EquationMatching generated.snapshot.language))
      (projection : Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.project generated.snapshot.language vertex = generated.vertex)

def Choice.contract {generated : Generated} : Choice generated → Contract
  | .uniform => .uniformEquationFormation
  | .displayed _ _ _ => .displayedProfile

def Choice.status {generated : Generated} : Choice generated → Option Bool
  | .uniform => generated.equationAdmission
  | .displayed vertex matching _ =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.admit? generated.snapshot.language matching vertex

theorem displayed_status_exact (generated : Generated)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.Vertex generated.snapshot.language)
    (matching : List (Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.EquationMatching generated.snapshot.language))
    (projection : Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.project generated.snapshot.language vertex = generated.vertex) :
    (Choice.displayed vertex matching projection).status = some true ↔
      Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.carriersKnown generated.snapshot.language = true ∧
        Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.Consistent generated.snapshot.language matching vertex :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.admission_exact _ matching vertex

/-- Only the admission projection of the existing checker is adapted. The
catalogues, logical fragment, source snapshot and selected vertex are retained. -/
def checkingView (generated : Generated) (status : Option Bool) : Generated :=
  {generated with equationAdmission := status}

def check {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (status : Option Bool) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    Verdict (denotation tests formula source) :=
  Mettapedia.OSLF.NativeTypes.Decision.Admission.check (checkingView generated status)
    backend tests admission formula source budget

theorem original_contract {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    check generated generated.equationAdmission backend tests admission formula source budget =
      Mettapedia.OSLF.NativeTypes.Decision.Admission.check generated backend tests admission formula source budget := rfl

theorem complete {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (status : Option Bool) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term)
    (formed : Formed generated.logicFragment admission formula)
    (cube : status = some true) (sourceAdmitted : admitted source)
    (budget : Nat) (enough : workBound backend tests formula source ≤ budget) :
    ∃ answer, (check generated status backend tests admission formula source budget).readout = .decided answer :=
  Mettapedia.OSLF.NativeTypes.Decision.Admission.complete (checkingView generated status) backend tests admission
    formula source formed cube sourceAdmitted budget enough

theorem conclusive_mono {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (generated : Generated) (status : Option Bool) (backend : Backend.{u,v} system admitted)
    (tests : Leaf → Test system admitted) (admission : LeafAdmission Leaf)
    (formula : Formula Leaf) (source : system.Term) {small large : Nat} (answer : Bool)
    (read : (check generated status backend tests admission formula source small).readout = .decided answer)
    (ordered : small ≤ large) :
    (check generated status backend tests admission formula source large).readout = .decided answer :=
  Mettapedia.OSLF.NativeTypes.Decision.Admission.conclusive_mono (checkingView generated status) backend tests admission
    formula source answer read ordered

end Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission
