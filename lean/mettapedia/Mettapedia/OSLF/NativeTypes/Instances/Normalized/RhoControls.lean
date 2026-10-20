import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoProfile
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Meaning
import Mettapedia.OSLF.NativeTypes.Executable

/-!
# Native rho quote-drop query controls

The same COMM source is checked with equal quote-drop names, literally equal
names and distinct names. Source admission, retained receipts, negative answers
and interrupted native checking are separate controls.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open RhoProfile

def zero : Pattern := .apply "PZero" []
def quote (body : Pattern) : Pattern := .apply "NQuote" [body]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name payload : Pattern) : Pattern := .apply "POutput" [name, payload]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def par (children : List Pattern) : Pattern := .collection .hashBag children none

def communication (sent : Pattern) : Pattern :=
  par [output sent zero, input (quote zero) (drop (.bvar 0))]

def positive : Pattern := communication (quote (drop (quote zero)))
def canonical : Pattern := communication (quote zero)
def negative : Pattern := communication (quote (par []))

def doneFormula : profile.driver.Formula := .atom ⟨0, by decide⟩

def decision (formula : profile.driver.Formula) (source : Pattern) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Runtime.search profile.driver profile.engine formula source budget

#guard profile.profileChoice.status == some true
#guard form positive == form canonical
#guard form positive != form negative
#guard (decision (.possibility doneFormula) positive 0).readout == .judgment .unknown
#guard (decision (.possibility doneFormula) positive 1).readout == .judgment .unknown
#guard (decision (.possibility doneFormula) positive 40).readout == .judgment (.decided true)
#guard (decision (.possibility doneFormula) canonical 40).readout == .judgment (.decided true)
#guard (decision (.possibility doneFormula) negative 40).readout == .judgment (.decided false)
#guard (decision (.possibility doneFormula) done 40).readout == .judgment (.decided false)
#guard (decision (.outgoingUniversal doneFormula) positive 40).readout == .judgment (.decided true)
#guard (decision (.outgoingUniversal .bottom) positive 40).readout == .judgment (.decided false)
#guard (decision (.possibility doneFormula) malformed 40).readout == .sourceRefused .illScopedOrSorted
#guard (profile.engine.cursor.tasks positive).flatten.length == 1
#guard (decision (.outgoingUniversal doneFormula) positive 40).observations.map
    (fun observed => observed.receipt.job.declaration.declarationIndex) == [0]
#guard (Mettapedia.OSLF.NativeTypes.Runtime.resume 39
    (decision (.possibility doneFormula) positive 1)).readout ==
  (decision (.possibility doneFormula) positive 40).readout
#guard (Mettapedia.OSLF.NativeTypes.Runtime.resume 39
    (decision (.possibility doneFormula) positive 1)).spent ==
  (decision (.possibility doneFormula) positive 40).spent

def request : Executable.Request :=
  .normalized GeneralRho.snapshot fragment Structural.heytingFragment vertex [] proc profile

def publicObserve (source : Pattern) (budget : Nat) :=
  (Executable.generate request).map fun installed =>
    (Executable.ask installed (.possibility (.constructor "Done")) source budget).readout

#guard (Executable.generate request).map (fun _ => ()) == .ok ()
#guard publicObserve positive 0 == .ok (.checked (.judgment .unknown))
#guard publicObserve positive 40 == .ok (.checked (.judgment (.decided true)))
#guard publicObserve canonical 40 == .ok (.checked (.judgment (.decided true)))
#guard publicObserve negative 40 == .ok (.checked (.judgment (.decided false)))
#guard publicObserve malformed 40 == .ok (.checked (.sourceRefused .illScopedOrSorted))

/-- The computed native possibility denotes actual quotient COMM, rather
than an unrelated predicate on an encoded execution trace. -/
theorem native_possibility_iff_receipt (source : Pattern) :
    (gsltOSLF (Complete.QuoteDropCoherence.gslt plan [] proc presentation)).satisfies source
      (profile.sourceNativeType (.possibility doneFormula)).pred ↔
    ∃ receipt ∈ RhoPrimitive.receipts (form source), form receipt.target = done := by
  change gsltDiamond (profile.policy.sourceSystem generated [] proc)
    (profile.sourceTests ⟨0, by decide⟩).predicate source ↔ _
  refine (gsltDiamond_spec (profile.policy.sourceSystem generated [] proc)
    (profile.sourceTests ⟨0, by decide⟩).predicate source).trans ?_
  change (∃ target, (profile.policy.sourceSystem generated [] proc).Step source target ∧
    ((form target) == done) = true) ↔ _
  simp only [beq_iff_eq]
  exact possibility_iff_receipt source done

end Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoControls
