import Mettapedia.OSLF.Syntax.ScopedBindingEquationResources
import Mettapedia.OSLF.Syntax.ScopedBindingEquationNativePossibility

/-!
# Native target certificates joined to actual paid binding histories

A supplied native receipt already retains its event and dependent target
certificate. Funding adds an actual resource history whose complete firing
word is that event. It does not create a certificate from an affordable
price. Substitution transports the native certificate and preserves the
existence of funding for an index-based price profile.

These are paid paths in the declared linear state presentation, not a
concrete runtime or a claim about arbitrary state-dependent prices.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationFundedPossibility

open _root_.CategoryTheory ScopedEncoding ScopedEquationEvents
open ScopedEquationNativePossibility
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory

variable {S : Signature} {M : List (MetaArity S)} {Index : Type}
  {E : List (EqAxiom S M)} {rules : Index → UnpositionedRewrite (withMetas S M)}
  {permission : PositionPermission S} {sort : S.Srt}
  (postcondition : DisplayedFamily (values E sort))
  {point : (values E sort).Elements}
  (receipt : (possibilities E rules permission sort postcondition).obj point)
  (profile : Index → Nat) (amount : Nat)

noncomputable section

abbrev Funding :=
  ScopedEquationResources.PaidHistory E rules permission (point.1.unop.vars, sort) profile
    (receiptEvent postcondition receipt) amount

theorem funding_iff :
    Nonempty (Funding postcondition receipt profile amount) ↔
      profile (receiptEvent postcondition receipt).index ≤ amount :=
  ScopedEquationResources.paid_history_nonempty_iff E rules permission
    (point.1.unop.vars, sort) profile (receiptEvent postcondition receipt) amount

theorem funded_word_retains_event (funding : Funding postcondition receipt profile amount) :
    funding.eventWord = [receiptEvent postcondition receipt] :=
  ScopedEquationResources.PaidHistory.eventWord_eq E rules permission
    (point.1.unop.vars, sort) funding

theorem funding_preserved_under_substitution
    {after : (values E sort).Elements} (change : point ⟶ after) :
    Nonempty (Funding postcondition
      ((possibilities E rules permission sort postcondition).map change receipt) profile amount) ↔
        Nonempty (Funding postcondition receipt profile amount) := by
  rw [funding_iff, funding_iff, reindex_event]
  rfl

end

end Mettapedia.OSLF.Binding.ScopedEquationFundedPossibility
