import Mettapedia.OSLF.Syntax.RhoIntrinsicSealedCanonical
import Mettapedia.OSLF.Syntax.RhoScopeQuotientControls

/-!
# Controls for the complete canonical comparison and sealing admission

The checked comparison covers commutative parallel variables, name eta and
input binders. Distinct process origins with one quoted name remain distinct.
A quotation repaired by name eta is admitted at its equation class, whereas
a surviving quoted output using the surrounding binder has no sealed
representative. A malformed name bag also exposes why sorted admission is
required for the raw canonical-readback comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoIntrinsicReadback

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

def firstVariable : Term sig [Srt.pr, Srt.pr] Srt.pr := .var .zero

def secondVariable : Term sig [Srt.pr, Srt.pr] Srt.pr := .var (.succ .zero)

theorem open_parallel_equality_decision :
    equationClassTest (project (parallel firstVariable secondVariable))
      (project (parallel secondVariable firstVariable)) = true :=
  (equationClassTest_true_iff _ _).mpr
    (Quotient.sound (parallel_commutes firstVariable secondVariable))

theorem distinct_open_variables_decision :
    equationClassTest (project firstVariable) (project secondVariable) = false := by decide +kernel

theorem name_eta_equality_decision :
    equationClassTest (project (quoteRaw (dropRaw (.var (.zero : Var [Srt.nm] Srt.nm)))))
      (project (.var (.zero : Var [Srt.nm] Srt.nm))) = true := by decide +kernel

theorem equal_quoted_names_distinct_decided_processes :
    quote suspended = quote visible ∧ equationClassTest suspended visible = false :=
  ⟨same_actual_name, (equationClassTest_false_iff _ _).mpr suspended_not_visible⟩

theorem repaired_quote_class_admitted :
    intrinsicQuoteSafe 0 crossingQuote = false ∧ quoteSafeClassTest (project crossingQuote) = true :=
  ⟨crossingQuote_intrinsically_unsafe,
    (quoteSafeClassTest_true_iff _).mpr crossingQuote_class_has_safe_representative⟩

def persistentQuotedBinder : Term sig [] Srt.pr :=
  inputRaw (quoteRaw null) (dropRaw (quoteRaw (outputRaw (.var .zero) null)))

theorem persistent_quoted_binder_rejected :
    quoteSafeClassTest (project persistentQuotedBinder) = false := by decide +kernel

theorem persistent_quoted_binder_has_no_sealed_representative :
    ¬ HasQuoteSafeRepresentative (project persistentQuotedBinder) := by
  intro safe
  have admitted := (quoteSafeClassTest_true_iff _).mpr safe
  rw [persistent_quoted_binder_rejected] at admitted
  cases admitted

theorem persistent_quoted_binder_readback :
    classRead [] Srt.pr (encodeEquationClass (project persistentQuotedBinder)) =
      some (project persistentQuotedBinder) := read_encoded_equation_class _

def malformedNameBag : Pattern := .collection .hashBag [.bvar 0] none

theorem malformed_name_bag_raw_rejected : readName [Srt.nm] malformedNameBag = none := rfl

theorem malformed_name_bag_normalized_accepted :
    readNameClass [Srt.nm] (canonicalize malformedNameBag) =
      some (project (.var (.zero : Var [Srt.nm] Srt.nm))) := by
  have normalized : canonicalize malformedNameBag = .bvar 0 := by
    simp [malformedNameBag, canonicalize, canonicalizeList, normalizeBagElements,
      bagSplice, sortPatterns, collapseBag]
  rw [normalized]
  rfl

theorem unrestricted_raw_name_readout_invariance_false :
    ¬ ∀ pattern, readNameClass [Srt.nm] (canonicalize pattern) = readNameClass [Srt.nm] pattern := by
  intro invariant
  have same := invariant malformedNameBag
  rw [malformed_name_bag_normalized_accepted] at same
  change some (project (.var (.zero : Var [Srt.nm] Srt.nm))) = none at same
  cases same

theorem current_closed_carrier_is_a_proper_admission :
    (∃ admitted : TermQ rhoSourceE [] Srt.pr, HasQuoteSafeRepresentative admitted) ∧
      (∃ rejected : TermQ rhoSourceE [] Srt.pr, ¬ HasQuoteSafeRepresentative rejected) :=
  ⟨⟨project crossingQuote, crossingQuote_class_has_safe_representative⟩,
    ⟨project persistentQuotedBinder, persistent_quoted_binder_has_no_sealed_representative⟩⟩

end Mettapedia.OSLF.Binding.RhoIntrinsicReadback
