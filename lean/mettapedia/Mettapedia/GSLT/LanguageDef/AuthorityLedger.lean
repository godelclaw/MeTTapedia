import Mettapedia.GSLT.LanguageDef.PresentationEvidence
import Mettapedia.Languages.MeTTa.HE.HELanguageDef

/-!
# Concrete presentation evidence

This ledger supplies `exactFragment` witnesses for MeTTaZero query and
evaluation requests, using the observation-indexed equations carried by their
`BagExact` realizations.  It supplies an `authoredProbe` notice for the HE presentation.  These entries record the evidence supplied
here; they do not assert that other evidence is absent elsewhere in the tree.

The generic evidence datatype lives in `PresentationEvidence`.  Its kinds are
not ordered authority levels.  A reported model does not supply a typed
interpretation, and exact equality with an exporter result does not establish
artifact execution correctness.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthorityLedger

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization
open Mettapedia.GSLT.LanguageDef.PresentationEvidence

/-! ## Positive witness: MeTTaZero query and evaluation are exact fragments -/

section MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZero

noncomputable def zeroQueryEvidence (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : Evidence language :=
  .exactFragment "query requests: atom-level `query` bag versus `zero-query` rewriting"
    (zeroQuery model space spaceTerm) rfl

noncomputable def zeroEvaluationEvidence (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : Evidence language :=
  .exactFragment "evaluation requests: atom-level `evaluateOne` bag versus `zero-evaluate` rewriting"
    (zeroEvaluate model space spaceTerm) rfl

theorem zeroQueryEvidence_kind (model : Model) (space : model.Space) (spaceTerm : Pattern) :
    (zeroQueryEvidence model space spaceTerm).kind = .exactFragment := rfl

end MeTTaZero

/-! ## Probe notices: no operational realization is supplied by these entries -/

/-- A notice for the HE presentation.  This entry makes no claim about which
simulation or adequacy theorems other modules provide. -/
def heEvidence : Evidence Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE :=
  .authoredProbe "mettaHE: this entry records the presentation without supplying an operational realization"

theorem heEvidence_kind : heEvidence.kind = .authoredProbe := rfl


end Mettapedia.GSLT.LanguageDef.AuthorityLedger
