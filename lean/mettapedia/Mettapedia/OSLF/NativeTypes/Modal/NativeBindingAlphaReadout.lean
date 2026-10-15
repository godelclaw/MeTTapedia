import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingRendering
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical
import Mettapedia.OSLF.MeTTaIL.ScopedStepPremise

/-!
# Alpha readout of actual contextual program substitutions

Original binder display labels are retained in authored declarations and
receipts. Their semantic readout erases display metadata, with an earned
comparison to substitution by actual canonical program arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingAlphaReadout

open Mettapedia.OSLF.MeTTaIL Syntax

theorem erase_substitution (assignment : ContextSubstitution.Assignment)
    (canonical : ∀ index, (assignment index).hasCanonicalBinderMetadata = true) (pattern : Pattern) :
    (ContextSubstitution.substitute assignment pattern).eraseBinderMetadata =
      ContextSubstitution.substitute assignment pattern.eraseBinderMetadata := by
  rw [eraseBinderMetadata_substitute]
  have same : (fun index => (assignment index).eraseBinderMetadata) = assignment := by
    funext index
    exact Pattern.eraseBinderMetadata_eq_self_of_canonical (canonical index)
  rw [same]

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingAlphaReadout
