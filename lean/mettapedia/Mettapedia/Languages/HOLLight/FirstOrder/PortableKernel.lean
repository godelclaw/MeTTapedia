import Mettapedia.Languages.HOLLight.FirstOrder.Multifunctor
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.Languages.HOLLight.FirstOrder.Validation

/-!
# HOL Light's kernel as a portable module

The first-order calculus of HOL Light over a finite axiom list is a validated
calculus, so it has a portable module rendering. Reading the rendering back
through the verified reader and the original calculus validator recovers exactly
the same validated package (`kernelModule_read`). The loaded package is faithful
to HOL Light: it derives the rendering of a sequent exactly when HOL Light's ten
rules and the admitted axioms derive a theorem with that sequent
(`kernelModule_faithful`).

Loading a module grants no theorem authority beyond what the original validator
admits; definitions and type definitions extend the theory and are replayed
separately by the export receiver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic

/-- The portable module of HOL Light's first-order calculus over an axiom list. -/
def kernelModule (axioms : List Sequent) : String :=
  ModuleFormat.Portable.renderCalculus (validatedHolCalculus axioms).val

/-- **Exact loading.** The verified reader and validator recover the package. -/
theorem kernelModule_read (axioms : List Sequent) :
    ModuleFormat.Portable.readValidatedCalculus? (kernelModule axioms) =
      some (validatedHolCalculus axioms) :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

/-- **Faithfulness of the loaded package.** For axiom lists admitted by a policy
that admits nothing else, the loaded calculus derives the rendering of a sequent
exactly when HOL Light derives a theorem with that sequent. -/
theorem kernelModule_faithful (axioms : List Sequent) (policy : AxiomPolicy) [DecidablePred policy]
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    {loaded : ValidatedCalculusLanguageDef}
    (read : ModuleFormat.Portable.readValidatedCalculus? (kernelModule axioms) = some loaded)
    (sequent : Sequent) :
    RuleSignature.Derivable (CertificateGSLT.ruleSignature loaded) (sequentJ sequent) ↔
      ∃ out : Theorem, Derives (Rule policy) out ∧ out.sequent = sequent := by
  rw [kernelModule_read] at read
  cases Option.some.inj read
  have calculus : (validatedHolCalculus axioms).1 = holCalculus axioms := rfl
  constructor
  · exact translation_reflects calculus admitted inList sequent
  · rintro ⟨out, derived, rfl⟩
    exact translation_derivable calculus inList derived

/-- The bare kernel's module loads exactly. -/
theorem bareKernelModule_read :
    ModuleFormat.Portable.readValidatedCalculus? (kernelModule []) = some (validatedHolCalculus []) :=
  kernelModule_read []

end Mettapedia.Languages.HOLLight.FirstOrder
