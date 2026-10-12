import Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Original rho backend for compositional native decisions

The GSLT and equations come from the original authored rho presentation.
The decision engine receives the proved finite canonical successor algorithm,
including receipt origins, rather than a caller-supplied coverage oracle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical

def admitted (source : rhoReflectiveGSLT.Term) : Prop := admit source.1 = true

theorem every_carrier_admitted (source : rhoReflectiveGSLT.Term) : admitted source := by
  exact (admit_exact source.1).mpr (presentedRhoProcessEquiv source).2

def backend : Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.Backend rhoReflectiveGSLT admitted where
  Receipt := OriginalReceipt
  target := originalTarget
  frontier := originalFrontier
  closed budget source := closed budget source.1
  sound _ source receipt _ := originalTarget_sound source receipt
  coverage _ _ complete _ step := by
    obtain ⟨receipt, listed, related⟩ := originalFrontier_coverage complete step
    exact ⟨receipt, listed, rhoReflectiveGSLT.equations.symm related⟩
  target_admitted _ source _ receipt _ := originalTarget_admitted source receipt
  completionBudget source := completionBudget source.1
  complete_at source _ := complete_at source.1
  frontier_stable := originalFrontier_stable
  closed_stable source budget enough := closed_stable source.1 budget enough

#print axioms every_carrier_admitted
#print axioms backend

end Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend
