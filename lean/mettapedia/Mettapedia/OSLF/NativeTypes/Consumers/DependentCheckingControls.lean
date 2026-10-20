import Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TowerChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.FormationSensitiveRestrictionPreservation

/-! # Supplied typed steps distinguish direction, formation and profile pruning. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis


def betaCertificate : Certificate Tower.Checking.decoder (.nil : Tower.Ctx 0)
    Tower.Checking.Controls.beta Tower.Checking.Controls.ground Tower.Checking.Controls.sortTerm where
  source := Tower.Checking.Controls.request 6 Tower.Checking.Controls.beta Tower.Checking.Controls.sortTerm
  step := .betaPi (.var 0) Tower.Checking.Controls.ground
  target := Tower.Checking.Controls.request 0 Tower.Checking.Controls.ground Tower.Checking.Controls.sortTerm

/-- Both endpoints have certificates, but the selected step goes the other way. -/
def reverseCertificate : Certificate Tower.Checking.decoder (.nil : Tower.Ctx 0)
    Tower.Checking.Controls.ground Tower.Checking.Controls.beta Tower.Checking.Controls.sortTerm where
  source := Tower.Checking.Controls.request 0 Tower.Checking.Controls.ground Tower.Checking.Controls.sortTerm
  step := .betaPi (.var 0) Tower.Checking.Controls.ground
  target := Tower.Checking.Controls.request 6 Tower.Checking.Controls.beta Tower.Checking.Controls.sortTerm

def rawCertificate : Certificate Tower.Checking.decoder (.nil : Tower.Ctx 0)
    Tower.Checking.Controls.rawBeta (.app Tower.Checking.Controls.ground Tower.Checking.Controls.ground) Tower.Checking.Controls.sortTerm where
  source := Tower.Checking.Controls.request 6 Tower.Checking.Controls.rawBeta Tower.Checking.Controls.sortTerm
  step := .betaPi (.var 0) (.app Tower.Checking.Controls.ground Tower.Checking.Controls.ground)
  target := Tower.Checking.Controls.request 6 (.app Tower.Checking.Controls.ground Tower.Checking.Controls.ground) Tower.Checking.Controls.sortTerm

def forgedSource : Certificate Tower.Checking.decoder (.nil : Tower.Ctx 0)
    Tower.Checking.Controls.beta Tower.Checking.Controls.ground Tower.Checking.Controls.sortTerm :=
  {betaCertificate with source := Tower.Checking.Controls.request 99 Tower.Checking.Controls.beta Tower.Checking.Controls.sortTerm}

def forgedTarget : Certificate Tower.Checking.decoder (.nil : Tower.Ctx 0)
    Tower.Checking.Controls.beta Tower.Checking.Controls.ground Tower.Checking.Controls.sortTerm :=
  {betaCertificate with target := Tower.Checking.Controls.request 6 Tower.Checking.Controls.ground Tower.Checking.Controls.sortTerm}

def verdicts : List (String × Bool) :=
  [("formed directional beta", betaCertificate.check Tower.Checking.decoder),
   ("reverse conversion still valid",
     (StructuralConversionCode.Code.symm Tower.Checking.Controls.betaCode).check Tower.rules.headEq
       Tower.Checking.decoder.decode Tower.Checking.Controls.ground Tower.Checking.Controls.beta),
   ("reverse beta is not this supplied directional step",
     !(reverseCertificate.check Tower.Checking.decoder)),
   ("raw step alone accepted",
     rawCertificate.step.check Tower.rules.headEq Tower.Checking.decoder.decode
       Tower.Checking.Controls.rawBeta (.app Tower.Checking.Controls.ground Tower.Checking.Controls.ground)),
   ("raw step does not earn formed native type", !(rawCertificate.check Tower.Checking.decoder)),
   ("missing source graph root", !(forgedSource.check Tower.Checking.decoder)),
   ("wrong target graph root", !(forgedTarget.check Tower.Checking.decoder))]

theorem all_pass : verdicts.all Prod.snd = true := by decide

theorem beta_native :
    (gsltOSLF (theory Tower.rules 0)).satisfies (S := ()) Tower.Checking.Controls.beta
      (nativeType Tower.rules .nil Tower.Checking.Controls.sortTerm Tower.Checking.Controls.ground).pred :=
  betaCertificate.sound Tower.Checking.decoder (by decide)

/-- Rejection of supplied evidence does not mean the native type is empty. -/
theorem rejected_certificate_not_nonmembership :
    forgedSource.check Tower.Checking.decoder = false ∧
      (gsltOSLF (theory Tower.rules 0)).satisfies (S := ()) Tower.Checking.Controls.beta
        (nativeType Tower.rules .nil Tower.Checking.Controls.sortTerm Tower.Checking.Controls.ground).pred :=
  ⟨by decide, beta_native⟩

namespace Pruning

open FormationSensitive.RestrictionPreservation
open ConstantExpansion.Examples (secondAliasName)
open FormationSensitive.Dependencies.Examples (aliasName)

/-- The smaller package keeps the step and its source proof, but the
new typed-edge observation detects the omitted target declaration. -/
theorem bad_package_not_native :
    ¬ (gsltOSLF (theory (selected false) 0)).satisfies (S := ())
      (.const secondAliasName)
      (nativeType (selected false) .nil (sortTm Tower.zero) (.const aliasName)).pred := by
  intro member
  exact omitted_body_untypable
    ((native_exact _ _ _ _ _).mp member).2.2.typing

theorem repaired_package_native :
    (gsltOSLF (theory (selected true) 0)).satisfies (S := ())
      (.const secondAliasName)
      (nativeType (selected true) .nil (sortTm Tower.zero) (.const aliasName)).pred := by
  apply (native_exact _ _ _ _ _).mpr
  refine ⟨original_judgment true .nil .nil, .root (retained_step true), ?_⟩
  exact ⟨.nil, .const retained_body_lookup (.headType (.sort _)) (.sort _)⟩

/-- The earlier conversion query cannot distinguish this admission failure. -/
theorem conversion_and_typed_edge_separate :
    (gsltOSLF (FormationSensitiveCheckingOSLF.theory (selected false) 0)).satisfies
      (S := ()) (.const secondAliasName)
      (FormationSensitiveCheckingOSLF.conversionNativeType (selected false)
        (.const aliasName)).pred ∧
      ¬ (gsltOSLF (theory (selected false) 0)).satisfies (S := ())
        (.const secondAliasName)
        (nativeType (selected false) .nil (sortTm Tower.zero) (.const aliasName)).pred :=
  ⟨retained_conversion_oslf false, bad_package_not_native⟩

end Pruning
end Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking.Controls
