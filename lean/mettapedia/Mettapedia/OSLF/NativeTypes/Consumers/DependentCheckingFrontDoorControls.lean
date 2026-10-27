import Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingFrontDoor
import Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingControls

/-!
# Controls: supplied dependent steps through the front door

The tower's certificates, each asked through the front door on the system it presents, with the kernel evaluating
the answers:

- the formed directional β step: `typed ∧ ◇typed` holds (an exploration of one round), so the source has the native
  type;
- a certificate whose source request is forged, and one whose step goes the other way: the formula fails on their
  systems (closed regions). A rejected certificate is no refutation of the native type, which the β certificate
  inhabits.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking.FrontDoorControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Controls

/-- The front door's answer on a certificate's system, at its source. -/
def answer {source target : Tm Tower.Head 0}
    (certificate : Certificate Tower.Checking.decoder (.nil : Tower.Ctx 0) source target Tower.Checking.Controls.sortTerm)
    (rounds : ℕ) : Answer :=
  ask ((certificateSystem Tower.Checking.decoder certificate).unfolded (false, source)).observed.env [] systemLanguage 2
    typedStep (pathPattern []) none rounds

theorem beta_answer : answer betaCertificate 1 = .proved (.exploration 1) := by decide +kernel

/-- **The formed β step has the native type**, by the front door on its certificate's system. -/
theorem beta_native_frontDoor :
    (gsltOSLF (theory Tower.rules 0)).satisfies (S := ()) Tower.Checking.Controls.beta
      (nativeType Tower.rules .nil Tower.Checking.Controls.sortTerm Tower.Checking.Controls.ground).pred :=
  (native_iff_frontDoor Tower.Checking.decoder .nil _ _ _).mpr ⟨betaCertificate, ask_proved beta_answer⟩

theorem forged_answer : answer forgedSource 2 = .refuted (.closedRegion 2) := by decide +kernel

/-- **A forged source request fails** on its system. -/
theorem forged_fails : forgedSource.check Tower.Checking.decoder = false := by
  cases checked : forgedSource.check Tower.Checking.decoder with
  | false => rfl
  | true => exact absurd ((check_iff_frontDoor _ forgedSource).mp checked) (ask_refuted forged_answer)

theorem reverse_answer : answer reverseCertificate 2 = .refuted (.closedRegion 2) := by decide +kernel

/-- **A step the other way fails** on its system. -/
theorem reverse_fails : reverseCertificate.check Tower.Checking.decoder = false := by
  cases checked : reverseCertificate.check Tower.Checking.decoder with
  | false => rfl
  | true => exact absurd ((check_iff_frontDoor _ reverseCertificate).mp checked) (ask_refuted reverse_answer)

end Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking.FrontDoorControls
