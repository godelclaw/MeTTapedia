import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Profile
import Mettapedia.OSLF.NativeTypes.Runtime.Session

/-!
# Native meaning in the independent authored equation semantics

The normalized executor and the source presentation have different primitive
step encodings. Their comparison extends through every supported logical
connective and outgoing modality, and hence to actual native membership.
Observations retain their explicit normal-form interpretation throughout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized

open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

variable {generated : Generated} {bound : List TypeExpr} {expected : TypeExpr}

def Profile.sourceTests (profile : Profile generated bound expected) (leaf : profile.Leaf) :
    Test (profile.policy.sourceSystem generated bound expected) profile.admitted :=
  Test.ofBoolean
    ⟨fun source => profile.observations[leaf].observe (profile.nf source) = true, by
      intro first second related
      exact Iff.of_eq (congrArg
        (fun value => profile.observations[leaf].observe value = true)
        (profile.certificate.normalizer.eqvGen_eq related))⟩
    (fun source => profile.observations[leaf].observe (profile.nf source)) (fun _ => Iff.rfl)

theorem Profile.denotation_iff_source (profile : Profile generated bound expected)
    (formula : Formula profile.Leaf) (source : Pattern) :
    denotation profile.tests formula (.empty _) source ↔ denotation profile.sourceTests formula (.empty _) source := by
  induction formula generalizing source with
  | atom => rfl
  | top => rfl
  | bottom => rfl
  | separating _ _ _ _ _ =>
    simp [denotation, Mettapedia.OSLF.NativeTypes.Decision.Spatial.spatialPredicate,
      Mettapedia.OSLF.NativeTypes.Decision.Spatial.SpatialTheory.empty]
  | conj first second firstIH secondIH => exact and_congr (firstIH source) (secondIH source)
  | disj first second firstIH secondIH => exact or_congr (firstIH source) (secondIH source)
  | neg inner ih => exact not_congr (ih source)
  | imp first second firstIH secondIH => exact imp_congr (firstIH source) (secondIH source)
  | possibility inner ih =>
    change gsltDiamond profile.system (denotation profile.tests inner) source ↔
      gsltDiamond (profile.policy.sourceSystem generated bound expected)
        (denotation profile.sourceTests inner) source
    exact (gsltDiamond_spec profile.system (denotation profile.tests inner) source).trans
      ((exists_congr fun target => and_congr (profile.step_iff_source source target) (ih target)).trans
        (gsltDiamond_spec (profile.policy.sourceSystem generated bound expected)
          (denotation profile.sourceTests inner) source).symm)
  | outgoingUniversal inner ih =>
    change (∀ target, profile.system.Step source target → denotation profile.tests inner (.empty _) target) ↔
      (∀ target, (profile.policy.sourceSystem generated bound expected).Step source target →
        denotation profile.sourceTests inner (.empty _) target)
    exact forall_congr' fun target => imp_congr (profile.step_iff_source source target) (ih target)

def Profile.sourceNativeType (profile : Profile generated bound expected)
    (formula : Formula profile.Leaf) :
    GSLTNativeType (profile.policy.sourceSystem generated bound expected) :=
  nativeType profile.sourceTests formula

theorem Profile.native_membership_iff_source (profile : Profile generated bound expected)
    (formula : Formula profile.Leaf) (source : Pattern) :
    (gsltOSLF profile.system).satisfies source (nativeType profile.tests formula).pred ↔
      (gsltOSLF (profile.policy.sourceSystem generated bound expected)).satisfies source
        (profile.sourceNativeType formula).pred :=
  profile.denotation_iff_source formula source

theorem Profile.meaning_iff_source (profile : Profile generated bound expected)
    (formula : Formula profile.Leaf) (source : Pattern) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning profile.driver formula source ↔
      Source generated bound expected source ∧
        (gsltOSLF (profile.policy.sourceSystem generated bound expected)).satisfies source
          (profile.sourceNativeType formula).pred := by
  constructor
  · rintro ⟨term, typed, same, holds⟩
    change term = source at same
    subst term
    exact ⟨typed,
      (profile.denotation_iff_source formula source).mp holds⟩
  · rintro ⟨typed, holds⟩
    exact ⟨source, typed, rfl,
      (profile.denotation_iff_source formula source).mpr holds⟩

theorem Profile.positive_source (profile : Profile generated bound expected)
    {formula : Formula profile.Leaf} {source : Pattern}
    (session : Mettapedia.OSLF.NativeTypes.Runtime.Session profile.driver profile.engine formula source)
    (read : session.readout = .judgment (.decided true)) :
    Source generated bound expected source ∧
      (gsltOSLF (profile.policy.sourceSystem generated bound expected)).satisfies source
        (profile.sourceNativeType formula).pred :=
  (profile.meaning_iff_source formula source).mp
    (Mettapedia.OSLF.NativeTypes.Runtime.positive session read)

theorem Profile.negative_source (profile : Profile generated bound expected)
    {formula : Formula profile.Leaf} {source : Pattern}
    (session : Mettapedia.OSLF.NativeTypes.Runtime.Session profile.driver profile.engine formula source)
    (read : session.readout = .judgment (.decided false))
    (typed : Source generated bound expected source) :
    ¬ (gsltOSLF (profile.policy.sourceSystem generated bound expected)).satisfies source
        (profile.sourceNativeType formula).pred := by
  intro holds
  exact Mettapedia.OSLF.NativeTypes.Runtime.negative session read
    ((profile.meaning_iff_source formula source).mpr ⟨typed, holds⟩)

end Mettapedia.OSLF.NativeTypes.Instances.Normalized
