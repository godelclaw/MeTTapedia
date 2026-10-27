import Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems

/-!
# Formation-preserving dependent steps through the front door

The consumer's native type at a source is "the source has the type, and it steps to the target, which has the type".
Its evidence is supplied, not searched: a certificate checks the source's typing, the selected step and the target's
typing. A certificate presents a finite system: the source, typed by its request, with one edge, checked by the step
code, to the target, typed by its request (`certificateSystem`). The front door asks it by its paths
(`PathSystems`):

- **a certificate checks exactly when the front door's `typed ∧ ◇typed` holds** at the source
  (`check_iff_frontDoor`);
- **the native type holds exactly when some certificate's system satisfies it** (`native_iff_frontDoor`), since every
  inhabitant has a certificate and every checked certificate is sound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PathSystems

variable {Head : Type} {n : Nat} {R : Rules Head} [DecidableEq Head] [DecidableRel R.headTyping]
    [DecidablePred R.isUniverse] [∀ u v w, Decidable (R.join u v w)]
    [DecidableRel R.cumulative] [DecidableRel R.headEq]

/-- A node of a certificate's system: the source (`false`) or the target (`true`), with its term. -/
abbrev Node (Head : Type) (n : Nat) := Bool × Tm Head n

/-- **The system a certificate presents**: the source, typed by its request, with one edge, checked by the step code,
to the target, typed by its request. -/
def certificateSystem (decoder : StructuralConversionCode.RootDecoder R.computation) {context : Ctx Head n}
    {source target type : Tm Head n} (certificate : Certificate decoder context source target type) :
    Listed (Node Head n) where
  successors
    | (false, _) => if certificate.step.check R.headEq decoder.decode source target then [(true, target)] else []
    | (true, _) => []
  observations name node :=
    name == "typed" &&
      match node with
      | (false, _) => certificate.source.check decoder
      | (true, _) => certificate.target.check decoder

/-- The source has the type, and steps to a node that has the type. -/
def typedStep : Formula 0 := .and (.inRelation "typed") (.possibly .any (.inRelation "typed"))

/-- **A certificate checks exactly when the front door's `typed ∧ ◇typed` holds** at the source of its system. -/
theorem check_iff_frontDoor (decoder : StructuralConversionCode.RootDecoder R.computation) {context : Ctx Head n}
    {source target type : Tm Head n} (certificate : Certificate decoder context source target type) :
    certificate.check decoder = true ↔
      ((certificateSystem decoder certificate).unfolded (false, source)).observed.reading.sat Env.closed typedStep
        (pathPattern []) := by
  change _ ↔ (_ ∧ _)
  rw [Listed.sat_observe_iff _ _ "typed" (Listed.reach_nil _ _),
    Listed.sat_possibly_iff _ _ Env.closed _ (Listed.reach_nil _ _)]
  simp only [Certificate.check, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨sourceChecked, stepChecked⟩, targetChecked⟩
    refine ⟨by simpa [certificateSystem] using sourceChecked, 0, by simp [certificateSystem, stepChecked], ?_⟩
    have reached : (certificateSystem decoder certificate).reach (false, source) ([] ++ [0]) = some (true, target) := by
      rw [Listed.reach_append, Listed.reach_nil]
      simp [certificateSystem, stepChecked]
    rw [Listed.sat_observe_iff _ _ "typed" reached]
    simpa [certificateSystem] using targetChecked
  · rintro ⟨sourceChecked, position, below, targetHolds⟩
    simp only [certificateSystem, beq_self_eq_true, Bool.true_and] at sourceChecked
    have stepChecked : certificate.step.check R.headEq decoder.decode source target = true := by
      by_contra unchecked
      simp [certificateSystem, unchecked] at below
    have positionZero : position = 0 := by
      simp [certificateSystem, stepChecked] at below
      omega
    subst positionZero
    have reached : (certificateSystem decoder certificate).reach (false, source) ([] ++ [0]) = some (true, target) := by
      rw [Listed.reach_append, Listed.reach_nil]
      simp [certificateSystem, stepChecked]
    rw [Listed.sat_observe_iff _ _ "typed" reached] at targetHolds
    simp only [certificateSystem, beq_self_eq_true, Bool.true_and] at targetHolds
    exact ⟨⟨sourceChecked, stepChecked⟩, targetHolds⟩

/-- **The native type holds exactly when some certificate's system satisfies `typed ∧ ◇typed`** at the source. -/
theorem native_iff_frontDoor (decoder : StructuralConversionCode.RootDecoder R.computation) (context : Ctx Head n)
    (source target type : Tm Head n) :
    (gsltOSLF (theory R n)).satisfies (S := ()) source (nativeType R context type target).pred ↔
      ∃ certificate : Certificate decoder context source target type,
        ((certificateSystem decoder certificate).unfolded (false, source)).observed.reading.sat Env.closed typedStep
          (pathPattern []) := by
  rw [native_iff_certificate decoder context source target type]
  exact exists_congr fun certificate => check_iff_frontDoor decoder certificate

end Mettapedia.OSLF.NativeTypes.Consumers.DependentChecking
