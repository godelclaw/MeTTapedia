import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitModalCharacteristic
import Mettapedia.GSLT.Logic.InterfaceModalAdequacy

/-!
# Actual modal, structural and payload observations on generated kit values

The finite modal characteristic is compiled from the hereditarily admitted
source tree. Agreement on all interface-correct modal formulas therefore
recovers its complete class against an arbitrary supported native value.
This derives the comparison with actual IPO and same-fixed-point payload
bisimilarity without a finite-branching assumption on arbitrary source rules.

Outside this generated-left domain, the generic modal soundness still holds;
full finitary completeness needs the actual target-fibre condition proved in
the common subject layer. Finite kit permissions alone do not discharge it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit.Modal

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.InterfaceModalLogic

universe u v w z

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {OriginalOrigins : Type z} {NativeOrigins : Type w}
variable (opened : Policy source Parallel)
  (originalRules : OriginalOrigins → ReactionRule (.origin : SourceCategory source Parallel))

theorem logicallyEquivalent_iff_embedded_equal_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (left : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened left)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (rightSupported : ClassSupported opened right) :
    LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (value (classEmbedding left) (classEmbedding_supported opened left))
      (value right rightSupported) ↔ classEmbedding left = right := by
  constructor
  · obtain ⟨representative, permitted, rfl⟩ := generated
    intro related
    have selfHolds := (characteristic_iff opened originalRules origins representative permitted
      (classOf (embed representative)) ⟨_, embed_supported opened representative, rfl⟩).mpr rfl
    have recovered := (related (characteristic opened representative permitted)).mp selfHolds
    exact (characteristic_iff opened originalRules origins representative permitted right rightSupported).mp recovered
  · rintro rfl
    exact logicallyEquivalent_refl _ _

theorem logicallyEquivalent_iff_source_equal_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (first second : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened first) :
    LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (value (classEmbedding first) (classEmbedding_supported opened first))
      (value (classEmbedding second) (classEmbedding_supported opened second)) ↔ first = second :=
  (logicallyEquivalent_iff_embedded_equal_of_generated opened originalRules origins first generated
    (classEmbedding second) (classEmbedding_supported opened second)).trans
      ⟨fun same => classEmbedding_injective same, congrArg classEmbedding⟩

theorem actual_ipo_iff_modal_observation_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (left : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened left)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (rightSupported : ClassSupported opened right) :
    IPOBisimilar (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
      (value (classEmbedding left) (classEmbedding_supported opened left))
      (value right rightSupported) ↔
        LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
          (value (classEmbedding left) (classEmbedding_supported opened left)) (value right rightSupported) :=
  (observer_bisimilar_iff_embedded_equal_of_generated opened originalRules origins left generated right rightSupported).trans
    (logicallyEquivalent_iff_embedded_equal_of_generated opened originalRules origins left generated right rightSupported).symm

theorem actual_same_fixed_point_iff_modal_observation_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (left : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened left)
    (right : ValueClass (source := source) (Parallel := Parallel) (.original sort))
    (rightSupported : ClassSupported opened right) :
    (payloadSystem (NativeOrigins := NativeOrigins) opened originalRules).Bisimilar _ (classEmbedding left) right ↔
      LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
        (value (classEmbedding left) (classEmbedding_supported opened left)) (value right rightSupported) :=
  (payload_bisimilar_iff_embedded_equal_of_generated opened originalRules origins left generated right rightSupported).trans
    (logicallyEquivalent_iff_embedded_equal_of_generated opened originalRules origins left generated right rightSupported).symm

theorem independently_defined_partial_structural_iff_modal_of_generated (origins : Nonempty NativeOrigins)
    {sort : source.Srt} (first second : Class source Parallel sort)
    (generated : StructuralObservations.Generated opened first) :
    StructuralObservations.PartialLogicalEquivalent opened first second ↔
      LogicallyEquivalent (categoryRules (NativeOrigins := NativeOrigins) originalRules opened)
        (value (classEmbedding first) (classEmbedding_supported opened first))
        (value (classEmbedding second) (classEmbedding_supported opened second)) :=
  (StructuralObservations.partialLogicalEquivalent_iff_equal_of_generated opened first second generated).trans
    (logicallyEquivalent_iff_source_equal_of_generated opened originalRules origins first second generated).symm

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit.Modal
