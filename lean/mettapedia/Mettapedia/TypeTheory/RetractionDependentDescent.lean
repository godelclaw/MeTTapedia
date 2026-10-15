import Mathlib.Logic.Equiv.Defs

/-!
# Dependent section descent along a map with a supplied section

A section of the readout map gives an explicit reconstruction. A dependent
consumer descends precisely when its values agree, after transport, on
each readout fibre. The reconstruction is unique, and restriction and
reconstruction give an equivalence of complete dependent sections.

The section is independently supplied; the theorem does not assert that
its composite with the readout is the identity on the retained source.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RetractionDependentDescent

universe u v w u' v' w'

variable {Source : Type u} {Target : Type v}
variable (readout : Source → Target) (representative : Target → Source)
variable (represents : Function.RightInverse representative readout)
variable (family : Target → Type w)

def Compatible (consumer : (source : Source) → family (readout source)) : Prop :=
  ∀ first second, readout first = readout second → HEq (consumer first) (consumer second)

theorem compatible_iff_transport (consumer : (source : Source) → family (readout source)) :
    Compatible readout family consumer ↔
      ∀ first second (same : readout first = readout second),
        cast (congrArg family same) (consumer first) = consumer second := by
  constructor
  · intro compatible first second same
    exact eq_of_heq ((cast_heq _ _).trans (compatible first second same))
  · intro transported first second same
    exact (cast_heq _ _).symm.trans (heq_of_eq (transported first second same))

def restrict (consumer : (target : Target) → family target) :
    (source : Source) → family (readout source) := fun source => consumer (readout source)

theorem section_congr (consumer : (target : Target) → family target)
    {first second : Target} (same : first = second) : HEq (consumer first) (consumer second) := by
  cases same
  rfl

theorem restrict_compatible (consumer : (target : Target) → family target) :
    Compatible readout family (restrict readout family consumer) :=
  fun _ _ same => section_congr family consumer same

def descend (consumer : (source : Source) → family (readout source)) :
    (target : Target) → family target :=
  fun target => cast (congrArg family (represents target)) (consumer (representative target))

theorem descend_beta (consumer : (source : Source) → family (readout source))
    (compatible : Compatible readout family consumer) (source : Source) :
    descend readout representative represents family consumer (readout source) = consumer source :=
  eq_of_heq ((cast_heq _ _).trans (compatible (representative (readout source)) source
    (represents (readout source))))

theorem descend_eta (consumer : (target : Target) → family target) (target : Target) :
    descend readout representative represents family (restrict readout family consumer) target = consumer target :=
  eq_of_heq ((cast_heq _ _).trans (section_congr family consumer (represents target)))

def sectionsEquiv :
    {consumer : ((source : Source) → family (readout source)) // Compatible readout family consumer} ≃
      ((target : Target) → family target) where
  toFun consumer := descend readout representative represents family consumer.val
  invFun consumer := ⟨restrict readout family consumer, restrict_compatible readout family consumer⟩
  left_inv consumer := by
    apply Subtype.ext
    funext source
    exact descend_beta readout representative represents family consumer.val consumer.property source
  right_inv consumer := funext (descend_eta readout representative represents family consumer)

theorem unique_descent (consumer : (source : Source) → family (readout source))
    (targetConsumer : (target : Target) → family target)
    (agrees : restrict readout family targetConsumer = consumer) :
    targetConsumer = descend readout representative represents family consumer := by
  calc
    targetConsumer = descend readout representative represents family
        (restrict readout family targetConsumer) :=
      (funext (descend_eta readout representative represents family targetConsumer)).symm
    _ = descend readout representative represents family consumer :=
      congrArg (descend readout representative represents family) agrees

include representative represents in
theorem descent_exists_iff (consumer : (source : Source) → family (readout source)) :
    (∃ targetConsumer : (target : Target) → family target,
      restrict readout family targetConsumer = consumer) ↔ Compatible readout family consumer := by
  constructor
  · rintro ⟨targetConsumer, rfl⟩
    exact restrict_compatible readout family targetConsumer
  · intro compatible
    exact ⟨descend readout representative represents family consumer,
      funext (descend_beta readout representative represents family consumer compatible)⟩

theorem dependent_apply_congr {Result : Target → Type w'}
    (action : (target : Target) → family target → Result target)
    {first second : Target} (same : first = second)
    {value : family first} {other : family second} (values : HEq value other) :
    HEq (action first value) (action second other) := by
  cases same
  cases values
  rfl

variable {NextSource : Type u'} {NextTarget : Type v'}

/-- Reconstruction commutes with a supplied dependent action even when
the two independently chosen representatives do not commute with it. -/
theorem descend_commutes
    (nextReadout : NextSource → NextTarget) (nextRepresentative : NextTarget → NextSource)
    (nextRepresents : Function.RightInverse nextRepresentative nextReadout)
    (nextFamily : NextTarget → Type w')
    (sourceMap : Source → NextSource) (targetMap : Target → NextTarget)
    (readout_natural : ∀ source, nextReadout (sourceMap source) = targetMap (readout source))
    (action : (target : Target) → family target → nextFamily (targetMap target))
    (consumer : (source : Source) → family (readout source))
    (nextConsumer : (source : NextSource) → nextFamily (nextReadout source))
    (nextCompatible : Compatible nextReadout nextFamily nextConsumer)
    (consumer_natural : ∀ source,
      HEq (action (readout source) (consumer source)) (nextConsumer (sourceMap source)))
    (target : Target) :
    HEq (action target (descend readout representative represents family consumer target))
      (descend nextReadout nextRepresentative nextRepresents nextFamily nextConsumer
        (targetMap target)) := by
  have reconstructed : HEq
      (action target (descend readout representative represents family consumer target))
      (action (readout (representative target)) (consumer (representative target))) :=
    dependent_apply_congr family action (represents target).symm (cast_heq _ _)
  have next_same : nextReadout (sourceMap (representative target)) = targetMap target :=
    (readout_natural _).trans (congrArg targetMap (represents target))
  exact reconstructed.trans ((consumer_natural _).trans
    ((heq_of_eq (descend_beta nextReadout nextRepresentative nextRepresents nextFamily
      nextConsumer nextCompatible (sourceMap (representative target)))).symm.trans
      (section_congr nextFamily
        (descend nextReadout nextRepresentative nextRepresents nextFamily nextConsumer) next_same)))

end Mettapedia.TypeTheory.RetractionDependentDescent
