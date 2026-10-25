import Mathlib.Logic.Equiv.Defs

/-!
# Displayed exact evidence and gradual precision

An exact capability may be displayed over an unchanged raw value without
turning the raw language, propositions, or theoremhood into approximate
objects.  A status is suspended, carries exact evidence, or carries a local
refutation.  Precision fills a suspension but never changes the raw index.

The central characterization is observer-relative: an observation satisfies
the dynamic gradual guarantee exactly when it factors through the raw value.
Evidence-sensitive observations need not be gradual, and a negative control
shows that this distinction is real.

Exact evidence transports covariantly along constructional maps.  Refutations
do not: they transport only when the map also reflects exact evidence.
Without reflection, safe transport returns a refutation to suspension.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedEvidence

universe uRaw uExact uReason uRaw' uExact' uOutput

-- Raw values and their displayed evidence have independent universe bounds.
-- The bundled family combines those bounds only in its result sort.
set_option linter.checkUnivs false in
/-- An exact evidence family displayed over a raw carrier. -/
structure Family where
  Raw : Type uRaw
  Exact : Raw → Type uExact

/-- A proof-relevant reason why exact evidence is impossible at one raw
value. -/
structure Refutation (family : Family.{uRaw, uExact})
    (Reason : Type uReason) (raw : family.Raw) where
  reason : Reason
  refutes : family.Exact raw → False

/-- Live evidence at one fixed raw value. -/
inductive Status (family : Family.{uRaw, uExact})
    (Reason : Type uReason) (raw : family.Raw) where
  | suspended
  | established (evidence : family.Exact raw)
  | refuted (obstruction : Refutation family Reason raw)

namespace Status

variable {family : Family.{uRaw, uExact}} {Reason : Type uReason}
  {raw : family.Raw}

/-- `Refines precise coarse` means that `precise` contains at least the
information of `coarse`.  Exact evidence and refutation both refine a
suspension; neither silently refines the other. -/
inductive Refines : Status family Reason raw → Status family Reason raw → Prop
  | refl (status : Status family Reason raw) : Refines status status
  | established_suspended (evidence : family.Exact raw) :
      Refines (.established evidence) .suspended
  | refuted_suspended (obstruction : Refutation family Reason raw) :
      Refines (.refuted obstruction) .suspended

namespace Refines

theorem trans {first middle last : Status family Reason raw}
    (firstMiddle : Refines first middle)
    (middleLast : Refines middle last) : Refines first last := by
  cases firstMiddle with
  | refl => exact middleLast
  | established_suspended evidence =>
      cases middleLast with
      | refl => exact .established_suspended evidence
  | refuted_suspended obstruction =>
      cases middleLast with
      | refl => exact .refuted_suspended obstruction

/-- Every evidence state refines the same suspended raw state. -/
theorem toSuspended (status : Status family Reason raw) :
    Refines status .suspended := by
  cases status with
  | suspended => exact .refl _
  | established evidence => exact .established_suspended evidence
  | refuted obstruction => exact .refuted_suspended obstruction

/-- Established evidence is rigid in the precision order. -/
theorem established_rigid {precise : Status family Reason raw}
    {evidence : family.Exact raw}
    (precision : Refines precise (.established evidence)) :
    precise = .established evidence := by
  cases precision
  rfl

/-- A current refutation is rigid in the precision order. -/
theorem refuted_rigid {precise : Status family Reason raw}
    {obstruction : Refutation family Reason raw}
    (precision : Refines precise (.refuted obstruction)) :
    precise = .refuted obstruction := by
  cases precision
  rfl

/-- Exact evidence cannot refine a refutation at the same raw value. -/
theorem established_not_refines_refuted (evidence : family.Exact raw)
    (obstruction : Refutation family Reason raw) :
    ¬ Refines (.established evidence) (.refuted obstruction) := by
  intro precision
  cases precision

end Refines

/-! ## Observer-relative graduality -/

/-- An observation ignores gradual evidence exactly when it factors through
the underlying raw value. -/
def FactorsThroughRaw {Output : Type uOutput} (observe :
    ∀ raw : family.Raw, Status family Reason raw → Output) : Prop :=
  ∃ readRaw : family.Raw → Output,
    ∀ (raw : family.Raw) (status : Status family Reason raw),
      observe raw status = readRaw raw

/-- A type-valued observation is precision invariant when refinement cannot
change its result type. -/
def PrecisionInvariant {Output : Type uOutput} (observe :
    ∀ raw : family.Raw, Status family Reason raw → Output) : Prop :=
  ∀ (raw : family.Raw) {precise coarse : Status family Reason raw},
    Refines precise coarse → observe raw precise = observe raw coarse

/-- The dynamic gradual guarantee is exactly raw factorization.  This theorem
states both the positive rule and its boundary: evidence-sensitive observers
are outside the guarantee unless a separate invariance theorem is supplied. -/
theorem factorsThroughRaw_iff_precisionInvariant
    {Output : Type uOutput}
    (observe : ∀ raw : family.Raw, Status family Reason raw → Output) :
    FactorsThroughRaw observe ↔ PrecisionInvariant observe := by
  constructor
  · rintro ⟨readRaw, factors⟩ raw precise coarse _precision
    rw [factors raw precise, factors raw coarse]
  · intro invariant
    refine ⟨fun raw => observe raw .suspended, ?_⟩
    intro raw status
    exact invariant raw (Refines.toSuspended status)

end Status

/-! ## Constructional maps and the variance of refutation -/

/-- A constructional map transports raw values and exact evidence forward. -/
structure ExactMap (source : Family.{uRaw, uExact})
    (target : Family.{uRaw', uExact'}) where
  mapRaw : source.Raw → target.Raw
  mapExact : {raw : source.Raw} →
    source.Exact raw → target.Exact (mapRaw raw)

namespace ExactMap

variable {source : Family.{uRaw, uExact}}
  {target : Family.{uRaw', uExact'}}

/-- Reflection is the extra property required to transport negative
evidence in the same direction as an exact map. -/
structure ReflectsExact (map : ExactMap source target) where
  reflect : {raw : source.Raw} →
    target.Exact (map.mapRaw raw) → source.Exact raw

/-- Safe covariant transport preserves exact evidence and invalidates a
refutation to suspension. -/
def mapSafe (map : ExactMap source target) {Reason : Type uReason}
    {raw : source.Raw} :
    Status source Reason raw → Status target Reason (map.mapRaw raw)
  | .suspended => .suspended
  | .established evidence => .established (map.mapExact evidence)
  | .refuted _ => .suspended

/-- Safe transport computes on established evidence without checking it again. -/
@[simp] theorem mapSafe_established (map : ExactMap source target)
    {Reason : Type uReason} {raw : source.Raw} (evidence : source.Exact raw) :
    map.mapSafe (Reason := Reason) (.established evidence) =
      .established (map.mapExact evidence) := rfl

/-- Forward transport alone cannot preserve a refutation. -/
@[simp] theorem mapSafe_refuted (map : ExactMap source target)
    {Reason : Type uReason} {raw : source.Raw} (obstruction : Refutation source Reason raw) :
    map.mapSafe (.refuted obstruction) = .suspended := rfl

/-- Transport negative evidence by the supplied reflection of exact evidence. -/
def mapRefutation (map : ExactMap source target) (reflection : map.ReflectsExact)
    {Reason : Type uReason} {raw : source.Raw} (obstruction : Refutation source Reason raw) :
    Refutation target Reason (map.mapRaw raw) where
  reason := obstruction.reason
  refutes := fun targetEvidence => obstruction.refutes (reflection.reflect targetEvidence)

/-- A reflecting exact map may transport refutation constructively. -/
def mapReflecting (map : ExactMap source target)
    (reflection : map.ReflectsExact) {Reason : Type uReason}
    {raw : source.Raw} :
    Status source Reason raw → Status target Reason (map.mapRaw raw)
  | .suspended => .suspended
  | .established evidence => .established (map.mapExact evidence)
  | .refuted obstruction => .refuted (map.mapRefutation reflection obstruction)

/-- Safe transport is monotone in precision. -/
theorem mapSafe_mono (map : ExactMap source target)
    {Reason : Type uReason} {raw : source.Raw}
    {precise coarse : Status source Reason raw}
    (precision : Status.Refines precise coarse) :
    Status.Refines (map.mapSafe precise) (map.mapSafe coarse) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      exact .established_suspended (map.mapExact evidence)
  | refuted_suspended obstruction => exact .refl _

/-- Reflecting transport is also monotone, while retaining refutations. -/
theorem mapReflecting_mono (map : ExactMap source target)
    (reflection : map.ReflectsExact)
    {Reason : Type uReason} {raw : source.Raw}
    {precise coarse : Status source Reason raw}
    (precision : Status.Refines precise coarse) :
    Status.Refines (map.mapReflecting reflection precise)
      (map.mapReflecting reflection coarse) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      exact .established_suspended (map.mapExact evidence)
  | refuted_suspended obstruction =>
      exact .refuted_suspended (map.mapRefutation reflection obstruction)

end ExactMap

/-! ## Positive and negative controls -/

namespace Canary

/-- A genuinely varying exact family: evidence is impossible at `false` and
inhabited at `true`. -/
def varying : Family where
  Raw := Bool
  Exact
    | false => PEmpty
    | true => PUnit

/-- The varying evidence family is not equivalent to one constant fibre. -/
theorem varying_not_constant :
    ¬ ∃ Uniform : Type,
      ∀ raw : varying.Raw, Nonempty ((varying.Exact raw) ≃ Uniform) := by
  rintro ⟨Uniform, uniform⟩
  obtain ⟨trueEquiv⟩ := uniform true
  obtain ⟨falseEquiv⟩ := uniform false
  have inhabitant : Uniform := trueEquiv.toFun PUnit.unit
  have impossible : PEmpty := by
    exact falseEquiv.symm.toFun inhabitant
  exact PEmpty.elim impossible

/-- A raw-indexed observation ignores evidence. -/
def rawObservation (raw : varying.Raw)
    (_status : Status varying Unit raw) : Bool := raw

theorem rawObservation_is_gradual :
    Status.PrecisionInvariant rawObservation := by
  rw [← Status.factorsThroughRaw_iff_precisionInvariant]
  exact ⟨id, fun _ _ => rfl⟩

/-- A small constant family used to show that evidence-sensitive observation
does not satisfy the gradual guarantee automatically. -/
def unitFamily : Family where
  Raw := Unit
  Exact := fun _ => Unit

def evidenceObservation (_raw : unitFamily.Raw) :
    Status unitFamily Unit () → Bool
  | .suspended => false
  | .established _ => true
  | .refuted _ => true

/-- Negative control: observing whether evidence is present does not factor
through raw semantics and changes along a precision refinement. -/
theorem evidenceObservation_not_gradual :
    ¬ Status.PrecisionInvariant evidenceObservation := by
  intro invariant
  have changed := invariant ()
    (Status.Refines.established_suspended (family := unitFamily)
      (Reason := Unit) ())
  simp [evidenceObservation] at changed

/-- An empty source family maps covariantly into an inhabited target family,
but cannot reflect exact evidence. -/
def emptyFamily : Family where
  Raw := Unit
  Exact := fun _ => Empty

def emptyToUnit : ExactMap emptyFamily unitFamily where
  mapRaw := id
  mapExact := fun impossible => nomatch impossible

def emptyRefutation : Refutation emptyFamily Unit () where
  reason := ()
  refutes := fun impossible => nomatch impossible

theorem safe_transport_invalidates_unreflected_refutation :
    emptyToUnit.mapSafe (.refuted emptyRefutation) =
      (Status.suspended : Status unitFamily Unit ()) :=
  rfl

/-- Negative evidence cannot be transported to the inhabited target: this is
why reflection is a real obligation rather than bookkeeping. -/
theorem target_refutation_impossible :
    ¬ Nonempty (Refutation unitFamily Unit ()) := by
  rintro ⟨obstruction⟩
  exact obstruction.refutes ()

end Canary

/-! ## Axiom audit -/

#print axioms Status.Refines.trans
#print axioms Status.factorsThroughRaw_iff_precisionInvariant
#print axioms ExactMap.mapSafe_mono
#print axioms ExactMap.mapReflecting_mono
#print axioms Canary.varying_not_constant
#print axioms Canary.rawObservation_is_gradual
#print axioms Canary.evidenceObservation_not_gradual
#print axioms Canary.target_refutation_impossible


/-! ## Products, dependent sums and construction squares -/

universe uRawTwo uExactTwo uKey uRetry uRevision

namespace Family

/-- Product of two displayed capabilities.  Its raw carrier is the ordinary
product, while exactness retains evidence for both components. -/
def product (left : Family.{uRaw, uExact})
    (right : Family.{uRaw', uExact'}) :
    Family.{max uRaw uRaw', max uExact uExact'} where
  Raw := left.Raw × right.Raw
  Exact := fun raw => left.Exact raw.1 × right.Exact raw.2

/-- Dependent sum of displayed capabilities.  The second raw carrier and its
exact evidence may depend on the first raw value. -/
def sigma (base : Family.{uRaw, uExact})
    (next : base.Raw -> Family.{uRaw', uExact'}) :
    Family.{max uRaw uRaw', max uExact uExact'} where
  Raw := Sigma fun raw => (next raw).Raw
  Exact := fun raw => base.Exact raw.1 × (next raw.1).Exact raw.2

end Family
namespace Status

variable {Reason : Type uReason}

/-! ## Constructional combination -/

/-- Combine two gradual capabilities.  Exact evidence is constructed only
when both components are exact.  Every other combination retains the raw
pair and suspends the optional product capability; component blame cannot be
promoted to blame for the product without an additional reflection law. -/
def combine {left : Family.{uRaw, uExact}}
    {right : Family.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw} :
    Status (Reason := Reason) left leftRaw -> Status (Reason := Reason) right rightRaw ->
      Status (Reason := Reason) (Family.product left right) (leftRaw, rightRaw)
  | .established leftEvidence, .established rightEvidence =>
      .established (leftEvidence, rightEvidence)
  | _, _ => .suspended

theorem combine_left_mono {left : Family.{uRaw, uExact}}
    {right : Family.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw} {refined coarse : Status (Reason := Reason) left leftRaw}
    (precision : Refines refined coarse) (rightState : Status (Reason := Reason) right rightRaw) :
    Refines (combine refined rightState) (combine coarse rightState) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      cases rightState with
      | established rightEvidence =>
          show Refines
            (Status.established (family := Family.product left right)
              (raw := (leftRaw, rightRaw)) (evidence, rightEvidence))
            (Status.suspended (family := Family.product left right)
              (raw := (leftRaw, rightRaw)))
          exact @Refines.established_suspended (Family.product left right)
            Reason (leftRaw, rightRaw) (evidence, rightEvidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases rightState <;> exact .refl _

theorem combine_right_mono {left : Family.{uRaw, uExact}}
    {right : Family.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw} (leftState : Status (Reason := Reason) left leftRaw)
    {refined coarse : Status (Reason := Reason) right rightRaw}
    (precision : Refines refined coarse) :
    Refines (combine leftState refined) (combine leftState coarse) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      cases leftState with
      | established leftEvidence =>
          show Refines
            (Status.established (family := Family.product left right)
              (raw := (leftRaw, rightRaw)) (leftEvidence, evidence))
            (Status.suspended (family := Family.product left right)
              (raw := (leftRaw, rightRaw)))
          exact @Refines.established_suspended (Family.product left right)
            Reason (leftRaw, rightRaw) (leftEvidence, evidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases leftState <;> exact .refl _

/-- Product combination is monotone in both precision coordinates. -/
theorem combine_mono {left : Family.{uRaw, uExact}}
    {right : Family.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw}
    {leftRefined leftCoarse : Status (Reason := Reason) left leftRaw}
    {rightRefined rightCoarse : Status (Reason := Reason) right rightRaw}
    (leftPrecision : Refines leftRefined leftCoarse)
    (rightPrecision : Refines rightRefined rightCoarse) :
    Refines (combine leftRefined rightRefined)
      (combine leftCoarse rightCoarse) :=
  Refines.trans
    (combine_left_mono leftPrecision rightRefined)
    (combine_right_mono leftCoarse rightPrecision)

/-- Dependent capability combination retains the dependency of the second
fibre on the unchanged first raw value. -/
def combineDependent {base : Family.{uRaw, uExact}}
    {next : base.Raw -> Family.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw} :
    Status (Reason := Reason) base baseRaw -> Status (Reason := Reason) (next baseRaw) nextRaw ->
      Status (Reason := Reason) (Family.sigma base next) ⟨baseRaw, nextRaw⟩
  | .established baseEvidence, .established nextEvidence =>
      .established (baseEvidence, nextEvidence)
  | _, _ => .suspended

theorem combineDependent_left_mono {base : Family.{uRaw, uExact}}
    {next : base.Raw -> Family.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw}
    {refined coarse : Status (Reason := Reason) base baseRaw}
    (precision : Refines refined coarse)
    (nextState : Status (Reason := Reason) (next baseRaw) nextRaw) :
    Refines (combineDependent refined nextState)
      (combineDependent coarse nextState) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      cases nextState with
      | established nextEvidence =>
          show Refines
            (Status.established (family := Family.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩) (evidence, nextEvidence))
            (Status.suspended (family := Family.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩))
          exact @Refines.established_suspended (Family.sigma base next)
            Reason ⟨baseRaw, nextRaw⟩ (evidence, nextEvidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases nextState <;> exact .refl _

theorem combineDependent_right_mono {base : Family.{uRaw, uExact}}
    {next : base.Raw -> Family.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw} (baseState : Status (Reason := Reason) base baseRaw)
    {refined coarse : Status (Reason := Reason) (next baseRaw) nextRaw}
    (precision : Refines refined coarse) :
    Refines (combineDependent baseState refined)
      (combineDependent baseState coarse) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      cases baseState with
      | established baseEvidence =>
          show Refines
            (Status.established (family := Family.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩) (baseEvidence, evidence))
            (Status.suspended (family := Family.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩))
          exact @Refines.established_suspended (Family.sigma base next)
            Reason ⟨baseRaw, nextRaw⟩ (baseEvidence, evidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases baseState <;> exact .refl _

theorem combineDependent_mono {base : Family.{uRaw, uExact}}
    {next : base.Raw -> Family.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw}
    {baseRefined baseCoarse : Status (Reason := Reason) base baseRaw}
    {nextRefined nextCoarse : Status (Reason := Reason) (next baseRaw) nextRaw}
    (basePrecision : Refines baseRefined baseCoarse)
    (nextPrecision : Refines nextRefined nextCoarse) :
    Refines (combineDependent baseRefined nextRefined)
      (combineDependent baseCoarse nextCoarse) :=
  Refines.trans
    (combineDependent_left_mono basePrecision nextRefined)
    (combineDependent_right_mono baseCoarse nextPrecision)

end Status

namespace ExactMap

/-- Exact maps compose in the same direction as constructional execution. -/
def comp {first : Family.{uRaw, uExact}}
    {second : Family.{uRaw', uExact'}}
    {third : Family.{uRawTwo, uExactTwo}}
    (later : ExactMap second third) (earlier : ExactMap first second) :
    ExactMap first third where
  mapRaw := fun raw => later.mapRaw (earlier.mapRaw raw)
  mapExact := fun evidence => later.mapExact (earlier.mapExact evidence)

/-- Identity transports both the raw value and exact evidence unchanged. -/
def id (fibre : Family.{uRaw, uExact}) : ExactMap fibre fibre where
  mapRaw := fun raw => raw
  mapExact := fun evidence => evidence

def reflects_id (fibre : Family.{uRaw, uExact}) :
    (ExactMap.id fibre).ReflectsExact := by
  exact ⟨fun evidence => evidence⟩

def reflects_comp {first : Family.{uRaw, uExact}}
    {second : Family.{uRaw', uExact'}}
    {third : Family.{uRawTwo, uExactTwo}}
    {later : ExactMap second third} {earlier : ExactMap first second}
    (laterReflects : later.ReflectsExact)
    (earlierReflects : earlier.ReflectsExact) :
    (later.comp earlier).ReflectsExact := by
  exact ⟨fun evidence =>
    earlierReflects.reflect (laterReflects.reflect evidence)⟩

/-! ### Proof-relevant construction squares -/

/-- A commuting square of constructional capability maps.  Raw commutation
is stated as equality of the constructed values.  Exact commutation is
proof-relevant and therefore uses heterogeneous equality: before the raw
square is identified, the two pieces of exact evidence inhabit fibres over
propositionally equal rather than definitionally equal raw values. -/
structure Square {northWest : Family.{uRaw, uExact}}
    {northEast : Family.{uRaw', uExact'}}
    {southWest : Family.{uRawTwo, uExactTwo}}
    {southEast : Family.{uKey, uRetry}}
    (north : ExactMap northWest northEast)
    (west : ExactMap northWest southWest)
    (east : ExactMap northEast southEast)
    (south : ExactMap southWest southEast) where
  raw_commutes : ∀ raw,
    east.mapRaw (north.mapRaw raw) = south.mapRaw (west.mapRaw raw)
  exact_commutes : ∀ {raw} (evidence : northWest.Exact raw),
    HEq (east.mapExact (north.mapExact evidence))
      (south.mapExact (west.mapExact evidence))

end ExactMap

namespace ExactMap.Square

variable {Reason : Type uReason}

private theorem suspended_heq_of_raw_eq
    {fibre : Family.{uRaw, uExact}} {leftRaw rightRaw : fibre.Raw}
    (rawEquality : leftRaw = rightRaw) :
    HEq (Status.suspended : Status (Reason := Reason) fibre leftRaw)
      (Status.suspended : Status (Reason := Reason) fibre rightRaw) := by
  subst rightRaw
  rfl

private theorem exact_heq_of_raw_eq_of_evidence_heq
    {fibre : Family.{uRaw, uExact}} {leftRaw rightRaw : fibre.Raw}
    {leftEvidence : fibre.Exact leftRaw}
    {rightEvidence : fibre.Exact rightRaw}
    (rawEquality : leftRaw = rightRaw)
    (evidenceEquality : HEq leftEvidence rightEvidence) :
    HEq (Status.established (Reason := Reason) leftEvidence)
      (Status.established (Reason := Reason) rightEvidence) := by
  subst rightRaw
  have equalEvidence : leftEvidence = rightEvidence := eq_of_heq evidenceEquality
  subst rightEvidence
  rfl

/-- A construction square commutes on all safely transported gradual states.
This includes suspended and refuted inputs: safe maps deliberately invalidate
blame unless reflection has separately been proved, so neither route can
smuggle a negative judgment into the target fibre. -/
theorem mapSafe_commutes {northWest : Family.{uRaw, uExact}}
    {northEast : Family.{uRaw', uExact'}}
    {southWest : Family.{uRawTwo, uExactTwo}}
    {southEast : Family.{uKey, uRetry}}
    {north : ExactMap northWest northEast}
    {west : ExactMap northWest southWest}
    {east : ExactMap northEast southEast}
    {south : ExactMap southWest southEast}
    (square : ExactMap.Square north west east south)
    {raw : northWest.Raw} (state : Status (Reason := Reason) northWest raw) :
    HEq (mapSafe east (mapSafe north state))
      (mapSafe south (mapSafe west state)) := by
  cases state with
  | suspended =>
      exact suspended_heq_of_raw_eq (square.raw_commutes raw)
  | refuted blame =>
      exact suspended_heq_of_raw_eq (square.raw_commutes raw)
  | established evidence =>
      exact exact_heq_of_raw_eq_of_evidence_heq
        (square.raw_commutes raw) (square.exact_commutes evidence)

end ExactMap.Square
namespace Status.Refines

theorem mapSafe {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}} {map : ExactMap source target}
    {Reason : Type uReason} {raw : source.Raw}
    {precise coarse : Status source Reason raw} (precision : Status.Refines precise coarse) :
    Status.Refines (map.mapSafe precise) (map.mapSafe coarse) :=
  ExactMap.mapSafe_mono map precision

theorem mapReflecting {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}} {map : ExactMap source target}
    (reflection : map.ReflectsExact) {Reason : Type uReason} {raw : source.Raw}
    {precise coarse : Status source Reason raw} (precision : Status.Refines precise coarse) :
    Status.Refines (map.mapReflecting reflection precise)
      (map.mapReflecting reflection coarse) :=
  ExactMap.mapReflecting_mono map reflection precision

end Status.Refines

namespace Status

variable {family : Family.{uRaw, uExact}} {Reason : Type uReason} {raw : family.Raw}

/-! ## Revision invalidation -/

/-- Forget all cached capability evidence while retaining the raw index. -/
def invalidate (_state : Status (Reason := Reason) family raw) : Status (Reason := Reason) family raw := .suspended

theorem refines_invalidate (state : Status (Reason := Reason) family raw) :
    Refines state state.invalidate := by
  cases state with
  | suspended => exact .refl _
  | established evidence => exact .established_suspended evidence
  | refuted blame => exact .refuted_suspended blame

/-- A cached state is active only at its exact revision. -/
def activateAt {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) (state : Status (Reason := Reason) family raw) : Status (Reason := Reason) family raw :=
  if cached = current then state else state.invalidate

@[simp] theorem activateAt_current {Revision : Type uRevision}
    [DecidableEq Revision]
    (revision : Revision) (state : Status (Reason := Reason) family raw) :
    state.activateAt revision revision = state := by
  simp [activateAt]

theorem activateAt_stale {Revision : Type uRevision} [DecidableEq Revision]
    {cached current : Revision} (stale : cached ≠ current)
    (state : Status (Reason := Reason) family raw) :
    state.activateAt cached current = .suspended := by
  simp [activateAt, stale, invalidate]

end Status

#print axioms Status.combine_mono
#print axioms Status.combineDependent_mono
#print axioms ExactMap.Square.mapSafe_commutes


/-! ## Composition and revision coherence of evidence transport -/

universe uRaw'' uExact''

section TransportCoherence

open Status

variable {Reason : Type uReason}

namespace ExactMap

/-- Safe transport is compositional.  In the negative case both sides forget
the unsupported blame at the first forward-only boundary. -/
@[simp] theorem mapSafe_comp
    {first : Family.{uRaw, uExact}}
    {second : Family.{uRaw', uExact'}}
    {third : Family.{uRaw'', uExact''}}
    (later : ExactMap second third) (earlier : ExactMap first second)
    {raw : first.Raw} (state : Status (Reason := Reason) first raw) :
    mapSafe later (mapSafe earlier state) =
      mapSafe (later.comp earlier) state := by
  cases state <;> rfl

/-- The safe identity map is identity on suspension and exact evidence.  On
blame it performs the deliberate forward-only invalidation. -/
theorem mapSafe_id_refines
    {fibre : Family.{uRaw, uExact}} {raw : fibre.Raw}
    (state : Status (Reason := Reason) fibre raw) :
    Refines state (mapSafe (ExactMap.id fibre) state) := by
  cases state with
  | suspended => exact .refl _
  | established evidence => exact .refl _
  | refuted blame => exact .refuted_suspended blame

/-- Once exact reflection is supplied, identity transport preserves every
state, including its local blame path. -/
@[simp] theorem mapReflecting_id
    {fibre : Family.{uRaw, uExact}} {raw : fibre.Raw}
    (state : Status (Reason := Reason) fibre raw) :
    mapReflecting (ExactMap.id fibre) (ExactMap.reflects_id fibre) state = state := by
  cases state <;> rfl

/-- Reflecting transport is fully functorial, including proof-relevant blame.
The reflection proof is the extra capability that makes the negative case
sound. -/
@[simp] theorem mapReflecting_comp
    {first : Family.{uRaw, uExact}}
    {second : Family.{uRaw', uExact'}}
    {third : Family.{uRaw'', uExact''}}
    (later : ExactMap second third) (earlier : ExactMap first second)
    (laterReflects : later.ReflectsExact)
    (earlierReflects : earlier.ReflectsExact)
    {raw : first.Raw} (state : Status (Reason := Reason) first raw) :
    mapReflecting later laterReflects (mapReflecting earlier earlierReflects state) =
      mapReflecting (later.comp earlier)
        (ExactMap.reflects_comp laterReflects earlierReflects) state := by
  cases state <;> rfl

/-! ## Revision coherence -/

/-- Revision activation commutes with every safe constructional map. -/
theorem mapSafe_activateAt
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}}
    (map : ExactMap source target)
    {raw : source.Raw} {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) (state : Status (Reason := Reason) source raw) :
    mapSafe map (state.activateAt cached current) =
      (mapSafe map state).activateAt cached current := by
  by_cases same : cached = current
  · subst current
    simp
  · simp [activateAt, same, invalidate]
    rfl

/-- Revision activation also commutes with reflecting transport, so stable
blame is retained exactly while current and forgotten exactly when stale. -/
theorem mapReflecting_activateAt
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}}
    (map : ExactMap source target) (reflects : map.ReflectsExact)
    {raw : source.Raw} {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) (state : Status (Reason := Reason) source raw) :
    mapReflecting map reflects (state.activateAt cached current) =
      (mapReflecting map reflects state).activateAt cached current := by
  by_cases same : cached = current
  · subst current
    simp
  · simp [activateAt, same, invalidate]
    rfl

/-- Laws earned by every forward constructional map.  This is the exact
capability SemanticService may request from a native realization without assuming
reflection of negative evidence. -/
structure SafeTransportLaws
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}} (map : ExactMap source target) : Prop where
  exact_preserved : forall {raw : source.Raw} (evidence : source.Exact raw),
    mapSafe (Reason := Reason) map (.established evidence) = .established (map.mapExact evidence)
  blame_invalidated : forall {raw : source.Raw}
    (blame : Refutation (Reason := Reason) source raw),
    mapSafe map (.refuted blame) = .suspended
  precision_monotone : forall {raw : source.Raw}
    {refined coarse : Status (Reason := Reason) source raw}, Refines refined coarse ->
      Refines (mapSafe map refined) (mapSafe map coarse)

/-- Every constructional map earns the safe laws without replaying a checker
or manufacturing a negative judgment. -/
theorem safeTransportLaws
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}} (map : ExactMap source target) :
    SafeTransportLaws (Reason := Reason) map where
  exact_preserved := fun _ => rfl
  blame_invalidated := fun _ => rfl
  precision_monotone := fun precision => precision.mapSafe

/-- Strong transport laws are earned only by an exact-reflecting map. -/
structure ReflectingTransportLaws
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}} (map : ExactMap source target)
    (reflects : map.ReflectsExact) : Prop where
  exact_preserved : forall {raw : source.Raw} (evidence : source.Exact raw),
    mapReflecting (Reason := Reason) map reflects (.established evidence) = .established (map.mapExact evidence)
  blame_preserved : forall {raw : source.Raw}
    (blame : Refutation (Reason := Reason) source raw),
    mapReflecting map reflects (.refuted blame) =
      .refuted ⟨blame.reason, fun evidence => blame.refutes (reflects.reflect evidence)⟩
  precision_monotone : forall {raw : source.Raw}
    {refined coarse : Status (Reason := Reason) source raw}, Refines refined coarse ->
      Refines (mapReflecting map reflects refined) (mapReflecting map reflects coarse)

theorem reflectingTransportLaws
    {source : Family.{uRaw, uExact}}
    {target : Family.{uRaw', uExact'}} (map : ExactMap source target)
    (reflects : map.ReflectsExact) : ReflectingTransportLaws (Reason := Reason) map reflects where
  exact_preserved := fun _ => rfl
  blame_preserved := fun _ => rfl
  precision_monotone := fun precision => Status.Refines.mapReflecting reflects precision

/-- Reflection is a genuine additional capability: identity earns it. -/
theorem identityReflectingTransportLaws
    (fibre : Family.{uRaw, uExact}) :
    ReflectingTransportLaws (Reason := Reason) (ExactMap.id fibre)
      (ExactMap.reflects_id fibre) :=
  reflectingTransportLaws _ _

/-- Every proof-relevant construction square earns state-level naturality for
suspension, exact evidence, and safely invalidated blame. -/
structure SafeSquareLaws
    {northWest : Family.{uRaw, uExact}}
    {northEast : Family.{uRaw', uExact'}}
    {southWest : Family.{uRaw'', uExact''}}
    {southEast : Family.{uKey, uRetry}}
    {north : ExactMap northWest northEast}
    {west : ExactMap northWest southWest}
    {east : ExactMap northEast southEast}
    {south : ExactMap southWest southEast}
    (square : ExactMap.Square north west east south) : Prop where
  gradual_commutes : forall {raw : northWest.Raw}
    (state : Status (Reason := Reason) northWest raw),
    HEq (mapSafe east (mapSafe north state))
      (mapSafe south (mapSafe west state))

theorem safeSquareLaws
    {northWest : Family.{uRaw, uExact}}
    {northEast : Family.{uRaw', uExact'}}
    {southWest : Family.{uRaw'', uExact''}}
    {southEast : Family.{uKey, uRetry}}
    {north : ExactMap northWest northEast}
    {west : ExactMap northWest southWest}
    {east : ExactMap northEast southEast}
    {south : ExactMap southWest southEast}
    (square : ExactMap.Square north west east south) : SafeSquareLaws (Reason := Reason) square :=
  ⟨square.mapSafe_commutes⟩

end ExactMap

namespace Status

/-- Independent native premises can be revision-activated before or after
their constructional product is formed. -/
theorem combine_activateAt
    {left : Family.{uRaw, uExact}}
    {right : Family.{uRaw', uExact'}}
    {leftRaw : left.Raw} {rightRaw : right.Raw}
    {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision)
    (leftState : Status (Reason := Reason) left leftRaw) (rightState : Status (Reason := Reason) right rightRaw) :
    (Status.combine leftState rightState).activateAt cached current =
      Status.combine (leftState.activateAt cached current)
        (rightState.activateAt cached current) := by
  by_cases same : cached = current
  · subst current
    simp [activateAt]
  · simp [activateAt, same, invalidate, Status.combine]

/-- The same revision law holds for genuinely dependent Sigma premises; the
second fibre remains indexed by the unchanged first raw value. -/
theorem combineDependent_activateAt
    {base : Family.{uRaw, uExact}}
    {next : base.Raw -> Family.{uRaw', uExact'}}
    {baseRaw : base.Raw} {nextRaw : (next baseRaw).Raw}
    {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision)
    (baseState : Status (Reason := Reason) base baseRaw)
    (nextState : Status (Reason := Reason) (next baseRaw) nextRaw) :
    (Status.combineDependent baseState nextState).activateAt cached current =
      Status.combineDependent (baseState.activateAt cached current)
        (nextState.activateAt cached current) := by
  by_cases same : cached = current
  · subst current
    simp [activateAt]
  · simp [activateAt, same, invalidate, Status.combineDependent]

end Status

end TransportCoherence

end Mettapedia.TypeTheory.DisplayedEvidence
