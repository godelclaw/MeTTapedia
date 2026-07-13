import Mathlib.Tactic

/-!
# PNP v13 CD-ENF normalization

The normal form has exactly three evidence leaf kinds: neutral, safe-buffer,
and hidden-gauge.  Boolean structure is preserved by a recursive normalizer.
Observer output is not a primitive raw constructor; it must be expanded by an
`observerToEvidence` map with a semantics theorem.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a

/-- Raw evidence before CD-ENF.  There is deliberately no observer-output
constructor here. -/
inductive RawEvidence (Neutral : Type v) (Safe : Type w) (Gauge : Type x) where
  | neutral : Neutral -> RawEvidence Neutral Safe Gauge
  | safe : Safe -> RawEvidence Neutral Safe Gauge
  | gauge : Gauge -> RawEvidence Neutral Safe Gauge
  | top : RawEvidence Neutral Safe Gauge
  | bot : RawEvidence Neutral Safe Gauge
  | conj :
      RawEvidence Neutral Safe Gauge ->
      RawEvidence Neutral Safe Gauge ->
      RawEvidence Neutral Safe Gauge
  | disj :
      RawEvidence Neutral Safe Gauge ->
      RawEvidence Neutral Safe Gauge ->
      RawEvidence Neutral Safe Gauge
  | neg :
      RawEvidence Neutral Safe Gauge ->
      RawEvidence Neutral Safe Gauge
deriving Repr

/-- CD-ENF evidence.  The leaf constructors are exactly `N`, `S`, and `G`. -/
inductive NormalEvidence (Neutral : Type v) (Safe : Type w) (Gauge : Type x) where
  | N : Neutral -> NormalEvidence Neutral Safe Gauge
  | S : Safe -> NormalEvidence Neutral Safe Gauge
  | G : Gauge -> NormalEvidence Neutral Safe Gauge
  | top : NormalEvidence Neutral Safe Gauge
  | bot : NormalEvidence Neutral Safe Gauge
  | conj :
      NormalEvidence Neutral Safe Gauge ->
      NormalEvidence Neutral Safe Gauge ->
      NormalEvidence Neutral Safe Gauge
  | disj :
      NormalEvidence Neutral Safe Gauge ->
      NormalEvidence Neutral Safe Gauge ->
      NormalEvidence Neutral Safe Gauge
  | neg :
      NormalEvidence Neutral Safe Gauge ->
      NormalEvidence Neutral Safe Gauge
deriving Repr

/-- Semantics of the three evidence leaf classes. -/
structure EvidenceSemantics
    (Omega : Type u) (Neutral : Type v) (Safe : Type w) (Gauge : Type x) where
  neutralSat : Neutral -> Omega -> Prop
  safeSat : Safe -> Omega -> Prop
  gaugeSat : Gauge -> Omega -> Prop

namespace EvidenceSemantics

variable {Omega : Type u} {Neutral : Type v} {Safe : Type w} {Gauge : Type x}

def SatRaw (S : EvidenceSemantics Omega Neutral Safe Gauge) :
    RawEvidence Neutral Safe Gauge -> Omega -> Prop
  | .neutral n => S.neutralSat n
  | .safe q => S.safeSat q
  | .gauge g => S.gaugeSat g
  | .top => fun _ => True
  | .bot => fun _ => False
  | .conj E F => fun omega => S.SatRaw E omega ∧ S.SatRaw F omega
  | .disj E F => fun omega => S.SatRaw E omega ∨ S.SatRaw F omega
  | .neg E => fun omega => ¬ S.SatRaw E omega

def SatNormal (S : EvidenceSemantics Omega Neutral Safe Gauge) :
    NormalEvidence Neutral Safe Gauge -> Omega -> Prop
  | .N n => S.neutralSat n
  | .S q => S.safeSat q
  | .G g => S.gaugeSat g
  | .top => fun _ => True
  | .bot => fun _ => False
  | .conj E F => fun omega => S.SatNormal E omega ∧ S.SatNormal F omega
  | .disj E F => fun omega => S.SatNormal E omega ∨ S.SatNormal F omega
  | .neg E => fun omega => ¬ S.SatNormal E omega

end EvidenceSemantics

/-- Recursive CD-ENF normalizer. -/
def CDENF {Neutral : Type v} {Safe : Type w} {Gauge : Type x} :
    RawEvidence Neutral Safe Gauge -> NormalEvidence Neutral Safe Gauge
  | .neutral n => .N n
  | .safe q => .S q
  | .gauge g => .G g
  | .top => .top
  | .bot => .bot
  | .conj E F => .conj (CDENF E) (CDENF F)
  | .disj E F => .disj (CDENF E) (CDENF F)
  | .neg E => .neg (CDENF E)

/-- Syntactic semantics preservation: once a raw term is already built only
from preclassified neutral/safe/gauge leaves, `CDENF` renames those leaves and
preserves Boolean semantics.  This theorem does not expand primitives emitted
by an actual observer execution. -/
theorem CDENF_semantics
    {Omega : Type u} {Neutral : Type v} {Safe : Type w} {Gauge : Type x}
    (S : EvidenceSemantics Omega Neutral Safe Gauge)
    (E : RawEvidence Neutral Safe Gauge) :
    S.SatNormal (CDENF E) = S.SatRaw E := by
  induction E with
  | neutral n => rfl
  | safe q => rfl
  | gauge g => rfl
  | top => rfl
  | bot => rfl
  | conj E F hE hF =>
      funext omega
      simp [CDENF, EvidenceSemantics.SatNormal, EvidenceSemantics.SatRaw,
        hE, hF]
  | disj E F hE hF =>
      funext omega
      simp [CDENF, EvidenceSemantics.SatNormal, EvidenceSemantics.SatRaw,
        hE, hF]
  | neg E hE =>
      funext omega
      simp [CDENF, EvidenceSemantics.SatNormal, EvidenceSemantics.SatRaw,
        hE]

/-- Observer outputs must be expanded into raw evidence by this interface;
there is no raw observer-output constructor. -/
structure ObserverEvidenceInterface
    (Omega : Type u) (Public : Type v) (Observer : Type w) (Output : Type x)
    (Neutral : Type y) (Safe : Type z) (Gauge : Type a) where
  semantics : EvidenceSemantics Omega Neutral Safe Gauge
  publicInput : Omega -> Public
  evalObserver : Observer -> Public -> Output
  observerToEvidence : Observer -> Output -> RawEvidence Neutral Safe Gauge
  observerToEvidence_sat :
    ∀ observer output,
      semantics.SatRaw (observerToEvidence observer output) =
        fun omega => evalObserver observer (publicInput omega) = output

theorem observerToEvidence_sat
    {Omega : Type u} {Public : Type v} {Observer : Type w} {Output : Type x}
    {Neutral : Type y} {Safe : Type z} {Gauge : Type a}
    (I : ObserverEvidenceInterface
      Omega Public Observer Output Neutral Safe Gauge)
    (observer : Observer) (output : Output) :
    I.semantics.SatRaw (I.observerToEvidence observer output) =
      fun omega => I.evalObserver observer (I.publicInput omega) = output :=
  I.observerToEvidence_sat observer output

theorem observerToCDENF_sat
    {Omega : Type u} {Public : Type v} {Observer : Type w} {Output : Type x}
    {Neutral : Type y} {Safe : Type z} {Gauge : Type a}
    (I : ObserverEvidenceInterface
      Omega Public Observer Output Neutral Safe Gauge)
    (observer : Observer) (output : Output) :
    I.semantics.SatNormal (CDENF (I.observerToEvidence observer output)) =
      fun omega => I.evalObserver observer (I.publicInput omega) = output := by
  rw [CDENF_semantics, observerToEvidence_sat I observer output]

/-! ## Faithful execution-trace expansion target -/

/-- Safe leaves occurring in a normal-evidence term. -/
def NormalEvidence.safeLeaves
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x} :
    NormalEvidence Neutral Safe Gauge -> List Safe
  | .N _ | .G _ | .top | .bot => []
  | .S q => [q]
  | .conj E F | .disj E F => E.safeLeaves ++ F.safeLeaves
  | .neg E => E.safeLeaves

/-- Gauge leaves occurring in a normal-evidence term. -/
def NormalEvidence.gaugeLeaves
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x} :
    NormalEvidence Neutral Safe Gauge -> List Gauge
  | .N _ | .S _ | .top | .bot => []
  | .G gamma => [gamma]
  | .conj E F | .disj E F => E.gaugeLeaves ++ F.gaugeLeaves
  | .neg E => E.gaugeLeaves

/-- Open target for the work not performed by `CDENF_semantics`: every
primitive occurrence from a real execution trace receives a sound normal
expansion; every safe leaf carries its actual legality guard; and every
target-relevant quotient/witness use exposes the required fresh gauge support.

The target is intentionally execution-indexed.  Merely choosing a datatype
whose constructors are already N/S/G cannot inhabit it without supplying the
occurrence, soundness, legality, and support fields. -/
structure V13ExecutionTracePrimitiveExpansionTarget
    (Omega : Type u) (Trace : Type v) (Primitive : Type w)
    (Neutral : Type x) (Safe : Type y) (Gauge : Type z)
    (GaugeCoord : Type a) [DecidableEq GaugeCoord] where
  semantics : EvidenceSemantics Omega Neutral Safe Gauge
  primitiveSat : Primitive -> Omega -> Prop
  primitiveOccurs : Trace -> Primitive -> Prop
  expansion : Trace -> Primitive -> NormalEvidence Neutral Safe Gauge
  safeLegalAt : Trace -> Safe -> Prop
  gaugeSupport : Gauge -> Finset GaugeCoord
  requiredFreshGaugeSupport : Trace -> Primitive -> Finset GaugeCoord
  expansion_sound : forall trace primitive,
    primitiveOccurs trace primitive ->
      semantics.SatNormal (expansion trace primitive) = primitiveSat primitive
  every_safe_leaf_is_legal : forall trace primitive,
    primitiveOccurs trace primitive ->
      forall q, q ∈ (expansion trace primitive).safeLeaves -> safeLegalAt trace q
  fresh_gauge_support_exposed : forall trace primitive,
    primitiveOccurs trace primitive ->
      forall coord, coord ∈ requiredFreshGaugeSupport trace primitive ->
        exists gamma, gamma ∈ (expansion trace primitive).gaugeLeaves ∧
          coord ∈ gaugeSupport gamma

/-! ## Toy semantics -/

def toyCDENFNeutral := Unit
def toyCDENFSafe := Bool
def toyCDENFGauge := Unit

def toyCDENFSemantics :
    EvidenceSemantics Bool toyCDENFNeutral toyCDENFSafe toyCDENFGauge where
  neutralSat := fun _ _ => True
  safeSat := fun q omega => omega = q
  gaugeSat := fun _ _ => True

def toyCDENFRaw :
    RawEvidence toyCDENFNeutral toyCDENFSafe toyCDENFGauge :=
  .conj (.neutral ()) (.safe true)

theorem toyCDENF_semantics :
    toyCDENFSemantics.SatNormal (CDENF toyCDENFRaw) =
      toyCDENFSemantics.SatRaw toyCDENFRaw :=
  CDENF_semantics toyCDENFSemantics toyCDENFRaw

def toyObserverEvidenceInterface :
    ObserverEvidenceInterface
      Bool Bool Unit Bool toyCDENFNeutral toyCDENFSafe toyCDENFGauge where
  semantics := toyCDENFSemantics
  publicInput := fun omega => omega
  evalObserver := fun _ pub => pub
  observerToEvidence := fun _ output => .safe output
  observerToEvidence_sat := by
    intro observer output
    funext omega
    rfl

theorem toy_observerToCDENF_sat (output : Bool) :
    toyObserverEvidenceInterface.semantics.SatNormal
        (CDENF (toyObserverEvidenceInterface.observerToEvidence () output)) =
      fun omega =>
        toyObserverEvidenceInterface.evalObserver ()
          (toyObserverEvidenceInterface.publicInput omega) = output :=
  observerToCDENF_sat toyObserverEvidenceInterface () output

end Mettapedia.Computability.PNP
