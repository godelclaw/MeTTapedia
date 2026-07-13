import Mettapedia.Computability.PNP.V13CDENF
import Mettapedia.Computability.PNP.V13FaithfulM4HypothesisBoundary

/-!
# Execution traces for the faithful regioned M4 scaffold

This module constructs an actual finite request/response execution on the
regioned scaffold.  Public reads, guarded buffer probes, raw-gauge reads, and
target-relevant quotient uses are executed against a sampled world while an
explicit prefix and charged gauge support are updated.

The resulting occurrence expansion inhabits
`V13ExecutionTracePrimitiveExpansionTarget`: public and illegal reads become
neutral leaves, legal buffer reads become safe leaves, and raw-gauge or
quotient use exposes gauge leaves.  Quotient expansion uses the two raw
coordinates `x` and `g`, rather than treating `z` as a target tag.

This is a theorem about the finite scaffold request language below.  It is not
Hypothesis D.33 for arbitrary polynomial-time observer executions.  Connecting
the manuscript observer semantics and its generated primitives to this request
language remains exactly the named `V13D33AtomCompleteness` field.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Requests, execution state, and emitted occurrences -/

inductive V13M4ScaffoldRequest (m t : Nat) where
  | publicSyntax : V13M4ConcretePublicPrimitive m t ->
      V13M4ScaffoldRequest m t
  | guardedBuffer : V13M4ConcreteGaugeIndex m -> V13M4ScaffoldRequest m t
  | rawGauge : V13M4ConcreteGaugeIndex m -> V13M4ScaffoldRequest m t
  | quotientUse : V13M4ConcreteGaugeIndex m -> V13M4ScaffoldRequest m t
deriving DecidableEq, Repr

structure V13M4ScaffoldExecutionState (m : Nat) where
  evidencePrefix : V13M4ConcretePrefix m
  chargedGaugeSupport : Finset (V13M4ConcreteGaugeIndex m)

inductive V13M4ScaffoldObservation (m t : Nat) where
  | publicValue : V13M4ConcretePublicPrimitive m t -> Bool ->
      V13M4ScaffoldObservation m t
  | safeBufferValue : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ScaffoldObservation m t
  | illegalBuffer : V13M4ConcreteGaugeIndex m ->
      V13M4ScaffoldObservation m t
  | rawGaugeValue : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ScaffoldObservation m t
  | quotientValue : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ScaffoldObservation m t
deriving DecidableEq, Repr

structure V13M4ScaffoldPrimitiveOccurrence (m t : Nat) where
  before : V13M4ScaffoldExecutionState m
  observation : V13M4ScaffoldObservation m t

def V13M4ScaffoldPrimitiveOccurrence.WellFormed {m t : Nat}
    (occ : V13M4ScaffoldPrimitiveOccurrence m t) : Prop :=
  match occ.observation with
  | .safeBufferValue q _ => q ∉ occ.before.evidencePrefix.bufferVisited
  | .illegalBuffer q => q ∈ occ.before.evidencePrefix.bufferVisited
  | _ => True

def v13M4ScaffoldObserveGauge {m : Nat}
    (pref : V13M4ConcretePrefix m) (v : V13M4ConcreteGaugeIndex m)
    (value : Bool) : V13M4ConcretePrefix m :=
  { pref with gaugeObservation := Function.update pref.gaugeObservation v (some value) }

def v13M4ScaffoldVisitBuffer {m : Nat}
    (pref : V13M4ConcretePrefix m) (q : V13M4ConcreteGaugeIndex m) :
    V13M4ConcretePrefix m :=
  { pref with bufferVisited := insert q pref.bufferVisited }

def v13M4ScaffoldStep {m t : Nat}
    (omega : V13M4ConcreteWorld m t)
    (state : V13M4ScaffoldExecutionState m)
    (request : V13M4ScaffoldRequest m t) :
    V13M4ScaffoldExecutionState m × V13M4ScaffoldPrimitiveOccurrence m t :=
  match request with
  | .publicSyntax primitive =>
      (state, ⟨state, .publicValue primitive
        (v13M4ConcretePrimitiveValue primitive omega)⟩)
  | .guardedBuffer q =>
      if q ∉ state.evidencePrefix.bufferVisited then
        ({ state with evidencePrefix :=
            v13M4ScaffoldVisitBuffer state.evidencePrefix q },
          ⟨state, .safeBufferValue q (omega.bufferLeft q)⟩)
      else
        (state, ⟨state, .illegalBuffer q⟩)
  | .rawGauge v =>
      ({ evidencePrefix :=
           v13M4ScaffoldObserveGauge state.evidencePrefix v (omega.g v)
         chargedGaugeSupport := insert v state.chargedGaugeSupport },
        ⟨state, .rawGaugeValue v (omega.g v)⟩)
  | .quotientUse v =>
      ({ state with chargedGaugeSupport := insert v state.chargedGaugeSupport },
        ⟨state, .quotientValue v (omega.z v)⟩)

def v13M4ScaffoldRun {m t : Nat}
    (omega : V13M4ConcreteWorld m t) :
    V13M4ScaffoldExecutionState m -> List (V13M4ScaffoldRequest m t) ->
      V13M4ScaffoldExecutionState m ×
        List (V13M4ScaffoldPrimitiveOccurrence m t)
  | state, [] => (state, [])
  | state, request :: requests =>
      let step := v13M4ScaffoldStep omega state request
      let rest := v13M4ScaffoldRun omega step.1 requests
      (rest.1, step.2 :: rest.2)

structure V13M4ScaffoldExecutionTrace (m t : Nat) where
  world : V13M4ConcreteWorld m t
  initial : V13M4ScaffoldExecutionState m
  requests : List (V13M4ScaffoldRequest m t)

def V13M4ScaffoldExecutionTrace.occurrences {m t : Nat}
    (trace : V13M4ScaffoldExecutionTrace m t) :
    List (V13M4ScaffoldPrimitiveOccurrence m t) :=
  (v13M4ScaffoldRun trace.world trace.initial trace.requests).2

theorem v13M4ScaffoldStep_wellFormed {m t : Nat}
    (omega : V13M4ConcreteWorld m t)
    (state : V13M4ScaffoldExecutionState m)
    (request : V13M4ScaffoldRequest m t) :
    (v13M4ScaffoldStep omega state request).2.WellFormed := by
  cases request with
  | publicSyntax primitive => trivial
  | guardedBuffer q =>
      simp only [v13M4ScaffoldStep]
      split <;> simp_all [V13M4ScaffoldPrimitiveOccurrence.WellFormed]
  | rawGauge v => trivial
  | quotientUse v => trivial

theorem v13M4ScaffoldRun_occurrences_wellFormed {m t : Nat}
    (omega : V13M4ConcreteWorld m t)
    (state : V13M4ScaffoldExecutionState m)
    (requests : List (V13M4ScaffoldRequest m t)) :
    forall occ, occ ∈ (v13M4ScaffoldRun omega state requests).2 ->
      occ.WellFormed := by
  induction requests generalizing state with
  | nil => simp [v13M4ScaffoldRun]
  | cons request requests ih =>
      intro occ hocc
      simp only [v13M4ScaffoldRun] at hocc
      rcases hstep : v13M4ScaffoldStep omega state request with ⟨next, emitted⟩
      rw [hstep] at hocc
      simp only at hocc
      rcases hrest : v13M4ScaffoldRun omega next requests with ⟨final, rest⟩
      rw [hrest] at hocc
      simp only [List.mem_cons] at hocc
      rcases hocc with rfl | hocc
      · simpa [hstep] using v13M4ScaffoldStep_wellFormed omega state request
      · exact ih next occ (by simpa [hrest] using hocc)

/-! ## CD-ENF leaf language and semantics -/

inductive V13M4ScaffoldNeutralAtom (m t : Nat) where
  | publicValue : V13M4ConcretePublicPrimitive m t -> Bool ->
      V13M4ScaffoldNeutralAtom m t
  | illegalBuffer : V13M4ConcreteGaugeIndex m ->
      V13M4ScaffoldNeutralAtom m t
deriving DecidableEq, Repr

structure V13M4ScaffoldSafeAtom (m : Nat) where
  before : V13M4ScaffoldExecutionState m
  probe : V13M4ConcreteGaugeIndex m
  value : Bool

inductive V13M4ScaffoldGaugeAtom (m : Nat) where
  | rawGauge : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ScaffoldGaugeAtom m
  | rawWitness : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ScaffoldGaugeAtom m
deriving DecidableEq, Repr

def v13M4ScaffoldEvidenceSemantics (m t : Nat) :
    EvidenceSemantics (V13M4ConcreteWorld m t)
      (V13M4ScaffoldNeutralAtom m t) (V13M4ScaffoldSafeAtom m)
      (V13M4ScaffoldGaugeAtom m) where
  neutralSat
    | .publicValue primitive value, omega =>
        v13M4ConcretePrimitiveValue primitive omega = value
    | .illegalBuffer _, _ => True
  safeSat atom omega := omega.bufferLeft atom.probe = atom.value
  gaugeSat
    | .rawGauge v value, omega => omega.g v = value
    | .rawWitness v value, omega => xor (omega.z v) (omega.g v) = value

def v13M4ScaffoldPrimitiveSat {m t : Nat}
    (occ : V13M4ScaffoldPrimitiveOccurrence m t)
    (omega : V13M4ConcreteWorld m t) : Prop :=
  match occ.observation with
  | .publicValue primitive value =>
      v13M4ConcretePrimitiveValue primitive omega = value
  | .safeBufferValue q value => omega.bufferLeft q = value
  | .illegalBuffer _ => True
  | .rawGaugeValue v value => omega.g v = value
  | .quotientValue v value => omega.z v = value

def v13M4ScaffoldQuotientExpansion {m t : Nat}
    (v : V13M4ConcreteGaugeIndex m) (value : Bool) :
    NormalEvidence (V13M4ScaffoldNeutralAtom m t)
      (V13M4ScaffoldSafeAtom m) (V13M4ScaffoldGaugeAtom m) :=
  if value then
    .disj
      (.conj (.G (.rawWitness v false)) (.G (.rawGauge v true)))
      (.conj (.G (.rawWitness v true)) (.G (.rawGauge v false)))
  else
    .disj
      (.conj (.G (.rawWitness v false)) (.G (.rawGauge v false)))
      (.conj (.G (.rawWitness v true)) (.G (.rawGauge v true)))

def v13M4ScaffoldPrimitiveExpansion {m t : Nat}
    (occ : V13M4ScaffoldPrimitiveOccurrence m t) :
    NormalEvidence (V13M4ScaffoldNeutralAtom m t)
      (V13M4ScaffoldSafeAtom m) (V13M4ScaffoldGaugeAtom m) :=
  match occ.observation with
  | .publicValue primitive value => .N (.publicValue primitive value)
  | .safeBufferValue q value => .S ⟨occ.before, q, value⟩
  | .illegalBuffer q => .N (.illegalBuffer q)
  | .rawGaugeValue v value => .G (.rawGauge v value)
  | .quotientValue v value => v13M4ScaffoldQuotientExpansion v value

theorem v13M4ScaffoldQuotientExpansion_sound {m t : Nat}
    (v : V13M4ConcreteGaugeIndex m) (value : Bool) :
    (v13M4ScaffoldEvidenceSemantics m t).SatNormal
      (v13M4ScaffoldQuotientExpansion (t := t) v value) =
        fun omega => omega.z v = value := by
  funext omega
  cases value <;> cases hz : omega.z v <;> cases hg : omega.g v <;>
    simp [v13M4ScaffoldQuotientExpansion, v13M4ScaffoldEvidenceSemantics,
      EvidenceSemantics.SatNormal, hz, hg]

theorem v13M4ScaffoldPrimitiveExpansion_sound {m t : Nat}
    (occ : V13M4ScaffoldPrimitiveOccurrence m t) :
    (v13M4ScaffoldEvidenceSemantics m t).SatNormal
      (v13M4ScaffoldPrimitiveExpansion occ) =
        v13M4ScaffoldPrimitiveSat occ := by
  cases occ with
  | mk before observation =>
      cases observation with
      | publicValue primitive value => rfl
      | safeBufferValue q value => rfl
      | illegalBuffer q => rfl
      | rawGaugeValue v value => rfl
      | quotientValue v value =>
          exact v13M4ScaffoldQuotientExpansion_sound v value

def v13M4ScaffoldGaugeAtomSupport {m : Nat}
    (atom : V13M4ScaffoldGaugeAtom m) :
    Finset (V13M4ConcreteGaugeIndex m) :=
  match atom with
  | .rawGauge v _ | .rawWitness v _ => {v}

def v13M4ScaffoldRequiredFreshGaugeSupport {m t : Nat}
    (occ : V13M4ScaffoldPrimitiveOccurrence m t) :
    Finset (V13M4ConcreteGaugeIndex m) :=
  match occ.observation with
  | .rawGaugeValue v _ | .quotientValue v _ =>
      if v ∈ occ.before.chargedGaugeSupport then ∅ else {v}
  | _ => ∅

theorem v13M4ScaffoldRequiredFreshGaugeSupport_fresh {m t : Nat}
    (occ : V13M4ScaffoldPrimitiveOccurrence m t)
    (v : V13M4ConcreteGaugeIndex m)
    (hv : v ∈ v13M4ScaffoldRequiredFreshGaugeSupport occ) :
    v ∉ occ.before.chargedGaugeSupport := by
  rcases occ with ⟨before, observation⟩
  cases observation with
  | publicValue primitive value =>
      simp [v13M4ScaffoldRequiredFreshGaugeSupport] at hv
  | safeBufferValue probe value =>
      simp [v13M4ScaffoldRequiredFreshGaugeSupport] at hv
  | illegalBuffer probe =>
      simp [v13M4ScaffoldRequiredFreshGaugeSupport] at hv
  | rawGaugeValue coord value =>
      by_cases hcharged : coord ∈ before.chargedGaugeSupport
      · simp [v13M4ScaffoldRequiredFreshGaugeSupport, hcharged] at hv
      · have : v = coord := by
          simpa [v13M4ScaffoldRequiredFreshGaugeSupport, hcharged] using hv
        subst v
        exact hcharged
  | quotientValue coord value =>
      by_cases hcharged : coord ∈ before.chargedGaugeSupport
      · simp [v13M4ScaffoldRequiredFreshGaugeSupport, hcharged] at hv
      · have : v = coord := by
          simpa [v13M4ScaffoldRequiredFreshGaugeSupport, hcharged] using hv
        subst v
        exact hcharged

/-! ## The scaffold execution-expansion target -/

noncomputable def v13M4ScaffoldExecutionTraceExpansion (m t : Nat) :
    V13ExecutionTracePrimitiveExpansionTarget
      (V13M4ConcreteWorld m t) (V13M4ScaffoldExecutionTrace m t)
      (V13M4ScaffoldPrimitiveOccurrence m t)
      (V13M4ScaffoldNeutralAtom m t) (V13M4ScaffoldSafeAtom m)
      (V13M4ScaffoldGaugeAtom m) (V13M4ConcreteGaugeIndex m) where
  semantics := v13M4ScaffoldEvidenceSemantics m t
  primitiveSat := v13M4ScaffoldPrimitiveSat
  primitiveOccurs := fun trace occ => occ ∈ trace.occurrences
  expansion := fun _ occ => v13M4ScaffoldPrimitiveExpansion occ
  safeLegalAt := fun _ atom =>
    atom.probe ∉ atom.before.evidencePrefix.bufferVisited
  gaugeSupport := v13M4ScaffoldGaugeAtomSupport
  requiredFreshGaugeSupport := fun _ occ =>
    v13M4ScaffoldRequiredFreshGaugeSupport occ
  expansion_sound := by
    intro trace occ _
    exact v13M4ScaffoldPrimitiveExpansion_sound occ
  every_safe_leaf_is_legal := by
    intro trace occ hocc q hq
    have hwell := v13M4ScaffoldRun_occurrences_wellFormed
      trace.world trace.initial trace.requests occ hocc
    rcases occ with ⟨before, observation⟩
    cases observation with
    | publicValue primitive value =>
        simp [v13M4ScaffoldPrimitiveExpansion,
          NormalEvidence.safeLeaves] at hq
    | safeBufferValue probe value =>
        simp [v13M4ScaffoldPrimitiveExpansion,
          NormalEvidence.safeLeaves] at hq
        subst q
        change probe ∉ before.evidencePrefix.bufferVisited at hwell
        exact hwell
    | illegalBuffer probe =>
        simp [v13M4ScaffoldPrimitiveExpansion,
          NormalEvidence.safeLeaves] at hq
    | rawGaugeValue coord value =>
        simp [v13M4ScaffoldPrimitiveExpansion,
          NormalEvidence.safeLeaves] at hq
    | quotientValue coord value =>
        cases value <;>
          simp [v13M4ScaffoldPrimitiveExpansion,
            v13M4ScaffoldQuotientExpansion,
            NormalEvidence.safeLeaves] at hq
  fresh_gauge_support_exposed := by
    intro trace occ _ coord hcoord
    rcases occ with ⟨before, observation⟩
    cases observation with
    | publicValue primitive value =>
        simp [v13M4ScaffoldRequiredFreshGaugeSupport] at hcoord
    | safeBufferValue probe value =>
        simp [v13M4ScaffoldRequiredFreshGaugeSupport] at hcoord
    | illegalBuffer probe =>
        simp [v13M4ScaffoldRequiredFreshGaugeSupport] at hcoord
    | rawGaugeValue v value =>
        by_cases hv : v ∈ before.chargedGaugeSupport
        · simp [v13M4ScaffoldRequiredFreshGaugeSupport, hv] at hcoord
        · have hcoordEq : coord = v := by
            simpa [v13M4ScaffoldRequiredFreshGaugeSupport, hv] using hcoord
          subst coord
          exact ⟨.rawGauge v value, by
            simp [v13M4ScaffoldPrimitiveExpansion,
              NormalEvidence.gaugeLeaves], by
            simp [v13M4ScaffoldGaugeAtomSupport]⟩
    | quotientValue v value =>
        by_cases hv : v ∈ before.chargedGaugeSupport
        · simp [v13M4ScaffoldRequiredFreshGaugeSupport, hv] at hcoord
        · have hcoordEq : coord = v := by
            simpa [v13M4ScaffoldRequiredFreshGaugeSupport, hv] using hcoord
          subst coord
          refine ⟨.rawWitness v false, ?_, by
            simp [v13M4ScaffoldGaugeAtomSupport]⟩
          cases value <;>
            simp [v13M4ScaffoldPrimitiveExpansion,
              v13M4ScaffoldQuotientExpansion, NormalEvidence.gaugeLeaves]

/-- Every public primitive is in the declared full catalog and has a total
neutral expansion in the scaffold execution language. -/
theorem v13M4Scaffold_fullPublicSyntax_expands
    (m t : Nat) (primitive : V13M4ConcretePublicPrimitive m t)
    (state : V13M4ScaffoldExecutionState m)
    (value : Bool) :
    primitive ∈ V13M4ConcreteE.fullPublicSyntax () m t ∧
      v13M4ScaffoldPrimitiveExpansion
        (V13M4ScaffoldPrimitiveOccurrence.mk state (.publicValue primitive value)) =
          .N (.publicValue primitive value) := by
  constructor
  · change primitive ∈ (Finset.univ :
      Finset (V13M4ConcretePublicPrimitive m t))
    simp
  · rfl

/-- A one-request execution really emits every requested public catalog
primitive with its world value; catalog coverage is not merely a datatype
enumeration. -/
theorem v13M4Scaffold_everyPublicPrimitive_executes
    {m t : Nat} (omega : V13M4ConcreteWorld m t)
    (state : V13M4ScaffoldExecutionState m)
    (primitive : V13M4ConcretePublicPrimitive m t) :
    let trace : V13M4ScaffoldExecutionTrace m t :=
      ⟨omega, state, [.publicSyntax primitive]⟩
    let occ : V13M4ScaffoldPrimitiveOccurrence m t :=
      ⟨state, .publicValue primitive
        (v13M4ConcretePrimitiveValue primitive omega)⟩
    occ ∈ trace.occurrences := by
  simp [V13M4ScaffoldExecutionTrace.occurrences, v13M4ScaffoldRun,
    v13M4ScaffoldStep]

/-- Legal safe leaves inherit the protected-distance guarantee from the real
scaffold probe catalog. -/
theorem v13M4Scaffold_safeLeaf_protectedDistance
    {m t : Nat} (trace : V13M4ScaffoldExecutionTrace m t)
    (atom : V13M4ScaffoldSafeAtom m)
    (hlegal : (v13M4ScaffoldExecutionTraceExpansion m t).safeLegalAt trace atom)
    (site : V13M4ConcreteG.Site () m t)
    (hsite : site ∈ V13M4ConcreteC.probeSupport atom.probe)
    (protectedSite : V13M4ConcreteG.Site () m t)
    (hprotected : V13M4ConcreteG.isProtected protectedSite) :
    V13M4ConcreteE.safeRadius () m t <=
      V13M4ConcreteG.distance site protectedSite := by
  change atom.probe ∉ atom.before.evidencePrefix.bufferVisited at hlegal
  have hlegalC : @V13M4LocalComponents.legalProbe
      V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC () m t
      atom.before.evidencePrefix atom.probe := by
    change atom.probe ∉ atom.before.evidencePrefix.bufferVisited
    exact hlegal
  exact @V13M4LocalComponents.legal_probe_protected_distance
    V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC () m t
    atom.before.evidencePrefix atom.probe hlegalC site hsite protectedSite
    hprotected

end Mettapedia.Computability.PNP
