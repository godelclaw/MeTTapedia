import Mettapedia.Computability.PNP.V13GaugeBufferedLockedInterface

/-!
# PNP v13 public-input interface battery

This module consolidates the finite public-input red-team tests around the
abstract gauge-buffered locked interface.  The full-public-read decomposition
test is deliberately stated with one explicit concrete obligation: a primitive
public read whose CD-ENF contains only neutral leaves must be target-blind.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f p

/-! ## CD-ENF leaf predicates for the public-read test -/

def NormalEvidenceOnlyNeutralLeaves
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x} :
    NormalEvidence Neutral Safe Gauge -> Prop
  | .N _ => True
  | .S _ => False
  | .G _ => False
  | .top => True
  | .bot => True
  | .conj E F =>
      NormalEvidenceOnlyNeutralLeaves E ∧
        NormalEvidenceOnlyNeutralLeaves F
  | .disj E F =>
      NormalEvidenceOnlyNeutralLeaves E ∧
        NormalEvidenceOnlyNeutralLeaves F
  | .neg E => NormalEvidenceOnlyNeutralLeaves E

def NormalEvidenceHasChargedLeaf
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x} :
    NormalEvidence Neutral Safe Gauge -> Prop
  | .N _ => False
  | .S _ => True
  | .G _ => True
  | .top => False
  | .bot => False
  | .conj E F =>
      NormalEvidenceHasChargedLeaf E ∨
        NormalEvidenceHasChargedLeaf F
  | .disj E F =>
      NormalEvidenceHasChargedLeaf E ∨
        NormalEvidenceHasChargedLeaf F
  | .neg E => NormalEvidenceHasChargedLeaf E

theorem normalEvidence_onlyNeutral_or_hasCharged
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x}
    (E : NormalEvidence Neutral Safe Gauge) :
    NormalEvidenceOnlyNeutralLeaves E ∨
      NormalEvidenceHasChargedLeaf E := by
  induction E with
  | N _ => exact Or.inl trivial
  | S _ => exact Or.inr trivial
  | G _ => exact Or.inr trivial
  | top => exact Or.inl trivial
  | bot => exact Or.inl trivial
  | conj E F hE hF =>
      rcases hE with hE | hE
      · rcases hF with hF | hF
        · exact Or.inl ⟨hE, hF⟩
        · exact Or.inr (Or.inr hF)
      · exact Or.inr (Or.inl hE)
  | disj E F hE hF =>
      rcases hE with hE | hE
      · rcases hF with hF | hF
        · exact Or.inl ⟨hE, hF⟩
        · exact Or.inr (Or.inr hF)
      · exact Or.inr (Or.inl hE)
  | neg E hE => exact hE

theorem CDENF_onlyNeutral_or_hasCharged
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x}
    (E : RawEvidence Neutral Safe Gauge) :
    NormalEvidenceOnlyNeutralLeaves (CDENF E) ∨
      NormalEvidenceHasChargedLeaf (CDENF E) :=
  normalEvidence_onlyNeutral_or_hasCharged (CDENF E)

/-!
The single public-read frontier carried by the abstract battery.  A concrete
ensemble must prove that neutral-only public reads are target-blind.
-/
def PublicReadNeutralOnlyTargetBlind
    {PublicSymbol : Type p} {Neutral : Type v} {Safe : Type w}
    {Gauge : Type x}
    (readPublic : PublicSymbol -> RawEvidence Neutral Safe Gauge)
    (targetBlind : PublicSymbol -> Prop) : Prop :=
  ∀ theta,
    NormalEvidenceOnlyNeutralLeaves (CDENF (readPublic theta)) ->
      targetBlind theta

structure PublicReadCDENFInterface
    (PublicSymbol : Type p) (Neutral : Type v) (Safe : Type w)
    (Gauge : Type x) where
  readPublic : PublicSymbol -> RawEvidence Neutral Safe Gauge
  targetBlind : PublicSymbol -> Prop
  neutralOnly_targetBlind :
    PublicReadNeutralOnlyTargetBlind readPublic targetBlind

theorem public_read_cdenf_normalizes_neutral_or_charged
    {PublicSymbol : Type p} {Neutral : Type v} {Safe : Type w}
    {Gauge : Type x}
    (D : PublicReadCDENFInterface PublicSymbol Neutral Safe Gauge)
    (theta : PublicSymbol) :
    (NormalEvidenceOnlyNeutralLeaves (CDENF (D.readPublic theta)) ∧
        D.targetBlind theta) ∨
      NormalEvidenceHasChargedLeaf (CDENF (D.readPublic theta)) := by
  rcases CDENF_onlyNeutral_or_hasCharged (D.readPublic theta) with hNeutral | hCharged
  · exact Or.inl ⟨hNeutral, D.neutralOnly_targetBlind theta hNeutral⟩
  · exact Or.inr hCharged

/-! ## Structural no-opaque-run check -/

def RawEvidenceHasNoOpaqueRunAtom
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x} :
    RawEvidence Neutral Safe Gauge -> Prop
  | .neutral _ => True
  | .safe _ => True
  | .gauge _ => True
  | .top => True
  | .bot => True
  | .conj E F =>
      RawEvidenceHasNoOpaqueRunAtom E ∧ RawEvidenceHasNoOpaqueRunAtom F
  | .disj E F =>
      RawEvidenceHasNoOpaqueRunAtom E ∧ RawEvidenceHasNoOpaqueRunAtom F
  | .neg E => RawEvidenceHasNoOpaqueRunAtom E

theorem v13RawEvidence_has_no_opaque_run_atom
    {Neutral : Type v} {Safe : Type w} {Gauge : Type x}
    (E : RawEvidence Neutral Safe Gauge) :
    RawEvidenceHasNoOpaqueRunAtom E := by
  induction E with
  | neutral _ => trivial
  | safe _ => trivial
  | gauge _ => trivial
  | top => trivial
  | bot => trivial
  | conj _ _ hE hF => exact ⟨hE, hF⟩
  | disj _ _ hE hF => exact ⟨hE, hF⟩
  | neg _ hE => exact hE

/-! ## Named battery over the abstract interface -/

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]
variable {Public : Type v} {Neutral : Type w} {Safe : Type x}
variable {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
variable {Pair : Type a} [Fintype Pair] {Stage : Type b} {Branch : Type c}
variable {HistoryAtom : Type d} {Pivot : Type e}
variable {Observer : Type f} {Output : Type f} {Skeleton : Type w}
variable {PublicSymbol : Type p}

structure V13InterfaceConsistencyBattery
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (D : PublicReadCDENFInterface PublicSymbol Neutral Safe Gauge) where
  test1_sameFullPublic_noOpposite :
    ¬ ∃ w0 w1,
      L.publicInput w0 = L.publicInput w1 ∧
        L.target w0 = false ∧ L.target w1 = true
  test2_neutral_generates_target_contradiction :
    ¬ ∃ f : Skeleton -> Bool,
      ∀ omega, L.target omega = f (L.neutralSkeleton omega)
  test3_publicBit_derivative_mass_ge_one :
    ∀ {n : Nat} (Ybit : Fin n -> Omega -> Bool)
      (Gamma : CouplingOnOppositePhases.{u, a} Omega L.target)
      (_hGen : ∃ f : (Fin n -> Bool) -> Bool,
        ∀ omega, L.target omega = f (fun r => Ybit r omega)),
      1 ≤ publicBitTotalDerivativeMass Ybit Gamma
  test4_measurable_not_admissible :
    ∀ C : FiniteSigmaField.{u, d} Omega,
      MeasurableWrt C L.target ->
        NontrivialWitnessBit L.target ->
          ¬ BalancedConditioning C L.target
  test5_boundary_mixing_blocks_pivot_sufficiency :
    L.epsMix < (1 / 2 : Rat) ->
      ¬ ∃ h0 : Pivot -> Bool,
        ∀ omega, L.target omega = h0 (L.pivotSummary omega)
  test6_no_opaque_run_atom :
    (∀ E : RawEvidence Neutral Safe Gauge,
        RawEvidenceHasNoOpaqueRunAtom E) ∧
      (∀ observer output,
        L.observerEvidence.semantics.SatRaw
            (L.observerEvidence.observerToEvidence observer output) =
          fun omega =>
            L.observerEvidence.evalObserver observer
              (L.observerEvidence.publicInput omega) = output)
  test7_neutral_skeleton_not_target_sufficient :
    ¬ ∃ f : Skeleton -> Bool,
      ∀ omega, L.target omega = f (L.neutralSkeleton omega)
  test8_full_public_read_decomposes :
    ∀ theta,
      (NormalEvidenceOnlyNeutralLeaves (CDENF (D.readPublic theta)) ∧
          D.targetBlind theta) ∨
        NormalEvidenceHasChargedLeaf (CDENF (D.readPublic theta))

theorem v13_interfaceConsistencyBattery
    (L : GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (D : PublicReadCDENFInterface PublicSymbol Neutral Safe Gauge) :
    V13InterfaceConsistencyBattery L D := by
  refine
    { test1_sameFullPublic_noOpposite := ?test1
      test2_neutral_generates_target_contradiction := ?test2
      test3_publicBit_derivative_mass_ge_one := ?test3
      test4_measurable_not_admissible := ?test4
      test5_boundary_mixing_blocks_pivot_sufficiency := ?test5
      test6_no_opaque_run_atom := ?test6
      test7_neutral_skeleton_not_target_sufficient := ?test7
      test8_full_public_read_decomposes := ?test8 }
  · exact sameFullY_noOpposite L.publicInput L.target L.singleMessage
  · exact L.neutral_skeleton_not_target_sufficient
  · intro n Ybit Gamma hGen
    exact publicBit_derivative_mass_ge_one Ybit L.target Gamma hGen
  · intro C hMeas hNondeg
    exact measurable_not_admissible L.target C hMeas hNondeg
  · intro hSmall
    exact L.boundary_mixing_blocks_pivot_sufficiency hSmall
  · exact
      ⟨fun E => v13RawEvidence_has_no_opaque_run_atom E,
        fun observer output => observerToEvidence_sat L.observerEvidence observer output⟩
  · exact L.neutral_skeleton_not_target_sufficient
  · intro theta
    exact public_read_cdenf_normalizes_neutral_or_charged D theta

/-! ## Checked citation table and enforced-vs-assumed ledger -/

inductive V13LedgerStatus where
  | provedEnforcedByAbstractInterface
  | carriedAsAssumption
deriving DecidableEq, Repr

structure V13BatteryCitationRow where
  testNumber : Nat
  testName : String
  theoremName : String
  status : V13LedgerStatus
deriving Repr

def v13InterfaceBatteryCitations : List V13BatteryCitationRow := [
  {
    testNumber := 1
    testName := "Same full public instance cannot be message-opposite"
    theoremName := "sameFullY_noOpposite / V13InterfaceConsistencyBattery.test1_sameFullPublic_noOpposite"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 2
    testName := "Neutral atoms cannot generate target"
    theoremName := "neutral_generates_target_contradiction / V13InterfaceConsistencyBattery.test2_neutral_generates_target_contradiction"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 3
    testName := "Full public bits have total derivative mass"
    theoremName := "publicBit_derivative_mass_ge_one / V13InterfaceConsistencyBattery.test3_publicBit_derivative_mass_ge_one"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 4
    testName := "Full public input is not admissible conditioning"
    theoremName := "measurable_not_admissible / V13InterfaceConsistencyBattery.test4_measurable_not_admissible"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 5
    testName := "Boundary feature sufficiency forces large error"
    theoremName := "boundary_mixing_blocks_pivot_sufficiency / V13InterfaceConsistencyBattery.test5_boundary_mixing_blocks_pivot_sufficiency"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 6
    testName := "No opaque run atom"
    theoremName := "v13RawEvidence_has_no_opaque_run_atom / observerToEvidence_sat"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 7
    testName := "Neutral skeleton is not sufficient"
    theoremName := "neutralSkeleton_not_sufficient / V13InterfaceConsistencyBattery.test7_neutral_skeleton_not_target_sufficient"
    status := .provedEnforcedByAbstractInterface
  },
  {
    testNumber := 8
    testName := "Full public read must decompose to charged leaves"
    theoremName := "public_read_cdenf_normalizes_neutral_or_charged"
    status := .carriedAsAssumption
  }
]

theorem v13InterfaceBatteryCitations_length :
    v13InterfaceBatteryCitations.length = 8 := by
  rfl

structure V13EnforcedAssumedLedgerRow where
  item : String
  status : V13LedgerStatus
  checkedName : String
  concreteObligation : String
deriving Repr

def v13InterfaceEnforcedAssumedLedger : List V13EnforcedAssumedLedgerRow := [
  {
    item := "field singleMessage"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.singleMessage"
    concreteObligation := "Prove the target bit is a function of the full public instance on support."
  },
  {
    item := "field hiddenGaugeProduct"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.hiddenGaugeProduct"
    concreteObligation := "Prove unsupported gauge coordinates remain product-fair under legal prefixes."
  },
  {
    item := "field noPublicTargetTags"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.noPublicTargetTags"
    concreteObligation := "Prove neutral skeleton pair-neutrality, existence of opposite pairs, and skeleton non-sufficiency."
  },
  {
    item := "field atomCompleteness"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.atomCompleteness"
    concreteObligation := "Show normalized target-relevant atoms are exhausted by neutral, safe-buffer, and gauge evidence."
  },
  {
    item := "field gaugeFaithfulness"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.gaugeFaithfulness"
    concreteObligation := "Show quotient or gauge use exposes charged raw gauge support rather than a canonical representative."
  },
  {
    item := "field safeQSSM"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.safeQSSM"
    concreteObligation := "Prove the concrete safe-buffer leakage bound."
  },
  {
    item := "field boundedGaugeIncidence"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.boundedGaugeIncidence"
    concreteObligation := "Prove each gauge charge has bounded target incidence."
  },
  {
    item := "field boundaryMixing"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.boundaryMixing"
    concreteObligation := "Prove the pivot-summary near-random baseline for the concrete boundary law."
  },
  {
    item := "field admissibleHistories"
    status := .carriedAsAssumption
    checkedName := "GaugeBufferedLockedInterface.admissibleHistories"
    concreteObligation := "Prove current target balance under the admitted history field."
  },
  {
    item := "test 1 same full public no opposite"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test1_sameFullPublic_noOpposite"
    concreteObligation := "Supply the singleMessage field."
  },
  {
    item := "test 2 neutral atoms cannot generate target"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test2_neutral_generates_target_contradiction"
    concreteObligation := "Supply noPublicTargetTags for the neutral skeleton."
  },
  {
    item := "test 3 public-bit derivative mass"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test3_publicBit_derivative_mass_ge_one"
    concreteObligation := "Instantiate the finite public-bit encoding and opposite-phase coupling."
  },
  {
    item := "test 4 measurable conditioning obstruction"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test4_measurable_not_admissible"
    concreteObligation := "Instantiate the finite field representing the proposed conditioning."
  },
  {
    item := "test 5 boundary non-sufficiency"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test5_boundary_mixing_blocks_pivot_sufficiency"
    concreteObligation := "Supply boundaryMixing and the epsMix < 1/2 parameter inequality."
  },
  {
    item := "test 6 no opaque run atom"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test6_no_opaque_run_atom"
    concreteObligation := "Expand observers through observerToEvidence; RawEvidence has no observer-output constructor."
  },
  {
    item := "test 7 neutral skeleton not sufficient"
    status := .provedEnforcedByAbstractInterface
    checkedName := "V13InterfaceConsistencyBattery.test7_neutral_skeleton_not_target_sufficient"
    concreteObligation := "Supply noPublicTargetTags for the neutral skeleton."
  },
  {
    item := "test 8 full public read decomposition"
    status := .carriedAsAssumption
    checkedName := "public_read_cdenf_normalizes_neutral_or_charged"
    concreteObligation := "Prove PublicReadNeutralOnlyTargetBlind for every primitive public read."
  }
]

theorem v13InterfaceEnforcedAssumedLedger_length :
    v13InterfaceEnforcedAssumedLedger.length = 17 := by
  rfl

theorem v13InterfaceLedger_test8_is_carried_assumption :
    (v13InterfaceBatteryCitations.get ⟨7, by decide⟩).status =
      V13LedgerStatus.carriedAsAssumption := by
  rfl

end Mettapedia.Computability.PNP
