import Mettapedia.Computability.PNP.V15RealEnsembleSpine

/-!
# PNP v15: real linear CNF ensemble

This module gives an actual CNF/SAT realization of the existing real linear
single-message surface.  For a public instance `Y = (A, b)`, the formula has
one concrete unit clause per witness coordinate, locking that coordinate to
the full public decoder `A⁻¹ b`.  This is a real finite CNF construction over
the v13 linear public instance; it is not the manuscript M4 ensemble and does
not prove any analytic frontier.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u

namespace ConcreteCNF

/-- Unit-clause equality is exactly equality of the addressed variable and
the forced Boolean value. -/
theorem unitClause_eq_unitClause_iff {Var : Type u} {v v' : Var}
    {value value' : Bool} :
    unitClause v value = unitClause v' value' ↔
      v = v' ∧ value = value' := by
  cases value <;> cases value' <;> simp [unitClause, unitLiteral]

end ConcreteCNF

/-- CNF variables for the real linear public instance are the witness
coordinates. -/
abbrev V13RealLinearCNFVar (m : Nat) :=
  Fin m

/-- CNF witnesses are Boolean assignments to the witness-coordinate variables. -/
abbrev V13RealLinearCNFWitness (m : Nat) :=
  ConcreteCNF.Assignment (V13RealLinearCNFVar m)

/-- The Boolean witness assignment decoded from the full real linear public
instance. -/
def v13RealLinearCNFDecodedAssignment {m : Nat}
    (Y : V13RealLinearPublic m) :
    V13RealLinearCNFWitness m :=
  fun j => v13RealLinearMessageOfPublic j Y

/-- Concrete CNF formula for the real linear public instance: one unit clause
locks each witness coordinate to the full public decoder `A⁻¹ b`. -/
def v13RealLinearCNFFormula {m : Nat}
    (Y : V13RealLinearPublic m) :
    ConcreteCNF.Formula (V13RealLinearCNFVar m) :=
  List.ofFn fun j : Fin m =>
    ConcreteCNF.unitClause j (v13RealLinearCNFDecodedAssignment Y j)

/-- The decoded public assignment satisfies the concrete real linear CNF. -/
theorem v13RealLinearCNFFormula_satisfied_decodedAssignment {m : Nat}
    (Y : V13RealLinearPublic m) :
    ConcreteCNF.IsSatFormula
      (v13RealLinearCNFFormula Y)
      (v13RealLinearCNFDecodedAssignment Y) := by
  intro clause hclause
  rcases List.mem_ofFn.mp hclause with ⟨j, rfl⟩
  exact
    (ConcreteCNF.isSatClause_unitClause_iff
      (v13RealLinearCNFDecodedAssignment Y) j
      (v13RealLinearCNFDecodedAssignment Y j)).mpr rfl

/-- Every satisfying assignment agrees with the full public decoder on each
witness coordinate. -/
theorem v13RealLinearCNFFormula_forces_decodedBit {m : Nat}
    {Y : V13RealLinearPublic m}
    {W : V13RealLinearCNFWitness m}
    (hW :
      ConcreteCNF.IsSatFormula
        (v13RealLinearCNFFormula Y) W)
    (j : Fin m) :
    W j = v13RealLinearCNFDecodedAssignment Y j := by
  have hclause :
      ConcreteCNF.unitClause j (v13RealLinearCNFDecodedAssignment Y j) ∈
        v13RealLinearCNFFormula Y := by
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  exact
    (ConcreteCNF.isSatClause_unitClause_iff
      W j (v13RealLinearCNFDecodedAssignment Y j)).mp
      (hW _ hclause)

/-- Satisfaction of the real linear CNF is exactly equality with the decoded
public assignment. -/
theorem v13RealLinearCNFFormula_sat_iff_decodedAssignment {m : Nat}
    {Y : V13RealLinearPublic m}
    {W : V13RealLinearCNFWitness m} :
    ConcreteCNF.IsSatFormula (v13RealLinearCNFFormula Y) W ↔
      ∀ j : Fin m, W j = v13RealLinearCNFDecodedAssignment Y j := by
  constructor
  · intro hW j
    exact v13RealLinearCNFFormula_forces_decodedBit hW j
  · intro hEq clause hclause
    rcases List.mem_ofFn.mp hclause with ⟨j, rfl⟩
    exact
      (ConcreteCNF.isSatClause_unitClause_iff
        W j (v13RealLinearCNFDecodedAssignment Y j)).mpr (hEq j)

/-- Semantic CNF verifier for the real linear SAT ensemble. -/
def v13RealLinearCNFVerifier {m : Nat}
    (Y : V13RealLinearPublic m)
    (W : V13RealLinearCNFWitness m) : Prop :=
  ConcreteCNF.IsSatFormula (v13RealLinearCNFFormula Y) W

/-- Executable verifier for the real linear CNF: check equality with the full
public decoded assignment. -/
def v13RealLinearCNFVerifierDecision {m : Nat}
    (Y : V13RealLinearPublic m)
    (W : V13RealLinearCNFWitness m) : Bool :=
  decide (∀ j : Fin m, W j = v13RealLinearCNFDecodedAssignment Y j)

/-- The executable verifier decides the semantic CNF verifier. -/
theorem v13RealLinearCNFVerifierDecision_correct {m : Nat}
    {Y : V13RealLinearPublic m}
    {W : V13RealLinearCNFWitness m} :
    v13RealLinearCNFVerifierDecision Y W = true ↔
      v13RealLinearCNFVerifier Y W := by
  rw [v13RealLinearCNFVerifierDecision, decide_eq_true_iff]
  exact
    (v13RealLinearCNFFormula_sat_iff_decodedAssignment
      (Y := Y) (W := W)).symm

/-- Fixed witness readout: read the selected witness coordinate. -/
def v13RealLinearCNFReadout {m : Nat}
    (i₀ : Fin m) (W : V13RealLinearCNFWitness m) : Bool :=
  W i₀

/-- Every verifier-valid real linear CNF witness reads the fixed public
message. -/
theorem v13RealLinearCNFReadout_eq_publicMessage_of_valid {m : Nat}
    (i₀ : Fin m) {Y : V13RealLinearPublic m}
    {W : V13RealLinearCNFWitness m}
    (hW : v13RealLinearCNFVerifier Y W) :
    v13RealLinearCNFReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y := by
  exact v13RealLinearCNFFormula_forces_decodedBit hW i₀

/-- Public formula-syntax tag: whether the concrete CNF contains the positive
unit clause for the selected target coordinate. -/
def v13RealLinearCNFFormulaPositiveTargetTag {m : Nat}
    (i₀ : Fin m)
    (formula : ConcreteCNF.Formula (V13RealLinearCNFVar m)) : Bool :=
  decide (ConcreteCNF.unitClause i₀ true ∈ formula)

/-- In the all-bits-locking real linear CNF, the public target-unit tag is
exactly the fixed public message. -/
theorem v13RealLinearCNFFormulaPositiveTargetTag_eq_publicMessage {m : Nat}
    (i₀ : Fin m) (Y : V13RealLinearPublic m) :
    v13RealLinearCNFFormulaPositiveTargetTag i₀
        (v13RealLinearCNFFormula Y) =
      v13RealLinearMessageOfPublic i₀ Y := by
  by_cases hmsg : v13RealLinearMessageOfPublic i₀ Y = true
  · have hmem :
        ConcreteCNF.unitClause i₀ true ∈ v13RealLinearCNFFormula Y := by
      refine List.mem_ofFn.mpr ⟨i₀, ?_⟩
      simp [v13RealLinearCNFDecodedAssignment, hmsg]
    simp [v13RealLinearCNFFormulaPositiveTargetTag, hmem, hmsg]
  · have hfalse : v13RealLinearMessageOfPublic i₀ Y = false :=
      Bool.eq_false_iff.mpr hmsg
    have hnot :
        ConcreteCNF.unitClause i₀ true ∉ v13RealLinearCNFFormula Y := by
      intro hmem
      rcases List.mem_ofFn.mp hmem with ⟨j, hEq⟩
      have hparts := ConcreteCNF.unitClause_eq_unitClause_iff.mp hEq
      have hj : j = i₀ := hparts.1
      have hval : v13RealLinearCNFDecodedAssignment Y j = true := hparts.2
      subst i₀
      simp [v13RealLinearCNFDecodedAssignment, hfalse] at hval
    simp [v13RealLinearCNFFormulaPositiveTargetTag, hnot, hfalse]

/-- Formula-syntax-only message determination for the all-bits-locking real
linear CNF. -/
theorem v13RealLinearCNFFormula_publicSyntaxDeterminesMessage {m : Nat}
    (i₀ : Fin m) :
    ∃ f : ConcreteCNF.Formula (V13RealLinearCNFVar m) -> Bool,
      ∀ Y : V13RealLinearPublic m,
        v13RealLinearMessageOfPublic i₀ Y =
          f (v13RealLinearCNFFormula Y) := by
  exact
    ⟨v13RealLinearCNFFormulaPositiveTargetTag i₀,
      fun Y =>
        (v13RealLinearCNFFormulaPositiveTargetTag_eq_publicMessage
          i₀ Y).symm⟩

/-- No-public-target-tags shape for the formula syntax viewed as the public
skeleton: the public CNF formula alone should not determine the message. -/
def V13RealLinearCNFFormulaNoPublicTargetTags {m : Nat}
    (i₀ : Fin m) : Prop :=
  ¬ ∃ f : ConcreteCNF.Formula (V13RealLinearCNFVar m) -> Bool,
      ∀ Y : V13RealLinearPublic m,
        v13RealLinearMessageOfPublic i₀ Y =
          f (v13RealLinearCNFFormula Y)

/-- Named obstruction: the all-bits-locking real linear CNF exposes the target
message through the public target-coordinate unit clause, so this encoding
cannot supply `noPublicTargetTags` with formula syntax as the public skeleton. -/
theorem v13RealLinearCNFFormula_noPublicTargetTags_obstruction {m : Nat}
    (i₀ : Fin m) :
    ¬ V13RealLinearCNFFormulaNoPublicTargetTags i₀ := by
  intro hNoTags
  exact hNoTags (v13RealLinearCNFFormula_publicSyntaxDeterminesMessage i₀)

/-- No-public-readout-tags shape for verifier-valid CNF witnesses: the public
CNF formula alone should not determine every valid witness readout. -/
def V13RealLinearCNFFormulaNoPublicReadoutTags {m : Nat}
    (i₀ : Fin m) : Prop :=
  ¬ ∃ f : ConcreteCNF.Formula (V13RealLinearCNFVar m) -> Bool,
      ∀ {Y : V13RealLinearPublic m} {W : V13RealLinearCNFWitness m},
        v13RealLinearCNFVerifier Y W ->
          v13RealLinearCNFReadout i₀ W =
            f (v13RealLinearCNFFormula Y)

/-- The public formula syntax determines the readout of every verifier-valid
witness in the all-bits-locking real linear CNF. -/
theorem v13RealLinearCNFFormula_publicSyntaxDeterminesReadout {m : Nat}
    (i₀ : Fin m) :
    ∃ f : ConcreteCNF.Formula (V13RealLinearCNFVar m) -> Bool,
      ∀ {Y : V13RealLinearPublic m} {W : V13RealLinearCNFWitness m},
        v13RealLinearCNFVerifier Y W ->
          v13RealLinearCNFReadout i₀ W =
            f (v13RealLinearCNFFormula Y) := by
  refine ⟨v13RealLinearCNFFormulaPositiveTargetTag i₀, ?_⟩
  intro Y W hW
  calc
    v13RealLinearCNFReadout i₀ W =
        v13RealLinearMessageOfPublic i₀ Y :=
      v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ hW
    _ =
        v13RealLinearCNFFormulaPositiveTargetTag i₀
          (v13RealLinearCNFFormula Y) :=
      (v13RealLinearCNFFormulaPositiveTargetTag_eq_publicMessage
        i₀ Y).symm

/-- Named CNF-readout obstruction: every satisfying readout is fixed, but the
fixing is visible in the public formula syntax through the target unit clause. -/
theorem v13RealLinearCNFFormula_noPublicReadoutTags_obstruction {m : Nat}
    (i₀ : Fin m) :
    ¬ V13RealLinearCNFFormulaNoPublicReadoutTags i₀ := by
  intro hNoTags
  exact hNoTags (v13RealLinearCNFFormula_publicSyntaxDeterminesReadout i₀)

/-- A SAT world for the real linear CNF ensemble is a public instance together
with a satisfying CNF assignment. -/
structure V13RealLinearCNFWorld (m : Nat) where
  publicInput : V13RealLinearPublic m
  assignment : V13RealLinearCNFWitness m
  sat : v13RealLinearCNFVerifier publicInput assignment

/-- The real linear public surface as a concrete single-message CNF/SAT
spine. -/
def v13RealLinearCNFSingleMessageSATSpine {m : Nat} (i₀ : Fin m) :
    RealSingleMessageSATSpine
      (V13RealLinearCNFWorld m)
      (V13RealLinearPublic m)
      (V13RealLinearCNFWitness m) where
  publicInput := fun omega => omega.publicInput
  witnessOfWorld := fun omega => omega.assignment
  verifier := v13RealLinearCNFVerifier
  messageOfPublic := v13RealLinearMessageOfPublic i₀
  witnessReadout := v13RealLinearCNFReadout i₀
  target := fun omega => v13RealLinearCNFReadout i₀ omega.assignment
  worldWitnessValid := by
    intro omega
    exact omega.sat
  readout_eq_message_of_valid := by
    intro Y W hW
    exact v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ hW
  target_eq_message := by
    intro omega
    exact v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ omega.sat

/-- Structural `singleMessage` for the real linear CNF/SAT spine. -/
theorem v13RealLinearCNFSingleMessageSATSpine_singleMessage {m : Nat}
    (i₀ : Fin m) :
    ∀ w0 w1 : V13RealLinearCNFWorld m,
      w0.publicInput = w1.publicInput →
        v13RealLinearCNFReadout i₀ w0.assignment =
          v13RealLinearCNFReadout i₀ w1.assignment :=
  (v13RealLinearCNFSingleMessageSATSpine i₀).singleMessage

/-- The concrete real linear CNF instantiated in the manuscript CNF readout
interface. -/
def v13RealLinearCNFReadoutData {m : Nat} (i₀ : Fin m) :
    ManuscriptCNFReadoutData
      (V13RealLinearPublic m)
      (fun _Y => V13RealLinearCNFVar m)
      (fun _Y => V13RealLinearCNFWitness m)
      Bool where
  support := fun _Y => True
  formula := v13RealLinearCNFFormula
  validWitness := v13RealLinearCNFVerifier
  extract := fun _Y α => α
  witnessMessage := fun _Y W => v13RealLinearCNFReadout i₀ W
  projection := fun _Y α => v13RealLinearCNFReadout i₀ α
  cnfSound := by
    intro Y α hα
    exact hα
  projection_eq_witnessMessage := by
    intro Y α hα
    rfl

/-- The real linear CNF readout data has the semantic single-message promise. -/
theorem v13RealLinearCNFReadoutData_singleMessagePromise {m : Nat}
    (i₀ : Fin m) :
    (v13RealLinearCNFReadoutData i₀).SingleMessagePromise := by
  intro Y W W' _hY hW hW'
  calc
    v13RealLinearCNFReadout i₀ W =
        v13RealLinearMessageOfPublic i₀ Y :=
      v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ hW
    _ = v13RealLinearCNFReadout i₀ W' :=
      (v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ hW').symm

/-- Every supported real linear public instance has a satisfying CNF
assignment. -/
theorem v13RealLinearCNFReadoutData_supportedSatisfiable {m : Nat}
    (i₀ : Fin m) :
    (v13RealLinearCNFReadoutData i₀).SupportedCNFSatisfiable := by
  intro Y _hY
  exact
    ⟨v13RealLinearCNFDecodedAssignment Y,
      v13RealLinearCNFFormula_satisfied_decodedAssignment Y⟩

/-- The arbitrary-output SAT-search readout obligation holds for the concrete
real linear CNF because every satisfying assignment has the same selected
witness-coordinate readout. -/
theorem
    v13RealLinearCNFReadoutData_supportedArbitraryOutputSATSearchCorrect
    {m : Nat} (i₀ : Fin m) :
    (v13RealLinearCNFReadoutData i₀).SupportedArbitraryOutputSATSearchCorrect := by
  exact
    (v13RealLinearCNFReadoutData i₀)
      |>.supportedArbitraryOutputSATSearchCorrect_of_singleMessagePromise
        (v13RealLinearCNFReadoutData_singleMessagePromise i₀)
        (v13RealLinearCNFReadoutData_supportedSatisfiable i₀)

/-! ## Gauge-buffered real linear CNF -/

/-- Gauge-buffered real linear CNF variables: `some j` is a locked witness
coordinate, and `none` is one free hidden gauge coordinate. -/
abbrev V13RealLinearGaugeCNFVar (m : Nat) :=
  Option (Fin m)

/-- Gauge-buffered real linear CNF witnesses are assignments to locked witness
coordinates plus one free hidden gauge coordinate. -/
abbrev V13RealLinearGaugeCNFWitness (m : Nat) :=
  ConcreteCNF.Assignment (V13RealLinearGaugeCNFVar m)

/-- The gauge-buffered CNF formula locks the real witness coordinates exactly
as before, and deliberately leaves the hidden gauge coordinate unconstrained. -/
def v13RealLinearGaugeCNFFormula {m : Nat}
    (Y : V13RealLinearPublic m) :
    ConcreteCNF.Formula (V13RealLinearGaugeCNFVar m) :=
  List.ofFn fun j : Fin m =>
    ConcreteCNF.unitClause (some j) (v13RealLinearCNFDecodedAssignment Y j)

/-- Canonical satisfying gauge-buffered assignment with an arbitrary hidden
gauge bit. -/
def v13RealLinearGaugeCNFAssignment {m : Nat}
    (Y : V13RealLinearPublic m) (gauge : Bool) :
    V13RealLinearGaugeCNFWitness m
  | some j => v13RealLinearCNFDecodedAssignment Y j
  | none => gauge

/-- Semantic verifier for the gauge-buffered real linear CNF. -/
def v13RealLinearGaugeCNFVerifier {m : Nat}
    (Y : V13RealLinearPublic m)
    (W : V13RealLinearGaugeCNFWitness m) : Prop :=
  ConcreteCNF.IsSatFormula (v13RealLinearGaugeCNFFormula Y) W

/-- Fixed readout for the gauge-buffered CNF reads the selected locked witness
coordinate, not the free hidden gauge coordinate. -/
def v13RealLinearGaugeCNFReadout {m : Nat}
    (i₀ : Fin m) (W : V13RealLinearGaugeCNFWitness m) : Bool :=
  W (some i₀)

/-- Read the free hidden gauge coordinate. -/
def v13RealLinearGaugeCNFHiddenGauge {m : Nat}
    (W : V13RealLinearGaugeCNFWitness m) : Bool :=
  W none

/-- The canonical gauge-buffered assignment satisfies the CNF for either
hidden gauge bit. -/
theorem v13RealLinearGaugeCNFFormula_satisfied_assignment {m : Nat}
    (Y : V13RealLinearPublic m) (gauge : Bool) :
    v13RealLinearGaugeCNFVerifier Y
      (v13RealLinearGaugeCNFAssignment Y gauge) := by
  intro clause hclause
  rcases List.mem_ofFn.mp hclause with ⟨j, rfl⟩
  exact
    (ConcreteCNF.isSatClause_unitClause_iff
      (v13RealLinearGaugeCNFAssignment Y gauge)
      (some j)
      (v13RealLinearCNFDecodedAssignment Y j)).mpr rfl

/-- Every satisfying gauge-buffered assignment agrees with the full public
decoder on every locked witness coordinate. -/
theorem v13RealLinearGaugeCNFFormula_forces_decodedBit {m : Nat}
    {Y : V13RealLinearPublic m}
    {W : V13RealLinearGaugeCNFWitness m}
    (hW : v13RealLinearGaugeCNFVerifier Y W)
    (j : Fin m) :
    W (some j) = v13RealLinearCNFDecodedAssignment Y j := by
  have hclause :
      ConcreteCNF.unitClause
          (some j) (v13RealLinearCNFDecodedAssignment Y j) ∈
        v13RealLinearGaugeCNFFormula Y := by
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  exact
    (ConcreteCNF.isSatClause_unitClause_iff
      W (some j) (v13RealLinearCNFDecodedAssignment Y j)).mp
      (hW _ hclause)

/-- Satisfaction of the gauge-buffered real linear CNF is exactly agreement
with the decoded public assignment on all locked witness coordinates. -/
theorem v13RealLinearGaugeCNFFormula_sat_iff_lockedAssignment {m : Nat}
    {Y : V13RealLinearPublic m}
    {W : V13RealLinearGaugeCNFWitness m} :
    v13RealLinearGaugeCNFVerifier Y W ↔
      ∀ j : Fin m, W (some j) = v13RealLinearCNFDecodedAssignment Y j := by
  constructor
  · intro hW j
    exact v13RealLinearGaugeCNFFormula_forces_decodedBit hW j
  · intro hEq clause hclause
    rcases List.mem_ofFn.mp hclause with ⟨j, rfl⟩
    exact
      (ConcreteCNF.isSatClause_unitClause_iff
        W (some j) (v13RealLinearCNFDecodedAssignment Y j)).mpr
        (hEq j)

/-- Executable verifier for the gauge-buffered real linear CNF: check the
locked witness coordinates and ignore the free hidden gauge coordinate. -/
def v13RealLinearGaugeCNFVerifierDecision {m : Nat}
    (Y : V13RealLinearPublic m)
    (W : V13RealLinearGaugeCNFWitness m) : Bool :=
  decide (∀ j : Fin m, W (some j) = v13RealLinearCNFDecodedAssignment Y j)

/-- The executable gauge-buffered verifier decides the semantic CNF verifier. -/
theorem v13RealLinearGaugeCNFVerifierDecision_correct {m : Nat}
    {Y : V13RealLinearPublic m}
    {W : V13RealLinearGaugeCNFWitness m} :
    v13RealLinearGaugeCNFVerifierDecision Y W = true ↔
      v13RealLinearGaugeCNFVerifier Y W := by
  rw [v13RealLinearGaugeCNFVerifierDecision, decide_eq_true_iff]
  exact
    (v13RealLinearGaugeCNFFormula_sat_iff_lockedAssignment
      (Y := Y) (W := W)).symm

/-- Every verifier-valid gauge-buffered assignment reads the fixed public
message. -/
theorem v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid
    {m : Nat} (i₀ : Fin m) {Y : V13RealLinearPublic m}
    {W : V13RealLinearGaugeCNFWitness m}
    (hW : v13RealLinearGaugeCNFVerifier Y W) :
    v13RealLinearGaugeCNFReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y := by
  exact v13RealLinearGaugeCNFFormula_forces_decodedBit hW i₀

/-- Flip the free hidden gauge coordinate when `gamma = true`; leave every
locked witness coordinate unchanged. -/
def v13RealLinearGaugeCNFGaugeAction {m : Nat}
    (gamma : Bool) (W : V13RealLinearGaugeCNFWitness m) :
    V13RealLinearGaugeCNFWitness m
  | some j => W (some j)
  | none => if gamma then !W none else W none

@[simp] theorem v13RealLinearGaugeCNFGaugeAction_locked {m : Nat}
    (gamma : Bool) (W : V13RealLinearGaugeCNFWitness m) (j : Fin m) :
    v13RealLinearGaugeCNFGaugeAction gamma W (some j) = W (some j) :=
  rfl

@[simp] theorem v13RealLinearGaugeCNFGaugeAction_false {m : Nat}
    (W : V13RealLinearGaugeCNFWitness m) :
    v13RealLinearGaugeCNFGaugeAction false W = W := by
  funext v
  cases v with
  | some j => rfl
  | none => rfl

/-- The hidden gauge action preserves verifier validity because the formula
does not mention the hidden gauge coordinate. -/
theorem v13RealLinearGaugeCNFGaugeAction_preserves_verifier {m : Nat}
    (gamma : Bool) {Y : V13RealLinearPublic m}
    {W : V13RealLinearGaugeCNFWitness m}
    (hW : v13RealLinearGaugeCNFVerifier Y W) :
    v13RealLinearGaugeCNFVerifier Y
      (v13RealLinearGaugeCNFGaugeAction gamma W) := by
  intro clause hclause
  rcases List.mem_ofFn.mp hclause with ⟨j, rfl⟩
  have hbit := v13RealLinearGaugeCNFFormula_forces_decodedBit hW j
  exact
    (ConcreteCNF.isSatClause_unitClause_iff
      (v13RealLinearGaugeCNFGaugeAction gamma W)
      (some j)
      (v13RealLinearCNFDecodedAssignment Y j)).mpr hbit

/-- The hidden gauge action preserves the message readout. -/
theorem v13RealLinearGaugeCNFGaugeAction_preserves_readout {m : Nat}
    (gamma : Bool) (i₀ : Fin m) (W : V13RealLinearGaugeCNFWitness m) :
    v13RealLinearGaugeCNFReadout i₀
        (v13RealLinearGaugeCNFGaugeAction gamma W) =
      v13RealLinearGaugeCNFReadout i₀ W :=
  rfl

/-- The hidden gauge action is nontrivial on satisfying assignments for every
public instance. -/
theorem v13RealLinearGaugeCNFGaugeAction_nontrivial {m : Nat}
    (Y : V13RealLinearPublic m) :
    ∃ W : V13RealLinearGaugeCNFWitness m,
      v13RealLinearGaugeCNFVerifier Y W ∧
        v13RealLinearGaugeCNFGaugeAction true W ≠ W := by
  let W := v13RealLinearGaugeCNFAssignment Y false
  refine
    ⟨W, v13RealLinearGaugeCNFFormula_satisfied_assignment Y false, ?_⟩
  intro hfixed
  have hcoord := congrFun hfixed none
  simp [W, v13RealLinearGaugeCNFGaugeAction,
    v13RealLinearGaugeCNFAssignment] at hcoord

/-- A SAT world for the gauge-buffered real linear CNF ensemble. -/
structure V13RealLinearGaugeCNFWorld (m : Nat) where
  publicInput : V13RealLinearPublic m
  assignment : V13RealLinearGaugeCNFWitness m
  sat : v13RealLinearGaugeCNFVerifier publicInput assignment

/-- The gauge-buffered real linear CNF as a concrete single-message SAT
spine. -/
def v13RealLinearGaugeCNFSingleMessageSATSpine {m : Nat} (i₀ : Fin m) :
    RealSingleMessageSATSpine
      (V13RealLinearGaugeCNFWorld m)
      (V13RealLinearPublic m)
      (V13RealLinearGaugeCNFWitness m) where
  publicInput := fun omega => omega.publicInput
  witnessOfWorld := fun omega => omega.assignment
  verifier := v13RealLinearGaugeCNFVerifier
  messageOfPublic := v13RealLinearMessageOfPublic i₀
  witnessReadout := v13RealLinearGaugeCNFReadout i₀
  target := fun omega => v13RealLinearGaugeCNFReadout i₀ omega.assignment
  worldWitnessValid := by
    intro omega
    exact omega.sat
  readout_eq_message_of_valid := by
    intro Y W hW
    exact v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid i₀ hW
  target_eq_message := by
    intro omega
    exact v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid i₀ omega.sat

/-- Structural `singleMessage` for the gauge-buffered real linear CNF/SAT
spine. -/
theorem v13RealLinearGaugeCNFSingleMessageSATSpine_singleMessage
    {m : Nat} (i₀ : Fin m) :
    ∀ w0 w1 : V13RealLinearGaugeCNFWorld m,
      w0.publicInput = w1.publicInput →
        v13RealLinearGaugeCNFReadout i₀ w0.assignment =
          v13RealLinearGaugeCNFReadout i₀ w1.assignment :=
  (v13RealLinearGaugeCNFSingleMessageSATSpine i₀).singleMessage

/-! ## No-target-rows CNF structural transfer -/

/-- CNF world over the adjusted no-target-rows real linear surface: a base
no-target-rows world together with a satisfying assignment for its concrete
CNF public instance. -/
structure V13RealLinearNoTargetRowsCNFWorld (m : Nat) (i₀ : Fin m) where
  base : V13RealLinearNoTargetRowsWorld m i₀
  assignment : V13RealLinearCNFWitness m
  sat :
    v13RealLinearCNFVerifier
      (v13RealLinearNoTargetRowsPublicInput base) assignment

/-- Canonical satisfying CNF world over a no-target-rows base world. -/
def v13RealLinearNoTargetRowsCNFWorldOfBase {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsWorld m i₀) :
    V13RealLinearNoTargetRowsCNFWorld m i₀ where
  base := omega
  assignment :=
    v13RealLinearCNFDecodedAssignment
      (v13RealLinearNoTargetRowsPublicInput omega)
  sat :=
    v13RealLinearCNFFormula_satisfied_decodedAssignment
      (v13RealLinearNoTargetRowsPublicInput omega)

/-- The no-target-rows CNF world has exactly one satisfying assignment over
each base no-target-rows world. -/
noncomputable def v13RealLinearNoTargetRowsCNFWorldBaseEquiv
    {m : Nat} {i₀ : Fin m} :
    V13RealLinearNoTargetRowsCNFWorld m i₀ ≃
      V13RealLinearNoTargetRowsWorld m i₀ where
  toFun := fun omega => omega.base
  invFun := v13RealLinearNoTargetRowsCNFWorldOfBase
  left_inv := by
    intro omega
    cases omega with
    | mk base assignment sat =>
        have hassign :
            assignment =
              v13RealLinearCNFDecodedAssignment
                (v13RealLinearNoTargetRowsPublicInput base) := by
          funext j
          exact v13RealLinearCNFFormula_forces_decodedBit sat j
        cases hassign
        rfl
  right_inv := by
    intro omega
    rfl

noncomputable instance v13RealLinearNoTargetRowsCNFWorldFintype
    {m : Nat} {i₀ : Fin m} :
    Fintype (V13RealLinearNoTargetRowsCNFWorld m i₀) :=
  Fintype.ofEquiv (V13RealLinearNoTargetRowsWorld m i₀)
    v13RealLinearNoTargetRowsCNFWorldBaseEquiv.symm

/-- The neutral skeleton of a no-target-rows CNF world is the same map
skeleton as the base public-surface world.  It deliberately does not include
the full formula syntax, whose target-unit leak is recorded separately. -/
def v13RealLinearNoTargetRowsCNFNeutralSkeleton {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsCNFWorld m i₀) :
    V13RealLinearNoTargetRowsMap m i₀ :=
  v13RealLinearNoTargetRowsNeutralSkeleton omega.base

/-- Opposite support for the no-target-rows CNF world is inherited from the
base public-surface opposite support. -/
def v13RealLinearNoTargetRowsCNFOppositeSupport {m : Nat} {i₀ : Fin m}
    (omega₀ omega₁ : V13RealLinearNoTargetRowsCNFWorld m i₀) : Prop :=
  v13RealLinearNoTargetRowsOppositeSupport omega₀.base omega₁.base

/-- CNF-world target: read the selected coordinate from the satisfying CNF
assignment. -/
def v13RealLinearNoTargetRowsCNFTarget {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsCNFWorld m i₀) : Bool :=
  v13RealLinearCNFReadout i₀ omega.assignment

/-- The CNF target readout over a no-target-rows world is the fixed public
message of its concrete public instance. -/
theorem v13RealLinearNoTargetRowsCNFReadout_eq_publicMessage {m : Nat}
    {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsCNFWorld m i₀) :
    v13RealLinearNoTargetRowsCNFTarget omega =
      v13RealLinearMessageOfPublic i₀
        (v13RealLinearNoTargetRowsPublicInput omega.base) :=
  v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ omega.sat

/-- Structural `singleMessage` transfer for the concrete real linear CNF
world over the adjusted no-target-rows public surface. -/
theorem v13RealLinearNoTargetRowsCNF_singleMessage {m : Nat}
    (i₀ : Fin m) :
    ∀ omega₀ omega₁ : V13RealLinearNoTargetRowsCNFWorld m i₀,
      v13RealLinearNoTargetRowsPublicInput omega₀.base =
        v13RealLinearNoTargetRowsPublicInput omega₁.base ->
      v13RealLinearNoTargetRowsCNFTarget omega₀ =
        v13RealLinearNoTargetRowsCNFTarget omega₁ := by
  intro omega₀ omega₁ hPublic
  calc
    v13RealLinearNoTargetRowsCNFTarget omega₀ =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega₀.base) :=
      v13RealLinearNoTargetRowsCNFReadout_eq_publicMessage omega₀
    _ =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega₁.base) := by
      rw [hPublic]
    _ = v13RealLinearNoTargetRowsCNFTarget omega₁ :=
      (v13RealLinearNoTargetRowsCNFReadout_eq_publicMessage omega₁).symm

/-- A manuscript-facing hidden gauge action should be able to move the hidden
witness while preserving the public instance.  This shape asks only for that
witness-changing part over the concrete no-target-rows CNF world. -/
def V13RealLinearNoTargetRowsCNFWitnessChangingGaugeAction {m : Nat}
    (i₀ : Fin m) : Prop :=
  ∃ act :
      Bool ->
        V13RealLinearNoTargetRowsCNFWorld m i₀ ->
          V13RealLinearNoTargetRowsCNFWorld m i₀,
    (∀ omega,
      v13RealLinearNoTargetRowsPublicInput (act true omega).base =
        v13RealLinearNoTargetRowsPublicInput omega.base) ∧
      ∃ omega,
        (act true omega).assignment ≠ omega.assignment

/-- Named hidden-gauge obstruction for the all-bits-locking real linear CNF:
because every public instance has a unique satisfying assignment, no
public-preserving action can change a satisfying witness assignment.  The
current CNF therefore lacks the free hidden witness coordinate needed for a
nontrivial manuscript-style gauge action. -/
theorem
    v13RealLinearNoTargetRowsCNF_hiddenWitnessGaugeAction_obstruction
    {m : Nat} (i₀ : Fin m) :
    ¬ V13RealLinearNoTargetRowsCNFWitnessChangingGaugeAction i₀ := by
  rintro ⟨act, hPublic, omega, hchanges⟩
  have hAct :
      (act true omega).assignment =
        v13RealLinearCNFDecodedAssignment
          (v13RealLinearNoTargetRowsPublicInput
            (act true omega).base) := by
    funext j
    exact v13RealLinearCNFFormula_forces_decodedBit
      (act true omega).sat j
  have hOmega :
      omega.assignment =
        v13RealLinearCNFDecodedAssignment
          (v13RealLinearNoTargetRowsPublicInput omega.base) := by
    funext j
    exact v13RealLinearCNFFormula_forces_decodedBit omega.sat j
  have hDecoded :
      v13RealLinearCNFDecodedAssignment
          (v13RealLinearNoTargetRowsPublicInput
            (act true omega).base) =
        v13RealLinearCNFDecodedAssignment
          (v13RealLinearNoTargetRowsPublicInput omega.base) := by
    rw [hPublic omega]
  exact hchanges (hAct.trans (hDecoded.trans hOmega.symm))

/-- Public-coordinate history field lifted from the base no-target-rows
surface to the concrete CNF world. -/
noncomputable def v13RealLinearNoTargetRowsCNFPublicCoordinateField
    {m : Nat} {i₀ : Fin m}
    (coordinate : V13RealLinearPublicCoordinate m) :
    FiniteSigmaField (V13RealLinearNoTargetRowsCNFWorld m i₀) where
  Atom := ZMod 2
  atomDecidable := inferInstance
  atom := fun omega =>
    v13RealLinearCoordinateValue coordinate
      (v13RealLinearNoTargetRowsPublicInput omega.base)

/-- The CNF readout target agrees with the base no-target-rows target bit. -/
theorem v13RealLinearNoTargetRowsCNFReadout_eq_targetBit {m : Nat}
    {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsCNFWorld m i₀) :
    v13RealLinearNoTargetRowsCNFTarget omega =
      v13RealLinearNoTargetRowsTargetBit omega.base := by
  calc
    v13RealLinearNoTargetRowsCNFTarget omega =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega.base) :=
      v13RealLinearCNFReadout_eq_publicMessage_of_valid i₀ omega.sat
    _ = v13RealLinearNoTargetRowsTargetBit omega.base := by
      have hdecode :=
        v13RealLinearNoTargetRows_fullPublic_decodes_target i₀ omega.base
      simpa [v13RealLinearMessageOfPublic,
        v13RealLinearNoTargetRowsTargetBit, v13RealLinearFullDecoder]
        using congrArg v13RealLinearBit hdecode

/-- Target-true public-coordinate fibers in the CNF world are the corresponding
base no-target-rows fibers. -/
noncomputable def v13RealLinearNoTargetRowsCNFFiberTrueEquivBase
    {m : Nat} {i₀ : Fin m}
    (coordinate : V13RealLinearPublicCoordinate m) (value : ZMod 2) :
    FiberTrue
        (fun omega : V13RealLinearNoTargetRowsCNFWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega.base))
        (@v13RealLinearNoTargetRowsCNFTarget m i₀) value ≃
      FiberTrue
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega))
        (@v13RealLinearNoTargetRowsTargetBit m i₀) value where
  toFun := fun omega =>
    ⟨omega.val.base, by
      exact ⟨omega.property.1,
        by
          have htarget :=
            v13RealLinearNoTargetRowsCNFReadout_eq_targetBit omega.val
          exact htarget ▸ omega.property.2⟩⟩
  invFun := fun omega =>
    ⟨v13RealLinearNoTargetRowsCNFWorldOfBase omega.val, by
      constructor
      · exact omega.property.1
      · rw [v13RealLinearNoTargetRowsCNFReadout_eq_targetBit]
        exact omega.property.2⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsCNFWorldBaseEquiv.left_inv omega.val
  right_inv := by
    intro omega
    rfl

/-- Target-false public-coordinate fibers in the CNF world are the
corresponding base no-target-rows fibers. -/
noncomputable def v13RealLinearNoTargetRowsCNFFiberFalseEquivBase
    {m : Nat} {i₀ : Fin m}
    (coordinate : V13RealLinearPublicCoordinate m) (value : ZMod 2) :
    FiberFalse
        (fun omega : V13RealLinearNoTargetRowsCNFWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega.base))
        (@v13RealLinearNoTargetRowsCNFTarget m i₀) value ≃
      FiberFalse
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega))
        (@v13RealLinearNoTargetRowsTargetBit m i₀) value where
  toFun := fun omega =>
    ⟨omega.val.base, by
      exact ⟨omega.property.1,
        by
          have htarget :=
            v13RealLinearNoTargetRowsCNFReadout_eq_targetBit omega.val
          exact htarget ▸ omega.property.2⟩⟩
  invFun := fun omega =>
    ⟨v13RealLinearNoTargetRowsCNFWorldOfBase omega.val, by
      constructor
      · exact omega.property.1
      · rw [v13RealLinearNoTargetRowsCNFReadout_eq_targetBit]
        exact omega.property.2⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsCNFWorldBaseEquiv.left_inv omega.val
  right_inv := by
    intro omega
    rfl

/-- Public-coordinate conditioning balance transfers from the base
no-target-rows surface to the concrete CNF world. -/
theorem v13RealLinearNoTargetRowsCNF_publicCoordinate_balancedConditioning
    {m : Nat} (i₀ : Fin m)
    (coordinate : V13RealLinearPublicCoordinate m) :
    BalancedConditioning
      (v13RealLinearNoTargetRowsCNFPublicCoordinateField (i₀ := i₀)
        coordinate)
      (@v13RealLinearNoTargetRowsCNFTarget m i₀) := by
  classical
  change Neutral
    (fun omega : V13RealLinearNoTargetRowsCNFWorld m i₀ =>
      v13RealLinearCoordinateValue coordinate
        (v13RealLinearNoTargetRowsPublicInput omega.base))
    (@v13RealLinearNoTargetRowsCNFTarget m i₀)
  intro value
  calc
    Fintype.card
        (FiberTrue
          (fun omega : V13RealLinearNoTargetRowsCNFWorld m i₀ =>
            v13RealLinearCoordinateValue coordinate
              (v13RealLinearNoTargetRowsPublicInput omega.base))
          (@v13RealLinearNoTargetRowsCNFTarget m i₀) value) =
        Fintype.card
          (FiberTrue
            (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
              v13RealLinearCoordinateValue coordinate
                (v13RealLinearNoTargetRowsPublicInput omega))
            (@v13RealLinearNoTargetRowsTargetBit m i₀) value) :=
      Fintype.card_congr
        (v13RealLinearNoTargetRowsCNFFiberTrueEquivBase coordinate value)
    _ =
        Fintype.card
          (FiberFalse
            (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
              v13RealLinearCoordinateValue coordinate
                (v13RealLinearNoTargetRowsPublicInput omega))
            (@v13RealLinearNoTargetRowsTargetBit m i₀) value) := by
      have h :=
        v13RealLinearNoTargetRows_publicCoordinate_balancedConditioning
          i₀ coordinate
      change Neutral
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega))
        (@v13RealLinearNoTargetRowsTargetBit m i₀) at h
      exact h value
    _ =
        Fintype.card
          (FiberFalse
            (fun omega : V13RealLinearNoTargetRowsCNFWorld m i₀ =>
              v13RealLinearCoordinateValue coordinate
                (v13RealLinearNoTargetRowsPublicInput omega.base))
            (@v13RealLinearNoTargetRowsCNFTarget m i₀) value) :=
      (Fintype.card_congr
        (v13RealLinearNoTargetRowsCNFFiberFalseEquivBase
          coordinate value)).symm

/-- Constant-true correct fibers in the CNF world are the corresponding base
no-target-rows fibers. -/
noncomputable def v13RealLinearNoTargetRowsCNFCorrectTrueEquivBase
    {m : Nat} {i₀ : Fin m} :
    {omega : V13RealLinearNoTargetRowsCNFWorld m i₀ //
      (fun _ : V13RealLinearNoTargetRowsCNFWorld m i₀ => true) omega =
        v13RealLinearNoTargetRowsCNFTarget omega} ≃
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        (fun _ : V13RealLinearNoTargetRowsWorld m i₀ => true) omega =
          v13RealLinearNoTargetRowsTargetBit omega} where
  toFun := fun omega =>
    ⟨omega.val.base, by
      have htarget :=
        v13RealLinearNoTargetRowsCNFReadout_eq_targetBit omega.val
      exact htarget ▸ omega.property⟩
  invFun := fun omega =>
    ⟨v13RealLinearNoTargetRowsCNFWorldOfBase omega.val, by
      rw [v13RealLinearNoTargetRowsCNFReadout_eq_targetBit]
      exact omega.property⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsCNFWorldBaseEquiv.left_inv omega.val
  right_inv := by
    intro omega
    rfl

/-- Global target balance transfers from the base no-target-rows surface to
the concrete CNF world. -/
theorem v13RealLinearNoTargetRowsCNF_target_balanced {m : Nat}
    (i₀ : Fin m) (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsCNFTarget m i₀) := by
  unfold BalancedBit globalDecoderSuccess
  have hcorrect :
      Fintype.card
        {omega : V13RealLinearNoTargetRowsCNFWorld m i₀ //
          (fun _ : V13RealLinearNoTargetRowsCNFWorld m i₀ => true) omega =
            v13RealLinearNoTargetRowsCNFTarget omega} =
        Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          (fun _ : V13RealLinearNoTargetRowsWorld m i₀ => true) omega =
            v13RealLinearNoTargetRowsTargetBit omega} :=
    Fintype.card_congr v13RealLinearNoTargetRowsCNFCorrectTrueEquivBase
  have hall :
      Fintype.card (V13RealLinearNoTargetRowsCNFWorld m i₀) =
        Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) :=
    Fintype.card_congr v13RealLinearNoTargetRowsCNFWorldBaseEquiv
  rw [hcorrect, hall]
  exact v13RealLinearNoTargetRows_target_balanced i₀ hm

/-- Structural `admissibleHistories` transfer for the concrete no-target-rows
CNF world using a single public-coordinate history field. -/
theorem v13RealLinearNoTargetRowsCNF_admissibleHistories {m : Nat}
    (i₀ : Fin m) (coordinate : V13RealLinearPublicCoordinate m)
    (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsCNFTarget m i₀) ∧
      BalancedConditioning
        (v13RealLinearNoTargetRowsCNFPublicCoordinateField (i₀ := i₀)
          coordinate)
        (@v13RealLinearNoTargetRowsCNFTarget m i₀) :=
  ⟨v13RealLinearNoTargetRowsCNF_target_balanced i₀ hm,
    v13RealLinearNoTargetRowsCNF_publicCoordinate_balancedConditioning
      i₀ coordinate⟩

/-- Pair-neutrality transfers from the no-target-rows public surface to the
CNF world when the neutral skeleton is the base no-target-rows map skeleton. -/
theorem v13RealLinearNoTargetRowsCNF_pairNeutral {m : Nat}
    {i₀ : Fin m} :
    PairNeutral
      (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
      (@v13RealLinearNoTargetRowsCNFNeutralSkeleton m i₀) := by
  intro omega₀ omega₁ hSupport
  exact
    v13RealLinearNoTargetRows_pairNeutral omega₀.base omega₁.base hSupport

/-- The opposite-message pair transfers through canonical satisfying CNF
assignments. -/
theorem v13RealLinearNoTargetRowsCNF_hasMessageOppositePair {m : Nat}
    (i₀ : Fin m) (hm : 1 < m) :
    HasMessageOppositePair
      (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
      (@v13RealLinearNoTargetRowsCNFTarget m i₀) := by
  rcases v13RealLinearNoTargetRows_hasMessageOppositePair i₀ hm with
    ⟨omega₀, omega₁, hSupport, h0, h1⟩
  refine
    ⟨v13RealLinearNoTargetRowsCNFWorldOfBase omega₀,
      v13RealLinearNoTargetRowsCNFWorldOfBase omega₁,
      hSupport, ?_, ?_⟩
  · rw [v13RealLinearNoTargetRowsCNFReadout_eq_targetBit]
    exact h0
  · rw [v13RealLinearNoTargetRowsCNFReadout_eq_targetBit]
    exact h1

/-- Structural `noPublicTargetTags` transfer for the concrete real linear CNF
world over the adjusted no-target-rows surface.  This transfers the
manuscript-shaped neutral-skeleton field; it does not erase the separate fact
that the full all-bits-locking formula syntax exposes the target-unit tag. -/
theorem v13RealLinearNoTargetRowsCNF_noPublicTargetTags {m : Nat}
    (i₀ : Fin m) (hm : 1 < m) :
    PairNeutral
        (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsCNFNeutralSkeleton m i₀) ∧
      HasMessageOppositePair
        (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsCNFTarget m i₀) ∧
        ¬ ∃ f : V13RealLinearNoTargetRowsMap m i₀ -> Bool,
          ∀ omega : V13RealLinearNoTargetRowsCNFWorld m i₀,
            v13RealLinearNoTargetRowsCNFTarget omega =
              f (v13RealLinearNoTargetRowsCNFNeutralSkeleton omega) := by
  have hPair :
      PairNeutral
        (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsCNFNeutralSkeleton m i₀) :=
    v13RealLinearNoTargetRowsCNF_pairNeutral
  have hOpp :
      HasMessageOppositePair
        (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsCNFTarget m i₀) :=
    v13RealLinearNoTargetRowsCNF_hasMessageOppositePair i₀ hm
  exact
    ⟨hPair, hOpp,
      neutralSkeleton_not_sufficient
        (@v13RealLinearNoTargetRowsCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsCNFNeutralSkeleton m i₀)
        (@v13RealLinearNoTargetRowsCNFTarget m i₀)
        hPair hOpp⟩

/-! ## No-target-rows gauge-buffered CNF construction -/

/-- Gauge-buffered CNF world over the adjusted no-target-rows real linear
surface.  The locked witness coordinates satisfy the public instance, while
one extra hidden gauge coordinate remains free. -/
structure V13RealLinearNoTargetRowsGaugeCNFWorld
    (m : Nat) (i₀ : Fin m) where
  base : V13RealLinearNoTargetRowsWorld m i₀
  assignment : V13RealLinearGaugeCNFWitness m
  sat :
    v13RealLinearGaugeCNFVerifier
      (v13RealLinearNoTargetRowsPublicInput base) assignment

/-- Canonical no-target-rows gauge-buffered CNF world with a chosen hidden
gauge bit. -/
def v13RealLinearNoTargetRowsGaugeCNFWorldOfBase {m : Nat}
    {i₀ : Fin m} (omega : V13RealLinearNoTargetRowsWorld m i₀)
    (gauge : Bool) :
    V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ where
  base := omega
  assignment :=
    v13RealLinearGaugeCNFAssignment
      (v13RealLinearNoTargetRowsPublicInput omega) gauge
  sat :=
    v13RealLinearGaugeCNFFormula_satisfied_assignment
      (v13RealLinearNoTargetRowsPublicInput omega) gauge

/-- Target readout for the no-target-rows gauge-buffered CNF world. -/
def v13RealLinearNoTargetRowsGaugeCNFTarget {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) : Bool :=
  v13RealLinearGaugeCNFReadout i₀ omega.assignment

/-- Hidden-gauge readout for the no-target-rows gauge-buffered CNF world. -/
def v13RealLinearNoTargetRowsGaugeCNFHiddenGauge {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) : Bool :=
  v13RealLinearGaugeCNFHiddenGauge omega.assignment

/-- The no-target-rows gauge-buffered CNF target readout is the fixed public
message of its concrete public instance. -/
theorem v13RealLinearNoTargetRowsGaugeCNFReadout_eq_publicMessage
    {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    v13RealLinearNoTargetRowsGaugeCNFTarget omega =
      v13RealLinearMessageOfPublic i₀
        (v13RealLinearNoTargetRowsPublicInput omega.base) :=
  v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid i₀ omega.sat

/-- Structural `singleMessage` transfer for the no-target-rows
gauge-buffered CNF world. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_singleMessage {m : Nat}
    (i₀ : Fin m) :
    ∀ omega₀ omega₁ : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀,
      v13RealLinearNoTargetRowsPublicInput omega₀.base =
        v13RealLinearNoTargetRowsPublicInput omega₁.base ->
      v13RealLinearNoTargetRowsGaugeCNFTarget omega₀ =
        v13RealLinearNoTargetRowsGaugeCNFTarget omega₁ := by
  intro omega₀ omega₁ hPublic
  calc
    v13RealLinearNoTargetRowsGaugeCNFTarget omega₀ =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega₀.base) :=
      v13RealLinearNoTargetRowsGaugeCNFReadout_eq_publicMessage omega₀
    _ =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega₁.base) := by
      rw [hPublic]
    _ = v13RealLinearNoTargetRowsGaugeCNFTarget omega₁ :=
      (v13RealLinearNoTargetRowsGaugeCNFReadout_eq_publicMessage
        omega₁).symm

/-- The neutral skeleton of a no-target-rows gauge-buffered CNF world is the
same map skeleton as the base no-target-rows world. -/
def v13RealLinearNoTargetRowsGaugeCNFNeutralSkeleton
    {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    V13RealLinearNoTargetRowsMap m i₀ :=
  v13RealLinearNoTargetRowsNeutralSkeleton omega.base

/-- Opposite support for the no-target-rows gauge-buffered CNF world is
inherited from the base no-target-rows world. -/
def v13RealLinearNoTargetRowsGaugeCNFOppositeSupport
    {m : Nat} {i₀ : Fin m}
    (omega₀ omega₁ : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    Prop :=
  v13RealLinearNoTargetRowsOppositeSupport omega₀.base omega₁.base

/-- The gauge-buffered CNF readout target agrees with the base
no-target-rows target bit. -/
theorem v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit
    {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    v13RealLinearNoTargetRowsGaugeCNFTarget omega =
      v13RealLinearNoTargetRowsTargetBit omega.base := by
  calc
    v13RealLinearNoTargetRowsGaugeCNFTarget omega =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega.base) :=
      v13RealLinearNoTargetRowsGaugeCNFReadout_eq_publicMessage omega
    _ = v13RealLinearNoTargetRowsTargetBit omega.base := by
      have hdecode :=
        v13RealLinearNoTargetRows_fullPublic_decodes_target i₀ omega.base
      simpa [v13RealLinearMessageOfPublic,
        v13RealLinearNoTargetRowsTargetBit, v13RealLinearFullDecoder]
        using congrArg v13RealLinearBit hdecode

/-- Pair-neutrality transfers to the gauge-buffered CNF world when the public
neutral skeleton is the base no-target-rows map skeleton. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_pairNeutral
    {m : Nat} {i₀ : Fin m} :
    PairNeutral
      (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
      (@v13RealLinearNoTargetRowsGaugeCNFNeutralSkeleton m i₀) := by
  intro omega₀ omega₁ hSupport
  exact
    v13RealLinearNoTargetRows_pairNeutral omega₀.base omega₁.base
      hSupport

/-- Opposite-message pairs transfer to the gauge-buffered CNF world by using
canonical satisfying assignments with a fixed hidden gauge bit. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_hasMessageOppositePair
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    HasMessageOppositePair
      (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
      (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) := by
  rcases v13RealLinearNoTargetRows_hasMessageOppositePair i₀ hm with
    ⟨omega₀, omega₁, hSupport, h0, h1⟩
  refine
    ⟨v13RealLinearNoTargetRowsGaugeCNFWorldOfBase omega₀ false,
      v13RealLinearNoTargetRowsGaugeCNFWorldOfBase omega₁ false,
      hSupport, ?_, ?_⟩
  · rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
    exact h0
  · rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
    exact h1

/-- Structural `noPublicTargetTags` transfer for the no-target-rows
gauge-buffered CNF world.  The transferred public skeleton is the
manuscript-shaped no-target-rows map skeleton; the hidden gauge coordinate is
not public data and the full locking formula-syntax leak remains recorded by
the separate obstruction theorem above. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_noPublicTargetTags
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    PairNeutral
        (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsGaugeCNFNeutralSkeleton m i₀) ∧
      HasMessageOppositePair
        (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) ∧
        ¬ ∃ f : V13RealLinearNoTargetRowsMap m i₀ -> Bool,
          ∀ omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀,
            v13RealLinearNoTargetRowsGaugeCNFTarget omega =
              f (v13RealLinearNoTargetRowsGaugeCNFNeutralSkeleton
                omega) := by
  have hPair :
      PairNeutral
        (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsGaugeCNFNeutralSkeleton m i₀) :=
    v13RealLinearNoTargetRowsGaugeCNF_pairNeutral
  have hOpp :
      HasMessageOppositePair
        (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) :=
    v13RealLinearNoTargetRowsGaugeCNF_hasMessageOppositePair i₀ hm
  exact
    ⟨hPair, hOpp,
      neutralSkeleton_not_sufficient
        (@v13RealLinearNoTargetRowsGaugeCNFOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsGaugeCNFNeutralSkeleton m i₀)
        (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀)
        hPair hOpp⟩

/-- A gauge-buffered no-target-rows CNF world is exactly a base no-target-rows
world together with the free hidden gauge bit. -/
noncomputable def v13RealLinearNoTargetRowsGaugeCNFWorldBaseGaugeEquiv
    {m : Nat} {i₀ : Fin m} :
    V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ ≃
      V13RealLinearNoTargetRowsWorld m i₀ × Bool where
  toFun := fun omega =>
    (omega.base, v13RealLinearNoTargetRowsGaugeCNFHiddenGauge omega)
  invFun := fun data =>
    v13RealLinearNoTargetRowsGaugeCNFWorldOfBase data.1 data.2
  left_inv := by
    intro omega
    cases omega with
    | mk base assignment sat =>
        let publicInput := v13RealLinearNoTargetRowsPublicInput base
        let gauge := v13RealLinearGaugeCNFHiddenGauge assignment
        let canonical := v13RealLinearGaugeCNFAssignment publicInput gauge
        have hassign :
            assignment = canonical := by
          funext v
          cases v with
          | some j =>
              exact v13RealLinearGaugeCNFFormula_forces_decodedBit sat j
          | none => rfl
        change
          v13RealLinearNoTargetRowsGaugeCNFWorldOfBase base gauge =
            { base := base, assignment := assignment, sat := sat }
        exact
          Eq.ndrec
            (motive := fun assignment' =>
              ∀ sat' : v13RealLinearGaugeCNFVerifier publicInput
                  assignment',
                v13RealLinearNoTargetRowsGaugeCNFWorldOfBase base gauge =
                  { base := base, assignment := assignment', sat := sat' })
            (by
              intro sat'
              have hs :
                  v13RealLinearGaugeCNFFormula_satisfied_assignment
                      publicInput gauge =
                    sat' := Subsingleton.elim _ _
              cases hs
              rfl)
            hassign.symm sat
  right_inv := by
    intro data
    cases data with
    | mk base gauge => rfl

noncomputable instance v13RealLinearNoTargetRowsGaugeCNFWorldFintype
    {m : Nat} {i₀ : Fin m} :
    Fintype (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :=
  Fintype.ofEquiv (V13RealLinearNoTargetRowsWorld m i₀ × Bool)
    v13RealLinearNoTargetRowsGaugeCNFWorldBaseGaugeEquiv.symm

/-- Public-coordinate history field lifted to the gauge-buffered CNF world. -/
noncomputable def v13RealLinearNoTargetRowsGaugeCNFPublicCoordinateField
    {m : Nat} {i₀ : Fin m}
    (coordinate : V13RealLinearPublicCoordinate m) :
    FiniteSigmaField (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) where
  Atom := ZMod 2
  atomDecidable := inferInstance
  atom := fun omega =>
    v13RealLinearCoordinateValue coordinate
      (v13RealLinearNoTargetRowsPublicInput omega.base)

/-- Target-true worlds in the gauge-buffered CNF world are target-true base
worlds with an arbitrary hidden gauge bit. -/
noncomputable def v13RealLinearNoTargetRowsGaugeCNFTargetTrueEquivBaseProd
    {m : Nat} {i₀ : Fin m} :
    {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
      v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} ≃
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        v13RealLinearNoTargetRowsTargetBit omega = true} × Bool where
  toFun := fun omega =>
    (⟨omega.val.base, by
      have htarget :=
        v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit omega.val
      exact htarget ▸ omega.property⟩,
      v13RealLinearNoTargetRowsGaugeCNFHiddenGauge omega.val)
  invFun := fun data =>
    ⟨v13RealLinearNoTargetRowsGaugeCNFWorldOfBase data.1.val data.2, by
      rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
      exact data.1.property⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsGaugeCNFWorldBaseGaugeEquiv.left_inv
      omega.val
  right_inv := by
    intro data
    cases data with
    | mk omega gauge =>
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl

/-- Target-false worlds in the gauge-buffered CNF world are target-false base
worlds with an arbitrary hidden gauge bit. -/
noncomputable def v13RealLinearNoTargetRowsGaugeCNFTargetFalseEquivBaseProd
    {m : Nat} {i₀ : Fin m} :
    {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
      v13RealLinearNoTargetRowsGaugeCNFTarget omega = false} ≃
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        v13RealLinearNoTargetRowsTargetBit omega = false} × Bool where
  toFun := fun omega =>
    (⟨omega.val.base, by
      have htarget :=
        v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit omega.val
      exact htarget ▸ omega.property⟩,
      v13RealLinearNoTargetRowsGaugeCNFHiddenGauge omega.val)
  invFun := fun data =>
    ⟨v13RealLinearNoTargetRowsGaugeCNFWorldOfBase data.1.val data.2, by
      rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
      exact data.1.property⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsGaugeCNFWorldBaseGaugeEquiv.left_inv
      omega.val
  right_inv := by
    intro data
    cases data with
    | mk omega gauge =>
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl

theorem v13RealLinearNoTargetRowsGaugeCNFTarget_false_card_eq_true
    {m : Nat} {i₀ : Fin m} :
    Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = false} =
      Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} := by
  calc
    Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = false} =
        Fintype.card
          ({omega : V13RealLinearNoTargetRowsWorld m i₀ //
            v13RealLinearNoTargetRowsTargetBit omega = false} × Bool) :=
      Fintype.card_congr
        v13RealLinearNoTargetRowsGaugeCNFTargetFalseEquivBaseProd
    _ =
        Fintype.card
          ({omega : V13RealLinearNoTargetRowsWorld m i₀ //
            v13RealLinearNoTargetRowsTargetBit omega = true} × Bool) := by
      rw [Fintype.card_prod, Fintype.card_prod,
        v13RealLinearNoTargetRowsTarget_false_card_eq_true]
    _ =
        Fintype.card
          {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
            v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} :=
      (Fintype.card_congr
        v13RealLinearNoTargetRowsGaugeCNFTargetTrueEquivBaseProd).symm

theorem
    v13RealLinearNoTargetRowsGaugeCNF_constantTrue_correct_card_eq_true
    {m : Nat} {i₀ : Fin m} :
    Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          (fun _ : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
            true) omega =
            v13RealLinearNoTargetRowsGaugeCNFTarget omega} =
      Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} := by
  let e :
      {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
        (fun _ : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
          true) omega =
          v13RealLinearNoTargetRowsGaugeCNFTarget omega} ≃
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} :=
    { toFun := fun omega => ⟨omega.val, omega.property.symm⟩
      invFun := fun omega => ⟨omega.val, omega.property.symm⟩
      left_inv := by
        intro omega
        cases omega
        rfl
      right_inv := by
        intro omega
        cases omega
        rfl }
  exact Fintype.card_congr e

theorem
    v13RealLinearNoTargetRowsGaugeCNF_world_card_eq_two_mul_target_true
    {m : Nat} (i₀ : Fin m) :
    Fintype.card (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) =
      2 * Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} := by
  set a : Nat :=
    Fintype.card
      {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
        v13RealLinearNoTargetRowsGaugeCNFTarget omega = true}
  have hcomp :
      Fintype.card
          {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
            v13RealLinearNoTargetRowsGaugeCNFTarget omega = false} =
        Fintype.card (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) -
          a := by
    simpa [a] using
      (Fintype.card_subtype_compl
        (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true))
  have heq :
      a =
        Fintype.card
          {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
            v13RealLinearNoTargetRowsGaugeCNFTarget omega = false} := by
    simpa [a] using
      (@v13RealLinearNoTargetRowsGaugeCNFTarget_false_card_eq_true
        m i₀).symm
  have hsub :
      Fintype.card (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) -
          a =
        a := by
    simpa [heq] using hcomp.symm
  have hle :
      a ≤
        Fintype.card (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) := by
    simpa [a] using
      Fintype.card_subtype_le
        (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true)
  have hsum :
      Fintype.card (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) =
        a + a :=
    Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum

theorem v13RealLinearNoTargetRowsGaugeCNFTarget_true_card_pos
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    0 <
      Fintype.card
        {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
          v13RealLinearNoTargetRowsGaugeCNFTarget omega = true} := by
  rcases Fintype.card_pos_iff.mp
      (v13RealLinearNoTargetRowsTarget_true_card_pos i₀ hm) with
    ⟨omega⟩
  apply Fintype.card_pos_iff.mpr
  exact
    ⟨⟨v13RealLinearNoTargetRowsGaugeCNFWorldOfBase omega.val false, by
      rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
      exact omega.property⟩⟩

/-- Global target balance transfers to the gauge-buffered CNF world. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_target_balanced
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) := by
  unfold BalancedBit globalDecoderSuccess
  rw [v13RealLinearNoTargetRowsGaugeCNF_constantTrue_correct_card_eq_true]
  rw [v13RealLinearNoTargetRowsGaugeCNF_world_card_eq_two_mul_target_true
    i₀]
  set a : Nat :=
    Fintype.card
      {omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ //
        v13RealLinearNoTargetRowsGaugeCNFTarget omega = true}
  have hpos : 0 < a := by
    simpa [a] using
      v13RealLinearNoTargetRowsGaugeCNFTarget_true_card_pos i₀ hm
  have hne : (a : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [Nat.cast_mul]
  field_simp [hne]
  norm_num

/-- Target-true public-coordinate fibers in the gauge-buffered CNF world are
base target-true fibers times the hidden gauge bit. -/
noncomputable def v13RealLinearNoTargetRowsGaugeCNFFiberTrueEquivBaseProd
    {m : Nat} {i₀ : Fin m}
    (coordinate : V13RealLinearPublicCoordinate m) (value : ZMod 2) :
    FiberTrue
        (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega.base))
        (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) value ≃
      FiberTrue
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega))
        (@v13RealLinearNoTargetRowsTargetBit m i₀) value × Bool where
  toFun := fun omega =>
    (⟨omega.val.base, by
      exact ⟨omega.property.1, by
        have htarget :=
          v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit
            omega.val
        exact htarget ▸ omega.property.2⟩⟩,
      v13RealLinearNoTargetRowsGaugeCNFHiddenGauge omega.val)
  invFun := fun data =>
    ⟨v13RealLinearNoTargetRowsGaugeCNFWorldOfBase data.1.val data.2, by
      constructor
      · exact data.1.property.1
      · rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
        exact data.1.property.2⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsGaugeCNFWorldBaseGaugeEquiv.left_inv
      omega.val
  right_inv := by
    intro data
    cases data with
    | mk omega gauge =>
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl

/-- Target-false public-coordinate fibers in the gauge-buffered CNF world are
base target-false fibers times the hidden gauge bit. -/
noncomputable def v13RealLinearNoTargetRowsGaugeCNFFiberFalseEquivBaseProd
    {m : Nat} {i₀ : Fin m}
    (coordinate : V13RealLinearPublicCoordinate m) (value : ZMod 2) :
    FiberFalse
        (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega.base))
        (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) value ≃
      FiberFalse
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega))
        (@v13RealLinearNoTargetRowsTargetBit m i₀) value × Bool where
  toFun := fun omega =>
    (⟨omega.val.base, by
      exact ⟨omega.property.1, by
        have htarget :=
          v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit
            omega.val
        exact htarget ▸ omega.property.2⟩⟩,
      v13RealLinearNoTargetRowsGaugeCNFHiddenGauge omega.val)
  invFun := fun data =>
    ⟨v13RealLinearNoTargetRowsGaugeCNFWorldOfBase data.1.val data.2, by
      constructor
      · exact data.1.property.1
      · rw [v13RealLinearNoTargetRowsGaugeCNFReadout_eq_targetBit]
        exact data.1.property.2⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    exact v13RealLinearNoTargetRowsGaugeCNFWorldBaseGaugeEquiv.left_inv
      omega.val
  right_inv := by
    intro data
    cases data with
    | mk omega gauge =>
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · rfl

/-- Public-coordinate conditioning balance transfers to the gauge-buffered
CNF world. -/
theorem
    v13RealLinearNoTargetRowsGaugeCNF_publicCoordinate_balancedConditioning
    {m : Nat} (i₀ : Fin m)
    (coordinate : V13RealLinearPublicCoordinate m) :
    BalancedConditioning
      (v13RealLinearNoTargetRowsGaugeCNFPublicCoordinateField
        (i₀ := i₀) coordinate)
      (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) := by
  classical
  change Neutral
    (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
      v13RealLinearCoordinateValue coordinate
        (v13RealLinearNoTargetRowsPublicInput omega.base))
    (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀)
  intro value
  calc
    Fintype.card
        (FiberTrue
          (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
            v13RealLinearCoordinateValue coordinate
              (v13RealLinearNoTargetRowsPublicInput omega.base))
          (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) value) =
        Fintype.card
          (FiberTrue
            (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
              v13RealLinearCoordinateValue coordinate
                (v13RealLinearNoTargetRowsPublicInput omega))
            (@v13RealLinearNoTargetRowsTargetBit m i₀) value × Bool) :=
      Fintype.card_congr
        (v13RealLinearNoTargetRowsGaugeCNFFiberTrueEquivBaseProd
          coordinate value)
    _ =
        Fintype.card
          (FiberFalse
            (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
              v13RealLinearCoordinateValue coordinate
                (v13RealLinearNoTargetRowsPublicInput omega))
            (@v13RealLinearNoTargetRowsTargetBit m i₀) value × Bool) := by
      have h :=
        v13RealLinearNoTargetRows_publicCoordinate_balancedConditioning
          i₀ coordinate
      change Neutral
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearCoordinateValue coordinate
            (v13RealLinearNoTargetRowsPublicInput omega))
        (@v13RealLinearNoTargetRowsTargetBit m i₀) at h
      rw [Fintype.card_prod, Fintype.card_prod, h value]
    _ =
        Fintype.card
          (FiberFalse
            (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
              v13RealLinearCoordinateValue coordinate
                (v13RealLinearNoTargetRowsPublicInput omega.base))
            (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) value) :=
      (Fintype.card_congr
        (v13RealLinearNoTargetRowsGaugeCNFFiberFalseEquivBaseProd
          coordinate value)).symm

/-- Structural `admissibleHistories` transfer for the gauge-buffered
no-target-rows CNF world using a public-coordinate history field. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_admissibleHistories
    {m : Nat} (i₀ : Fin m)
    (coordinate : V13RealLinearPublicCoordinate m) (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) ∧
      BalancedConditioning
        (v13RealLinearNoTargetRowsGaugeCNFPublicCoordinateField
          (i₀ := i₀) coordinate)
        (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀) :=
  ⟨v13RealLinearNoTargetRowsGaugeCNF_target_balanced i₀ hm,
    v13RealLinearNoTargetRowsGaugeCNF_publicCoordinate_balancedConditioning
      i₀ coordinate⟩

/-- Flip the hidden gauge coordinate of a no-target-rows gauge-buffered CNF
world, preserving the base public instance and verifier validity. -/
def v13RealLinearNoTargetRowsGaugeCNFGaugeAction {m : Nat}
    {i₀ : Fin m} (gamma : Bool)
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ where
  base := omega.base
  assignment := v13RealLinearGaugeCNFGaugeAction gamma omega.assignment
  sat :=
    v13RealLinearGaugeCNFGaugeAction_preserves_verifier gamma omega.sat

@[simp] theorem v13RealLinearNoTargetRowsGaugeCNFGaugeAction_public
    {m : Nat} {i₀ : Fin m} (gamma : Bool)
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    (v13RealLinearNoTargetRowsGaugeCNFGaugeAction gamma omega).base =
      omega.base :=
  rfl

/-- The no-target-rows gauge action preserves the target readout. -/
theorem v13RealLinearNoTargetRowsGaugeCNFGaugeAction_preserves_target
    {m : Nat} {i₀ : Fin m} (gamma : Bool)
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    v13RealLinearNoTargetRowsGaugeCNFTarget
        (v13RealLinearNoTargetRowsGaugeCNFGaugeAction gamma omega) =
      v13RealLinearNoTargetRowsGaugeCNFTarget omega :=
  v13RealLinearGaugeCNFGaugeAction_preserves_readout
    gamma i₀ omega.assignment

/-- The no-target-rows gauge action flips the hidden gauge coordinate when
`gamma = true`. -/
theorem v13RealLinearNoTargetRowsGaugeCNFGaugeAction_hidden_true
    {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) :
    v13RealLinearNoTargetRowsGaugeCNFHiddenGauge
        (v13RealLinearNoTargetRowsGaugeCNFGaugeAction true omega) =
      !v13RealLinearNoTargetRowsGaugeCNFHiddenGauge omega :=
  rfl

/-- The no-target-rows gauge action is nontrivial over every base world:
choosing hidden gauge `false` and acting by `true` changes the satisfying
assignment while preserving the public instance. -/
theorem v13RealLinearNoTargetRowsGaugeCNFGaugeAction_nontrivial
    {m : Nat} {i₀ : Fin m}
    (base : V13RealLinearNoTargetRowsWorld m i₀) :
    ∃ omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀,
      v13RealLinearNoTargetRowsGaugeCNFGaugeAction true omega ≠ omega := by
  let omega :=
    v13RealLinearNoTargetRowsGaugeCNFWorldOfBase base false
  refine ⟨omega, ?_⟩
  intro hfixed
  have hcoord := congrFun (congrArg
    (fun omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ =>
      omega.assignment) hfixed) none
  simp [omega,
    v13RealLinearNoTargetRowsGaugeCNFWorldOfBase,
    v13RealLinearGaugeCNFAssignment,
    v13RealLinearNoTargetRowsGaugeCNFGaugeAction,
    v13RealLinearGaugeCNFGaugeAction] at hcoord

end Mettapedia.Computability.PNP
