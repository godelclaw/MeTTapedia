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

/-- Public formula-syntax tag for the gauge-buffered CNF: whether the
concrete CNF contains the positive unit clause for the selected locked target
coordinate. -/
def v13RealLinearGaugeCNFFormulaPositiveTargetTag {m : Nat}
    (i₀ : Fin m)
    (formula : ConcreteCNF.Formula (V13RealLinearGaugeCNFVar m)) : Bool :=
  decide (ConcreteCNF.unitClause (some i₀) true ∈ formula)

/-- In the gauge-buffered CNF, the public target-unit tag is still exactly the
fixed public message.  The extra hidden gauge coordinate does not remove the
formula-syntax leak. -/
theorem v13RealLinearGaugeCNFFormulaPositiveTargetTag_eq_publicMessage
    {m : Nat} (i₀ : Fin m) (Y : V13RealLinearPublic m) :
    v13RealLinearGaugeCNFFormulaPositiveTargetTag i₀
        (v13RealLinearGaugeCNFFormula Y) =
      v13RealLinearMessageOfPublic i₀ Y := by
  by_cases hmsg : v13RealLinearMessageOfPublic i₀ Y = true
  · have hmem :
        ConcreteCNF.unitClause (some i₀) true ∈
          v13RealLinearGaugeCNFFormula Y := by
      refine List.mem_ofFn.mpr ⟨i₀, ?_⟩
      simp [v13RealLinearCNFDecodedAssignment, hmsg]
    simp [v13RealLinearGaugeCNFFormulaPositiveTargetTag, hmem, hmsg]
  · have hfalse : v13RealLinearMessageOfPublic i₀ Y = false :=
      Bool.eq_false_iff.mpr hmsg
    have hnot :
        ConcreteCNF.unitClause (some i₀) true ∉
          v13RealLinearGaugeCNFFormula Y := by
      intro hmem
      rcases List.mem_ofFn.mp hmem with ⟨j, hEq⟩
      have hparts := ConcreteCNF.unitClause_eq_unitClause_iff.mp hEq
      have hj : j = i₀ := Option.some.inj hparts.1
      have hval : v13RealLinearCNFDecodedAssignment Y j = true := hparts.2
      subst i₀
      simp [v13RealLinearCNFDecodedAssignment, hfalse] at hval
    simp [v13RealLinearGaugeCNFFormulaPositiveTargetTag, hnot, hfalse]

/-- Formula-syntax-only message determination for the gauge-buffered real
linear CNF. -/
theorem v13RealLinearGaugeCNFFormula_publicSyntaxDeterminesMessage
    {m : Nat} (i₀ : Fin m) :
    ∃ f : ConcreteCNF.Formula (V13RealLinearGaugeCNFVar m) -> Bool,
      ∀ Y : V13RealLinearPublic m,
        v13RealLinearMessageOfPublic i₀ Y =
          f (v13RealLinearGaugeCNFFormula Y) := by
  exact
    ⟨v13RealLinearGaugeCNFFormulaPositiveTargetTag i₀,
      fun Y =>
        (v13RealLinearGaugeCNFFormulaPositiveTargetTag_eq_publicMessage
          i₀ Y).symm⟩

/-- No-public-target-tags shape for the full gauge-buffered CNF formula syntax
viewed as the public skeleton. -/
def V13RealLinearGaugeCNFFormulaNoPublicTargetTags {m : Nat}
    (i₀ : Fin m) : Prop :=
  ¬ ∃ f : ConcreteCNF.Formula (V13RealLinearGaugeCNFVar m) -> Bool,
      ∀ Y : V13RealLinearPublic m,
        v13RealLinearMessageOfPublic i₀ Y =
          f (v13RealLinearGaugeCNFFormula Y)

/-- Named obstruction: the gauge-buffered CNF still exposes the target message
through the public target-coordinate unit clause when the full formula syntax
is used as the public skeleton.  The transferred `noPublicTargetTags` theorem
therefore has to use the no-target-rows neutral skeleton instead. -/
theorem v13RealLinearGaugeCNFFormula_noPublicTargetTags_obstruction
    {m : Nat} (i₀ : Fin m) :
    ¬ V13RealLinearGaugeCNFFormulaNoPublicTargetTags i₀ := by
  intro hNoTags
  exact hNoTags
    (v13RealLinearGaugeCNFFormula_publicSyntaxDeterminesMessage i₀)

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

/-! ## Concrete small real-linear gauge-CNF instance -/

/-- The selected message coordinate in the concrete two-coordinate real-linear
gauge-CNF instance. -/
def v13RealLinearSmallGaugeCNFMessageIndex : Fin 2 :=
  0

/-- The spare locked coordinate in the concrete two-coordinate real-linear
gauge-CNF instance. -/
def v13RealLinearSmallGaugeCNFSpareIndex : Fin 2 :=
  1

/-- Two-coordinate public right-hand side: the selected coordinate stores the
message bit and the spare coordinate is fixed to zero. -/
def v13RealLinearSmallGaugeCNFRhs (msg : Bool) : F2Vec 2 :=
  fun j =>
    if j = v13RealLinearSmallGaugeCNFMessageIndex then
      if msg then (1 : ZMod 2) else 0
    else
      0

/-- Concrete public instance in the real linear family: identity map with the
chosen two-coordinate right-hand side. -/
def v13RealLinearSmallGaugeCNFPublic (msg : Bool) :
    V13RealLinearPublic 2 where
  A := v13RealLinearIdentity 2
  b := v13RealLinearSmallGaugeCNFRhs msg

/-- The real public decoder reads back the selected message bit of the small
instance. -/
theorem v13RealLinearSmallGaugeCNFPublic_message
    (msg : Bool) :
    v13RealLinearMessageOfPublic
      v13RealLinearSmallGaugeCNFMessageIndex
      (v13RealLinearSmallGaugeCNFPublic msg) = msg := by
  cases msg <;>
    simp [v13RealLinearMessageOfPublic, v13RealLinearBit,
      v13RealLinearSmallGaugeCNFPublic, v13RealLinearSmallGaugeCNFRhs,
      v13RealLinearSmallGaugeCNFMessageIndex, v13RealLinearIdentity]

/-- Variables of the concrete small gauge-CNF instance: two locked coordinates
plus the free hidden gauge coordinate `none`. -/
abbrev V13RealLinearSmallGaugeCNFVar :=
  V13RealLinearGaugeCNFVar 2

/-- Witness assignments for the concrete small gauge-CNF instance. -/
abbrev V13RealLinearSmallGaugeCNFWitness :=
  V13RealLinearGaugeCNFWitness 2

/-- The concrete two-clause CNF: lock the selected coordinate to `msg`, lock
the spare coordinate to `false`, and leave `none` as hidden gauge state. -/
def v13RealLinearSmallGaugeCNFFormula
    (msg : Bool) : ConcreteCNF.Formula V13RealLinearSmallGaugeCNFVar :=
  [ConcreteCNF.unitClause
      (some v13RealLinearSmallGaugeCNFMessageIndex) msg,
    ConcreteCNF.unitClause
      (some v13RealLinearSmallGaugeCNFSpareIndex) false]

/-- The explicit two-clause formula is exactly the generic real-linear
gauge-CNF formula at the corresponding concrete public instance. -/
theorem v13RealLinearSmallGaugeCNFFormula_eq_realGaugeCNFFormula
    (msg : Bool) :
    v13RealLinearSmallGaugeCNFFormula msg =
      v13RealLinearGaugeCNFFormula
        (v13RealLinearSmallGaugeCNFPublic msg) := by
  cases msg <;>
    simp [v13RealLinearSmallGaugeCNFFormula,
      v13RealLinearGaugeCNFFormula, v13RealLinearCNFDecodedAssignment,
      v13RealLinearMessageOfPublic, v13RealLinearBit,
      v13RealLinearSmallGaugeCNFPublic, v13RealLinearSmallGaugeCNFRhs,
      v13RealLinearSmallGaugeCNFMessageIndex,
      v13RealLinearSmallGaugeCNFSpareIndex, v13RealLinearIdentity]

/-- Public message readout `M(Y)` for the explicit small instance. -/
def v13RealLinearSmallGaugeCNFMessage (msg : Bool) : Bool :=
  msg

/-- Public formula-syntax tag for the explicit small CNF: whether the public
formula contains the positive unit clause for the locked message coordinate. -/
def v13RealLinearSmallGaugeCNFFormulaPositiveTargetTag
    (formula : ConcreteCNF.Formula V13RealLinearSmallGaugeCNFVar) : Bool :=
  decide
    (ConcreteCNF.unitClause
        (some v13RealLinearSmallGaugeCNFMessageIndex) true ∈ formula)

/-- In the explicit small CNF, the public formula-syntax target tag is exactly
the message bit. -/
theorem v13RealLinearSmallGaugeCNFFormulaPositiveTargetTag_eq_message
    (msg : Bool) :
    v13RealLinearSmallGaugeCNFFormulaPositiveTargetTag
        (v13RealLinearSmallGaugeCNFFormula msg) =
      msg := by
  cases msg <;>
    simp [v13RealLinearSmallGaugeCNFFormulaPositiveTargetTag,
      v13RealLinearSmallGaugeCNFFormula,
      v13RealLinearSmallGaugeCNFMessageIndex,
      v13RealLinearSmallGaugeCNFSpareIndex,
      ConcreteCNF.unitClause, ConcreteCNF.unitLiteral]

/-- Formula-syntax-only message determination for the explicit small
gauge-CNF. -/
theorem v13RealLinearSmallGaugeCNFFormula_publicSyntaxDeterminesMessage :
    ∃ f : ConcreteCNF.Formula V13RealLinearSmallGaugeCNFVar -> Bool,
      ∀ msg : Bool,
        v13RealLinearSmallGaugeCNFMessage msg =
          f (v13RealLinearSmallGaugeCNFFormula msg) := by
  exact
    ⟨v13RealLinearSmallGaugeCNFFormulaPositiveTargetTag,
      fun msg =>
        (v13RealLinearSmallGaugeCNFFormulaPositiveTargetTag_eq_message
          msg).symm⟩

/-- No-public-target-tags shape for the explicit small CNF when the full
public formula syntax is taken as the public skeleton. -/
def V13RealLinearSmallGaugeCNFFormulaNoPublicTargetTags : Prop :=
  ¬ ∃ f : ConcreteCNF.Formula V13RealLinearSmallGaugeCNFVar -> Bool,
      ∀ msg : Bool,
        v13RealLinearSmallGaugeCNFMessage msg =
          f (v13RealLinearSmallGaugeCNFFormula msg)

/-- Named obstruction: the explicit small CNF is single-message and has a
hidden gauge coordinate, but its full public formula syntax still exposes the
message through the target unit clause.  Therefore this concrete syntax cannot
provide `noPublicTargetTags` unless the public skeleton is restricted away from
the target row. -/
theorem v13RealLinearSmallGaugeCNFFormula_noPublicTargetTags_obstruction :
    ¬ V13RealLinearSmallGaugeCNFFormulaNoPublicTargetTags := by
  intro hNoTags
  exact hNoTags
    v13RealLinearSmallGaugeCNFFormula_publicSyntaxDeterminesMessage

/-- Semantic verifier for the explicit small gauge-CNF instance. -/
def v13RealLinearSmallGaugeCNFVerifier
    (msg : Bool) (W : V13RealLinearSmallGaugeCNFWitness) : Prop :=
  ConcreteCNF.IsSatFormula (v13RealLinearSmallGaugeCNFFormula msg) W

/-- Executable verifier for the explicit small gauge-CNF instance. -/
def v13RealLinearSmallGaugeCNFVerifierDecision
    (msg : Bool) (W : V13RealLinearSmallGaugeCNFWitness) : Bool :=
  decide
    (W (some v13RealLinearSmallGaugeCNFMessageIndex) = msg ∧
      W (some v13RealLinearSmallGaugeCNFSpareIndex) = false)

/-- Satisfaction of the explicit two-clause CNF is exactly the two locked
coordinate equalities. -/
theorem v13RealLinearSmallGaugeCNFFormula_sat_iff
    {msg : Bool} {W : V13RealLinearSmallGaugeCNFWitness} :
    v13RealLinearSmallGaugeCNFVerifier msg W ↔
      W (some v13RealLinearSmallGaugeCNFMessageIndex) = msg ∧
        W (some v13RealLinearSmallGaugeCNFSpareIndex) = false := by
  constructor
  · intro hW
    constructor
    · have hclause :
          ConcreteCNF.IsSatClause
            (ConcreteCNF.unitClause
              (some v13RealLinearSmallGaugeCNFMessageIndex) msg) W := by
        exact hW _ (by simp [v13RealLinearSmallGaugeCNFFormula])
      exact
        (ConcreteCNF.isSatClause_unitClause_iff W
          (some v13RealLinearSmallGaugeCNFMessageIndex) msg).mp hclause
    · have hclause :
          ConcreteCNF.IsSatClause
            (ConcreteCNF.unitClause
              (some v13RealLinearSmallGaugeCNFSpareIndex) false) W := by
        exact hW _ (by simp [v13RealLinearSmallGaugeCNFFormula])
      exact
        (ConcreteCNF.isSatClause_unitClause_iff W
          (some v13RealLinearSmallGaugeCNFSpareIndex) false).mp hclause
  · intro hLocked clause hclause
    simp [v13RealLinearSmallGaugeCNFFormula] at hclause
    rcases hclause with hclause | hclause
    · rw [hclause]
      exact
        (ConcreteCNF.isSatClause_unitClause_iff W
          (some v13RealLinearSmallGaugeCNFMessageIndex) msg).mpr
          hLocked.1
    · rw [hclause]
      exact
        (ConcreteCNF.isSatClause_unitClause_iff W
          (some v13RealLinearSmallGaugeCNFSpareIndex) false).mpr
          hLocked.2

/-- The executable verifier decides the semantic verifier. -/
theorem v13RealLinearSmallGaugeCNFVerifierDecision_correct
    {msg : Bool} {W : V13RealLinearSmallGaugeCNFWitness} :
    v13RealLinearSmallGaugeCNFVerifierDecision msg W = true ↔
      v13RealLinearSmallGaugeCNFVerifier msg W := by
  rw [v13RealLinearSmallGaugeCNFVerifierDecision, decide_eq_true_iff]
  exact v13RealLinearSmallGaugeCNFFormula_sat_iff.symm

/-- Canonical satisfying assignment with an arbitrary hidden gauge bit. -/
def v13RealLinearSmallGaugeCNFAssignment
    (msg gauge : Bool) : V13RealLinearSmallGaugeCNFWitness
  | some j =>
      if j = v13RealLinearSmallGaugeCNFMessageIndex then
        msg
      else
        false
  | none => gauge

@[simp] theorem v13RealLinearSmallGaugeCNFAssignment_message
    (msg gauge : Bool) :
    v13RealLinearSmallGaugeCNFAssignment msg gauge
        (some v13RealLinearSmallGaugeCNFMessageIndex) = msg := by
  simp [v13RealLinearSmallGaugeCNFAssignment]

@[simp] theorem v13RealLinearSmallGaugeCNFAssignment_spare
    (msg gauge : Bool) :
    v13RealLinearSmallGaugeCNFAssignment msg gauge
        (some v13RealLinearSmallGaugeCNFSpareIndex) = false := by
  simp [v13RealLinearSmallGaugeCNFAssignment,
    v13RealLinearSmallGaugeCNFMessageIndex,
    v13RealLinearSmallGaugeCNFSpareIndex]

@[simp] theorem v13RealLinearSmallGaugeCNFAssignment_hiddenGauge
    (msg gauge : Bool) :
    v13RealLinearSmallGaugeCNFAssignment msg gauge none = gauge :=
  rfl

/-- The canonical assignment satisfies the explicit small CNF for either
hidden gauge bit. -/
theorem v13RealLinearSmallGaugeCNFFormula_satisfied_assignment
    (msg gauge : Bool) :
    v13RealLinearSmallGaugeCNFVerifier msg
      (v13RealLinearSmallGaugeCNFAssignment msg gauge) := by
  exact v13RealLinearSmallGaugeCNFFormula_sat_iff.mpr
    ⟨v13RealLinearSmallGaugeCNFAssignment_message msg gauge,
      v13RealLinearSmallGaugeCNFAssignment_spare msg gauge⟩

/-- Fixed readout for the explicit small CNF: read the selected locked
coordinate. -/
def v13RealLinearSmallGaugeCNFReadout
    (W : V13RealLinearSmallGaugeCNFWitness) : Bool :=
  W (some v13RealLinearSmallGaugeCNFMessageIndex)

/-- Any verifier-valid witness for the small concrete CNF reads the public
message. -/
theorem v13RealLinearSmallGaugeCNFReadout_eq_message_of_valid
    {msg : Bool} {W : V13RealLinearSmallGaugeCNFWitness}
    (hW : v13RealLinearSmallGaugeCNFVerifier msg W) :
    v13RealLinearSmallGaugeCNFReadout W =
      v13RealLinearSmallGaugeCNFMessage msg :=
  (v13RealLinearSmallGaugeCNFFormula_sat_iff.mp hW).1

/-- The explicit small real-linear gauge-CNF instance is single-message:
hidden gauge assignments may vary, but all satisfying witnesses have the same
readout. -/
theorem v13RealLinearSmallGaugeCNF_singleMessage
    (msg : Bool) :
    SingleMessageReadout
      (v13RealLinearSmallGaugeCNFVerifier msg)
      v13RealLinearSmallGaugeCNFReadout := by
  intro W W' hW hW'
  calc
    v13RealLinearSmallGaugeCNFReadout W =
        v13RealLinearSmallGaugeCNFMessage msg :=
      v13RealLinearSmallGaugeCNFReadout_eq_message_of_valid hW
    _ = v13RealLinearSmallGaugeCNFReadout W' :=
      (v13RealLinearSmallGaugeCNFReadout_eq_message_of_valid hW').symm

/-! ## Global small real-linear gauge-CNF SAT-world surface -/

/-- Global SAT worlds for the explicit small real-linear gauge-CNF ensemble:
the public message bit varies, and the witness is any verifier-valid
satisfying assignment, not just the canonical representative. -/
structure V13RealLinearSmallGaugeCNFSATWorld where
  msg : Bool
  assignment : V13RealLinearSmallGaugeCNFWitness
  sat : v13RealLinearSmallGaugeCNFVerifier msg assignment

/-- Public input for the global SAT-world surface: the concrete public
message bit selecting the small CNF instance. -/
def v13RealLinearSmallGaugeCNFSATWorldPublicInput
    (omega : V13RealLinearSmallGaugeCNFSATWorld) : Bool :=
  omega.msg

/-- Target readout on global SAT worlds, computed from the carried satisfying
witness. -/
def v13RealLinearSmallGaugeCNFSATWorldTarget
    (omega : V13RealLinearSmallGaugeCNFSATWorld) : Bool :=
  v13RealLinearSmallGaugeCNFReadout omega.assignment

/-- Every global SAT world reads the fixed public message of its CNF
instance. -/
theorem v13RealLinearSmallGaugeCNFSATWorldTarget_eq_message
    (omega : V13RealLinearSmallGaugeCNFSATWorld) :
    v13RealLinearSmallGaugeCNFSATWorldTarget omega =
      v13RealLinearSmallGaugeCNFMessage omega.msg :=
  v13RealLinearSmallGaugeCNFReadout_eq_message_of_valid omega.sat

/-- Structural `singleMessage` transfer for the global SAT-world surface:
inside one public small CNF instance, all verifier-valid satisfying witnesses
have the same fixed message readout. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_singleMessage :
    ∀ omega₀ omega₁ : V13RealLinearSmallGaugeCNFSATWorld,
      v13RealLinearSmallGaugeCNFSATWorldPublicInput omega₀ =
        v13RealLinearSmallGaugeCNFSATWorldPublicInput omega₁ ->
        v13RealLinearSmallGaugeCNFSATWorldTarget omega₀ =
          v13RealLinearSmallGaugeCNFSATWorldTarget omega₁ := by
  intro omega₀ omega₁ hPublic
  rw [v13RealLinearSmallGaugeCNFSATWorldTarget_eq_message omega₀,
    v13RealLinearSmallGaugeCNFSATWorldTarget_eq_message omega₁]
  exact congrArg v13RealLinearSmallGaugeCNFMessage hPublic

/-- Target-blind neutral skeleton for global SAT worlds: retain the hidden
gauge bit carried by the satisfying witness and omit the public message. -/
def v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
    (omega : V13RealLinearSmallGaugeCNFSATWorld) : Bool :=
  omega.assignment none

/-- Opposite support for SAT worlds pairs verifier-valid worlds with opposite
public messages but the same hidden gauge bit. -/
def v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
    (omega₀ omega₁ : V13RealLinearSmallGaugeCNFSATWorld) : Prop :=
  v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton omega₀ =
      v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton omega₁ ∧
    omega₀.msg = false ∧ omega₁.msg = true

/-- The hidden-gauge neutral skeleton is pair-neutral across supported
opposite-message SAT-world pairs. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_pairNeutral :
    PairNeutral
      v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
      v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton := by
  intro omega₀ omega₁ hSupport
  exact hSupport.1

/-- The SAT-world surface has an explicit opposite-message pair in the same
hidden-gauge fiber. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_hasMessageOppositePair :
    HasMessageOppositePair
      v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
      v13RealLinearSmallGaugeCNFSATWorldTarget := by
  let omegaFalse : V13RealLinearSmallGaugeCNFSATWorld :=
    { msg := false
      assignment := v13RealLinearSmallGaugeCNFAssignment false false
      sat := v13RealLinearSmallGaugeCNFFormula_satisfied_assignment
        false false }
  let omegaTrue : V13RealLinearSmallGaugeCNFSATWorld :=
    { msg := true
      assignment := v13RealLinearSmallGaugeCNFAssignment true false
      sat := v13RealLinearSmallGaugeCNFFormula_satisfied_assignment
        true false }
  refine ⟨omegaFalse, omegaTrue, ?_, ?_, ?_⟩
  · simp [omegaFalse, omegaTrue,
      v13RealLinearSmallGaugeCNFSATWorldOppositeSupport,
      v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton,
      v13RealLinearSmallGaugeCNFAssignment]
  · simp [omegaFalse, v13RealLinearSmallGaugeCNFSATWorldTarget,
      v13RealLinearSmallGaugeCNFReadout,
      v13RealLinearSmallGaugeCNFAssignment]
  · simp [omegaTrue, v13RealLinearSmallGaugeCNFSATWorldTarget,
      v13RealLinearSmallGaugeCNFReadout,
      v13RealLinearSmallGaugeCNFAssignment]

/-- Structural `noPublicTargetTags` transfer for global SAT worlds: the hidden
gauge skeleton is target-blind, yet the surface contains same-skeleton worlds
with opposite fixed message readouts. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_noPublicTargetTags :
    PairNeutral
        v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton ∧
      HasMessageOppositePair
        v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
        v13RealLinearSmallGaugeCNFSATWorldTarget ∧
        ¬ ∃ f : Bool -> Bool,
          ∀ omega : V13RealLinearSmallGaugeCNFSATWorld,
            v13RealLinearSmallGaugeCNFSATWorldTarget omega =
              f (v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton omega) := by
  have hPair :
      PairNeutral
        v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton :=
    v13RealLinearSmallGaugeCNFSATWorld_pairNeutral
  have hOpp :
      HasMessageOppositePair
        v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
        v13RealLinearSmallGaugeCNFSATWorldTarget :=
    v13RealLinearSmallGaugeCNFSATWorld_hasMessageOppositePair
  exact
    ⟨hPair, hOpp,
      neutralSkeleton_not_sufficient
        v13RealLinearSmallGaugeCNFSATWorldOppositeSupport
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
        v13RealLinearSmallGaugeCNFSATWorldTarget
        hPair hOpp⟩

/-- Canonical SAT world with a chosen public message and hidden gauge bit. -/
def v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge
    (msg gauge : Bool) : V13RealLinearSmallGaugeCNFSATWorld where
  msg := msg
  assignment := v13RealLinearSmallGaugeCNFAssignment msg gauge
  sat := v13RealLinearSmallGaugeCNFFormula_satisfied_assignment msg gauge

/-- Every verifier-valid SAT world is the canonical world with the same public
message and hidden-gauge coordinate. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_eq_worldOfMessageGauge
    (omega : V13RealLinearSmallGaugeCNFSATWorld) :
    v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge
        omega.msg (omega.assignment none) = omega := by
  cases omega with
  | mk msg assignment sat =>
  simp [v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge]
  funext v
  cases v with
  | none =>
      rfl
  | some j =>
      rcases v13RealLinearSmallGaugeCNFFormula_sat_iff.mp sat with
        ⟨hmsg, hspare⟩
      fin_cases j
      · simpa [v13RealLinearSmallGaugeCNFAssignment,
          v13RealLinearSmallGaugeCNFMessageIndex] using hmsg.symm
      · simpa [v13RealLinearSmallGaugeCNFAssignment,
          v13RealLinearSmallGaugeCNFMessageIndex,
          v13RealLinearSmallGaugeCNFSpareIndex] using hspare.symm

/-- The SAT-world surface is exactly a public message bit together with a
hidden gauge bit. -/
def v13RealLinearSmallGaugeCNFSATWorldEquivBoolProd :
    V13RealLinearSmallGaugeCNFSATWorld ≃ Bool × Bool where
  toFun := fun omega => (omega.msg, omega.assignment none)
  invFun := fun data =>
    v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge data.1 data.2
  left_inv := by
    intro omega
    exact v13RealLinearSmallGaugeCNFSATWorld_eq_worldOfMessageGauge omega
  right_inv := by
    intro data
    cases data
    rfl

instance v13RealLinearSmallGaugeCNFSATWorldFintype :
    Fintype V13RealLinearSmallGaugeCNFSATWorld :=
  Fintype.ofEquiv (Bool × Bool)
    v13RealLinearSmallGaugeCNFSATWorldEquivBoolProd.symm

/-- History field for SAT worlds: observe only the hidden gauge bit, not the
public message bit. -/
def v13RealLinearSmallGaugeCNFSATWorldHistoryField :
    FiniteSigmaField V13RealLinearSmallGaugeCNFSATWorld where
  Atom := Bool
  atomDecidable := inferInstance
  atom := v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton

/-- The global SAT-world surface has four states. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_card :
    Fintype.card V13RealLinearSmallGaugeCNFSATWorld = 4 := by
  calc
    Fintype.card V13RealLinearSmallGaugeCNFSATWorld =
        Fintype.card (Bool × Bool) :=
      Fintype.card_congr
        v13RealLinearSmallGaugeCNFSATWorldEquivBoolProd
    _ = 4 := by
      norm_num

/-- Target-true SAT worlds are exactly the two hidden gauge choices over the
true public message. -/
def v13RealLinearSmallGaugeCNFSATWorldTargetTrueEquivGauge :
    {omega : V13RealLinearSmallGaugeCNFSATWorld //
      v13RealLinearSmallGaugeCNFSATWorldTarget omega = true} ≃ Bool where
  toFun := fun omega =>
    v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton omega.val
  invFun := fun gauge =>
    ⟨v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge true gauge, by
      simp [v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge,
        v13RealLinearSmallGaugeCNFSATWorldTarget,
        v13RealLinearSmallGaugeCNFReadout,
        v13RealLinearSmallGaugeCNFAssignment]⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    have hmsg : omega.val.msg = true := by
      have htarget :=
        v13RealLinearSmallGaugeCNFSATWorldTarget_eq_message omega.val
      rw [omega.property] at htarget
      simpa [v13RealLinearSmallGaugeCNFMessage] using htarget.symm
    calc
      v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge true
          (v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton omega.val) =
          v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge
            omega.val.msg (omega.val.assignment none) := by
            simp [v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton, hmsg]
      _ = omega.val :=
          v13RealLinearSmallGaugeCNFSATWorld_eq_worldOfMessageGauge omega.val
  right_inv := by
    intro gauge
    rfl

/-- Correct SAT worlds for the constant-true decoder are target-true worlds. -/
def v13RealLinearSmallGaugeCNFSATWorldCorrectTrueEquivTargetTrue :
    {omega : V13RealLinearSmallGaugeCNFSATWorld //
      (fun _ : V13RealLinearSmallGaugeCNFSATWorld => true) omega =
        v13RealLinearSmallGaugeCNFSATWorldTarget omega} ≃
      {omega : V13RealLinearSmallGaugeCNFSATWorld //
        v13RealLinearSmallGaugeCNFSATWorldTarget omega = true} where
  toFun := fun omega => ⟨omega.val, omega.property.symm⟩
  invFun := fun omega => ⟨omega.val, omega.property.symm⟩
  left_inv := by
    intro omega
    cases omega
    rfl
  right_inv := by
    intro omega
    cases omega
    rfl

/-- There are two target-true SAT worlds. -/
theorem v13RealLinearSmallGaugeCNFSATWorldTarget_true_card :
    Fintype.card
        {omega : V13RealLinearSmallGaugeCNFSATWorld //
          v13RealLinearSmallGaugeCNFSATWorldTarget omega = true} = 2 := by
  calc
    Fintype.card
        {omega : V13RealLinearSmallGaugeCNFSATWorld //
          v13RealLinearSmallGaugeCNFSATWorldTarget omega = true} =
        Fintype.card Bool :=
      Fintype.card_congr
        v13RealLinearSmallGaugeCNFSATWorldTargetTrueEquivGauge
    _ = 2 := by
      norm_num

/-- The SAT-world target is balanced across the two public message bits and
the two hidden gauge states. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_target_balanced :
    BalancedBit v13RealLinearSmallGaugeCNFSATWorldTarget := by
  unfold BalancedBit globalDecoderSuccess
  rw [Fintype.card_congr
    v13RealLinearSmallGaugeCNFSATWorldCorrectTrueEquivTargetTrue,
    v13RealLinearSmallGaugeCNFSATWorldTarget_true_card,
    v13RealLinearSmallGaugeCNFSATWorld_card]
  norm_num

/-- In a fixed hidden-gauge fiber, the target-true SAT world is unique. -/
def v13RealLinearSmallGaugeCNFSATWorldFiberTrueEquivUnit
    (gauge : Bool) :
    FiberTrue
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
        v13RealLinearSmallGaugeCNFSATWorldTarget gauge ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    ⟨v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge true gauge, by
      simp [v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge,
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton,
        v13RealLinearSmallGaugeCNFSATWorldTarget,
        v13RealLinearSmallGaugeCNFReadout,
        v13RealLinearSmallGaugeCNFAssignment]⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    rcases omega.property with ⟨hgauge, htarget⟩
    have hmsg : omega.val.msg = true := by
      have htargetMsg :=
        v13RealLinearSmallGaugeCNFSATWorldTarget_eq_message omega.val
      rw [htarget] at htargetMsg
      simpa [v13RealLinearSmallGaugeCNFMessage] using htargetMsg.symm
    have hgauge' : gauge = omega.val.assignment none := by
      simpa [v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton] using hgauge.symm
    calc
      v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge true gauge =
          v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge
            omega.val.msg (omega.val.assignment none) := by
            simp [hmsg, hgauge']
      _ = omega.val :=
          v13RealLinearSmallGaugeCNFSATWorld_eq_worldOfMessageGauge omega.val
  right_inv := by
    intro unitValue
    cases unitValue
    rfl

/-- In a fixed hidden-gauge fiber, the target-false SAT world is unique. -/
def v13RealLinearSmallGaugeCNFSATWorldFiberFalseEquivUnit
    (gauge : Bool) :
    FiberFalse
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
        v13RealLinearSmallGaugeCNFSATWorldTarget gauge ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    ⟨v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge false gauge, by
      simp [v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge,
        v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton,
        v13RealLinearSmallGaugeCNFSATWorldTarget,
        v13RealLinearSmallGaugeCNFReadout,
        v13RealLinearSmallGaugeCNFAssignment]⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    rcases omega.property with ⟨hgauge, htarget⟩
    have hmsg : omega.val.msg = false := by
      have htargetMsg :=
        v13RealLinearSmallGaugeCNFSATWorldTarget_eq_message omega.val
      rw [htarget] at htargetMsg
      simpa [v13RealLinearSmallGaugeCNFMessage] using htargetMsg.symm
    have hgauge' : gauge = omega.val.assignment none := by
      simpa [v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton] using hgauge.symm
    calc
      v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge false gauge =
          v13RealLinearSmallGaugeCNFSATWorldOfMessageGauge
            omega.val.msg (omega.val.assignment none) := by
            simp [hmsg, hgauge']
      _ = omega.val :=
          v13RealLinearSmallGaugeCNFSATWorld_eq_worldOfMessageGauge omega.val
  right_inv := by
    intro unitValue
    cases unitValue
    rfl

/-- The hidden-gauge SAT-world history field is balanced: conditioning on
either hidden-gauge value leaves one false-message and one true-message world. -/
theorem
    v13RealLinearSmallGaugeCNFSATWorld_historyField_balancedConditioning :
    BalancedConditioning
      v13RealLinearSmallGaugeCNFSATWorldHistoryField
      v13RealLinearSmallGaugeCNFSATWorldTarget := by
  change Neutral
    v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
    v13RealLinearSmallGaugeCNFSATWorldTarget
  intro gauge
  calc
    Fintype.card
        (FiberTrue
          v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
          v13RealLinearSmallGaugeCNFSATWorldTarget gauge) =
        Fintype.card Unit :=
      Fintype.card_congr
        (v13RealLinearSmallGaugeCNFSATWorldFiberTrueEquivUnit gauge)
    _ = Fintype.card Unit := rfl
    _ =
        Fintype.card
          (FiberFalse
            v13RealLinearSmallGaugeCNFSATWorldNeutralSkeleton
            v13RealLinearSmallGaugeCNFSATWorldTarget gauge) :=
      (Fintype.card_congr
        (v13RealLinearSmallGaugeCNFSATWorldFiberFalseEquivUnit gauge)).symm

/-- Structural `admissibleHistories` transfer for global SAT worlds.  The
surface over both public message bits is balanced, and the hidden-gauge history
field is target-neutral. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_admissibleHistories :
    BalancedBit v13RealLinearSmallGaugeCNFSATWorldTarget ∧
      BalancedConditioning
        v13RealLinearSmallGaugeCNFSATWorldHistoryField
        v13RealLinearSmallGaugeCNFSATWorldTarget :=
  ⟨v13RealLinearSmallGaugeCNFSATWorld_target_balanced,
    v13RealLinearSmallGaugeCNFSATWorld_historyField_balancedConditioning⟩

/-- Hidden gauge readout for the explicit small real-linear gauge-CNF
instance. -/
def v13RealLinearSmallGaugeCNFHiddenGauge
    (W : V13RealLinearSmallGaugeCNFWitness) : Bool :=
  W none

/-- The explicit small instance uses the same hidden-gauge flip as the general
real-linear gauge-CNF family. -/
def v13RealLinearSmallGaugeCNFGaugeAction
    (gamma : Bool) (W : V13RealLinearSmallGaugeCNFWitness) :
    V13RealLinearSmallGaugeCNFWitness :=
  v13RealLinearGaugeCNFGaugeAction gamma W

/-- The hidden-gauge action preserves the two locked clauses of the explicit
small CNF. -/
theorem v13RealLinearSmallGaugeCNFGaugeAction_preserves_verifier
    (gamma : Bool) {msg : Bool} {W : V13RealLinearSmallGaugeCNFWitness}
    (hW : v13RealLinearSmallGaugeCNFVerifier msg W) :
    v13RealLinearSmallGaugeCNFVerifier msg
      (v13RealLinearSmallGaugeCNFGaugeAction gamma W) := by
  rcases v13RealLinearSmallGaugeCNFFormula_sat_iff.mp hW with
    ⟨hmsg, hspare⟩
  exact v13RealLinearSmallGaugeCNFFormula_sat_iff.mpr
    ⟨by
      simpa [v13RealLinearSmallGaugeCNFGaugeAction] using hmsg,
     by
      simpa [v13RealLinearSmallGaugeCNFGaugeAction] using hspare⟩

/-- The hidden-gauge action preserves the fixed message readout. -/
theorem v13RealLinearSmallGaugeCNFGaugeAction_preserves_readout
    (gamma : Bool) (W : V13RealLinearSmallGaugeCNFWitness) :
    v13RealLinearSmallGaugeCNFReadout
        (v13RealLinearSmallGaugeCNFGaugeAction gamma W) =
      v13RealLinearSmallGaugeCNFReadout W :=
  rfl

/-- Acting by `true` flips the hidden gauge coordinate. -/
theorem v13RealLinearSmallGaugeCNFGaugeAction_hidden_true
    (W : V13RealLinearSmallGaugeCNFWitness) :
    v13RealLinearSmallGaugeCNFHiddenGauge
        (v13RealLinearSmallGaugeCNFGaugeAction true W) =
      !v13RealLinearSmallGaugeCNFHiddenGauge W :=
  rfl

/-- The hidden-gauge action is nontrivial on satisfying witnesses for either
public message bit. -/
theorem v13RealLinearSmallGaugeCNFGaugeAction_nontrivial
    (msg : Bool) :
    ∃ W : V13RealLinearSmallGaugeCNFWitness,
      v13RealLinearSmallGaugeCNFVerifier msg W ∧
        v13RealLinearSmallGaugeCNFGaugeAction true W ≠ W := by
  let W := v13RealLinearSmallGaugeCNFAssignment msg false
  refine
    ⟨W, v13RealLinearSmallGaugeCNFFormula_satisfied_assignment msg false,
      ?_⟩
  intro hfixed
  have hcoord := congrFun hfixed none
  simp [W, v13RealLinearSmallGaugeCNFGaugeAction,
    v13RealLinearGaugeCNFGaugeAction] at hcoord

/-- A valid world for the explicit small real-linear gauge-CNF instance is a
satisfying assignment for the chosen public message bit. -/
structure V13RealLinearSmallGaugeCNFWorld (msg : Bool) where
  assignment : V13RealLinearSmallGaugeCNFWitness
  sat : v13RealLinearSmallGaugeCNFVerifier msg assignment

/-- Canonical valid world with a chosen hidden gauge bit. -/
def v13RealLinearSmallGaugeCNFWorldOfGauge
    (msg gauge : Bool) : V13RealLinearSmallGaugeCNFWorld msg where
  assignment := v13RealLinearSmallGaugeCNFAssignment msg gauge
  sat := v13RealLinearSmallGaugeCNFFormula_satisfied_assignment msg gauge

/-- Target readout on valid small gauge-CNF worlds. -/
def v13RealLinearSmallGaugeCNFTarget {msg : Bool}
    (omega : V13RealLinearSmallGaugeCNFWorld msg) : Bool :=
  v13RealLinearSmallGaugeCNFReadout omega.assignment

/-- Hidden gauge readout on valid small gauge-CNF worlds. -/
def v13RealLinearSmallGaugeCNFWorldHiddenGauge {msg : Bool}
    (omega : V13RealLinearSmallGaugeCNFWorld msg) : Bool :=
  v13RealLinearSmallGaugeCNFHiddenGauge omega.assignment

/-- Hidden-gauge action on valid small gauge-CNF worlds. -/
def v13RealLinearSmallGaugeCNFWorldGaugeAction {msg : Bool}
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFWorld msg) :
    V13RealLinearSmallGaugeCNFWorld msg where
  assignment := v13RealLinearSmallGaugeCNFGaugeAction gamma omega.assignment
  sat := v13RealLinearSmallGaugeCNFGaugeAction_preserves_verifier
    gamma omega.sat

/-- The world-level hidden-gauge action preserves target readout. -/
theorem v13RealLinearSmallGaugeCNFWorldGaugeAction_preserves_target
    {msg : Bool} (gamma : Bool)
    (omega : V13RealLinearSmallGaugeCNFWorld msg) :
    v13RealLinearSmallGaugeCNFTarget
        (v13RealLinearSmallGaugeCNFWorldGaugeAction gamma omega) =
      v13RealLinearSmallGaugeCNFTarget omega :=
  v13RealLinearSmallGaugeCNFGaugeAction_preserves_readout
    gamma omega.assignment

/-- Acting by `true` flips the world-level hidden gauge coordinate. -/
theorem v13RealLinearSmallGaugeCNFWorldGaugeAction_hidden_true
    {msg : Bool} (omega : V13RealLinearSmallGaugeCNFWorld msg) :
    v13RealLinearSmallGaugeCNFWorldHiddenGauge
        (v13RealLinearSmallGaugeCNFWorldGaugeAction true omega) =
      !v13RealLinearSmallGaugeCNFWorldHiddenGauge omega :=
  rfl

/-- Neutral evidence atoms for the explicit small gauge-CNF surface. -/
abbrev V13RealLinearSmallGaugeCNFNeutral :=
  Unit

/-- Safe evidence atoms for the explicit small gauge-CNF surface. -/
abbrev V13RealLinearSmallGaugeCNFSafe :=
  Unit

/-- The concrete gauge family is the Boolean hidden-gauge flip. -/
abbrev V13RealLinearSmallGaugeCNFGauge :=
  Bool

/-! ## Global small real-linear gauge-CNF SAT-world hidden-gauge product -/

/-- Hidden-gauge action on global SAT worlds: preserve the public small CNF
instance and apply the concrete verifier-preserving hidden-gauge flip to the
carried satisfying witness. -/
def v13RealLinearSmallGaugeCNFSATWorldGaugeAction
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFSATWorld) :
    V13RealLinearSmallGaugeCNFSATWorld where
  msg := omega.msg
  assignment := v13RealLinearSmallGaugeCNFGaugeAction gamma omega.assignment
  sat := v13RealLinearSmallGaugeCNFGaugeAction_preserves_verifier
    gamma omega.sat

/-- The SAT-world hidden-gauge action preserves the public CNF instance. -/
theorem v13RealLinearSmallGaugeCNFSATWorldGaugeAction_publicInput
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFSATWorld) :
    v13RealLinearSmallGaugeCNFSATWorldPublicInput
        (v13RealLinearSmallGaugeCNFSATWorldGaugeAction gamma omega) =
      v13RealLinearSmallGaugeCNFSATWorldPublicInput omega :=
  rfl

/-- The SAT-world hidden-gauge action preserves the message readout. -/
theorem v13RealLinearSmallGaugeCNFSATWorldGaugeAction_preserves_target
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFSATWorld) :
    v13RealLinearSmallGaugeCNFSATWorldTarget
        (v13RealLinearSmallGaugeCNFSATWorldGaugeAction gamma omega) =
      v13RealLinearSmallGaugeCNFSATWorldTarget omega :=
  v13RealLinearSmallGaugeCNFGaugeAction_preserves_readout
    gamma omega.assignment

/-- Gauge satisfaction for the SAT-world surface is target preservation under
the concrete hidden-gauge action on satisfying witnesses. -/
def v13RealLinearSmallGaugeCNFSATWorldGaugeSat
    (gamma : V13RealLinearSmallGaugeCNFGauge)
    (omega : V13RealLinearSmallGaugeCNFSATWorld) : Prop :=
  v13RealLinearSmallGaugeCNFSATWorldTarget
      (v13RealLinearSmallGaugeCNFSATWorldGaugeAction gamma omega) =
    v13RealLinearSmallGaugeCNFSATWorldTarget omega

/-- Evidence semantics for the global small real-linear gauge-CNF SAT-world
surface. -/
def v13RealLinearSmallGaugeCNFSATWorldSemantics :
    EvidenceSemantics
      V13RealLinearSmallGaugeCNFSATWorld
      V13RealLinearSmallGaugeCNFNeutral
      V13RealLinearSmallGaugeCNFSafe
      V13RealLinearSmallGaugeCNFGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := v13RealLinearSmallGaugeCNFSATWorldGaugeSat

/-- Structural `atomCompleteness` transfer for the global SAT-world small
real-linear gauge-CNF surface: CD-ENF normalization preserves the concrete
SAT-world evidence semantics. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_atomCompleteness :
    ∀ E :
      RawEvidence
        V13RealLinearSmallGaugeCNFNeutral
        V13RealLinearSmallGaugeCNFSafe
        V13RealLinearSmallGaugeCNFGauge,
      v13RealLinearSmallGaugeCNFSATWorldSemantics.SatNormal (CDENF E) =
        v13RealLinearSmallGaugeCNFSATWorldSemantics.SatRaw E := by
  intro E
  exact CDENF_semantics v13RealLinearSmallGaugeCNFSATWorldSemantics E

/-- Structural `gaugeFaithfulness` transfer for the global SAT-world small
real-linear gauge-CNF surface: a raw gauge atom normalizes to exactly the
concrete hidden-gauge predicate on satisfying SAT worlds. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_gaugeFaithfulness :
    ∀ gamma : V13RealLinearSmallGaugeCNFGauge,
      v13RealLinearSmallGaugeCNFSATWorldSemantics.SatNormal
          (CDENF (.gauge gamma)) =
        v13RealLinearSmallGaugeCNFSATWorldSemantics.gaugeSat gamma := by
  intro gamma
  rfl

/-- Structural `hiddenGaugeProduct` transfer for the global SAT-world small
real-linear gauge-CNF surface.  Every hidden-gauge action is satisfied because
the action preserves verifier validity and the fixed message readout. -/
theorem v13RealLinearSmallGaugeCNFSATWorld_hiddenGaugeProduct :
    ∀ gamma omega,
      v13RealLinearSmallGaugeCNFSATWorldSemantics.gaugeSat gamma omega := by
  intro gamma omega
  exact
    v13RealLinearSmallGaugeCNFSATWorldGaugeAction_preserves_target
      gamma omega

/-- Gauge satisfaction for the explicit small surface is target preservation
under the concrete hidden-gauge action. -/
def v13RealLinearSmallGaugeCNFGaugeSat
    (msg : Bool) (gamma : V13RealLinearSmallGaugeCNFGauge)
    (omega : V13RealLinearSmallGaugeCNFWorld msg) : Prop :=
  v13RealLinearSmallGaugeCNFTarget
      (v13RealLinearSmallGaugeCNFWorldGaugeAction gamma omega) =
    v13RealLinearSmallGaugeCNFTarget omega

/-- Evidence semantics for the explicit small gauge-CNF surface. -/
def v13RealLinearSmallGaugeCNFSemantics
    (msg : Bool) :
    EvidenceSemantics
      (V13RealLinearSmallGaugeCNFWorld msg)
      V13RealLinearSmallGaugeCNFNeutral
      V13RealLinearSmallGaugeCNFSafe
      V13RealLinearSmallGaugeCNFGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := v13RealLinearSmallGaugeCNFGaugeSat msg

/-- Structural `atomCompleteness` transfer for the explicit small
real-linear gauge-CNF surface: CD-ENF normalization preserves the concrete
evidence semantics. -/
theorem v13RealLinearSmallGaugeCNF_atomCompleteness
    (msg : Bool) :
    ∀ E :
      RawEvidence
        V13RealLinearSmallGaugeCNFNeutral
        V13RealLinearSmallGaugeCNFSafe
        V13RealLinearSmallGaugeCNFGauge,
      (v13RealLinearSmallGaugeCNFSemantics msg).SatNormal (CDENF E) =
        (v13RealLinearSmallGaugeCNFSemantics msg).SatRaw E := by
  intro E
  exact CDENF_semantics (v13RealLinearSmallGaugeCNFSemantics msg) E

/-- Structural `gaugeFaithfulness` transfer for the explicit small
real-linear gauge-CNF surface: a raw gauge atom normalizes to exactly the
concrete hidden-gauge predicate. -/
theorem v13RealLinearSmallGaugeCNF_gaugeFaithfulness
    (msg : Bool) :
    ∀ gamma : V13RealLinearSmallGaugeCNFGauge,
      (v13RealLinearSmallGaugeCNFSemantics msg).SatNormal
          (CDENF (.gauge gamma)) =
        (v13RealLinearSmallGaugeCNFSemantics msg).gaugeSat gamma := by
  intro gamma
  rfl

/-- Structural `hiddenGaugeProduct` transfer for the explicit small
real-linear gauge-CNF instance: every Boolean gauge action is satisfied at
every verifier-valid world because it only flips the hidden gauge coordinate
and preserves the locked message readout. -/
theorem v13RealLinearSmallGaugeCNF_hiddenGaugeProduct
    (msg : Bool) :
    ∀ gamma omega,
      (v13RealLinearSmallGaugeCNFSemantics msg).gaugeSat gamma omega := by
  intro gamma omega
  exact
    v13RealLinearSmallGaugeCNFWorldGaugeAction_preserves_target
      gamma omega

/-! ## Global two-message small real-linear gauge-CNF ensemble -/

/-- Global valid worlds for the explicit small real-linear gauge-CNF ensemble:
the public message bit varies, and the hidden gauge bit remains free.  The CNF
assignment attached below is the canonical satisfying assignment for this
public message and gauge bit. -/
structure V13RealLinearSmallGaugeCNFEnsembleWorld where
  msg : Bool
  gauge : Bool
deriving DecidableEq, Fintype

/-- Public input for the global small real-linear gauge-CNF ensemble: the
locked message bit selecting the concrete public CNF instance. -/
def v13RealLinearSmallGaugeCNFEnsemblePublicInput
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) : Bool :=
  omega.msg

/-- The satisfying CNF assignment represented by a global small-ensemble
world. -/
def v13RealLinearSmallGaugeCNFEnsembleAssignment
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) :
    V13RealLinearSmallGaugeCNFWitness :=
  v13RealLinearSmallGaugeCNFAssignment omega.msg omega.gauge

/-- Each global small-ensemble world carries a real satisfying assignment for
the corresponding concrete public message. -/
theorem v13RealLinearSmallGaugeCNFEnsembleAssignment_valid
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) :
    v13RealLinearSmallGaugeCNFVerifier omega.msg
      (v13RealLinearSmallGaugeCNFEnsembleAssignment omega) :=
  v13RealLinearSmallGaugeCNFFormula_satisfied_assignment
    omega.msg omega.gauge

/-- Target readout for the global small-ensemble world. -/
def v13RealLinearSmallGaugeCNFEnsembleTarget
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) : Bool :=
  v13RealLinearSmallGaugeCNFReadout
    (v13RealLinearSmallGaugeCNFEnsembleAssignment omega)

/-- The global target readout is the public message bit of the represented
small CNF instance. -/
theorem v13RealLinearSmallGaugeCNFEnsembleTarget_eq_message
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) :
    v13RealLinearSmallGaugeCNFEnsembleTarget omega =
      v13RealLinearSmallGaugeCNFMessage omega.msg := by
  cases omega
  simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
    v13RealLinearSmallGaugeCNFEnsembleAssignment,
    v13RealLinearSmallGaugeCNFReadout,
    v13RealLinearSmallGaugeCNFMessage]

/-! ## Global small real-linear gauge-CNF single-message transfer -/

/-- Structural `singleMessage` transfer for the global two-message small
real-linear gauge-CNF ensemble.  Inside a fixed public CNF instance, varying
the hidden gauge bit does not change the target readout. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_singleMessage :
    ∀ omega₀ omega₁ : V13RealLinearSmallGaugeCNFEnsembleWorld,
      v13RealLinearSmallGaugeCNFEnsemblePublicInput omega₀ =
        v13RealLinearSmallGaugeCNFEnsemblePublicInput omega₁ ->
        v13RealLinearSmallGaugeCNFEnsembleTarget omega₀ =
          v13RealLinearSmallGaugeCNFEnsembleTarget omega₁ := by
  intro omega₀ omega₁ hPublic
  rw [v13RealLinearSmallGaugeCNFEnsembleTarget_eq_message omega₀,
    v13RealLinearSmallGaugeCNFEnsembleTarget_eq_message omega₁]
  exact congrArg v13RealLinearSmallGaugeCNFMessage hPublic

/-! ## Global small real-linear gauge-CNF hidden-gauge-product transfer -/

/-- Hidden-gauge action on the global small real-linear gauge-CNF ensemble.
It preserves the public message bit and applies the concrete SAT-level
hidden-gauge flip to the represented witness assignment. -/
def v13RealLinearSmallGaugeCNFEnsembleGaugeAction
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) :
    V13RealLinearSmallGaugeCNFEnsembleWorld where
  msg := omega.msg
  gauge := if gamma then !omega.gauge else omega.gauge

/-- The global hidden-gauge action is exactly the SAT-level hidden-gauge
action on the represented concrete witness assignment. -/
theorem v13RealLinearSmallGaugeCNFEnsembleGaugeAction_assignment
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) :
    v13RealLinearSmallGaugeCNFEnsembleAssignment
        (v13RealLinearSmallGaugeCNFEnsembleGaugeAction gamma omega) =
      v13RealLinearSmallGaugeCNFGaugeAction gamma
        (v13RealLinearSmallGaugeCNFEnsembleAssignment omega) := by
  funext v
  cases v with
  | some j =>
      rfl
  | none =>
      rfl

/-- The global hidden-gauge action preserves target readout because it is the
concrete SAT-level hidden-gauge action on the represented witness. -/
theorem v13RealLinearSmallGaugeCNFEnsembleGaugeAction_preserves_target
    (gamma : Bool) (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) :
    v13RealLinearSmallGaugeCNFEnsembleTarget
        (v13RealLinearSmallGaugeCNFEnsembleGaugeAction gamma omega) =
      v13RealLinearSmallGaugeCNFEnsembleTarget omega := by
  unfold v13RealLinearSmallGaugeCNFEnsembleTarget
  rw [v13RealLinearSmallGaugeCNFEnsembleGaugeAction_assignment]
  exact
    v13RealLinearSmallGaugeCNFGaugeAction_preserves_readout
      gamma (v13RealLinearSmallGaugeCNFEnsembleAssignment omega)

/-- Gauge satisfaction for the global small ensemble is target preservation
under the concrete hidden-gauge action. -/
def v13RealLinearSmallGaugeCNFEnsembleGaugeSat
    (gamma : V13RealLinearSmallGaugeCNFGauge)
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) : Prop :=
  v13RealLinearSmallGaugeCNFEnsembleTarget
      (v13RealLinearSmallGaugeCNFEnsembleGaugeAction gamma omega) =
    v13RealLinearSmallGaugeCNFEnsembleTarget omega

/-- Evidence semantics for the global small real-linear gauge-CNF ensemble. -/
def v13RealLinearSmallGaugeCNFEnsembleSemantics :
    EvidenceSemantics
      V13RealLinearSmallGaugeCNFEnsembleWorld
      V13RealLinearSmallGaugeCNFNeutral
      V13RealLinearSmallGaugeCNFSafe
      V13RealLinearSmallGaugeCNFGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := v13RealLinearSmallGaugeCNFEnsembleGaugeSat

/-- Structural `atomCompleteness` transfer for the global two-message small
real-linear gauge-CNF ensemble: CD-ENF normalization preserves the concrete
global evidence semantics. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_atomCompleteness :
    ∀ E :
      RawEvidence
        V13RealLinearSmallGaugeCNFNeutral
        V13RealLinearSmallGaugeCNFSafe
        V13RealLinearSmallGaugeCNFGauge,
      v13RealLinearSmallGaugeCNFEnsembleSemantics.SatNormal (CDENF E) =
        v13RealLinearSmallGaugeCNFEnsembleSemantics.SatRaw E := by
  intro E
  exact CDENF_semantics v13RealLinearSmallGaugeCNFEnsembleSemantics E

/-- Structural `gaugeFaithfulness` transfer for the global two-message small
real-linear gauge-CNF ensemble: a normalized gauge atom is exactly the
concrete global hidden-gauge target-preservation predicate. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_gaugeFaithfulness :
    ∀ gamma : V13RealLinearSmallGaugeCNFGauge,
      v13RealLinearSmallGaugeCNFEnsembleSemantics.SatNormal
          (CDENF (.gauge gamma)) =
        v13RealLinearSmallGaugeCNFEnsembleSemantics.gaugeSat gamma := by
  intro gamma
  rfl

/-- Structural `hiddenGaugeProduct` transfer for the global two-message small
real-linear gauge-CNF ensemble.  Every Boolean hidden-gauge action is
satisfied at every global world because the action only flips the hidden
coordinate and preserves the represented SAT witness readout. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_hiddenGaugeProduct :
    ∀ gamma omega,
      v13RealLinearSmallGaugeCNFEnsembleSemantics.gaugeSat gamma omega := by
  intro gamma omega
  exact
    v13RealLinearSmallGaugeCNFEnsembleGaugeAction_preserves_target
      gamma omega

/-- History field for the global small ensemble: observe only the hidden gauge
bit, not the public message bit. -/
def v13RealLinearSmallGaugeCNFEnsembleHistoryField :
    FiniteSigmaField V13RealLinearSmallGaugeCNFEnsembleWorld where
  Atom := Bool
  atomDecidable := inferInstance
  atom := fun omega => omega.gauge

/-- The global small-ensemble world is exactly a public message bit together
with a hidden gauge bit. -/
def v13RealLinearSmallGaugeCNFEnsembleWorldEquivBoolProd :
    V13RealLinearSmallGaugeCNFEnsembleWorld ≃ Bool × Bool where
  toFun := fun omega => (omega.msg, omega.gauge)
  invFun := fun data => { msg := data.1, gauge := data.2 }
  left_inv := by
    intro omega
    cases omega
    rfl
  right_inv := by
    intro data
    cases data
    rfl

/-- The global small-ensemble world has four states. -/
theorem v13RealLinearSmallGaugeCNFEnsembleWorld_card :
    Fintype.card V13RealLinearSmallGaugeCNFEnsembleWorld = 4 := by
  calc
    Fintype.card V13RealLinearSmallGaugeCNFEnsembleWorld =
        Fintype.card (Bool × Bool) :=
      Fintype.card_congr
        v13RealLinearSmallGaugeCNFEnsembleWorldEquivBoolProd
    _ = 4 := by
      norm_num

/-- Target-true global small-ensemble worlds are exactly the two choices of
hidden gauge bit over the true public message. -/
def v13RealLinearSmallGaugeCNFEnsembleTargetTrueEquivGauge :
    {omega : V13RealLinearSmallGaugeCNFEnsembleWorld //
      v13RealLinearSmallGaugeCNFEnsembleTarget omega = true} ≃ Bool where
  toFun := fun omega => omega.val.gauge
  invFun := fun gauge =>
    ⟨{ msg := true, gauge := gauge }, by
      simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
        v13RealLinearSmallGaugeCNFEnsembleAssignment,
        v13RealLinearSmallGaugeCNFReadout]⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    cases omega with
    | mk omega htarget =>
        cases omega with
        | mk msg gauge =>
            cases msg
            · simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
                v13RealLinearSmallGaugeCNFEnsembleAssignment,
                v13RealLinearSmallGaugeCNFReadout] at htarget
            · rfl
  right_inv := by
    intro gauge
    rfl

/-- Correct worlds for the constant-true decoder are the target-true worlds. -/
def v13RealLinearSmallGaugeCNFEnsembleCorrectTrueEquivTargetTrue :
    {omega : V13RealLinearSmallGaugeCNFEnsembleWorld //
      (fun _ : V13RealLinearSmallGaugeCNFEnsembleWorld => true) omega =
        v13RealLinearSmallGaugeCNFEnsembleTarget omega} ≃
      {omega : V13RealLinearSmallGaugeCNFEnsembleWorld //
        v13RealLinearSmallGaugeCNFEnsembleTarget omega = true} where
  toFun := fun omega => ⟨omega.val, omega.property.symm⟩
  invFun := fun omega => ⟨omega.val, omega.property.symm⟩
  left_inv := by
    intro omega
    cases omega
    rfl
  right_inv := by
    intro omega
    cases omega
    rfl

/-- There are two target-true global small-ensemble worlds. -/
theorem v13RealLinearSmallGaugeCNFEnsembleTarget_true_card :
    Fintype.card
        {omega : V13RealLinearSmallGaugeCNFEnsembleWorld //
          v13RealLinearSmallGaugeCNFEnsembleTarget omega = true} = 2 := by
  calc
    Fintype.card
        {omega : V13RealLinearSmallGaugeCNFEnsembleWorld //
          v13RealLinearSmallGaugeCNFEnsembleTarget omega = true} =
        Fintype.card Bool :=
      Fintype.card_congr
        v13RealLinearSmallGaugeCNFEnsembleTargetTrueEquivGauge
    _ = 2 := by
      norm_num

/-- The global small real-linear gauge-CNF target is balanced across the two
public messages and the two hidden gauge states. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_target_balanced :
    BalancedBit v13RealLinearSmallGaugeCNFEnsembleTarget := by
  unfold BalancedBit globalDecoderSuccess
  rw [Fintype.card_congr
    v13RealLinearSmallGaugeCNFEnsembleCorrectTrueEquivTargetTrue,
    v13RealLinearSmallGaugeCNFEnsembleTarget_true_card,
    v13RealLinearSmallGaugeCNFEnsembleWorld_card]
  norm_num

/-- In a fixed hidden-gauge fiber, the target-true global world is unique. -/
def v13RealLinearSmallGaugeCNFEnsembleFiberTrueEquivUnit
    (gauge : Bool) :
    FiberTrue
        (fun omega : V13RealLinearSmallGaugeCNFEnsembleWorld =>
          omega.gauge)
        v13RealLinearSmallGaugeCNFEnsembleTarget gauge ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    ⟨{ msg := true, gauge := gauge }, by
      simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
        v13RealLinearSmallGaugeCNFEnsembleAssignment,
        v13RealLinearSmallGaugeCNFReadout]⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    cases omega with
    | mk omega hprops =>
        cases omega with
        | mk msg gauge' =>
            rcases hprops with ⟨hgauge, htarget⟩
            cases msg
            · simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
                v13RealLinearSmallGaugeCNFEnsembleAssignment,
                v13RealLinearSmallGaugeCNFReadout] at htarget
            · cases hgauge
              rfl
  right_inv := by
    intro unitValue
    cases unitValue
    rfl

/-- In a fixed hidden-gauge fiber, the target-false global world is unique. -/
def v13RealLinearSmallGaugeCNFEnsembleFiberFalseEquivUnit
    (gauge : Bool) :
    FiberFalse
        (fun omega : V13RealLinearSmallGaugeCNFEnsembleWorld =>
          omega.gauge)
        v13RealLinearSmallGaugeCNFEnsembleTarget gauge ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    ⟨{ msg := false, gauge := gauge }, by
      simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
        v13RealLinearSmallGaugeCNFEnsembleAssignment,
        v13RealLinearSmallGaugeCNFReadout]⟩
  left_inv := by
    intro omega
    apply Subtype.ext
    cases omega with
    | mk omega hprops =>
        cases omega with
        | mk msg gauge' =>
            rcases hprops with ⟨hgauge, htarget⟩
            cases msg
            · cases hgauge
              rfl
            · simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
                v13RealLinearSmallGaugeCNFEnsembleAssignment,
                v13RealLinearSmallGaugeCNFReadout] at htarget
  right_inv := by
    intro unitValue
    cases unitValue
    rfl

/-- The hidden-gauge history field is balanced: conditioning on either hidden
gauge value leaves one false-message and one true-message world. -/
theorem
    v13RealLinearSmallGaugeCNFEnsemble_historyField_balancedConditioning :
    BalancedConditioning
      v13RealLinearSmallGaugeCNFEnsembleHistoryField
      v13RealLinearSmallGaugeCNFEnsembleTarget := by
  change Neutral
    (fun omega : V13RealLinearSmallGaugeCNFEnsembleWorld =>
      omega.gauge)
    v13RealLinearSmallGaugeCNFEnsembleTarget
  intro gauge
  calc
    Fintype.card
        (FiberTrue
          (fun omega : V13RealLinearSmallGaugeCNFEnsembleWorld =>
            omega.gauge)
          v13RealLinearSmallGaugeCNFEnsembleTarget gauge) =
        Fintype.card Unit :=
      Fintype.card_congr
        (v13RealLinearSmallGaugeCNFEnsembleFiberTrueEquivUnit gauge)
    _ = Fintype.card Unit := rfl
    _ =
        Fintype.card
          (FiberFalse
            (fun omega : V13RealLinearSmallGaugeCNFEnsembleWorld =>
              omega.gauge)
            v13RealLinearSmallGaugeCNFEnsembleTarget gauge) :=
      (Fintype.card_congr
        (v13RealLinearSmallGaugeCNFEnsembleFiberFalseEquivUnit gauge)).symm

/-- Structural `admissibleHistories` transfer for the global two-message
small real-linear gauge-CNF ensemble.  The fixed-message slices are constant,
but the ensemble over both public message bits is balanced, and the hidden
gauge history field is target-neutral. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_admissibleHistories :
    BalancedBit v13RealLinearSmallGaugeCNFEnsembleTarget ∧
      BalancedConditioning
        v13RealLinearSmallGaugeCNFEnsembleHistoryField
        v13RealLinearSmallGaugeCNFEnsembleTarget :=
  ⟨v13RealLinearSmallGaugeCNFEnsemble_target_balanced,
    v13RealLinearSmallGaugeCNFEnsemble_historyField_balancedConditioning⟩

/-! ## Global small real-linear gauge-CNF no-public-target-tags transfer -/

/-- Target-blind neutral skeleton for the global small real-linear gauge-CNF
ensemble.  It records only the hidden gauge bit and deliberately omits the
public message bit and full formula syntax. -/
def v13RealLinearSmallGaugeCNFEnsembleNeutralSkeleton
    (omega : V13RealLinearSmallGaugeCNFEnsembleWorld) : Bool :=
  omega.gauge

/-- Opposite support for the global small ensemble pairs the two public
message phases within the same hidden-gauge fiber. -/
def v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
    (omega₀ omega₁ : V13RealLinearSmallGaugeCNFEnsembleWorld) : Prop :=
  omega₀.gauge = omega₁.gauge ∧
    omega₀.msg = false ∧ omega₁.msg = true

/-- The target-blind neutral skeleton is pair-neutral across the supported
opposite-message pairs. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_pairNeutral :
    PairNeutral
      v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
      v13RealLinearSmallGaugeCNFEnsembleNeutralSkeleton := by
  intro omega₀ omega₁ hSupport
  exact hSupport.1

/-- The global small ensemble has an explicit opposite-message pair for the
same hidden gauge bit. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_hasMessageOppositePair :
    HasMessageOppositePair
      v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
      v13RealLinearSmallGaugeCNFEnsembleTarget := by
  refine
    ⟨{ msg := false, gauge := false },
      { msg := true, gauge := false },
      ?_, ?_, ?_⟩
  · simp [v13RealLinearSmallGaugeCNFEnsembleOppositeSupport]
  · simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
      v13RealLinearSmallGaugeCNFEnsembleAssignment,
      v13RealLinearSmallGaugeCNFReadout]
  · simp [v13RealLinearSmallGaugeCNFEnsembleTarget,
      v13RealLinearSmallGaugeCNFEnsembleAssignment,
      v13RealLinearSmallGaugeCNFReadout]

/-- Structural `noPublicTargetTags` transfer for the global small real-linear
gauge-CNF ensemble, using the target-blind neutral skeleton.  This is separate
from the full-formula-syntax obstruction: the full two-clause formula exposes
the target unit clause, while this neutral skeleton does not include that row. -/
theorem v13RealLinearSmallGaugeCNFEnsemble_noPublicTargetTags :
    PairNeutral
        v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
        v13RealLinearSmallGaugeCNFEnsembleNeutralSkeleton ∧
      HasMessageOppositePair
        v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
        v13RealLinearSmallGaugeCNFEnsembleTarget ∧
        ¬ ∃ f : Bool -> Bool,
          ∀ omega : V13RealLinearSmallGaugeCNFEnsembleWorld,
            v13RealLinearSmallGaugeCNFEnsembleTarget omega =
              f (v13RealLinearSmallGaugeCNFEnsembleNeutralSkeleton omega) := by
  have hPair :
      PairNeutral
        v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
        v13RealLinearSmallGaugeCNFEnsembleNeutralSkeleton :=
    v13RealLinearSmallGaugeCNFEnsemble_pairNeutral
  have hOpp :
      HasMessageOppositePair
        v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
        v13RealLinearSmallGaugeCNFEnsembleTarget :=
    v13RealLinearSmallGaugeCNFEnsemble_hasMessageOppositePair
  exact
    ⟨hPair, hOpp,
      neutralSkeleton_not_sufficient
        v13RealLinearSmallGaugeCNFEnsembleOppositeSupport
        v13RealLinearSmallGaugeCNFEnsembleNeutralSkeleton
        v13RealLinearSmallGaugeCNFEnsembleTarget
        hPair hOpp⟩

/-! ## Gauge-buffered real linear CNF self-reduction -/

/-- Explicit P=NP-side SAT decider object for the gauge-buffered real linear
CNF variable type.  The theorems below remain conditional on this object; they
do not construct an unconditional SAT solver. -/
abbrev V13RealLinearGaugeCNFPNPSATDecider (m : Nat) :=
  RealCNFPNPSATDecider (V13RealLinearGaugeCNFVar m)

/-- Bit-fixing variable order for a concrete gauge-buffered real linear CNF,
computed from the variables that actually occur in the finite formula.  The
free hidden gauge coordinate is absent from the formula and need not be
fixed. -/
def v13RealLinearGaugeCNFBitFixVarOrder {m : Nat}
    (Y : V13RealLinearPublic m) :
    List (V13RealLinearGaugeCNFVar m) :=
  ConcreteCNF.formulaVarCover (v13RealLinearGaugeCNFFormula Y)

/-- The formula-syntax variable cover has no duplicate variables. -/
theorem v13RealLinearGaugeCNFBitFixVarOrder_nodup {m : Nat}
    (Y : V13RealLinearPublic m) :
    (v13RealLinearGaugeCNFBitFixVarOrder Y).Nodup := by
  unfold v13RealLinearGaugeCNFBitFixVarOrder
  exact ConcreteCNF.formulaVarCover_nodup (v13RealLinearGaugeCNFFormula Y)

/-- The bit-fixing variable order covers every variable used by the concrete
gauge-buffered CNF formula. -/
theorem v13RealLinearGaugeCNFFormula_usesOnly_bitFixVarOrder
    {m : Nat} (Y : V13RealLinearPublic m) :
    ConcreteCNF.FormulaUsesOnly
      (v13RealLinearGaugeCNFFormula Y)
      (v13RealLinearGaugeCNFBitFixVarOrder Y) := by
  unfold v13RealLinearGaugeCNFBitFixVarOrder
  exact
    ConcreteCNF.formulaUsesOnly_formulaVarCover
      (v13RealLinearGaugeCNFFormula Y)

/-- Every concrete gauge-buffered real linear public instance has a satisfying
assignment, for either choice of the free hidden gauge coordinate. -/
theorem v13RealLinearGaugeCNFFormula_satisfiable {m : Nat}
    (Y : V13RealLinearPublic m) :
    ∃ σ : V13RealLinearGaugeCNFWitness m,
      v13RealLinearGaugeCNFVerifier Y σ :=
  ⟨v13RealLinearGaugeCNFAssignment Y false,
    v13RealLinearGaugeCNFFormula_satisfied_assignment Y false⟩

/-- Standard bit-fixing search-to-decision assignment for the concrete
gauge-buffered real linear CNF, conditional on the explicit SAT decider
object. -/
def v13RealLinearGaugeCNFSelfReductionAssignment {m : Nat}
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (Y : V13RealLinearPublic m) :
    V13RealLinearGaugeCNFWitness m :=
  realCNFBitFixAssignment D
    (v13RealLinearGaugeCNFFormula Y)
    (v13RealLinearGaugeCNFBitFixVarOrder Y)

/-- Bit-fixing with the explicit SAT decider returns a satisfying assignment
for the concrete gauge-buffered CNF. -/
theorem v13RealLinearGaugeCNFSelfReductionAssignment_satisfies
    {m : Nat} (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (Y : V13RealLinearPublic m) :
    v13RealLinearGaugeCNFVerifier Y
      (v13RealLinearGaugeCNFSelfReductionAssignment D Y) := by
  exact
    realCNFBitFixAssignment_satisfies
      D
      (v13RealLinearGaugeCNFFormula_usesOnly_bitFixVarOrder Y)
      (v13RealLinearGaugeCNFBitFixVarOrder_nodup Y)
      (v13RealLinearGaugeCNFFormula_satisfiable Y)

/-- The recovered bit-fixing witness reads the fixed public message.  This is
the P=NP-conditional upper side: the hidden gauge coordinate may be chosen by
search, but the selected locked coordinate is forced by the CNF. -/
theorem v13RealLinearGaugeCNFSelfReduction_readout_eq_publicMessage
    {m : Nat} (i₀ : Fin m)
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (Y : V13RealLinearPublic m) :
    v13RealLinearGaugeCNFReadout i₀
        (v13RealLinearGaugeCNFSelfReductionAssignment D Y) =
      v13RealLinearMessageOfPublic i₀ Y :=
  v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid i₀
    (v13RealLinearGaugeCNFSelfReductionAssignment_satisfies D Y)

/-- Any verifier-valid witness has the same readout as the bit-fixing witness
returned by the explicit P=NP-side search-to-decision decoder. -/
theorem
    v13RealLinearGaugeCNFSelfReduction_readout_eq_validWitness_readout
    {m : Nat} (i₀ : Fin m)
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    {Y : V13RealLinearPublic m} {W : V13RealLinearGaugeCNFWitness m}
    (hW : v13RealLinearGaugeCNFVerifier Y W) :
    v13RealLinearGaugeCNFReadout i₀
        (v13RealLinearGaugeCNFSelfReductionAssignment D Y) =
      v13RealLinearGaugeCNFReadout i₀ W := by
  calc
    v13RealLinearGaugeCNFReadout i₀
        (v13RealLinearGaugeCNFSelfReductionAssignment D Y) =
        v13RealLinearMessageOfPublic i₀ Y :=
      v13RealLinearGaugeCNFSelfReduction_readout_eq_publicMessage i₀ D Y
    _ = v13RealLinearGaugeCNFReadout i₀ W :=
      (v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid i₀ hW).symm

/-- The concrete self-reduction uses a fixed program skeleton around the
explicit SAT decider, so the associated `kpolyAt` model is constant in the
target-block count. -/
theorem v13RealLinearGaugeCNFConstantDecoderKpolyAt_const {m : Nat}
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (targetBlocks targetBlocks' : Nat) :
    realCNFConstantDecoderKpolyAt D targetBlocks =
      realCNFConstantDecoderKpolyAt D targetBlocks' :=
  realCNFConstantDecoderKpolyAt_const D targetBlocks targetBlocks'

/-- Conditional upper-bound discharge for the concrete gauge-buffered real
linear CNF: given the explicit P=NP-side SAT decider and a lower-framework
regime identifying `kpolyAt` with the fixed self-reduction decoder and
`etaTimes t` with a linear floor, the self-reduction upper inequality follows.
-/
theorem v13RealLinearGaugeCNF_selfReductionUpperHypothesis_givenPNP
    {m : Nat} {F : CompressionLowerFramework}
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (R : RealCNFConstantDecoderRegime F D) :
    SelfReductionUpperHypothesis F :=
  realCNF_selfReductionUpperHypothesis_givenPNP D R

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

/-- No-target-rows gauge-buffered CNF world whose satisfying assignment is
recovered by the explicit P=NP-side bit-fixing self-reduction. -/
def v13RealLinearNoTargetRowsGaugeCNFWorldOfSelfReduction
    {m : Nat} {i₀ : Fin m}
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (omega : V13RealLinearNoTargetRowsWorld m i₀) :
    V13RealLinearNoTargetRowsGaugeCNFWorld m i₀ where
  base := omega
  assignment :=
    v13RealLinearGaugeCNFSelfReductionAssignment D
      (v13RealLinearNoTargetRowsPublicInput omega)
  sat :=
    v13RealLinearGaugeCNFSelfReductionAssignment_satisfies D
      (v13RealLinearNoTargetRowsPublicInput omega)

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

/-- The no-target-rows gauge-buffered CNF world as a concrete
single-message SAT spine: public input is the adjusted no-target-rows real
linear instance, hidden witness is the gauge-buffered CNF assignment, and
readout is the selected message coordinate. -/
def v13RealLinearNoTargetRowsGaugeCNFSingleMessageSATSpine
    {m : Nat} (i₀ : Fin m) :
    RealSingleMessageSATSpine
      (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀)
      (V13RealLinearPublic m)
      (V13RealLinearGaugeCNFWitness m) where
  publicInput := fun omega =>
    v13RealLinearNoTargetRowsPublicInput omega.base
  witnessOfWorld := fun omega => omega.assignment
  verifier := v13RealLinearGaugeCNFVerifier
  messageOfPublic := v13RealLinearMessageOfPublic i₀
  witnessReadout := v13RealLinearGaugeCNFReadout i₀
  target := v13RealLinearNoTargetRowsGaugeCNFTarget
  worldWitnessValid := by
    intro omega
    exact omega.sat
  readout_eq_message_of_valid := by
    intro Y W hW
    exact v13RealLinearGaugeCNFReadout_eq_publicMessage_of_valid i₀ hW
  target_eq_message := by
    intro omega
    exact v13RealLinearNoTargetRowsGaugeCNFReadout_eq_publicMessage omega

/-- Structural `singleMessage` projected from the concrete no-target-rows
gauge-CNF SAT spine. -/
theorem
    v13RealLinearNoTargetRowsGaugeCNFSingleMessageSATSpine_singleMessage
    {m : Nat} (i₀ : Fin m) :
    ∀ omega₀ omega₁ : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀,
      v13RealLinearNoTargetRowsPublicInput omega₀.base =
        v13RealLinearNoTargetRowsPublicInput omega₁.base ->
      v13RealLinearNoTargetRowsGaugeCNFTarget omega₀ =
        v13RealLinearNoTargetRowsGaugeCNFTarget omega₁ :=
  (v13RealLinearNoTargetRowsGaugeCNFSingleMessageSATSpine i₀).singleMessage

/-- Any verifier-valid gauge-CNF witness over the same no-target-rows public
instance reads the fixed public message coordinate. -/
theorem
    v13RealLinearNoTargetRowsGaugeCNFSingleMessageSATSpine_readout_eq_publicMessage
    {m : Nat} (i₀ : Fin m) {Y : V13RealLinearPublic m}
    {W : V13RealLinearGaugeCNFWitness m}
    (hW : v13RealLinearGaugeCNFVerifier Y W) :
    v13RealLinearGaugeCNFReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y :=
  (v13RealLinearNoTargetRowsGaugeCNFSingleMessageSATSpine i₀)
    |>.readout_eq_message_of_valid hW

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

/-- In the no-target-rows gauge-buffered CNF surface, bit-fixing under the
explicit P=NP-side SAT decider recovers a satisfying witness whose readout is
the hidden target bit of the base world. -/
theorem
    v13RealLinearNoTargetRowsGaugeCNFSelfReduction_target_eq_targetBit
    {m : Nat} {i₀ : Fin m}
    (D : V13RealLinearGaugeCNFPNPSATDecider m)
    (omega : V13RealLinearNoTargetRowsWorld m i₀) :
    v13RealLinearNoTargetRowsGaugeCNFTarget
        (v13RealLinearNoTargetRowsGaugeCNFWorldOfSelfReduction D omega) =
      v13RealLinearNoTargetRowsTargetBit omega := by
  calc
    v13RealLinearNoTargetRowsGaugeCNFTarget
        (v13RealLinearNoTargetRowsGaugeCNFWorldOfSelfReduction D omega) =
        v13RealLinearMessageOfPublic i₀
          (v13RealLinearNoTargetRowsPublicInput omega) := by
      simpa [v13RealLinearNoTargetRowsGaugeCNFTarget,
        v13RealLinearNoTargetRowsGaugeCNFWorldOfSelfReduction] using
        v13RealLinearGaugeCNFSelfReduction_readout_eq_publicMessage
          i₀ D (v13RealLinearNoTargetRowsPublicInput omega)
    _ = v13RealLinearNoTargetRowsTargetBit omega := by
      have hdecode :=
        v13RealLinearNoTargetRows_fullPublic_decodes_target i₀ omega
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

/-! ## Gauge-buffered CNF evidence semantics -/

/-- Neutral evidence atoms for the gauge-buffered real linear CNF surface. -/
abbrev V13RealLinearNoTargetRowsGaugeCNFNeutral :=
  Unit

/-- Safe evidence atoms for the gauge-buffered real linear CNF surface. -/
abbrev V13RealLinearNoTargetRowsGaugeCNFSafe :=
  Unit

/-- The concrete gauge family is the Boolean hidden-gauge flip. -/
abbrev V13RealLinearNoTargetRowsGaugeCNFGauge :=
  Bool

/-- Gauge satisfaction says the explicit gauge action preserves the public
instance and the target readout. -/
def v13RealLinearNoTargetRowsGaugeCNFGaugeSat {m : Nat}
    {i₀ : Fin m}
    (gamma : V13RealLinearNoTargetRowsGaugeCNFGauge)
    (omega : V13RealLinearNoTargetRowsGaugeCNFWorld m i₀) : Prop :=
  v13RealLinearNoTargetRowsPublicInput
      (v13RealLinearNoTargetRowsGaugeCNFGaugeAction gamma omega).base =
    v13RealLinearNoTargetRowsPublicInput omega.base ∧
    v13RealLinearNoTargetRowsGaugeCNFTarget
        (v13RealLinearNoTargetRowsGaugeCNFGaugeAction gamma omega) =
      v13RealLinearNoTargetRowsGaugeCNFTarget omega

/-- Evidence semantics for the gauge-buffered CNF surface.  The gauge atom is
interpreted by the concrete hidden-gauge action invariants. -/
def v13RealLinearNoTargetRowsGaugeCNFSemantics {m : Nat}
    (i₀ : Fin m) :
    EvidenceSemantics
      (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀)
      V13RealLinearNoTargetRowsGaugeCNFNeutral
      V13RealLinearNoTargetRowsGaugeCNFSafe
      V13RealLinearNoTargetRowsGaugeCNFGauge where
  neutralSat := fun _ _ => True
  safeSat := fun _ _ => True
  gaugeSat := v13RealLinearNoTargetRowsGaugeCNFGaugeSat

/-- Structural `atomCompleteness` for the gauge-buffered CNF surface: CD-ENF
normalization preserves the concrete evidence semantics. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_atomCompleteness
    {m : Nat} (i₀ : Fin m) :
    ∀ E :
      RawEvidence
        V13RealLinearNoTargetRowsGaugeCNFNeutral
        V13RealLinearNoTargetRowsGaugeCNFSafe
        V13RealLinearNoTargetRowsGaugeCNFGauge,
      (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀).SatNormal
          (CDENF E) =
        (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀).SatRaw E := by
  intro E
  exact CDENF_semantics (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀) E

/-- Structural `gaugeFaithfulness` for the gauge-buffered CNF surface: a raw
gauge atom normalizes to exactly the concrete hidden-gauge predicate. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_gaugeFaithfulness
    {m : Nat} (i₀ : Fin m) :
    ∀ gamma : V13RealLinearNoTargetRowsGaugeCNFGauge,
      (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀).SatNormal
          (CDENF (.gauge gamma)) =
        (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀).gaugeSat gamma := by
  intro gamma
  rfl

/-- The concrete hidden-gauge action satisfies the gauge predicate at every
world.  This is the `hiddenGaugeProduct` structural field for the
gauge-buffered no-target-rows CNF surface. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_hiddenGaugeProduct
    {m : Nat} (i₀ : Fin m) :
    ∀ gamma omega,
      (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀).gaugeSat
        gamma omega := by
  intro gamma omega
  exact
    ⟨rfl,
      v13RealLinearNoTargetRowsGaugeCNFGaugeAction_preserves_target
        gamma omega⟩

/-- Explicit manuscript-facing gauge-action data for the gauge-buffered CNF
surface. -/
def v13RealLinearNoTargetRowsGaugeCNFGaugeActionData {m : Nat}
    (i₀ : Fin m) :
    RealM4GaugeActionData
      (V13RealLinearNoTargetRowsGaugeCNFWorld m i₀)
      (V13RealLinearPublic m)
      V13RealLinearNoTargetRowsGaugeCNFNeutral
      V13RealLinearNoTargetRowsGaugeCNFSafe
      V13RealLinearNoTargetRowsGaugeCNFGauge
      (@v13RealLinearNoTargetRowsGaugeCNFTarget m i₀)
      (fun omega =>
        v13RealLinearNoTargetRowsPublicInput omega.base)
      (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀) where
  act := v13RealLinearNoTargetRowsGaugeCNFGaugeAction
  publicInvariant := by
    intro gamma omega
    simp [v13RealLinearNoTargetRowsGaugeCNFGaugeAction]
  targetInvariant := by
    intro gamma omega
    exact
      v13RealLinearNoTargetRowsGaugeCNFGaugeAction_preserves_target
        gamma omega
  gaugeSatisfied :=
    v13RealLinearNoTargetRowsGaugeCNF_hiddenGaugeProduct i₀

/-- The action-data projection recovers the same concrete
`hiddenGaugeProduct` field. -/
theorem v13RealLinearNoTargetRowsGaugeCNF_hiddenGaugeProduct_fromActionData
    {m : Nat} (i₀ : Fin m) :
    ∀ gamma omega,
      (v13RealLinearNoTargetRowsGaugeCNFSemantics i₀).gaugeSat
        gamma omega :=
  RealM4GaugeActionData.hiddenGaugeProduct
    (v13RealLinearNoTargetRowsGaugeCNFGaugeActionData i₀)

end Mettapedia.Computability.PNP
