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

end Mettapedia.Computability.PNP
