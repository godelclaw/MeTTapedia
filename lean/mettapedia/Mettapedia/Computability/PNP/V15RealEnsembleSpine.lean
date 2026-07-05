import Mettapedia.Computability.PNP.PNPv13LockedCoreLabCanaries
import Mettapedia.Computability.PNP.V13ConditionalClash
import Mettapedia.Computability.PNP.V13RealRungOneQRowBound

/-!
# PNP v15 real ensemble spine

This module starts the real-ensemble lift beyond the v14 toy endpoint.  It
records the manuscript-facing single-message SAT spine as an interface over a
public instance, hidden witness, verifier, fixed public message, and witness
readout.  The checked inhabitant below is the real v13 linear public surface:
the full public instance `(A, A x)` fixes the target coordinate and any valid
witness reads the same message.

This is not yet the full M4 SAT ensemble.  The ledger at the end records the
remaining construction obligations separately from the four irreducible
mathematical inputs.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f g h i j k l p

/-- Real single-message SAT spine: every supported world supplies a public
instance and a hidden witness; every verifier-valid witness reads the fixed
message of that public instance. -/
structure RealSingleMessageSATSpine
    (World : Type u) (Public : Type v) (Witness : Type w) where
  publicInput : World -> Public
  witnessOfWorld : World -> Witness
  verifier : Public -> Witness -> Prop
  messageOfPublic : Public -> Bool
  witnessReadout : Witness -> Bool
  target : World -> Bool
  worldWitnessValid :
    ∀ omega, verifier (publicInput omega) (witnessOfWorld omega)
  readout_eq_message_of_valid :
    ∀ {Y W}, verifier Y W -> witnessReadout W = messageOfPublic Y
  target_eq_message :
    ∀ omega, target omega = messageOfPublic (publicInput omega)

namespace RealSingleMessageSATSpine

variable {World : Type u} {Public : Type v} {Witness : Type w}

/-- The fixed public message makes the target single-valued over the full
public instance. -/
theorem singleMessage
    (S : RealSingleMessageSATSpine World Public Witness) :
    ∀ w0 w1, S.publicInput w0 = S.publicInput w1 ->
      S.target w0 = S.target w1 := by
  intro w0 w1 hPublic
  calc
    S.target w0 = S.messageOfPublic (S.publicInput w0) :=
      S.target_eq_message w0
    _ = S.messageOfPublic (S.publicInput w1) := by rw [hPublic]
    _ = S.target w1 := (S.target_eq_message w1).symm

/-- Any two verifier-valid hidden witnesses over one public instance have the
same readout. -/
theorem readout_eq_of_valid
    (S : RealSingleMessageSATSpine World Public Witness)
    {Y : Public} {W W' : Witness}
    (hW : S.verifier Y W) (hW' : S.verifier Y W') :
    S.witnessReadout W = S.witnessReadout W' := by
  calc
    S.witnessReadout W = S.messageOfPublic Y :=
      S.readout_eq_message_of_valid hW
    _ = S.witnessReadout W' :=
      (S.readout_eq_message_of_valid hW').symm

/-- The canonical hidden witness attached to a world reads the target bit. -/
theorem worldWitness_readout_eq_target
    (S : RealSingleMessageSATSpine World Public Witness)
    (omega : World) :
    S.witnessReadout (S.witnessOfWorld omega) = S.target omega := by
  calc
    S.witnessReadout (S.witnessOfWorld omega) =
        S.messageOfPublic (S.publicInput omega) :=
      S.readout_eq_message_of_valid (S.worldWitnessValid omega)
    _ = S.target omega := (S.target_eq_message omega).symm

end RealSingleMessageSATSpine

/-! ## Real v13 linear surface as a single-message spine -/

def v13RealLinearBit (a : ZMod 2) : Bool :=
  decide (a = 1)

def v13RealLinearVerifier {m : Nat}
    (Y : V13RealLinearPublic m) (W : F2Vec m) : Prop :=
  Y.A.toEquiv W = Y.b

def v13RealLinearWitnessReadout {m : Nat}
    (i₀ : Fin m) (W : F2Vec m) : Bool :=
  v13RealLinearBit (W i₀)

def v13RealLinearMessageOfPublic {m : Nat}
    (i₀ : Fin m) (Y : V13RealLinearPublic m) : Bool :=
  v13RealLinearBit (Y.A.toEquiv.symm Y.b i₀)

def v13RealLinearTargetBit {m : Nat}
    (i₀ : Fin m) (omega : V13RealLinearWorld m) : Bool :=
  v13RealLinearBit (v13RealLinearTarget i₀ omega)

theorem v13RealLinearVerifier_readout_eq_message {m : Nat}
    (i₀ : Fin m) {Y : V13RealLinearPublic m} {W : F2Vec m}
    (hW : v13RealLinearVerifier Y W) :
    v13RealLinearWitnessReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y := by
  have hWitness : W = Y.A.toEquiv.symm Y.b := by
    calc
      W = Y.A.toEquiv.symm (Y.A.toEquiv W) := by simp
      _ = Y.A.toEquiv.symm Y.b := by rw [hW]
  unfold v13RealLinearWitnessReadout v13RealLinearMessageOfPublic
  rw [hWitness]

theorem v13RealLinear_worldWitness_valid {m : Nat}
    (omega : V13RealLinearWorld m) :
    v13RealLinearVerifier (v13RealLinearPublicInput omega) omega.x := by
  rfl

theorem v13RealLinearTargetBit_eq_messageOfPublic {m : Nat}
    (i₀ : Fin m) (omega : V13RealLinearWorld m) :
    v13RealLinearTargetBit i₀ omega =
      v13RealLinearMessageOfPublic i₀ (v13RealLinearPublicInput omega) := by
  unfold v13RealLinearTargetBit v13RealLinearMessageOfPublic
  change
    v13RealLinearBit (v13RealLinearTarget i₀ omega) =
      v13RealLinearBit
        (v13RealLinearFullDecoder i₀ (v13RealLinearPublicInput omega))
  rw [v13RealLinear_fullPublic_decodes_target]

/-- The real linear public surface supplies the readout/single-message spine:
valid hidden witnesses over `(A, A x)` all read the public message
`(A^{-1} b)_{i₀}`. -/
def v13RealLinearSingleMessageSATSpine {m : Nat} (i₀ : Fin m) :
    RealSingleMessageSATSpine
      (V13RealLinearWorld m) (V13RealLinearPublic m) (F2Vec m) where
  publicInput := v13RealLinearPublicInput
  witnessOfWorld := fun omega => omega.x
  verifier := v13RealLinearVerifier
  messageOfPublic := v13RealLinearMessageOfPublic i₀
  witnessReadout := v13RealLinearWitnessReadout i₀
  target := v13RealLinearTargetBit i₀
  worldWitnessValid := v13RealLinear_worldWitness_valid
  readout_eq_message_of_valid := v13RealLinearVerifier_readout_eq_message i₀
  target_eq_message := v13RealLinearTargetBit_eq_messageOfPublic i₀

theorem v13RealLinearSingleMessageSATSpine_singleMessage {m : Nat}
    (i₀ : Fin m) :
    ∀ w0 w1 : V13RealLinearWorld m,
      v13RealLinearPublicInput w0 = v13RealLinearPublicInput w1 ->
        v13RealLinearTargetBit i₀ w0 = v13RealLinearTargetBit i₀ w1 :=
  (v13RealLinearSingleMessageSATSpine i₀).singleMessage

theorem v13RealLinear_validWitness_readout_eq_publicMessage {m : Nat}
    (i₀ : Fin m) {Y : V13RealLinearPublic m} {W : F2Vec m}
    (hW : v13RealLinearVerifier Y W) :
    v13RealLinearWitnessReadout i₀ W =
      v13RealLinearMessageOfPublic i₀ Y :=
  (v13RealLinearSingleMessageSATSpine i₀).readout_eq_message_of_valid hW

/-! ## Real no-target-rows public neutrality package -/

noncomputable instance v13RealLinearNoTargetRowsWorldInstNonempty
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)] :
    Nonempty (V13RealLinearNoTargetRowsWorld m i₀) :=
  ⟨(⟨v13RealLinearNoTargetRowShear i₀ hm.out,
      v13RealLinearNoTargetRowShear_targetRows_empty i₀ hm.out⟩,
    f2ZeroVec m)⟩

def v13RealLinearNoTargetRowsTargetBit {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsWorld m i₀) : Bool :=
  v13RealLinearBit (omega.2 i₀)

@[simp] theorem v13RealLinearBit_eq_true_iff (a : ZMod 2) :
    v13RealLinearBit a = true ↔ a = 1 := by
  unfold v13RealLinearBit
  by_cases h : a = 1 <;> simp [h]

@[simp] theorem v13RealLinearBit_eq_false_iff (a : ZMod 2) :
    v13RealLinearBit a = false ↔ a = 0 := by
  constructor
  · intro hfalse
    have hne : a ≠ 1 := by
      intro hone
      simp [v13RealLinearBit, hone] at hfalse
    fin_cases a
    · rfl
    · exact False.elim (hne rfl)
  · intro hzero
    simp [v13RealLinearBit, hzero]

noncomputable def v13RealLinearNoTargetRowsTargetFlipEquiv
    {m : Nat} {i₀ : Fin m} :
    {omega : V13RealLinearNoTargetRowsWorld m i₀ //
      v13RealLinearNoTargetRowsTargetBit omega = false} ≃
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        v13RealLinearNoTargetRowsTargetBit omega = true} := by
  classical
  let e := v13RealLinearSingleBit i₀
  exact
    { toFun := fun omega =>
        ⟨(omega.val.1, f2AddVec omega.val.2 e), by
          have hx : omega.val.2 i₀ = 0 :=
            (v13RealLinearBit_eq_false_iff _).mp omega.property
          simp [v13RealLinearNoTargetRowsTargetBit, v13RealLinearBit,
            e, f2AddVec, v13RealLinearSingleBit, hx]⟩
      invFun := fun omega =>
        ⟨(omega.val.1, f2AddVec omega.val.2 e), by
          have hx : omega.val.2 i₀ = 1 :=
            (v13RealLinearBit_eq_true_iff _).mp omega.property
          simp [v13RealLinearNoTargetRowsTargetBit, v13RealLinearBit,
            e, f2AddVec, v13RealLinearSingleBit, hx, f2_one_add_one]⟩
      left_inv := by
        intro omega
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · funext j
          simp [e, f2AddVec, f2_add_right_self]
      right_inv := by
        intro omega
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · funext j
          simp [e, f2AddVec, f2_add_right_self] }

theorem v13RealLinearNoTargetRowsTarget_false_card_eq_true
    {m : Nat} {i₀ : Fin m} :
    Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          v13RealLinearNoTargetRowsTargetBit omega = false} =
      Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          v13RealLinearNoTargetRowsTargetBit omega = true} :=
  Fintype.card_congr
    (@v13RealLinearNoTargetRowsTargetFlipEquiv m i₀)

theorem v13RealLinearNoTargetRows_constantTrue_correct_card_eq_true
    {m : Nat} {i₀ : Fin m} :
    Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          (fun _ : V13RealLinearNoTargetRowsWorld m i₀ => true) omega =
            v13RealLinearNoTargetRowsTargetBit omega} =
      Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          v13RealLinearNoTargetRowsTargetBit omega = true} := by
  let e :
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        (fun _ : V13RealLinearNoTargetRowsWorld m i₀ => true) omega =
          v13RealLinearNoTargetRowsTargetBit omega} ≃
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          v13RealLinearNoTargetRowsTargetBit omega = true} :=
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

theorem v13RealLinearNoTargetRows_world_card_eq_two_mul_target_true
    {m : Nat} (i₀ : Fin m) :
    Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) =
      2 * Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          v13RealLinearNoTargetRowsTargetBit omega = true} := by
  set a : Nat :=
    Fintype.card
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        v13RealLinearNoTargetRowsTargetBit omega = true}
  have hcomp :
      Fintype.card
          {omega : V13RealLinearNoTargetRowsWorld m i₀ //
            v13RealLinearNoTargetRowsTargetBit omega = false} =
        Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) - a := by
    simpa [a] using
      (Fintype.card_subtype_compl
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearNoTargetRowsTargetBit omega = true))
  have heq :
      a =
        Fintype.card
          {omega : V13RealLinearNoTargetRowsWorld m i₀ //
            v13RealLinearNoTargetRowsTargetBit omega = false} := by
    simpa [a] using
      (@v13RealLinearNoTargetRowsTarget_false_card_eq_true m i₀).symm
  have hsub :
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) - a = a := by
    simpa [heq] using hcomp.symm
  have hle :
      a ≤ Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) := by
    simpa [a] using
      Fintype.card_subtype_le
        (fun omega : V13RealLinearNoTargetRowsWorld m i₀ =>
          v13RealLinearNoTargetRowsTargetBit omega = true)
  have hsum :
      Fintype.card (V13RealLinearNoTargetRowsWorld m i₀) = a + a :=
    Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum

theorem v13RealLinearNoTargetRowsTarget_true_card_pos
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    0 <
      Fintype.card
        {omega : V13RealLinearNoTargetRowsWorld m i₀ //
          v13RealLinearNoTargetRowsTargetBit omega = true} := by
  let A : V13RealLinearNoTargetRowsMap m i₀ :=
    ⟨v13RealLinearNoTargetRowShear i₀ hm,
      v13RealLinearNoTargetRowShear_targetRows_empty i₀ hm⟩
  let omega : V13RealLinearNoTargetRowsWorld m i₀ :=
    (A, v13RealLinearSingleBit i₀)
  exact
    Fintype.card_pos_iff.mpr
      ⟨⟨omega, by
        simp [omega, v13RealLinearNoTargetRowsTargetBit,
          v13RealLinearBit, v13RealLinearSingleBit]⟩⟩

theorem v13RealLinearNoTargetRows_target_balanced
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsTargetBit m i₀) := by
  unfold BalancedBit globalDecoderSuccess
  rw [v13RealLinearNoTargetRows_constantTrue_correct_card_eq_true]
  rw [v13RealLinearNoTargetRows_world_card_eq_two_mul_target_true i₀]
  set a : Nat :=
    Fintype.card
      {omega : V13RealLinearNoTargetRowsWorld m i₀ //
        v13RealLinearNoTargetRowsTargetBit omega = true}
  have hpos : 0 < a := by
    simpa [a] using
      v13RealLinearNoTargetRowsTarget_true_card_pos i₀ hm
  have hne : (a : Rat) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [Nat.cast_mul]
  field_simp [hne]
  norm_num

def v13RealLinearNoTargetRowsNeutralSkeleton {m : Nat} {i₀ : Fin m}
    (omega : V13RealLinearNoTargetRowsWorld m i₀) :
    V13RealLinearNoTargetRowsMap m i₀ :=
  omega.1

def v13RealLinearNoTargetRowsOppositeSupport {m : Nat} {i₀ : Fin m}
    (omega₀ omega₁ : V13RealLinearNoTargetRowsWorld m i₀) : Prop :=
  omega₀.1 = omega₁.1

theorem v13RealLinearNoTargetRows_pairNeutral {m : Nat} {i₀ : Fin m} :
    PairNeutral
      (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
      (@v13RealLinearNoTargetRowsNeutralSkeleton m i₀) := by
  intro omega₀ omega₁ hSupport
  exact hSupport

theorem v13RealLinearNoTargetRows_hasMessageOppositePair
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    HasMessageOppositePair
      (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
      (@v13RealLinearNoTargetRowsTargetBit m i₀) := by
  let A : V13RealLinearNoTargetRowsMap m i₀ :=
    ⟨v13RealLinearNoTargetRowShear i₀ hm,
      v13RealLinearNoTargetRowShear_targetRows_empty i₀ hm⟩
  let omega₀ : V13RealLinearNoTargetRowsWorld m i₀ :=
    (A, f2ZeroVec m)
  let omega₁ : V13RealLinearNoTargetRowsWorld m i₀ :=
    (A, v13RealLinearSingleBit i₀)
  refine ⟨omega₀, omega₁, rfl, ?_, ?_⟩
  · simp [omega₀, v13RealLinearNoTargetRowsTargetBit,
      v13RealLinearBit, f2ZeroVec]
  · simp [omega₁, v13RealLinearNoTargetRowsTargetBit,
      v13RealLinearBit, v13RealLinearSingleBit]

/-- The adjusted real linear no-target-rows surface has the v13
`noPublicTargetTags` shape: the neutral skeleton is constant across an
opposite pair, the pair crosses the target bit, and therefore the neutral
skeleton alone cannot determine the target.  This is a real public-surface
construction theorem, not the full M4 mechanical interface certificate. -/
theorem v13RealLinearNoTargetRows_noPublicTargetTags
    {m : Nat} (i₀ : Fin m) (hm : 1 < m) :
    PairNeutral
        (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsNeutralSkeleton m i₀) ∧
      HasMessageOppositePair
        (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsTargetBit m i₀) ∧
        ¬ ∃ f : V13RealLinearNoTargetRowsMap m i₀ -> Bool,
          ∀ omega : V13RealLinearNoTargetRowsWorld m i₀,
            v13RealLinearNoTargetRowsTargetBit omega =
              f (v13RealLinearNoTargetRowsNeutralSkeleton omega) := by
  have hPair :
      PairNeutral
        (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsNeutralSkeleton m i₀) :=
    v13RealLinearNoTargetRows_pairNeutral
  have hOpp :
      HasMessageOppositePair
        (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsTargetBit m i₀) :=
    v13RealLinearNoTargetRows_hasMessageOppositePair i₀ hm
  exact
    ⟨hPair, hOpp,
      neutralSkeleton_not_sufficient
        (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
        (@v13RealLinearNoTargetRowsNeutralSkeleton m i₀)
        (@v13RealLinearNoTargetRowsTargetBit m i₀)
        hPair hOpp⟩

def v13RealLinearNoTargetRowsHistoryField {m : Nat} {i₀ : Fin m}
    (row : Fin m) :
    FiniteSigmaField (V13RealLinearNoTargetRowsWorld m i₀) where
  Atom := ZMod 2
  atomDecidable := inferInstance
  atom := fun omega => omega.1.val.toEquiv omega.2 row

/-- For the adjusted real no-target-rows surface, conditioning on one public
right-hand-side row remains balanced for the target bit.  Together with
`v13RealLinearNoTargetRows_target_balanced`, this gives an admissible row
history field for this real public surface; the full M4 history-field package
still has to identify the manuscript history atoms. -/
theorem v13RealLinearNoTargetRows_historyField_balancedConditioning
    {m : Nat} (i₀ row : Fin m) :
    BalancedConditioning
      (v13RealLinearNoTargetRowsHistoryField (i₀ := i₀) row)
      (@v13RealLinearNoTargetRowsTargetBit m i₀) := by
  classical
  unfold BalancedConditioning Neutral
  intro rhs
  have h :=
    v13RealLinearNoTargetRowsRhsTargetFiber_card_eq
      i₀ row rhs
  simpa [v13RealLinearNoTargetRowsHistoryField,
    v13RealLinearNoTargetRowsTargetBit,
    V13RealLinearNoTargetRowsRhsTargetFiber,
    FiberTrue, FiberFalse] using h.symm

/-- The adjusted real no-target-rows row-history field satisfies the v13
`admissibleHistories` balance pair in dimensions with an explicit no-target
map.  This is still a public-surface construction theorem, not the full M4
manuscript-history identification. -/
theorem v13RealLinearNoTargetRows_historyField_admissible
    {m : Nat} (i₀ row : Fin m) (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsTargetBit m i₀) ∧
      BalancedConditioning
        (v13RealLinearNoTargetRowsHistoryField (i₀ := i₀) row)
        (@v13RealLinearNoTargetRowsTargetBit m i₀) :=
  ⟨v13RealLinearNoTargetRows_target_balanced i₀ hm,
    v13RealLinearNoTargetRows_historyField_balancedConditioning i₀ row⟩

def v13RealLinearNoTargetRowsPublicCoordinateField {m : Nat}
    {i₀ : Fin m} (coordinate : V13RealLinearPublicCoordinate m) :
    FiniteSigmaField (V13RealLinearNoTargetRowsWorld m i₀) where
  Atom := ZMod 2
  atomDecidable := inferInstance
  atom := fun omega =>
    v13RealLinearCoordinateValue coordinate
      (v13RealLinearNoTargetRowsPublicInput omega)

/-- Every single public coordinate of the adjusted real no-target-rows surface
has balanced target fibers.  This packages the rung-one public-surface
cardinality theorem as a v13 `BalancedConditioning` statement. -/
theorem v13RealLinearNoTargetRows_publicCoordinate_balancedConditioning
    {m : Nat} (i₀ : Fin m)
    (coordinate : V13RealLinearPublicCoordinate m) :
    BalancedConditioning
      (v13RealLinearNoTargetRowsPublicCoordinateField (i₀ := i₀) coordinate)
      (@v13RealLinearNoTargetRowsTargetBit m i₀) := by
  classical
  unfold BalancedConditioning Neutral
  intro value
  have h :=
    v13RealLinearNoTargetRowsCoordinateTargetFiber_card_eq
      i₀ coordinate value
  simpa [v13RealLinearNoTargetRowsPublicCoordinateField,
    v13RealLinearNoTargetRowsTargetBit,
    V13RealLinearNoTargetRowsCoordinateTargetFiber,
    FiberTrue, FiberFalse] using h.symm

/-- The adjusted real no-target-rows public-coordinate field satisfies the v13
`admissibleHistories` balance pair for every public coordinate.  This is still
a public-surface construction theorem; full M4 must identify the manuscript
history atoms and connect them to this surface. -/
theorem v13RealLinearNoTargetRows_publicCoordinate_admissible
    {m : Nat} (i₀ : Fin m)
    (coordinate : V13RealLinearPublicCoordinate m) (hm : 1 < m) :
    BalancedBit (@v13RealLinearNoTargetRowsTargetBit m i₀) ∧
      BalancedConditioning
        (v13RealLinearNoTargetRowsPublicCoordinateField (i₀ := i₀)
          coordinate)
        (@v13RealLinearNoTargetRowsTargetBit m i₀) :=
  ⟨v13RealLinearNoTargetRows_target_balanced i₀ hm,
    v13RealLinearNoTargetRows_publicCoordinate_balancedConditioning
      i₀ coordinate⟩

theorem v13RealLinearNoTargetRows_singleMessage
    {m : Nat} (i₀ : Fin m) :
    ∀ omega₀ omega₁ : V13RealLinearNoTargetRowsWorld m i₀,
      v13RealLinearNoTargetRowsPublicInput omega₀ =
        v13RealLinearNoTargetRowsPublicInput omega₁ ->
      v13RealLinearNoTargetRowsTargetBit omega₀ =
        v13RealLinearNoTargetRowsTargetBit omega₁ := by
  intro omega₀ omega₁ hPublic
  unfold v13RealLinearNoTargetRowsTargetBit
  rw [v13RealLinearNoTargetRows_fullPublic_determines_target
    i₀ omega₀ omega₁ hPublic]

/-! ## Appendix D locked-core adapter for the real spine -/

/-- A supported public lock together with one locked completion.  This is the
world shape used to adapt Appendix D locked cores to the real single-message
spine. -/
structure RealM4LockedCoreWorld
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) where
  publicLock : PublicLock
  support : C.support publicLock
  completion : C.LockedCompletion publicLock

/-- Hidden witness package for one Appendix D locked completion. -/
structure RealM4LockedCoreWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) where
  publicLock : PublicLock
  completion : C.LockedCompletion publicLock

def RealM4LockedCoreWorld.toWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {C : AppendixDLockedCore PublicLock Quotient LockAux Message}
    (omega : RealM4LockedCoreWorld C) :
    RealM4LockedCoreWitness C where
  publicLock := omega.publicLock
  completion := omega.completion

def realM4LockedCoreVerifier
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (Y : PublicLock) (W : RealM4LockedCoreWitness C) : Prop :=
  W.publicLock = Y ∧ C.support Y

def realM4LockedCoreWitnessReadout
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {C : AppendixDLockedCore PublicLock Quotient LockAux Message}
    (messageBit : Message -> Bool)
    (W : RealM4LockedCoreWitness C) : Bool :=
  messageBit W.completion.message

def realM4LockedCoreMessageOfPublic
    {PublicLock : Type u} {Message : Type z}
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (Y : PublicLock) : Bool :=
  messageBit (publicMessage Y)

theorem realM4LockedCoreWitness_readout_eq_publicMessage
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage)
    {Y : PublicLock} {W : RealM4LockedCoreWitness C}
    (hW : realM4LockedCoreVerifier C Y W) :
    realM4LockedCoreWitnessReadout messageBit W =
      realM4LockedCoreMessageOfPublic publicMessage messageBit Y := by
  rcases hW with ⟨hPublic, hSupportY⟩
  have hSupportW : C.support W.publicLock := by
    simpa [hPublic] using hSupportY
  have hMessage : W.completion.message = publicMessage W.publicLock :=
    hinvariant hSupportW W.completion
  unfold realM4LockedCoreWitnessReadout realM4LockedCoreMessageOfPublic
  rw [hMessage, hPublic]

/-- A public-message invariant adapts an Appendix D locked core to the real
single-message spine.  This proves the wiring from the invariant to the
single-message interface; it does not construct the invariant for M4. -/
def realM4LockedCoreSingleMessageSATSpine
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    RealSingleMessageSATSpine
      (RealM4LockedCoreWorld C) PublicLock (RealM4LockedCoreWitness C) where
  publicInput := fun omega => omega.publicLock
  witnessOfWorld := fun omega => omega.toWitness
  verifier := realM4LockedCoreVerifier C
  messageOfPublic := realM4LockedCoreMessageOfPublic publicMessage messageBit
  witnessReadout := realM4LockedCoreWitnessReadout messageBit
  target := fun omega =>
    realM4LockedCoreMessageOfPublic publicMessage messageBit omega.publicLock
  worldWitnessValid := by
    intro omega
    exact ⟨rfl, omega.support⟩
  readout_eq_message_of_valid :=
    realM4LockedCoreWitness_readout_eq_publicMessage
      C publicMessage messageBit hinvariant
  target_eq_message := by
    intro omega
    rfl

theorem realM4LockedCore_singleMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    ∀ w0 w1 : RealM4LockedCoreWorld C,
      w0.publicLock = w1.publicLock ->
        realM4LockedCoreMessageOfPublic publicMessage messageBit w0.publicLock =
          realM4LockedCoreMessageOfPublic publicMessage messageBit w1.publicLock :=
  (realM4LockedCoreSingleMessageSATSpine
    C publicMessage messageBit hinvariant).singleMessage

theorem realM4LockedCore_readout_eq_of_valid_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : C.PublicMessageInvariant publicMessage)
    {Y : PublicLock} {W W' : RealM4LockedCoreWitness C}
    (hW : realM4LockedCoreVerifier C Y W)
    (hW' : realM4LockedCoreVerifier C Y W') :
    realM4LockedCoreWitnessReadout messageBit W =
      realM4LockedCoreWitnessReadout messageBit W' :=
  (realM4LockedCoreSingleMessageSATSpine
    C publicMessage messageBit hinvariant).readout_eq_of_valid hW hW'

theorem realM4_lockedMessageRigidity_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message)
    {publicMessage : PublicLock -> Message}
    (hinvariant : C.PublicMessageInvariant publicMessage) :
    C.LockedMessageRigidity :=
  C.lockedMessageRigidity_of_publicMessageInvariant hinvariant

theorem realM4_cnfSingleMessageReadout_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) :=
  D.singleMessageReadout_of_lockedMessageRigidity
    (D.core.lockedMessageRigidity_of_publicMessageInvariant hinvariant) hY

theorem realM4_semanticI26_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    (∃ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α) ∧
    (∀ α : ConcreteCNF.Assignment (Var Y),
      ConcreteCNF.IsSatFormula (D.formula Y) α ->
        D.validWitness Y (D.extract Y α)) ∧
    SingleMessageReadout
      (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) :=
  D.semantic_i26_items_of_lockedMessageRigidity
    (D.core.lockedMessageRigidity_of_publicMessageInvariant hinvariant) hY

theorem realM4_exists_correctForAllSatSearchOutputs_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    ∃ msg : Message,
      CorrectForAllSatSearchOutputs
        (ConcreteCNF.IsSatFormula (D.formula Y)) (D.projection Y) msg :=
  D.exists_correctForAllSatSearchOutputs_of_lockedMessageRigidity
    (D.core.lockedMessageRigidity_of_publicMessageInvariant hinvariant) hY

theorem realM4_supportedArbitraryOutputSATSearchCorrect_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage) :
    D.toManuscriptCNFReadoutData.SupportedArbitraryOutputSATSearchCorrect := by
  intro Y hY
  exact
    realM4_exists_correctForAllSatSearchOutputs_of_publicMessageInvariant
      D hinvariant hY

/-! ## Appendix I CNF adapter for the real spine -/

/-- A supported public CNF instance together with a satisfying assignment. -/
structure RealM4CNFWorld
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  publicInstance : Public
  support : D.support publicInstance
  assignment : ConcreteCNF.Assignment (Var publicInstance)
  sat : ConcreteCNF.IsSatFormula (D.formula publicInstance) assignment

/-- Hidden CNF witness package for the real Appendix I spine. -/
structure RealM4CNFWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  publicInstance : Public
  assignment : ConcreteCNF.Assignment (Var publicInstance)

def RealM4CNFWorld.toWitness
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (omega : RealM4CNFWorld D) :
    RealM4CNFWitness D where
  publicInstance := omega.publicInstance
  assignment := omega.assignment

def realM4CNFVerifier
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (Y : Public) (W : RealM4CNFWitness D) : Prop :=
  D.support Y ∧
    ∃ _hPublic : W.publicInstance = Y,
      ConcreteCNF.IsSatFormula (D.formula W.publicInstance) W.assignment

def realM4CNFWitnessReadout
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (messageBit : Message -> Bool)
    (W : RealM4CNFWitness D) : Bool :=
  messageBit (D.projection W.publicInstance W.assignment)

def realM4CNFMessageOfPublic
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (Y : Public) : Bool :=
  messageBit (publicMessage (D.publicLock Y))

theorem realM4CNFWitness_readout_eq_publicMessage
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} {W : RealM4CNFWitness D}
    (hW : realM4CNFVerifier D Y W) :
    realM4CNFWitnessReadout messageBit W =
      realM4CNFMessageOfPublic D publicMessage messageBit Y := by
  rcases W with ⟨YW, α⟩
  change D.support Y ∧
    ∃ hPublic : YW = Y,
      ConcreteCNF.IsSatFormula (D.formula YW) α at hW
  rcases hW with ⟨hSupportY, ⟨hPublic, hSat⟩⟩
  have hSupportYW : D.support YW := by
    rw [hPublic]
    exact hSupportY
  have hCompletionMessage :
      (D.witnessCompletion (D.extract YW α) (D.cnfSound hSat)).message =
        publicMessage (D.publicLock YW) :=
    hinvariant (D.support_publicLock hSupportYW)
      (D.witnessCompletion (D.extract YW α) (D.cnfSound hSat))
  have hProjection :
      D.projection YW α = publicMessage (D.publicLock Y) := by
    calc
      D.projection YW α =
          D.witnessMessage YW (D.extract YW α) :=
        D.projection_eq_witnessMessage hSat
      _ = (D.witnessCompletion (D.extract YW α) (D.cnfSound hSat)).message :=
        D.witnessMessage_eq_completionMessage (D.cnfSound hSat)
      _ = publicMessage (D.publicLock YW) :=
        hCompletionMessage
      _ = publicMessage (D.publicLock Y) := by rw [hPublic]
  exact congrArg messageBit hProjection

/-- Appendix I CNF assignments form the real single-message SAT spine once the
locked core supplies a public-message invariant.  This is the SAT-assignment
spine; it does not construct the invariant or the polynomial uniformity data. -/
def realM4CNFSingleMessageSATSpine
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage) :
    RealSingleMessageSATSpine
      (RealM4CNFWorld D) Public (RealM4CNFWitness D) where
  publicInput := fun omega => omega.publicInstance
  witnessOfWorld := fun omega => omega.toWitness
  verifier := realM4CNFVerifier D
  messageOfPublic := realM4CNFMessageOfPublic D publicMessage messageBit
  witnessReadout := realM4CNFWitnessReadout messageBit
  target := fun omega =>
    realM4CNFMessageOfPublic D publicMessage messageBit omega.publicInstance
  worldWitnessValid := by
    intro omega
    exact ⟨omega.support, ⟨rfl, omega.sat⟩⟩
  readout_eq_message_of_valid :=
    realM4CNFWitness_readout_eq_publicMessage
      D publicMessage messageBit hinvariant
  target_eq_message := by
    intro omega
    rfl

theorem realM4CNF_singleMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage) :
    ∀ w0 w1 : RealM4CNFWorld D,
      w0.publicInstance = w1.publicInstance ->
        realM4CNFMessageOfPublic D publicMessage messageBit w0.publicInstance =
          realM4CNFMessageOfPublic D publicMessage messageBit w1.publicInstance :=
  (realM4CNFSingleMessageSATSpine
    D publicMessage messageBit hinvariant).singleMessage

theorem realM4CNF_readout_eq_of_valid_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (publicMessage : PublicLock -> Message)
    (messageBit : Message -> Bool)
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} {W W' : RealM4CNFWitness D}
    (hW : realM4CNFVerifier D Y W)
    (hW' : realM4CNFVerifier D Y W') :
    realM4CNFWitnessReadout messageBit W =
      realM4CNFWitnessReadout messageBit W' :=
  (realM4CNFSingleMessageSATSpine
    D publicMessage messageBit hinvariant).readout_eq_of_valid
      (W := W) (W' := W') hW hW'

/-! ## Real CNF bit-fixing self-reduction core -/

namespace ConcreteCNF

variable {Var : Type u}

def Literal.var : Literal Var -> Var
  | .pos v => v
  | .neg v => v

def unitLiteral (v : Var) (value : Bool) : Literal Var :=
  if value then Literal.pos v else Literal.neg v

def unitClause (v : Var) (value : Bool) : Clause Var :=
  [unitLiteral v value]

def prefixClauses (pre : List (Var × Bool)) : Formula Var :=
  pre.map (fun fixed => unitClause fixed.1 fixed.2)

def restrictWithPrefix
    (formula : Formula Var) (pre : List (Var × Bool)) :
    Formula Var :=
  formula ++ prefixClauses pre

def FormulaUsesOnly (formula : Formula Var) (vars : List Var) : Prop :=
  ∀ {clause}, clause ∈ formula ->
    ∀ {lit}, lit ∈ clause -> lit.var ∈ vars

theorem isSatClause_unitClause_iff
    (σ : Assignment Var) (v : Var) (value : Bool) :
    IsSatClause (unitClause v value) σ ↔ σ v = value := by
  cases value <;>
    simp [unitClause, unitLiteral, IsSatClause, Literal.eval]

theorem isSatFormula_append_iff
    (formula extra : Formula Var) (σ : Assignment Var) :
    IsSatFormula (formula ++ extra) σ ↔
      IsSatFormula formula σ ∧ IsSatFormula extra σ := by
  constructor
  · intro h
    constructor
    · intro clause hclause
      exact h clause (List.mem_append_left extra hclause)
    · intro clause hclause
      exact h clause (List.mem_append_right formula hclause)
  · intro h clause hclause
    rcases List.mem_append.mp hclause with hformula | hextra
    · exact h.1 clause hformula
    · exact h.2 clause hextra

end ConcreteCNF

namespace CNFPrefix

variable {Var : Type u}

def Satisfied (σ : ConcreteCNF.Assignment Var)
    (pre : List (Var × Bool)) : Prop :=
  ∀ {v value}, (v, value) ∈ pre -> σ v = value

def value [DecidableEq Var] : List (Var × Bool) -> Var -> Bool
  | [], _ => false
  | (u, bit) :: rest, v => if v = u then bit else value rest v

def assignment [DecidableEq Var]
    (pre : List (Var × Bool)) : ConcreteCNF.Assignment Var :=
  fun v => value pre v

theorem satisfied_nil (σ : ConcreteCNF.Assignment Var) :
    Satisfied σ [] := by
  intro v value hmem
  cases hmem

theorem satisfied_append_single
    {σ : ConcreteCNF.Assignment Var} {pre : List (Var × Bool)}
    {v : Var} {value : Bool}
    (hprefix : Satisfied σ pre) (hvalue : σ v = value) :
    Satisfied σ (pre ++ [(v, value)]) := by
  intro u bit hmem
  rcases List.mem_append.mp hmem with hprefixMem | hsingle
  · exact hprefix hprefixMem
  · have hpair : (u, bit) = (v, value) := by
      simpa using hsingle
    cases hpair
    exact hvalue

theorem exists_pair_of_mem_keys
    {pre : List (Var × Bool)} {v : Var}
    (hmem : v ∈ pre.map Prod.fst) :
    ∃ value, (v, value) ∈ pre := by
  induction pre with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases head with ⟨u, bit⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · exact ⟨bit, by simp [hhead]⟩
      · rcases ih htail with ⟨value, hvalue⟩
        exact ⟨value, by simp [hvalue]⟩

theorem value_eq_of_mem [DecidableEq Var]
    {pre : List (Var × Bool)}
    (hnodup : (pre.map Prod.fst).Nodup)
    {v : Var} {bit : Bool} (hmem : (v, bit) ∈ pre) :
    value pre v = bit := by
  induction pre with
  | nil =>
      cases hmem
  | cons head tail ih =>
      rcases head with ⟨u, headBit⟩
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hnotMem, htailNodup⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases hhead
        simp [value]
      · have hv_ne_u : v ≠ u := by
          intro hv_eq_u
          apply hnotMem
          have hv_in_tail_keys : v ∈ tail.map Prod.fst := by
            exact List.mem_map.mpr ⟨(v, bit), htail, rfl⟩
          simpa [hv_eq_u] using hv_in_tail_keys
        simp [value, hv_ne_u]
        exact ih htailNodup htail

theorem assignment_eq_of_mem [DecidableEq Var]
    {pre : List (Var × Bool)}
    (hnodup : (pre.map Prod.fst).Nodup)
    {v : Var} {bit : Bool} (hmem : (v, bit) ∈ pre) :
    assignment pre v = bit :=
  value_eq_of_mem hnodup hmem

end CNFPrefix

namespace ConcreteCNF

variable {Var : Type u}

theorem isSatFormula_prefixClauses_iff
    (pre : List (Var × Bool)) (σ : Assignment Var) :
    IsSatFormula (prefixClauses pre) σ ↔
      CNFPrefix.Satisfied σ pre := by
  constructor
  · intro h v value hmem
    have hclause :
        unitClause v value ∈ prefixClauses pre := by
      exact List.mem_map.mpr ⟨(v, value), hmem, rfl⟩
    exact (isSatClause_unitClause_iff σ v value).mp (h _ hclause)
  · intro hprefix clause hclause
    rcases List.mem_map.mp hclause with ⟨fixed, hfixed, hclauseEq⟩
    rcases fixed with ⟨v, value⟩
    cases hclauseEq
    exact (isSatClause_unitClause_iff σ v value).mpr (hprefix hfixed)

theorem isSatFormula_restrictWithPrefix_iff
    (formula : Formula Var) (pre : List (Var × Bool))
    (σ : Assignment Var) :
    IsSatFormula (restrictWithPrefix formula pre) σ ↔
      IsSatFormula formula σ ∧ CNFPrefix.Satisfied σ pre := by
  rw [restrictWithPrefix, isSatFormula_append_iff,
    isSatFormula_prefixClauses_iff]

theorem isSatFormula_of_agree_on_formulaUsesOnly
    {formula : Formula Var} {vars : List Var}
    {σ τ : Assignment Var}
    (hvars : FormulaUsesOnly formula vars)
    (hσ : IsSatFormula formula σ)
    (hagree : ∀ {v : Var}, v ∈ vars -> τ v = σ v) :
    IsSatFormula formula τ := by
  intro clause hclause
  rcases hσ clause hclause with ⟨lit, hlit, heval⟩
  refine ⟨lit, hlit, ?_⟩
  have hvar : lit.var ∈ vars := hvars hclause hlit
  cases lit with
  | pos v =>
      have hag : τ v = σ v := hagree (by simpa [Literal.var] using hvar)
      simpa [Literal.eval, hag] using heval
  | neg v =>
      have hag : τ v = σ v := hagree (by simpa [Literal.var] using hvar)
      simpa [Literal.eval, hag] using heval

end ConcreteCNF

def RealCNFRestrictedSatisfiable
    {Var : Type u} (formula : ConcreteCNF.Formula Var)
    (pre : List (Var × Bool)) : Prop :=
  ∃ σ : ConcreteCNF.Assignment Var,
    ConcreteCNF.IsSatFormula formula σ ∧ CNFPrefix.Satisfied σ pre

/-- Explicit P=NP-side SAT decider object for real CNF formulas at a fixed
variable type.  The program and clock fields are charged by the constant
decoder cost model below; the theorem remains conditional on this object. -/
structure RealCNFPNPSATDecider (Var : Type u) where
  decideSat : ConcreteCNF.Formula Var -> Bool
  decidesSat :
    ∀ formula, decideSat formula = true ↔
      ∃ σ : ConcreteCNF.Assignment Var,
        ConcreteCNF.IsSatFormula formula σ
  programLength : Nat
  clockExponent : Nat
  clockExponent_pos : 0 < clockExponent

theorem realCNFRestricted_decideSat_true_iff
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var)
    (pre : List (Var × Bool)) :
    D.decideSat (ConcreteCNF.restrictWithPrefix formula pre) = true ↔
      RealCNFRestrictedSatisfiable formula pre := by
  constructor
  · intro hdec
    rcases (D.decidesSat _).mp hdec with ⟨σ, hσ⟩
    exact
      ⟨σ, (ConcreteCNF.isSatFormula_restrictWithPrefix_iff
        formula pre σ).mp hσ⟩
  · intro hsat
    rcases hsat with ⟨σ, hσ⟩
    exact
      (D.decidesSat _).mpr
        ⟨σ, (ConcreteCNF.isSatFormula_restrictWithPrefix_iff
          formula pre σ).mpr hσ⟩

def realCNFBitFixPrefixAux
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var) :
    List (Var × Bool) -> List Var -> List (Var × Bool)
  | pre, [] => pre
  | pre, v :: vars =>
      let falsePrefix := pre ++ [(v, false)]
      if D.decideSat (ConcreteCNF.restrictWithPrefix formula falsePrefix) then
        realCNFBitFixPrefixAux D formula falsePrefix vars
      else
        realCNFBitFixPrefixAux D formula (pre ++ [(v, true)]) vars

def realCNFBitFixPrefix
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var) (vars : List Var) :
    List (Var × Bool) :=
  realCNFBitFixPrefixAux D formula [] vars

def realCNFBitFixAssignment
    {Var : Type u} [DecidableEq Var]
    (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var) (vars : List Var) :
    ConcreteCNF.Assignment Var :=
  CNFPrefix.assignment (realCNFBitFixPrefix D formula vars)

theorem realCNFBitFixPrefixAux_keys
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (formula : ConcreteCNF.Formula Var)
    (pre : List (Var × Bool)) (vars : List Var) :
    (realCNFBitFixPrefixAux D formula pre vars).map Prod.fst =
      pre.map Prod.fst ++ vars := by
  induction vars generalizing pre with
  | nil =>
      simp [realCNFBitFixPrefixAux]
  | cons v vars ih =>
      unfold realCNFBitFixPrefixAux
      by_cases hdec :
          D.decideSat
            (ConcreteCNF.restrictWithPrefix formula
              (pre ++ [(v, false)])) = true
      · simp [hdec, ih, List.map_append, List.append_assoc]
      · simp [hdec, ih, List.map_append, List.append_assoc]

theorem realCNFBitFixPrefixAux_satisfiable
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    {formula : ConcreteCNF.Formula Var}
    {pre : List (Var × Bool)} {vars : List Var}
    (hSat : RealCNFRestrictedSatisfiable formula pre) :
    RealCNFRestrictedSatisfiable formula
      (realCNFBitFixPrefixAux D formula pre vars) := by
  induction vars generalizing pre with
  | nil =>
      simpa [realCNFBitFixPrefixAux] using hSat
  | cons v vars ih =>
      unfold realCNFBitFixPrefixAux
      by_cases hdec :
          D.decideSat
            (ConcreteCNF.restrictWithPrefix formula
              (pre ++ [(v, false)])) = true
      · simp [hdec]
        exact ih ((realCNFRestricted_decideSat_true_iff
          D formula (pre ++ [(v, false)])).mp hdec)
      · simp [hdec]
        apply ih
        rcases hSat with ⟨σ, hformula, hprefix⟩
        by_cases hvFalse : σ v = false
        · have hFalseSat :
            RealCNFRestrictedSatisfiable formula
              (pre ++ [(v, false)]) :=
            ⟨σ, hformula,
              CNFPrefix.satisfied_append_single hprefix hvFalse⟩
          exact False.elim
            (hdec ((realCNFRestricted_decideSat_true_iff
              D formula (pre ++ [(v, false)])).mpr hFalseSat))
        · have hvTrue : σ v = true := by
            cases hσv : σ v <;> simp [hσv] at hvFalse ⊢
          exact
            ⟨σ, hformula,
              CNFPrefix.satisfied_append_single hprefix hvTrue⟩

theorem realCNFBitFixAssignment_satisfies
    {Var : Type u} [DecidableEq Var]
    (D : RealCNFPNPSATDecider Var)
    {formula : ConcreteCNF.Formula Var} {vars : List Var}
    (hvars : ConcreteCNF.FormulaUsesOnly formula vars)
    (hnodup : vars.Nodup)
    (hSat : ∃ σ : ConcreteCNF.Assignment Var,
      ConcreteCNF.IsSatFormula formula σ) :
    ConcreteCNF.IsSatFormula formula
      (realCNFBitFixAssignment D formula vars) := by
  have hStart : RealCNFRestrictedSatisfiable formula [] := by
    rcases hSat with ⟨σ, hσ⟩
    exact ⟨σ, hσ, CNFPrefix.satisfied_nil σ⟩
  have hFinal :
      RealCNFRestrictedSatisfiable formula
        (realCNFBitFixPrefix D formula vars) := by
    simpa [realCNFBitFixPrefix] using
      (realCNFBitFixPrefixAux_satisfiable
        D (formula := formula) (pre := []) (vars := vars) hStart)
  rcases hFinal with ⟨σ, hσformula, hσpre⟩
  apply ConcreteCNF.isSatFormula_of_agree_on_formulaUsesOnly
    hvars hσformula
  intro v hv
  let finalPrefix := realCNFBitFixPrefix D formula vars
  have hkeys : finalPrefix.map Prod.fst = vars := by
    simpa [finalPrefix, realCNFBitFixPrefix] using
      (realCNFBitFixPrefixAux_keys
        D formula ([] : List (Var × Bool)) vars)
  have hprefixNodup : (finalPrefix.map Prod.fst).Nodup := by
    simpa [hkeys] using hnodup
  have hvKey : v ∈ finalPrefix.map Prod.fst := by
    simpa [hkeys] using hv
  rcases CNFPrefix.exists_pair_of_mem_keys hvKey with ⟨bit, hbit⟩
  have hAssignment :
      realCNFBitFixAssignment D formula vars v = bit := by
    simpa [realCNFBitFixAssignment, finalPrefix] using
      (CNFPrefix.assignment_eq_of_mem hprefixNodup hbit)
  have hSigma : σ v = bit := hσpre hbit
  exact hAssignment.trans hSigma.symm

theorem realM4_bitFixingAssignment_satisfies
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {Y : Public} (hY : D.support Y)
    [DecidableEq (Var Y)]
    (A : RealCNFPNPSATDecider (Var Y))
    (vars : List (Var Y))
    (hvars : ConcreteCNF.FormulaUsesOnly (D.formula Y) vars)
    (hnodup : vars.Nodup) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (realCNFBitFixAssignment A (D.formula Y) vars) :=
  realCNFBitFixAssignment_satisfies A hvars hnodup (D.satOnSupport hY)

theorem realM4_bitFixingReadout_eq_publicMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y)
    [DecidableEq (Var Y)]
    (A : RealCNFPNPSATDecider (Var Y))
    (vars : List (Var Y))
    (hvars : ConcreteCNF.FormulaUsesOnly (D.formula Y) vars)
    (hnodup : vars.Nodup) :
    D.projection Y (realCNFBitFixAssignment A (D.formula Y) vars) =
      publicMessage (D.publicLock Y) := by
  let α := realCNFBitFixAssignment A (D.formula Y) vars
  have hα :
      ConcreteCNF.IsSatFormula (D.formula Y) α :=
    realM4_bitFixingAssignment_satisfies
      D hY A vars hvars hnodup
  have hValid : D.validWitness Y (D.extract Y α) :=
    D.cnfSound hα
  calc
    D.projection Y α = D.witnessMessage Y (D.extract Y α) :=
      D.projection_eq_witnessMessage hα
    _ = (D.witnessCompletion (D.extract Y α) hValid).message :=
      D.witnessMessage_eq_completionMessage hValid
    _ = publicMessage (D.publicLock Y) :=
      hinvariant (D.support_publicLock hY)
        (D.witnessCompletion (D.extract Y α) hValid)

/-- Family-level packaging of the real Appendix I data needed by the CNF
bit-fixing self-reduction.  It records, for each public instance, an ordered
finite variable cover for the CNF formula and an explicit P=NP-side SAT
decider, together with a uniform program-length bound for that decider family.
-/
structure RealM4CNFUniformBitFixingData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varDecidable : (Y : Public) -> DecidableEq (Var Y)
  varOrder : (Y : Public) -> List (Var Y)
  varOrder_nodup : ∀ Y : Public, (varOrder Y).Nodup
  formulaUsesOnly :
    ∀ {Y : Public}, D.support Y ->
      ConcreteCNF.FormulaUsesOnly (D.formula Y) (varOrder Y)
  satDecider : (Y : Public) -> RealCNFPNPSATDecider (Var Y)
  programLengthBound : Nat
  satDecider_programLength_le :
    ∀ Y : Public, (satDecider Y).programLength ≤ programLengthBound

/-- Construction-side portion of the real Appendix I uniform CNF data.  It
contains the finite variable cover and decidable equality needed to run
bit-fixing, but deliberately excludes the P=NP SAT decider family. -/
structure RealM4CNFUniformSupportData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varDecidable : (Y : Public) -> DecidableEq (Var Y)
  varOrder : (Y : Public) -> List (Var Y)
  varOrder_nodup : ∀ Y : Public, (varOrder Y).Nodup
  formulaUsesOnly :
    ∀ {Y : Public}, D.support Y ->
      ConcreteCNF.FormulaUsesOnly (D.formula Y) (varOrder Y)

/-- Explicit P=NP-side SAT-decider family for the real Appendix I formulas.
This is the conditional upper-side input; it is not construction data and is
not an unconditional algorithm for SAT. -/
structure RealM4ExplicitPNPDeciderFamily
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  satDecider : (Y : Public) -> RealCNFPNPSATDecider (Var Y)
  programLengthBound : Nat
  satDecider_programLength_le :
    ∀ Y : Public, (satDecider Y).programLength ≤ programLengthBound

/-- Construction-side finite variable-family data for the real Appendix I CNF
instances.  Once the real M4 variables are supplied as finite types, the
uniform bit-fixing support package uses the canonical enumeration of all
variables, so no separate hand-written variable cover is needed. -/
structure RealM4FiniteCNFVariableFamilyData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (_D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varDecidable : (Y : Public) -> DecidableEq (Var Y)
  varFintype : (Y : Public) -> Fintype (Var Y)

namespace RealM4FiniteCNFVariableFamilyData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

/-- Canonical support data from finite real CNF variable families. -/
noncomputable def uniformSupport
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4CNFUniformSupportData D where
  varDecidable := V.varDecidable
  varOrder := fun Y =>
    letI := V.varDecidable Y
    letI := V.varFintype Y
    (Finset.univ : Finset (Var Y)).toList
  varOrder_nodup := by
    intro Y
    letI := V.varDecidable Y
    letI := V.varFintype Y
    exact Finset.nodup_toList _
  formulaUsesOnly := by
    intro Y hY clause hclause lit hlit
    letI := V.varDecidable Y
    letI := V.varFintype Y
    simp

end RealM4FiniteCNFVariableFamilyData

/-- Top-level alias: finite real CNF variables canonically supply the uniform
support data needed by bit-fixing. -/
noncomputable def realM4_uniformCNFSupport_of_finiteVariables
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4CNFUniformSupportData D :=
  V.uniformSupport

namespace RealM4CNFUniformSupportData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

/-- Combine construction-side uniform support with the explicit P=NP SAT
decider family to recover the older bundled bit-fixing package. -/
def withPNPDecider
    (B : RealM4CNFUniformSupportData D)
    (A : RealM4ExplicitPNPDeciderFamily D) :
    RealM4CNFUniformBitFixingData D where
  varDecidable := B.varDecidable
  varOrder := B.varOrder
  varOrder_nodup := B.varOrder_nodup
  formulaUsesOnly := B.formulaUsesOnly
  satDecider := A.satDecider
  programLengthBound := A.programLengthBound
  satDecider_programLength_le := A.satDecider_programLength_le

end RealM4CNFUniformSupportData

namespace RealM4CNFUniformBitFixingData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def bitFixingAssignment
    (U : RealM4CNFUniformBitFixingData D) (Y : Public) :
    ConcreteCNF.Assignment (Var Y) := by
  letI := U.varDecidable Y
  exact realCNFBitFixAssignment (U.satDecider Y) (D.formula Y) (U.varOrder Y)

theorem bitFixingAssignment_satisfies
    (U : RealM4CNFUniformBitFixingData D)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (U.bitFixingAssignment Y) := by
  dsimp [bitFixingAssignment]
  letI := U.varDecidable Y
  exact
    realM4_bitFixingAssignment_satisfies
      D hY (U.satDecider Y) (U.varOrder Y)
      (U.formulaUsesOnly hY) (U.varOrder_nodup Y)

end RealM4CNFUniformBitFixingData

theorem realM4_uniformBitFixingAssignment_satisfies
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (U : RealM4CNFUniformBitFixingData D)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (U.bitFixingAssignment Y) :=
  U.bitFixingAssignment_satisfies hY

theorem realM4_uniformBitFixingReadout_eq_publicMessage_of_publicMessageInvariant
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (U : RealM4CNFUniformBitFixingData D)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    D.projection Y (U.bitFixingAssignment Y) =
      publicMessage (D.publicLock Y) := by
  dsimp [RealM4CNFUniformBitFixingData.bitFixingAssignment]
  letI := U.varDecidable Y
  exact
    realM4_bitFixingReadout_eq_publicMessage_of_publicMessageInvariant
      D hinvariant hY (U.satDecider Y) (U.varOrder Y)
      (U.formulaUsesOnly hY) (U.varOrder_nodup Y)

theorem realM4_uniformSupportWithPNPDecider_assignment_satisfies
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (B : RealM4CNFUniformSupportData D)
    (A : RealM4ExplicitPNPDeciderFamily D)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      ((B.withPNPDecider A).bitFixingAssignment Y) :=
  realM4_uniformBitFixingAssignment_satisfies
    D (B.withPNPDecider A) hY

theorem realM4_uniformSupportWithPNPDecider_readout_eq_publicMessage
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (B : RealM4CNFUniformSupportData D)
    (A : RealM4ExplicitPNPDeciderFamily D)
    {publicMessage : PublicLock -> Message}
    (hinvariant : D.core.PublicMessageInvariant publicMessage)
    {Y : Public} (hY : D.support Y) :
    D.projection Y ((B.withPNPDecider A).bitFixingAssignment Y) =
      publicMessage (D.publicLock Y) :=
  realM4_uniformBitFixingReadout_eq_publicMessage_of_publicMessageInvariant
    D (B.withPNPDecider A) hinvariant hY

def realCNFRestrictedFormulaCompilerProgramLength : Nat :=
  1

def realCNFBitFixingDriverProgramLength : Nat :=
  1

def realCNFReadoutProgramLength : Nat :=
  1

def realCNFSelfReductionDecoderCost
    {Var : Type u} (D : RealCNFPNPSATDecider Var) : Nat :=
  D.programLength +
    realCNFRestrictedFormulaCompilerProgramLength +
      realCNFBitFixingDriverProgramLength +
        realCNFReadoutProgramLength

def realCNFConstantDecoderKpolyAt
    {Var : Type u} (D : RealCNFPNPSATDecider Var) : Nat -> Nat :=
  fun _targetBlocks => realCNFSelfReductionDecoderCost D

def realCNFLinearEtaTimes (eta : Nat) : Nat -> Nat :=
  fun targetBlocks => eta * targetBlocks

theorem realCNFConstantDecoderKpolyAt_eq
    {Var : Type u} (D : RealCNFPNPSATDecider Var) (targetBlocks : Nat) :
    realCNFConstantDecoderKpolyAt D targetBlocks =
      realCNFSelfReductionDecoderCost D :=
  rfl

def realM4UniformSelfReductionDecoderCost
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) : Nat :=
  U.programLengthBound +
    realCNFRestrictedFormulaCompilerProgramLength +
      realCNFBitFixingDriverProgramLength +
        realCNFReadoutProgramLength

theorem realM4UniformSelfReductionDecoderCost_bounds_instance
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) (Y : Public) :
    realCNFSelfReductionDecoderCost (U.satDecider Y) ≤
      realM4UniformSelfReductionDecoderCost U := by
  unfold realCNFSelfReductionDecoderCost
    realM4UniformSelfReductionDecoderCost
  exact
    Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right
          (U.satDecider_programLength_le Y)
          realCNFRestrictedFormulaCompilerProgramLength)
        realCNFBitFixingDriverProgramLength)
      realCNFReadoutProgramLength

def realM4UniformConstantDecoderKpolyAt
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) : Nat -> Nat :=
  fun _targetBlocks => realM4UniformSelfReductionDecoderCost U

theorem realM4UniformConstantDecoderKpolyAt_eq
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D) (targetBlocks : Nat) :
    realM4UniformConstantDecoderKpolyAt U targetBlocks =
      realM4UniformSelfReductionDecoderCost U :=
  rfl

structure RealCNFConstantDecoderRegime
    {Var : Type u} (F : CompressionLowerFramework)
    (D : RealCNFPNPSATDecider Var) where
  eta : Nat
  kpolyAt_eq : F.kpolyAt = realCNFConstantDecoderKpolyAt D
  etaTimes_eq : F.etaTimes = realCNFLinearEtaTimes eta
  floor_dominates_decoder :
    realCNFSelfReductionDecoderCost D < eta * F.targetBlocks

/-- Construction-side discharge of the upper inequality once the real lower
framework's `kpolyAt` is identified with the fixed CNF bit-fixing decoder.
The theorem is conditional on the explicit P=NP SAT decider object. -/
theorem realCNF_selfReductionUpperHypothesis_givenPNP
    {Var : Type u} {F : CompressionLowerFramework}
    (D : RealCNFPNPSATDecider Var)
    (R : RealCNFConstantDecoderRegime F D) :
    SelfReductionUpperHypothesis F where
  upperStrictlyBelowCompressionFloor := by
    rw [R.kpolyAt_eq, R.etaTimes_eq]
    exact R.floor_dominates_decoder

structure RealM4UniformConstantDecoderRegime
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (F : CompressionLowerFramework)
    (U : RealM4CNFUniformBitFixingData D) where
  eta : Nat
  kpolyAt_eq : F.kpolyAt = realM4UniformConstantDecoderKpolyAt U
  etaTimes_eq : F.etaTimes = realCNFLinearEtaTimes eta
  floor_dominates_decoder :
    realM4UniformSelfReductionDecoderCost U < eta * F.targetBlocks

/-- Family-level real upper-side discharge, conditional on explicit P=NP SAT
deciders and a uniform program-length bound for the Appendix I bit-fixing
decoder family.  The real lower framework must still identify its `kpolyAt`
with this uniform constant decoder cost. -/
theorem realM4_uniformSelfReductionUpperHypothesis_givenPNP
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    {F : CompressionLowerFramework}
    (U : RealM4CNFUniformBitFixingData D)
    (R : RealM4UniformConstantDecoderRegime F U) :
    SelfReductionUpperHypothesis F where
  upperStrictlyBelowCompressionFloor := by
    rw [R.kpolyAt_eq, R.etaTimes_eq]
    exact R.floor_dominates_decoder

/-! ## Real-M4 lower machine as construction data -/

/-- Explicit real lower-side machine data: the product small-success and
compression-from-success budget machine, plus the kernel/local-neutrality
certificate needed by the v13 lower-bound chain.  Constructing this for M4
must use the manuscript compression-from-success machinery, not toy budgets. -/
structure RealM4CompressionLowerMachineData where
  Predictor : Type u
  short : Predictor -> Prop
  uLocal : Predictor -> Prop
  pivotSuccess : Predictor -> Nat
  tupleSuccess : Predictor -> Nat
  halfBudget : Nat
  halfPlusSlackBudget : Nat
  smallSuccessBudget : Nat
  targetBlocks : Nat
  etaTimes : Nat -> Nat
  kpolyAt : Nat -> Nat
  productSmallSuccess :
    ∀ A : Predictor,
      pivotSuccess A ≤ halfPlusSlackBudget ->
        tupleSuccess A ≤ smallSuccessBudget
  compressionFromSuccess :
    (∀ A : Predictor, short A -> tupleSuccess A ≤ smallSuccessBudget) ->
      etaTimes targetBlocks ≤ kpolyAt targetBlocks
  exactLocalHalfBound :
    ∀ A : Predictor, uLocal A -> pivotSuccess A ≤ halfBudget
  halfBudget_le_starBudget :
    halfBudget ≤ halfPlusSlackBudget

namespace RealM4CompressionLowerMachineData

/-- Forget the real lower-machine data to the v13 lower framework. -/
def lowerFramework
    (M : RealM4CompressionLowerMachineData) :
    CompressionLowerFramework where
  Predictor := M.Predictor
  short := M.short
  uLocal := M.uLocal
  pivotSuccess := M.pivotSuccess
  tupleSuccess := M.tupleSuccess
  halfBudget := M.halfBudget
  halfPlusSlackBudget := M.halfPlusSlackBudget
  smallSuccessBudget := M.smallSuccessBudget
  targetBlocks := M.targetBlocks
  etaTimes := M.etaTimes
  kpolyAt := M.kpolyAt
  productSmallSuccess := M.productSmallSuccess
  compressionFromSuccess := M.compressionFromSuccess

/-- The same data supplies the v13 kernel-neutrality certificate. -/
def kernelNeutrality
    (M : RealM4CompressionLowerMachineData) :
    CompressionKernelNeutrality M.lowerFramework where
  exactLocalHalfBound := M.exactLocalHalfBound
  halfBudget_le_starBudget := M.halfBudget_le_starBudget

/-- Lower consequence obtained from the real lower-machine data and the
StarSW transfer input. -/
theorem compressionLower
    (M : RealM4CompressionLowerMachineData)
    (starSWHardness : CompressionStarSWHardness M.lowerFramework) :
    M.lowerFramework.etaTimes M.lowerFramework.targetBlocks ≤
      M.lowerFramework.kpolyAt M.lowerFramework.targetBlocks :=
  compressionLower_of_budget_machine
    M.kernelNeutrality starSWHardness

end RealM4CompressionLowerMachineData

/-- Top-level alias exposing the v13 lower framework supplied by the real
lower-machine data. -/
def realM4_lowerFramework_of_lowerMachineData
    (M : RealM4CompressionLowerMachineData) :
    CompressionLowerFramework :=
  M.lowerFramework

/-- Top-level alias exposing kernel neutrality supplied by the real lower
machine data. -/
def realM4_kernelNeutrality_of_lowerMachineData
    (M : RealM4CompressionLowerMachineData) :
    CompressionKernelNeutrality M.lowerFramework :=
  M.kernelNeutrality

/-! ## Real-M4 public-lock coverage as construction data -/

/-- Explicit construction data for Appendix I public-lock coverage.  For every
supported public lock, the real ensemble must construct a supported public
instance whose public-lock syntax is exactly that lock. -/
structure RealM4PublicLockCoverageData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  representative :
    ∀ {Ylock : PublicLock}, D.core.support Ylock -> Public
  representative_support :
    ∀ {Ylock : PublicLock} (hYlock : D.core.support Ylock),
      D.support (representative hYlock)
  representative_publicLock :
    ∀ {Ylock : PublicLock} (hYlock : D.core.support Ylock),
      D.publicLock (representative hYlock) = Ylock

namespace RealM4PublicLockCoverageData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

/-- The representative data discharges the Appendix D proposition-level
coverage condition used to lift Appendix I satisfiability to D.7. -/
theorem publicLockCoverage
    (C : RealM4PublicLockCoverageData D) :
    D.toAppendixDWitnessData.PublicLockCoveredBySupportedInstances := by
  intro Ylock hYlock
  exact
    ⟨C.representative hYlock,
      C.representative_support hYlock,
      C.representative_publicLock hYlock⟩

/-- Appendix I satisfiability on supported representatives gives D.7 lock
satisfiability once the coverage representative data is constructed. -/
theorem lockSatisfiable
    (C : RealM4PublicLockCoverageData D) :
    D.core.LockSatisfiable :=
  D.core_lockSatisfiable_of_publicLockCovered C.publicLockCoverage

end RealM4PublicLockCoverageData

/-- Top-level alias for the real-M4 public-lock coverage transfer. -/
theorem realM4_publicLockCoverage_of_representatives
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (C : RealM4PublicLockCoverageData D) :
    D.toAppendixDWitnessData.PublicLockCoveredBySupportedInstances :=
  C.publicLockCoverage

theorem realM4_lockSatisfiable_of_publicLockCoverageData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (C : RealM4PublicLockCoverageData D) :
    D.core.LockSatisfiable :=
  C.lockSatisfiable

/-! ## Real-M4 locked-message rigidity as construction data -/

/-- Explicit construction data for Appendix D.8.  The real ensemble supplies a
public message for each public lock and proves that every accepted locked
completion over a supported lock reads exactly that message. -/
structure RealM4LockedMessageRigidityData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    (C : AppendixDLockedCore PublicLock Quotient LockAux Message) where
  publicMessage : PublicLock -> Message
  completionMessage_eq_publicMessage :
    C.PublicMessageInvariant publicMessage

namespace RealM4LockedMessageRigidityData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {C : AppendixDLockedCore PublicLock Quotient LockAux Message}

/-- The data directly supplies the public-message invariant used by the real
single-message readout spine. -/
theorem publicMessageInvariant
    (R : RealM4LockedMessageRigidityData C) :
    C.PublicMessageInvariant R.publicMessage :=
  R.completionMessage_eq_publicMessage

/-- The old Appendix D.8 proposition follows from the explicit locked-message
data. -/
theorem lockedMessageRigidity
    (R : RealM4LockedMessageRigidityData C) :
    C.LockedMessageRigidity :=
  C.lockedMessageRigidity_of_publicMessageInvariant
    R.publicMessageInvariant

/-- D.7 satisfiability plus D.8 rigidity construct the explicit
locked-message data by choosing the common message of each supported lock.
The default message is used only outside support. -/
noncomputable def ofLockedRigidity
    (defaultMessage : Message)
    (lockSatisfiable : C.LockSatisfiable)
    (lockedMessageRigidity : C.LockedMessageRigidity) :
    RealM4LockedMessageRigidityData C where
  publicMessage :=
    C.publicMessageOfLockedRigidity
      defaultMessage lockSatisfiable lockedMessageRigidity
  completionMessage_eq_publicMessage :=
    C.publicMessageInvariant_of_lockSatisfiable_of_lockedMessageRigidity
      defaultMessage lockSatisfiable lockedMessageRigidity

end RealM4LockedMessageRigidityData

/-- Top-level alias exposing the public-message invariant supplied by the real
locked-message data. -/
theorem realM4_publicMessageInvariant_of_lockedMessageData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {C : AppendixDLockedCore PublicLock Quotient LockAux Message}
    (R : RealM4LockedMessageRigidityData C) :
    C.PublicMessageInvariant R.publicMessage :=
  R.publicMessageInvariant

/-- Top-level alias exposing D.8 as a consequence of the real locked-message
data. -/
theorem realM4_lockedMessageRigidity_of_lockedMessageData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {C : AppendixDLockedCore PublicLock Quotient LockAux Message}
    (R : RealM4LockedMessageRigidityData C) :
    C.LockedMessageRigidity :=
  R.lockedMessageRigidity

/-- Public-lock coverage supplies D.7; together with D.8 this constructs the
explicit locked-message data used by the real single-message and self-reduction
readout adapters. -/
noncomputable def realM4_lockedMessageData_of_coverageDataAndRigidity
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity) :
    RealM4LockedMessageRigidityData D.core :=
  RealM4LockedMessageRigidityData.ofLockedRigidity
    defaultMessage coverageData.lockSatisfiable lockedMessageRigidity

/-! ## Real-M4 self-reduction upper discharge package -/

/-- Real Appendix I package that discharges the upper self-reduction side once
the public-message invariant, uniform bit-fixing data, and real constant
decoder regime have all been constructed.  The SAT decider family remains an
explicit P=NP-side input inside `uniformBitFixing`; this is not an
unconditional upper bound. -/
structure RealM4SelfReductionUpperDischarge
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (F : CompressionLowerFramework) where
  publicMessage : PublicLock -> Message
  publicMessageInvariant : D.core.PublicMessageInvariant publicMessage
  uniformBitFixing : RealM4CNFUniformBitFixingData D
  constantDecoderRegime :
    RealM4UniformConstantDecoderRegime F uniformBitFixing

/-- Same real upper-side discharge, but with the construction-side CNF support
and the P=NP SAT decider family split into separate fields.  This is the
preferred package for the real endgame audit because the conditional
assumption is a visible object. -/
structure RealM4SelfReductionUpperExplicitPNPDischarge
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (F : CompressionLowerFramework) where
  publicMessage : PublicLock -> Message
  publicMessageInvariant : D.core.PublicMessageInvariant publicMessage
  uniformSupport : RealM4CNFUniformSupportData D
  pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D
  constantDecoderRegime :
    RealM4UniformConstantDecoderRegime F
      (uniformSupport.withPNPDecider pnpDeciderFamily)

namespace RealM4SelfReductionUpperDischarge

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}
variable {F : CompressionLowerFramework}

def selfReductionUpper
    (S : RealM4SelfReductionUpperDischarge D F) :
    SelfReductionUpperHypothesis F :=
  realM4_uniformSelfReductionUpperHypothesis_givenPNP
    S.uniformBitFixing S.constantDecoderRegime

theorem bitFixingAssignment_satisfies
    (S : RealM4SelfReductionUpperDischarge D F)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (S.uniformBitFixing.bitFixingAssignment Y) :=
  realM4_uniformBitFixingAssignment_satisfies
    D S.uniformBitFixing hY

theorem bitFixingReadout_eq_publicMessage
    (S : RealM4SelfReductionUpperDischarge D F)
    {Y : Public} (hY : D.support Y) :
    D.projection Y (S.uniformBitFixing.bitFixingAssignment Y) =
      S.publicMessage (D.publicLock Y) :=
  realM4_uniformBitFixingReadout_eq_publicMessage_of_publicMessageInvariant
    D S.uniformBitFixing S.publicMessageInvariant hY

theorem instanceDecoderCost_le_uniform
    (S : RealM4SelfReductionUpperDischarge D F) (Y : Public) :
    realCNFSelfReductionDecoderCost (S.uniformBitFixing.satDecider Y) ≤
      realM4UniformSelfReductionDecoderCost S.uniformBitFixing :=
  realM4UniformSelfReductionDecoderCost_bounds_instance
    S.uniformBitFixing Y

end RealM4SelfReductionUpperDischarge

namespace RealM4SelfReductionUpperExplicitPNPDischarge

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}
variable {F : CompressionLowerFramework}

/-- Build the explicit-P=NP upper discharge package from the real Appendix D
D.7/D.8 locked-core obligations, instead of assuming a public-message
invariant as an extra construction input.  The default message is used only on
unsupported public locks. -/
noncomputable def ofLockedRigidity
    (defaultMessage : Message)
    (lockSatisfiable : D.core.LockSatisfiable)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider pnpDeciderFamily)) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F where
  publicMessage :=
    D.core.publicMessageOfLockedRigidity
      defaultMessage lockSatisfiable lockedMessageRigidity
  publicMessageInvariant :=
    D.core.publicMessageInvariant_of_lockSatisfiable_of_lockedMessageRigidity
      defaultMessage lockSatisfiable lockedMessageRigidity
  uniformSupport := uniformSupport
  pnpDeciderFamily := pnpDeciderFamily
  constantDecoderRegime := constantDecoderRegime

/-- Build the explicit-P=NP upper discharge package from Appendix I support
coverage and D.8 rigidity.  Appendix I satisfiability on support supplies D.7
once every supported public lock is represented by a supported public
instance. -/
noncomputable def ofCoveredLocksAndRigidity
    (defaultMessage : Message)
    (publicLockCoverage :
      D.toAppendixDWitnessData.PublicLockCoveredBySupportedInstances)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider pnpDeciderFamily)) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  ofLockedRigidity
    defaultMessage
    (D.core_lockSatisfiable_of_publicLockCovered publicLockCoverage)
    lockedMessageRigidity
    uniformSupport pnpDeciderFamily constantDecoderRegime

/-- Build the explicit-P=NP upper discharge package from public-lock
representative data and D.8 rigidity.  The representative data is the concrete
construction obligation behind public-lock coverage. -/
noncomputable def ofCoverageDataAndRigidity
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider pnpDeciderFamily)) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  ofCoveredLocksAndRigidity
    defaultMessage
    coverageData.publicLockCoverage
    lockedMessageRigidity
    uniformSupport pnpDeciderFamily constantDecoderRegime

/-- Build the explicit-P=NP upper discharge package directly from the real
locked-message data.  The public message is supplied by the construction data
itself; no choice of a supported completion is used to define it. -/
def ofLockedMessageData
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider pnpDeciderFamily)) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F where
  publicMessage := lockedMessageData.publicMessage
  publicMessageInvariant := lockedMessageData.publicMessageInvariant
  uniformSupport := uniformSupport
  pnpDeciderFamily := pnpDeciderFamily
  constantDecoderRegime := constantDecoderRegime

/-- Coverage-data staging wrapper for the direct locked-message-data upper
package.  Coverage remains an exposed real construction obligation for D.7,
while the upper readout side uses the explicit public-message data. -/
def ofCoverageDataAndLockedMessageData
    (_coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider pnpDeciderFamily)) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  ofLockedMessageData
    lockedMessageData uniformSupport pnpDeciderFamily constantDecoderRegime

def uniformBitFixing
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F) :
    RealM4CNFUniformBitFixingData D :=
  S.uniformSupport.withPNPDecider S.pnpDeciderFamily

def toDischarge
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F) :
    RealM4SelfReductionUpperDischarge D F where
  publicMessage := S.publicMessage
  publicMessageInvariant := S.publicMessageInvariant
  uniformBitFixing := S.uniformBitFixing
  constantDecoderRegime := by
    dsimp [uniformBitFixing]
    exact S.constantDecoderRegime

def selfReductionUpper
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F) :
    SelfReductionUpperHypothesis F :=
  S.toDischarge.selfReductionUpper

theorem bitFixingAssignment_satisfies
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F)
    {Y : Public} (hY : D.support Y) :
    ConcreteCNF.IsSatFormula (D.formula Y)
      (S.uniformBitFixing.bitFixingAssignment Y) := by
  simpa [uniformBitFixing] using
    realM4_uniformSupportWithPNPDecider_assignment_satisfies
      S.uniformSupport S.pnpDeciderFamily hY

theorem bitFixingReadout_eq_publicMessage
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F)
    {Y : Public} (hY : D.support Y) :
    D.projection Y (S.uniformBitFixing.bitFixingAssignment Y) =
      S.publicMessage (D.publicLock Y) := by
  simpa [uniformBitFixing] using
    realM4_uniformSupportWithPNPDecider_readout_eq_publicMessage
      S.uniformSupport S.pnpDeciderFamily S.publicMessageInvariant hY

theorem instanceDecoderCost_le_uniform
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F) (Y : Public) :
    realCNFSelfReductionDecoderCost (S.uniformBitFixing.satDecider Y) ≤
      realM4UniformSelfReductionDecoderCost S.uniformBitFixing := by
  simpa [uniformBitFixing] using
    realM4UniformSelfReductionDecoderCost_bounds_instance
      (S.uniformSupport.withPNPDecider S.pnpDeciderFamily) Y

end RealM4SelfReductionUpperExplicitPNPDischarge

/-- Combined checked output of the real Appendix I self-reduction package:
bit-fixing yields a satisfying assignment, its readout is the public message,
each instance decoder is bounded by the uniform constant decoder, and the
`SelfReductionUpperHypothesis` follows for the real lower framework. -/
theorem realM4_selfReductionUpperDischarge_assignment_readout_cost_and_upper
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    {F : CompressionLowerFramework}
    (S : RealM4SelfReductionUpperDischarge D F) :
    (∀ {Y : Public}, D.support Y ->
      ConcreteCNF.IsSatFormula (D.formula Y)
        (S.uniformBitFixing.bitFixingAssignment Y)) ∧
    (∀ {Y : Public}, D.support Y ->
      D.projection Y (S.uniformBitFixing.bitFixingAssignment Y) =
        S.publicMessage (D.publicLock Y)) ∧
    (∀ Y : Public,
      realCNFSelfReductionDecoderCost (S.uniformBitFixing.satDecider Y) ≤
        realM4UniformSelfReductionDecoderCost S.uniformBitFixing) ∧
    SelfReductionUpperHypothesis F := by
  exact
    ⟨fun {Y} hY =>
        RealM4SelfReductionUpperDischarge.bitFixingAssignment_satisfies
          S hY,
      fun {Y} hY =>
        RealM4SelfReductionUpperDischarge.bitFixingReadout_eq_publicMessage
          S hY,
      fun Y =>
        RealM4SelfReductionUpperDischarge.instanceDecoderCost_le_uniform
          S Y,
      RealM4SelfReductionUpperDischarge.selfReductionUpper S⟩

/-- Combined checked output of the explicit-P=NP real Appendix I
self-reduction package.  The SAT decider family is exposed as
`S.pnpDeciderFamily`; the result remains conditional on that object. -/
theorem realM4_selfReductionUpperExplicitPNPDischarge_assignment_readout_cost_and_upper
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    {F : CompressionLowerFramework}
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D F) :
    (∀ {Y : Public}, D.support Y ->
      ConcreteCNF.IsSatFormula (D.formula Y)
        (S.uniformBitFixing.bitFixingAssignment Y)) ∧
    (∀ {Y : Public}, D.support Y ->
      D.projection Y (S.uniformBitFixing.bitFixingAssignment Y) =
        S.publicMessage (D.publicLock Y)) ∧
    (∀ Y : Public,
      realCNFSelfReductionDecoderCost (S.uniformBitFixing.satDecider Y) ≤
        realM4UniformSelfReductionDecoderCost S.uniformBitFixing) ∧
    SelfReductionUpperHypothesis F := by
  exact
    ⟨fun {Y} hY =>
        RealM4SelfReductionUpperExplicitPNPDischarge.bitFixingAssignment_satisfies
          S hY,
      fun {Y} hY =>
        RealM4SelfReductionUpperExplicitPNPDischarge.bitFixingReadout_eq_publicMessage
          S hY,
      fun Y =>
        RealM4SelfReductionUpperExplicitPNPDischarge.instanceDecoderCost_le_uniform
          S Y,
      RealM4SelfReductionUpperExplicitPNPDischarge.selfReductionUpper S⟩

def realM4PublicMessageInvariantConstructionInputs : List String := [
  "defaultMessageForUnsupportedLocks",
  "lockSatisfiable",
  "lockedMessageRigidity"
]

theorem realM4PublicMessageInvariantConstructionInputs_exact :
    realM4PublicMessageInvariantConstructionInputs =
      [ "defaultMessageForUnsupportedLocks",
        "lockSatisfiable",
        "lockedMessageRigidity" ] := by
  rfl

def realM4PublicLockCoverageDataConstructionInputs : List String := [
  "publicLockRepresentative",
  "publicLockRepresentativeSupport",
  "publicLockRepresentativeSyntax"
]

theorem realM4PublicLockCoverageDataConstructionInputs_exact :
    realM4PublicLockCoverageDataConstructionInputs =
      [ "publicLockRepresentative",
        "publicLockRepresentativeSupport",
        "publicLockRepresentativeSyntax" ] := by
  rfl

def realM4LockedMessageRigidityDataConstructionInputs : List String := [
  "publicMessageOfLock",
  "lockedCompletionMessageEq"
]

theorem realM4LockedMessageRigidityDataConstructionInputs_exact :
    realM4LockedMessageRigidityDataConstructionInputs =
      [ "publicMessageOfLock",
        "lockedCompletionMessageEq" ] := by
  rfl

def realM4FiniteCNFVariableFamilyDataConstructionInputs : List String := [
  "varDecidable",
  "varFintype"
]

theorem realM4FiniteCNFVariableFamilyDataConstructionInputs_exact :
    realM4FiniteCNFVariableFamilyDataConstructionInputs =
      [ "varDecidable",
        "varFintype" ] := by
  rfl

def realM4CompressionLowerMachineDataConstructionInputs : List String := [
  "predictorClass",
  "shortPredicate",
  "localPredicate",
  "pivotSuccess",
  "tupleSuccess",
  "lowerBudgets",
  "targetBlocks",
  "etaTimes",
  "kpolyAt",
  "productSmallSuccess",
  "compressionFromSuccess",
  "kernelLocalHalfBound"
]

theorem realM4CompressionLowerMachineDataConstructionInputs_exact :
    realM4CompressionLowerMachineDataConstructionInputs =
      [ "predictorClass",
        "shortPredicate",
        "localPredicate",
        "pivotSuccess",
        "tupleSuccess",
        "lowerBudgets",
        "targetBlocks",
        "etaTimes",
        "kpolyAt",
        "productSmallSuccess",
        "compressionFromSuccess",
        "kernelLocalHalfBound" ] := by
  rfl

def realM4LockSatisfiableConstructionInputs : List String := [
  "publicLockCoverageData",
  "appendixISatOnSupport"
]

theorem realM4LockSatisfiableConstructionInputs_exact :
    realM4LockSatisfiableConstructionInputs =
      [ "publicLockCoverageData",
        "appendixISatOnSupport" ] := by
  rfl

def realM4SelfReductionUpperDischargePrerequisites : List String := [
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "uniformCNFBitFixingPackage",
  "realCompressionLowerFramework"
]

theorem realM4SelfReductionUpperDischargePrerequisites_exact :
    realM4SelfReductionUpperDischargePrerequisites =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFBitFixingPackage",
        "realCompressionLowerFramework" ] := by
  rfl

def realM4SelfReductionUpperConditionalInputs : List String := [
  "pnpDeciderFamily"
]

theorem realM4SelfReductionUpperConditionalInputs_exact :
    realM4SelfReductionUpperConditionalInputs =
      [ "pnpDeciderFamily" ] := by
  rfl

def realM4SelfReductionUpperExplicitPNPConstructionInputs : List String := [
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "uniformCNFSupportData",
  "realCompressionLowerFramework"
]

theorem realM4SelfReductionUpperExplicitPNPConstructionInputs_exact :
    realM4SelfReductionUpperExplicitPNPConstructionInputs =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "realCompressionLowerFramework" ] := by
  rfl

def realM4SelfReductionUpperExplicitPNPConditionalInputs : List String := [
  "pnpDeciderFamily"
]

theorem realM4SelfReductionUpperExplicitPNPConditionalInputs_exact :
    realM4SelfReductionUpperExplicitPNPConditionalInputs =
      [ "pnpDeciderFamily" ] := by
  rfl

/-! ## Real-M4 endgame staging without toy parameters -/

/-- CD-ENF atom completeness is already a generic theorem of the evidence
semantics.  It is not a separate real-M4 mathematical input. -/
theorem realM4_atomCompleteness_of_CDENF
    {Omega : Type u} {Neutral : Type v} {Safe : Type w}
    {Gauge : Type x}
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge) :
    ∀ E : RawEvidence Neutral Safe Gauge,
      semantics.SatNormal (CDENF E) = semantics.SatRaw E := by
  intro E
  exact CDENF_semantics semantics E

/-- Gauge faithfulness for a single gauge leaf is the gauge case of CD-ENF
semantics.  The real construction must still build the gauge predicate and
product law, but not a separate normalizer-correctness proof. -/
theorem realM4_gaugeFaithfulness_of_CDENF
    {Omega : Type u} {Neutral : Type v} {Safe : Type w}
    {Gauge : Type x}
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge) :
    ∀ gamma : Gauge,
      semantics.SatNormal (CDENF (.gauge gamma)) =
        semantics.gaugeSat gamma := by
  intro gamma
  rfl

/-- Mechanical real-interface data for the v13 clash interface, deliberately
excluding the three analytic frontier fields.  Constructing this data for the
real M4 ensemble is a construction obligation; it is not an irreducible
mathematical input. -/
structure RealM4MechanicalInterfaceData
    (Omega : Type u) [Fintype Omega] [Nonempty Omega]
    (Public : Type v) (Neutral : Type w) (Safe : Type x) (Gauge : Type y)
    (Transcript : Type z) [DecidableEq Transcript]
    (Pair : Type a) [Fintype Pair]
    (Stage : Type b) (Branch : Type c)
    (HistoryAtom : Type d) (Pivot : Type e)
    (Observer : Type f) (Output : Type f) (Skeleton : Type w) where
  law : FiniteRationalLaw Omega
  target : Omega -> Bool
  publicInput : Omega -> Public
  neutralSkeleton : Omega -> Skeleton
  oppositeSupport : Omega -> Omega -> Prop
  transcript : Omega -> Transcript
  observerBit : Transcript -> Bool
  phaseA :
    EvidenceSpineBound law target transcript observerBit Pair Stage Branch
  semantics : EvidenceSemantics Omega Neutral Safe Gauge
  observerEvidence :
    ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge
  historyField : FiniteSigmaField.{u, d} Omega
  pivotSummary : Omega -> Pivot
  epsMix : Rat
  safeCost : Safe -> Rat
  safeBudget : Rat
  gaugeIncidence : Gauge -> Nat
  gaugeBound : Nat
  singleMessage :
    ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1
  hiddenGaugeProduct :
    ∀ gamma omega, semantics.gaugeSat gamma omega
  noPublicTargetTags :
    PairNeutral oppositeSupport neutralSkeleton ∧
      HasMessageOppositePair oppositeSupport target ∧
        ¬ ∃ f : Skeleton -> Bool, ∀ omega, target omega = f (neutralSkeleton omega)
  atomCompleteness :
    ∀ E : RawEvidence Neutral Safe Gauge,
      semantics.SatNormal (CDENF E) = semantics.SatRaw E
  gaugeFaithfulness :
    ∀ gamma : Gauge,
      semantics.SatNormal (CDENF (.gauge gamma)) =
        semantics.gaugeSat gamma
  admissibleHistories :
    BalancedBit target ∧
      BalancedConditioning (Omega := Omega) historyField target

namespace RealM4MechanicalInterfaceData

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]
variable {Public : Type v} {Neutral : Type w} {Safe : Type x}
variable {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
variable {Pair : Type a} [Fintype Pair] {Stage : Type b} {Branch : Type c}
variable {HistoryAtom : Type d} {Pivot : Type e}
variable {Observer : Type f} {Output : Type f} {Skeleton : Type w}

/-- Build real mechanical interface data while deriving the CD-ENF structural
fields from the generic normalizer semantics.  The remaining arguments are the
actual real construction obligations; `atomCompleteness` and
`gaugeFaithfulness` are filled by `CDENF_semantics`. -/
def ofCDENFComponents
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target) :
    RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton where
  law := law
  target := target
  publicInput := publicInput
  neutralSkeleton := neutralSkeleton
  oppositeSupport := oppositeSupport
  transcript := transcript
  observerBit := observerBit
  phaseA := phaseA
  semantics := semantics
  observerEvidence := observerEvidence
  historyField := historyField
  pivotSummary := pivotSummary
  epsMix := epsMix
  safeCost := safeCost
  safeBudget := safeBudget
  gaugeIncidence := gaugeIncidence
  gaugeBound := gaugeBound
  singleMessage := singleMessage
  hiddenGaugeProduct := hiddenGaugeProduct
  noPublicTargetTags := noPublicTargetTags
  atomCompleteness := realM4_atomCompleteness_of_CDENF semantics
  gaugeFaithfulness := realM4_gaugeFaithfulness_of_CDENF semantics
  admissibleHistories := admissibleHistories

/--
Specialized real-public-surface constructor for the adjusted linear
no-target-rows spine.  The full public input determines the target bit, while
the neutral skeleton and chosen public-coordinate history field use the
checked no-target-rows cardinality proofs.  Thus `noPublicTargetTags` and
`admissibleHistories` are derived from the public-surface certificate instead
of being passed as opaque mechanical fields.

This is still a transfer constructor for the real linear public surface, not a
claim that the full M4 ensemble has already been identified with that surface.
-/
noncomputable def ofNoTargetRowsPublicCoordinateCDENFComponents
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega) :
    RealM4MechanicalInterfaceData
      (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
      Neutral Safe Gauge Transcript Pair Stage Branch HistoryAtom Pivot
      Observer Output (V13RealLinearNoTargetRowsMap m i₀) :=
  ofCDENFComponents
    law
    (@v13RealLinearNoTargetRowsTargetBit m i₀)
    (@v13RealLinearNoTargetRowsPublicInput m i₀)
    (@v13RealLinearNoTargetRowsNeutralSkeleton m i₀)
    (@v13RealLinearNoTargetRowsOppositeSupport m i₀)
    transcript observerBit phaseA semantics observerEvidence
    (v13RealLinearNoTargetRowsPublicCoordinateField (i₀ := i₀)
      coordinate)
    pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
    (v13RealLinearNoTargetRows_singleMessage i₀)
    hiddenGaugeProduct
    (v13RealLinearNoTargetRows_noPublicTargetTags i₀ hm.out)
    (v13RealLinearNoTargetRows_publicCoordinate_admissible
      i₀ coordinate hm.out)

/-- Fill the real mechanical interface with the three analytic frontier
fields.  This is the exact point where safe-QSSM, bounded gauge incidence, and
boundary mixing enter the v13 `GaugeBufferedLockedInterface`. -/
def withAnalyticFrontier
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix) :
    GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton where
  law := M.law
  target := M.target
  publicInput := M.publicInput
  neutralSkeleton := M.neutralSkeleton
  oppositeSupport := M.oppositeSupport
  transcript := M.transcript
  observerBit := M.observerBit
  phaseA := M.phaseA
  semantics := M.semantics
  observerEvidence := M.observerEvidence
  historyField := M.historyField
  pivotSummary := M.pivotSummary
  epsMix := M.epsMix
  safeCost := M.safeCost
  safeBudget := M.safeBudget
  gaugeIncidence := M.gaugeIncidence
  gaugeBound := M.gaugeBound
  singleMessage := M.singleMessage
  hiddenGaugeProduct := M.hiddenGaugeProduct
  noPublicTargetTags := M.noPublicTargetTags
  atomCompleteness := M.atomCompleteness
  gaugeFaithfulness := M.gaugeFaithfulness
  safeQSSM := safeQSSM
  boundedGaugeIncidence := boundedGaugeIncidence
  boundaryMixing := boundaryMixing
  admissibleHistories := M.admissibleHistories

/-- Real safe-qSSM analytic frontier field over explicit mechanical data. -/
structure SafeQSSMFrontier
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton) :
    Prop where
  safeQSSM :
    ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget

/-- Real bounded-gauge-incidence analytic frontier field over explicit
mechanical data. -/
structure BoundedGaugeIncidenceFrontier
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton) :
    Prop where
  boundedGaugeIncidence :
    ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound

/-- Real boundary-mixing analytic frontier field.  The strict smallness bound
is part of the boundary-mixing frontier, not a separate construction theorem. -/
structure BoundaryMixingFrontier
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton) :
    Prop where
  boundaryMixing : BoundaryMixingBound M.target M.pivotSummary M.epsMix
  epsSmall : M.epsMix < (1 / 2 : Rat)

/-- Fill the real mechanical interface from the three named analytic frontier
fields. -/
def withRealAnalyticFrontier
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (safeQSSM : SafeQSSMFrontier M)
    (boundedGaugeIncidence : BoundedGaugeIncidenceFrontier M)
    (boundaryMixing : BoundaryMixingFrontier M) :
    GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton :=
  M.withAnalyticFrontier
    safeQSSM.safeQSSM
    boundedGaugeIncidence.boundedGaugeIncidence
    boundaryMixing.boundaryMixing

end RealM4MechanicalInterfaceData

/-- Mechanical data needed to assemble the real conditional endgame once the
three analytic fields and the P=NP-side self-reduction package are supplied.
This still does not construct the real M4 ensemble; it names the construction
certificate that must be produced before the final theorem can expose only the
four irreducible mathematical inputs. -/
structure RealM4EndgameMechanicalData
    (Omega : Type u) [Fintype Omega] [Nonempty Omega]
    (Public : Type v) (Neutral : Type w) (Safe : Type x) (Gauge : Type y)
    (Transcript : Type z) [DecidableEq Transcript]
    (Pair : Type a) [Fintype Pair]
    (Stage : Type b) (Branch : Type c)
    (HistoryAtom : Type d) (Pivot : Type e)
    (Observer : Type f) (Output : Type f) (Skeleton : Type w) where
  interfaceData :
    RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton
  fixedGapBudget : Rat
  phaseABudget :
    (1 / 2 : Rat) * interfaceData.phaseA.telescoping.derivativeSum ≤
      fixedGapBudget
  epsSmall : interfaceData.epsMix < (1 / 2 : Rat)
  lowerFramework : CompressionLowerFramework
  kernelNeutrality : CompressionKernelNeutrality lowerFramework

namespace RealM4EndgameMechanicalData

variable {Omega : Type u} [Fintype Omega] [Nonempty Omega]
variable {Public : Type v} {Neutral : Type w} {Safe : Type x}
variable {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
variable {Pair : Type a} [Fintype Pair] {Stage : Type b} {Branch : Type c}
variable {HistoryAtom : Type d} {Pivot : Type e}
variable {Observer : Type f} {Output : Type f} {Skeleton : Type w}

def ofComponents
    (interfaceData :
      RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
        Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
        Skeleton)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * interfaceData.phaseA.telescoping.derivativeSum ≤
        fixedGapBudget)
    (epsSmall : interfaceData.epsMix < (1 / 2 : Rat))
    (lowerFramework : CompressionLowerFramework)
    (kernelNeutrality : CompressionKernelNeutrality lowerFramework) :
    RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
      Skeleton where
  interfaceData := interfaceData
  fixedGapBudget := fixedGapBudget
  phaseABudget := phaseABudget
  epsSmall := epsSmall
  lowerFramework := lowerFramework
  kernelNeutrality := kernelNeutrality

/-- Assemble endgame mechanical data from explicit interface data and the real
lower-machine construction data. -/
def ofComponentsWithLowerMachine
    (interfaceData :
      RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
        Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
        Skeleton)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * interfaceData.phaseA.telescoping.derivativeSum ≤
        fixedGapBudget)
    (epsSmall : interfaceData.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData) :
    RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
      Skeleton :=
  ofComponents
    interfaceData fixedGapBudget phaseABudget epsSmall
    lowerMachine.lowerFramework lowerMachine.kernelNeutrality

/-- Canonical Phase-A fixed gap budget: choose the declared budget to be
exactly the half-derivative bound supplied by the v13 Phase-A lemma. -/
noncomputable def canonicalFixedGapBudget
    (interfaceData :
      RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
        Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
        Skeleton) : Rat :=
  (1 / 2 : Rat) * interfaceData.phaseA.telescoping.derivativeSum

/-- With the canonical fixed gap budget, the Phase-A budget inequality is a
definition-level numeric fact rather than a separate construction input. -/
theorem canonicalPhaseABudget
    (interfaceData :
      RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
        Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
        Skeleton) :
    (1 / 2 : Rat) * interfaceData.phaseA.telescoping.derivativeSum ≤
      canonicalFixedGapBudget interfaceData := by
  exact le_rfl

/-- Assemble endgame mechanical data while discharging the Phase-A budget by
the canonical fixed-gap choice.  The strict `epsSmall` bound and lower-machine
data remain real construction obligations. -/
noncomputable def ofComponentsWithCanonicalGap
    (interfaceData :
      RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
        Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
        Skeleton)
    (epsSmall : interfaceData.epsMix < (1 / 2 : Rat))
    (lowerFramework : CompressionLowerFramework)
    (kernelNeutrality : CompressionKernelNeutrality lowerFramework) :
    RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
      Skeleton :=
  ofComponents
    interfaceData (canonicalFixedGapBudget interfaceData)
    (canonicalPhaseABudget interfaceData) epsSmall lowerFramework
    kernelNeutrality

/-- Lower-machine version of `ofComponentsWithCanonicalGap`. -/
noncomputable def ofComponentsWithLowerMachineCanonicalGap
    (interfaceData :
      RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
        Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
        Skeleton)
    (epsSmall : interfaceData.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData) :
    RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
      Skeleton :=
  ofComponentsWithCanonicalGap
    interfaceData epsSmall lowerMachine.lowerFramework
    lowerMachine.kernelNeutrality

/-- Build the real endgame mechanical package directly from CD-ENF component
data.  This avoids reintroducing `atomCompleteness` and `gaugeFaithfulness` as
hidden fields of a prebuilt `RealM4MechanicalInterfaceData`; both are derived
from the generic CD-ENF semantics theorem. -/
def ofCDENFComponents
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerFramework : CompressionLowerFramework)
    (kernelNeutrality : CompressionKernelNeutrality lowerFramework) :
    RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
      Skeleton where
  interfaceData :=
    RealM4MechanicalInterfaceData.ofCDENFComponents
      law target publicInput neutralSkeleton oppositeSupport transcript
      observerBit phaseA semantics observerEvidence historyField pivotSummary
      epsMix safeCost safeBudget gaugeIncidence gaugeBound singleMessage
      hiddenGaugeProduct noPublicTargetTags admissibleHistories
  fixedGapBudget := fixedGapBudget
  phaseABudget := by
    simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
      phaseABudget
  epsSmall := by
    simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using epsSmall
  lowerFramework := lowerFramework
  kernelNeutrality := kernelNeutrality

/-- Build the real endgame mechanical package directly from CD-ENF component
data and the explicit lower-machine construction data. -/
def ofCDENFComponentsWithLowerMachine
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData) :
    RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output
      Skeleton :=
  ofCDENFComponents
    law target publicInput neutralSkeleton oppositeSupport transcript
    observerBit phaseA semantics observerEvidence historyField pivotSummary
    epsMix safeCost safeBudget gaugeIncidence gaugeBound singleMessage
    hiddenGaugeProduct noPublicTargetTags admissibleHistories
    fixedGapBudget phaseABudget epsSmall
    lowerMachine.lowerFramework lowerMachine.kernelNeutrality

def interfaceWithAnalyticFrontier
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
      Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton :=
  C.interfaceData.withAnalyticFrontier
    safeQSSM boundedGaugeIncidence boundaryMixing

def parameterRecordWithUpper
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (upper : SelfReductionUpperHypothesis C.lowerFramework)
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    ParameterRecord
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing) where
  fixedGapBudget := C.fixedGapBudget
  phaseABudget := by
    simpa [interfaceWithAnalyticFrontier,
      RealM4MechanicalInterfaceData.withAnalyticFrontier] using
      C.phaseABudget
  epsSmall := by
    simpa [interfaceWithAnalyticFrontier,
      RealM4MechanicalInterfaceData.withAnalyticFrontier] using
      C.epsSmall
  lowerFramework := C.lowerFramework
  kernelNeutrality := C.kernelNeutrality
  starSWHardness := starSWHardness
  selfReductionUpper := upper

def parameterRecord
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (S : RealM4SelfReductionUpperDischarge D C.lowerFramework)
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    ParameterRecord
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing) :=
  C.parameterRecordWithUpper
    (RealM4SelfReductionUpperDischarge.selfReductionUpper S)
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

def parameterRecordExplicitPNP
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D C.lowerFramework)
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    ParameterRecord
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing) :=
  C.parameterRecordWithUpper
    (RealM4SelfReductionUpperExplicitPNPDischarge.selfReductionUpper S)
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

end RealM4EndgameMechanicalData

/--
Real-ensemble conditional endgame staging theorem.  Given a construction
certificate for the real mechanical interface/lower framework, the explicit
P=NP-side self-reduction discharge package, StarSW hardness, and the three
analytic frontier fields, the v13 `UpperLowerClash` follows.

This is not a proof of `P != NP`, and it does not yet construct the manuscript
M4 ensemble.  It records the wiring that will become the top-level theorem
once the construction certificate is supplied by real M4 proofs.
-/
theorem realM4_conditionalClash_from_endgameMechanicalData
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (S : RealM4SelfReductionUpperDischarge D C.lowerFramework)
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    UpperLowerClash
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      (C.parameterRecord S starSWHardness
        safeQSSM boundedGaugeIncidence boundaryMixing) :=
  v13_upperLowerClash
    (C.interfaceWithAnalyticFrontier
      safeQSSM boundedGaugeIncidence boundaryMixing)
    (C.parameterRecord S starSWHardness
      safeQSSM boundedGaugeIncidence boundaryMixing)

/--
Explicit-P=NP version of the real-ensemble conditional endgame staging
theorem.  The self-reduction upper side is supplied by a package whose SAT
decider family is a named P=NP-side field, while the lower content remains
StarSW hardness plus the three analytic frontier fields.

This is not a proof of `P != NP`, and it does not yet construct the manuscript
M4 ensemble.  It records the conditional wiring to be used once the real M4
construction certificates are supplied.
-/
theorem realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D C.lowerFramework)
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    UpperLowerClash
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      (C.parameterRecordExplicitPNP S starSWHardness
        safeQSSM boundedGaugeIncidence boundaryMixing) :=
  v13_upperLowerClash
    (C.interfaceWithAnalyticFrontier
      safeQSSM boundedGaugeIncidence boundaryMixing)
    (C.parameterRecordExplicitPNP S starSWHardness
      safeQSSM boundedGaugeIncidence boundaryMixing)

/--
Covered-locks version of the real-ensemble conditional endgame staging
theorem.  Instead of assuming the explicit-P=NP upper discharge package as an
input, this theorem constructs it from the exposed real Appendix I/D
construction ingredients: public-lock support coverage, D.8 locked-message
rigidity, uniform CNF support, the constant decoder regime, and the explicit
P=NP-side SAT decider family.

This is still conditional staging for the real M4 spine, not a proof of
`P != NP`; the listed construction ingredients remain to be proved for the
manuscript ensemble.
-/
theorem realM4_conditionalClash_from_coveredLocksAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (defaultMessage : Message)
    (publicLockCoverage :
      D.toAppendixDWitnessData.PublicLockCoveredBySupportedInstances)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime C.lowerFramework
        (uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    UpperLowerClash
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      (C.parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoveredLocksAndRigidity
          (D := D) (F := C.lowerFramework)
          defaultMessage publicLockCoverage lockedMessageRigidity
          uniformSupport pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
    C
    (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoveredLocksAndRigidity
      (D := D) (F := C.lowerFramework)
      defaultMessage publicLockCoverage lockedMessageRigidity
      uniformSupport pnpDeciderFamily constantDecoderRegime)
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
Coverage-data version of the real-ensemble conditional endgame staging
theorem.  Public-lock coverage is supplied as representative construction data
rather than as a raw proposition; the self-reduction upper side remains
conditional on the explicit P=NP decider family.
-/
theorem realM4_conditionalClash_from_coverageDataAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime C.lowerFramework
        (uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    UpperLowerClash
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      (C.parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := C.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          uniformSupport pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_coveredLocksAndRigidity_explicitPNP
    C defaultMessage coverageData.publicLockCoverage lockedMessageRigidity
    uniformSupport pnpDeciderFamily constantDecoderRegime
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
Locked-message-data version of the real-ensemble conditional endgame staging
theorem.  The construction supplies the public message function and proves all
accepted locked completions read it; public-lock coverage remains exposed as
the D.7 construction obligation, and the upper self-reduction side remains
conditional on the explicit P=NP decider family.
-/
theorem realM4_conditionalClash_from_coverageDataAndLockedMessageData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (C : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime C.lowerFramework
        (uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness : CompressionStarSWHardness C.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ C.interfaceData.safeCost q ∧
        C.interfaceData.safeCost q ≤ C.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        C.interfaceData.gaugeIncidence gamma ≤ C.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound C.interfaceData.target C.interfaceData.pivotSummary
        C.interfaceData.epsMix) :
    UpperLowerClash
      (C.interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      (C.parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
          (D := D) (F := C.lowerFramework)
          coverageData lockedMessageData
          uniformSupport pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
    C
    (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
      (D := D) (F := C.lowerFramework)
      coverageData lockedMessageData
      uniformSupport pnpDeciderFamily constantDecoderRegime)
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
Lower-machine-data version of the real-ensemble conditional endgame staging
theorem.  The real lower framework and kernel neutrality are supplied by one
explicit lower-machine construction object, while public-lock coverage,
locked-message data, uniform CNF support, the constant-decoder regime, the
StarSW input, and the three analytic fields remain visible.
-/
theorem realM4_conditionalClash_from_lowerMachine_coverageDataAndLockedMessageData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * M.phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : M.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          M fixedGapBudget phaseABudget epsSmall
          lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          M fixedGapBudget phaseABudget epsSmall
          lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
          (D := D) (F := lowerMachine.lowerFramework)
          coverageData lockedMessageData
          uniformSupport pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_coverageDataAndLockedMessageData_explicitPNP
    (RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
      M fixedGapBudget phaseABudget epsSmall lowerMachine)
    coverageData lockedMessageData
    uniformSupport pnpDeciderFamily constantDecoderRegime
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
Finite-variable version of the real-ensemble conditional endgame staging
theorem.  The uniform CNF support package is built by enumerating all variables
from explicit finite variable-family data; the P=NP decider remains a visible
conditional input to the upper-side self-reduction.
-/
theorem realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * M.phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : M.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          M fixedGapBudget phaseABudget epsSmall
          lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          M fixedGapBudget phaseABudget epsSmall
          lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
          (D := D) (F := lowerMachine.lowerFramework)
          coverageData lockedMessageData
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_coverageDataAndLockedMessageData_explicitPNP
    M fixedGapBudget phaseABudget epsSmall lowerMachine
    coverageData lockedMessageData finiteVariables.uniformSupport
    pnpDeciderFamily constantDecoderRegime
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
Finite-variable lower-machine staging from the manuscript D.8 rigidity
proposition.  Public-lock representative data supplies D.7; D.7 plus D.8
construct the public-message invariant used by the explicit-P=NP
self-reduction package.  Thus the theorem exposes D.8 directly instead of
assuming a prebuilt public-message data package.
-/
theorem realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * M.phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : M.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          M fixedGapBudget phaseABudget epsSmall
          lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          M fixedGapBudget phaseABudget epsSmall
          lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_coverageDataAndRigidity_explicitPNP
    (RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
      M fixedGapBudget phaseABudget epsSmall lowerMachine)
    defaultMessage coverageData lockedMessageRigidity
    finiteVariables.uniformSupport pnpDeciderFamily constantDecoderRegime
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
Canonical-gap version of the finite-variable lower-machine staging theorem.
The Phase-A fixed budget is chosen to be exactly the half-derivative bound, so
`fixedGapBudget` and `phaseABudget` are not theorem hypotheses on this route.

This only discharges the numeric Phase-A budget wrapper.  The lower-machine
data, D.8 rigidity, public-lock coverage, finite CNF variables, strict
boundary-mixing smallness, explicit P=NP decider, StarSW hardness, and the
three analytic fields remain visible inputs.
-/
theorem realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (epsSmall : M.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          M epsSmall lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          M epsSmall lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) := by
  simpa [RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
    RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
    RealM4EndgameMechanicalData.ofComponentsWithLowerMachine] using
    (realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
      M (RealM4EndgameMechanicalData.canonicalFixedGapBudget M)
      (RealM4EndgameMechanicalData.canonicalPhaseABudget M) epsSmall
      lowerMachine defaultMessage coverageData lockedMessageRigidity
      finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
      safeQSSM boundedGaugeIncidence boundaryMixing)

/--
Real-frontier version of the canonical-gap lower-machine staging theorem.  The
three analytic fields are supplied as explicit frontier objects over the real
mechanical interface.  In particular, the strict `epsSmall` proof is carried
by the boundary-mixing frontier rather than exposed as a separate construction
input.
-/
theorem realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM : RealM4MechanicalInterfaceData.SafeQSSMFrontier M)
    (boundedGaugeIncidence :
      RealM4MechanicalInterfaceData.BoundedGaugeIncidenceFrontier M)
    (boundaryMixing :
      RealM4MechanicalInterfaceData.BoundaryMixingFrontier M) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          M boundaryMixing.epsSmall lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          M boundaryMixing.epsSmall lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_explicitPNP
    M boundaryMixing.epsSmall lowerMachine defaultMessage coverageData
    lockedMessageRigidity finiteVariables pnpDeciderFamily
    constantDecoderRegime starSWHardness safeQSSM.safeQSSM
    boundedGaugeIncidence.boundedGaugeIncidence boundaryMixing.boundaryMixing

/--
Component-level covered-locks staging theorem.  This removes the
`RealM4EndgameMechanicalData` package from the theorem hypotheses by building
it from the explicit construction components: the mechanical interface data,
phase-A budget, small-boundary-mixing bound, real lower framework, and kernel
neutrality payload.

This still leaves those components as real M4 construction obligations; it
only prevents the endgame wrapper from hiding them as one opaque parameter.
-/
theorem realM4_conditionalClash_from_components_coveredLocksAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * M.phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : M.epsMix < (1 / 2 : Rat))
    (lowerFramework : CompressionLowerFramework)
    (kernelNeutrality : CompressionKernelNeutrality lowerFramework)
    (defaultMessage : Message)
    (publicLockCoverage :
      D.toAppendixDWitnessData.PublicLockCoveredBySupportedInstances)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerFramework
        (uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness : CompressionStarSWHardness lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix) :
    UpperLowerClash
      (M.withAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponents
          M fixedGapBudget phaseABudget epsSmall lowerFramework
          kernelNeutrality).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoveredLocksAndRigidity
          (D := D) (F := lowerFramework)
          defaultMessage publicLockCoverage lockedMessageRigidity
          uniformSupport pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_coveredLocksAndRigidity_explicitPNP
    (RealM4EndgameMechanicalData.ofComponents
      M fixedGapBudget phaseABudget epsSmall lowerFramework kernelNeutrality)
    defaultMessage publicLockCoverage lockedMessageRigidity
    uniformSupport pnpDeciderFamily constantDecoderRegime
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
CD-ENF-component covered-locks staging theorem.  This removes both endgame
wrappers from the theorem hypotheses: the mechanical interface is built from
component data, while `atomCompleteness` and `gaugeFaithfulness` are supplied
by the generic CD-ENF semantics theorem rather than accepted as assumptions.

The theorem is still conditional on the explicit P=NP decider family and still
leaves the real construction obligations visible: public-lock coverage, D.8
locked-message rigidity, uniform CNF support, the constant-decoder regime,
hidden-gauge product, no-public-target-tags, admissible histories, and the
real lower/budget data.
-/
theorem realM4_conditionalClash_from_CDENFComponents_coveredLocksAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerFramework : CompressionLowerFramework)
    (kernelNeutrality : CompressionKernelNeutrality lowerFramework)
    (defaultMessage : Message)
    (publicLockCoverage :
      D.toAppendixDWitnessData.PublicLockCoveredBySupportedInstances)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerFramework
        (uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness : CompressionStarSWHardness lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound target pivotSummary epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          law target publicInput neutralSkeleton oppositeSupport transcript
          observerBit phaseA semantics observerEvidence historyField
          pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
          singleMessage hiddenGaugeProduct noPublicTargetTags
          admissibleHistories fixedGapBudget phaseABudget epsSmall
          lowerFramework kernelNeutrality).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          law target publicInput neutralSkeleton oppositeSupport transcript
          observerBit phaseA semantics observerEvidence historyField
          pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
          singleMessage hiddenGaugeProduct noPublicTargetTags
          admissibleHistories fixedGapBudget phaseABudget epsSmall
          lowerFramework kernelNeutrality).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoveredLocksAndRigidity
          (D := D) (F := lowerFramework)
          defaultMessage publicLockCoverage lockedMessageRigidity
          uniformSupport pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) := by
  exact
    realM4_conditionalClash_from_coveredLocksAndRigidity_explicitPNP
      (RealM4EndgameMechanicalData.ofCDENFComponents
        (HistoryAtom := HistoryAtom) (Observer := Observer)
        (Output := Output)
        law target publicInput neutralSkeleton oppositeSupport transcript
        observerBit phaseA semantics observerEvidence historyField
        pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
        singleMessage hiddenGaugeProduct noPublicTargetTags
        admissibleHistories fixedGapBudget phaseABudget epsSmall
        lowerFramework kernelNeutrality)
      defaultMessage publicLockCoverage lockedMessageRigidity
      uniformSupport pnpDeciderFamily constantDecoderRegime
      starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
CD-ENF-component, lower-machine, finite-variable real endgame staging theorem.
This is the sharpest current mechanical assembly layer: atom completeness and
gauge faithfulness come from CD-ENF semantics, the lower framework and kernel
neutrality come from explicit lower-machine data, uniform CNF support comes
from finite variable-family data, and the upper-side package uses public-lock
coverage data plus locked-message data.  The P=NP decider remains explicit and
conditional.

The remaining construction arguments are still real M4 obligations, not
irreducible frontier assumptions.
-/
theorem realM4_conditionalClash_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound target pivotSummary epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          law target publicInput neutralSkeleton oppositeSupport transcript
          observerBit phaseA semantics observerEvidence historyField
          pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
          singleMessage hiddenGaugeProduct noPublicTargetTags
          admissibleHistories fixedGapBudget phaseABudget epsSmall
          lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          law target publicInput neutralSkeleton oppositeSupport transcript
          observerBit phaseA semantics observerEvidence historyField
          pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
          singleMessage hiddenGaugeProduct noPublicTargetTags
          admissibleHistories fixedGapBudget phaseABudget epsSmall
          lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
          (D := D) (F := lowerMachine.lowerFramework)
          coverageData lockedMessageData
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP
    (RealM4MechanicalInterfaceData.ofCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      law target publicInput neutralSkeleton oppositeSupport transcript
      observerBit phaseA semantics observerEvidence historyField pivotSummary
      epsMix safeCost safeBudget gaugeIncidence gaugeBound singleMessage
      hiddenGaugeProduct noPublicTargetTags admissibleHistories)
    fixedGapBudget
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        phaseABudget)
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using epsSmall)
    lowerMachine coverageData lockedMessageData finiteVariables
    pnpDeciderFamily constantDecoderRegime starSWHardness
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        safeQSSM)
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        boundedGaugeIncidence)
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        boundaryMixing)

/--
CD-ENF-component, lower-machine, finite-variable real endgame staging theorem
from the manuscript D.8 locked-message rigidity proposition.  Public-lock
coverage data supplies D.7, D.8 constructs the fixed public-message readout,
and CD-ENF supplies atom-completeness and gauge-faithfulness.

This is still conditional staging: D.8, public-lock coverage, finite CNF
variables, lower-machine data, the budget bounds, the explicit P=NP decider,
StarSW hardness, and the three analytic fields remain visible inputs.
-/
theorem realM4_conditionalClash_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound target pivotSummary epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          law target publicInput neutralSkeleton oppositeSupport transcript
          observerBit phaseA semantics observerEvidence historyField
          pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
          singleMessage hiddenGaugeProduct noPublicTargetTags
          admissibleHistories fixedGapBudget phaseABudget epsSmall
          lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          law target publicInput neutralSkeleton oppositeSupport transcript
          observerBit phaseA semantics observerEvidence historyField
          pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
          singleMessage hiddenGaugeProduct noPublicTargetTags
          admissibleHistories fixedGapBudget phaseABudget epsSmall
          lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    (RealM4MechanicalInterfaceData.ofCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      law target publicInput neutralSkeleton oppositeSupport transcript
      observerBit phaseA semantics observerEvidence historyField pivotSummary
      epsMix safeCost safeBudget gaugeIncidence gaugeBound singleMessage
      hiddenGaugeProduct noPublicTargetTags admissibleHistories)
    fixedGapBudget
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        phaseABudget)
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using epsSmall)
    lowerMachine defaultMessage coverageData lockedMessageRigidity
    finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        safeQSSM)
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        boundedGaugeIncidence)
    (by
      simpa [RealM4MechanicalInterfaceData.ofCDENFComponents] using
        boundaryMixing)

/-! ## Official Cook-style endpoint bridge boundary -/

/--
Minimal Cook-style complexity-class endpoint interface.  It exposes the
language universe, the two class predicates, and the official separation
proposition as the existence of an NP language outside P.  This is still an
interface, not a construction of the global complexity-class development.
-/
structure CookStylePNPClassInterface where
  Language : Type u
  inP : Language -> Prop
  inNP : Language -> Prop
  officialSeparation : Prop
  officialSeparation_iff_exists_np_not_p :
    officialSeparation ↔ ∃ L : Language, inNP L ∧ ¬ inP L

namespace CookStylePNPClassInterface

theorem officialSeparation_of_np_not_p
    (C : CookStylePNPClassInterface) {L : C.Language}
    (hNP : C.inNP L) (hNotP : ¬ C.inP L) :
    C.officialSeparation :=
  C.officialSeparation_iff_exists_np_not_p.mpr ⟨L, hNP, hNotP⟩

end CookStylePNPClassInterface

/--
Bridge data from the internal real-M4 clash endpoint to a Cook-style P-vs-NP
separation statement.  The bridge must expose the separated language, prove it
is in NP, and show that the internal clash rules out membership in P.

To finish the real route, the official statement must be instantiated by the
formal complexity-class development, and the bridge must prove that the
particular internal M4 `UpperLowerClash` rules out P membership without hiding
ensemble existence, lower hardness, or analytic assumptions in
parameters.
-/
structure RealM4OfficialPNPBridgeData
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    (L :
      GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
        Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (P : ParameterRecord L)
    (C : CookStylePNPClassInterface.{p}) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage
  internalClash_not_inP :
    UpperLowerClash L P -> ¬ C.inP separatedLanguage

/--
Adapter from a proved internal clash to the official endpoint, assuming the
separate bridge data.  This theorem is not a proof of P-vs-NP; the bridge data
is the still-open Cook-style endpoint obligation.
-/
theorem realM4_officialSeparation_from_internalClash_bridge
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {L :
      GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
        Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton}
    {P : ParameterRecord L}
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData L P C)
    (clash : UpperLowerClash L P) :
    C.officialSeparation :=
  C.officialSeparation_of_np_not_p
    bridge.separatedLanguage_inNP
    (bridge.internalClash_not_inP clash)

/--
Direct Cook-style existential endpoint from a proved internal clash and the
separate official bridge data.  This exposes the official content as an NP
language outside P, rather than only through the named `officialSeparation`
proposition.  The bridge remains an explicit construction obligation.
-/
theorem realM4_exists_np_not_p_from_internalClash_bridge
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {L :
      GaugeBufferedLockedInterface Omega Public Neutral Safe Gauge Transcript
        Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton}
    {P : ParameterRecord L}
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData L P C)
    (clash : UpperLowerClash L P) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  ⟨bridge.separatedLanguage,
    bridge.separatedLanguage_inNP,
    bridge.internalClash_not_inP clash⟩

/--
Official-endpoint staging theorem for already packaged real endgame data.
Given the explicit P=NP-side upper package, StarSW hardness, the three
analytic fields, and a separate Cook-style bridge, the internal real-M4
`UpperLowerClash` transports to the Cook-style separation proposition.

This remains conditional staging.  It does not construct the manuscript M4
ensemble, the four hard inputs, or the Cook-style bridge data.
-/
theorem realM4_officialSeparation_from_endgameMechanicalData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4EndgameMechanicalData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (S : RealM4SelfReductionUpperExplicitPNPDischarge D M.lowerFramework)
    (starSWHardness : CompressionStarSWHardness M.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.interfaceData.safeCost q ∧
        M.interfaceData.safeCost q ≤ M.interfaceData.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge,
        M.interfaceData.gaugeIncidence gamma ≤ M.interfaceData.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.interfaceData.target M.interfaceData.pivotSummary
        M.interfaceData.epsMix)
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        (M.interfaceWithAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing)
        (M.parameterRecordExplicitPNP S starSWHardness
          safeQSSM boundedGaugeIncidence boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
      M S starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing)

/--
Official-endpoint staging for the canonical-gap lower-machine route.  The
Phase-A fixed budget is chosen by construction, so the official endpoint
adapter does not take `fixedGapBudget` or `phaseABudget` as hypotheses.  The
Cook-style bridge remains a separate visible construction obligation.
-/
theorem realM4_officialSeparation_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (epsSmall : M.epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ M.safeCost q ∧ M.safeCost q ≤ M.safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, M.gaugeIncidence gamma ≤ M.gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound M.target M.pivotSummary M.epsMix)
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            M epsSmall lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing)
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            M epsSmall lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
            (D := D) (F := lowerMachine.lowerFramework)
            defaultMessage coverageData lockedMessageRigidity
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_explicitPNP
      M epsSmall lowerMachine defaultMessage coverageData
      lockedMessageRigidity finiteVariables pnpDeciderFamily
      constantDecoderRegime starSWHardness safeQSSM boundedGaugeIncidence
      boundaryMixing)

/--
Official-endpoint staging for the real-frontier canonical-gap route.  The
three analytic fields are frontier objects, with boundary mixing carrying the
strict smallness witness needed by the v13 clash.  The Cook-style bridge
remains a separate visible construction obligation.
-/
theorem realM4_officialSeparation_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM : RealM4MechanicalInterfaceData.SafeQSSMFrontier M)
    (boundedGaugeIncidence :
      RealM4MechanicalInterfaceData.BoundedGaugeIncidenceFrontier M)
    (boundaryMixing :
      RealM4MechanicalInterfaceData.BoundaryMixingFrontier M)
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            M boundaryMixing.epsSmall lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            M boundaryMixing.epsSmall lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
            (D := D) (F := lowerMachine.lowerFramework)
            defaultMessage coverageData lockedMessageRigidity
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM.safeQSSM
          boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
      M lowerMachine defaultMessage coverageData lockedMessageRigidity
      finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
      safeQSSM boundedGaugeIncidence boundaryMixing)

/--
Official-endpoint staging theorem for the sharpest current real component
assembly.  CD-ENF supplies atom-completeness and gauge-faithfulness, the lower
framework comes from explicit lower-machine data, uniform CNF support comes
from finite variable-family data, and the P=NP-side upper package is built
from public-lock coverage data plus locked-message data.

The theorem still exposes every real construction obligation and the
Cook-style bridge as hypotheses.  It is not a proof of P != NP and not a claim
that the manuscript M4 construction or the four hard inputs have been proved.
-/
theorem realM4_officialSeparation_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound target pivotSummary epsMix)
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            law target publicInput neutralSkeleton oppositeSupport transcript
            observerBit phaseA semantics observerEvidence historyField
            pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
            singleMessage hiddenGaugeProduct noPublicTargetTags
            admissibleHistories fixedGapBudget phaseABudget epsSmall
            lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing)
        ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            law target publicInput neutralSkeleton oppositeSupport transcript
            observerBit phaseA semantics observerEvidence historyField
            pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
            singleMessage hiddenGaugeProduct noPublicTargetTags
            admissibleHistories fixedGapBudget phaseABudget epsSmall
            lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
            (D := D) (F := lowerMachine.lowerFramework)
            coverageData lockedMessageData
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP
      law target publicInput neutralSkeleton oppositeSupport transcript
      observerBit phaseA semantics observerEvidence historyField pivotSummary
      epsMix safeCost safeBudget gaugeIncidence gaugeBound singleMessage
      hiddenGaugeProduct noPublicTargetTags admissibleHistories
      fixedGapBudget phaseABudget epsSmall lowerMachine coverageData
      lockedMessageData finiteVariables pnpDeciderFamily constantDecoderRegime
      starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing)

/--
Official-endpoint staging from the manuscript D.8 rigidity proposition rather
than from a prebuilt locked-message data package.  Public-lock coverage gives
D.7, D.7 plus D.8 constructs the public-message invariant for the upper
self-reduction, and the separate Cook-style bridge transports the resulting
internal clash to the official endpoint.

This is conditional staging only.  It leaves the real construction
obligations, the explicit P=NP decider family, StarSW hardness, the three
analytic fields, and the Cook-style bridge visible as hypotheses.
-/
theorem realM4_officialSeparation_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw Omega)
    (target : Omega -> Bool)
    (publicInput : Omega -> Public)
    (neutralSkeleton : Omega -> Skeleton)
    (oppositeSupport : Omega -> Omega -> Prop)
    (transcript : Omega -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law target transcript observerBit Pair Stage Branch)
    (semantics : EvidenceSemantics Omega Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface Omega Public Observer Output Neutral Safe Gauge)
    (historyField : FiniteSigmaField.{u, d} Omega)
    (pivotSummary : Omega -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (singleMessage :
      ∀ w0 w1, publicInput w0 = publicInput w1 -> target w0 = target w1)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (noPublicTargetTags :
      PairNeutral oppositeSupport neutralSkeleton ∧
        HasMessageOppositePair oppositeSupport target ∧
          ¬ ∃ f : Skeleton -> Bool,
            ∀ omega, target omega = f (neutralSkeleton omega))
    (admissibleHistories :
      BalancedBit target ∧
        BalancedConditioning (Omega := Omega) historyField target)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound target pivotSummary epsMix)
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            law target publicInput neutralSkeleton oppositeSupport transcript
            observerBit phaseA semantics observerEvidence historyField
            pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
            singleMessage hiddenGaugeProduct noPublicTargetTags
            admissibleHistories fixedGapBudget phaseABudget epsSmall
            lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing)
        ((RealM4EndgameMechanicalData.ofCDENFComponentsWithLowerMachine
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            law target publicInput neutralSkeleton oppositeSupport transcript
            observerBit phaseA semantics observerEvidence historyField
            pivotSummary epsMix safeCost safeBudget gaugeIncidence gaugeBound
            singleMessage hiddenGaugeProduct noPublicTargetTags
            admissibleHistories fixedGapBudget phaseABudget epsSmall
            lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
            (D := D) (F := lowerMachine.lowerFramework)
            defaultMessage coverageData lockedMessageRigidity
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
      law target publicInput neutralSkeleton oppositeSupport transcript
      observerBit phaseA semantics observerEvidence historyField pivotSummary
      epsMix safeCost safeBudget gaugeIncidence gaugeBound singleMessage
      hiddenGaugeProduct noPublicTargetTags admissibleHistories
      fixedGapBudget phaseABudget epsSmall lowerMachine defaultMessage
      coverageData lockedMessageRigidity finiteVariables pnpDeciderFamily
      constantDecoderRegime starSWHardness safeQSSM boundedGaugeIncidence
      boundaryMixing)

/--
No-target-rows real-public-surface staging theorem.  Compared with the raw
CD-ENF component theorem, the adjusted linear no-target-rows surface derives
the single-message, no-public-target-tags, and admissible-history fields using
the checked public-surface cardinality proofs.

This is still conditional staging for that real public surface.  The full M4
construction must still identify its public surface, neutral skeleton, and
history atoms with these checked data before this constructor closes the
corresponding global M4 obligations.
-/
theorem realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound
        (@v13RealLinearNoTargetRowsTargetBit m i₀) pivotSummary epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            i₀ coordinate law transcript observerBit phaseA semantics
            observerEvidence pivotSummary epsMix safeCost safeBudget
            gaugeIncidence gaugeBound hiddenGaugeProduct)
          fixedGapBudget phaseABudget epsSmall lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM boundedGaugeIncidence boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
          (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            i₀ coordinate law transcript observerBit phaseA semantics
            observerEvidence pivotSummary epsMix safeCost safeBudget
            gaugeIncidence gaugeBound hiddenGaugeProduct)
          fixedGapBudget phaseABudget epsSmall lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct)
    fixedGapBudget
    (by
      simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
        RealM4MechanicalInterfaceData.ofCDENFComponents] using
        phaseABudget)
    (by
      simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
        RealM4MechanicalInterfaceData.ofCDENFComponents] using epsSmall)
    lowerMachine defaultMessage coverageData lockedMessageRigidity
    finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
    (by
      simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
        RealM4MechanicalInterfaceData.ofCDENFComponents] using safeQSSM)
    (by
      simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
        RealM4MechanicalInterfaceData.ofCDENFComponents] using
        boundedGaugeIncidence)
    (by
      simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
        RealM4MechanicalInterfaceData.ofCDENFComponents] using
        boundaryMixing)

/--
Canonical-gap no-target-rows conditional staging theorem.  Compared with
`realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP`,
this route also discharges the Phase-A numeric budget wrapper by choosing the
fixed gap budget canonically as the half-derivative bound.  Thus
`fixedGapBudget` and `phaseABudget` are not hypotheses.

This remains conditional real-spine staging, not a proof of `P != NP` and not
a full manuscript M4 identification.  The strict `epsSmall` bound, hidden gauge
product, lower-machine data, public-lock coverage, D.8 rigidity, finite CNF
variables, explicit P=NP decider, StarSW hardness, and the three analytic
fields remain visible inputs.
-/
theorem realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_explicitPNP
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound
        (@v13RealLinearNoTargetRowsTargetBit m i₀) pivotSummary epsMix) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            i₀ coordinate law transcript observerBit phaseA semantics
            observerEvidence pivotSummary epsMix safeCost safeBudget
            gaugeIncidence gaugeBound hiddenGaugeProduct)
          (by
            simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
              RealM4MechanicalInterfaceData.ofCDENFComponents] using
              epsSmall)
          lowerMachine).interfaceWithAnalyticFrontier
        (by
          simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
            RealM4MechanicalInterfaceData.ofCDENFComponents,
            RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
            RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
            RealM4EndgameMechanicalData.ofComponents] using safeQSSM)
        (by
          simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
            RealM4MechanicalInterfaceData.ofCDENFComponents,
            RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
            RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
            RealM4EndgameMechanicalData.ofComponents] using
            boundedGaugeIncidence)
        (by
          simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
            RealM4MechanicalInterfaceData.ofCDENFComponents,
            RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
            RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
            RealM4EndgameMechanicalData.ofComponents] using
            boundaryMixing))
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            i₀ coordinate law transcript observerBit phaseA semantics
            observerEvidence pivotSummary epsMix safeCost safeBudget
            gaugeIncidence gaugeBound hiddenGaugeProduct)
          (by
            simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
              RealM4MechanicalInterfaceData.ofCDENFComponents] using
              epsSmall)
          lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness
        (by
          simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
            RealM4MechanicalInterfaceData.ofCDENFComponents,
            RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
            RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
            RealM4EndgameMechanicalData.ofComponents] using safeQSSM)
        (by
          simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
            RealM4MechanicalInterfaceData.ofCDENFComponents,
            RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
            RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
            RealM4EndgameMechanicalData.ofComponents] using
            boundedGaugeIncidence)
        (by
          simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
            RealM4MechanicalInterfaceData.ofCDENFComponents,
            RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
            RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
            RealM4EndgameMechanicalData.ofComponents] using
            boundaryMixing)) := by
  simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
    RealM4MechanicalInterfaceData.ofCDENFComponents,
    RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
    RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
    RealM4EndgameMechanicalData.ofComponents] using
    (realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_explicitPNP
      (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
        (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
        i₀ coordinate law transcript observerBit phaseA semantics
        observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
        gaugeBound hiddenGaugeProduct)
      (by
        simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
          RealM4MechanicalInterfaceData.ofCDENFComponents] using epsSmall)
      lowerMachine defaultMessage coverageData lockedMessageRigidity
      finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
      (by
        simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
          RealM4MechanicalInterfaceData.ofCDENFComponents] using safeQSSM)
      (by
        simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
          RealM4MechanicalInterfaceData.ofCDENFComponents] using
          boundedGaugeIncidence)
      (by
        simpa [RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
          RealM4MechanicalInterfaceData.ofCDENFComponents] using
          boundaryMixing))

/--
Canonical-gap no-target-rows staging with the three analytic inputs packaged
as real frontier objects over the constructed no-target-rows mechanical
interface.  Boundary mixing carries the strict `epsSmall` witness, so
`epsSmall` is not a separate hypothesis of this route.

This remains conditional real-spine staging: the no-target-rows constructor
derives `singleMessage`, `noPublicTargetTags`, `admissibleHistories`, and the
canonical Phase-A budget, but full M4 must still identify its public surface
and discharge the remaining construction inputs.
-/
theorem realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      RealM4MechanicalInterfaceData.SafeQSSMFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    (boundedGaugeIncidence :
      RealM4MechanicalInterfaceData.BoundedGaugeIncidenceFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    (boundaryMixing :
      RealM4MechanicalInterfaceData.BoundaryMixingFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct)) :
    UpperLowerClash
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            i₀ coordinate law transcript observerBit phaseA semantics
            observerEvidence pivotSummary epsMix safeCost safeBudget
            gaugeIncidence gaugeBound hiddenGaugeProduct)
          boundaryMixing.epsSmall lowerMachine).interfaceWithAnalyticFrontier
        safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing)
      ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
          (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
            (HistoryAtom := HistoryAtom) (Observer := Observer)
            (Output := Output)
            i₀ coordinate law transcript observerBit phaseA semantics
            observerEvidence pivotSummary epsMix safeCost safeBudget
            gaugeIncidence gaugeBound hiddenGaugeProduct)
          boundaryMixing.epsSmall lowerMachine).parameterRecordExplicitPNP
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
          (D := D) (F := lowerMachine.lowerFramework)
          defaultMessage coverageData lockedMessageRigidity
          finiteVariables.uniformSupport pnpDeciderFamily
          constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct)
    lowerMachine defaultMessage coverageData lockedMessageRigidity
    finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
    safeQSSM boundedGaugeIncidence boundaryMixing

/--
Cook-style official endpoint wrapper for the no-target-rows canonical-gap
real-frontier route.  The internal clash uses exactly the three analytic
frontier objects plus StarSW and the explicit P=NP decider; the Cook bridge
remains a separate visible construction obligation.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      RealM4MechanicalInterfaceData.SafeQSSMFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    (boundedGaugeIncidence :
      RealM4MechanicalInterfaceData.BoundedGaugeIncidenceFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    (boundaryMixing :
      RealM4MechanicalInterfaceData.BoundaryMixingFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
              (HistoryAtom := HistoryAtom) (Observer := Observer)
              (Output := Output)
              i₀ coordinate law transcript observerBit phaseA semantics
              observerEvidence pivotSummary epsMix safeCost safeBudget
              gaugeIncidence gaugeBound hiddenGaugeProduct)
            boundaryMixing.epsSmall lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
              (HistoryAtom := HistoryAtom) (Observer := Observer)
              (Output := Output)
              i₀ coordinate law transcript observerBit phaseA semantics
              observerEvidence pivotSummary epsMix safeCost safeBudget
              gaugeIncidence gaugeBound hiddenGaugeProduct)
            boundaryMixing.epsSmall lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
            (D := D) (F := lowerMachine.lowerFramework)
            defaultMessage coverageData lockedMessageRigidity
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM.safeQSSM
          boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct lowerMachine defaultMessage coverageData
      lockedMessageRigidity finiteVariables pnpDeciderFamily
      constantDecoderRegime starSWHardness safeQSSM boundedGaugeIncidence
      boundaryMixing)

/--
Explicit Cook-style existential endpoint for the current sharp no-target-rows,
canonical-gap, real-frontier route.  It states the endpoint as the existence
of an NP language outside P.  This is still conditional staging: the bridge
data, real construction data, StarSW, three analytic frontier objects, and
the explicit P=NP decider family are all visible hypotheses.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      RealM4MechanicalInterfaceData.SafeQSSMFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    (boundedGaugeIncidence :
      RealM4MechanicalInterfaceData.BoundedGaugeIncidenceFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    (boundaryMixing :
      RealM4MechanicalInterfaceData.BoundaryMixingFrontier
        (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
          (HistoryAtom := HistoryAtom) (Observer := Observer)
          (Output := Output)
          i₀ coordinate law transcript observerBit phaseA semantics
          observerEvidence pivotSummary epsMix safeCost safeBudget
          gaugeIncidence gaugeBound hiddenGaugeProduct))
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
              (HistoryAtom := HistoryAtom) (Observer := Observer)
              (Output := Output)
              i₀ coordinate law transcript observerBit phaseA semantics
              observerEvidence pivotSummary epsMix safeCost safeBudget
              gaugeIncidence gaugeBound hiddenGaugeProduct)
            boundaryMixing.epsSmall lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
            (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
              (HistoryAtom := HistoryAtom) (Observer := Observer)
              (Output := Output)
              i₀ coordinate law transcript observerBit phaseA semantics
              observerEvidence pivotSummary epsMix safeCost safeBudget
              gaugeIncidence gaugeBound hiddenGaugeProduct)
            boundaryMixing.epsSmall lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
            (D := D) (F := lowerMachine.lowerFramework)
            defaultMessage coverageData lockedMessageRigidity
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM.safeQSSM
          boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct lowerMachine defaultMessage coverageData
      lockedMessageRigidity finiteVariables pnpDeciderFamily
      constantDecoderRegime starSWHardness safeQSSM boundedGaugeIncidence
      boundaryMixing)

/--
Cook-style official endpoint staging for the adjusted real no-target-rows
public surface.  The theorem uses the no-target-rows mechanical constructor,
so `singleMessage`, `noPublicTargetTags`, and `admissibleHistories` are not
hypotheses of this route.

This remains a conditional staging theorem, not an official separation proof:
the Cook-style bridge, lower-machine data, public-lock coverage, D.8 rigidity,
finite CNF variables, budget bounds, explicit P=NP decider family, StarSW
hardness, and the three analytic fields remain visible inputs.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
    {m : Nat} (i₀ : Fin m) [hm : Fact (1 < m)]
    (coordinate : V13RealLinearPublicCoordinate m)
    {Neutral : Type} {Safe : Type x} {Gauge : Type y}
    {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type} {Pivot : Type e}
    {Observer : Type f} {Output : Type f}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (law : FiniteRationalLaw (V13RealLinearNoTargetRowsWorld m i₀))
    (transcript : V13RealLinearNoTargetRowsWorld m i₀ -> Transcript)
    (observerBit : Transcript -> Bool)
    (phaseA :
      EvidenceSpineBound law
        (@v13RealLinearNoTargetRowsTargetBit m i₀) transcript observerBit
        Pair Stage Branch)
    (semantics :
      EvidenceSemantics
        (V13RealLinearNoTargetRowsWorld m i₀) Neutral Safe Gauge)
    (observerEvidence :
      ObserverEvidenceInterface
        (V13RealLinearNoTargetRowsWorld m i₀) (V13RealLinearPublic m)
        Observer Output Neutral Safe Gauge)
    (pivotSummary : V13RealLinearNoTargetRowsWorld m i₀ -> Pivot)
    (epsMix : Rat)
    (safeCost : Safe -> Rat)
    (safeBudget : Rat)
    (gaugeIncidence : Gauge -> Nat)
    (gaugeBound : Nat)
    (hiddenGaugeProduct :
      ∀ gamma omega, semantics.gaugeSat gamma omega)
    (fixedGapBudget : Rat)
    (phaseABudget :
      (1 / 2 : Rat) * phaseA.telescoping.derivativeSum ≤ fixedGapBudget)
    (epsSmall : epsMix < (1 / 2 : Rat))
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (finiteVariables : RealM4FiniteCNFVariableFamilyData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        (finiteVariables.uniformSupport.withPNPDecider pnpDeciderFamily))
    (starSWHardness :
      CompressionStarSWHardness lowerMachine.lowerFramework)
    (safeQSSM :
      ∀ q : Safe, 0 ≤ safeCost q ∧ safeCost q ≤ safeBudget)
    (boundedGaugeIncidence :
      ∀ gamma : Gauge, gaugeIncidence gamma ≤ gaugeBound)
    (boundaryMixing :
      BoundaryMixingBound
        (@v13RealLinearNoTargetRowsTargetBit m i₀) pivotSummary epsMix)
    {C : CookStylePNPClassInterface.{p}}
    (bridge :
      RealM4OfficialPNPBridgeData
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
            (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
              (HistoryAtom := HistoryAtom) (Observer := Observer)
              (Output := Output)
              i₀ coordinate law transcript observerBit phaseA semantics
              observerEvidence pivotSummary epsMix safeCost safeBudget
              gaugeIncidence gaugeBound hiddenGaugeProduct)
            fixedGapBudget phaseABudget epsSmall lowerMachine).interfaceWithAnalyticFrontier
          safeQSSM boundedGaugeIncidence boundaryMixing)
        ((RealM4EndgameMechanicalData.ofComponentsWithLowerMachine
            (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
              (HistoryAtom := HistoryAtom) (Observer := Observer)
              (Output := Output)
              i₀ coordinate law transcript observerBit phaseA semantics
              observerEvidence pivotSummary epsMix safeCost safeBudget
              gaugeIncidence gaugeBound hiddenGaugeProduct)
            fixedGapBudget phaseABudget epsSmall lowerMachine).parameterRecordExplicitPNP
          (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
            (D := D) (F := lowerMachine.lowerFramework)
            defaultMessage coverageData lockedMessageRigidity
            finiteVariables.uniformSupport pnpDeciderFamily
            constantDecoderRegime)
          starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_explicitPNP
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct fixedGapBudget phaseABudget epsSmall
      lowerMachine defaultMessage coverageData lockedMessageRigidity
      finiteVariables pnpDeciderFamily constantDecoderRegime starSWHardness
      safeQSSM boundedGaugeIncidence boundaryMixing)

def realM4OfficialPNPBridgeConstructionInputs : List String := [
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP",
  "internalClashNotInP"
]

theorem realM4OfficialPNPBridgeConstructionInputs_exact :
    realM4OfficialPNPBridgeConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4OfficialPNPBridgeStatement : String :=
  "The real v15/M4 UpperLowerClash is only an internal endpoint.  A separate Cook-style P-vs-NP bridge must instantiate the official class interface, name the separated NP language, and prove that the internal clash rules out membership in P without hiding ensemble existence, lower hardness, or analytic assumptions in parameters."

def realM4EndgameStagingConstructionInputs : List String := [
  "realM4EndgameMechanicalData",
  "realM4SelfReductionUpperDischarge"
]

theorem realM4EndgameStagingConstructionInputs_exact :
    realM4EndgameStagingConstructionInputs =
      [ "realM4EndgameMechanicalData",
        "realM4SelfReductionUpperDischarge" ] := by
  rfl

def realM4EndgameStagingIrreducibleInputs : List String := [
  "starSWHardness",
  "safeQSSM",
  "boundedGaugeIncidence",
  "boundaryMixing"
]

theorem realM4EndgameStagingIrreducibleInputs_exact :
    realM4EndgameStagingIrreducibleInputs =
      [ "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4EndgameStagingStatement : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows from real construction data, the explicit P=NP-side self-reduction discharge, StarSW hardness, and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  After the construction data is proved for M4, the irreducible mathematical content is exactly StarSW plus those three analytic fields."

def realM4EndgameStagingConstructionInputsExplicitPNP : List String := [
  "realM4EndgameMechanicalData",
  "realM4SelfReductionUpperExplicitPNPDischarge"
]

theorem realM4EndgameStagingConstructionInputsExplicitPNP_exact :
    realM4EndgameStagingConstructionInputsExplicitPNP =
      [ "realM4EndgameMechanicalData",
        "realM4SelfReductionUpperExplicitPNPDischarge" ] := by
  rfl

def realM4EndgameStagingConditionalInputsExplicitPNP : List String := [
  "pnpDeciderFamily"
]

theorem realM4EndgameStagingConditionalInputsExplicitPNP_exact :
    realM4EndgameStagingConditionalInputsExplicitPNP =
      [ "pnpDeciderFamily" ] := by
  rfl

def realM4EndgameStagingHypothesisAuditExplicitPNP : List String := [
  "starSWHardness",
  "safeQSSM",
  "boundedGaugeIncidence",
  "boundaryMixing",
  "pnpDeciderFamily"
]

theorem realM4EndgameStagingHypothesisAuditExplicitPNP_exact :
    realM4EndgameStagingHypothesisAuditExplicitPNP =
      [ "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4EndgameStagingStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows from real construction data, StarSW hardness, and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, with the self-reduction upper side discharged conditionally from the explicit P=NP decider family."

def realM4CoveredLocksEndgameConstructionInputsExplicitPNP : List String := [
  "realM4MechanicalInterfaceData",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerFramework",
  "kernelNeutrality",
  "publicLockSupportCoverage",
  "lockedMessageRigidity",
  "uniformCNFSupportData",
  "realConstantDecoderRegime"
]

theorem realM4CoveredLocksEndgameConstructionInputsExplicitPNP_exact :
    realM4CoveredLocksEndgameConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockSupportCoverage",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CoveredLocksEndgameConditionalInputsExplicitPNP : List String := [
  "pnpDeciderFamily"
]

theorem realM4CoveredLocksEndgameConditionalInputsExplicitPNP_exact :
    realM4CoveredLocksEndgameConditionalInputsExplicitPNP =
      [ "pnpDeciderFamily" ] := by
  rfl

def realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP : List String := [
  "starSWHardness",
  "safeQSSM",
  "boundedGaugeIncidence",
  "boundaryMixing"
]

theorem realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP_exact :
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP =
      [ "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4CoveredLocksEndgameHypothesisAuditExplicitPNP : List String :=
  realM4CoveredLocksEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CoveredLocksEndgameHypothesisAuditExplicitPNP_exact :
    realM4CoveredLocksEndgameHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockSupportCoverage",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CoveredLocksEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the explicit P=NP-side self-reduction package from public-lock coverage, D.8 locked-message rigidity, uniform CNF support, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing."

def realM4CoverageDataEndgameConstructionInputsExplicitPNP : List String := [
  "realM4MechanicalInterfaceData",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerFramework",
  "kernelNeutrality",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "uniformCNFSupportData",
  "realConstantDecoderRegime"
]

theorem realM4CoverageDataEndgameConstructionInputsExplicitPNP_exact :
    realM4CoverageDataEndgameConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CoverageDataEndgameHypothesisAuditExplicitPNP : List String :=
  realM4CoverageDataEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CoverageDataEndgameHypothesisAuditExplicitPNP_exact :
    realM4CoverageDataEndgameHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CoverageDataEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the explicit P=NP-side self-reduction package from public-lock representative data, D.8 locked-message rigidity, uniform CNF support, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing."

def realM4CoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP :
    List String := [
  "realM4MechanicalInterfaceData",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerFramework",
  "kernelNeutrality",
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "uniformCNFSupportData",
  "realConstantDecoderRegime"
]

theorem realM4CoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP_exact :
    realM4CoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4CoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP_exact :
    realM4CoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CoverageAndLockedMessageDataEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the explicit P=NP-side self-reduction package from public-lock representative data, locked-message public-message data, uniform CNF support, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing."

def realM4LowerMachineCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP :
    List String := [
  "realM4MechanicalInterfaceData",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerMachineData",
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "uniformCNFSupportData",
  "realConstantDecoderRegime"
]

theorem realM4LowerMachineCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP_exact :
    realM4LowerMachineCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4LowerMachineCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4LowerMachineCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4LowerMachineCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP_exact :
    realM4LowerMachineCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4LowerMachineCoverageAndLockedMessageDataEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the real lower machine, public-lock representative data, locked-message public-message data, uniform CNF support, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family."

def realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP :
    List String := [
  "realM4MechanicalInterfaceData",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerMachineData",
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP_exact :
    realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP_exact :
    realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4LowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the real lower machine, public-lock representative data, locked-message public-message data, finite CNF variable-family data, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family."

def realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP :
    List String := [
  "law",
  "target",
  "publicInput",
  "neutralSkeleton",
  "oppositeSupport",
  "transcript",
  "observerBit",
  "phaseA",
  "semantics",
  "observerEvidence",
  "historyField",
  "pivotSummary",
  "epsMix",
  "safeCost",
  "safeBudget",
  "gaugeIncidence",
  "gaugeBound",
  "singleMessage",
  "hiddenGaugeProduct",
  "noPublicTargetTags",
  "admissibleHistories",
  "fixedGapBudget",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerMachineData",
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP_exact :
    realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP_exact :
    realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameHypothesisAuditExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the CD-ENF mechanical components, the real lower machine, public-lock representative data, locked-message public-message data, finite CNF variable-family data, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family."

def realM4CDENFComponentCoveredLocksEndgameConstructionInputsExplicitPNP :
    List String := [
  "law",
  "target",
  "publicInput",
  "neutralSkeleton",
  "oppositeSupport",
  "transcript",
  "observerBit",
  "phaseA",
  "semantics",
  "observerEvidence",
  "historyField",
  "pivotSummary",
  "epsMix",
  "safeCost",
  "safeBudget",
  "gaugeIncidence",
  "gaugeBound",
  "singleMessage",
  "hiddenGaugeProduct",
  "noPublicTargetTags",
  "admissibleHistories",
  "fixedGapBudget",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerFramework",
  "kernelNeutrality",
  "publicLockSupportCoverage",
  "lockedMessageRigidity",
  "uniformCNFSupportData",
  "realConstantDecoderRegime"
]

theorem realM4CDENFComponentCoveredLocksEndgameConstructionInputsExplicitPNP_exact :
    realM4CDENFComponentCoveredLocksEndgameConstructionInputsExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockSupportCoverage",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CDENFComponentCoveredLocksEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4CDENFComponentCoveredLocksEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CDENFComponentCoveredLocksEndgameHypothesisAuditExplicitPNP_exact :
    realM4CDENFComponentCoveredLocksEndgameHypothesisAuditExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerFramework",
        "kernelNeutrality",
        "publicLockSupportCoverage",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CDENFComponentCoveredLocksEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows from explicit CD-ENF mechanical components, public-lock coverage, D.8 locked-message rigidity, uniform CNF support, the real constant-decoder regime, StarSW hardness, and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, with atomCompleteness and gaugeFaithfulness construction-transferred from generic CD-ENF semantics and the upper side conditional on the explicit P=NP decider family."

def realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP :
    List String := [
  "law",
  "target",
  "publicInput",
  "neutralSkeleton",
  "oppositeSupport",
  "transcript",
  "observerBit",
  "phaseA",
  "semantics",
  "observerEvidence",
  "historyField",
  "pivotSummary",
  "epsMix",
  "safeCost",
  "safeBudget",
  "gaugeIncidence",
  "gaugeBound",
  "singleMessage",
  "hiddenGaugeProduct",
  "noPublicTargetTags",
  "admissibleHistories",
  "fixedGapBudget",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerMachineData",
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP_exact :
    realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameHypothesisAuditExplicitPNP_exact :
    realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameHypothesisAuditExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows by constructing the CD-ENF mechanical components, the real lower machine, public-lock representative data, D.8 locked-message rigidity, finite CNF variable-family data, and the constant decoder regime, then using StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  D.7 plus D.8 construct the fixed public-message readout; locked-message public-message data is not a separate hypothesis on this route."

def realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP :
    List String := [
  "targetCoordinate",
  "dimensionNontrivial",
  "publicCoordinateHistory",
  "law",
  "transcript",
  "observerBit",
  "phaseA",
  "semantics",
  "observerEvidence",
  "pivotSummary",
  "epsMix",
  "safeCost",
  "safeBudget",
  "gaugeIncidence",
  "gaugeBound",
  "hiddenGaugeProduct",
  "fixedGapBudget",
  "phaseABudget",
  "epsSmall",
  "realCompressionLowerMachineData",
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameHypothesisAuditExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, UpperLowerClash follows from the no-target-rows CD-ENF mechanical constructor, the real lower machine, public-lock representative data, D.8 locked-message rigidity, finite CNF variable-family data, and the constant decoder regime, then StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The route derives singleMessage, noPublicTargetTags, and admissibleHistories from the checked no-target-rows surface; full M4 must still identify its public surface and history atoms with this constructor."

def realM4NoTargetRowsOfficialEndpointConstructionInputsExplicitPNP :
    List String :=
  realM4NoTargetRowsLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP ++
    realM4OfficialPNPBridgeConstructionInputs

theorem realM4NoTargetRowsOfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsOfficialEndpointConstructionInputsExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4NoTargetRowsOfficialEndpointHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsOfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsOfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsOfficialEndpointHypothesisAuditExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsOfficialEndpointStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, a Cook-style official separation follows from the no-target-rows component assembly, D.8 locked-message rigidity, StarSW hardness, the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge.  The no-target-rows constructor derives singleMessage, noPublicTargetTags, and admissibleHistories; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsCanonicalGapEndgameConstructionInputsExplicitPNP :
    List String := [
  "targetCoordinate",
  "dimensionNontrivial",
  "publicCoordinateHistory",
  "law",
  "transcript",
  "observerBit",
  "phaseA",
  "semantics",
  "observerEvidence",
  "pivotSummary",
  "epsMix",
  "safeCost",
  "safeBudget",
  "gaugeIncidence",
  "gaugeBound",
  "hiddenGaugeProduct",
  "epsSmall",
  "realCompressionLowerMachineData",
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4NoTargetRowsCanonicalGapEndgameConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapEndgameConstructionInputsExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsCanonicalGapEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsCanonicalGapEndgameHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapEndgameHypothesisAuditExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapEndgameStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, UpperLowerClash follows from the no-target-rows CD-ENF mechanical constructor, canonical Phase-A fixed-gap choice, the real lower machine, public-lock representative data, D.8 locked-message rigidity, finite CNF variable-family data, and the constant decoder regime, then StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The route derives singleMessage, noPublicTargetTags, admissibleHistories, and the phaseABudget inequality by construction; full M4 must still identify its public surface and history atoms with this constructor."

def realM4NoTargetRowsCanonicalGapOfficialEndpointConstructionInputsExplicitPNP :
    List String :=
  realM4NoTargetRowsCanonicalGapEndgameConstructionInputsExplicitPNP ++
    realM4OfficialPNPBridgeConstructionInputs

theorem realM4NoTargetRowsCanonicalGapOfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapOfficialEndpointConstructionInputsExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapOfficialEndpointHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsCanonicalGapOfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsCanonicalGapOfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapOfficialEndpointHypothesisAuditExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapOfficialEndpointStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, a Cook-style official separation follows from the no-target-rows canonical-gap component assembly, D.8 locked-message rigidity, StarSW hardness, the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge.  The route derives singleMessage, noPublicTargetTags, admissibleHistories, and phaseABudget; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP :
    List String := [
  "targetCoordinate",
  "dimensionNontrivial",
  "publicCoordinateHistory",
  "law",
  "transcript",
  "observerBit",
  "phaseA",
  "semantics",
  "observerEvidence",
  "pivotSummary",
  "epsMix",
  "safeCost",
  "safeBudget",
  "gaugeIncidence",
  "gaugeBound",
  "hiddenGaugeProduct",
  "realCompressionLowerMachineData",
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4NoTargetRowsCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapRealFrontierEndgameStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, UpperLowerClash follows from the no-target-rows CD-ENF mechanical constructor, canonical Phase-A fixed-gap choice, the real lower machine, public-lock representative data, D.8 locked-message rigidity, finite CNF variable-family data, and the constant decoder regime, then exactly StarSW hardness and the three real analytic frontier objects safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The route derives singleMessage, noPublicTargetTags, admissibleHistories, and phaseABudget by construction; boundaryMixing carries epsSmall, so epsSmall is not a separate construction input."

def realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP :
    List String :=
  realM4NoTargetRowsCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4OfficialPNPBridgeConstructionInputs

theorem realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP =
      [ "targetCoordinate",
        "dimensionNontrivial",
        "publicCoordinateHistory",
        "law",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "hiddenGaugeProduct",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsCanonicalGapRealFrontierOfficialEndpointStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, a Cook-style official separation follows from the no-target-rows canonical-gap real-frontier assembly, D.8 locked-message rigidity, exactly StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge.  The route derives singleMessage, noPublicTargetTags, admissibleHistories, and phaseABudget; boundaryMixing includes epsSmall.  This is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4CanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP :
    List String := [
  "realM4MechanicalInterfaceData",
  "realCompressionLowerMachineData",
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "finiteCNFVariableFamilyData",
  "realConstantDecoderRegime"
]

theorem realM4CanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP_exact :
    realM4CanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4CanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4CanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP_exact :
    realM4CanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CanonicalGapRealFrontierEndgameStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, UpperLowerClash follows from explicit mechanical data, canonical Phase-A fixed-gap choice, the real lower machine, public-lock representative data, D.8 locked-message rigidity, finite CNF variable-family data, and the constant decoder regime, then exactly StarSW hardness and the three analytic frontier fields safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The boundaryMixing frontier carries the strict epsMix < 1/2 witness; epsSmall is not a separate construction input on this route."

def realM4CanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP :
    List String :=
  realM4CanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4OfficialPNPBridgeConstructionInputs

theorem realM4CanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4CanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4CanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP :
    List String :=
  realM4CanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4CanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4CanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP =
      [ "realM4MechanicalInterfaceData",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4CanonicalGapRealFrontierOfficialEndpointStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, a Cook-style official separation follows from the canonical-gap real-frontier assembly, D.8 locked-message rigidity, exactly StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge.  BoundaryMixing includes epsSmall; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4OfficialEndpointConstructionInputsExplicitPNP : List String :=
  realM4CDENFComponentLowerMachineFiniteCNFVariablesCoverageAndRigidityEndgameConstructionInputsExplicitPNP ++
    realM4OfficialPNPBridgeConstructionInputs

theorem realM4OfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4OfficialEndpointConstructionInputsExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4OfficialEndpointHypothesisAuditExplicitPNP : List String :=
  realM4OfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4OfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4OfficialEndpointHypothesisAuditExplicitPNP =
      [ "law",
        "target",
        "publicInput",
        "neutralSkeleton",
        "oppositeSupport",
        "transcript",
        "observerBit",
        "phaseA",
        "semantics",
        "observerEvidence",
        "historyField",
        "pivotSummary",
        "epsMix",
        "safeCost",
        "safeBudget",
        "gaugeIncidence",
        "gaugeBound",
        "singleMessage",
        "hiddenGaugeProduct",
        "noPublicTargetTags",
        "admissibleHistories",
        "fixedGapBudget",
        "phaseABudget",
        "epsSmall",
        "realCompressionLowerMachineData",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "finiteCNFVariableFamilyData",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4OfficialEndpointStatementExplicitPNP : String :=
  "For the real v15/M4 staging layer, a Cook-style official separation follows from the sharp real component assembly, D.8 locked-message rigidity, StarSW hardness, the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge that names the separated NP language and proves the internal clash rules out membership in P.  D.7 plus D.8 construct the fixed public-message readout; this is conditional staging, not a proof of P != NP."

/-! ## Real-M4 lift ledger -/

inductive RealM4LiftStatus where
  | constructionTransferred
  | partialConstructionTransferred
  | openConstruction
  | blockedByCounterexample
  | irreducibleInput
  | pnpConditionalInput
deriving DecidableEq, Repr

structure RealM4LiftLedgerRow where
  item : String
  status : RealM4LiftStatus
  checkedName : String
  note : String
deriving Repr

/-- Current real-ensemble lift ledger.  The theorem above transfers the
single-message readout spine to the real linear public surface.  The remaining
M4 construction obligations are deliberately not collapsed into the four
irreducible mathematical inputs. -/
def realM4LiftLedger : List RealM4LiftLedgerRow := [
  {
    item := "singleMessageSpine"
    status := .constructionTransferred
    checkedName := "v13RealLinearSingleMessageSATSpine_singleMessage"
    note := "The real linear public instance fixes the target bit and valid witnesses read the same public message."
  },
  {
    item := "publicMessageInvariantAdapter"
    status := .constructionTransferred
    checkedName := "realM4LockedCoreSingleMessageSATSpine"
    note := "Given a public-message invariant, the Appendix D locked core maps into the real single-message spine and Appendix I CNF readout."
  },
  {
    item := "appendixICNFSpineAdapter"
    status := .constructionTransferred
    checkedName := "realM4CNFSingleMessageSATSpine"
    note := "Given the same public-message invariant, satisfying Appendix I CNF assignments form the real single-message SAT spine."
  },
  {
    item := "appendixISATSearchReadoutAdapter"
    status := .constructionTransferred
    checkedName := "realM4_supportedArbitraryOutputSATSearchCorrect_of_publicMessageInvariant"
    note := "Given the same public-message invariant, the Appendix I projection is correct for every satisfying assignment that SAT search may return."
  },
  {
    item := "cnfBitFixingSelfReduction"
    status := .constructionTransferred
    checkedName := "realM4_bitFixingReadout_eq_publicMessage_of_publicMessageInvariant"
    note := "Given a public-message invariant, a finite variable cover, and an explicit SAT decider, CNF bit-fixing produces a satisfying assignment whose projection is the public message."
  },
  {
    item := "finiteCNFVariableFamilyData"
    status := .openConstruction
    checkedName := "RealM4FiniteCNFVariableFamilyData"
    note := "The real M4 Appendix I construction must expose each public instance's CNF variable family as a finite type with decidable equality."
  },
  {
    item := "uniformCNFSupportData"
    status := .partialConstructionTransferred
    checkedName := "RealM4FiniteCNFVariableFamilyData.uniformSupport"
    note := "Once finite variable-family data is constructed, the uniform support package is the canonical enumeration of all variables; with the conditional decider it reconstructs the bit-fixing package."
  },
  {
    item := "constantDecoderUpperInequality"
    status := .partialConstructionTransferred
    checkedName := "realM4_uniformSelfReductionUpperHypothesis_givenPNP"
    note := "The uniform CNF bit-fixing decoder gives the formal upper inequality once the real lower framework identifies kpolyAt with this constant decoder cost, conditional on the explicit P=NP decider family."
  },
  {
    item := "selfReductionUpperDischargePackage"
    status := .partialConstructionTransferred
    checkedName := "RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity"
    note := "Public-lock representative data supplies D.7; together with D.8 rigidity it constructs the public-message invariant inside the explicit-P=NP upper package."
  },
  {
    item := "deterministicReadoutOnly"
    status := .blockedByCounterexample
    checkedName := "lockedCoreIdentityReadoutFamily_lab_refutation"
    note := "Deterministic per-state readout alone does not supply cross-completion message rigidity."
  },
  {
    item := "publicMessageInvariant"
    status := .partialConstructionTransferred
    checkedName := "realM4_lockedMessageData_of_coverageDataAndRigidity"
    note := "D.7 lock satisfiability plus D.8 rigidity construct the fixed public-message function used by the real readout adapters."
  },
  {
    item := "publicLockCoverageData"
    status := .openConstruction
    checkedName := "RealM4PublicLockCoverageData"
    note := "The real M4 Appendix I construction must give a supported public-instance representative for every supported public lock syntax."
  },
  {
    item := "publicLockSupportCoverage"
    status := .partialConstructionTransferred
    checkedName := "RealM4PublicLockCoverageData.publicLockCoverage"
    note := "The proposition-level Appendix D coverage condition follows from explicit public-lock representative data."
  },
  {
    item := "lockSatisfiable"
    status := .partialConstructionTransferred
    checkedName := "AppendixICNFReadoutData.core_lockSatisfiable_of_publicLockCovered"
    note := "Appendix I satisfiability on supported public instances gives D.7 once public-lock support coverage is supplied."
  },
  {
    item := "lockedMessageRigidityData"
    status := .partialConstructionTransferred
    checkedName := "realM4_lockedMessageData_of_coverageDataAndRigidity"
    note := "No longer a primitive open input on the sharp route: public-lock coverage supplies D.7 and D.8 rigidity constructs the public-message data."
  },
  {
    item := "lockedMessageRigidity"
    status := .openConstruction
    checkedName := "AppendixDLockedCore.LockedMessageRigidity"
    note := "The real M4 locked core must prove Appendix D.8: every accepted completion over a supported public lock carries the same message."
  },
  {
    item := "noPublicTargetTags"
    status := .partialConstructionTransferred
    checkedName := "RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents"
    note := "The adjusted real no-target-rows linear surface now fills the mechanical no-public-target-tags field in the CD-ENF constructor; full M4 still has to identify its neutral skeleton with this surface."
  },
  {
    item := "atomCompleteness"
    status := .constructionTransferred
    checkedName := "realM4_atomCompleteness_of_CDENF"
    note := "The generic CD-ENF semantics theorem supplies atom completeness for any real evidence semantics."
  },
  {
    item := "gaugeFaithfulness"
    status := .constructionTransferred
    checkedName := "realM4_gaugeFaithfulness_of_CDENF"
    note := "Gauge-leaf faithfulness is the gauge case of CD-ENF semantics; the separate real obligation is the hidden-gauge product law."
  },
  {
    item := "hiddenGaugeProduct"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.hiddenGaugeProduct"
    note := "The M4 hidden-gauge product law is not yet constructed."
  },
  {
    item := "admissibleHistories"
    status := .partialConstructionTransferred
    checkedName := "RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents"
    note := "The adjusted real no-target-rows linear surface now fills the mechanical admissible-histories field for a chosen public-coordinate history; full M4 histories still need manuscript-history atom identification and connection."
  },
  {
    item := "realCompressionLowerMachineData"
    status := .openConstruction
    checkedName := "RealM4CompressionLowerMachineData"
    note := "The real M4 construction must build the product-small-success/compression-from-success lower machine and its kernel-local half-bound from manuscript data."
  },
  {
    item := "realCompressionLowerFramework"
    status := .partialConstructionTransferred
    checkedName := "RealM4CompressionLowerMachineData.lowerFramework"
    note := "The v13 lower framework is obtained by forgetting the explicit real lower-machine data."
  },
  {
    item := "phaseABudget"
    status := .constructionTransferred
    checkedName := "RealM4EndgameMechanicalData.canonicalPhaseABudget"
    note := "The sharp canonical-gap route chooses the fixed gap budget to be the half-derivative bound, so the v13 Phase-A budget inequality is discharged by construction."
  },
  {
    item := "epsSmall"
    status := .partialConstructionTransferred
    checkedName := "RealM4MechanicalInterfaceData.BoundaryMixingFrontier.epsSmall"
    note := "On the real-frontier route, the strict epsMix < 1/2 witness is carried by the boundaryMixing analytic frontier rather than exposed as a separate construction input."
  },
  {
    item := "kernelNeutrality"
    status := .partialConstructionTransferred
    checkedName := "RealM4CompressionLowerMachineData.kernelNeutrality"
    note := "Kernel neutrality is supplied by the explicit real lower-machine data."
  },
  {
    item := "selfReductionUpper"
    status := .partialConstructionTransferred
    checkedName := "realM4_selfReductionUpperExplicitPNPDischarge_assignment_readout_cost_and_upper"
    note := "No longer a standalone global input: the real upper side follows from the explicit-P=NP discharge package, whose construction prerequisites and conditional decider input are listed separately."
  },
  {
    item := "realEndgameMechanicalInterfaceSplit"
    status := .partialConstructionTransferred
    checkedName := "RealM4MechanicalInterfaceData.withAnalyticFrontier"
    note := "Separates construction-level interface fields from the three analytic frontier fields before constructing the v13 clash interface."
  },
  {
    item := "realM4EndgameMechanicalData"
    status := .partialConstructionTransferred
    checkedName := "RealM4EndgameMechanicalData.ofComponents"
    note := "The endgame wrapper is assembled from explicit components; those components remain the construction obligations."
  },
  {
    item := "realConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_endgameMechanicalData_explicitPNP"
    note := "Given real endgame mechanical data, the explicit-P=NP upper discharge package, StarSW, and the three analytic fields, the v13 UpperLowerClash wiring is checked."
  },
  {
    item := "realCoveredLocksConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_coveredLocksAndRigidity_explicitPNP"
    note := "Constructs the explicit-P=NP upper package from public-lock coverage, D.8, uniform CNF support, and the constant decoder regime before invoking the v13 UpperLowerClash wiring."
  },
  {
    item := "realCoverageDataConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_coverageDataAndRigidity_explicitPNP"
    note := "Constructs the explicit-P=NP upper package from public-lock representative data, D.8, uniform CNF support, and the constant decoder regime before invoking the v13 UpperLowerClash wiring."
  },
  {
    item := "realCoverageAndLockedMessageDataConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_coverageDataAndLockedMessageData_explicitPNP"
    note := "Constructs the explicit-P=NP upper package from public-lock representative data, locked-message public-message data, uniform CNF support, and the constant decoder regime before invoking the v13 UpperLowerClash wiring."
  },
  {
    item := "realLowerMachineCoverageAndLockedMessageDataConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_lowerMachine_coverageDataAndLockedMessageData_explicitPNP"
    note := "Builds the endgame wrapper from explicit lower-machine data, then invokes the covered-lock and locked-message-data clash staging theorem."
  },
  {
    item := "realLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP"
    note := "Builds uniform CNF support from finite variable-family data before invoking the lower-machine, covered-lock, and locked-message-data clash staging theorem."
  },
  {
    item := "realComponentCoveredLocksConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_components_coveredLocksAndRigidity_explicitPNP"
    note := "Builds the endgame mechanical-data wrapper from explicit components before the covered-locks clash staging theorem is invoked."
  },
  {
    item := "realCDENFComponentCoveredLocksConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_CDENFComponents_coveredLocksAndRigidity_explicitPNP"
    note := "Builds both real mechanical wrappers from CD-ENF component data; atom completeness and gauge faithfulness are construction-transferred from generic CD-ENF semantics."
  },
  {
    item := "realCDENFComponentLowerMachineFiniteCNFVariablesCoverageAndLockedMessageDataConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_CDENFComponents_lowerMachine_finiteCNFVariables_coverageDataAndLockedMessageData_explicitPNP"
    note := "Builds CD-ENF mechanical data, lower framework/kernel neutrality, uniform CNF support, and the explicit-P=NP upper package from construction data before invoking the v13 clash wiring."
  },
  {
    item := "officialPNPBridgeData"
    status := .openConstruction
    checkedName := "RealM4OfficialPNPBridgeData"
    note := "The internal UpperLowerClash still needs a separate Cook-style endpoint bridge before it can be read as an official P-vs-NP separation statement."
  },
  {
    item := "officialPNPBridgeAdapter"
    status := .partialConstructionTransferred
    checkedName := "realM4_exists_np_not_p_from_internalClash_bridge"
    note := "Once the official bridge data is constructed, any internal UpperLowerClash can be transported to the explicit Cook-style endpoint ∃ L, inNP L ∧ ¬ inP L; this does not construct the bridge."
  },
  {
    item := "realOfficialEndpointStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_finiteCNFVariables_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP"
    note := "Wires the current no-target-rows, canonical-gap, real-frontier internal clash assembly through explicit Cook-style bridge data to ∃ L, inNP L ∧ ¬ inP L; the bridge and real construction fields remain exposed obligations."
  },
  {
    item := "pnpDecider"
    status := .pnpConditionalInput
    checkedName := "RealM4ExplicitPNPDeciderFamily"
    note := "This is the P=NP-side conditional object for the upper self-reduction, not irreducible lower-bound content."
  },
  {
    item := "starSWHardness"
    status := .irreducibleInput
    checkedName := "CompressionStarSWHardness"
    note := "Irreducible SW-shaped hardness input after the construction layer is real."
  },
  {
    item := "safeQSSM"
    status := .irreducibleInput
    checkedName := "SafeQSSMFrontier"
    note := "Irreducible analytic input after the construction layer is real."
  },
  {
    item := "boundedGaugeIncidence"
    status := .irreducibleInput
    checkedName := "BoundedGaugeIncidenceFrontier"
    note := "Irreducible analytic input after the construction layer is real."
  },
  {
    item := "boundaryMixing"
    status := .irreducibleInput
    checkedName := "BoundaryMixingFrontier"
    note := "Irreducible analytic input after the construction layer is real."
  }
]

theorem realM4LiftLedger_statuses_exact :
    List.map (fun row => row.status) realM4LiftLedger =
      [ RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.blockedByCounterexample,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.pnpConditionalInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput] := by
  rfl

def realM4OpenConstructionItems : List String := [
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "noPublicTargetTags",
  "hiddenGaugeProduct",
  "admissibleHistories",
  "finiteCNFVariableFamilyData",
  "realCompressionLowerMachineData",
  "officialPNPBridgeData"
]

theorem realM4OpenConstructionItems_exact :
    realM4OpenConstructionItems =
      [ "publicLockCoverageData",
        "lockedMessageRigidity",
        "noPublicTargetTags",
        "hiddenGaugeProduct",
        "admissibleHistories",
        "finiteCNFVariableFamilyData",
        "realCompressionLowerMachineData",
        "officialPNPBridgeData" ] := by
  rfl

def realM4AfterConstructionIrreducibleInputs : List String := [
  "starSWHardness",
  "safeQSSM",
  "boundedGaugeIncidence",
  "boundaryMixing"
]

theorem realM4AfterConstructionIrreducibleInputs_exact :
    realM4AfterConstructionIrreducibleInputs =
      [ "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

/-- Guardrail imported into the real lift: deterministic readout by itself has
a checked finite counterexample, so M4 must provide public-message invariance
or an equivalent cross-completion rigidity theorem before SAT-search promotion. -/
theorem realM4_deterministicReadoutOnly_counterexample :
    ∃ C : AppendixDLockedCore Unit Bool Unit Bool,
      C.LockSatisfiable ∧ C.ReadDeterministic ∧
        ¬ C.LockedMessageRigidity :=
  lockedCoreLabCanaries_separate_readDeterministic_from_lockedMessageRigidity.2

theorem realM4_publicMessageInvariant_guardrails :
    (rigidAppendixDLockedCore.PublicMessageInvariant
        rigidAppendixDLockedCore_publicMessage ∧
      rigidAppendixDLockedCore.LockedMessageRigidity) ∧
      (∀ publicMessage : Unit -> Bool,
        ¬ ambiguousAppendixDLockedCore.PublicMessageInvariant publicMessage) ∧
      ¬ ambiguousAppendixDLockedCore.LockedMessageRigidity :=
  lockedCorePublicMessageInvariant_lab_guardrails

end Mettapedia.Computability.PNP
