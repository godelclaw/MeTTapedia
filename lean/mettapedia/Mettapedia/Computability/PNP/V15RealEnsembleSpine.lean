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

universe u v w x y z a b c d e f g h i j k l p q

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

def clauseVars (clause : Clause Var) : List Var :=
  clause.map Literal.var

def formulaVars (formula : Formula Var) : List Var :=
  List.flatMap clauseVars formula

def dedupVars [DecidableEq Var] : List Var -> List Var
  | [] => []
  | v :: vars =>
      if v ∈ vars then
        dedupVars vars
      else
        v :: dedupVars vars

def formulaVarCover [DecidableEq Var] (formula : Formula Var) : List Var :=
  dedupVars (formulaVars formula)

theorem mem_dedupVars [DecidableEq Var] {v : Var} :
    ∀ {vars : List Var}, v ∈ dedupVars vars ↔ v ∈ vars
  | [] => by simp [dedupVars]
  | u :: vars => by
      by_cases hmem : u ∈ vars
      · by_cases hvu : v = u
        · constructor
          · intro hv
            have hvvars : v ∈ vars :=
              (mem_dedupVars (v := v) (vars := vars)).mp (by
                simpa [dedupVars, hmem] using hv)
            exact List.mem_cons_of_mem u hvvars
          · intro hv
            cases hv with
            | head =>
                simpa [dedupVars, hmem] using
                  (mem_dedupVars (v := v) (vars := vars)).mpr hmem
            | tail _ htail =>
                simpa [dedupVars, hmem] using
                  (mem_dedupVars (v := v) (vars := vars)).mpr htail
        · simp [dedupVars, hmem, mem_dedupVars, hvu]
      · by_cases hvu : v = u
        · subst hvu
          simp [dedupVars, hmem]
        · simp [dedupVars, hmem, mem_dedupVars, hvu]

theorem nodup_dedupVars [DecidableEq Var] :
    ∀ vars : List Var, (dedupVars vars).Nodup
  | [] => by simp [dedupVars]
  | v :: vars => by
      by_cases hmem : v ∈ vars
      · simp [dedupVars, hmem, nodup_dedupVars vars]
      · simp [dedupVars, hmem, nodup_dedupVars vars,
          mem_dedupVars]

theorem formulaUsesOnly_formulaVars (formula : Formula Var) :
    FormulaUsesOnly formula (formulaVars formula) := by
  intro clause hclause lit hlit
  unfold formulaVars clauseVars
  exact List.mem_flatMap.mpr
    ⟨clause, hclause, List.mem_map.mpr ⟨lit, hlit, rfl⟩⟩

theorem formulaVarCover_nodup [DecidableEq Var]
    (formula : Formula Var) :
    (formulaVarCover formula).Nodup := by
  unfold formulaVarCover
  exact nodup_dedupVars _

theorem formulaUsesOnly_formulaVarCover [DecidableEq Var]
    (formula : Formula Var) :
    FormulaUsesOnly formula (formulaVarCover formula) := by
  intro clause hclause lit hlit
  have hmem : lit.var ∈ formulaVars formula :=
    formulaUsesOnly_formulaVars formula hclause hlit
  unfold formulaVarCover
  exact mem_dedupVars.mpr hmem

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

def decidableEqOfNatCode {α : Type u} (code : α -> Nat)
    (code_injective : Function.Injective code) : DecidableEq α :=
  fun a b =>
    if h : code a = code b then
      isTrue (code_injective h)
    else
      isFalse (fun hab => h (congrArg code hab))

/-- Construction-side variable syntax coding for real Appendix I CNF
instances.  A real M4 variable family should be syntactic address data; an
injective natural-number code mechanically supplies decidable equality without
requiring the whole ambient variable type to be finite. -/
structure RealM4CNFVariableNatCodingData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (_D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varCode : (Y : Public) -> Var Y -> Nat
  varCode_injective : ∀ Y : Public, Function.Injective (varCode Y)

namespace RealM4CNFVariableNatCodingData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def varDecidable
    (C : RealM4CNFVariableNatCodingData D) :
    (Y : Public) -> DecidableEq (Var Y) :=
  fun Y => decidableEqOfNatCode (C.varCode Y) (C.varCode_injective Y)

end RealM4CNFVariableNatCodingData

/-- Encodable real CNF variable syntax for Appendix I instances.  The PNP
target does not depend on Mathlib's `Encodable`; this is the minimal local
program-syntax interface needed here: an encoder, a decoder, and the
decode-after-encode roundtrip.  It mechanically supplies the injective Nat
code used by the formula-syntax support route. -/
structure RealM4CNFVariableEncodableSyntaxData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (_D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varEncode : (Y : Public) -> Var Y -> Nat
  varDecode : (Y : Public) -> Nat -> Option (Var Y)
  varDecode_varEncode :
    ∀ (Y : Public) (v : Var Y), varDecode Y (varEncode Y v) = some v

namespace RealM4CNFVariableEncodableSyntaxData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def variableNatCoding
    (E : RealM4CNFVariableEncodableSyntaxData D) :
    RealM4CNFVariableNatCodingData D where
  varCode := E.varEncode
  varCode_injective := by
    intro Y v v' hcode
    have hdecode :
        E.varDecode Y (E.varEncode Y v) =
          E.varDecode Y (E.varEncode Y v') := by
      rw [hcode]
    rw [E.varDecode_varEncode Y v, E.varDecode_varEncode Y v'] at hdecode
    exact Option.some.inj hdecode

end RealM4CNFVariableEncodableSyntaxData

/--
Address-syntax presentation for real Appendix I CNF variables.  This is the
sharper construction boundary for the manuscript M4 route: the real variable
family should be parsed from tagged/address-style syntax, and that address
syntax should itself have an encoder/decoder roundtrip.  The derived
`RealM4CNFVariableEncodableSyntaxData` below is then mechanical.
-/
structure RealM4CNFVariableAddressSyntaxData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Address : Public -> Type a}
    {Var : Public -> Type y} {Witness : Public -> Type y}
    (_D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  addressEncode : (Y : Public) -> Address Y -> Nat
  addressDecode : (Y : Public) -> Nat -> Option (Address Y)
  addressDecode_addressEncode :
    ∀ (Y : Public) (addr : Address Y),
      addressDecode Y (addressEncode Y addr) = some addr
  varAddress : (Y : Public) -> Var Y -> Address Y
  varDecodeAddress : (Y : Public) -> Address Y -> Option (Var Y)
  varDecodeAddress_varAddress :
    ∀ (Y : Public) (v : Var Y),
      varDecodeAddress Y (varAddress Y v) = some v

namespace RealM4CNFVariableAddressSyntaxData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Address : Public -> Type a}
variable {Var : Public -> Type y} {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def encodableSyntax
    (A : RealM4CNFVariableAddressSyntaxData (Address := Address) D) :
    RealM4CNFVariableEncodableSyntaxData D where
  varEncode := fun Y v => A.addressEncode Y (A.varAddress Y v)
  varDecode := fun Y n =>
    match A.addressDecode Y n with
    | some addr => A.varDecodeAddress Y addr
    | none => none
  varDecode_varEncode := by
    intro Y v
    simp [A.addressDecode_addressEncode, A.varDecodeAddress_varAddress]

end RealM4CNFVariableAddressSyntaxData

/-- Top-level alias: injective natural coding of real CNF variables supplies
the decidable equality needed by formula-syntax CNF support. -/
def realM4_varDecidable_of_variableNatCoding
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (C : RealM4CNFVariableNatCodingData D) :
    (Y : Public) -> DecidableEq (Var Y) :=
  C.varDecidable

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

/--
Uniform CNF support extracted from the formula syntax itself.  Bit-fixing
needs a finite list covering the variables occurring in each finite CNF
formula, not a `Fintype` for the whole ambient variable type.  The remaining
construction-side obligation is decidable equality for the real variable
syntax at each public instance.
-/
def realM4_uniformCNFSupport_of_formulaSyntax
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness)
    (varDecidable : (Y : Public) -> DecidableEq (Var Y)) :
    RealM4CNFUniformSupportData D where
  varDecidable := varDecidable
  varOrder := fun Y =>
    letI := varDecidable Y
    ConcreteCNF.formulaVarCover (D.formula Y)
  varOrder_nodup := by
    intro Y
    letI := varDecidable Y
    exact ConcreteCNF.formulaVarCover_nodup (D.formula Y)
  formulaUsesOnly := by
    intro Y hY clause hclause lit hlit
    letI := varDecidable Y
    exact
      ConcreteCNF.formulaUsesOnly_formulaVarCover
        (D.formula Y) hclause hlit

namespace RealM4CNFVariableNatCodingData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def formulaSyntaxSupport
    (C : RealM4CNFVariableNatCodingData D) :
    RealM4CNFUniformSupportData D :=
  realM4_uniformCNFSupport_of_formulaSyntax D C.varDecidable

end RealM4CNFVariableNatCodingData

/-- Formula-syntax CNF support from injectively coded real variable syntax.
The finite cover still comes from each CNF formula; the variable coding only
supplies decidable equality for deduplication and bit-fixing. -/
def realM4_uniformCNFSupport_of_variableNatCoding
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (C : RealM4CNFVariableNatCodingData D) :
    RealM4CNFUniformSupportData D :=
  C.formulaSyntaxSupport

namespace RealM4CNFVariableEncodableSyntaxData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def formulaSyntaxSupport
    (E : RealM4CNFVariableEncodableSyntaxData D) :
    RealM4CNFUniformSupportData D :=
  E.variableNatCoding.formulaSyntaxSupport

end RealM4CNFVariableEncodableSyntaxData

/-- Top-level alias: locally encodable real variable syntax supplies the
Nat-coded variable package used by formula-syntax CNF support. -/
def realM4_variableNatCoding_of_encodableSyntax
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (E : RealM4CNFVariableEncodableSyntaxData D) :
    RealM4CNFVariableNatCodingData D :=
  E.variableNatCoding

/-- Top-level alias: real variable address syntax supplies the local
encode/decode package used by the formula-syntax CNF support route. -/
def realM4_variableEncodableSyntax_of_addressSyntax
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Address : Public -> Type a}
    {Var : Public -> Type y} {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (A : RealM4CNFVariableAddressSyntaxData (Address := Address) D) :
    RealM4CNFVariableEncodableSyntaxData D :=
  A.encodableSyntax

/-- Top-level alias: real variable address syntax supplies the Nat-coded
variable package through the local encode/decode layer. -/
def realM4_variableNatCoding_of_addressSyntax
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Address : Public -> Type a}
    {Var : Public -> Type y} {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (A : RealM4CNFVariableAddressSyntaxData (Address := Address) D) :
    RealM4CNFVariableNatCodingData D :=
  (realM4_variableEncodableSyntax_of_addressSyntax A).variableNatCoding

/-- Top-level alias: locally encodable real variable syntax supplies
formula-syntax CNF support, deriving decidable equality from the roundtrip
encoder/decoder rather than assuming a raw equality procedure. -/
def realM4_formulaSyntaxCNFSupport_of_encodableSyntax
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (E : RealM4CNFVariableEncodableSyntaxData D) :
    RealM4CNFUniformSupportData D :=
  E.formulaSyntaxSupport

/-- Top-level alias: real variable address syntax supplies formula-syntax CNF
support through the local encode/decode and Nat-coded routes. -/
def realM4_formulaSyntaxCNFSupport_of_addressSyntax
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Address : Public -> Type a}
    {Var : Public -> Type y} {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (A : RealM4CNFVariableAddressSyntaxData (Address := Address) D) :
    RealM4CNFUniformSupportData D :=
  (realM4_variableEncodableSyntax_of_addressSyntax A).formulaSyntaxSupport

/-- Construction-side finite variable-type data.  This is weaker than the
older finite variable-family package because it asks only for finite variable
types; decidable equality and formula-syntax support are supplied via the
derived Nat coding below. -/
structure RealM4FiniteCNFVariableTypeData
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    (_D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness) where
  varFintype : (Y : Public) -> Fintype (Var Y)

namespace RealM4FiniteCNFVariableTypeData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

/-- Any finite variable type has an injective Nat code through its canonical
equivalence with `Fin (card Var)`.  This is a construction supplier for the
Nat-coded formula-syntax route; an actual syntactic code is still the sharper
M4 obligation when the ambient variable type is not finite. -/
noncomputable def variableNatCoding
    (V : RealM4FiniteCNFVariableTypeData D) :
    RealM4CNFVariableNatCodingData D where
  varCode := fun Y v =>
    letI := V.varFintype Y
    (Fintype.equivFin (Var Y) v).val
  varCode_injective := by
    intro Y v v' hcode
    letI := V.varFintype Y
    have hfin :
        Fintype.equivFin (Var Y) v =
          Fintype.equivFin (Var Y) v' := by
      apply Fin.ext
      exact hcode
    exact (Fintype.equivFin (Var Y)).injective hfin

noncomputable def formulaSyntaxSupport
    (V : RealM4FiniteCNFVariableTypeData D) :
    RealM4CNFUniformSupportData D :=
  (V.variableNatCoding).formulaSyntaxSupport

end RealM4FiniteCNFVariableTypeData

/-- Top-level alias: finite real CNF variable types supply the Nat-coded
variable package used by the formula-syntax support route. -/
noncomputable def realM4_variableNatCoding_of_finiteVariableTypes
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (V : RealM4FiniteCNFVariableTypeData D) :
    RealM4CNFVariableNatCodingData D :=
  V.variableNatCoding

/-- Top-level alias: finite variable types supply formula-syntax CNF support
through the Nat-coded route, avoiding a primitive decidable-equality input. -/
noncomputable def realM4_formulaSyntaxCNFSupport_of_finiteVariableTypes
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (V : RealM4FiniteCNFVariableTypeData D) :
    RealM4CNFUniformSupportData D :=
  V.formulaSyntaxSupport

namespace RealM4FiniteCNFVariableFamilyData

variable {PublicLock : Type u} {Quotient : Type v}
variable {LockAux : Type w} {Message : Type z}
variable {Public : Type x} {Var : Public -> Type y}
variable {Witness : Public -> Type y}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message Public Var Witness}

def finiteTypeData
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4FiniteCNFVariableTypeData D where
  varFintype := V.varFintype

noncomputable def variableNatCoding
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4CNFVariableNatCodingData D :=
  V.finiteTypeData.variableNatCoding

noncomputable def formulaSyntaxSupportViaNatCoding
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4CNFUniformSupportData D :=
  V.finiteTypeData.formulaSyntaxSupport

end RealM4FiniteCNFVariableFamilyData

/-- Backward-compatible alias: the older finite variable-family package
supplies the newer Nat-coded variable package. -/
noncomputable def realM4_variableNatCoding_of_finiteVariables
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4CNFVariableNatCodingData D :=
  V.variableNatCoding

/-- Backward-compatible alias: the older finite variable-family package
supplies formula-syntax CNF support through the newer Nat-coded route. -/
noncomputable def realM4_formulaSyntaxCNFSupport_of_finiteVariablesNatCoding
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (V : RealM4FiniteCNFVariableFamilyData D) :
    RealM4CNFUniformSupportData D :=
  V.formulaSyntaxSupportViaNatCoding

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

theorem realCNFConstantDecoderKpolyAt_const
    {Var : Type u} (D : RealCNFPNPSATDecider Var)
    (targetBlocks targetBlocks' : Nat) :
    realCNFConstantDecoderKpolyAt D targetBlocks =
      realCNFConstantDecoderKpolyAt D targetBlocks' :=
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

theorem realM4UniformConstantDecoderKpolyAt_const
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    (U : RealM4CNFUniformBitFixingData D)
    (targetBlocks targetBlocks' : Nat) :
    realM4UniformConstantDecoderKpolyAt U targetBlocks =
      realM4UniformConstantDecoderKpolyAt U targetBlocks' :=
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

/-- Named constructor for the real constant-decoder regime from the explicit
K-poly compatibility facts.  The fixed program model is already the constant
function `realM4UniformConstantDecoderKpolyAt`; what remains for the real M4
lower framework is to identify its `kpolyAt` and `etaTimes` with this model
and prove the numeric floor inequality. -/
def realM4_uniformConstantDecoderRegime_of_kpolyCompatibility
    {PublicLock : Type u} {Quotient : Type v}
    {LockAux : Type w} {Message : Type z}
    {Public : Type x} {Var : Public -> Type y}
    {Witness : Public -> Type y}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message Public Var Witness}
    {F : CompressionLowerFramework}
    (U : RealM4CNFUniformBitFixingData D)
    (eta : Nat)
    (kpolyAt_eq : F.kpolyAt = realM4UniformConstantDecoderKpolyAt U)
    (etaTimes_eq : F.etaTimes = realCNFLinearEtaTimes eta)
    (floor_dominates_decoder :
      realM4UniformSelfReductionDecoderCost U < eta * F.targetBlocks) :
    RealM4UniformConstantDecoderRegime F U where
  eta := eta
  kpolyAt_eq := kpolyAt_eq
  etaTimes_eq := etaTimes_eq
  floor_dominates_decoder := floor_dominates_decoder

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

def realM4FiniteCNFVariableTypeDataConstructionInputs : List String := [
  "varFintype"
]

theorem realM4FiniteCNFVariableTypeDataConstructionInputs_exact :
    realM4FiniteCNFVariableTypeDataConstructionInputs =
      [ "varFintype" ] := by
  rfl

def realM4VariableNatCodingFromFiniteTypeConstructionInputs :
    List String := [
  "cnfVariableFintype"
]

theorem realM4VariableNatCodingFromFiniteTypeConstructionInputs_exact :
    realM4VariableNatCodingFromFiniteTypeConstructionInputs =
      [ "cnfVariableFintype" ] := by
  rfl

def realM4FormulaSyntaxCNFSupportConstructionInputs : List String := [
  "varDecidable"
]

theorem realM4FormulaSyntaxCNFSupportConstructionInputs_exact :
    realM4FormulaSyntaxCNFSupportConstructionInputs =
      [ "varDecidable" ] := by
  rfl

def realM4VariableNatCodingConstructionInputs : List String := [
  "varCode",
  "varCodeInjective"
]

theorem realM4VariableNatCodingConstructionInputs_exact :
    realM4VariableNatCodingConstructionInputs =
      [ "varCode",
        "varCodeInjective" ] := by
  rfl

def realM4VariableEncodableSyntaxConstructionInputs : List String := [
  "varEncode",
  "varDecode",
  "varDecodeEncodeRoundtrip"
]

theorem realM4VariableEncodableSyntaxConstructionInputs_exact :
    realM4VariableEncodableSyntaxConstructionInputs =
      [ "varEncode",
        "varDecode",
        "varDecodeEncodeRoundtrip" ] := by
  rfl

def realM4VariableAddressSyntaxConstructionInputs : List String := [
  "addressEncode",
  "addressDecode",
  "addressDecodeEncodeRoundtrip",
  "varAddress",
  "varDecodeAddress",
  "varDecodeAddressRoundtrip"
]

theorem realM4VariableAddressSyntaxConstructionInputs_exact :
    realM4VariableAddressSyntaxConstructionInputs =
      [ "addressEncode",
        "addressDecode",
        "addressDecodeEncodeRoundtrip",
        "varAddress",
        "varDecodeAddress",
        "varDecodeAddressRoundtrip" ] := by
  rfl

def realM4VariableEncodableSyntaxFromAddressSyntaxConstructionInputs :
    List String := [
  "cnfVariableAddressSyntax"
]

theorem realM4VariableEncodableSyntaxFromAddressSyntaxConstructionInputs_exact :
    realM4VariableEncodableSyntaxFromAddressSyntaxConstructionInputs =
      [ "cnfVariableAddressSyntax" ] := by
  rfl

def realM4VariableNatCodingFromEncodableSyntaxConstructionInputs :
    List String := [
  "cnfVariableEncodableSyntax"
]

theorem realM4VariableNatCodingFromEncodableSyntaxConstructionInputs_exact :
    realM4VariableNatCodingFromEncodableSyntaxConstructionInputs =
      [ "cnfVariableEncodableSyntax" ] := by
  rfl

def realM4VariableNatCodingFromAddressSyntaxConstructionInputs :
    List String := [
  "cnfVariableAddressSyntax"
]

theorem realM4VariableNatCodingFromAddressSyntaxConstructionInputs_exact :
    realM4VariableNatCodingFromAddressSyntaxConstructionInputs =
      [ "cnfVariableAddressSyntax" ] := by
  rfl

def realM4FormulaSyntaxCNFSupportFromNatCodingConstructionInputs :
    List String := [
  "cnfVariableNatCoding"
]

theorem realM4FormulaSyntaxCNFSupportFromNatCodingConstructionInputs_exact :
    realM4FormulaSyntaxCNFSupportFromNatCodingConstructionInputs =
      [ "cnfVariableNatCoding" ] := by
  rfl

def realM4FormulaSyntaxCNFSupportFromEncodableSyntaxConstructionInputs :
    List String := [
  "cnfVariableEncodableSyntax"
]

theorem realM4FormulaSyntaxCNFSupportFromEncodableSyntaxConstructionInputs_exact :
    realM4FormulaSyntaxCNFSupportFromEncodableSyntaxConstructionInputs =
      [ "cnfVariableEncodableSyntax" ] := by
  rfl

def realM4FormulaSyntaxCNFSupportFromAddressSyntaxConstructionInputs :
    List String := [
  "cnfVariableAddressSyntax"
]

theorem realM4FormulaSyntaxCNFSupportFromAddressSyntaxConstructionInputs_exact :
    realM4FormulaSyntaxCNFSupportFromAddressSyntaxConstructionInputs =
      [ "cnfVariableAddressSyntax" ] := by
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

def realM4ConstantDecoderRegimeConstructionInputs : List String := [
  "uniformCNFBitFixingPackage",
  "realCompressionLowerFramework",
  "kpolyAtConstantDecoderIdentification",
  "etaTimesLinearFloorIdentification",
  "constantDecoderBelowLinearFloor"
]

theorem realM4ConstantDecoderRegimeConstructionInputs_exact :
    realM4ConstantDecoderRegimeConstructionInputs =
      [ "uniformCNFBitFixingPackage",
        "realCompressionLowerFramework",
        "kpolyAtConstantDecoderIdentification",
        "etaTimesLinearFloorIdentification",
        "constantDecoderBelowLinearFloor" ] := by
  rfl

def realM4ConstantDecoderRegimeExplicitPNPConstructionInputs : List String := [
  "uniformCNFSupportData",
  "realCompressionLowerFramework",
  "kpolyAtConstantDecoderIdentification",
  "etaTimesLinearFloorIdentification",
  "constantDecoderBelowLinearFloor"
]

theorem realM4ConstantDecoderRegimeExplicitPNPConstructionInputs_exact :
    realM4ConstantDecoderRegimeExplicitPNPConstructionInputs =
      [ "uniformCNFSupportData",
        "realCompressionLowerFramework",
        "kpolyAtConstantDecoderIdentification",
        "etaTimesLinearFloorIdentification",
        "constantDecoderBelowLinearFloor" ] := by
  rfl

def realM4ConstantDecoderProgramModelConstructionInputs : List String := [
  "explicitPNPDeciderProgramLengthBound",
  "fixedRestrictedFormulaCompilerProgram",
  "fixedBitFixingDriverProgram",
  "fixedReadoutProgram"
]

theorem realM4ConstantDecoderProgramModelConstructionInputs_exact :
    realM4ConstantDecoderProgramModelConstructionInputs =
      [ "explicitPNPDeciderProgramLengthBound",
        "fixedRestrictedFormulaCompilerProgram",
        "fixedBitFixingDriverProgram",
        "fixedReadoutProgram" ] := by
  rfl

def realM4ConstantDecoderProgramModelStatement : String :=
  "The real v15/M4 upper-side K-poly model has a target-block-constant decoder cost: a uniform P=NP SAT-decider program-length bound plus the fixed restricted-formula compiler, bit-fixing driver, and readout program.  The remaining real constant-decoder-regime obligation is lower-framework compatibility: identify kpolyAt with this constant program, identify etaTimes with the linear floor, and prove the constant sits below that floor."

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
  "realCompressionLowerFramework",
  "realConstantDecoderRegime"
]

theorem realM4SelfReductionUpperDischargePrerequisites_exact :
    realM4SelfReductionUpperDischargePrerequisites =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFBitFixingPackage",
        "realCompressionLowerFramework",
        "realConstantDecoderRegime" ] := by
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
  "realCompressionLowerFramework",
  "realConstantDecoderRegime"
]

theorem realM4SelfReductionUpperExplicitPNPConstructionInputs_exact :
    realM4SelfReductionUpperExplicitPNPConstructionInputs =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "realCompressionLowerFramework",
        "realConstantDecoderRegime" ] := by
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
Formula-syntax support version of the canonical-gap real-frontier staging
theorem.  The CNF variable cover is extracted from the finite formula syntax,
so this route does not require a `Fintype` for the whole ambient variable
family.  The remaining construction obligation on the upper-side syntax is
decidable equality for variables at each public instance, while the P=NP
decider family remains an explicit conditional input.
-/
theorem realM4_conditionalClash_from_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
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
    (varDecidable : (Y : CNFPublic) -> DecidableEq (Var Y))
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_uniformCNFSupport_of_formulaSyntax
          D varDecidable).withPNPDecider pnpDeciderFamily))
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
          (realM4_uniformCNFSupport_of_formulaSyntax D varDecidable)
          pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_coverageDataAndRigidity_explicitPNP
    (RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      M boundaryMixing.epsSmall lowerMachine)
    defaultMessage coverageData lockedMessageRigidity
    (realM4_uniformCNFSupport_of_formulaSyntax D varDecidable)
    pnpDeciderFamily constantDecoderRegime starSWHardness
    safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
    boundaryMixing.boundaryMixing

/--
Address-syntax version of the canonical-gap real-frontier staging theorem.
The real CNF address syntax constructs the local syntax roundtrip, Nat coding,
and formula-syntax support used by the upper-side self-reduction.  Address
syntax itself remains a visible M4 construction input, and the P=NP decider
family remains an explicit conditional input.
-/
theorem realM4_conditionalClash_from_lowerMachine_addressSyntax_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_formulaSyntaxCNFSupport_of_addressSyntax
          variableAddressSyntax).withPNPDecider pnpDeciderFamily))
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
          (realM4_formulaSyntaxCNFSupport_of_addressSyntax variableAddressSyntax)
          pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_coverageDataAndRigidity_explicitPNP
    (RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      M boundaryMixing.epsSmall lowerMachine)
    defaultMessage coverageData lockedMessageRigidity
    (realM4_formulaSyntaxCNFSupport_of_addressSyntax variableAddressSyntax)
    pnpDeciderFamily constantDecoderRegime starSWHardness
    safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
    boundaryMixing.boundaryMixing

/--
Locked-message-data version of the address-syntax canonical-gap real-frontier
staging theorem.  This route uses the explicit public-message invariant
package for the upper readout side, rather than taking a raw D.8 rigidity
proposition and a default message at the theorem boundary.
-/
theorem realM4_conditionalClash_from_lowerMachine_addressSyntax_coverageDataAndLockedMessageData_canonicalGap_realFrontier_explicitPNP
    {Omega : Type u} [Fintype Omega] [Nonempty Omega]
    {Public : Type v} {Neutral : Type w} {Safe : Type x}
    {Gauge : Type y} {Transcript : Type z} [DecidableEq Transcript]
    {Pair : Type a} [Fintype Pair]
    {Stage : Type b} {Branch : Type c}
    {HistoryAtom : Type d} {Pivot : Type e}
    {Observer : Type f} {Output : Type f} {Skeleton : Type w}
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    (M : RealM4MechanicalInterfaceData Omega Public Neutral Safe Gauge
      Transcript Pair Stage Branch HistoryAtom Pivot Observer Output Skeleton)
    (lowerMachine : RealM4CompressionLowerMachineData)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_formulaSyntaxCNFSupport_of_addressSyntax
          variableAddressSyntax).withPNPDecider pnpDeciderFamily))
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
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
          (D := D) (F := lowerMachine.lowerFramework)
          coverageData lockedMessageData
          (realM4_formulaSyntaxCNFSupport_of_addressSyntax variableAddressSyntax)
          pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_coverageDataAndLockedMessageData_explicitPNP
    (RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      M boundaryMixing.epsSmall lowerMachine)
    coverageData lockedMessageData
    (realM4_formulaSyntaxCNFSupport_of_addressSyntax variableAddressSyntax)
    pnpDeciderFamily constantDecoderRegime starSWHardness
    safeQSSM.safeQSSM boundedGaugeIncidence.boundedGaugeIncidence
    boundaryMixing.boundaryMixing

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

/-- The Cook-style class equality proposition: every NP language is in P. -/
def pEqualsNP (C : CookStylePNPClassInterface) : Prop :=
  ∀ L : C.Language, C.inNP L -> C.inP L

theorem officialSeparation_of_np_not_p
    (C : CookStylePNPClassInterface) {L : C.Language}
    (hNP : C.inNP L) (hNotP : ¬ C.inP L) :
    C.officialSeparation :=
  C.officialSeparation_iff_exists_np_not_p.mpr ⟨L, hNP, hNotP⟩

theorem not_pEqualsNP_of_np_not_p
    (C : CookStylePNPClassInterface) {L : C.Language}
    (hNP : C.inNP L) (hNotP : ¬ C.inP L) :
    ¬ C.pEqualsNP := by
  intro hEq
  exact hNotP (hEq L hNP)

/-- In the abstract Cook-style endpoint interface, official separation is
equivalent to the negation of the class-equality proposition `P = NP`. -/
theorem officialSeparation_iff_not_pEqualsNP
    (C : CookStylePNPClassInterface) :
    C.officialSeparation ↔ ¬ C.pEqualsNP := by
  classical
  rw [C.officialSeparation_iff_exists_np_not_p]
  constructor
  · intro hSep
    rcases hSep with ⟨L, hNP, hNotP⟩
    exact C.not_pEqualsNP_of_np_not_p hNP hNotP
  · intro hNotEq
    by_contra hNoWitness
    apply hNotEq
    intro L hNP
    by_contra hNotP
    exact hNoWitness ⟨L, hNP, hNotP⟩

theorem officialSeparation_of_not_pEqualsNP
    (C : CookStylePNPClassInterface) (hNotEq : ¬ C.pEqualsNP) :
    C.officialSeparation :=
  (C.officialSeparation_iff_not_pEqualsNP).mpr hNotEq

theorem not_pEqualsNP_of_officialSeparation
    (C : CookStylePNPClassInterface) (hSep : C.officialSeparation) :
    ¬ C.pEqualsNP :=
  (C.officialSeparation_iff_not_pEqualsNP).mp hSep

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
Degenerate official-bridge inhabitant from an arbitrary NP language.
Because `UpperLowerClash` contains `False`, a bridge whose only anti-P
argument is `UpperLowerClash L P -> ¬ inP` can be filled by ex falso.  This is
a guardrail theorem: the raw bridge data below is only a typed endpoint
adapter, not the real Cook-style bridge required for serious PNP progress.
-/
def realM4_officialBridgeData_of_npWitness_exFalso
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
    (language : C.Language) (hNP : C.inNP language) :
    RealM4OfficialPNPBridgeData L P C where
  separatedLanguage := language
  separatedLanguage_inNP := hNP
  internalClash_not_inP := by
    intro clash hP
    exact False.elim clash.noConsistentBounds

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
Stricter Cook-style bridge boundary for the real endpoint.

Unlike `RealM4OfficialPNPBridgeData`, this data does not consume an already
contradictory `UpperLowerClash`.  It names an NP language and requires a proof
that P-membership for that language supplies the explicit upper-side
self-reduction discharge used by the real endgame.  The lower machine,
StarSW hardness, and the three analytic fields remain outside this bridge.
-/
structure RealM4OfficialPToUpperBridgeData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p}) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage
  upperDischarge_of_inP :
    C.inP separatedLanguage -> RealM4SelfReductionUpperExplicitPNPDischarge D F

/--
Construction-side support for the decomposed official P-to-decider bridge.
These are M4/Appendix-I upper ingredients, not official complexity-class
content: a default message, public-lock coverage, D.8 rigidity, and uniform
CNF support.
-/
structure RealM4OfficialPToDeciderUpperSupportData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness) where
  defaultMessage : Message
  coverageData : RealM4PublicLockCoverageData D
  lockedMessageRigidity : D.core.LockedMessageRigidity
  uniformSupport : RealM4CNFUniformSupportData D

namespace RealM4OfficialPToDeciderUpperSupportData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}

/-- Package construction-side official upper support from already-derived
uniform CNF support. -/
def ofCoverageRigidityAndUniformSupport
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (uniformSupport : RealM4CNFUniformSupportData D) :
    RealM4OfficialPToDeciderUpperSupportData D where
  defaultMessage := defaultMessage
  coverageData := coverageData
  lockedMessageRigidity := lockedMessageRigidity
  uniformSupport := uniformSupport

/-- Package construction-side official upper support from injectively
Nat-coded formula syntax. -/
def ofCoverageRigidityAndVariableNatCoding
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableNatCoding : RealM4CNFVariableNatCodingData D) :
    RealM4OfficialPToDeciderUpperSupportData D :=
  ofCoverageRigidityAndUniformSupport defaultMessage coverageData
    lockedMessageRigidity
    (realM4_uniformCNFSupport_of_variableNatCoding variableNatCoding)

/-- Package construction-side official upper support from locally encodable
real variable syntax.  This is the sharper supplier for the real M4 route:
syntax roundtrip data yields the Nat coding, which yields decidable equality
and formula-syntax CNF support. -/
def ofCoverageRigidityAndEncodableSyntax
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableSyntax : RealM4CNFVariableEncodableSyntaxData D) :
    RealM4OfficialPToDeciderUpperSupportData D :=
  ofCoverageRigidityAndVariableNatCoding defaultMessage coverageData
    lockedMessageRigidity
    (realM4_variableNatCoding_of_encodableSyntax variableSyntax)

/-- Package construction-side official upper support from real variable
address syntax. -/
def ofCoverageRigidityAndAddressSyntax
    {Address : CNFPublic -> Type a}
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D) :
    RealM4OfficialPToDeciderUpperSupportData D :=
  ofCoverageRigidityAndEncodableSyntax defaultMessage coverageData
    lockedMessageRigidity
    (realM4_variableEncodableSyntax_of_addressSyntax variableAddressSyntax)

end RealM4OfficialPToDeciderUpperSupportData

/--
Construction-side support for the decomposed official P-to-decider bridge
when the public-message invariant is carried as explicit locked-message data.
Unlike `RealM4OfficialPToDeciderUpperSupportData`, this support package does
not need a default message or a raw D.8 proposition at the theorem boundary.
-/
structure RealM4OfficialPToDeciderLockedMessageUpperSupportData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness) where
  coverageData : RealM4PublicLockCoverageData D
  lockedMessageData : RealM4LockedMessageRigidityData D.core
  uniformSupport : RealM4CNFUniformSupportData D

namespace RealM4OfficialPToDeciderLockedMessageUpperSupportData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}

def ofCoverageLockedMessageDataAndUniformSupport
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (uniformSupport : RealM4CNFUniformSupportData D) :
    RealM4OfficialPToDeciderLockedMessageUpperSupportData D where
  coverageData := coverageData
  lockedMessageData := lockedMessageData
  uniformSupport := uniformSupport

def ofCoverageLockedMessageDataAndVariableNatCoding
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableNatCoding : RealM4CNFVariableNatCodingData D) :
    RealM4OfficialPToDeciderLockedMessageUpperSupportData D :=
  ofCoverageLockedMessageDataAndUniformSupport coverageData lockedMessageData
    (realM4_uniformCNFSupport_of_variableNatCoding variableNatCoding)

def ofCoverageLockedMessageDataAndEncodableSyntax
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableSyntax : RealM4CNFVariableEncodableSyntaxData D) :
    RealM4OfficialPToDeciderLockedMessageUpperSupportData D :=
  ofCoverageLockedMessageDataAndVariableNatCoding coverageData
    lockedMessageData
    (realM4_variableNatCoding_of_encodableSyntax variableSyntax)

def ofCoverageLockedMessageDataAndAddressSyntax
    {Address : CNFPublic -> Type a}
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D) :
    RealM4OfficialPToDeciderLockedMessageUpperSupportData D :=
  ofCoverageLockedMessageDataAndEncodableSyntax coverageData
    lockedMessageData
    (realM4_variableEncodableSyntax_of_addressSyntax variableAddressSyntax)

end RealM4OfficialPToDeciderLockedMessageUpperSupportData

/--
Official-language part of the decomposed P-to-decider bridge.  This is the
remaining Cook-style bridge content after construction-side M4 support has
been separated: name the NP language, prove it is in NP, and show that
P-membership for that language supplies the explicit SAT-decider family and
constant-decoder regime required by the upper self-reduction.
-/
structure RealM4OfficialPToDeciderLanguageData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p})
    (S : RealM4OfficialPToDeciderUpperSupportData D) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage
  pnpDeciderFamily_of_inP :
    C.inP separatedLanguage -> RealM4ExplicitPNPDeciderFamily D
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (S.uniformSupport.withPNPDecider (pnpDeciderFamily_of_inP hP))

/-- The official-language witness part of the Cook-style bridge, separated
from the P-membership consequences. -/
structure RealM4OfficialLanguageNPData
    (C : CookStylePNPClassInterface.{p}) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage

/-- The P-membership-to-SAT-decider part of the Cook-style bridge, separated
from both the named NP language and the K-poly constant-decoder regime. -/
structure RealM4OfficialPToDeciderFamilyData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (C : CookStylePNPClassInterface.{p})
    (N : RealM4OfficialLanguageNPData C) where
  pnpDeciderFamily_of_inP :
    C.inP N.separatedLanguage -> RealM4ExplicitPNPDeciderFamily D

/--
Support-neutral P-membership-to-constant-decoder-regime data.  The real
K-poly/floor compatibility obligation depends on the uniform CNF support and
the P-derived SAT decider family, not on whether the readout support package is
the legacy default-message/D.8 route or the explicit locked-message-data route.
-/
structure RealM4OfficialPToUniformConstantDecoderRegimeData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p})
    (uniformSupport : RealM4CNFUniformSupportData D)
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N) where
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP N.separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider (P.pnpDeciderFamily_of_inP hP))

/-- The P-membership-to-constant-decoder-regime part of the Cook-style bridge.
This keeps the real K-poly/floor compatibility obligation separate from the
mere construction of SAT deciders from P-membership. -/
structure RealM4OfficialPToConstantDecoderRegimeData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p})
    (S : RealM4OfficialPToDeciderUpperSupportData D)
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N) where
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP N.separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (S.uniformSupport.withPNPDecider (P.pnpDeciderFamily_of_inP hP))

/-- Official-language package for the locked-message-data bridge route. -/
structure RealM4OfficialPToDeciderLockedMessageLanguageData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p})
    (S : RealM4OfficialPToDeciderLockedMessageUpperSupportData D) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage
  pnpDeciderFamily_of_inP :
    C.inP separatedLanguage -> RealM4ExplicitPNPDeciderFamily D
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (S.uniformSupport.withPNPDecider (pnpDeciderFamily_of_inP hP))

/-- The P-membership-to-constant-decoder-regime obligation for the
locked-message-data official bridge route. -/
structure RealM4OfficialPToLockedMessageConstantDecoderRegimeData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p})
    (S : RealM4OfficialPToDeciderLockedMessageUpperSupportData D)
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N) where
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP N.separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (S.uniformSupport.withPNPDecider (P.pnpDeciderFamily_of_inP hP))

namespace RealM4OfficialPToUniformConstantDecoderRegimeData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}
variable {F : CompressionLowerFramework}
variable {C : CookStylePNPClassInterface.{p}}
variable {uniformSupport : RealM4CNFUniformSupportData D}
variable {N : RealM4OfficialLanguageNPData C}
variable {P : RealM4OfficialPToDeciderFamilyData D C N}

/-- Build the support-neutral official constant-decoder obligation from
explicit P-membership-indexed K-poly compatibility facts.  This keeps the
program model fixed and exposes the remaining real obligation: P-membership
must provide the real lower-framework identification and floor inequality for
the P-derived decider family. -/
def ofKpolyCompatibility
    (eta_of_inP : C.inP N.separatedLanguage -> Nat)
    (kpolyAt_eq_of_inP :
      ∀ hP : C.inP N.separatedLanguage,
        F.kpolyAt =
          realM4UniformConstantDecoderKpolyAt
            (uniformSupport.withPNPDecider
              (P.pnpDeciderFamily_of_inP hP)))
    (etaTimes_eq_of_inP :
      ∀ hP : C.inP N.separatedLanguage,
        F.etaTimes = realCNFLinearEtaTimes (eta_of_inP hP))
    (floor_dominates_decoder_of_inP :
      ∀ hP : C.inP N.separatedLanguage,
        realM4UniformSelfReductionDecoderCost
            (uniformSupport.withPNPDecider
              (P.pnpDeciderFamily_of_inP hP)) <
          (eta_of_inP hP) * F.targetBlocks) :
    RealM4OfficialPToUniformConstantDecoderRegimeData
      D F C uniformSupport N P where
  constantDecoderRegime_of_inP := by
    intro hP
    exact
      realM4_uniformConstantDecoderRegime_of_kpolyCompatibility
        (uniformSupport.withPNPDecider (P.pnpDeciderFamily_of_inP hP))
        (eta_of_inP hP)
        (kpolyAt_eq_of_inP hP)
        (etaTimes_eq_of_inP hP)
        (floor_dominates_decoder_of_inP hP)

/-- Reindex support-neutral constant-decoder data to the legacy upper-support
package. -/
def toLegacySupport
    (S : RealM4OfficialPToDeciderUpperSupportData D)
    (R :
      RealM4OfficialPToUniformConstantDecoderRegimeData
        D F C S.uniformSupport N P) :
    RealM4OfficialPToConstantDecoderRegimeData D F C S N P where
  constantDecoderRegime_of_inP := R.constantDecoderRegime_of_inP

/-- Reindex support-neutral constant-decoder data to the locked-message
upper-support package. -/
def toLockedMessageSupport
    (S : RealM4OfficialPToDeciderLockedMessageUpperSupportData D)
    (R :
      RealM4OfficialPToUniformConstantDecoderRegimeData
        D F C S.uniformSupport N P) :
    RealM4OfficialPToLockedMessageConstantDecoderRegimeData D F C S N P where
  constantDecoderRegime_of_inP := R.constantDecoderRegime_of_inP

/-- Forget the legacy readout-support wrapper from a constant-decoder regime. -/
def ofLegacySupport
    {S : RealM4OfficialPToDeciderUpperSupportData D}
    (R : RealM4OfficialPToConstantDecoderRegimeData D F C S N P) :
    RealM4OfficialPToUniformConstantDecoderRegimeData
      D F C S.uniformSupport N P where
  constantDecoderRegime_of_inP := R.constantDecoderRegime_of_inP

/-- Forget the locked-message readout-support wrapper from a
constant-decoder regime. -/
def ofLockedMessageSupport
    {S : RealM4OfficialPToDeciderLockedMessageUpperSupportData D}
    (R : RealM4OfficialPToLockedMessageConstantDecoderRegimeData
      D F C S N P) :
    RealM4OfficialPToUniformConstantDecoderRegimeData
      D F C S.uniformSupport N P where
  constantDecoderRegime_of_inP := R.constantDecoderRegime_of_inP

end RealM4OfficialPToUniformConstantDecoderRegimeData

namespace RealM4OfficialPToDeciderLanguageData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}
variable {F : CompressionLowerFramework}
variable {C : CookStylePNPClassInterface.{p}}
variable {S : RealM4OfficialPToDeciderUpperSupportData D}

/-- Reassemble the legacy language-data package from the split official bridge
obligations. -/
def ofSplitOfficialData
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N)
    (R : RealM4OfficialPToConstantDecoderRegimeData D F C S N P) :
    RealM4OfficialPToDeciderLanguageData D F C S where
  separatedLanguage := N.separatedLanguage
  separatedLanguage_inNP := N.separatedLanguage_inNP
  pnpDeciderFamily_of_inP := P.pnpDeciderFamily_of_inP
  constantDecoderRegime_of_inP := R.constantDecoderRegime_of_inP

/-- Reassemble the legacy language-data package from split official bridge
obligations when the constant-decoder regime is supplied in the
support-neutral form. -/
def ofSplitOfficialUniformRegimeData
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N)
    (R : RealM4OfficialPToUniformConstantDecoderRegimeData
      D F C S.uniformSupport N P) :
    RealM4OfficialPToDeciderLanguageData D F C S :=
  ofSplitOfficialData N P
    (RealM4OfficialPToUniformConstantDecoderRegimeData.toLegacySupport S R)

/-- Project the named NP language out of the legacy package. -/
def languageNPData
    (L : RealM4OfficialPToDeciderLanguageData D F C S) :
    RealM4OfficialLanguageNPData C where
  separatedLanguage := L.separatedLanguage
  separatedLanguage_inNP := L.separatedLanguage_inNP

/-- Project the P-membership-to-SAT-decider obligation out of the legacy
package. -/
def pToDeciderFamilyData
    (L : RealM4OfficialPToDeciderLanguageData D F C S) :
    RealM4OfficialPToDeciderFamilyData D C L.languageNPData where
  pnpDeciderFamily_of_inP := L.pnpDeciderFamily_of_inP

/-- Project the P-membership-to-constant-decoder-regime obligation out of the
legacy package. -/
def pToConstantDecoderRegimeData
    (L : RealM4OfficialPToDeciderLanguageData D F C S) :
    RealM4OfficialPToConstantDecoderRegimeData D F C S
      L.languageNPData L.pToDeciderFamilyData where
  constantDecoderRegime_of_inP := L.constantDecoderRegime_of_inP

end RealM4OfficialPToDeciderLanguageData

namespace RealM4OfficialPToDeciderLockedMessageLanguageData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}
variable {F : CompressionLowerFramework}
variable {C : CookStylePNPClassInterface.{p}}
variable {S : RealM4OfficialPToDeciderLockedMessageUpperSupportData D}

def ofSplitOfficialData
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N)
    (R : RealM4OfficialPToLockedMessageConstantDecoderRegimeData
      D F C S N P) :
    RealM4OfficialPToDeciderLockedMessageLanguageData D F C S where
  separatedLanguage := N.separatedLanguage
  separatedLanguage_inNP := N.separatedLanguage_inNP
  pnpDeciderFamily_of_inP := P.pnpDeciderFamily_of_inP
  constantDecoderRegime_of_inP := R.constantDecoderRegime_of_inP

/-- Reassemble the locked-message language-data package from split official
bridge obligations when the constant-decoder regime is supplied in the
support-neutral form. -/
def ofSplitOfficialUniformRegimeData
    (N : RealM4OfficialLanguageNPData C)
    (P : RealM4OfficialPToDeciderFamilyData D C N)
    (R : RealM4OfficialPToUniformConstantDecoderRegimeData
      D F C S.uniformSupport N P) :
    RealM4OfficialPToDeciderLockedMessageLanguageData D F C S :=
  ofSplitOfficialData N P
    (RealM4OfficialPToUniformConstantDecoderRegimeData.toLockedMessageSupport
      S R)

def languageNPData
    (L : RealM4OfficialPToDeciderLockedMessageLanguageData D F C S) :
    RealM4OfficialLanguageNPData C where
  separatedLanguage := L.separatedLanguage
  separatedLanguage_inNP := L.separatedLanguage_inNP

def pToDeciderFamilyData
    (L : RealM4OfficialPToDeciderLockedMessageLanguageData D F C S) :
    RealM4OfficialPToDeciderFamilyData D C L.languageNPData where
  pnpDeciderFamily_of_inP := L.pnpDeciderFamily_of_inP

def pToConstantDecoderRegimeData
    (L : RealM4OfficialPToDeciderLockedMessageLanguageData D F C S) :
    RealM4OfficialPToLockedMessageConstantDecoderRegimeData D F C S
      L.languageNPData L.pToDeciderFamilyData where
  constantDecoderRegime_of_inP := L.constantDecoderRegime_of_inP

end RealM4OfficialPToDeciderLockedMessageLanguageData

/--
Decomposed official upper bridge.  This is the next sharper target behind
`RealM4OfficialPToUpperBridgeData`: P-membership of the named NP language must
produce the explicit SAT decider family and constant-decoder regime, while the
construction-side Appendix I support and D.7/D.8 readout data remain visible.
-/
structure RealM4OfficialPToDeciderUpperBridgeData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p}) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage
  defaultMessage : Message
  coverageData : RealM4PublicLockCoverageData D
  lockedMessageRigidity : D.core.LockedMessageRigidity
  uniformSupport : RealM4CNFUniformSupportData D
  pnpDeciderFamily_of_inP :
    C.inP separatedLanguage -> RealM4ExplicitPNPDeciderFamily D
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider (pnpDeciderFamily_of_inP hP))

/-- Decomposed official upper bridge whose construction-side support carries
explicit locked-message public-message data. -/
structure RealM4OfficialPToDeciderLockedMessageUpperBridgeData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    (D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness)
    (F : CompressionLowerFramework)
    (C : CookStylePNPClassInterface.{p}) where
  separatedLanguage : C.Language
  separatedLanguage_inNP : C.inNP separatedLanguage
  coverageData : RealM4PublicLockCoverageData D
  lockedMessageData : RealM4LockedMessageRigidityData D.core
  uniformSupport : RealM4CNFUniformSupportData D
  pnpDeciderFamily_of_inP :
    C.inP separatedLanguage -> RealM4ExplicitPNPDeciderFamily D
  constantDecoderRegime_of_inP :
    ∀ hP : C.inP separatedLanguage,
      RealM4UniformConstantDecoderRegime F
        (uniformSupport.withPNPDecider (pnpDeciderFamily_of_inP hP))

/-- Reassemble the monolithic P-to-decider bridge from separated construction
support and official-language implication data. -/
def realM4_officialPToDeciderUpperBridgeData_of_supportAndLanguage
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (S : RealM4OfficialPToDeciderUpperSupportData D)
    (L : RealM4OfficialPToDeciderLanguageData D F C S) :
    RealM4OfficialPToDeciderUpperBridgeData D F C where
  separatedLanguage := L.separatedLanguage
  separatedLanguage_inNP := L.separatedLanguage_inNP
  defaultMessage := S.defaultMessage
  coverageData := S.coverageData
  lockedMessageRigidity := S.lockedMessageRigidity
  uniformSupport := S.uniformSupport
  pnpDeciderFamily_of_inP := L.pnpDeciderFamily_of_inP
  constantDecoderRegime_of_inP := L.constantDecoderRegime_of_inP

/-- Reassemble the locked-message-data P-to-decider bridge from separated
construction support and official-language implication data. -/
def realM4_officialPToDeciderLockedMessageUpperBridgeData_of_supportAndLanguage
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (S : RealM4OfficialPToDeciderLockedMessageUpperSupportData D)
    (L : RealM4OfficialPToDeciderLockedMessageLanguageData D F C S) :
    RealM4OfficialPToDeciderLockedMessageUpperBridgeData D F C where
  separatedLanguage := L.separatedLanguage
  separatedLanguage_inNP := L.separatedLanguage_inNP
  coverageData := S.coverageData
  lockedMessageData := S.lockedMessageData
  uniformSupport := S.uniformSupport
  pnpDeciderFamily_of_inP := L.pnpDeciderFamily_of_inP
  constantDecoderRegime_of_inP := L.constantDecoderRegime_of_inP

namespace RealM4OfficialPToUpperBridgeData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}
variable {F : CompressionLowerFramework}
variable {C : CookStylePNPClassInterface.{p}}

/-- Under the official class-equality branch `P = NP`, the strict upper
bridge supplies the exact explicit-PNP self-reduction package used by the real
endgame.  This keeps the conditional branch tied to the Cook-style interface
instead of treating the SAT decider family as a free theorem input. -/
noncomputable def upperDischarge_of_pEqualsNP
    (B : RealM4OfficialPToUpperBridgeData D F C)
    (hEq : C.pEqualsNP) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  B.upperDischarge_of_inP
    (hEq B.separatedLanguage B.separatedLanguage_inNP)

end RealM4OfficialPToUpperBridgeData

namespace RealM4OfficialPToDeciderUpperBridgeData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}
variable {F : CompressionLowerFramework}
variable {C : CookStylePNPClassInterface.{p}}

/-- Assemble the strict official upper bridge from the decomposed
P-membership-to-decider data and the visible M4 construction-side support. -/
noncomputable def upperBridge
    (B : RealM4OfficialPToDeciderUpperBridgeData D F C) :
    RealM4OfficialPToUpperBridgeData D F C where
  separatedLanguage := B.separatedLanguage
  separatedLanguage_inNP := B.separatedLanguage_inNP
  upperDischarge_of_inP := by
    intro hP
    exact
      RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndRigidity
        B.defaultMessage B.coverageData B.lockedMessageRigidity
        B.uniformSupport (B.pnpDeciderFamily_of_inP hP)
        (B.constantDecoderRegime_of_inP hP)

/-- Direct official `P = NP` branch for the decomposed P-membership-to-decider
bridge.  The SAT decider family and constant decoder regime are obtained from
P-membership of the named NP language, which is obtained from `pEqualsNP`. -/
noncomputable def upperDischarge_of_pEqualsNP
    (B : RealM4OfficialPToDeciderUpperBridgeData D F C)
    (hEq : C.pEqualsNP) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  B.upperBridge.upperDischarge_of_pEqualsNP hEq

end RealM4OfficialPToDeciderUpperBridgeData

namespace RealM4OfficialPToDeciderLockedMessageUpperBridgeData

variable {PublicLock : Type g} {Quotient : Type h}
variable {LockAux : Type i} {Message : Type j}
variable {CNFPublic : Type k} {Var : CNFPublic -> Type l}
variable {Witness : CNFPublic -> Type l}
variable
  {D : AppendixICNFReadoutData
    PublicLock Quotient LockAux Message CNFPublic Var Witness}
variable {F : CompressionLowerFramework}
variable {C : CookStylePNPClassInterface.{p}}

noncomputable def upperBridge
    (B : RealM4OfficialPToDeciderLockedMessageUpperBridgeData D F C) :
    RealM4OfficialPToUpperBridgeData D F C where
  separatedLanguage := B.separatedLanguage
  separatedLanguage_inNP := B.separatedLanguage_inNP
  upperDischarge_of_inP := by
    intro hP
    exact
      RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
        B.coverageData B.lockedMessageData B.uniformSupport
        (B.pnpDeciderFamily_of_inP hP)
        (B.constantDecoderRegime_of_inP hP)

/-- Direct official `P = NP` branch for the locked-message-data
P-membership-to-decider bridge. -/
noncomputable def upperDischarge_of_pEqualsNP
    (B : RealM4OfficialPToDeciderLockedMessageUpperBridgeData D F C)
    (hEq : C.pEqualsNP) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  B.upperBridge.upperDischarge_of_pEqualsNP hEq

end RealM4OfficialPToDeciderLockedMessageUpperBridgeData

/-- Top-level alias exposing the construction of the strict upper bridge from
the decomposed P-membership-to-decider data. -/
noncomputable def realM4_officialUpperBridge_of_pMembershipDeciderData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (B : RealM4OfficialPToDeciderUpperBridgeData D F C) :
    RealM4OfficialPToUpperBridgeData D F C :=
  B.upperBridge

/-- Top-level alias exposing the strict upper bridge from the locked-message
P-membership-to-decider data. -/
noncomputable def realM4_officialUpperBridge_of_pMembershipDeciderLockedMessageData
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (B : RealM4OfficialPToDeciderLockedMessageUpperBridgeData D F C) :
    RealM4OfficialPToUpperBridgeData D F C :=
  B.upperBridge

/-- Top-level alias for extracting the explicit self-reduction upper package
from official class equality through the strict upper bridge. -/
noncomputable def realM4_upperDischarge_of_pEqualsNP_upperBridge
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (B : RealM4OfficialPToUpperBridgeData D F C)
    (hEq : C.pEqualsNP) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  B.upperDischarge_of_pEqualsNP hEq

/-- Top-level alias for extracting the explicit self-reduction upper package
from official class equality through the decomposed P-to-decider bridge. -/
noncomputable def realM4_upperDischarge_of_pEqualsNP_pMembershipDeciderBridge
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (B : RealM4OfficialPToDeciderUpperBridgeData D F C)
    (hEq : C.pEqualsNP) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  B.upperDischarge_of_pEqualsNP hEq

/-- Top-level alias for extracting the explicit self-reduction upper package
from official class equality through the locked-message P-to-decider bridge. -/
noncomputable def realM4_upperDischarge_of_pEqualsNP_pMembershipDeciderLockedMessageBridge
    {PublicLock : Type g} {Quotient : Type h}
    {LockAux : Type i} {Message : Type j}
    {CNFPublic : Type k} {Var : CNFPublic -> Type l}
    {Witness : CNFPublic -> Type l}
    {D : AppendixICNFReadoutData
      PublicLock Quotient LockAux Message CNFPublic Var Witness}
    {F : CompressionLowerFramework}
    {C : CookStylePNPClassInterface.{p}}
    (B : RealM4OfficialPToDeciderLockedMessageUpperBridgeData D F C)
    (hEq : C.pEqualsNP) :
    RealM4SelfReductionUpperExplicitPNPDischarge D F :=
  B.upperDischarge_of_pEqualsNP hEq

/--
Official endpoint from the stricter upper bridge.  The bridge contributes only
the NP language and the P-membership-to-upper-discharge implication; StarSW and
the three analytic frontiers remain visible theorem hypotheses.
-/
theorem realM4_officialSeparation_from_endgameMechanicalData_upperBridge
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
      RealM4OfficialPToUpperBridgeData D M.lowerFramework C) :
    C.officialSeparation :=
  C.officialSeparation_of_np_not_p
    bridge.separatedLanguage_inNP
    (by
      intro hP
      exact
        (realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
          M (bridge.upperDischarge_of_inP hP) starSWHardness
          safeQSSM boundedGaugeIncidence boundaryMixing).noConsistentBounds)

/--
Explicit contradiction branch from official `P = NP`.  The upper package is
derived from `pEqualsNP` through the bridge's named NP language; StarSW and
the three analytic frontiers remain the only irreducible content in the clash.
-/
theorem realM4_false_of_pEqualsNP_from_endgameMechanicalData_upperBridge
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
      RealM4OfficialPToUpperBridgeData D M.lowerFramework C)
    (hEq : C.pEqualsNP) :
    False :=
  (realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
    M (bridge.upperDischarge_of_pEqualsNP hEq) starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing).noConsistentBounds

/--
Cook-style existential endpoint from the stricter upper bridge.  This is the
same content as `realM4_officialSeparation_from_endgameMechanicalData_upperBridge`
spelled directly as `∃ L, inNP L ∧ ¬ inP L`.
-/
theorem realM4_exists_np_not_p_from_endgameMechanicalData_upperBridge
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
      RealM4OfficialPToUpperBridgeData D M.lowerFramework C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  ⟨bridge.separatedLanguage,
    bridge.separatedLanguage_inNP,
    by
      intro hP
      exact
        (realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
          M (bridge.upperDischarge_of_inP hP) starSWHardness
          safeQSSM boundedGaugeIncidence boundaryMixing).noConsistentBounds⟩

/--
Cook-style negated class equality from the stricter upper bridge.  This is
the same nondegenerate endpoint as the existential theorem above, stated as
`not (P = NP)` inside the supplied Cook-style interface.
-/
theorem realM4_not_pEqualsNP_from_endgameMechanicalData_upperBridge
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
      RealM4OfficialPToUpperBridgeData D M.lowerFramework C) :
    ¬ C.pEqualsNP :=
  C.not_pEqualsNP_of_np_not_p
    bridge.separatedLanguage_inNP
    (by
      intro hP
      exact
        (realM4_conditionalClash_from_endgameMechanicalData_explicitPNP
          M (bridge.upperDischarge_of_inP hP) starSWHardness
          safeQSSM boundedGaugeIncidence boundaryMixing).noConsistentBounds)

/--
Official endpoint from the decomposed P-membership-to-decider bridge.  This
keeps the upper-side SAT decider route visible: the theorem does not take a
free P=NP decider family, but the bridge data must show how P-membership of
the named NP language yields that family and the constant-decoder regime.
-/
theorem realM4_officialSeparation_from_endgameMechanicalData_pMembershipDeciderBridge
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
      RealM4OfficialPToDeciderUpperBridgeData D M.lowerFramework C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge

/-- Cook-style existential endpoint from the decomposed
P-membership-to-decider bridge. -/
theorem realM4_exists_np_not_p_from_endgameMechanicalData_pMembershipDeciderBridge
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
      RealM4OfficialPToDeciderUpperBridgeData D M.lowerFramework C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge

/-- Cook-style negated class equality from the decomposed
P-membership-to-decider bridge. -/
theorem realM4_not_pEqualsNP_from_endgameMechanicalData_pMembershipDeciderBridge
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
      RealM4OfficialPToDeciderUpperBridgeData D M.lowerFramework C) :
    ¬ C.pEqualsNP :=
  realM4_not_pEqualsNP_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge

/-- Explicit `P = NP` contradiction branch from the decomposed
P-membership-to-decider bridge. -/
theorem realM4_false_of_pEqualsNP_from_endgameMechanicalData_pMembershipDeciderBridge
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
      RealM4OfficialPToDeciderUpperBridgeData D M.lowerFramework C)
    (hEq : C.pEqualsNP) :
    False :=
  realM4_false_of_pEqualsNP_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge hEq

/--
Official endpoint from the locked-message-data decomposed
P-membership-to-decider bridge.  This is the same Cook-style route as the
ordinary P-to-decider bridge, but the upper support package carries the
public-message invariant as explicit locked-message data.
-/
theorem realM4_officialSeparation_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D M.lowerFramework C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge

/-- Cook-style existential endpoint from the locked-message-data
P-membership-to-decider bridge. -/
theorem realM4_exists_np_not_p_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D M.lowerFramework C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge

/-- Cook-style negated class equality from the locked-message-data
P-membership-to-decider bridge. -/
theorem realM4_not_pEqualsNP_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D M.lowerFramework C) :
    ¬ C.pEqualsNP :=
  realM4_not_pEqualsNP_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge

/-- Explicit `P = NP` contradiction branch from the locked-message-data
P-membership-to-decider bridge. -/
theorem realM4_false_of_pEqualsNP_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D M.lowerFramework C)
    (hEq : C.pEqualsNP) :
    False :=
  realM4_false_of_pEqualsNP_from_endgameMechanicalData_upperBridge
    M starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing
    bridge.upperBridge hEq

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
No-target-rows real-frontier staging with the CNF variable cover extracted
from each formula's finite syntax.  Compared with the finite-variable route,
this removes the unnecessary obligation to make the whole ambient CNF variable
family finite; the upper-side construction only needs decidable equality for
the variable syntax, plus the explicit P=NP decider family and constant
decoder regime.
-/
theorem realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
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
    (varDecidable : (Y : CNFPublic) -> DecidableEq (Var Y))
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_uniformCNFSupport_of_formulaSyntax
          D varDecidable).withPNPDecider pnpDeciderFamily))
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
          (realM4_uniformCNFSupport_of_formulaSyntax D varDecidable)
          pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct)
    lowerMachine defaultMessage coverageData lockedMessageRigidity
    varDecidable pnpDeciderFamily constantDecoderRegime starSWHardness
    safeQSSM boundedGaugeIncidence boundaryMixing

/--
No-target-rows real-frontier staging from real CNF variable address syntax.
This is the sharp internal `UpperLowerClash` route for the current checked
public surface: address syntax supplies the local syntax roundtrip, Nat coding,
and formula support used by the explicit-P=NP upper side.  It does not
construct the real address syntax, the real lower machine, D.8 rigidity, or
the analytic frontier fields.
-/
theorem realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_addressSyntax_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_formulaSyntaxCNFSupport_of_addressSyntax
          variableAddressSyntax).withPNPDecider pnpDeciderFamily))
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
          (realM4_formulaSyntaxCNFSupport_of_addressSyntax
            variableAddressSyntax)
          pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_addressSyntax_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct)
    lowerMachine defaultMessage coverageData lockedMessageRigidity
    variableAddressSyntax pnpDeciderFamily constantDecoderRegime
    starSWHardness safeQSSM boundedGaugeIncidence boundaryMixing

/--
No-target-rows real-frontier staging from address syntax and explicit
locked-message data.  Compared with the raw-rigidity route, the theorem
boundary carries the public-message invariant package used by the upper
readout adapter directly.
-/
theorem realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_addressSyntax_coverageDataAndLockedMessageData_canonicalGap_realFrontier_explicitPNP
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_formulaSyntaxCNFSupport_of_addressSyntax
          variableAddressSyntax).withPNPDecider pnpDeciderFamily))
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
        (RealM4SelfReductionUpperExplicitPNPDischarge.ofCoverageDataAndLockedMessageData
          (D := D) (F := lowerMachine.lowerFramework)
          coverageData lockedMessageData
          (realM4_formulaSyntaxCNFSupport_of_addressSyntax
            variableAddressSyntax)
          pnpDeciderFamily constantDecoderRegime)
        starSWHardness safeQSSM.safeQSSM
        boundedGaugeIncidence.boundedGaugeIncidence
        boundaryMixing.boundaryMixing) :=
  realM4_conditionalClash_from_lowerMachine_addressSyntax_coverageDataAndLockedMessageData_canonicalGap_realFrontier_explicitPNP
    (RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct)
    lowerMachine coverageData lockedMessageData variableAddressSyntax
    pnpDeciderFamily constantDecoderRegime starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing

/--
Cook-style official endpoint for the no-target-rows canonical-gap real-frontier
route through the decomposed P-membership-to-decider upper bridge.  Unlike the
older explicit-PNP endpoint, this theorem does not take a free SAT decider
family or raw clash-to-not-P bridge as hypotheses; those must be produced by
the named official bridge from P-membership of the separated NP language.

This is still conditional real-spine staging, not a proof of P != NP and not a
claim that the full manuscript M4 ensemble has already been identified.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderBridge
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
      RealM4OfficialPToDeciderUpperBridgeData D lowerMachine.lowerFramework C) :
    C.officialSeparation := by
  let interfaceData :=
    RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct
  let M :=
    RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      interfaceData boundaryMixing.epsSmall lowerMachine
  have hStar : CompressionStarSWHardness M.lowerFramework := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using starSWHardness
  have hSafe :
      ∀ q : Safe, 0 ≤ M.interfaceData.safeCost q ∧
        M.interfaceData.safeCost q ≤ M.interfaceData.safeBudget := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      safeQSSM.safeQSSM
  have hBounded :
      ∀ gamma : Gauge,
        M.interfaceData.gaugeIncidence gamma ≤ M.interfaceData.gaugeBound := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundedGaugeIncidence.boundedGaugeIncidence
  have hBoundary :
      BoundaryMixingBound M.interfaceData.target M.interfaceData.pivotSummary
        M.interfaceData.epsMix := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundaryMixing.boundaryMixing
  have hBridge :
      RealM4OfficialPToDeciderUpperBridgeData D M.lowerFramework C := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using bridge
  exact
    realM4_officialSeparation_from_endgameMechanicalData_pMembershipDeciderBridge
      M hStar hSafe hBounded hBoundary hBridge

/--
Existential Cook-style endpoint for the same no-target-rows canonical-gap
real-frontier route through the decomposed P-membership-to-decider bridge.
The result exposes `∃ L, inNP L ∧ ¬ inP L` while keeping the bridge, StarSW,
and the three analytic frontiers visible.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderBridge
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
      RealM4OfficialPToDeciderUpperBridgeData D lowerMachine.lowerFramework C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage := by
  let interfaceData :=
    RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct
  let M :=
    RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      interfaceData boundaryMixing.epsSmall lowerMachine
  have hStar : CompressionStarSWHardness M.lowerFramework := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using starSWHardness
  have hSafe :
      ∀ q : Safe, 0 ≤ M.interfaceData.safeCost q ∧
        M.interfaceData.safeCost q ≤ M.interfaceData.safeBudget := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      safeQSSM.safeQSSM
  have hBounded :
      ∀ gamma : Gauge,
        M.interfaceData.gaugeIncidence gamma ≤ M.interfaceData.gaugeBound := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundedGaugeIncidence.boundedGaugeIncidence
  have hBoundary :
      BoundaryMixingBound M.interfaceData.target M.interfaceData.pivotSummary
        M.interfaceData.epsMix := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundaryMixing.boundaryMixing
  have hBridge :
      RealM4OfficialPToDeciderUpperBridgeData D M.lowerFramework C := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using bridge
  exact
    realM4_exists_np_not_p_from_endgameMechanicalData_pMembershipDeciderBridge
      M hStar hSafe hBounded hBoundary hBridge

/--
No-target-rows official endpoint from separated support and language bridge
data.  This is the same route as
`realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderBridge`,
but the construction-side M4 support data and the official-language
P-membership implication are separate hypotheses.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderSupportAndLanguage
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
    (supportData : RealM4OfficialPToDeciderUpperSupportData D)
    (languageData :
      RealM4OfficialPToDeciderLanguageData
        D lowerMachine.lowerFramework C supportData) :
    C.officialSeparation :=
  realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderBridge
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (realM4_officialPToDeciderUpperBridgeData_of_supportAndLanguage
      supportData languageData)

/--
Existential no-target-rows endpoint from separated construction support and
official-language implication data.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderSupportAndLanguage
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
    (supportData : RealM4OfficialPToDeciderUpperSupportData D)
    (languageData :
      RealM4OfficialPToDeciderLanguageData
        D lowerMachine.lowerFramework C supportData) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderBridge
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (realM4_officialPToDeciderUpperBridgeData_of_supportAndLanguage
      supportData languageData)

/--
No-target-rows official endpoint from locally encodable real CNF variable
syntax.  This is only a supplier wrapper around the decomposed
P-membership-to-decider route: syntax encodability constructs the
construction-side upper support, while the official-language implication data,
StarSW hardness, and the three analytic frontier fields remain theorem
hypotheses.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderEncodableSyntax
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
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableSyntax : RealM4CNFVariableEncodableSyntaxData D)
    (languageData :
      RealM4OfficialPToDeciderLanguageData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndEncodableSyntax
            defaultMessage coverageData lockedMessageRigidity
            variableSyntax)) :
    C.officialSeparation :=
  realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderSupportAndLanguage
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndEncodableSyntax
      defaultMessage coverageData lockedMessageRigidity variableSyntax)
    languageData

/--
Existential no-target-rows official endpoint from locally encodable real CNF
variable syntax and official-language P-membership-to-decider data.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderEncodableSyntax
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
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableSyntax : RealM4CNFVariableEncodableSyntaxData D)
    (languageData :
      RealM4OfficialPToDeciderLanguageData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndEncodableSyntax
            defaultMessage coverageData lockedMessageRigidity
            variableSyntax)) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderSupportAndLanguage
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndEncodableSyntax
      defaultMessage coverageData lockedMessageRigidity variableSyntax)
    languageData

/--
No-target-rows official endpoint from real CNF variable address syntax.  This
is the sharper supplier wrapper around the decomposed P-membership-to-decider
route: address syntax constructs the local encodable syntax, Nat coding, and
formula support used by the construction-side upper bridge.  The official
language data, StarSW hardness, and the three analytic frontier fields remain
visible hypotheses.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntax
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageData :
      RealM4OfficialPToDeciderLanguageData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax
            defaultMessage coverageData lockedMessageRigidity
            variableAddressSyntax)) :
    C.officialSeparation :=
  realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderSupportAndLanguage
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax
      defaultMessage coverageData lockedMessageRigidity variableAddressSyntax)
    languageData

/--
Existential no-target-rows official endpoint from real CNF variable address
syntax and official-language P-membership-to-decider data.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntax
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageData :
      RealM4OfficialPToDeciderLanguageData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax
            defaultMessage coverageData lockedMessageRigidity
            variableAddressSyntax)) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderSupportAndLanguage
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax
      defaultMessage coverageData lockedMessageRigidity variableAddressSyntax)
    languageData

/--
No-target-rows official endpoint from real CNF variable address syntax and
split official bridge obligations.  The wrapper reassembles the legacy
official-language package internally, so the sharp address-syntax route exposes
the named NP language, P-to-SAT-decider implication, and P-to-constant-decoder
regime as separate theorem hypotheses.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntaxSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToConstantDecoderRegimeData :
      RealM4OfficialPToConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax
            defaultMessage coverageData lockedMessageRigidity
            variableAddressSyntax)
          languageNPData pToDeciderFamilyData) :
    C.officialSeparation :=
  realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntax
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing defaultMessage coverageData
    lockedMessageRigidity variableAddressSyntax
    (RealM4OfficialPToDeciderLanguageData.ofSplitOfficialData
      languageNPData pToDeciderFamilyData pToConstantDecoderRegimeData)

/--
Existential no-target-rows official endpoint from real CNF variable address
syntax and split official bridge obligations.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntaxSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (defaultMessage : Message)
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageRigidity : D.core.LockedMessageRigidity)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToConstantDecoderRegimeData :
      RealM4OfficialPToConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax
            defaultMessage coverageData lockedMessageRigidity
            variableAddressSyntax)
          languageNPData pToDeciderFamilyData) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntax
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing defaultMessage coverageData
    lockedMessageRigidity variableAddressSyntax
    (RealM4OfficialPToDeciderLanguageData.ofSplitOfficialData
      languageNPData pToDeciderFamilyData pToConstantDecoderRegimeData)

/--
No-target-rows official endpoint through the locked-message-data
P-membership-to-decider bridge.  This is the real-spine variant of the
decomposed official route whose upper-side support carries explicit
locked-message public-message data rather than a default message plus a raw
D.8 rigidity proposition.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D lowerMachine.lowerFramework C) :
    C.officialSeparation := by
  let interfaceData :=
    RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct
  let M :=
    RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      interfaceData boundaryMixing.epsSmall lowerMachine
  have hStar : CompressionStarSWHardness M.lowerFramework := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using starSWHardness
  have hSafe :
      ∀ q : Safe, 0 ≤ M.interfaceData.safeCost q ∧
        M.interfaceData.safeCost q ≤ M.interfaceData.safeBudget := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      safeQSSM.safeQSSM
  have hBounded :
      ∀ gamma : Gauge,
        M.interfaceData.gaugeIncidence gamma ≤ M.interfaceData.gaugeBound := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundedGaugeIncidence.boundedGaugeIncidence
  have hBoundary :
      BoundaryMixingBound M.interfaceData.target M.interfaceData.pivotSummary
        M.interfaceData.epsMix := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundaryMixing.boundaryMixing
  have hBridge :
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D M.lowerFramework C := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using bridge
  exact
    realM4_officialSeparation_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge
      M hStar hSafe hBounded hBoundary hBridge

/--
Existential Cook-style endpoint for the no-target-rows canonical-gap route
through the locked-message-data P-membership-to-decider bridge.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D lowerMachine.lowerFramework C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage := by
  let interfaceData :=
    RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents
      (HistoryAtom := HistoryAtom) (Observer := Observer) (Output := Output)
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct
  let M :=
    RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap
      interfaceData boundaryMixing.epsSmall lowerMachine
  have hStar : CompressionStarSWHardness M.lowerFramework := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using starSWHardness
  have hSafe :
      ∀ q : Safe, 0 ≤ M.interfaceData.safeCost q ∧
        M.interfaceData.safeCost q ≤ M.interfaceData.safeBudget := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      safeQSSM.safeQSSM
  have hBounded :
      ∀ gamma : Gauge,
        M.interfaceData.gaugeIncidence gamma ≤ M.interfaceData.gaugeBound := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundedGaugeIncidence.boundedGaugeIncidence
  have hBoundary :
      BoundaryMixingBound M.interfaceData.target M.interfaceData.pivotSummary
        M.interfaceData.epsMix := by
    simpa [M, interfaceData,
      RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents,
      RealM4MechanicalInterfaceData.ofNoTargetRowsPublicCoordinateCDENFComponents,
      RealM4MechanicalInterfaceData.ofCDENFComponents] using
      boundaryMixing.boundaryMixing
  have hBridge :
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D M.lowerFramework C := by
    simpa [M, RealM4EndgameMechanicalData.ofComponentsWithLowerMachineCanonicalGap,
      RealM4EndgameMechanicalData.ofComponentsWithCanonicalGap,
      RealM4EndgameMechanicalData.ofComponents] using bridge
  exact
    realM4_exists_np_not_p_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge
      M hStar hSafe hBounded hBoundary hBridge

/--
Cook-style class inequality for the no-target-rows canonical-gap route through
the locked-message-data P-membership-to-decider bridge.  This packages the
official upper-side implications in the bridge object; it does not construct
that bridge or discharge the real constant-decoder-regime obligation.
-/
theorem realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D lowerMachine.lowerFramework C) :
    ¬ C.pEqualsNP :=
  C.not_pEqualsNP_of_officialSeparation
    (realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
      boundedGaugeIncidence boundaryMixing bridge)

/-- Explicit contradiction branch for the same locked-message bridge route. -/
theorem realM4_false_of_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
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
      RealM4OfficialPToDeciderLockedMessageUpperBridgeData
        D lowerMachine.lowerFramework C)
    (hEq : C.pEqualsNP) :
    False :=
  (realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing bridge) hEq

/--
No-target-rows official endpoint from real CNF address syntax, explicit
locked-message data, and split official bridge obligations.  This removes the
default-message/raw-rigidity adapter from the sharp address-syntax official
route while keeping StarSW and the three analytic fields as the only content
inputs after construction data.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToConstantDecoderRegimeData :
      RealM4OfficialPToLockedMessageConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
            coverageData lockedMessageData variableAddressSyntax)
          languageNPData pToDeciderFamilyData) :
    C.officialSeparation :=
  realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (realM4_officialPToDeciderLockedMessageUpperBridgeData_of_supportAndLanguage
      (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
        coverageData lockedMessageData variableAddressSyntax)
      (RealM4OfficialPToDeciderLockedMessageLanguageData.ofSplitOfficialData
        languageNPData pToDeciderFamilyData pToConstantDecoderRegimeData))

/--
Existential no-target-rows official endpoint from real CNF address syntax,
explicit locked-message data, and split official bridge obligations.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToConstantDecoderRegimeData :
      RealM4OfficialPToLockedMessageConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
            coverageData lockedMessageData variableAddressSyntax)
          languageNPData pToDeciderFamilyData) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing
    (realM4_officialPToDeciderLockedMessageUpperBridgeData_of_supportAndLanguage
      (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
        coverageData lockedMessageData variableAddressSyntax)
      (RealM4OfficialPToDeciderLockedMessageLanguageData.ofSplitOfficialData
        languageNPData pToDeciderFamilyData pToConstantDecoderRegimeData))

/--
No-target-rows official endpoint from real CNF address syntax, explicit
locked-message data, and split official obligations whose constant-decoder
part is support-neutral.  The wrapper reindexes that obligation to the
locked-message support package internally.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToUniformConstantDecoderRegimeData :
      RealM4OfficialPToUniformConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
            coverageData lockedMessageData variableAddressSyntax).uniformSupport
          languageNPData pToDeciderFamilyData) :
    C.officialSeparation :=
  realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxSplit
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing coverageData lockedMessageData
    variableAddressSyntax languageNPData pToDeciderFamilyData
    (RealM4OfficialPToUniformConstantDecoderRegimeData.toLockedMessageSupport
      (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
        coverageData lockedMessageData variableAddressSyntax)
      pToUniformConstantDecoderRegimeData)

/--
Existential no-target-rows endpoint from real CNF address syntax, explicit
locked-message data, and split official obligations whose constant-decoder
part is support-neutral.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToUniformConstantDecoderRegimeData :
      RealM4OfficialPToUniformConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
            coverageData lockedMessageData variableAddressSyntax).uniformSupport
          languageNPData pToDeciderFamilyData) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxSplit
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing coverageData lockedMessageData
    variableAddressSyntax languageNPData pToDeciderFamilyData
    (RealM4OfficialPToUniformConstantDecoderRegimeData.toLockedMessageSupport
      (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
        coverageData lockedMessageData variableAddressSyntax)
      pToUniformConstantDecoderRegimeData)

/--
Cook-style class-inequality endpoint for the sharpest current no-target-rows
real-frontier staging route.  The theorem surface is the support-neutral split
official bridge route: construction data remains visible, and the only
mathematical content inputs are StarSW and the three analytic frontiers.

This is conditional staging for the current real public-surface spine, not a
proof of P != NP and not yet a full manuscript M4 identification.
-/
theorem realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToUniformConstantDecoderRegimeData :
      RealM4OfficialPToUniformConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
            coverageData lockedMessageData variableAddressSyntax).uniformSupport
          languageNPData pToDeciderFamilyData) :
    ¬ C.pEqualsNP := by
  exact
    C.not_pEqualsNP_of_officialSeparation
      (realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
      boundedGaugeIncidence boundaryMixing coverageData lockedMessageData
      variableAddressSyntax languageNPData pToDeciderFamilyData
      pToUniformConstantDecoderRegimeData)

/-- Explicit contradiction form of the same sharp no-target-rows
support-neutral official route. -/
theorem realM4_false_of_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (pToUniformConstantDecoderRegimeData :
      RealM4OfficialPToUniformConstantDecoderRegimeData
        D lowerMachine.lowerFramework C
          (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
            coverageData lockedMessageData variableAddressSyntax).uniformSupport
          languageNPData pToDeciderFamilyData)
    (hEq : C.pEqualsNP) :
    False :=
  (realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing coverageData lockedMessageData
    variableAddressSyntax languageNPData pToDeciderFamilyData
    pToUniformConstantDecoderRegimeData) hEq

/--
Cook-style class-inequality endpoint for the sharp no-target-rows route with
the support-neutral constant-decoder regime constructed from explicit
P-membership-indexed K-poly compatibility facts.

This theorem removes the bundled constant-decoder-regime object from the
endpoint surface on this path.  It does not prove the real K-poly
identifications or floor inequality from P-membership; those remain visible
obligations, alongside the named NP language and the P-to-decider family.
-/
theorem realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (eta_of_inP : C.inP languageNPData.separatedLanguage -> Nat)
    (kpolyAt_eq_of_inP :
      ∀ hP : C.inP languageNPData.separatedLanguage,
        lowerMachine.lowerFramework.kpolyAt =
          realM4UniformConstantDecoderKpolyAt
            ((RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
              coverageData lockedMessageData variableAddressSyntax).uniformSupport.withPNPDecider
                (pToDeciderFamilyData.pnpDeciderFamily_of_inP hP)))
    (etaTimes_eq_of_inP :
      ∀ hP : C.inP languageNPData.separatedLanguage,
        lowerMachine.lowerFramework.etaTimes =
          realCNFLinearEtaTimes (eta_of_inP hP))
    (floor_dominates_decoder_of_inP :
      ∀ hP : C.inP languageNPData.separatedLanguage,
        realM4UniformSelfReductionDecoderCost
            ((RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
              coverageData lockedMessageData variableAddressSyntax).uniformSupport.withPNPDecider
                (pToDeciderFamilyData.pnpDeciderFamily_of_inP hP)) <
          (eta_of_inP hP) * lowerMachine.lowerFramework.targetBlocks) :
    ¬ C.pEqualsNP :=
  realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing coverageData lockedMessageData
    variableAddressSyntax languageNPData pToDeciderFamilyData
    (RealM4OfficialPToUniformConstantDecoderRegimeData.ofKpolyCompatibility
      (D := D) (F := lowerMachine.lowerFramework) (C := C)
      (uniformSupport :=
        (RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
          coverageData lockedMessageData variableAddressSyntax).uniformSupport)
      (N := languageNPData) (P := pToDeciderFamilyData)
      eta_of_inP kpolyAt_eq_of_inP etaTimes_eq_of_inP
      floor_dominates_decoder_of_inP)

/-- Explicit contradiction form of the K-poly-compatibility split route. -/
theorem realM4_false_of_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplit
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
    {CNFPublic : Type k} {Address : CNFPublic -> Type q}
    {Var : CNFPublic -> Type l}
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
    (coverageData : RealM4PublicLockCoverageData D)
    (lockedMessageData : RealM4LockedMessageRigidityData D.core)
    (variableAddressSyntax :
      RealM4CNFVariableAddressSyntaxData (Address := Address) D)
    (languageNPData : RealM4OfficialLanguageNPData C)
    (pToDeciderFamilyData :
      RealM4OfficialPToDeciderFamilyData D C languageNPData)
    (eta_of_inP : C.inP languageNPData.separatedLanguage -> Nat)
    (kpolyAt_eq_of_inP :
      ∀ hP : C.inP languageNPData.separatedLanguage,
        lowerMachine.lowerFramework.kpolyAt =
          realM4UniformConstantDecoderKpolyAt
            ((RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
              coverageData lockedMessageData variableAddressSyntax).uniformSupport.withPNPDecider
                (pToDeciderFamilyData.pnpDeciderFamily_of_inP hP)))
    (etaTimes_eq_of_inP :
      ∀ hP : C.inP languageNPData.separatedLanguage,
        lowerMachine.lowerFramework.etaTimes =
          realCNFLinearEtaTimes (eta_of_inP hP))
    (floor_dominates_decoder_of_inP :
      ∀ hP : C.inP languageNPData.separatedLanguage,
        realM4UniformSelfReductionDecoderCost
            ((RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax
              coverageData lockedMessageData variableAddressSyntax).uniformSupport.withPNPDecider
                (pToDeciderFamilyData.pnpDeciderFamily_of_inP hP)) <
          (eta_of_inP hP) * lowerMachine.lowerFramework.targetBlocks)
    (hEq : C.pEqualsNP) :
    False :=
  (realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplit
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine starSWHardness safeQSSM
    boundedGaugeIncidence boundaryMixing coverageData lockedMessageData
    variableAddressSyntax languageNPData pToDeciderFamilyData eta_of_inP
    kpolyAt_eq_of_inP etaTimes_eq_of_inP
    floor_dominates_decoder_of_inP) hEq

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
Cook-style official endpoint wrapper for the no-target-rows canonical-gap
real-frontier route with CNF support extracted from formula syntax.  This is
the sharp official staging path: it avoids reintroducing finite-variable-family
data after the formula-syntax support construction, while keeping the Cook
bridge as a separate visible construction obligation.
-/
theorem realM4_officialSeparation_from_noTargetRowsCDENF_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
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
    (varDecidable : (Y : CNFPublic) -> DecidableEq (Var Y))
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_uniformCNFSupport_of_formulaSyntax
          D varDecidable).withPNPDecider pnpDeciderFamily))
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
            (realM4_uniformCNFSupport_of_formulaSyntax D varDecidable)
            pnpDeciderFamily constantDecoderRegime)
          starSWHardness safeQSSM.safeQSSM
          boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        C) :
    C.officialSeparation :=
  realM4_officialSeparation_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct lowerMachine defaultMessage coverageData
      lockedMessageRigidity varDecidable pnpDeciderFamily
      constantDecoderRegime starSWHardness safeQSSM boundedGaugeIncidence
      boundaryMixing)

/--
Explicit Cook-style existential endpoint for the formula-syntax no-target-rows,
canonical-gap, real-frontier route.  The endpoint is the existence of an NP
language outside P inside the supplied Cook-style interface, conditional on
the visible bridge and construction data plus StarSW, the three analytic
frontiers, and the explicit P=NP decider family.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
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
    (varDecidable : (Y : CNFPublic) -> DecidableEq (Var Y))
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_uniformCNFSupport_of_formulaSyntax
          D varDecidable).withPNPDecider pnpDeciderFamily))
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
            (realM4_uniformCNFSupport_of_formulaSyntax D varDecidable)
            pnpDeciderFamily constantDecoderRegime)
          starSWHardness safeQSSM.safeQSSM
          boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_internalClash_bridge bridge
    (realM4_conditionalClash_from_noTargetRowsCDENF_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
      i₀ coordinate law transcript observerBit phaseA semantics
      observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
      gaugeBound hiddenGaugeProduct lowerMachine defaultMessage coverageData
      lockedMessageRigidity varDecidable pnpDeciderFamily
      constantDecoderRegime starSWHardness safeQSSM boundedGaugeIncidence
      boundaryMixing)

/--
Explicit Cook-style existential endpoint for the formula-syntax no-target-rows
route when the real CNF variable syntax is supplied by an injective natural
code.  The code mechanically provides decidable equality; the finite variable
cover still comes from the formula syntax.  The result remains conditional on
the visible bridge and construction data plus StarSW, the three analytic
frontiers, and the explicit P=NP decider family.
-/
theorem realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_natCodedFormulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
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
    (variableCoding : RealM4CNFVariableNatCodingData D)
    (pnpDeciderFamily : RealM4ExplicitPNPDeciderFamily D)
    (constantDecoderRegime :
      RealM4UniformConstantDecoderRegime lowerMachine.lowerFramework
        ((realM4_uniformCNFSupport_of_variableNatCoding
          variableCoding).withPNPDecider pnpDeciderFamily))
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
            (realM4_uniformCNFSupport_of_variableNatCoding variableCoding)
            pnpDeciderFamily constantDecoderRegime)
          starSWHardness safeQSSM.safeQSSM
          boundedGaugeIncidence.boundedGaugeIncidence
          boundaryMixing.boundaryMixing)
        C) :
    ∃ separatedLanguage : C.Language,
      C.inNP separatedLanguage ∧ ¬ C.inP separatedLanguage :=
  realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_formulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP
    i₀ coordinate law transcript observerBit phaseA semantics
    observerEvidence pivotSummary epsMix safeCost safeBudget gaugeIncidence
    gaugeBound hiddenGaugeProduct lowerMachine defaultMessage coverageData
    lockedMessageRigidity (realM4_varDecidable_of_variableNatCoding
      variableCoding) pnpDeciderFamily constantDecoderRegime starSWHardness
    safeQSSM boundedGaugeIncidence boundaryMixing bridge

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
  "The real v15/M4 UpperLowerClash is only an internal endpoint.  A separate Cook-style P-vs-NP bridge must instantiate the official class interface, name the separated NP language, and prove that membership in P would generate the internal upper/lower clash without hiding ensemble existence, lower hardness, or analytic assumptions in parameters.  A proof that only uses the False field inside UpperLowerClash is degenerate and does not constitute the real Cook-style bridge."

def realM4OfficialUpperBridgeConstructionInputs : List String := [
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP",
  "pMembershipToSelfReductionUpperDischarge"
]

theorem realM4OfficialUpperBridgeConstructionInputs_exact :
    realM4OfficialUpperBridgeConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "pMembershipToSelfReductionUpperDischarge" ] := by
  rfl

def realM4OfficialUpperBridgeStatement : String :=
  "For the real v15/M4 Cook-style bridge, the nondegenerate endpoint obligation is to name an NP language and prove that P-membership for that language constructs the explicit self-reduction upper discharge used by the real endgame.  StarSW hardness, the lower machine, and the three analytic fields remain outside this bridge and visible at the theorem boundary."

def realM4OfficialPToDeciderUpperSupportConstructionInputs :
    List String := [
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "uniformCNFSupportData"
]

theorem realM4OfficialPToDeciderUpperSupportConstructionInputs_exact :
    realM4OfficialPToDeciderUpperSupportConstructionInputs =
      [ "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "uniformCNFSupportData" ] := by
  rfl

def realM4OfficialPToDeciderUpperSupportFromEncodableSyntaxConstructionInputs :
    List String := [
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "cnfVariableEncodableSyntax"
]

theorem realM4OfficialPToDeciderUpperSupportFromEncodableSyntaxConstructionInputs_exact :
    realM4OfficialPToDeciderUpperSupportFromEncodableSyntaxConstructionInputs =
      [ "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "cnfVariableEncodableSyntax" ] := by
  rfl

def realM4OfficialPToDeciderUpperSupportFromAddressSyntaxConstructionInputs :
    List String := [
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "cnfVariableAddressSyntax"
]

theorem realM4OfficialPToDeciderUpperSupportFromAddressSyntaxConstructionInputs_exact :
    realM4OfficialPToDeciderUpperSupportFromAddressSyntaxConstructionInputs =
      [ "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "cnfVariableAddressSyntax" ] := by
  rfl

def realM4OfficialPToDeciderLockedMessageUpperSupportConstructionInputs :
    List String := [
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "uniformCNFSupportData"
]

theorem realM4OfficialPToDeciderLockedMessageUpperSupportConstructionInputs_exact :
    realM4OfficialPToDeciderLockedMessageUpperSupportConstructionInputs =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData" ] := by
  rfl

def realM4OfficialPToDeciderLockedMessageUpperSupportFromAddressSyntaxConstructionInputs :
    List String := [
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "cnfVariableAddressSyntax"
]

theorem realM4OfficialPToDeciderLockedMessageUpperSupportFromAddressSyntaxConstructionInputs_exact :
    realM4OfficialPToDeciderLockedMessageUpperSupportFromAddressSyntaxConstructionInputs =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax" ] := by
  rfl

def realM4OfficialLanguageNPConstructionInputs : List String := [
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP"
]

theorem realM4OfficialLanguageNPConstructionInputs_exact :
    realM4OfficialLanguageNPConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP" ] := by
  rfl

def realM4OfficialPToDeciderFamilyConstructionInputs : List String := [
  "officialLanguageNPData",
  "pMembershipToPNPDeciderFamily"
]

theorem realM4OfficialPToDeciderFamilyConstructionInputs_exact :
    realM4OfficialPToDeciderFamilyConstructionInputs =
      [ "officialLanguageNPData",
        "pMembershipToPNPDeciderFamily" ] := by
  rfl

def realM4OfficialPToUniformConstantDecoderRegimeConstructionInputs :
    List String := [
  "officialLanguageNPData",
  "officialPToDeciderFamilyData",
  "uniformCNFSupportData",
  "pMembershipConstantDecoderRegime"
]

theorem realM4OfficialPToUniformConstantDecoderRegimeConstructionInputs_exact :
    realM4OfficialPToUniformConstantDecoderRegimeConstructionInputs =
      [ "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "uniformCNFSupportData",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToUniformConstantDecoderRegimeKpolyCompatibilityConstructionInputs :
    List String := [
  "officialLanguageNPData",
  "officialPToDeciderFamilyData",
  "uniformCNFSupportData",
  "pMembershipKpolyAtConstantDecoderIdentification",
  "pMembershipEtaTimesLinearFloorIdentification",
  "pMembershipConstantDecoderBelowLinearFloor"
]

theorem realM4OfficialPToUniformConstantDecoderRegimeKpolyCompatibilityConstructionInputs_exact :
    realM4OfficialPToUniformConstantDecoderRegimeKpolyCompatibilityConstructionInputs =
      [ "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "uniformCNFSupportData",
        "pMembershipKpolyAtConstantDecoderIdentification",
        "pMembershipEtaTimesLinearFloorIdentification",
        "pMembershipConstantDecoderBelowLinearFloor" ] := by
  rfl

def realM4OfficialPToUniformConstantDecoderRegimeKpolyCompatibilityStatement : String :=
  "The support-neutral official P-to-constant-decoder-regime obligation is constructed from explicit P-membership-indexed K-poly compatibility facts: the P-derived SAT decider family must identify the real lower framework's kpolyAt with the fixed constant decoder program, identify etaTimes with the linear floor, and prove the fixed decoder cost lies below that floor.  This decomposes the bridge obligation; it does not prove those compatibility facts from P-membership."

def realM4OfficialPToConstantDecoderRegimeConstructionInputs :
    List String := [
  "officialLanguageNPData",
  "officialPToDeciderFamilyData",
  "pMembershipConstantDecoderRegime"
]

theorem realM4OfficialPToConstantDecoderRegimeConstructionInputs_exact :
    realM4OfficialPToConstantDecoderRegimeConstructionInputs =
      [ "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToLockedMessageConstantDecoderRegimeConstructionInputs :
    List String := [
  "officialLanguageNPData",
  "officialPToDeciderFamilyData",
  "pMembershipConstantDecoderRegime"
]

theorem realM4OfficialPToLockedMessageConstantDecoderRegimeConstructionInputs_exact :
    realM4OfficialPToLockedMessageConstantDecoderRegimeConstructionInputs =
      [ "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderLanguageSplitConstructionInputs :
    List String :=
  realM4OfficialLanguageNPConstructionInputs ++
    realM4OfficialPToDeciderFamilyConstructionInputs ++
      realM4OfficialPToConstantDecoderRegimeConstructionInputs

theorem realM4OfficialPToDeciderLanguageSplitConstructionInputs_exact :
    realM4OfficialPToDeciderLanguageSplitConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "officialLanguageNPData",
        "pMembershipToPNPDeciderFamily",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderLockedMessageLanguageSplitConstructionInputs :
    List String :=
  realM4OfficialLanguageNPConstructionInputs ++
    realM4OfficialPToDeciderFamilyConstructionInputs ++
      realM4OfficialPToLockedMessageConstantDecoderRegimeConstructionInputs

theorem realM4OfficialPToDeciderLockedMessageLanguageSplitConstructionInputs_exact :
    realM4OfficialPToDeciderLockedMessageLanguageSplitConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "officialLanguageNPData",
        "pMembershipToPNPDeciderFamily",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderLanguageConstructionInputs : List String := [
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP",
  "pMembershipToPNPDeciderFamily",
  "pMembershipConstantDecoderRegime"
]

theorem realM4OfficialPToDeciderLanguageConstructionInputs_exact :
    realM4OfficialPToDeciderLanguageConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "pMembershipToPNPDeciderFamily",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderUpperBridgeDecomposedInputs :
    List String :=
  realM4OfficialPToDeciderUpperSupportConstructionInputs ++
    realM4OfficialPToDeciderLanguageConstructionInputs

theorem realM4OfficialPToDeciderUpperBridgeDecomposedInputs_exact :
    realM4OfficialPToDeciderUpperBridgeDecomposedInputs =
      [ "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "pMembershipToPNPDeciderFamily",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderUpperBridgeDecompositionStatement : String :=
  "The real v15/M4 official P-to-decider upper bridge decomposes into construction-side support data and official-language implication data.  The support data contains the default message, public-lock coverage, D.8 locked-message rigidity, and uniform CNF support.  The official-language side further splits into the named NP language, the P-membership-to-SAT-decider implication, and the P-membership-to-constant-decoder-regime implication."

def realM4OfficialPToDeciderLockedMessageUpperBridgeDecomposedInputs :
    List String :=
  realM4OfficialPToDeciderLockedMessageUpperSupportConstructionInputs ++
    realM4OfficialPToDeciderLanguageConstructionInputs

theorem realM4OfficialPToDeciderLockedMessageUpperBridgeDecomposedInputs_exact :
    realM4OfficialPToDeciderLockedMessageUpperBridgeDecomposedInputs =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "pMembershipToPNPDeciderFamily",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderLockedMessageUpperBridgeDecompositionStatement : String :=
  "The real v15/M4 locked-message official P-to-decider upper bridge decomposes into construction-side support data and official-language implication data.  The support data contains public-lock coverage, locked-message public-message data, and uniform CNF support.  The official-language side further splits into the named NP language, the P-membership-to-SAT-decider implication, and the P-membership-to-constant-decoder-regime implication."

def realM4OfficialPToDeciderUpperBridgeConstructionInputs : List String := [
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP",
  "defaultMessage",
  "publicLockCoverageData",
  "lockedMessageRigidity",
  "uniformCNFSupportData",
  "pMembershipToPNPDeciderFamily",
  "pMembershipConstantDecoderRegime"
]

theorem realM4OfficialPToDeciderUpperBridgeConstructionInputs_exact :
    realM4OfficialPToDeciderUpperBridgeConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "defaultMessage",
        "publicLockCoverageData",
        "lockedMessageRigidity",
        "uniformCNFSupportData",
        "pMembershipToPNPDeciderFamily",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderUpperBridgeStatement : String :=
  "For the real v15/M4 official upper bridge, P-membership of the named NP language must construct the Appendix-I SAT decider family and the associated constant-decoder regime.  Public-lock coverage, D.8 locked-message rigidity, and uniform CNF support remain explicit construction data; StarSW hardness and the analytic fields are not part of the bridge."

def realM4OfficialPToDeciderLockedMessageUpperBridgeConstructionInputs :
    List String := [
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP",
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "uniformCNFSupportData",
  "pMembershipToPNPDeciderFamily",
  "pMembershipConstantDecoderRegime"
]

theorem realM4OfficialPToDeciderLockedMessageUpperBridgeConstructionInputs_exact :
    realM4OfficialPToDeciderLockedMessageUpperBridgeConstructionInputs =
      [ "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "uniformCNFSupportData",
        "pMembershipToPNPDeciderFamily",
        "pMembershipConstantDecoderRegime" ] := by
  rfl

def realM4OfficialPToDeciderLockedMessageUpperBridgeStatement : String :=
  "For the real v15/M4 locked-message official upper bridge, P-membership of the named NP language must construct the Appendix-I SAT decider family and the associated constant-decoder regime.  Public-lock coverage, locked-message public-message data, and uniform CNF support remain explicit construction data; StarSW hardness and the analytic fields are not part of the bridge."

def realM4OfficialPToUniformConstantDecoderRegimeAdapterStatement : String :=
  "The official P-membership-to-constant-decoder-regime obligation is support-neutral once uniform CNF support is fixed: it reindexes to both the legacy default-message/D.8 upper-support package and the explicit locked-message-data upper-support package."

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

def realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP :
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
  "cnfVariableDecidableEquality",
  "realConstantDecoderRegime"
]

theorem realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP =
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
        "cnfVariableDecidableEquality",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP =
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
        "cnfVariableDecidableEquality",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, UpperLowerClash follows from the no-target-rows CD-ENF mechanical constructor, canonical Phase-A fixed-gap choice, the real lower machine, public-lock representative data, D.8 locked-message rigidity, formula-syntax CNF variable support with decidable variable equality, and the constant decoder regime, then exactly StarSW hardness and the three real analytic frontier objects safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The route derives singleMessage, noPublicTargetTags, admissibleHistories, and phaseABudget by construction; boundaryMixing carries epsSmall, so epsSmall is not a separate construction input."

def realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP :
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
  "cnfVariableAddressSyntax",
  "realConstantDecoderRegime"
]

theorem realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP =
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
        "cnfVariableAddressSyntax",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP =
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
        "cnfVariableAddressSyntax",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsAddressSyntaxCanonicalGapRealFrontierEndgameStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, UpperLowerClash follows from the no-target-rows CD-ENF mechanical constructor, canonical Phase-A fixed-gap choice, the real lower machine, public-lock representative data, D.8 locked-message rigidity, real CNF variable address syntax, and the constant decoder regime, then exactly StarSW hardness and the three real analytic frontier objects safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The address syntax constructs the local syntax roundtrip, Nat coding, and formula support; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP :
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
  "publicLockCoverageData",
  "lockedMessageRigidityData",
  "cnfVariableAddressSyntax",
  "realConstantDecoderRegime"
]

theorem realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP =
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "realConstantDecoderRegime" ] := by
  rfl

def realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameHypothesisAuditExplicitPNP =
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "realConstantDecoderRegime",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing",
        "pnpDeciderFamily" ] := by
  rfl

def realM4NoTargetRowsAddressSyntaxLockedMessageDataCanonicalGapRealFrontierEndgameStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, UpperLowerClash follows from the no-target-rows CD-ENF mechanical constructor, canonical Phase-A fixed-gap choice, the real lower machine, public-lock representative data, locked-message public-message data, real CNF variable address syntax, and the constant decoder regime, then exactly StarSW hardness and the three real analytic frontier objects safeQSSM / boundedGaugeIncidence / boundaryMixing with the explicit P=NP decider family.  The address syntax constructs the local syntax roundtrip, Nat coding, and formula support; the locked-message data carries the public-message invariant used by the upper readout adapter.  This is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP :
    List String :=
  realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierEndgameConstructionInputsExplicitPNP ++
    realM4OfficialPNPBridgeConstructionInputs

theorem realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP =
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
        "cnfVariableDecidableEquality",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP =
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
        "cnfVariableDecidableEquality",
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

def realM4NoTargetRowsFormulaSupportCanonicalGapRealFrontierOfficialEndpointStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, a Cook-style official separation endpoint follows from the no-target-rows canonical-gap real-frontier assembly, public-lock representative data, D.8 locked-message rigidity, formula-syntax CNF variable support with decidable variable equality, exactly StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge.  The route derives singleMessage, noPublicTargetTags, admissibleHistories, and phaseABudget; boundaryMixing includes epsSmall.  This is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP :
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
  "cnfVariableNatCoding",
  "realConstantDecoderRegime",
  "cookStylePNPClassInterface",
  "separatedLanguage",
  "separatedLanguageInNP",
  "internalClashNotInP"
]

theorem realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP_exact :
    realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP =
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
        "cnfVariableNatCoding",
        "realConstantDecoderRegime",
        "cookStylePNPClassInterface",
        "separatedLanguage",
        "separatedLanguageInNP",
        "internalClashNotInP" ] := by
  rfl

def realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP :
    List String :=
  realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointConstructionInputsExplicitPNP ++
    realM4CoveredLocksEndgameIrreducibleInputsExplicitPNP ++
      realM4CoveredLocksEndgameConditionalInputsExplicitPNP

theorem realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP_exact :
    realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointHypothesisAuditExplicitPNP =
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
        "cnfVariableNatCoding",
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

def realM4NoTargetRowsNatCodedFormulaSupportCanonicalGapRealFrontierOfficialEndpointStatementExplicitPNP : String :=
  "For the adjusted real no-target-rows public surface, a Cook-style official separation endpoint follows from the no-target-rows canonical-gap real-frontier assembly, public-lock representative data, D.8 locked-message rigidity, formula-syntax CNF variable support from injective natural coding of variable syntax, exactly StarSW hardness and the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing, the explicit P=NP decider family used by the upper side, and a separate Cook-style bridge.  The route derives decidable variable equality, singleMessage, noPublicTargetTags, admissibleHistories, and phaseABudget; boundaryMixing includes epsSmall.  This is conditional staging, not a proof of P != NP and not yet a full M4 identification."

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

def realM4NoTargetRowsPToDeciderOfficialEndpointConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "officialPToDeciderUpperSupportData",
    "officialPToDeciderLanguageData" ]

theorem realM4NoTargetRowsPToDeciderOfficialEndpointConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderOfficialEndpointConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "officialPToDeciderUpperSupportData",
        "officialPToDeciderLanguageData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs :
    List String :=
  [ "starSWHardness",
    "safeQSSM",
    "boundedGaugeIncidence",
    "boundaryMixing" ]

theorem realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs_exact :
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs =
      [ "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderOfficialEndpointHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderOfficialEndpointConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderOfficialEndpointHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderOfficialEndpointHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "officialPToDeciderUpperSupportData",
        "officialPToDeciderLanguageData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderOfficialEndpointStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style endpoint follows from the explicit real public-surface and lower-machine construction data, separated official upper support data, official P-membership-to-decider language data, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The theorem does not take a free P=NP decider family or raw clash-to-not-P bridge; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "officialPToDeciderLockedMessageUpperBridgeData" ]

theorem realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "officialPToDeciderLockedMessageUpperBridgeData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "officialPToDeciderLockedMessageUpperBridgeData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageBridgeClassInequalityStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style class inequality follows from the explicit real public-surface and lower-machine construction data, the packaged locked-message official P-to-decider upper bridge, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The bridge still contains the official NP-language, P-to-decider, and constant-decoder-regime obligations; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "cnfVariableEncodableSyntax",
    "officialPToDeciderLanguageData" ]

theorem realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "cnfVariableEncodableSyntax",
        "officialPToDeciderLanguageData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "cnfVariableEncodableSyntax",
        "officialPToDeciderLanguageData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderEncodableSyntaxOfficialEndpointStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style endpoint follows from the explicit real public-surface and lower-machine construction data, public-lock coverage, D.8 locked-message rigidity, locally encodable CNF variable syntax, official P-membership-to-decider language data, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The syntax roundtrip constructs the Nat coding and uniform formula support; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "cnfVariableAddressSyntax",
    "officialPToDeciderLanguageData" ]

theorem realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "cnfVariableAddressSyntax",
        "officialPToDeciderLanguageData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "cnfVariableAddressSyntax",
        "officialPToDeciderLanguageData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderAddressSyntaxOfficialEndpointStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style endpoint follows from the explicit real public-surface and lower-machine construction data, public-lock coverage, D.8 locked-message rigidity, real CNF variable address syntax, official P-membership-to-decider language data, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The address syntax constructs the local syntax roundtrip, Nat coding, and uniform formula support; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "cnfVariableAddressSyntax",
    "officialLanguageNPData",
    "officialPToDeciderFamilyData",
    "officialPToConstantDecoderRegimeData" ]

theorem realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "officialPToConstantDecoderRegimeData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "officialPToConstantDecoderRegimeData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderAddressSyntaxSplitOfficialEndpointStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style endpoint follows from the explicit real public-surface and lower-machine construction data, public-lock coverage, D.8 locked-message rigidity, real CNF variable address syntax, split official language/P-to-decider/P-to-constant-decoder-regime data, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The address syntax constructs the local syntax roundtrip, Nat coding, and uniform formula support; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "publicLockCoverageData",
    "lockedMessageRigidityData",
    "cnfVariableAddressSyntax",
    "officialLanguageNPData",
    "officialPToDeciderFamilyData",
    "officialPToLockedMessageConstantDecoderRegimeData" ]

theorem realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "officialPToLockedMessageConstantDecoderRegimeData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "officialPToLockedMessageConstantDecoderRegimeData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxSplitOfficialEndpointStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style endpoint follows from the explicit real public-surface and lower-machine construction data, public-lock coverage, locked-message public-message data, real CNF variable address syntax, split official language/P-to-decider/P-to-locked-message-constant-decoder-regime data, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The address syntax constructs the local syntax roundtrip, Nat coding, and uniform formula support; the locked-message data supplies the public-message invariant consumed by the upper readout adapter.  This is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "publicLockCoverageData",
    "lockedMessageRigidityData",
    "cnfVariableAddressSyntax",
    "officialLanguageNPData",
    "officialPToDeciderFamilyData",
    "officialPToUniformConstantDecoderRegimeData" ]

theorem realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "officialPToUniformConstantDecoderRegimeData" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "officialPToUniformConstantDecoderRegimeData",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxUniformRegimeSplitOfficialEndpointStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style endpoint follows from the explicit real public-surface and lower-machine construction data, public-lock coverage, locked-message public-message data, real CNF variable address syntax, split official language/P-to-decider data, support-neutral P-to-constant-decoder-regime data, and exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing.  The constant-decoder obligation is indexed only by the uniform CNF support and is reindexed to the locked-message upper support internally.  This is conditional staging, not a proof of P != NP and not yet a full M4 identification."

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityConstructionInputs :
    List String :=
  [ "noTargetRowsPublicSurface",
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
    "publicLockCoverageData",
    "lockedMessageRigidityData",
    "cnfVariableAddressSyntax",
    "officialLanguageNPData",
    "officialPToDeciderFamilyData",
    "pMembershipKpolyAtConstantDecoderIdentification",
    "pMembershipEtaTimesLinearFloorIdentification",
    "pMembershipConstantDecoderBelowLinearFloor" ]

theorem realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityConstructionInputs_exact :
    realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityConstructionInputs =
      [ "noTargetRowsPublicSurface",
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipKpolyAtConstantDecoderIdentification",
        "pMembershipEtaTimesLinearFloorIdentification",
        "pMembershipConstantDecoderBelowLinearFloor" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityHypothesisAudit :
    List String :=
  realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityConstructionInputs ++
    realM4NoTargetRowsPToDeciderOfficialEndpointContentInputs

theorem realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityHypothesisAudit_exact :
    realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityHypothesisAudit =
      [ "noTargetRowsPublicSurface",
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
        "publicLockCoverageData",
        "lockedMessageRigidityData",
        "cnfVariableAddressSyntax",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipKpolyAtConstantDecoderIdentification",
        "pMembershipEtaTimesLinearFloorIdentification",
        "pMembershipConstantDecoderBelowLinearFloor",
        "starSWHardness",
        "safeQSSM",
        "boundedGaugeIncidence",
        "boundaryMixing" ] := by
  rfl

def realM4NoTargetRowsPToDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplitClassInequalityStatement : String :=
  "For the real v15/M4 no-target-rows staging route, the Cook-style class inequality follows from the explicit real public-surface and lower-machine construction data, public-lock coverage, locked-message public-message data, real CNF variable address syntax, split official language/P-to-decider data, and the three explicit P-membership-indexed K-poly compatibility facts needed to construct the support-neutral constant-decoder regime.  The endpoint still depends on exactly StarSW hardness plus the three analytic fields safeQSSM / boundedGaugeIncidence / boundaryMixing as mathematical frontier inputs; this is conditional staging, not a proof of P != NP and not yet a full M4 identification."

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
    item := "formulaSyntaxCNFSupport"
    status := .partialConstructionTransferred
    checkedName := "realM4_uniformCNFSupport_of_formulaSyntax"
    note := "The sharp upper-side route extracts the variable cover from each finite CNF formula, so whole-variable Fintype data is no longer needed; decidable equality is supplied mechanically once the real variable syntax has injective Nat coding."
  },
  {
    item := "cnfVariableDecidableEquality"
    status := .partialConstructionTransferred
    checkedName := "realM4_varDecidable_of_variableNatCoding"
    note := "Decidable equality for real CNF variables follows from injective natural coding of the variable syntax; the remaining construction obligation is the code and its injectivity proof."
  },
  {
    item := "cnfVariableAddressSyntax"
    status := .openConstruction
    checkedName := "RealM4CNFVariableAddressSyntaxData"
    note := "The real M4 variable syntax must supply tagged/address-style syntax, a syntax encoder/decoder roundtrip, and a parser back to variables."
  },
  {
    item := "cnfVariableEncodableSyntaxFromAddressSyntax"
    status := .partialConstructionTransferred
    checkedName := "realM4_variableEncodableSyntax_of_addressSyntax"
    note := "Real variable address syntax mechanically supplies the local encode/decode package used by the CNF support route."
  },
  {
    item := "cnfVariableNatCodingFromEncodableSyntax"
    status := .partialConstructionTransferred
    checkedName := "realM4_variableNatCoding_of_encodableSyntax"
    note := "Locally encodable real variable syntax mechanically supplies the injective Nat code used by formula-syntax CNF support."
  },
  {
    item := "cnfVariableNatCodingFromFiniteTypes"
    status := .partialConstructionTransferred
    checkedName := "realM4_variableNatCoding_of_finiteVariableTypes"
    note := "Finite real CNF variable types mechanically supply an injective Nat code through their canonical finite equivalence.  This is a supplier for the Nat-coded route, not a substitute for explicit syntactic coding when the real variable family is infinite."
  },
  {
    item := "uniformCNFSupportData"
    status := .partialConstructionTransferred
    checkedName := "RealM4FiniteCNFVariableFamilyData.uniformSupport"
    note := "Once finite variable-family data is constructed, the uniform support package is the canonical enumeration of all variables; with the conditional decider it reconstructs the bit-fixing package."
  },
  {
    item := "realConstantDecoderRegime"
    status := .openConstruction
    checkedName := "RealM4UniformConstantDecoderRegime"
    note := "The real lower framework must identify kpolyAt with the fixed uniform self-reduction decoder, identify etaTimes with the linear floor, and prove that this constant decoder sits below the target-block floor.  This is K-poly compatibility for the real construction, not a new analytic input."
  },
  {
    item := "realConstantDecoderProgramModel"
    status := .constructionTransferred
    checkedName := "realM4UniformConstantDecoderKpolyAt_const"
    note := "The upper-side program model is target-block constant: the uniform P=NP decider program-length bound is combined with fixed compiler, bit-fixing-driver, and readout program lengths.  The open part is lower-framework compatibility with this fixed program."
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
    status := .openConstruction
    checkedName := "realM4_lockedMessageData_of_coverageDataAndRigidity"
    note := "Primitive sharp-route readout construction item: the real M4 locked core must supply an explicit public-message function and prove every accepted completion over a supported lock reads that message."
  },
  {
    item := "lockedMessageRigidity"
    status := .partialConstructionTransferred
    checkedName := "realM4_lockedMessageRigidity_of_lockedMessageData"
    note := "The old Appendix D.8 proposition follows from explicit locked-message public-message data; it is not primitive on the sharp locked-message route."
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
    item := "realLowerMachineAddressSyntaxCoverageAndRigidityConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_lowerMachine_addressSyntax_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP"
    note := "Builds uniform formula support from real CNF address syntax before invoking the lower-machine, public-lock coverage, D.8 rigidity, explicit-P=NP upper, and real-frontier clash staging theorem."
  },
  {
    item := "realLowerMachineAddressSyntaxCoverageAndLockedMessageDataConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_lowerMachine_addressSyntax_coverageDataAndLockedMessageData_canonicalGap_realFrontier_explicitPNP"
    note := "Sharpens the address-syntax internal clash route so the upper readout side takes explicit locked-message public-message data instead of raw D.8 rigidity plus a default message."
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
    status := .blockedByCounterexample
    checkedName := "RealM4OfficialPNPBridgeData"
    note := "The raw clash-to-not-P bridge is too weak as a real Cook target because it can be inhabited from an arbitrary NP-language witness by ex falso."
  },
  {
    item := "officialPNPBridgeExFalsoOnly"
    status := .blockedByCounterexample
    checkedName := "realM4_officialBridgeData_of_npWitness_exFalso"
    note := "The raw bridge adapter can be inhabited from any NP-language witness by ex falso from UpperLowerClash.noConsistentBounds, so this adapter alone is not the real Cook-style bridge."
  },
  {
    item := "officialPNPUpperBridgeData"
    status := .partialConstructionTransferred
    checkedName := "realM4_officialUpperBridge_of_pMembershipDeciderData"
    note := "The nondegenerate upper bridge can be assembled from decomposed P-membership-to-decider data plus visible M4 construction-side support."
  },
  {
    item := "officialPToDeciderUpperBridgeData"
    status := .partialConstructionTransferred
    checkedName := "realM4_officialPToDeciderUpperBridgeData_of_supportAndLanguage"
    note := "The monolithic official P-to-decider bridge is assembled from separated construction-side upper support data and official-language implication data."
  },
  {
    item := "officialPToDeciderUpperSupportData"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToDeciderUpperSupportData.ofCoverageRigidityAndAddressSyntax"
    note := "Construction-side upper support is separated from the official bridge and can be built from default message, public-lock coverage, D.8 rigidity, and real CNF variable address syntax."
  },
  {
    item := "officialPToDeciderLockedMessageUpperSupportData"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToDeciderLockedMessageUpperSupportData.ofCoverageLockedMessageDataAndAddressSyntax"
    note := "Construction-side official upper support can also be built from public-lock coverage, explicit locked-message public-message data, and real CNF variable address syntax, with no default-message/raw-D.8 boundary."
  },
  {
    item := "officialLanguageNPData"
    status := .openConstruction
    checkedName := "RealM4OfficialLanguageNPData"
    note := "Official Cook-style bridge content: name the language represented by the real M4 ensemble and prove it is in NP."
  },
  {
    item := "officialPToDeciderFamilyData"
    status := .openConstruction
    checkedName := "RealM4OfficialPToDeciderFamilyData"
    note := "Official Cook-style bridge content: prove that P-membership of the named NP language supplies the Appendix-I SAT decider family."
  },
  {
    item := "officialPToUniformConstantDecoderRegimeData"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToUniformConstantDecoderRegimeData.ofKpolyCompatibility"
    note := "The support-neutral constant-decoder regime is no longer primitive on the sharp route; it is constructed from explicit P-membership-indexed K-poly compatibility facts."
  },
  {
    item := "officialPToUniformConstantDecoderRegimeKpolyCompatibility"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToUniformConstantDecoderRegimeData.ofKpolyCompatibility"
    note := "The support-neutral constant-decoder obligation is built from explicit P-membership-indexed K-poly compatibility facts: kpolyAt identifies with the fixed constant decoder program, etaTimes identifies with the linear floor, and the decoder cost lies below that floor."
  },
  {
    item := "pMembershipKpolyAtConstantDecoderIdentification"
    status := .openConstruction
    checkedName := "RealM4OfficialPToUniformConstantDecoderRegimeData.ofKpolyCompatibility"
    note := "Real official P-membership must identify the lower framework's kpolyAt with the fixed uniform constant-decoder program for the P-derived decider family."
  },
  {
    item := "pMembershipEtaTimesLinearFloorIdentification"
    status := .openConstruction
    checkedName := "RealM4OfficialPToUniformConstantDecoderRegimeData.ofKpolyCompatibility"
    note := "Real official P-membership must identify the lower framework's etaTimes with the linear compression floor used by the real lower framework."
  },
  {
    item := "pMembershipConstantDecoderBelowLinearFloor"
    status := .openConstruction
    checkedName := "RealM4OfficialPToUniformConstantDecoderRegimeData.ofKpolyCompatibility"
    note := "Real official P-membership must prove the fixed self-reduction decoder cost lies below the linear compression floor in the target regime."
  },
  {
    item := "officialPToConstantDecoderRegimeData"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToUniformConstantDecoderRegimeData.toLegacySupport"
    note := "The legacy constant-decoder-regime package is no longer primitive on the sharp route; it is obtained by reindexing the support-neutral obligation to the legacy upper-support package."
  },
  {
    item := "officialPToDeciderLanguageData"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToDeciderLanguageData"
    note := "The legacy official-language package is now reassembled from the named NP-language data, P-to-decider data, and P-to-constant-decoder-regime data."
  },
  {
    item := "officialPToDeciderLockedMessageLanguageData"
    status := .partialConstructionTransferred
    checkedName := "RealM4OfficialPToDeciderLockedMessageLanguageData"
    note := "The locked-message official-language package is reassembled from the same named NP-language and P-to-decider obligations, but its constant-decoder regime is indexed by locked-message support data."
  },
  {
    item := "officialPToDeciderLockedMessageUpperBridgeData"
    status := .partialConstructionTransferred
    checkedName := "realM4_officialPToDeciderLockedMessageUpperBridgeData_of_supportAndLanguage"
    note := "The monolithic locked-message official P-to-decider bridge is assembled from locked-message construction-side support data and official-language implication data."
  },
  {
    item := "officialPToDeciderUpperBridgeAdapter"
    status := .partialConstructionTransferred
    checkedName := "realM4_not_pEqualsNP_from_endgameMechanicalData_pMembershipDeciderBridge"
    note := "Given the decomposed P-membership-to-decider bridge, real endgame data plus StarSW and the three analytic fields rule out Cook-style P = NP; the existential endpoint follows by the class-interface equivalence."
  },
  {
    item := "officialPToDeciderLockedMessageUpperBridgeAdapter"
    status := .partialConstructionTransferred
    checkedName := "realM4_not_pEqualsNP_from_endgameMechanicalData_pMembershipDeciderLockedMessageBridge"
    note := "Given the locked-message decomposed P-membership-to-decider bridge, real endgame data plus StarSW and the three analytic fields rule out Cook-style P = NP; the existential endpoint follows by the class-interface equivalence."
  },
  {
    item := "realNoTargetRowsPToDeciderLockedMessageBridgeClassInequality"
    status := .partialConstructionTransferred
    checkedName := "realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageBridge"
    note := "Restates the no-target-rows canonical-gap real-frontier route through the locked-message official bridge as Cook-style P != NP, while keeping construction of that bridge and the real constant-decoder regime as explicit obligations."
  },
  {
    item := "realNoTargetRowsPToDeciderOfficialEndpointStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntax"
    note := "Routes the current no-target-rows, canonical-gap, real-frontier construction through the decomposed official P-membership-to-decider bridge, with construction-side upper support supplied by real CNF address syntax; no free explicit P=NP decider family or raw clash-to-not-P bridge is a theorem hypothesis on this route."
  },
  {
    item := "realNoTargetRowsPToDeciderSplitOfficialEndpointStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderAddressSyntaxSplit"
    note := "Sharpens the address-syntax official endpoint route so the theorem surface takes the named NP language, P-to-decider family, and P-to-constant-decoder-regime obligations separately instead of a bundled language-data package."
  },
  {
    item := "realNoTargetRowsPToDeciderLockedMessageSplitOfficialEndpointStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxSplit"
    note := "Routes the sharp no-target-rows address-syntax official endpoint through explicit locked-message public-message data, eliminating the default-message/raw-rigidity adapter on this path while keeping the named official obligations split."
  },
  {
    item := "realNoTargetRowsPToDeciderUniformRegimeOfficialEndpointStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit"
    note := "Sharpens the locked-message address-syntax official endpoint so the P-to-constant-decoder obligation is support-neutral and reindexed to locked-message support internally."
  },
  {
    item := "realNoTargetRowsPToDeciderUniformRegimeOfficialClassInequality"
    status := .partialConstructionTransferred
    checkedName := "realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxUniformRegimeSplit"
    note := "Restates the sharp support-neutral official endpoint as the Cook-style class inequality, with the contradiction form available separately from the same construction data and four frontier inputs."
  },
  {
    item := "realNoTargetRowsPToDeciderKpolyCompatibilityOfficialClassInequality"
    status := .partialConstructionTransferred
    checkedName := "realM4_not_pEqualsNP_from_noTargetRowsCDENF_lowerMachine_canonicalGap_realFrontier_pMembershipDeciderLockedMessageAddressSyntaxKpolyCompatibilitySplit"
    note := "Restates the sharp support-neutral official endpoint as the Cook-style class inequality while constructing the constant-decoder regime internally from explicit K-poly compatibility facts."
  },
  {
    item := "officialPNPUpperBridgeAdapter"
    status := .partialConstructionTransferred
    checkedName := "realM4_not_pEqualsNP_from_endgameMechanicalData_upperBridge"
    note := "Given the strict upper bridge, the real endgame data plus StarSW and the three analytic fields rule out Cook-style P = NP without taking a free P=NP decider family as a theorem hypothesis."
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
    checkedName := "realM4_exists_np_not_p_from_noTargetRowsCDENF_lowerMachine_natCodedFormulaSupport_coverageDataAndRigidity_canonicalGap_realFrontier_explicitPNP"
    note := "Wires the current no-target-rows, canonical-gap, Nat-coded formula-support real-frontier internal clash assembly through explicit Cook-style bridge data to ∃ L, inNP L ∧ ¬ inP L; the bridge and real construction fields remain exposed obligations."
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
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.constructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.blockedByCounterexample,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
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
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.blockedByCounterexample,
        RealM4LiftStatus.blockedByCounterexample,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
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
  "lockedMessageRigidityData",
  "noPublicTargetTags",
  "hiddenGaugeProduct",
  "admissibleHistories",
  "cnfVariableAddressSyntax",
  "realCompressionLowerMachineData",
  "realConstantDecoderRegime",
  "officialLanguageNPData",
  "officialPToDeciderFamilyData",
  "pMembershipKpolyAtConstantDecoderIdentification",
  "pMembershipEtaTimesLinearFloorIdentification",
  "pMembershipConstantDecoderBelowLinearFloor"
]

theorem realM4OpenConstructionItems_exact :
    realM4OpenConstructionItems =
      [ "publicLockCoverageData",
        "lockedMessageRigidityData",
        "noPublicTargetTags",
        "hiddenGaugeProduct",
        "admissibleHistories",
        "cnfVariableAddressSyntax",
        "realCompressionLowerMachineData",
        "realConstantDecoderRegime",
        "officialLanguageNPData",
        "officialPToDeciderFamilyData",
        "pMembershipKpolyAtConstantDecoderIdentification",
        "pMembershipEtaTimesLinearFloorIdentification",
        "pMembershipConstantDecoderBelowLinearFloor" ] := by
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
