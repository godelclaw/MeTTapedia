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

universe u v w x y z a b c d e f g h i j k l

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

def realM4SelfReductionUpperDischargePrerequisites : List String := [
  "publicMessageInvariant",
  "uniformCNFBitFixingPackage",
  "realCompressionLowerFramework"
]

theorem realM4SelfReductionUpperDischargePrerequisites_exact :
    realM4SelfReductionUpperDischargePrerequisites =
      [ "publicMessageInvariant",
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
  "publicMessageInvariant",
  "uniformCNFSupportData",
  "realCompressionLowerFramework"
]

theorem realM4SelfReductionUpperExplicitPNPConstructionInputs_exact :
    realM4SelfReductionUpperExplicitPNPConstructionInputs =
      [ "publicMessageInvariant",
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
    item := "uniformCNFSupportData"
    status := .partialConstructionTransferred
    checkedName := "RealM4CNFUniformSupportData.withPNPDecider"
    note := "The construction-side family adapter is split from the P=NP decider family; with that conditional decider it reconstructs the uniform bit-fixing package."
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
    checkedName := "realM4_selfReductionUpperExplicitPNPDischarge_assignment_readout_cost_and_upper"
    note := "Bundles the public-message invariant, construction-side uniform support, explicit P=NP decider family, and constant decoder regime into the real upper-side discharge package."
  },
  {
    item := "deterministicReadoutOnly"
    status := .blockedByCounterexample
    checkedName := "lockedCoreIdentityReadoutFamily_lab_refutation"
    note := "Deterministic per-state readout alone does not supply cross-completion message rigidity."
  },
  {
    item := "publicMessageInvariant"
    status := .openConstruction
    checkedName := "lockedCorePublicMessageInvariant_lab_guardrails"
    note := "A real M4 lock needs a public-message invariant or equivalent cross-completion rigidity theorem."
  },
  {
    item := "noPublicTargetTags"
    status := .partialConstructionTransferred
    checkedName := "v13RealLinearNoTargetRows_noPublicTargetTags"
    note := "The adjusted real no-target-rows linear surface proves the v13 neutral-skeleton/opposite-pair shape; the full M4 mechanical interface still has to connect this surface to its neutral skeleton."
  },
  {
    item := "atomCompleteness"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.atomCompleteness"
    note := "The M4 raw evidence atoms still need a concrete CD-ENF completeness proof."
  },
  {
    item := "gaugeFaithfulness"
    status := .openConstruction
    checkedName := "GaugeBufferedLockedInterface.gaugeFaithfulness"
    note := "The M4 hidden-gauge leaves still need a concrete faithfulness proof."
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
    checkedName := "v13RealLinearNoTargetRows_publicCoordinate_admissible"
    note := "Every single public coordinate of the adjusted real no-target-rows surface has the balanced-bit and balanced-conditioning pair; full M4 histories still need manuscript-history atom identification and connection."
  },
  {
    item := "realCompressionLowerFramework"
    status := .openConstruction
    checkedName := "CompressionLowerFramework"
    note := "The real lower framework must use manuscript compression-from-success data, not toy dummy budgets."
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
    status := .openConstruction
    checkedName := "RealM4EndgameMechanicalData"
    note := "The real M4 construction still has to supply the mechanical interface data, phase-A budget, eps-small bound, lower framework, and kernel-neutrality payload."
  },
  {
    item := "realConditionalClashStaging"
    status := .partialConstructionTransferred
    checkedName := "realM4_conditionalClash_from_endgameMechanicalData_explicitPNP"
    note := "Given real endgame mechanical data, the explicit-P=NP upper discharge package, StarSW, and the three analytic fields, the v13 UpperLowerClash wiring is checked."
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
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.blockedByCounterexample,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.openConstruction,
        RealM4LiftStatus.partialConstructionTransferred,
        RealM4LiftStatus.pnpConditionalInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput,
        RealM4LiftStatus.irreducibleInput] := by
  rfl

def realM4OpenConstructionItems : List String := [
  "publicMessageInvariant",
  "noPublicTargetTags",
  "atomCompleteness",
  "gaugeFaithfulness",
  "hiddenGaugeProduct",
  "admissibleHistories",
  "uniformCNFSupportData",
  "realCompressionLowerFramework",
  "realM4EndgameMechanicalData"
]

theorem realM4OpenConstructionItems_exact :
    realM4OpenConstructionItems =
      [ "publicMessageInvariant",
        "noPublicTargetTags",
        "atomCompleteness",
        "gaugeFaithfulness",
        "hiddenGaugeProduct",
        "admissibleHistories",
        "uniformCNFSupportData",
        "realCompressionLowerFramework",
        "realM4EndgameMechanicalData" ] := by
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
