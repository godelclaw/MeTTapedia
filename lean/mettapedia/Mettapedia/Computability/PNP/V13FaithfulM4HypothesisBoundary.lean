import Mettapedia.Computability.PNP.V13FaithfulM4Mechanical

/-!
# Exact hypothesis boundary for the concrete M4 scaffold

The concrete regioned object reaches the locked-message boundary but does not
cross it.  Its local lock auxiliary can absorb any message choice, so exact
Hypothesis D.8 is false.  This module proves that obstruction against the
faithful record and consequently proves that the full
`V13M4OpenConstructionObligations` record is not inhabited on this object.

The public catalog itself contains every visible geometry, quotient, buffer,
lock, readout, and probe-syntax primitive and contains no raw assignment.  Its
exact D.30 record is constructible.  D.33 remains open because classifying a
new datatype is not a proof that actual observer executions expand to those
classes.  D.48 and every quantitative analytic package also remain exact open
hypotheses.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## D.30 on the full concrete public catalog -/

theorem v13M4Concrete_noPrimitiveRecoversTargetWithoutCharge
    (m t : Nat) (primitive : V13M4ConcretePublicPrimitive m t) :
    ¬ v13M4ConcreteRecoversTargetWithoutCharge primitive := by
  rintro ⟨j, recover, hrecover⟩
  let omega0 : V13M4ConcreteWorld m t :=
    { neutralToken := false
      z := fun _ => false
      g := fun _ => false
      bufferLeft := fun _ => false
      messageBits := fun _ => false }
  let omega1 : V13M4ConcreteWorld m t :=
    { neutralToken := false
      z := fun _ => false
      g := fun _ => false
      bufferLeft := fun _ => false
      messageBits := fun _ => true }
  have h0 := hrecover omega0
  have h1 := hrecover omega1
  have hvalue : v13M4ConcretePrimitiveValue primitive omega0 =
      v13M4ConcretePrimitiveValue primitive omega1 := by
    cases primitive <;> rfl
  have hfalse : false = recover (v13M4ConcretePrimitiveValue primitive omega0) := by
    simpa [omega0] using h0
  have htrue : true = recover (v13M4ConcretePrimitiveValue primitive omega1) := by
    simpa [omega1] using h1
  have : false = true := hfalse.trans (hvalue ▸ htrue.symm)
  contradiction

/-- Exact D.30 full-public-syntax coverage for the current scaffold.  This
does not establish D.8: the public syntax is tag-free precisely while the
current lock relation still leaves the message free. -/
theorem v13M4Concrete_D30_noPublicTargetTags :
    V13D30NoPublicTargetTags V13M4ConcreteE := by
  constructor
  constructor
  · intro theta m t primitive _
    cases theta
    change v13M4ConcreteDeclaredNeutral primitive ∨
      v13M4ConcreteChargedExpansion primitive
    cases primitive <;> simp [
      v13M4ConcreteDeclaredNeutral, v13M4ConcreteChargedExpansion]
  · intro theta m t primitive _
    cases theta
    change ¬False
    simp
  · intro theta m t primitive _
    cases theta
    change ¬v13M4ConcreteRecoversTargetWithoutCharge primitive
    exact v13M4Concrete_noPrimitiveRecoversTargetWithoutCharge m t primitive

/-! ## Exact D.8 obstruction -/

def v13M4ConcreteZeroPublic : V13M4ConcretePublic 0 0 := ⟨false⟩
def v13M4ConcreteZeroGauge : V13M4ConcreteGaugeVector 0 := fun _ => false
def v13M4ConcreteFalseLockAux : V13M4ConcreteMessageVector 0 := fun _ => false
def v13M4ConcreteTrueLockAux : V13M4ConcreteMessageVector 0 := fun _ => true

def v13M4ConcreteZeroWorld : V13M4ConcreteWorld 0 0 where
  neutralToken := false
  z := fun _ => false
  g := fun _ => false
  bufferLeft := fun _ => false
  messageBits := fun _ => false

theorem v13M4Concrete_zeroPublic_supported :
    exists omega : V13M4ConcreteE.World () 0 0,
      V13M4ConcreteE.supported omega ∧
        V13M4ConcreteE.publicInput omega = v13M4ConcreteZeroPublic := by
  exact ⟨v13M4ConcreteZeroWorld, trivial, rfl⟩

theorem v13M4Concrete_falseCompletion_lock :
    @V13M4LocalComponents.lockPredicate V13M4ConcreteE V13M4ConcreteG
      V13M4ConcreteC () 0 0 v13M4ConcreteZeroPublic
      v13M4ConcreteZeroGauge v13M4ConcreteFalseLockAux [false] := by
  constructor
  · rfl
  · intro i
    fin_cases i
    rfl

theorem v13M4Concrete_falseCompletion_readout :
    @V13M4LocalComponents.readoutPredicate V13M4ConcreteE V13M4ConcreteG
      V13M4ConcreteC () 0 0 v13M4ConcreteZeroPublic
      v13M4ConcreteZeroGauge v13M4ConcreteFalseLockAux [false] := by
  constructor
  · rfl
  · intro i
    fin_cases i
    rfl

theorem v13M4Concrete_trueCompletion_lock :
    @V13M4LocalComponents.lockPredicate V13M4ConcreteE V13M4ConcreteG
      V13M4ConcreteC () 0 0 v13M4ConcreteZeroPublic
      v13M4ConcreteZeroGauge v13M4ConcreteTrueLockAux [true] := by
  constructor
  · rfl
  · intro i
    fin_cases i
    rfl

theorem v13M4Concrete_trueCompletion_readout :
    @V13M4LocalComponents.readoutPredicate V13M4ConcreteE V13M4ConcreteG
      V13M4ConcreteC () 0 0 v13M4ConcreteZeroPublic
      v13M4ConcreteZeroGauge v13M4ConcreteTrueLockAux [true] := by
  constructor
  · rfl
  · intro i
    fin_cases i
    rfl

/-- Precise honest hatch: the current bounded-arity connector is not a locked
core.  It has two accepted completions over one supported public syntax with
different messages, so exact Hypothesis D.8 fails. -/
theorem v13M4Concrete_D8_lockedMessageRigidity_obstruction :
    ¬ V13D8LockedMessageRigidity V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC := by
  intro hD8
  have hmessages := hD8.locked_message_rigidity () 0 0
    v13M4ConcreteZeroPublic
    v13M4ConcreteZeroGauge v13M4ConcreteZeroGauge
    v13M4ConcreteFalseLockAux v13M4ConcreteTrueLockAux
    [false] [true]
    v13M4Concrete_zeroPublic_supported
    v13M4Concrete_falseCompletion_lock
    v13M4Concrete_falseCompletion_readout
    v13M4Concrete_trueCompletion_lock
    v13M4Concrete_trueCompletion_readout
  simp at hmessages

/-! ## Exact unresolved records -/

/-- Actual normalized-primitive carrier expected from a future execution-trace
expansion.  Merely declaring these constructors does not establish D.33. -/
inductive V13M4ConcreteNormalizedPrimitive (m t : Nat) where
  | publicSyntax : V13M4ConcretePublicPrimitive m t ->
      V13M4ConcreteNormalizedPrimitive m t
  | safeBuffer : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ConcreteNormalizedPrimitive m t
  | rawGauge : V13M4ConcreteGaugeIndex m -> Bool ->
      V13M4ConcreteNormalizedPrimitive m t
deriving DecidableEq, Repr

/-- Exact open boundary on this one ensemble.  No field is replaced by a
weaker proposition.  The D.8 field makes the boundary uninhabited for the
current scaffold, as proved below; a revised lock core is required before the
remaining hypotheses can be assembled into a faithful M4 inhabitant. -/
structure V13M4ConcreteExactHypothesisBoundary where
  uniformGaugeLift :
    V13M4UniformGaugeLift V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
  adaptiveHiddenGaugeProduct : V13HiddenGaugeProductFrontier V13M4ConcreteE
  D8_lockedMessageRigidity :
    V13D8LockedMessageRigidity V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
  D30_noPublicTargetTags : V13D30NoPublicTargetTags V13M4ConcreteE
  D33_atomCompleteness :
    V13D33AtomCompleteness V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
      (fun _ m t => V13M4ConcreteNormalizedPrimitive m t)
  D48_compatibleCouplings :
    V13D48CompatibleCouplings V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
  analytic : V13FaithfulAnalyticFrontiers V13M4ConcreteE

theorem v13M4Concrete_exactHypothesisBoundary_obstructed :
    ¬ Nonempty V13M4ConcreteExactHypothesisBoundary := by
  rintro ⟨boundary⟩
  exact v13M4Concrete_D8_lockedMessageRigidity_obstruction
    boundary.D8_lockedMessageRigidity

/-- Therefore the exact faithful construction record itself is not inhabited
on this scaffold, independently of how D.33 or D.48 are later formulated. -/
theorem v13M4Concrete_openConstructionObligations_obstructed :
    ¬ Nonempty
      (V13M4OpenConstructionObligations V13M4ConcreteE V13M4ConcreteG
        V13M4ConcreteC
        (fun _ m t => V13M4ConcreteNormalizedPrimitive m t)
        (fun _ m t => V13M4ConcreteCNFVar m t)) := by
  rintro ⟨construction⟩
  exact v13M4Concrete_D8_lockedMessageRigidity_obstruction
    construction.D8_lockedMessageRigidity

end Mettapedia.Computability.PNP
