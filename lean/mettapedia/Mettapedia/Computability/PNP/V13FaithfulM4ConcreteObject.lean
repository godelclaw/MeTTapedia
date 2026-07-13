import Mathlib.Data.Nat.Dist
import Mettapedia.Computability.PNP.PNPv13FaithfulM4Spec

/-!
# A regioned mechanical Appendix-D/I object

This module defines a size-indexed five-region finite object with growing
quotient/gauge rank.  It is a mechanical scaffold for the faithful M4
specification: public syntax contains geometry and local constraint kinds but
no raw witness assignment; worlds contain explicit `x/g/z` representatives,
a bounded-arity lock/readout layer, and a strictly positive non-degenerate
buffer layer.

The local lock relation deliberately does not force a common message.  Thus
this object does not claim Hypothesis D.8, and no target message is baked into
the readout predicate.  D.8, D.30, D.33, D.48, the adaptive hidden-gauge
product law, and the four analytic packages are handled at the explicit
hypothesis boundary in later modules.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Finite indices and the five bands -/

abbrev V13M4ConcreteGaugeIndex (m : Nat) := Fin (m + 1)
abbrev V13M4ConcreteMessageIndex (t : Nat) := Fin (t + 1)
abbrev V13M4ConcreteGaugeVector (m : Nat) := V13M4ConcreteGaugeIndex m -> Bool
abbrev V13M4ConcreteMessageVector (t : Nat) := V13M4ConcreteMessageIndex t -> Bool

/-- Map every message-local constraint to a genuine quotient coordinate. -/
def v13M4ConcreteMessageGaugeIndex {m t : Nat}
    (i : V13M4ConcreteMessageIndex t) : V13M4ConcreteGaugeIndex m :=
  ⟨i.val % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- Concrete sites.  Every band is nonempty even at size zero, while the
buffer, gauge, lock, and readout bands grow with their corresponding index. -/
inductive V13M4ConcreteSite (m t : Nat) where
  | neutral : V13M4ConcreteSite m t
  | buffer : V13M4ConcreteGaugeIndex m -> V13M4ConcreteSite m t
  | locked : V13M4ConcreteMessageIndex t -> V13M4ConcreteSite m t
  | gauge : V13M4ConcreteGaugeIndex m -> V13M4ConcreteSite m t
  | readout : V13M4ConcreteMessageIndex t -> V13M4ConcreteSite m t
deriving DecidableEq, Fintype, Repr

def v13M4ConcreteRegion {m t : Nat} : V13M4ConcreteSite m t -> V13M4Region
  | .neutral => .neutral
  | .buffer _ => .buffer
  | .locked _ => .locked
  | .gauge _ => .gauge
  | .readout _ => .readout

/-- Consecutive code used for the concrete path geometry. -/
def v13M4ConcreteSiteCode {m t : Nat} : V13M4ConcreteSite m t -> Nat
  | .neutral => 0
  | .buffer v => 1 + v.val
  | .locked i => 1 + (m + 1) + i.val
  | .gauge v => 1 + (m + 1) + (t + 1) + v.val
  | .readout i => 1 + (m + 1) + (t + 1) + (m + 1) + i.val

/-- The graph is the path induced by consecutive site codes. -/
def v13M4ConcreteEdge {m t : Nat}
    (a b : V13M4ConcreteSite m t) : Prop :=
  v13M4ConcreteSiteCode a + 1 = v13M4ConcreteSiteCode b ∨
    v13M4ConcreteSiteCode b + 1 = v13M4ConcreteSiteCode a

/-- Exact path distance for the consecutive site coding. -/
def v13M4ConcreteDistance {m t : Nat}
    (a b : V13M4ConcreteSite m t) : Nat :=
  Nat.dist (v13M4ConcreteSiteCode a) (v13M4ConcreteSiteCode b)

inductive V13M4ConcreteScope (m t : Nat) where
  | neutral
  | quotient : V13M4ConcreteGaugeIndex m -> V13M4ConcreteScope m t
  | buffer : V13M4ConcreteGaugeIndex m -> V13M4ConcreteScope m t
  | locked : V13M4ConcreteMessageIndex t -> V13M4ConcreteScope m t
  | readout : V13M4ConcreteMessageIndex t -> V13M4ConcreteScope m t
deriving DecidableEq, Fintype, Repr

def v13M4ConcreteScopeSites {m t : Nat} :
    V13M4ConcreteScope m t -> Finset (V13M4ConcreteSite m t)
  | .neutral => {.neutral}
  | .quotient v => {.gauge v}
  | .buffer v => {.buffer v, .gauge v}
  | .locked i => {.locked i, .gauge (v13M4ConcreteMessageGaugeIndex i)}
  | .readout i =>
      {.readout i, .locked i, .gauge (v13M4ConcreteMessageGaugeIndex i)}

/-! ## Public syntax, hidden witnesses, and sampler worlds -/

/-- The visible object carries only a neutral token.  The geometry, local XOR
constraint kinds, buffer law, and probe catalog are canonical functions of
`m,t`; no `x/g/z`, auxiliary, or message assignment is present here. -/
structure V13M4ConcretePublic (m t : Nat) where
  neutralToken : Bool
deriving DecidableEq, Fintype, Repr

/-- Two buffer bits per quotient coordinate.  Their parity is constrained by
the quotient boundary, leaving two admissible positive-mass choices. -/
abbrev V13M4ConcreteBufferAux (m : Nat) :=
  V13M4ConcreteGaugeIndex m -> Bool × Bool

/-- Explicit Appendix-D witness blocks. -/
structure V13M4ConcreteWitness (m t : Nat) where
  x : V13M4ConcreteGaugeVector m
  g : V13M4ConcreteGaugeVector m
  z : V13M4ConcreteGaugeVector m
  lockAux : V13M4ConcreteMessageVector t
  bufferAux : V13M4ConcreteBufferAux m
  localAux : Unit
  messageBits : V13M4ConcreteMessageVector t
deriving DecidableEq

/-- Sampler randomness before the deterministic gauge lift and local auxiliary
completion are assembled into a witness. -/
structure V13M4ConcreteWorld (m t : Nat) where
  neutralToken : Bool
  z : V13M4ConcreteGaugeVector m
  g : V13M4ConcreteGaugeVector m
  bufferLeft : V13M4ConcreteGaugeVector m
  messageBits : V13M4ConcreteMessageVector t
deriving DecidableEq

def v13M4ConcreteWorldEquivTuple (m t : Nat) :
    V13M4ConcreteWorld m t ≃
      Bool × V13M4ConcreteGaugeVector m × V13M4ConcreteGaugeVector m ×
        V13M4ConcreteGaugeVector m × V13M4ConcreteMessageVector t where
  toFun omega :=
    (omega.neutralToken, omega.z, omega.g, omega.bufferLeft, omega.messageBits)
  invFun data :=
    { neutralToken := data.1
      z := data.2.1
      g := data.2.2.1
      bufferLeft := data.2.2.2.1
      messageBits := data.2.2.2.2 }
  left_inv omega := by cases omega; rfl
  right_inv data := by rcases data with ⟨token, z, g, left, message⟩; rfl

noncomputable instance (m t : Nat) : Fintype (V13M4ConcreteWorld m t) :=
  Fintype.ofEquiv
    (Bool × V13M4ConcreteGaugeVector m × V13M4ConcreteGaugeVector m ×
      V13M4ConcreteGaugeVector m × V13M4ConcreteMessageVector t)
    (v13M4ConcreteWorldEquivTuple m t).symm

def v13M4ConcretePublicInput {m t : Nat}
    (omega : V13M4ConcreteWorld m t) : V13M4ConcretePublic m t :=
  ⟨omega.neutralToken⟩

def v13M4ConcreteWitnessOfWorld {m t : Nat}
    (omega : V13M4ConcreteWorld m t) : V13M4ConcreteWitness m t where
  x v := xor (omega.z v) (omega.g v)
  g := omega.g
  z := omega.z
  lockAux i := xor (omega.messageBits i)
    (omega.z (v13M4ConcreteMessageGaugeIndex i))
  bufferAux v :=
    (omega.bufferLeft v, xor (omega.bufferLeft v) (omega.z v))
  localAux := ()
  messageBits := omega.messageBits

def v13M4ConcreteMessage {m t : Nat}
    (W : V13M4ConcreteWitness m t) : List Bool :=
  List.ofFn W.messageBits

/-- Lock constraints are local three-bit XOR constraints.  The lock auxiliary
is existential witness data; this relation does not assert a desired message. -/
def v13M4ConcreteLockPredicate {m t : Nat}
    (_Y : V13M4ConcretePublic m t) (z : V13M4ConcreteGaugeVector m)
    (xi : V13M4ConcreteMessageVector t) (M : List Bool) : Prop :=
  M.length = t + 1 ∧
    forall i : V13M4ConcreteMessageIndex t,
      xi i = xor (M.getD i.val false) (z (v13M4ConcreteMessageGaugeIndex i))

/-- The readout layer checks the same bounded-arity connector from the opposite
direction.  It never compares the message with a public target. -/
def v13M4ConcreteReadoutPredicate {m t : Nat}
    (_Y : V13M4ConcretePublic m t) (z : V13M4ConcreteGaugeVector m)
    (xi : V13M4ConcreteMessageVector t) (M : List Bool) : Prop :=
  M.length = t + 1 ∧
    forall i : V13M4ConcreteMessageIndex t,
      M.getD i.val false = xor (xi i) (z (v13M4ConcreteMessageGaugeIndex i))

/-- Nontrivial positive buffer CSP: `left XOR right = z` at every coordinate. -/
def v13M4ConcreteBufferPredicate {m t : Nat}
    (_Y : V13M4ConcretePublic m t) (z : V13M4ConcreteGaugeVector m)
    (xi : V13M4ConcreteBufferAux m) : Prop :=
  forall v, z v = xor (xi v).1 (xi v).2

def v13M4ConcreteQuotientEquations {m t : Nat}
    (W : V13M4ConcreteWitness m t) : Prop :=
  forall v, W.z v = xor (W.x v) (W.g v)

def v13M4ConcreteVerifier {m t : Nat}
    (Y : V13M4ConcretePublic m t) (W : V13M4ConcreteWitness m t) : Prop :=
  v13M4ConcreteLockPredicate Y W.z W.lockAux (v13M4ConcreteMessage W) ∧
  v13M4ConcreteReadoutPredicate Y W.z W.lockAux (v13M4ConcreteMessage W) ∧
  v13M4ConcreteQuotientEquations W ∧
  v13M4ConcreteBufferPredicate Y W.z W.bufferAux ∧
  True

/-! ## Adaptive prefix and full visible primitive catalog -/

/-- A finite adaptive evidence prefix.  It records the outcomes of every
non-neutral scaffold read: safe-buffer values, raw-gauge values, and quotient
values.  `chargedGaugeSupport` records the union of raw-gauge and quotient
supports exposed by those reads; `bufferVisited` is retained as the dynamic
no-repeat guard used by the execution layer. -/
structure V13M4ConcretePrefix (m : Nat) where
  gaugeObservation : V13M4ConcreteGaugeIndex m -> Option Bool
  quotientObservation : V13M4ConcreteGaugeIndex m -> Option Bool
  bufferObservation : V13M4ConcreteGaugeIndex m -> Option Bool
  bufferVisited : Finset (V13M4ConcreteGaugeIndex m)
  chargedGaugeSupport : Finset (V13M4ConcreteGaugeIndex m)

def v13M4ConcreteObservedSupport {m : Nat}
    (observation : V13M4ConcreteGaugeIndex m -> Option Bool) :
    Finset (V13M4ConcreteGaugeIndex m) :=
  Finset.univ.filter fun v => (observation v).isSome

@[simp] theorem v13M4Concrete_mem_observedSupport {m : Nat}
    (observation : V13M4ConcreteGaugeIndex m -> Option Bool)
    (v : V13M4ConcreteGaugeIndex m) :
    v ∈ v13M4ConcreteObservedSupport observation <->
      (observation v).isSome := by
  simp [v13M4ConcreteObservedSupport]

theorem v13M4Concrete_observedSupport_update_some {m : Nat}
    (observation : V13M4ConcreteGaugeIndex m -> Option Bool)
    (v : V13M4ConcreteGaugeIndex m) (b : Bool) :
    v13M4ConcreteObservedSupport
        (Function.update observation v (some b)) =
      insert v (v13M4ConcreteObservedSupport observation) := by
  ext w
  by_cases hw : w = v
  · subst w
    simp
  · simp [Function.update, hw]

/-- Exact legal-prefix semantics for the scaffold request language.  Every
visited buffer coordinate has one recorded safe value, and the charged gauge
support is exactly the support exposed by raw-gauge and quotient reads.
Public reads need no extra field: their values are determined by the public
instance `Y` already present in `publicPrefixCondition`.

Order is intentionally forgotten.  For this finite scaffold every record
satisfying these support equations is realizable by listing its reads in any
order; the product law depends only on the resulting conditioning event. -/
def v13M4ConcreteLegalPrefix {m : Nat}
    (pref : V13M4ConcretePrefix m) : Prop :=
  pref.bufferVisited =
      v13M4ConcreteObservedSupport pref.bufferObservation ∧
    pref.chargedGaugeSupport =
      v13M4ConcreteObservedSupport pref.gaugeObservation ∪
        v13M4ConcreteObservedSupport pref.quotientObservation

def v13M4ConcretePrefixConsistent {m t : Nat}
    (pref : V13M4ConcretePrefix m) (omega : V13M4ConcreteWorld m t) : Prop :=
  (forall v b, pref.gaugeObservation v = some b -> omega.g v = b) ∧
    (forall v b, pref.quotientObservation v = some b -> omega.z v = b) ∧
      forall v b, pref.bufferObservation v = some b -> omega.bufferLeft v = b

def v13M4ConcreteGaugeSupport {m : Nat}
    (pref : V13M4ConcretePrefix m) : Finset (V13M4ConcreteGaugeIndex m) :=
  pref.chargedGaugeSupport

inductive V13M4ConcretePublicPrimitive (m t : Nat) where
  | geometry
  | neutralToken
  | quotientConstraint : V13M4ConcreteGaugeIndex m ->
      V13M4ConcretePublicPrimitive m t
  | bufferConstraint : V13M4ConcreteGaugeIndex m ->
      V13M4ConcretePublicPrimitive m t
  | lockConstraint : V13M4ConcreteMessageIndex t ->
      V13M4ConcretePublicPrimitive m t
  | readoutConstraint : V13M4ConcreteMessageIndex t ->
      V13M4ConcretePublicPrimitive m t
  | probeDeclaration : V13M4ConcreteGaugeIndex m ->
      V13M4ConcretePublicPrimitive m t
deriving DecidableEq, Fintype, Repr

def v13M4ConcretePrimitiveValue {m t : Nat}
    (primitive : V13M4ConcretePublicPrimitive m t)
    (omega : V13M4ConcreteWorld m t) : Bool :=
  match primitive with
  | .neutralToken => omega.neutralToken
  | _ => true

def v13M4ConcreteDeclaredNeutral {m t : Nat} :
    V13M4ConcretePublicPrimitive m t -> Prop
  | .geometry | .neutralToken | .probeDeclaration _ => True
  | _ => False

def v13M4ConcreteChargedExpansion {m t : Nat} :
    V13M4ConcretePublicPrimitive m t -> Prop
  | .quotientConstraint _ | .bufferConstraint _ |
      .lockConstraint _ | .readoutConstraint _ => True
  | _ => False

/-- Semantic audit predicate: a single visible primitive is an uncharged
target recovery exactly when its Boolean value equals some message coordinate
through a fixed decoder throughout the world space. -/
def v13M4ConcreteRecoversTargetWithoutCharge {m t : Nat}
    (primitive : V13M4ConcretePublicPrimitive m t) : Prop :=
  exists (j : V13M4ConcreteMessageIndex t) (recover : Bool -> Bool),
    forall omega : V13M4ConcreteWorld m t,
      omega.messageBits j = recover (v13M4ConcretePrimitiveValue primitive omega)

/-! ## Finite uniform sampler -/

/-- Uniform law on any nonempty finite type. -/
noncomputable def v13UniformFiniteLaw (Omega : Type) [Fintype Omega]
    [Nonempty Omega] : V13FiniteLaw Omega where
  mass _ := 1 / (Fintype.card Omega : Real)
  mass_nonnegative _ := by positivity
  mass_sum_one := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card Omega : Real) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [nsmul_eq_mul, hcard]

instance (m t : Nat) : Nonempty (V13M4ConcreteWorld m t) :=
  ⟨{
    neutralToken := false
    z := fun _ => false
    g := fun _ => false
    bufferLeft := fun _ => false
    messageBits := fun _ => false
  }⟩

/-! ## Gauge-vector action -/

def v13M4ConcreteWorldGaugeAction {m t : Nat}
    (s : V13M4ConcreteGaugeVector m) (omega : V13M4ConcreteWorld m t) :
    V13M4ConcreteWorld m t :=
  { omega with g := fun v => xor (omega.g v) (s v) }

def v13M4ConcreteWitnessGaugeAction {m t : Nat}
    (s : V13M4ConcreteGaugeVector m) (W : V13M4ConcreteWitness m t) :
    V13M4ConcreteWitness m t :=
  { W with
    x := fun v => xor (W.x v) (s v)
    g := fun v => xor (W.g v) (s v) }

/-- Concrete gauge fibers agree on every non-gauge sampler coordinate. -/
def v13M4ConcreteSameGaugeFiber {m t : Nat}
    (omega omega' : V13M4ConcreteWorld m t) : Prop :=
  omega.neutralToken = omega'.neutralToken ∧
  omega.z = omega'.z ∧
  omega.bufferLeft = omega'.bufferLeft ∧
  omega.messageBits = omega'.messageBits

end Mettapedia.Computability.PNP
