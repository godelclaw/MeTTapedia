import Mettapedia.Languages.MM0.RewriteRung

/-!
# The Peano rewriting rung: recursion equations as conversion over MM0

The bubble here declares six rewrite rules on Peano terms:

| rule | equation | justification in the root |
|---|---|---|
| `addZeroRight` | `a + 0 ↦ a` | the axiom `add0` |
| `addSuccRight` | `a + suc b ↦ suc (a + b)` | the axiom `addS` |
| `addZeroLeft` | `0 + a ↦ a` | the theorem `rung_add_zero_left`, by induction |
| `addSuccLeft` | `suc a + b ↦ suc (a + b)` | the theorem `rung_add_succ_left`, by induction |
| `mulZeroRight` | `a * 0 ↦ 0` | the axiom `mul0` |
| `mulSuccRight` | `a * suc b ↦ a * b + a` | the axiom `mulS` |

The two induction theorems are checked natively in the MM0 file that extends
`peano.mm0`; the Lean table records their statements word for word.

* **Justified** (`peanoJustification`): every rule is the equation of its
  table entry, so the rung theorem of `RewriteRung` applies.
* **Decided** (`conv_iff_norm`): the conversion of the six rules is equality of
  normal forms (`norm`), on open terms too. `normalizes` is the
  resulting checker; it is sound for the root (`normalizes_sound`) and accepts
  exactly the pairs that receipt mode accepts (`normalizes_iff_receipt`).
* **Demos**: `2 + 3 = 5`, `2 * 2 = 4` and `a + 0 = 0 + a` three ways each:
  a witness written directly at the root (`Demo.twoAddThreeDirect`, ...), the
  receipt of a rewriting trace, with its grade (`Demo.twoAddThree_receipt`,
  ...), and the rung, which checks normal forms and builds no certificate
  (`Demo.twoAddThree_rung`, ...).
* **Widening keeps soundness, not decision** (`Wide`). Adding the two left
  multiplication rules `0 * a ↦ 0` and `suc a * b ↦ a * b + b`, justified by
  induction theorems, keeps every conversion sound. It relates two distinct
  normal forms of the six rules, `suc ((a * b + b) + a)` and
  `suc ((a * b + a) + b)` (`Wide.critical_pair`), so the normal-form checker
  is not a decision procedure for the wider bubble.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.PeanoRewriteRung

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.MM0.PeanoEquationalFragment
open Mettapedia.Languages.MM0.RewriteRung
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.FreeConversion
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleElaboration

/-! ## The rules -/

/-- `a + 0 ↦ a`. -/
def addZeroRight : Rule := ⟨1, .add (.var 0) .zero, .var 0⟩
/-- `a + suc b ↦ suc (a + b)`. -/
def addSuccRight : Rule := ⟨2, .add (.var 0) (.succ (.var 1)), .succ (.add (.var 0) (.var 1))⟩
/-- `0 + a ↦ a`. -/
def addZeroLeft : Rule := ⟨1, .add .zero (.var 0), .var 0⟩
/-- `suc a + b ↦ suc (a + b)`. -/
def addSuccLeft : Rule := ⟨2, .add (.succ (.var 0)) (.var 1), .succ (.add (.var 0) (.var 1))⟩
/-- `a * 0 ↦ 0`. -/
def mulZeroRight : Rule := ⟨1, .mul (.var 0) .zero, .zero⟩
/-- `a * suc b ↦ a * b + a`. -/
def mulSuccRight : Rule :=
  ⟨2, .mul (.var 0) (.succ (.var 1)), .add (.mul (.var 0) (.var 1)) (.var 0)⟩
/-- `0 * a ↦ 0`. -/
def mulZeroLeft : Rule := ⟨1, .mul .zero (.var 0), .zero⟩
/-- `suc a * b ↦ a * b + b`. -/
def mulSuccLeft : Rule :=
  ⟨2, .mul (.succ (.var 0)) (.var 1), .add (.mul (.var 0) (.var 1)) (.var 1)⟩

/-- The six rules of the bubble. -/
def peanoRules : List Rule :=
  [addZeroRight, addSuccRight, addZeroLeft, addSuccLeft, mulZeroRight, mulSuccRight]

/-- The table position that justifies each rule. -/
def peanoIndex (rule : Rule) : Nat :=
  if rule = addZeroRight then add0Index
  else if rule = addSuccRight then addSIndex
  else if rule = addZeroLeft then addZeroLeftIndex
  else if rule = addSuccLeft then addSuccLeftIndex
  else if rule = mulZeroRight then mul0Index
  else if rule = mulSuccRight then mulSIndex
  else if rule = mulZeroLeft then mulZeroLeftIndex
  else if rule = mulSuccLeft then mulSuccLeftIndex
  else 0

/-- **Every rule is the equation of its table entry.** -/
def peanoJustification : Justification [] peanoRules where
  index := peanoIndex
  lookup rule member := by
    simp only [peanoRules, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Normal forms -/

section NormalForms

variable {n : Nat}

/-- `x + y` for `y` neither zero nor a successor: the left recursion
equations. -/
def addStuck : PTerm n → PTerm n → PTerm n
  | .zero, y => y
  | .succ x, y => .succ (addStuck x y)
  | x, y => .add x y

/-- The sum of two normal forms. -/
def addN (x : PTerm n) : PTerm n → PTerm n
  | .zero => x
  | .succ y => .succ (addN x y)
  | y => addStuck x y

/-- The product of two normal forms. -/
def mulN (x : PTerm n) : PTerm n → PTerm n
  | .zero => .zero
  | .succ y => addN (mulN x y) x
  | y => .mul x y

/-- The normal form of a term under the six rules. -/
def norm : PTerm n → PTerm n
  | .var i => .var i
  | .zero => .zero
  | .succ t => .succ (norm t)
  | .add t u => addN (norm t) (norm u)
  | .mul t u => mulN (norm t) (norm u)

theorem addN_zero_left : ∀ y : PTerm n, addN .zero y = y
  | .var _ => rfl
  | .zero => rfl
  | .succ y => by simp only [addN, addN_zero_left y]
  | .add _ _ => rfl
  | .mul _ _ => rfl

theorem addN_succ_left (x : PTerm n) : ∀ y : PTerm n, addN (.succ x) y = .succ (addN x y)
  | .var _ => rfl
  | .zero => rfl
  | .succ y => by simp only [addN, addN_succ_left x y]
  | .add _ _ => rfl
  | .mul _ _ => rfl

end NormalForms

/-- **Every step keeps the normal form.** -/
theorem step_norm {n : Nat} : ∀ {t u : PTerm n},
    Step peanoRules t u → norm t = norm u
  | _, _, .root member σ => by
      simp only [peanoRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · exact addN_zero_left _
      · exact addN_succ_left _ _
      · rfl
      · rfl
  | _, _, .succ step => by simp only [norm, step_norm step]
  | _, _, .addLeft _ step => by simp only [norm, step_norm step]
  | _, _, .addRight _ step => by simp only [norm, step_norm step]
  | _, _, .mulLeft _ step => by simp only [norm, step_norm step]
  | _, _, .mulRight _ step => by simp only [norm, step_norm step]

/-- Equality of normal forms, as a global equality. -/
abbrev normEquality : bubbles.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq t u := PLift (norm t = norm u)
  refl _ := ⟨rfl⟩
  symm equal := ⟨equal.down.symm⟩
  trans first second := ⟨first.down.trans second.down⟩

/-- Conversion keeps the normal form. -/
theorem conv_norm {n : Nat} {t u : PTerm n}
    (path : Conv peanoRules t u) : norm t = norm u :=
  (bubbles.sound normEquality (fun step => ⟨step_norm step⟩) path).down

section Reach

variable {n : Nat}

local notation "T" => PTerm n

/-- Two pattern arguments. -/
def pair (x y : T) : Fin 2 → T
  | ⟨0, _⟩ => x
  | _ => y

theorem mem_addZeroRight : addZeroRight ∈ peanoRules := by simp [peanoRules]
theorem mem_addSuccRight : addSuccRight ∈ peanoRules := by simp [peanoRules]
theorem mem_addZeroLeft : addZeroLeft ∈ peanoRules := by simp [peanoRules]
theorem mem_addSuccLeft : addSuccLeft ∈ peanoRules := by simp [peanoRules]
theorem mem_mulZeroRight : mulZeroRight ∈ peanoRules := by simp [peanoRules]
theorem mem_mulSuccRight : mulSuccRight ∈ peanoRules := by simp [peanoRules]

/-- `x + y` converts to the left recursion of `x` against a stuck `y`. -/
def addStuckReach (y : T) : (x : T) → Conv peanoRules (.add x y) (addStuck x y)
  | .zero => .step (Step.root mem_addZeroLeft fun _ => y)
  | .succ x => .trans (.step (Step.root mem_addSuccLeft (pair x y))) (mapSucc (addStuckReach y x))
  | .var i => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.add (.var i) y)
  | .add a b => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.add (.add a b) y)
  | .mul a b => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.add (.mul a b) y)

/-- `x + y` converts to the sum of normal forms. -/
def addReach (x : T) : (y : T) → Conv peanoRules (.add x y) (addN x y)
  | .zero => .step (Step.root mem_addZeroRight fun _ => x)
  | .succ y => .trans (.step (Step.root mem_addSuccRight (pair x y))) (mapSucc (addReach x y))
  | .var i => addStuckReach (.var i) x
  | .add a b => addStuckReach (.add a b) x
  | .mul a b => addStuckReach (.mul a b) x

/-- `x * y` converts to the product of normal forms. -/
def mulReach (x : T) : (y : T) → Conv peanoRules (.mul x y) (mulN x y)
  | .zero => .step (Step.root mem_mulZeroRight fun _ => x)
  | .succ y =>
      .trans (.step (Step.root mem_mulSuccRight (pair x y)))
        (.trans (mapAddLeft x (mulReach x y)) (addReach (mulN x y) x))
  | .var i => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.mul x (.var i))
  | .add a b => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.mul x (.add a b))
  | .mul a b => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.mul x (.mul a b))

/-- **Every term converts to its normal form.** -/
def toNorm : (t : T) → Conv peanoRules t (norm t)
  | .var i => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) (PTerm.var i)
  | .zero => ConversionEvidence.refl (computation := computation bubbles.State
      (bubbles.Step peanoRules)) PTerm.zero
  | .succ t => mapSucc (toNorm t)
  | .add t u =>
      .trans (mapAddLeft u (toNorm t))
        (.trans (mapAddRight (norm t) (toNorm u)) (addReach (norm t) (norm u)))
  | .mul t u =>
      .trans (mapMulLeft u (toNorm t))
        (.trans (mapMulRight (norm t) (toNorm u)) (mulReach (norm t) (norm u)))

end Reach

/-- **The conversion of the six rules is equality of normal forms.** -/
theorem conv_iff_norm {n : Nat} (t u : PTerm n) :
    Nonempty (Conv peanoRules t u) ↔ norm t = norm u := by
  constructor
  · rintro ⟨path⟩
    exact conv_norm path
  · intro equal
    exact ⟨.trans (toNorm t) (.symm (equal ▸ toNorm u))⟩

/-- **The normalizing checker**: accept `t ≡ u` when the normal forms agree. -/
def normalizes {n : Nat} (t u : PTerm n) : Bool :=
  decide (norm t = norm u)

/-- **The rung for the normalizing checker**: an accepted pair is an equation
the root derives. The run builds no certificate. -/
theorem normalizes_sound {n : Nat} {t u : PTerm n}
    (accepted : normalizes t u = true) :
    Derives terms definitions theorems (natContext n) [] (eqn (encode t) (encode u)) :=
  rung_sound_of_nonempty peanoJustification ((conv_iff_norm t u).mpr (of_decide_eq_true accepted))

/-- **The normalizing checker and receipt mode accept the same pairs.** -/
theorem normalizes_iff_receipt {n : Nat}
    (t u : PTerm n) :
    normalizes t u = true ↔
      ∃ path : Conv peanoRules t u,
        ProofWitness.check terms definitions theorems (natContext n) []
          (elaborate peanoJustification path).1 (eqn (encode t) (encode u)) = true := by
  rw [← rung_iff_receipt peanoJustification t u, conv_iff_norm, normalizes, decide_eq_true_iff]

/-- The normalizing checker refuses the lying pair `1 + 0 ≡ 0`. -/
theorem normalizes_refuses_lie :
    normalizes (n := 0) (.add (.succ .zero) .zero) .zero = false := by decide

/-- **Conversion is less than provable equality.** Peano arithmetic proves
`a + b = b + a` (`addcom` in `peano.mm1`), and the equation holds in the
standard model, but the bubble does not convert `a + b` to `b + a`: their
normal forms differ. -/
theorem normalizes_refuses_commutativity :
    normalizes (n := 2) (.add (.var 0) (.var 1)) (.add (.var 1) (.var 0)) = false ∧
      ∀ ρ : Fin 2 → ℕ, (PTerm.add (.var 0) (.var 1) : PTerm 2).value ρ =
        (PTerm.add (.var 1) (.var 0) : PTerm 2).value ρ :=
  ⟨by decide, fun ρ => Nat.add_comm _ _⟩

/-! ## Demos -/

namespace Demo

open PTerm (numeral)

local notation "N" => PTerm 0

/-- `2 + 3`. -/
def twoAddThree : N := .add (numeral 2) (numeral 3)
/-- `2 * 2`. -/
def twoMulTwo : N := .mul (numeral 2) (numeral 2)

/-- A forward trace step. -/
def fwd {n : Nat} (rule : Rule)
    (σ : List (PTerm n))
    (position : List Direction) : TraceStep n :=
  ⟨rule, σ, position, true⟩

/-- A backward trace step. -/
def bwd {n : Nat} (rule : Rule)
    (σ : List (PTerm n))
    (position : List Direction) : TraceStep n :=
  ⟨rule, σ, position, false⟩

/-! ### `2 + 3 = 5` -/

/-- Four rewrites: `addS` three times, then `add0`, each under the successors
already produced. -/
def twoAddThreeTrace : List (TraceStep 0) :=
  [ fwd addSuccRight [numeral 2, numeral 2] [],
    fwd addSuccRight [numeral 2, numeral 1] [.succ],
    fwd addSuccRight [numeral 2, numeral 0] [.succ, .succ],
    fwd addZeroRight [numeral 2] [.succ, .succ, .succ] ]

theorem twoAddThree_accepted : checkTrace peanoRules twoAddThree (numeral 5 : N) twoAddThreeTrace = true := by
  decide

/-- **Receipt mode**: the receipt of the trace. -/
def twoAddThreeReceipt : ProofWitness :=
  traceReceipt peanoJustification twoAddThreeTrace twoAddThree_accepted

theorem twoAddThree_receipt :
    ProofWitness.check terms definitions theorems (natContext 0) [] twoAddThreeReceipt
        (eqn (encode twoAddThree) (encode (numeral 5 : N))) = true ∧
      stepCount (traceConv peanoRules twoAddThreeTrace twoAddThree_accepted) = 4 ∧
      nodeCount twoAddThreeReceipt = 25 :=
  ⟨elaborate_accepted peanoJustification _, stepCount_traceConv _ _ _, by decide +kernel⟩

/-- **The tier-0 witness written directly at the root**: the congruence is
shared along the chain instead of repeated for each step. -/
def twoAddThreeDirect : ProofWitness :=
  let e (t : N) := encode t
  transW (e twoAddThree) (e (.succ (.add (numeral 2) (numeral 2)))) (e (numeral 5))
    (.theoremApp addSIndex [e (numeral 2), e (numeral 2)] [])
    (sucW (e (.add (numeral 2) (numeral 2))) (e (numeral 4))
      (transW (e (.add (numeral 2) (numeral 2))) (e (.succ (.add (numeral 2) (numeral 1))))
        (e (numeral 4))
        (.theoremApp addSIndex [e (numeral 2), e (numeral 1)] [])
        (sucW (e (.add (numeral 2) (numeral 1))) (e (numeral 3))
          (transW (e (.add (numeral 2) (numeral 1))) (e (.succ (.add (numeral 2) (numeral 0))))
            (e (numeral 3))
            (.theoremApp addSIndex [e (numeral 2), e (numeral 0)] [])
            (sucW (e (.add (numeral 2) (numeral 0))) (e (numeral 2))
              (.theoremApp add0Index [e (numeral 2)] []))))))

theorem twoAddThree_direct :
    Checks [] 0 twoAddThreeDirect (eqn (encode twoAddThree) (encode (numeral 5 : N))) ∧
      nodeCount twoAddThreeDirect = 19 := by
  refine ⟨?_, by decide +kernel⟩
  have add0At := checks_instance (extra := []) (index := add0Index)
    (left := addZeroRight.lhs) (right := addZeroRight.rhs) (lookup_add0 []) (n := 0)
  have addSAt := checks_instance (extra := []) (index := addSIndex)
    (left := addSuccRight.lhs) (right := addSuccRight.rhs) (lookup_addS []) (n := 0)
  exact checks_trans (encode_typed _) (encode_typed (.succ (.add (numeral 2) (numeral 2))))
    (encode_typed _) (addSAt (pair (numeral 2) (numeral 2)))
    (checks_suc (encode_typed (.add (numeral 2) (numeral 2))) (encode_typed (numeral 4))
      (checks_trans (encode_typed _) (encode_typed (.succ (.add (numeral 2) (numeral 1))))
        (encode_typed _) (addSAt (pair (numeral 2) (numeral 1)))
        (checks_suc (encode_typed (.add (numeral 2) (numeral 1))) (encode_typed (numeral 3))
          (checks_trans (encode_typed _) (encode_typed (.succ (.add (numeral 2) (numeral 0))))
            (encode_typed _) (addSAt (pair (numeral 2) (numeral 0)))
            (checks_suc (encode_typed (.add (numeral 2) (numeral 0))) (encode_typed (numeral 2))
              (add0At fun _ => numeral 2))))))

/-- **Rung mode**: the normal forms agree; the root derives the equation, and
no certificate is built for this run. -/
theorem twoAddThree_rung :
    normalizes twoAddThree (numeral 5 : N) = true ∧
      Derives terms definitions theorems (natContext 0) [] (eqn (encode twoAddThree) (encode (numeral 5 : N))) :=
  ⟨by decide, normalizes_sound (by decide)⟩

/-! ### `2 * 2 = 4` -/

/-- Seven rewrites: `mulS` twice, `mul0`, the left unit `0 + a ↦ a`, then
`addS` twice and `add0`. -/
def twoMulTwoTrace : List (TraceStep 0) :=
  [ fwd mulSuccRight [numeral 2, numeral 1] [],
    fwd mulSuccRight [numeral 2, numeral 0] [.addLeft],
    fwd mulZeroRight [numeral 2] [.addLeft, .addLeft],
    fwd addZeroLeft [numeral 2] [.addLeft],
    fwd addSuccRight [numeral 2, numeral 1] [],
    fwd addSuccRight [numeral 2, numeral 0] [.succ],
    fwd addZeroRight [numeral 2] [.succ, .succ] ]

theorem twoMulTwo_accepted : checkTrace peanoRules twoMulTwo (numeral 4 : N) twoMulTwoTrace = true := by
  decide

def twoMulTwoReceipt : ProofWitness :=
  traceReceipt peanoJustification twoMulTwoTrace twoMulTwo_accepted

theorem twoMulTwo_receipt :
    ProofWitness.check terms definitions theorems (natContext 0) [] twoMulTwoReceipt
        (eqn (encode twoMulTwo) (encode (numeral 4 : N))) = true ∧
      stepCount (traceConv peanoRules twoMulTwoTrace twoMulTwo_accepted) = 7 ∧
      nodeCount twoMulTwoReceipt = 47 :=
  ⟨elaborate_accepted peanoJustification _, stepCount_traceConv _ _ _, by decide +kernel⟩

/-- `2 * 2 = 4` written directly: `2 * 2 = 2 * 1 + 2 = 2 + 2 = 4`, with
`2 * 1 = 2 * 0 + 2 = 0 + 2 = 2`. -/
def twoMulTwoDirect : ProofWitness :=
  let e (t : N) := encode t
  let two := numeral (n := 0) 2
  let twoTimesOne : N := .mul two (numeral 1)
  let twoTimesZero : N := .mul two (numeral 0)
  let twoTimesOne_eq_two :=
    transW (e twoTimesOne) (e (.add twoTimesZero two)) (e two)
      (.theoremApp mulSIndex [e two, e (numeral 0)] [])
      (transW (e (.add twoTimesZero two)) (e (.add .zero two)) (e two)
        (addW (e twoTimesZero) (e .zero) (e two) (e two)
          (.theoremApp mul0Index [e two] []) (reflW (e two)))
        (.theoremApp addZeroLeftIndex [e two] []))
  let twoAddTwo_eq_four :=
    transW (e (.add two two)) (e (.succ (.add two (numeral 1)))) (e (numeral 4))
      (.theoremApp addSIndex [e two, e (numeral 1)] [])
      (sucW (e (.add two (numeral 1))) (e (numeral 3))
        (transW (e (.add two (numeral 1))) (e (.succ (.add two (numeral 0)))) (e (numeral 3))
          (.theoremApp addSIndex [e two, e (numeral 0)] [])
          (sucW (e (.add two (numeral 0))) (e two) (.theoremApp add0Index [e two] []))))
  transW (e twoMulTwo) (e (.add twoTimesOne two)) (e (numeral 4))
    (.theoremApp mulSIndex [e two, e (numeral 1)] [])
    (transW (e (.add twoTimesOne two)) (e (.add two two)) (e (numeral 4))
      (addW (e twoTimesOne) (e two) (e two) (e two) twoTimesOne_eq_two (reflW (e two)))
      twoAddTwo_eq_four)

theorem twoMulTwo_direct :
    Checks [] 0 twoMulTwoDirect (eqn (encode twoMulTwo) (encode (numeral 4 : N))) ∧
      nodeCount twoMulTwoDirect = 37 := by
  refine ⟨?_, by decide +kernel⟩
  have add0At := checks_instance (extra := []) (index := add0Index)
    (left := addZeroRight.lhs) (right := addZeroRight.rhs) (lookup_add0 []) (n := 0)
  have addSAt := checks_instance (extra := []) (index := addSIndex)
    (left := addSuccRight.lhs) (right := addSuccRight.rhs) (lookup_addS []) (n := 0)
  have addZeroLeftAt := checks_instance (extra := []) (index := addZeroLeftIndex)
    (left := addZeroLeft.lhs) (right := addZeroLeft.rhs) (lookup_addZeroLeft []) (n := 0)
  have mul0At := checks_instance (extra := []) (index := mul0Index)
    (left := mulZeroRight.lhs) (right := mulZeroRight.rhs) (lookup_mul0 []) (n := 0)
  have mulSAt := checks_instance (extra := []) (index := mulSIndex)
    (left := mulSuccRight.lhs) (right := mulSuccRight.rhs) (lookup_mulS []) (n := 0)
  let two := numeral (n := 0) 2
  have typed : ∀ t : N, NatTyped 0 (encode t) := encode_typed
  exact checks_trans (typed _) (typed (.add (.mul two (numeral 1)) two)) (typed _)
    (mulSAt (pair two (numeral 1)))
    (checks_trans (typed _) (typed (.add two two)) (typed _)
      (checks_add (typed (.mul two (numeral 1))) (typed two) (typed two) (typed two)
        (checks_trans (typed _) (typed (.add (.mul two (numeral 0)) two)) (typed two)
          (mulSAt (pair two (numeral 0)))
          (checks_trans (typed _) (typed (.add .zero two)) (typed two)
            (checks_add (typed (.mul two (numeral 0))) (typed .zero) (typed two) (typed two)
              (mul0At fun _ => two) (checks_refl (typed two)))
            (addZeroLeftAt fun _ => two)))
        (checks_refl (typed two)))
      (checks_trans (typed _) (typed (.succ (.add two (numeral 1)))) (typed _)
        (addSAt (pair two (numeral 1)))
        (checks_suc (typed (.add two (numeral 1))) (typed (numeral 3))
          (checks_trans (typed _) (typed (.succ (.add two (numeral 0)))) (typed _)
            (addSAt (pair two (numeral 0)))
            (checks_suc (typed (.add two (numeral 0))) (typed two) (add0At fun _ => two))))))

theorem twoMulTwo_rung :
    normalizes twoMulTwo (numeral 4 : N) = true ∧
      Derives terms definitions theorems (natContext 0) [] (eqn (encode twoMulTwo) (encode (numeral 4 : N))) :=
  ⟨by decide, normalizes_sound (by decide)⟩

/-! ### `a + 0 = 0 + a`, over one variable -/

local notation "V" => PTerm 1

/-- `a + 0`. -/
def addZero : V := .add (.var 0) .zero
/-- `0 + a`. -/
def zeroAdd : V := .add .zero (.var 0)

/-- Two rewrites: `a + 0 ↦ a`, then `0 + a ↦ a` backward. The second rule
needs induction at the root. -/
def addZeroTrace : List (TraceStep 1) :=
  [ fwd addZeroRight [.var 0] [], bwd addZeroLeft [.var 0] [] ]

theorem addZero_accepted : checkTrace peanoRules addZero zeroAdd addZeroTrace = true := by decide

def addZeroReceipt : ProofWitness :=
  traceReceipt peanoJustification addZeroTrace addZero_accepted

theorem addZero_receipt :
    ProofWitness.check terms definitions theorems (natContext 1) [] addZeroReceipt
        (eqn (encode addZero) (encode zeroAdd)) = true ∧
      stepCount (traceConv peanoRules addZeroTrace addZero_accepted) = 2 ∧
      nodeCount addZeroReceipt = 7 :=
  ⟨elaborate_accepted peanoJustification _, stepCount_traceConv _ _ _, by decide +kernel⟩

theorem addZero_rung :
    normalizes addZero zeroAdd = true ∧
      Derives terms definitions theorems (natContext 1) [] (eqn (encode addZero) (encode zeroAdd)) :=
  ⟨by decide, normalizes_sound (by decide)⟩

/-- The four right recursion rules alone. -/
def rightRules : List Rule := [addZeroRight, addSuccRight, mulZeroRight, mulSuccRight]

/-- Sum of normal forms under the right recursion equations alone. -/
def rightAdd {n : Nat} (x : PTerm n) : PTerm n → PTerm n
  | .zero => x
  | .succ y => .succ (rightAdd x y)
  | y => .add x y

/-- Product of normal forms under the right recursion equations alone. -/
def rightMul {n : Nat} (x : PTerm n) : PTerm n → PTerm n
  | .zero => .zero
  | .succ y => rightAdd (rightMul x y) x
  | y => .mul x y

/-- The normal form under the right recursion equations alone. -/
def rightNorm {n : Nat} : PTerm n → PTerm n
  | .var i => .var i
  | .zero => .zero
  | .succ t => .succ (rightNorm t)
  | .add t u => rightAdd (rightNorm t) (rightNorm u)
  | .mul t u => rightMul (rightNorm t) (rightNorm u)

theorem rightStep_norm {n : Nat} :
    ∀ {t u : PTerm n}, Step rightRules t u → rightNorm t = rightNorm u
  | _, _, .root member σ => by
      simp only [rightRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
  | _, _, .succ step => by simp only [rightNorm, rightStep_norm step]
  | _, _, .addLeft _ step => by simp only [rightNorm, rightStep_norm step]
  | _, _, .addRight _ step => by simp only [rightNorm, rightStep_norm step]
  | _, _, .mulLeft _ step => by simp only [rightNorm, rightStep_norm step]
  | _, _, .mulRight _ step => by simp only [rightNorm, rightStep_norm step]

/-- Equality of right normal forms, as a global equality. -/
abbrev rightEquality : bubbles.GlobalEquality.{0, 0, 0, 0, 0} where
  Eq t u := PLift (rightNorm t = rightNorm u)
  refl _ := ⟨rfl⟩
  symm equal := ⟨equal.down.symm⟩
  trans first second := ⟨first.down.trans second.down⟩

/-- **Without the left rules the same pair is not convertible**: the right
recursion equations keep the right normal form, and `a + 0` and `0 + a` have
different ones. -/
theorem addZero_needs_left_rules : ¬ Nonempty (Conv rightRules addZero zeroAdd) := by
  rintro ⟨path⟩
  have kept := (bubbles.sound rightEquality (fun step => ⟨rightStep_norm step⟩) path).down
  exact absurd kept (by decide)

end Demo

/-! ## Widening keeps soundness, not decision -/

namespace Wide

/-- The six rules and the two left multiplication rules. -/
def wideRules : List Rule := peanoRules ++ [mulZeroLeft, mulSuccLeft]

/-- The wider set is justified too: the two new rules by their induction
theorems. -/
def wideJustification : Justification [] wideRules where
  index := peanoIndex
  lookup rule member := by
    simp only [wideRules, peanoRules, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

local notation "W" => PTerm 2

/-- `a * b`, over the variables `a` and `b`. -/
def ab : W := .mul (.var 0) (.var 1)
/-- `suc ((a * b + b) + a)`. -/
def leftSide : W := .succ (.add (.add ab (.var 1)) (.var 0))
/-- `suc ((a * b + a) + b)`. -/
def rightSide : W := .succ (.add (.add ab (.var 0)) (.var 1))

/-- The critical pair of `mulSuccRight` and `mulSuccLeft` at `suc a * suc b`,
joined through it: three rewrites back to the overlap and three forward. -/
def criticalTrace : List (TraceStep 2) :=
  [ Demo.bwd mulSuccLeft [.var 0, .var 1] [.succ, .addLeft],
    Demo.bwd addSuccRight [.mul (.succ (.var 0)) (.var 1), .var 0] [],
    Demo.bwd mulSuccRight [.succ (.var 0), .var 1] [],
    Demo.fwd mulSuccLeft [.var 0, .succ (.var 1)] [],
    Demo.fwd addSuccRight [.mul (.var 0) (.succ (.var 1)), .var 1] [],
    Demo.fwd mulSuccRight [.var 0, .var 1] [.succ, .addLeft] ]

theorem critical_accepted : checkTrace wideRules leftSide rightSide criticalTrace = true := by
  decide

/-- **The wider bubble relates two distinct normal forms of the six rules**:
the trace is accepted and sound for the root, the normalizing checker
refuses the pair, and the two sides agree in the standard model, as every
derived equation must. -/
theorem critical_pair :
    checkTrace wideRules leftSide rightSide criticalTrace = true ∧
      Derives terms definitions theorems (natContext 2) [] (eqn (encode leftSide) (encode rightSide)) ∧
      normalizes leftSide rightSide = false ∧
      ∀ ρ : Fin 2 → ℕ, leftSide.value ρ = rightSide.value ρ := by
  refine ⟨critical_accepted, checkTrace_sound wideJustification _ critical_accepted,
    by decide, ?_⟩
  intro ρ
  exact derives_value (checkTrace_sound wideJustification _ critical_accepted) ρ

/-- The six-rule bubble does not relate the two sides. -/
theorem critical_not_in_six : ¬ Nonempty (Conv peanoRules leftSide rightSide) := by
  rw [conv_iff_norm]
  decide

end Wide

/-! ## Axiom audit -/

#print axioms peanoJustification
#print axioms conv_iff_norm
#print axioms normalizes_sound
#print axioms normalizes_iff_receipt
#print axioms normalizes_refuses_lie
#print axioms normalizes_refuses_commutativity
#print axioms Demo.twoAddThree_receipt
#print axioms Demo.twoAddThree_direct
#print axioms Demo.twoAddThree_rung
#print axioms Demo.twoMulTwo_receipt
#print axioms Demo.twoMulTwo_direct
#print axioms Demo.twoMulTwo_rung
#print axioms Demo.addZero_receipt
#print axioms Demo.addZero_rung
#print axioms Demo.addZero_needs_left_rules
#print axioms Wide.critical_pair
#print axioms Wide.critical_not_in_six

end Mettapedia.Languages.MM0.PeanoRewriteRung
