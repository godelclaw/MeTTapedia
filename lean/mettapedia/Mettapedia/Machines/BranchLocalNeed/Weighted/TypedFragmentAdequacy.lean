import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mettapedia.Machines.BranchLocalNeed.Weighted.WeightedRelNeedModel

/-!
# Typed CBPV Fragment and Core Adequacy Theorems against `CallTimeChoice`

This module defines the typed ground and single-cell CBPV fragments over `CallTimeChoice`
and proves their quantitative adequacy against `CallTimeChoice.Derives` and `CallTimeChoice.Observes`:
1. **Typed Fragment:** Defines ground value types (`GroundTy`), single-cell bodies
   (`NeedScopeComp`), and finite ground producers (`GroundComp`), together with their
   compilation into `CallTimeChoice.Val Nat`, `CallTimeChoice.VExp`, and `CallTimeChoice.Comp`.
2. **Compositional Denotation in `Rel_S`:** Gives the compositional weighted relational
   semantics over any commutative semiring `S`, where `seqBool` composes via the ground
   diagonal comonoid (`GroundComp`) or the pointed `NeedWeb Bool = Option Bool` affine-sharing
   comonoid (`NeedScopeComp`), `choose` is pointwise addition, `fail` is `0`, and `emit`
   preserves answer counts.
3. **Store-Transition Algebra & Operational Adequacy:**
   * Establishes the result-list homomorphisms (`resultSum_append`,
     `resultSum_indicator_eq_values_count`) and the four-branch `NeedCellBehavior` store-threading
     identities (`operationalSeqPending_eq_evalPending_seq`, `seq_toWebFn_eq_needComult_sum`).
   * Proves `GroundComp.derives_groundComp_adequacy` and `GroundComp.derives_groundComp_preserves_cells`:
     every `m : GroundComp G` derives a complete result list `L` under `CallTimeChoice.Derives`
     that preserves the incoming cell array (`r.2.cells = σ.cells`), produces only encoded ground
     values, and has exact multiplicity `(values L).count (encodeVal v) = m.denote Nat v`.
   * Proves the **General Two-Force Memoization Theorem** (`GroundComp.derives_need_doubleBody_adequacy`
     and `GroundComp.derives_need_doubleBody_empty`): for every finite Boolean producer
     `p : GroundComp .bool`, allocating `p.toComp` with `Comp.need` and forcing the cell twice
     via `NeedScopeComp.doubleBody.toComp` derives a complete result list `L` whose successful
     values are all diagonal Boolean pairs and whose counts satisfy
     `(values L).count (encodeVal (a, b)) = if a = b then p.denote Nat a else 0 = denoteNeedClosed Nat (p.denote Nat) doubleBody (a, b)`.
   * Proves the five positive and negative distinguishing controls (`control_need_double_coin`,
     `control_need_double_dupFalse`, `control_need_double_fail`, `control_need_discard_fail`,
     `control_delay_double_dupFalse`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.Weighted

open scoped BigOperators
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-! ## 1. Operational Homomorphisms on `CallTimeChoice` (`resultSum`) -/

/-- Weighted sum over all `(.ok w, σ)` results in a `CallTimeChoice` result list `L : List Result`.
Non-answer outcomes (`.fail`, `.blackhole`) contribute `0`. -/
def resultSum (L : List Result) (f : Val Nat → Store → Nat) : Nat :=
  (L.filterMap fun r =>
    match r.1 with
    | .ok w => some (f w r.2)
    | _ => none).sum

@[simp]
theorem resultSum_nil (f : Val Nat → Store → Nat) : resultSum [] f = 0 := rfl

@[simp]
theorem resultSum_ok (w : Val Nat) (σ : Store) (rest : List Result)
    (f : Val Nat → Store → Nat) :
    resultSum ((.ok w, σ) :: rest) f = f w σ + resultSum rest f := rfl

@[simp]
theorem resultSum_fail (σ : Store) (rest : List Result) (f : Val Nat → Store → Nat) :
    resultSum ((.fail, σ) :: rest) f = resultSum rest f := rfl

@[simp]
theorem resultSum_blackhole (σ : Store) (rest : List Result) (f : Val Nat → Store → Nat) :
    resultSum ((.blackhole, σ) :: rest) f = resultSum rest f := rfl

@[simp]
theorem resultSum_append (L₁ L₂ : List Result) (f : Val Nat → Store → Nat) :
    resultSum (L₁ ++ L₂) f = resultSum L₁ f + resultSum L₂ f := by
  unfold resultSum
  rw [List.filterMap_append, List.sum_append]

theorem resultSum_add (L : List Result) (f g : Val Nat → Store → Nat) :
    resultSum L (fun w σ => f w σ + g w σ) = resultSum L f + resultSum L g := by
  induction L with
  | nil => rfl
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      cases o with
      | ok w =>
          simp only [resultSum_ok, ih]
          omega
      | fail => exact ih
      | blackhole => exact ih

theorem resultSum_mul_const (L : List Result) (f : Val Nat → Store → Nat) (c : Nat) :
    resultSum L (fun w σ => f w σ * c) = resultSum L f * c := by
  induction L with
  | nil => simp [resultSum]
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      cases o with
      | ok w =>
          simp only [resultSum_ok, ih, Nat.add_mul]
      | fail => exact ih
      | blackhole => exact ih

/-- Exact connection between `resultSum` and `(values L).count v`:
summing the indicator `(if w = v then 1 else 0)` over `L` equals the exact
multiplicity of `v` in `values L`. -/
theorem resultSum_indicator_eq_values_count (L : List Result) (v : Val Nat) :
    resultSum L (fun w _ => if w = v then 1 else 0) = (values L).count v := by
  induction L with
  | nil => rfl
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      cases o with
      | ok w =>
          simp only [resultSum_ok, values, List.filterMap_cons, List.count_cons, ih]
          by_cases h : w = v
          · subst h
            simp [Nat.add_comm]
          · simp [h, beq_iff_eq]
      | fail =>
          simp only [resultSum_fail, values, List.filterMap_cons, ih]
      | blackhole =>
          simp only [resultSum_blackhole, values, List.filterMap_cons, ih]

@[simp]
theorem values_append (L₁ L₂ : List Result) :
    values (L₁ ++ L₂) = values L₁ ++ values L₂ := by
  unfold values
  rw [List.filterMap_append]

/-! ## 2. The Store-Transition Bijection for `NeedWeb` (Task 4 Core Bridge) -/

/-- A store-indexed behavior with respect to a memoized cell `ℓ` over a finite carrier `A`:
* `onUnforced : Nat` is the multiplicity of outcomes along paths that do **not** force `ℓ`
  (so a `.pending` cell at `ℓ` remains `.pending`);
* `onForced : A → Nat` is the multiplicity of outcomes along paths that **do** force `ℓ`
  and observe cached value `a`. -/
structure NeedCellBehavior (A : Type*) [Fintype A] [DecidableEq A] where
  onUnforced : Nat
  onForced : A → Nat

namespace NeedCellBehavior

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- View `NeedCellBehavior A` as a function on `Option A` (`NeedWeb A`). -/
def toWebFn (B : NeedCellBehavior A) : Option A → Nat
  | none => B.onUnforced
  | some a => B.onForced a

/-- When cell `ℓ` is initially `.pending` with producer distribution `w_c : A → Nat`,
the total answer count of a computation with behavior `B` is:
`B.onUnforced` (from paths that never force `ℓ`) plus `∑ a, w_c a * B.onForced a`
(from paths that force `ℓ`, triggering the producer once and caching `a`). -/
def evalPending (w_c : A → Nat) (B : NeedCellBehavior A) : Nat :=
  B.onUnforced + ∑ a : A, w_c a * B.onForced a

/-- When cell `ℓ` is already `.done a`, forcing `ℓ` returns `a` deterministically
without re-running the producer, so the total answer count is `B.onForced a + B.onUnforced`. -/
def evalDone (a : A) (B : NeedCellBehavior A) : Nat :=
  B.onForced a + B.onUnforced

/-- Sequential composition of two `NeedCellBehavior`s via `needComult`:
* `onUnforced = B₁.onUnforced * B₂.onUnforced` (`(none, none)`);
* `onForced a = B₁.onForced a * B₂.onForced a + B₁.onForced a * B₂.onUnforced + B₁.onUnforced * B₂.onForced a`
  (`(some a, some a) + (some a, none) + (none, some a)`). -/
def seq (B₁ B₂ : NeedCellBehavior A) : NeedCellBehavior A where
  onUnforced := B₁.onUnforced * B₂.onUnforced
  onForced a :=
    B₁.onForced a * B₂.onForced a +
    B₁.onForced a * B₂.onUnforced +
    B₁.onUnforced * B₂.onForced a

/-- Operational store-threading across `seq`:
In stage 1 (`B₁`), starting from `.pending`:
* Unforced paths (`B₁.onUnforced`) leave the cell `.pending`, so stage 2 (`B₂`) runs in
  `.pending` and produces `B₂.evalPending w_c`.
* Forced paths for `a` (`w_c a * B₁.onForced a`) update the cell to `.done a`, so stage 2 (`B₂`)
  runs in `.done a` and produces `B₂.evalDone a`. -/
def operationalSeqPending (w_c : A → Nat) (B₁ B₂ : NeedCellBehavior A) : Nat :=
  B₁.onUnforced * B₂.evalPending w_c +
    ∑ a : A, (w_c a * B₁.onForced a) * B₂.evalDone a

/-- **The Store-Transition Bijection Theorem (Task 4 Core Bridge):**
Operational store-threading of a `.pending` cell across `seq` (`operationalSeqPending`)
equals the `NeedWeb` comonoid composition `(B₁.seq B₂).evalPending w_c`! -/
theorem operationalSeqPending_eq_evalPending_seq
    (w_c : A → Nat) (B₁ B₂ : NeedCellBehavior A) :
    operationalSeqPending w_c B₁ B₂ = (B₁.seq B₂).evalPending w_c := by
  unfold operationalSeqPending evalPending evalDone seq
  simp only [Nat.mul_add, Finset.mul_sum]
  rw [Nat.add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : B₁.onUnforced * (w_c a * B₂.onForced a) = w_c a * B₁.onUnforced * B₂.onForced a := by
    rw [← Nat.mul_assoc, Nat.mul_comm B₁.onUnforced (w_c a)]
  have h2 : w_c a * (B₁.onForced a * B₂.onForced a) = w_c a * B₁.onForced a * B₂.onForced a :=
    (Nat.mul_assoc _ _ _).symm
  have h3 : w_c a * (B₁.onForced a * B₂.onUnforced) = w_c a * B₁.onForced a * B₂.onUnforced :=
    (Nat.mul_assoc _ _ _).symm
  have h4 : w_c a * (B₁.onUnforced * B₂.onForced a) = w_c a * B₁.onUnforced * B₂.onForced a :=
    (Nat.mul_assoc _ _ _).symm
  rw [h1, h2, h3, h4]
  omega

/-- Moreover, `(B₁.seq B₂).toWebFn u` is literally the `Rel_ℕ` convolution of
`B₁.toWebFn` and `B₂.toWebFn` against `needComult` from `WeightedRelNeedModel`! -/
theorem seq_toWebFn_eq_needComult_sum (B₁ B₂ : NeedCellBehavior A) (u : NeedWeb A) :
    (B₁.seq B₂).toWebFn u =
      ∑ u₁ : NeedWeb A, ∑ u₂ : NeedWeb A,
        needComult u (u₁, u₂) * B₁.toWebFn u₁ * B₂.toWebFn u₂ := by
  cases u with
  | none =>
      rw [Fintype.sum_option, Fintype.sum_option]
      simp [toWebFn, seq, needComult]
  | some a =>
      have h_inner (u₁ : Option A) :
          (∑ u₂ : Option A,
            needComult (some a) (u₁, u₂) * B₁.toWebFn u₁ * B₂.toWebFn u₂) =
          match u₁ with
          | none => B₁.onUnforced * B₂.onForced a
          | some a₁ =>
              if a₁ = a then
                B₁.onForced a * B₂.onUnforced + B₁.onForced a * B₂.onForced a
              else 0 := by
        cases u₁ with
        | none =>
            rw [Fintype.sum_option]
            simp [toWebFn, needComult]
        | some a₁ =>
            rw [Fintype.sum_option]
            by_cases h : a₁ = a
            · subst h; simp [toWebFn, needComult]
            · simp [h, toWebFn, needComult]
      simp_rw [h_inner]
      rw [Fintype.sum_option]
      simp [toWebFn, seq]
      omega

end NeedCellBehavior

/-! ## 3. Typed CBPV Fragment and Value Encoding (Task 2 & Task 3) -/

/-- Constructor symbol names in `CallTimeChoice` (avoiding `0 = normHead`):
* `1`: `Unit`
* `2`: `False`
* `3`: `True`
* `4`: `Pair` -/
def symUnit : Nat := 1
def symFalse : Nat := 2
def symTrue : Nat := 3
def symPair : Nat := 4

/-- Base ground types for the first-order typed CBPV fragment. -/
inductive GroundTy where
  | unit
  | bool
  | pair (left right : GroundTy)
  deriving DecidableEq, Repr

namespace GroundTy

/-- Set-based carrier (web) of a ground type. -/
@[reducible]
def Web : GroundTy → Type
  | .unit => Unit
  | .bool => Bool
  | .pair G₁ G₂ => Web G₁ × Web G₂

@[reducible]
instance instFintypeWeb : (G : GroundTy) → Fintype (Web G)
  | .unit => inferInstanceAs (Fintype Unit)
  | .bool => inferInstanceAs (Fintype Bool)
  | .pair G₁ G₂ => @instFintypeProd (Web G₁) (Web G₂) (instFintypeWeb G₁) (instFintypeWeb G₂)

@[reducible]
instance instDecidableEqWeb : (G : GroundTy) → DecidableEq (Web G)
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .pair G₁ G₂ => @instDecidableEqProd (Web G₁) (Web G₂) (instDecidableEqWeb G₁) (instDecidableEqWeb G₂)

/-- Encode an element of `G.Web` into a closed `CallTimeChoice.VExp`. -/
def encodeVExp : {G : GroundTy} → G.Web → VExp
  | .unit, () => .sym symUnit
  | .bool, false => .sym symFalse
  | .bool, true => .sym symTrue
  | .pair _ _, (x, y) => .app (.app (.sym symPair) (encodeVExp x)) (encodeVExp y)

/-- Encode an element of `G.Web` into a runtime `CallTimeChoice.Val Nat`. -/
def encodeVal : {G : GroundTy} → G.Web → Val Nat
  | .unit, () => .sym symUnit
  | .bool, false => .sym symFalse
  | .bool, true => .sym symTrue
  | .pair _ _, (x, y) => .app (.app (.sym symPair) (encodeVal x)) (encodeVal y)

/-- Encoded ground values contain no suspension or code-cell identities. -/
@[simp] theorem encodeVal_cellFree {G : GroundTy} (value : G.Web) :
    (encodeVal value).cellFree = true := by
  induction G with
  | unit => cases value; rfl
  | bool => cases value <;> rfl
  | pair left right leftIH rightIH =>
      rcases value with ⟨first, second⟩
      simp [encodeVal, Val.cellFree, leftIH, rightIH]

@[simp]
theorem eval_encodeVExp {G : GroundTy} (v : G.Web) (ρ : List (Val Nat)) :
    (encodeVExp v).eval ρ = encodeVal v := by
  induction G with
  | unit => cases v; rfl
  | bool => cases v <;> rfl
  | pair G₁ G₂ ih₁ ih₂ =>
      rcases v with ⟨x, y⟩
      simp [encodeVExp, encodeVal, VExp.eval, ih₁, ih₂]

theorem encodeVal_injective : {G : GroundTy} → Function.Injective (@encodeVal G)
  | .unit, (), (), _ => rfl
  | .bool, false, false, _ => rfl
  | .bool, false, true, h => by cases h
  | .bool, true, false, h => by cases h
  | .bool, true, true, _ => rfl
  | .pair G₁ G₂, (x₁, y₁), (x₂, y₂), h => by
      injection h with hf hy
      injection hf with _ hx
      rw [encodeVal_injective hx, encodeVal_injective hy]

end GroundTy

/-! ## 4. Exact Operational Adequacy for Real `.need` Cells in `CallTimeChoice` (Task 4) -/

/-- A syntactic body over a single real memoized cell `c` (bound by `Comp.need` in
`CallTimeChoice`), supporting:
* `ret v`: return ground value `v` (does not force `c`),
* `force`: execute `Comp.force` on the `need` cell `c`,
* `seqBool b₁ k`: execute `b₁` then `k` on the returned boolean value,
* `choose b₁ b₂`: nondeterministic branch,
* `fail`: failure,
* `emit e b`: emit event `e` and continue with `b`. -/
inductive NeedScopeComp : GroundTy → Type where
  | ret {G : GroundTy} (v : G.Web) : NeedScopeComp G
  | force : NeedScopeComp .bool
  | choose {G : GroundTy} (b₁ b₂ : NeedScopeComp G) : NeedScopeComp G
  | fail {G : GroundTy} : NeedScopeComp G
  | emit {G : GroundTy} (e : Nat) (b : NeedScopeComp G) : NeedScopeComp G
  | seqBool {G : GroundTy} (b₁ : NeedScopeComp .bool) (k : Bool → NeedScopeComp G) : NeedScopeComp G

namespace NeedScopeComp

/-- Compile `NeedScopeComp G` into a real `CallTimeChoice.Comp` where the bound
`.need` cell is at de Bruijn index `depth` in the runtime environment `ρ`.
Each enclosing `seqBool` binds one ground value at index `0`, shifting the `.need`
cell to index `depth + 1`. -/
def toCompAt : {G : GroundTy} → NeedScopeComp G → Nat → Comp
  | _, .ret v, _ => .ret (GroundTy.encodeVExp v)
  | _, .force, depth => .force (.var depth)
  | _, .choose b₁ b₂, depth => .choose (toCompAt b₁ depth) (toCompAt b₂ depth)
  | _, .fail, _ => .fail
  | _, .emit e b, depth => .emit e (toCompAt b depth)
  | _, .seqBool b₁ k, depth =>
      .seq (toCompAt b₁ depth)
        (.caseCon (.var 0) symFalse 0 (toCompAt (k false) (depth + 1))
          (.caseCon (.var 0) symTrue 0 (toCompAt (k true) (depth + 1)) .fail))

/-- Top-level compilation of `NeedScopeComp G` inside `Comp.need producer (body.toComp)`:
immediately inside `Comp.need`, the newly allocated `.need` cell is at de Bruijn index `0`. -/
def toComp {G : GroundTy} (b : NeedScopeComp G) : Comp :=
  b.toCompAt 0

/-- Compositional `Rel_S` interpretation of `NeedScopeComp G` as a weighted relation
`WRel S (NeedWeb Bool) G.Web`, defined directly through `needCounit`, `forceNeedRel`,
and `needComult` from `WeightedRelNeedModel`. -/
def denoteRel (S : Type*) [CommSemiring S] :
    {G : GroundTy} → NeedScopeComp G → WRel S (NeedWeb Bool) G.Web
  | G, .ret v => fun u out =>
      letI : DecidableEq G.Web := GroundTy.instDecidableEqWeb G
      needCounit u * (if v = out then 1 else 0)
  | .bool, .force => forceNeedRel
  | _, .choose b₁ b₂ => fun u out =>
      denoteRel S b₁ u out + denoteRel S b₂ u out
  | _, .fail => fun _ _ => 0
  | _, .emit _ b => denoteRel S b
  | _, .seqBool b₁ k => fun u out =>
      ∑ u₁ : NeedWeb Bool, ∑ u₂ : NeedWeb Bool, ∑ mid : Bool,
        needComult u (u₁, u₂) *
        denoteRel S b₁ u₁ mid * denoteRel S (k mid) u₂ out

/-- Compositional `Rel_S` denotation of `Comp.need producer body.toComp`
for a producer with weight distribution `w_c : WState S Bool`:
sums over `u : NeedWeb Bool` (`none` with weight `1`, `some a` with weight `w_c a`),
matching `bindNeed w_c (denoteRel S body)`. -/
def denoteNeedClosed (S : Type*) [CommSemiring S] {G : GroundTy}
    (w_c : WState S Bool) (body : NeedScopeComp G) (out : G.Web) : S :=
  denoteRel S body none out + ∑ a : Bool, w_c a * denoteRel S body (some a) out

/-- Exact agreement between `denoteNeedClosed` and `bindNeed` from `WeightedRelNeedModel`. -/
theorem denoteNeedClosed_eq_bindNeed (S : Type*) [CommSemiring S] {G : GroundTy}
    (w_c : WState S Bool) (body : NeedScopeComp G) (out : G.Web) :
    denoteNeedClosed S w_c body out = bindNeed w_c (denoteRel S body) out := by
  unfold denoteNeedClosed bindNeed
  exact add_comm _ _

/-! ### Canonical Typed Benchmark Programs in `NeedScopeComp` -/

/-- `doubleBody`: forces the `need` cell twice and returns `Pair x y`. -/
def doubleBody : NeedScopeComp (.pair .bool .bool) :=
  .seqBool .force (fun x =>
    .seqBool .force (fun y =>
      .ret (x, y)))

/-- `discardBody`: ignores the `need` cell and returns `false`. -/
def discardBody : NeedScopeComp .bool :=
  .ret false

/-- `forceOnceBody`: forces the `need` cell once and returns its value. -/
def forceOnceBody : NeedScopeComp .bool :=
  .force

/-- `branchAsymBody`: one branch forces the `need` cell, the other branch ignores it
and returns `false`. -/
def branchAsymBody : NeedScopeComp .bool :=
  .choose .force (.ret false)

/-- `coinComp`: `choose (ret False) (ret True)` in `CallTimeChoice`. -/
def coinComp : Comp :=
  .choose (.ret (.sym symFalse)) (.ret (.sym symTrue))

/-- `wCoinNat`: the `Rel_ℕ` state of `coinComp` (`false ↦ 1, true ↦ 1`). -/
def wCoinNat : Bool → Nat := fun _ => 1

/-- `wFailNat`: the `Rel_ℕ` state of `Comp.fail` (`false ↦ 0, true ↦ 0`). -/
def wFailNat : Bool → Nat := fun _ => 0

/-- `wTwoFalseOneTrue`: a producer with multiplicity `2` for `false` and `1` for `true`
(e.g. a 3-clause rule call). -/
def wTwoFalseOneTrue : Bool → Nat
  | false => 2
  | true => 1

/-! ### Core Adequacy Theorems Against `CallTimeChoice.run`, `Derives`, and `Observes` (Task 4) -/

/-- **Adequacy Theorem 1 (Shared Double Force / Call-Time Choice under `Observes`):**
For `Comp.need coinComp doubleBody.toComp`, `CallTimeChoice.Observes` derives a
complete result list `L` whose multiplicities agree with the compositional `Rel_ℕ`
denotation `denoteNeedClosed Nat wCoinNat doubleBody p` for EVERY pair `p : Bool × Bool`:
* `(false, false)` has count `1`,
* `(true, true)` has count `1`,
* `(false, true)` and `(true, false)` have count `0`. -/
theorem observes_doubleCoin_need :
    ∃ L : List Result,
      Observes [] (.need coinComp doubleBody.toComp) L ∧
      (∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          denoteNeedClosed Nat wCoinNat doubleBody p) ∧
      denoteNeedClosed Nat wCoinNat doubleBody (false, false) = 1 ∧
      denoteNeedClosed Nat wCoinNat doubleBody (true, true) = 1 ∧
      denoteNeedClosed Nat wCoinNat doubleBody (false, true) = 0 ∧
      denoteNeedClosed Nat wCoinNat doubleBody (true, false) = 0 := by
  have hobs : observeValues [] 40 (.need coinComp doubleBody.toComp) =
      some [GroundTy.encodeVal (G := .pair .bool .bool) (false, false),
            GroundTy.encodeVal (G := .pair .bool .bool) (true, true)] := by
    decide
  obtain ⟨L, hL, hvals⟩ := observeValues_sound hobs
  refine ⟨L, hL, ?_, by decide, by decide, by decide, by decide⟩
  rintro ⟨b₁, b₂⟩
  rw [hvals]
  cases b₁ <;> cases b₂ <;> decide

/-- **Adequacy Theorem 2 (Laziness / Unused Failing Cell under `Observes`):**
For `Comp.need .fail discardBody.toComp`, `CallTimeChoice.Observes` derives a
complete result list `L` whose multiplicities equal `denoteNeedClosed Nat wFailNat discardBody b`
(`false ↦ 1, true ↦ 0`). -/
theorem observes_discardFail_need :
    ∃ L : List Result,
      Observes [] (.need .fail discardBody.toComp) L ∧
      (∀ b : Bool,
        (values L).count (GroundTy.encodeVal (G := .bool) b) =
          denoteNeedClosed Nat wFailNat discardBody b) ∧
      denoteNeedClosed Nat wFailNat discardBody false = 1 ∧
      denoteNeedClosed Nat wFailNat discardBody true = 0 := by
  have hobs : observeValues [] 40 (.need .fail discardBody.toComp) =
      some [GroundTy.encodeVal (G := .bool) false] := by
    decide
  obtain ⟨L, hL, hvals⟩ := observeValues_sound hobs
  refine ⟨L, hL, ?_, by decide, by decide⟩
  intro b
  rw [hvals]
  cases b <;> decide

/-- **Adequacy Theorem 3 (Asymmetric Branching: Forced on One Branch, Ignored on Another):**
For `Comp.need coinComp branchAsymBody.toComp` (`choose (force c) (ret False)`),
the `none` component of `NeedWeb Bool` contributes `1` to `false` (from the unforced right branch),
while the `some a` components contribute `1` to `false` and `1` to `true` (from the forced left branch),
predicting the exact operational counts `false ↦ 2, true ↦ 1`! -/
theorem observes_branchAsym_need :
    ∃ L : List Result,
      Observes [] (.need coinComp branchAsymBody.toComp) L ∧
      (∀ b : Bool,
        (values L).count (GroundTy.encodeVal (G := .bool) b) =
          denoteNeedClosed Nat wCoinNat branchAsymBody b) ∧
      denoteNeedClosed Nat wCoinNat branchAsymBody false = 2 ∧
      denoteNeedClosed Nat wCoinNat branchAsymBody true = 1 := by
  have hobs : observeValues [] 40 (.need coinComp branchAsymBody.toComp) =
      some [GroundTy.encodeVal (G := .bool) false,
            GroundTy.encodeVal (G := .bool) true,
            GroundTy.encodeVal (G := .bool) false] := by
    decide
  obtain ⟨L, hL, hvals⟩ := observeValues_sound hobs
  refine ⟨L, hL, ?_, by decide, by decide⟩
  intro b
  rw [hvals]
  cases b <;> decide

/-- **Adequacy Theorem 4 (Multi-Clause Program Dispatch + Call-Time Choice):**
Consider a 3-rule program `progTwoFalseOneTrue` for rule head `1` (`pick/0`, avoiding `0 = normHead`):
* Rule 1: `pick() = ret False`
* Rule 2: `pick() = ret False` (duplicate rule! Counts with multiplicity 2)
* Rule 3: `pick() = ret True`
When bound in `need (.call 1 []) doubleBody.toComp`, the compositional `Rel_ℕ` model
predicts `(false, false) ↦ 2`, `(true, true) ↦ 1`, `(false, true) ↦ 0`, `(true, false) ↦ 0`,
matching `CallTimeChoice.Observes`! -/
def progTwoFalseOneTrue : Program :=
  [ { head := 1, arity := 0, body := .ret (.sym symFalse) },
    { head := 1, arity := 0, body := .ret (.sym symFalse) },
    { head := 1, arity := 0, body := .ret (.sym symTrue) } ]

theorem observes_multiClauseCall_need :
    ∃ L : List Result,
      Observes progTwoFalseOneTrue (.need (.call 1 []) doubleBody.toComp) L ∧
      (∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          denoteNeedClosed Nat wTwoFalseOneTrue doubleBody p) ∧
      denoteNeedClosed Nat wTwoFalseOneTrue doubleBody (false, false) = 2 ∧
      denoteNeedClosed Nat wTwoFalseOneTrue doubleBody (true, true) = 1 ∧
      denoteNeedClosed Nat wTwoFalseOneTrue doubleBody (false, true) = 0 ∧
      denoteNeedClosed Nat wTwoFalseOneTrue doubleBody (true, false) = 0 := by
  have hobs : observeValues progTwoFalseOneTrue 40 (.need (.call 1 []) doubleBody.toComp) =
      some [GroundTy.encodeVal (G := .pair .bool .bool) (false, false),
            GroundTy.encodeVal (G := .pair .bool .bool) (false, false),
            GroundTy.encodeVal (G := .pair .bool .bool) (true, true)] := by
    decide
  obtain ⟨L, hL, hvals⟩ := observeValues_sound hobs
  refine ⟨L, hL, ?_, by decide, by decide, by decide, by decide⟩
  rintro ⟨b₁, b₂⟩
  rw [hvals]
  cases b₁ <;> cases b₂ <;> decide

end NeedScopeComp

/-! ## 5. General Structural Adequacy of `GroundComp` Against `CallTimeChoice.Derives` -/

/-- A closed ground CBPV computation over `GroundTy`, supporting `ret`, `choose`, `fail`,
`emit`, `caseBool`, and `seqBool`. -/
inductive GroundComp : GroundTy → Type where
  | ret {G : GroundTy} (v : G.Web) : GroundComp G
  | choose {G : GroundTy} (m₁ m₂ : GroundComp G) : GroundComp G
  | fail {G : GroundTy} : GroundComp G
  | emit {G : GroundTy} (e : Nat) (m : GroundComp G) : GroundComp G
  | caseBool {G : GroundTy} (b : Bool) (mFalse mTrue : GroundComp G) : GroundComp G
  | seqBool {G : GroundTy} (m₁ : GroundComp .bool) (k : Bool → GroundComp G) : GroundComp G

namespace GroundComp

/-- Compositional `Rel_S` denotation of `GroundComp`. -/
def denote (S : Type*) [CommSemiring S] : {G : GroundTy} → GroundComp G → (G.Web → S)
  | _, .ret v => fun b => if v = b then 1 else 0
  | _, .choose m₁ m₂ => fun b => denote S m₁ b + denote S m₂ b
  | _, .fail => fun _ => 0
  | _, .emit _ m => denote S m
  | _, .caseBool b mFalse mTrue => if b then denote S mTrue else denote S mFalse
  | _, .seqBool m₁ k => fun b =>
      denote S m₁ false * denote S (k false) b +
      denote S m₁ true * denote S (k true) b

/-- Compile `GroundComp G` to `CallTimeChoice.Comp`. -/
def toComp : {G : GroundTy} → GroundComp G → Comp
  | _, .ret v => .ret (GroundTy.encodeVExp v)
  | _, .choose m₁ m₂ => .choose (toComp m₁) (toComp m₂)
  | _, .fail => .fail
  | _, .emit e m => .emit e (toComp m)
  | _, .caseBool b mFalse mTrue =>
      .caseCon (GroundTy.encodeVExp (G := .bool) b) symFalse 0 (toComp mFalse)
        (.caseCon (GroundTy.encodeVExp (G := .bool) b) symTrue 0 (toComp mTrue) .fail)
  | _, .seqBool m₁ k =>
      .seq (toComp m₁)
        (.caseCon (.var 0) symFalse 0 (toComp (k false))
          (.caseCon (.var 0) symTrue 0 (toComp (k true)) .fail))

/-- Helper lemma: `seqK` over a list `L₁` where every result has cell array `cells₀`
and every `.ok w` is either `encodeVal false` or `encodeVal true` derives a result list `L`
whose stores preserve `cells₀`, whose values are all encoded ground values, and whose counts
equal the linear combination of the continuation counts. -/
theorem derives_seqK_bool {P : Program} {G : GroundTy} (k : Bool → GroundComp G)
    (cells₀ : List Suspension) (ρ : List (Val Nat)) (L₁ : List Result)
    (hCells₁ : ∀ r ∈ L₁, r.2.cells = cells₀)
    (hL₁ : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
      w = GroundTy.encodeVal (G := .bool) false ∨
      w = GroundTy.encodeVal (G := .bool) true)
    (ihk : ∀ (b : Bool) (σ : Store) (ρ' : List (Val Nat)),
      ∃ L, Derives P (.eval σ ρ' (k b).toComp) L ∧
        (∀ r ∈ L, r.2.cells = σ.cells) ∧
        (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
        (∀ v : G.Web, (values L).count (GroundTy.encodeVal v) = (k b).denote Nat v)) :
    ∃ L,
      Derives P
        (.seqK
          (.caseCon (.var 0) symFalse 0 (k false).toComp
            (.caseCon (.var 0) symTrue 0 (k true).toComp .fail))
          ρ L₁)
        L ∧
      (∀ r ∈ L, r.2.cells = cells₀) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          (values L₁).count (GroundTy.encodeVal (G := .bool) false) * (k false).denote Nat v +
          (values L₁).count (GroundTy.encodeVal (G := .bool) true) * (k true).denote Nat v) := by
  induction L₁ with
  | nil =>
      refine ⟨[], .seqKNil, ?_, ?_, ?_⟩
      · intro r hr; cases hr
      · intro r hr; cases hr
      · intro v
        simp [values]
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      have hCells_rest : ∀ r ∈ rest, r.2.cells = cells₀ :=
        fun r hr => hCells₁ r (List.mem_cons_of_mem _ hr)
      have hrest : ∀ r ∈ rest, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true :=
        fun r hr => hL₁ r (List.mem_cons_of_mem _ hr)
      obtain ⟨L_rest, hDer_rest, hCells_Lrest, hEx_rest, hCount_rest⟩ := ih hCells_rest hrest
      have hσ_cells : σ.cells = cells₀ := hCells₁ (o, σ) List.mem_cons_self
      cases o with
      | fail =>
          refine ⟨(.fail, σ) :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hσ_cells
            · exact hCells_Lrest r hr'
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hEx_rest r hr' w hw
          · intro v
            simpa [values] using hCount_rest v
      | blackhole =>
          refine ⟨(.blackhole, σ) :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hσ_cells
            · exact hCells_Lrest r hr'
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hEx_rest r hr' w hw
          · intro v
            simpa [values] using hCount_rest v
      | ok w =>
          have hw := hL₁ (.ok w, σ) List.mem_cons_self w rfl
          rcases hw with rfl | rfl
          · obtain ⟨L_f, hDer_f, hCells_f, hEx_f, hCount_f⟩ :=
              ihk false σ (GroundTy.encodeVal (G := .bool) false :: ρ)
            have hHit :
                Derives P
                  (.eval σ (GroundTy.encodeVal (G := .bool) false :: ρ)
                    (.caseCon (.var 0) symFalse 0 (k false).toComp
                      (.caseCon (.var 0) symTrue 0 (k true).toComp .fail)))
                  L_f := .caseConHit (args := []) rfl hDer_f
            refine ⟨L_f ++ L_rest, .seqKOk hHit hDer_rest, ?_, ?_, ?_⟩
            · intro r hr
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · rw [hCells_f r hr₁, hσ_cells]
              · exact hCells_Lrest r hr₂
            · intro r hr w' hw'
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hEx_f r hr₁ w' hw'
              · exact hEx_rest r hr₂ w' hw'
            · intro v
              rw [values_append, List.count_append, hCount_f v, hCount_rest v]
              have hne : GroundTy.encodeVal (G := .bool) false ≠
                  GroundTy.encodeVal (G := .bool) true := by decide
              simp only [values, List.filterMap_cons, List.count_cons, beq_self_eq_true,
                ↓reduceIte, beq_iff_eq, hne, Nat.add_mul, Nat.one_mul]
              omega
          · obtain ⟨L_t, hDer_t, hCells_t, hEx_t, hCount_t⟩ :=
              ihk true σ (GroundTy.encodeVal (G := .bool) true :: ρ)
            have hMissHit :
                Derives P
                  (.eval σ (GroundTy.encodeVal (G := .bool) true :: ρ)
                    (.caseCon (.var 0) symFalse 0 (k false).toComp
                      (.caseCon (.var 0) symTrue 0 (k true).toComp .fail)))
                  L_t := .caseConMiss rfl (.caseConHit (args := []) rfl hDer_t)
            refine ⟨L_t ++ L_rest, .seqKOk hMissHit hDer_rest, ?_, ?_, ?_⟩
            · intro r hr
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · rw [hCells_t r hr₁, hσ_cells]
              · exact hCells_Lrest r hr₂
            · intro r hr w' hw'
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hEx_t r hr₁ w' hw'
              · exact hEx_rest r hr₂ w' hw'
            · intro v
              rw [values_append, List.count_append, hCount_t v, hCount_rest v]
              have hne : GroundTy.encodeVal (G := .bool) true ≠
                  GroundTy.encodeVal (G := .bool) false := by decide
              simp only [values, List.filterMap_cons, List.count_cons, beq_self_eq_true,
                ↓reduceIte, beq_iff_eq, hne, Nat.add_mul, Nat.one_mul]
              omega

/-- **General Structural Adequacy Theorem for `GroundComp` against `CallTimeChoice.Derives` (Task 4):**
For every `m : GroundComp G`, program `P`, store `σ`, and environment `ρ`, there exists a
derivable result list `L` (`Derives P (.eval σ ρ m.toComp) L`) such that
1. every result store in `L` preserves the incoming cell array (`r.2.cells = σ.cells`),
2. every `.ok w` in `L` is `GroundTy.encodeVal v₀` for some `v₀ : G.Web`, and
3. for every `v : G.Web`, the operational multiplicity `(values L).count (GroundTy.encodeVal v)`
   equals the compositional `Rel_ℕ` denotation `m.denote Nat v`! -/
theorem derives_groundComp_adequacy {G : GroundTy} (m : GroundComp G)
    (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ m.toComp) L ∧
      (∀ r ∈ L, r.2.cells = σ.cells) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web, (values L).count (GroundTy.encodeVal v) = m.denote Nat v) := by
  induction m generalizing σ ρ with
  | ret v₀ =>
      refine ⟨[(.ok (GroundTy.encodeVal v₀), σ)], ?_, ?_, ?_, ?_⟩
      · simpa only [toComp, GroundTy.eval_encodeVExp] using
          (Derives.ret (P := P) (σ := σ) (ρ := ρ) (v := GroundTy.encodeVExp v₀))
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr
        injection hw with hw'
        exact ⟨v₀, hw'.symm⟩
      · intro v
        simp only [values, List.filterMap_cons, List.filterMap_nil, List.count_singleton', denote]
        by_cases h : v₀ = v
        · subst h; simp
        · have hne : GroundTy.encodeVal v₀ ≠ GroundTy.encodeVal v :=
            fun heq => h (GroundTy.encodeVal_injective heq)
          simp [h, hne]
  | choose m₁ m₂ ih₁ ih₂ =>
      obtain ⟨L₁, hD₁, hCells₁, hEx₁, hC₁⟩ := ih₁ σ ρ
      obtain ⟨L₂, hD₂, hCells₂, hEx₂, hC₂⟩ := ih₂ σ ρ
      refine ⟨L₁ ++ L₂, .choose hD₁ hD₂, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr₁ | hr₂
        · exact hCells₁ r hr₁
        · exact hCells₂ r hr₂
      · intro r hr w hw
        rcases List.mem_append.mp hr with hr₁ | hr₂
        · exact hEx₁ r hr₁ w hw
        · exact hEx₂ r hr₂ w hw
      · intro v
        rw [values_append, List.count_append, hC₁ v, hC₂ v]
        rfl
  | fail =>
      refine ⟨[(.fail, σ)], .fail, ?_, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr
        cases hw
      · intro v
        rfl
  | emit e m ih =>
      obtain ⟨L, hD, hCells, hEx, hC⟩ := ih (σ.emit e) ρ
      exact ⟨L, .emit hD, hCells, hEx, hC⟩
  | caseBool b mFalse mTrue ihF ihT =>
      cases b with
      | false =>
          obtain ⟨L, hD, hCells, hEx, hC⟩ := ihF σ ρ
          have hHit : Derives P (.eval σ ρ (GroundComp.caseBool false mFalse mTrue).toComp) L :=
            .caseConHit (args := []) rfl hD
          exact ⟨L, hHit, hCells, hEx, hC⟩
      | true =>
          obtain ⟨L, hD, hCells, hEx, hC⟩ := ihT σ ρ
          have hMissHit : Derives P (.eval σ ρ (GroundComp.caseBool true mFalse mTrue).toComp) L :=
            .caseConMiss rfl (.caseConHit (args := []) rfl hD)
          exact ⟨L, hMissHit, hCells, hEx, hC⟩
  | seqBool m₁ k ih₁ ihk =>
      obtain ⟨L₁, hD₁, hCells₁, hEx₁, hC₁⟩ := ih₁ σ ρ
      have hBoolL₁ : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true := by
        intro r hr w hw
        obtain ⟨b₀, hb₀⟩ := hEx₁ r hr w hw
        cases b₀
        · exact Or.inl hb₀
        · exact Or.inr hb₀
      obtain ⟨L, hD_seqK, hCells_L, hEx_L, hCount_L⟩ :=
        derives_seqK_bool k σ.cells ρ L₁ hCells₁ hBoolL₁ ihk
      refine ⟨L, .seq hD₁ hD_seqK, hCells_L, hEx_L, ?_⟩
      intro v
      rw [hCount_L v, hC₁ false, hC₁ true]
      rfl

/-- Any source derivation of a `GroundComp` producer preserves the incoming store's
cell array on every returned branch (`emit` may extend `trace`, while `cells` is invariant). -/
theorem derives_groundComp_preserves_cells {G : GroundTy} (m : GroundComp G)
    {P : Program} {σ : Store} {ρ : List (Val Nat)} {L : List Result}
    (hD : Derives P (.eval σ ρ m.toComp) L) :
    ∀ r ∈ L, r.2.cells = σ.cells := by
  obtain ⟨L', hD', hCells', _, _⟩ := derives_groundComp_adequacy m P σ ρ
  cases hD.deterministic hD'
  exact hCells'

/-! ## 6. General Two-Force Memoization Theorem Against `CallTimeChoice.Derives` -/

/-- Allocating a cell at `σ.cells.length` places the pending suspension at index `σ.cells.length`. -/
theorem cells_alloc_getElem?_length (σ : Store) (code : Comp) (env : List (Val Nat)) :
    (σ.alloc code env).cells[σ.cells.length]? = some ⟨code, env, .pending⟩ := by
  simp [Store.alloc]

/-- Updating the memo of an existing cell at index `ℓ` replaces its `memo` field and preserves
its origin (`code` and `env`). -/
theorem cells_setMemo_getElem?_eq (σ : Store) (ℓ : Nat) (c : Suspension) (k : Memo)
    (h : σ.cells[ℓ]? = some c) :
    (σ.setMemo ℓ k).cells[ℓ]? = some { c with memo := k } := by
  simp [Store.setMemo, h]

/-- First-force commitment lemma: running `commitK ℓ` over a producer result list `L_prod`
where every branch has cell `c₀` at `ℓ` and every successful value is an encoded Boolean
preserves the successful value list (`values L_commit = values L_prod`) and commits
`.done w` at cell `ℓ` in every successful branch's store. -/
theorem derives_commitK_bool {P : Program} (ℓ : Nat) (c₀ : Suspension)
    (cells₁ : List Suspension) (hCell₁ : cells₁[ℓ]? = some c₀)
    (L_prod : List Result)
    (hCells : ∀ r ∈ L_prod, r.2.cells = cells₁)
    (hBool : ∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
      w = GroundTy.encodeVal (G := .bool) false ∨
      w = GroundTy.encodeVal (G := .bool) true) :
    ∃ L_commit : List Result,
      Derives P (.commitK ℓ L_prod) L_commit ∧
      values L_commit = values L_prod ∧
      (∀ r ∈ L_commit, ∀ w, r.1 = .ok w →
        (w = GroundTy.encodeVal (G := .bool) false ∨
         w = GroundTy.encodeVal (G := .bool) true) ∧
        r.2.cells[ℓ]? = some { c₀ with memo := .done w }) := by
  induction L_prod with
  | nil =>
      refine ⟨[], .commitNil, rfl, ?_⟩
      intro r hr; cases hr
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      have hCells_rest : ∀ r ∈ rest, r.2.cells = cells₁ :=
        fun r hr => hCells r (List.mem_cons_of_mem _ hr)
      have hBool_rest : ∀ r ∈ rest, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true :=
        fun r hr => hBool r (List.mem_cons_of_mem _ hr)
      obtain ⟨L_rest, hDer_rest, hVals_rest, hPost_rest⟩ := ih hCells_rest hBool_rest
      cases o with
      | fail =>
          refine ⟨(.fail, σ.setMemo ℓ .pending) :: L_rest, .commitStop rfl hDer_rest, ?_, ?_⟩
          · simpa [values] using hVals_rest
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hPost_rest r hr' w hw
      | blackhole =>
          refine ⟨(.blackhole, σ.setMemo ℓ .pending) :: L_rest, .commitStop rfl hDer_rest, ?_, ?_⟩
          · simpa [values] using hVals_rest
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hPost_rest r hr' w hw
      | ok w =>
          have hw := hBool (.ok w, σ) List.mem_cons_self w rfl
          have hσ : σ.cells = cells₁ := hCells (.ok w, σ) List.mem_cons_self
          have hw_cell : w.isCell = false := by
            rcases hw with rfl | rfl <;> rfl
          have hWhnf :
              Derives P (.forceVal (σ.setMemo ℓ (.done w)) w)
                [(.ok w, σ.setMemo ℓ (.done w))] :=
            .forceWhnf hw_cell
          refine ⟨(.ok w, σ.setMemo ℓ (.done w)) :: L_rest,
            .commitOk hWhnf hDer_rest, ?_, ?_⟩
          · simpa [values] using hVals_rest
          · intro r hr w' hw'
            rcases List.mem_cons.mp hr with rfl | hr'
            · injection hw' with hw_eq
              subst hw_eq
              refine ⟨hw, ?_⟩
              have hLookup : σ.cells[ℓ]? = some c₀ := by
                rw [hσ]
                exact hCell₁
              exact cells_setMemo_getElem?_eq σ ℓ c₀ (.done w) hLookup
            · exact hPost_rest r hr' w' hw'

/-- First-force theorem for a freshly allocated `GroundComp .bool` cell:
evaluating `.force (.var 0)` in `(σ.alloc p.toComp ρ)` and `(.need σ.cells.length :: ρ)`
runs `p.toComp` once, commits `.done w` at cell `ℓ = σ.cells.length` on every successful
branch, and produces `encodeVal b` with exact multiplicity `p.denote Nat b`. -/
theorem derives_firstForce_need_bool (p : GroundComp .bool)
    (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    let ℓ := σ.cells.length
    let σ₀ := σ.alloc p.toComp ρ
    ∃ L₁ : List Result,
      Derives P (.eval σ₀ (.need ℓ :: ρ) (.force (.var 0))) L₁ ∧
      (∀ r ∈ L₁, ∀ w, r.1 = .ok w →
        (w = GroundTy.encodeVal (G := .bool) false ∨
         w = GroundTy.encodeVal (G := .bool) true) ∧
        r.2.cells[ℓ]? = some ⟨p.toComp, ρ, .done w⟩) ∧
      (∀ b : Bool,
        (values L₁).count (GroundTy.encodeVal (G := .bool) b) = p.denote Nat b) := by
  intro ℓ σ₀
  have hLookup₀ : σ₀.cells[ℓ]? = some ⟨p.toComp, ρ, .pending⟩ :=
    cells_alloc_getElem?_length σ p.toComp ρ
  let σ₁ := σ₀.setMemo ℓ .evaluating
  have hLookup₁ : σ₁.cells[ℓ]? = some ⟨p.toComp, ρ, .evaluating⟩ :=
    cells_setMemo_getElem?_eq σ₀ ℓ ⟨p.toComp, ρ, .pending⟩ .evaluating hLookup₀
  obtain ⟨L_prod, hD_prod, hCells_prod, hEx_prod, hCount_prod⟩ :=
    derives_groundComp_adequacy p P σ₁ ρ
  have hBool_prod : ∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
      w = GroundTy.encodeVal (G := .bool) false ∨
      w = GroundTy.encodeVal (G := .bool) true := by
    intro r hr w hw
    obtain ⟨b₀, hb₀⟩ := hEx_prod r hr w hw
    cases b₀
    · exact Or.inl hb₀
    · exact Or.inr hb₀
  obtain ⟨L₁, hD_commit, hVals_eq, hPost_commit⟩ :=
    derives_commitK_bool ℓ ⟨p.toComp, ρ, .evaluating⟩ σ₁.cells hLookup₁
      L_prod hCells_prod hBool_prod
  have hForce : Derives P (.eval σ₀ (.need ℓ :: ρ) (.force (.var 0))) L₁ :=
    .force (.forcePending hLookup₀ rfl hD_prod hD_commit)
  refine ⟨L₁, hForce, hPost_commit, ?_⟩
  intro b
  rw [hVals_eq]
  exact hCount_prod b

/-- Second-force lemma at de Bruijn index `1`: when cell `ℓ` already has `c.memo = .done w`
for a non-cell value `w`, forcing `.var 1` in environment `w :: .need ℓ :: ρ`
returns `[(.ok w, σ')]` deterministically without re-evaluating the producer. -/
theorem derives_force_var1_done {P : Program} {σ' : Store} {ℓ : Nat} {c : Suspension}
    {w : Val Nat} (ρ : List (Val Nat))
    (hLookup : σ'.cells[ℓ]? = some c) (hMemo : c.memo = .done w)
    (hw_cell : w.isCell = false) :
    Derives P (.eval σ' (w :: .need ℓ :: ρ) (.force (.var 1))) [(.ok w, σ')] :=
  .force (.forceDone hLookup hMemo (.forceWhnf hw_cell))

/-- Continuation of the first `seqBool` in `NeedScopeComp.doubleBody.toComp`. -/
abbrev doubleCont : Comp :=
  .caseCon (.var 0) symFalse 0
    (NeedScopeComp.toCompAt (G := .pair .bool .bool)
      (.seqBool .force (fun y => .ret (G := .pair .bool .bool) (false, y))) 1)
    (.caseCon (.var 0) symTrue 0
      (NeedScopeComp.toCompAt (G := .pair .bool .bool)
        (.seqBool .force (fun y => .ret (G := .pair .bool .bool) (true, y))) 1)
      .fail)

/-- When the first force yielded `false` and committed `.done (encodeVal false)` at cell `ℓ`,
the continuation `doubleCont` forces cell `ℓ` a second time via `forceDone` and returns
the diagonal pair `(false, false)`. -/
theorem derives_doubleCont_false {P : Program} {σ' : Store} {ℓ : Nat} {c : Suspension}
    (ρ : List (Val Nat))
    (hLookup : σ'.cells[ℓ]? = some c)
    (hMemo : c.memo = .done (GroundTy.encodeVal (G := .bool) false)) :
    Derives P
      (.eval σ' (GroundTy.encodeVal (G := .bool) false :: .need ℓ :: ρ) doubleCont)
      [(.ok (GroundTy.encodeVal (G := .pair .bool .bool) (false, false)), σ')] := by
  refine .caseConHit (args := []) rfl ?_
  refine Derives.seq_single
    (derives_force_var1_done ρ hLookup hMemo rfl) ?_
  refine .caseConHit (args := []) rfl ?_
  exact .ret

/-- When the first force yielded `true` and committed `.done (encodeVal true)` at cell `ℓ`,
the continuation `doubleCont` forces cell `ℓ` a second time via `forceDone` and returns
the diagonal pair `(true, true)`. -/
theorem derives_doubleCont_true {P : Program} {σ' : Store} {ℓ : Nat} {c : Suspension}
    (ρ : List (Val Nat))
    (hLookup : σ'.cells[ℓ]? = some c)
    (hMemo : c.memo = .done (GroundTy.encodeVal (G := .bool) true)) :
    Derives P
      (.eval σ' (GroundTy.encodeVal (G := .bool) true :: .need ℓ :: ρ) doubleCont)
      [(.ok (GroundTy.encodeVal (G := .pair .bool .bool) (true, true)), σ')] := by
  refine .caseConMiss rfl (.caseConHit (args := []) rfl ?_)
  refine Derives.seq_single
    (derives_force_var1_done ρ hLookup hMemo rfl) ?_
  refine .caseConMiss rfl (.caseConHit (args := []) rfl ?_)
  exact .ret

@[simp]
theorem values_cons_ok (w : Val Nat) (σ : Store) (rest : List Result) :
    values ((.ok w, σ) :: rest) = w :: values rest := rfl

/-- Threading `doubleCont` across any first-force result list `L₁` where every successful
branch `(.ok w, σ')` has `c.memo = .done w` at cell `ℓ` produces one diagonal pair `(a, a)`
per occurrence of `a` in `L₁`, and no off-diagonal pairs. -/
theorem derives_doubleBody_seqK {P : Program} (ℓ : Nat) (ρ : List (Val Nat))
    (L₁ : List Result)
    (hCommitted : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
      (w = GroundTy.encodeVal (G := .bool) false ∨
       w = GroundTy.encodeVal (G := .bool) true) ∧
      ∃ c : Suspension, r.2.cells[ℓ]? = some c ∧ c.memo = .done w) :
    ∃ L : List Result,
      Derives P (.seqK doubleCont (.need ℓ :: ρ) L₁) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        ∃ ab : Bool × Bool,
          w = GroundTy.encodeVal (G := .pair .bool .bool) ab ∧ ab.1 = ab.2) ∧
      (∀ ab : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) ab) =
          if ab.1 = ab.2 then
            (values L₁).count (GroundTy.encodeVal (G := .bool) ab.1)
          else 0) := by
  induction L₁ with
  | nil =>
      refine ⟨[], .seqKNil, ?_, ?_⟩
      · intro r hr; cases hr
      · rintro ⟨a, b⟩
        cases a <;> cases b <;> simp [values]
  | cons r rest ih =>
      rcases r with ⟨o, σ'⟩
      have hRest : ∀ r ∈ rest, ∀ w, r.1 = .ok w →
          (w = GroundTy.encodeVal (G := .bool) false ∨
           w = GroundTy.encodeVal (G := .bool) true) ∧
          ∃ c : Suspension, r.2.cells[ℓ]? = some c ∧ c.memo = .done w :=
        fun r hr => hCommitted r (List.mem_cons_of_mem _ hr)
      obtain ⟨L_rest, hDer_rest, hDiag_rest, hCount_rest⟩ := ih hRest
      cases o with
      | fail =>
          refine ⟨(.fail, σ') :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_⟩
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hDiag_rest r hr' w hw
          · intro ab
            simpa [values] using hCount_rest ab
      | blackhole =>
          refine ⟨(.blackhole, σ') :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_⟩
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hDiag_rest r hr' w hw
          · intro ab
            simpa [values] using hCount_rest ab
      | ok w =>
          obtain ⟨hw_bool, c, hLookup, hMemo⟩ :=
            hCommitted (.ok w, σ') List.mem_cons_self w rfl
          rcases hw_bool with rfl | rfl
          · have hEvalF := derives_doubleCont_false (P := P) ρ hLookup hMemo
            refine ⟨(.ok (GroundTy.encodeVal (G := .pair .bool .bool) (false, false)), σ') :: L_rest,
              .seqKOk hEvalF hDer_rest, ?_, ?_⟩
            · intro r hr w' hw'
              rcases List.mem_cons.mp hr with rfl | hr'
              · injection hw' with hw_eq
                exact ⟨(false, false), hw_eq.symm, rfl⟩
              · exact hDiag_rest r hr' w' hw'
            · rintro ⟨a, b⟩
              rw [values_cons_ok, List.count_cons, hCount_rest (a, b),
                  values_cons_ok, List.count_cons]
              cases a <;> cases b
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (false, false) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (false, false)) = true := rfl
                have h2 : (GroundTy.encodeVal (G := .bool) false ==
                    GroundTy.encodeVal (G := .bool) false) = true := rfl
                rw [h1, h2]
                simp
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (false, false) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (false, true)) = false := rfl
                rw [h1]
                simp
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (false, false) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (true, false)) = false := rfl
                rw [h1]
                simp
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (false, false) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (true, true)) = false := rfl
                have h2 : (GroundTy.encodeVal (G := .bool) false ==
                    GroundTy.encodeVal (G := .bool) true) = false := rfl
                rw [h1, h2]
                simp
          · have hEvalT := derives_doubleCont_true (P := P) ρ hLookup hMemo
            refine ⟨(.ok (GroundTy.encodeVal (G := .pair .bool .bool) (true, true)), σ') :: L_rest,
              .seqKOk hEvalT hDer_rest, ?_, ?_⟩
            · intro r hr w' hw'
              rcases List.mem_cons.mp hr with rfl | hr'
              · injection hw' with hw_eq
                exact ⟨(true, true), hw_eq.symm, rfl⟩
              · exact hDiag_rest r hr' w' hw'
            · rintro ⟨a, b⟩
              rw [values_cons_ok, List.count_cons, hCount_rest (a, b),
                  values_cons_ok, List.count_cons]
              cases a <;> cases b
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (true, true) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (false, false)) = false := rfl
                have h2 : (GroundTy.encodeVal (G := .bool) true ==
                    GroundTy.encodeVal (G := .bool) false) = false := rfl
                rw [h1, h2]
                simp
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (true, true) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (false, true)) = false := rfl
                rw [h1]
                simp
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (true, true) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (true, false)) = false := rfl
                rw [h1]
                simp
              · have h1 : (GroundTy.encodeVal (G := .pair .bool .bool) (true, true) ==
                    GroundTy.encodeVal (G := .pair .bool .bool) (true, true)) = true := rfl
                have h2 : (GroundTy.encodeVal (G := .bool) true ==
                    GroundTy.encodeVal (G := .bool) true) = true := rfl
                rw [h1, h2]
                simp

/-- Algebraic evaluation of `NeedScopeComp.denoteNeedClosed` on `doubleBody`:
because `doubleBody` forces its `NeedWeb Bool` argument twice via `needComult`,
the `none` state contributes `0` and each `some a` state contributes `1` to `(a, a)`
and `0` to off-diagonal pairs. -/
theorem denoteNeedClosed_doubleBody_eq (w_c : Bool → Nat) (ab : Bool × Bool) :
    NeedScopeComp.denoteNeedClosed Nat w_c NeedScopeComp.doubleBody ab =
      if ab.1 = ab.2 then w_c ab.1 else 0 := by
  rcases ab with ⟨a, b⟩
  have h_none : NeedScopeComp.denoteRel Nat NeedScopeComp.doubleBody none (a, b) = 0 := by
    cases a <;> cases b <;> decide
  have h_some (c : Bool) :
      NeedScopeComp.denoteRel Nat NeedScopeComp.doubleBody (some c) (a, b) =
        if c = a ∧ c = b then 1 else 0 := by
    cases c <;> cases a <;> cases b <;> decide
  unfold NeedScopeComp.denoteNeedClosed
  rw [Fintype.sum_bool, h_none, h_some false, h_some true]
  cases a <;> cases b <;> simp

/-- **Principal Two-Force Memoization Theorem (`derives_need_doubleBody_adequacy`):**
For every finite Boolean producer `p : GroundComp .bool`, program `P`, store `σ`, and
environment `ρ`, there exists a complete result list `L` derived by `CallTimeChoice.Derives`
for `Comp.need p.toComp NeedScopeComp.doubleBody.toComp` such that:
1. every successful outcome in `L` is an encoded Boolean pair `(a, b)` with `a = b`,
2. for every `(a, b) : Bool × Bool`, the exact multiplicity in `values L` is
   `if a = b then p.denote Nat a else 0`, and
3. this count agrees with the compositional `NeedWeb` comonoid denotation
   `NeedScopeComp.denoteNeedClosed Nat (p.denote Nat) NeedScopeComp.doubleBody (a, b)`. -/
theorem derives_need_doubleBody_adequacy (p : GroundComp .bool)
    (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (.need p.toComp NeedScopeComp.doubleBody.toComp)) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        ∃ ab : Bool × Bool,
          w = GroundTy.encodeVal (G := .pair .bool .bool) ab ∧ ab.1 = ab.2) ∧
      (∀ ab : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) ab) =
          if ab.1 = ab.2 then p.denote Nat ab.1 else 0) ∧
      (∀ ab : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) ab) =
          NeedScopeComp.denoteNeedClosed Nat (p.denote Nat) NeedScopeComp.doubleBody ab) := by
  obtain ⟨L₁, hForce₁, hPost₁, hCount₁⟩ := derives_firstForce_need_bool p P σ ρ
  have hCommitted : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
      (w = GroundTy.encodeVal (G := .bool) false ∨
       w = GroundTy.encodeVal (G := .bool) true) ∧
      ∃ c : Suspension, r.2.cells[σ.cells.length]? = some c ∧ c.memo = .done w := by
    intro r hr w hw
    obtain ⟨hw_bool, hCell⟩ := hPost₁ r hr w hw
    exact ⟨hw_bool, ⟨p.toComp, ρ, .done w⟩, hCell, rfl⟩
  obtain ⟨L, hSeqK, hDiag, hCount⟩ :=
    derives_doubleBody_seqK (P := P) σ.cells.length ρ L₁ hCommitted
  have hNeed : Derives P (.eval σ ρ (.need p.toComp NeedScopeComp.doubleBody.toComp)) L :=
    .need (Derives.seq (m := .force (.var 0)) (n := doubleCont) hForce₁ hSeqK)
  refine ⟨L, hNeed, hDiag, ?_, ?_⟩
  · intro ab
    rw [hCount ab, hCount₁ ab.1]
  · intro ab
    rw [hCount ab, denoteNeedClosed_doubleBody_eq, hCount₁ ab.1]

/-- Specialization of `derives_need_doubleBody_adequacy` to the empty program, empty store,
and empty environment. -/
theorem derives_need_doubleBody_empty (p : GroundComp .bool) :
    ∃ L : List Result,
      Derives [] (.eval Store.empty [] (.need p.toComp NeedScopeComp.doubleBody.toComp)) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        ∃ ab : Bool × Bool,
          w = GroundTy.encodeVal (G := .pair .bool .bool) ab ∧ ab.1 = ab.2) ∧
      (∀ ab : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) ab) =
          if ab.1 = ab.2 then p.denote Nat ab.1 else 0) := by
  obtain ⟨L, hD, hDiag, hCount, _⟩ := derives_need_doubleBody_adequacy p [] Store.empty []
  exact ⟨L, hD, hDiag, hCount⟩

/-! ### Required Positive and Negative Controls Derived Against `CallTimeChoice.Derives` -/

/-- Producer 1: distinct Boolean coin `choose (ret false) (ret true)`. -/
def coinProducer : GroundComp .bool :=
  .choose (.ret false) (.ret true)

/-- Producer 2: duplicate `false` producer `choose (ret false) (ret false)`. -/
def dupFalseProducer : GroundComp .bool :=
  .choose (.ret false) (.ret false)

/-- **Control 1 (Distinct Boolean Coin, Two Forces of Same Memo Cell):**
Derived directly from `derives_need_doubleBody_empty`: forcing a shared coin cell twice
yields `(false, false)` once, `(true, true)` once, and unequal pairs zero times. -/
theorem control_need_double_coin :
    ∃ L : List Result,
      Derives [] (.eval Store.empty [] (.need coinProducer.toComp NeedScopeComp.doubleBody.toComp)) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        ∃ ab : Bool × Bool,
          w = GroundTy.encodeVal (G := .pair .bool .bool) ab ∧ ab.1 = ab.2) ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, false)) = 1 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, true)) = 1 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, true)) = 0 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, false)) = 0 := by
  obtain ⟨L, hD, hDiag, hCount⟩ := derives_need_doubleBody_empty coinProducer
  refine ⟨L, hD, hDiag, ?_, ?_, ?_, ?_⟩
  · simpa [coinProducer, denote] using hCount (false, false)
  · simpa [coinProducer, denote] using hCount (true, true)
  · simpa [coinProducer, denote] using hCount (false, true)
  · simpa [coinProducer, denote] using hCount (true, false)

/-- **Control 2 (Duplicate `false` Producer, Two Forces of Same Memo Cell):**
Derived directly from `derives_need_doubleBody_empty`: when a producer yields `false`
with multiplicity `2`, forcing its memoized `need` cell twice yields `(false, false)`
**twice** (not four times!), and all other pairs zero times. -/
theorem control_need_double_dupFalse :
    ∃ L : List Result,
      Derives [] (.eval Store.empty [] (.need dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp)) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        ∃ ab : Bool × Bool,
          w = GroundTy.encodeVal (G := .pair .bool .bool) ab ∧ ab.1 = ab.2) ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, false)) = 2 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, true)) = 0 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, true)) = 0 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, false)) = 0 := by
  obtain ⟨L, hD, hDiag, hCount⟩ := derives_need_doubleBody_empty dupFalseProducer
  refine ⟨L, hD, hDiag, ?_, ?_, ?_, ?_⟩
  · simpa [dupFalseProducer, denote] using hCount (false, false)
  · simpa [dupFalseProducer, denote] using hCount (true, true)
  · simpa [dupFalseProducer, denote] using hCount (false, true)
  · simpa [dupFalseProducer, denote] using hCount (true, false)

/-- **Control 3 (Failing Producer, Two Forces of Memo Cell):**
Forcing a failing memo cell twice derives a non-empty completed result list containing
a `.fail` outcome (keeping source failure distinct from fuel exhaustion), with zero
successful answers (`values L = []` and count `0` for every pair). -/
theorem control_need_double_fail :
    ∃ L : List Result,
      Derives [] (.eval Store.empty [] (.need (GroundComp.fail (G := .bool)).toComp NeedScopeComp.doubleBody.toComp)) L ∧
      (∃ σ_fail : Store, L = [(.fail, σ_fail)]) ∧
      values L = [] ∧
      (∀ ab : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) ab) = 0) := by
  let σ₀ := Store.empty.alloc (GroundComp.fail (G := .bool)).toComp []
  have hLookup₀ : σ₀.cells[0]? = some ⟨.fail, [], .pending⟩ :=
    cells_alloc_getElem?_length Store.empty .fail []
  have hForce :
      Derives [] (.eval σ₀ [.need 0] (.force (.var 0)))
        [(.fail, (σ₀.setMemo 0 .evaluating).setMemo 0 .pending)] :=
    .force (.forcePending hLookup₀ rfl .fail (.commitStop rfl .commitNil))
  have hNeed :
      Derives [] (.eval Store.empty [] (.need (GroundComp.fail (G := .bool)).toComp NeedScopeComp.doubleBody.toComp))
        [(.fail, (σ₀.setMemo 0 .evaluating).setMemo 0 .pending)] :=
    .need (.seq hForce (.seqKStop rfl .seqKNil))
  refine ⟨[(.fail, (σ₀.setMemo 0 .evaluating).setMemo 0 .pending)], hNeed,
    ⟨_, rfl⟩, rfl, ?_⟩
  intro ab
  rfl

/-- **Control 4 (Failing Producer, Unused Memo Cell Discarded):**
When the body discards the memoized cell (`NeedScopeComp.discardBody`), the failing
producer is never demanded, and `Derives` produces the single successful answer `false`. -/
theorem control_need_discard_fail (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (.need (GroundComp.fail (G := .bool)).toComp NeedScopeComp.discardBody.toComp)) L ∧
      L = [(.ok (GroundTy.encodeVal (G := .bool) false), σ.alloc .fail ρ)] ∧
      (values L).count (GroundTy.encodeVal (G := .bool) false) = 1 ∧
      (values L).count (GroundTy.encodeVal (G := .bool) true) = 0 := by
  refine ⟨[(.ok (GroundTy.encodeVal (G := .bool) false), σ.alloc .fail ρ)],
    .need .ret, rfl, rfl, rfl⟩

/-- **Control 5 (Duplicate `false` Producer, Resampling Thunk Forced Twice):**
Separating resampling (`delay`) from memoization (`need`): when the same duplicate-`false`
producer `dupFalseProducer` is bound with `Comp.delay` instead of `Comp.need` and forced
twice by `doubleBody`, `CallTimeChoice.Derives` produces `(false, false)` **four times**
(`2 × 2 = 4`), whereas `Comp.need` in `control_need_double_dupFalse` produced it **twice**. -/
theorem control_delay_double_dupFalse :
    ∃ L : List Result,
      Derives [] (.eval Store.empty [] (.delay dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp)) L ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, false)) = 4 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, true)) = 0 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, true)) = 0 ∧
      (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, false)) = 0 := by
  cases hrun : run [] 40 (.eval Store.empty [] (.delay dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp)) with
  | none =>
      exfalso
      revert hrun
      decide
  | some L =>
      refine ⟨L, run_sound [] 40 _ L hrun, ?_, ?_, ?_, ?_⟩
      · have h : (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, false)) = 4 := by
          have hvals : (run [] 40 (.eval Store.empty [] (.delay dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp))).map
              (fun res => (values res).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, false))) = some 4 := by
            decide
          rw [hrun] at hvals
          exact Option.some.inj hvals
        exact h
      · have h : (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, true)) = 0 := by
          have hvals : (run [] 40 (.eval Store.empty [] (.delay dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp))).map
              (fun res => (values res).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, true))) = some 0 := by
            decide
          rw [hrun] at hvals
          exact Option.some.inj hvals
        exact h
      · have h : (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, true)) = 0 := by
          have hvals : (run [] 40 (.eval Store.empty [] (.delay dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp))).map
              (fun res => (values res).count (GroundTy.encodeVal (G := .pair .bool .bool) (false, true))) = some 0 := by
            decide
          rw [hrun] at hvals
          exact Option.some.inj hvals
        exact h
      · have h : (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, false)) = 0 := by
          have hvals : (run [] 40 (.eval Store.empty [] (.delay dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp))).map
              (fun res => (values res).count (GroundTy.encodeVal (G := .pair .bool .bool) (true, false))) = some 0 := by
            decide
          rw [hrun] at hvals
          exact Option.some.inj hvals
        exact h

end GroundComp

/-! ## 7. General `NeedScopeComp` Adequacy and Dependent Multi-Cell Chains -/

section GeneralNeedAdequacy

open GroundComp

/-- Congruence for `resultSum` over the elements of `L`. -/
theorem resultSum_congr_mem {L : List Result} {f g : Val Nat → Store → Nat}
    (h : ∀ r ∈ L, ∀ w, r.1 = .ok w → f w r.2 = g w r.2) :
    resultSum L f = resultSum L g := by
  induction L with
  | nil => rfl
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      have hrest : ∀ r ∈ rest, ∀ w, r.1 = .ok w → f w r.2 = g w r.2 :=
        fun r hr => h r (List.mem_cons_of_mem _ hr)
      cases o with
      | ok w =>
          simp only [resultSum_ok, h (.ok w, σ) List.mem_cons_self w rfl, ih hrest]
      | fail => exact ih hrest
      | blackhole => exact ih hrest

/-- If `f` vanishes on every `.ok` result in `L`, then `resultSum L f = 0`. -/
theorem resultSum_eq_zero {L : List Result} {f : Val Nat → Store → Nat}
    (h : ∀ r ∈ L, ∀ w, r.1 = .ok w → f w r.2 = 0) :
    resultSum L f = 0 := by
  induction L with
  | nil => rfl
  | cons r rest ih =>
      have hrest : ∀ r' ∈ rest, ∀ w, r'.1 = .ok w → f w r'.2 = 0 :=
        fun r' hr' w hw => h r' (List.mem_cons_of_mem _ hr') w hw
      have hih := ih hrest
      rcases r with ⟨o, σ⟩
      cases o with
      | ok w =>
          have h0 : f w σ = 0 := h (.ok w, σ) List.mem_cons_self w rfl
          dsimp [resultSum] at hih ⊢
          rw [h0, Nat.zero_add]
          exact hih
      | fail => exact hih
      | blackhole => exact hih

/-- Lookup of a variable expression `VExp.var depth` when `ρ[depth]? = some w`. -/
theorem vexp_eval_var_of_getElem? {ρ : List (Val Nat)} {depth : Nat} {w : Val Nat}
    (h : ρ[depth]? = some w) :
    (VExp.var depth).eval ρ = w := by
  simp [VExp.eval, List.getD_eq_getElem?_getD, h]

/-- Forcing `.var depth` when `ρ[depth]? = some (.need ℓ)` and cell `ℓ` has
`c.memo = .done w` for a non-cell value `w` returns `[(.ok w, σ)]` deterministically. -/
theorem derives_force_var_done {P : Program} {σ : Store} {ρ : List (Val Nat)}
    {depth ℓ : Nat} {c : Suspension} {w : Val Nat}
    (hEnv : ρ[depth]? = some (.need ℓ))
    (hLookup : σ.cells[ℓ]? = some c)
    (hMemo : c.memo = .done w)
    (hw_cell : w.isCell = false) :
    Derives P (.eval σ ρ (.force (.var depth))) [(.ok w, σ)] := by
  have hForceVal : Derives P (.forceVal σ ((VExp.var depth).eval ρ)) [(.ok w, σ)] := by
    rw [vexp_eval_var_of_getElem? hEnv]
    exact .forceDone hLookup hMemo (.forceWhnf hw_cell)
  exact .force hForceVal

/-- Updating the memo of cell `ℓ` leaves all other cells `j ≠ ℓ` unchanged. -/
theorem cells_setMemo_getElem?_ne (σ : Store) (ℓ j : Nat) (k : Memo) (hne : ℓ ≠ j) :
    (σ.setMemo ℓ k).cells[j]? = σ.cells[j]? := by
  simp [Store.setMemo, hne]

/-- Allocating a cell at `σ.cells.length` leaves all earlier cells `j < σ.cells.length` unchanged. -/
theorem cells_alloc_getElem?_lt (σ : Store) (code : Comp) (env : List (Val Nat))
    {j : Nat} (hj : j < σ.cells.length) :
    (σ.alloc code env).cells[j]? = σ.cells[j]? := by
  simp [Store.alloc, List.getElem?_append_left hj]

/-- Algebraic identity for `NeedScopeComp.denoteRel` across `seqBool` in the cached/done phase:
when cell `ℓ` is already committed to `a₀`, sequential composition via `needComult`
factors into the product of `(none + some a₀)` sums. -/
theorem denoteRel_seqBool_done_sum {G : GroundTy}
    (b₁ : NeedScopeComp .bool) (k : Bool → NeedScopeComp G) (a₀ : Bool) (v : G.Web) :
    (b₁.denoteRel Nat none false + b₁.denoteRel Nat (some a₀) false) *
      ((k false).denoteRel Nat none v + (k false).denoteRel Nat (some a₀) v) +
    (b₁.denoteRel Nat none true + b₁.denoteRel Nat (some a₀) true) *
      ((k true).denoteRel Nat none v + (k true).denoteRel Nat (some a₀) v) =
    (NeedScopeComp.seqBool b₁ k).denoteRel Nat none v +
    (NeedScopeComp.seqBool b₁ k).denoteRel Nat (some a₀) v := by
  cases a₀ <;>
  · simp [NeedScopeComp.denoteRel, Fintype.sum_option, needComult,
      Nat.mul_add, Nat.add_mul]
    omega

/-- General `seqK` threading lemma for Boolean continuations that preserve `cells₀`. -/
theorem derives_seqK_bool_gen {P : Program} {G : GroundTy}
    (cFalse cTrue : Comp) (countFalse countTrue : G.Web → Nat)
    (cells₀ : List Suspension) (ρ : List (Val Nat)) (L₁ : List Result)
    (hCells₁ : ∀ r ∈ L₁, r.2.cells = cells₀)
    (hL₁ : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
      w = GroundTy.encodeVal (G := .bool) false ∨
      w = GroundTy.encodeVal (G := .bool) true)
    (ihF : ∀ σ : Store, σ.cells = cells₀ →
      ∃ L, Derives P (.eval σ (GroundTy.encodeVal (G := .bool) false :: ρ) cFalse) L ∧
        (∀ r ∈ L, r.2.cells = cells₀) ∧
        (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
        (∀ v : G.Web, (values L).count (GroundTy.encodeVal v) = countFalse v))
    (ihT : ∀ σ : Store, σ.cells = cells₀ →
      ∃ L, Derives P (.eval σ (GroundTy.encodeVal (G := .bool) true :: ρ) cTrue) L ∧
        (∀ r ∈ L, r.2.cells = cells₀) ∧
        (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
        (∀ v : G.Web, (values L).count (GroundTy.encodeVal v) = countTrue v)) :
    ∃ L,
      Derives P
        (.seqK
          (.caseCon (.var 0) symFalse 0 cFalse
            (.caseCon (.var 0) symTrue 0 cTrue .fail))
          ρ L₁)
        L ∧
      (∀ r ∈ L, r.2.cells = cells₀) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          (values L₁).count (GroundTy.encodeVal (G := .bool) false) * countFalse v +
          (values L₁).count (GroundTy.encodeVal (G := .bool) true) * countTrue v) := by
  induction L₁ with
  | nil =>
      refine ⟨[], .seqKNil, ?_, ?_, ?_⟩
      · intro r hr; cases hr
      · intro r hr; cases hr
      · intro v; simp [values]
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      have hCells_rest : ∀ r ∈ rest, r.2.cells = cells₀ :=
        fun r hr => hCells₁ r (List.mem_cons_of_mem _ hr)
      have hrest : ∀ r ∈ rest, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true :=
        fun r hr => hL₁ r (List.mem_cons_of_mem _ hr)
      obtain ⟨L_rest, hDer_rest, hCells_Lrest, hEx_rest, hCount_rest⟩ := ih hCells_rest hrest
      have hσ_cells : σ.cells = cells₀ := hCells₁ (o, σ) List.mem_cons_self
      cases o with
      | fail =>
          refine ⟨(.fail, σ) :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hσ_cells
            · exact hCells_Lrest r hr'
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hEx_rest r hr' w hw
          · intro v; simpa [values] using hCount_rest v
      | blackhole =>
          refine ⟨(.blackhole, σ) :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_, ?_⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hσ_cells
            · exact hCells_Lrest r hr'
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hEx_rest r hr' w hw
          · intro v; simpa [values] using hCount_rest v
      | ok w =>
          have hw := hL₁ (.ok w, σ) List.mem_cons_self w rfl
          rcases hw with rfl | rfl
          · obtain ⟨L_f, hDer_f, hCells_f, hEx_f, hCount_f⟩ := ihF σ hσ_cells
            have hHit :
                Derives P
                  (.eval σ (GroundTy.encodeVal (G := .bool) false :: ρ)
                    (.caseCon (.var 0) symFalse 0 cFalse
                      (.caseCon (.var 0) symTrue 0 cTrue .fail)))
                  L_f := .caseConHit (args := []) rfl hDer_f
            refine ⟨L_f ++ L_rest, .seqKOk hHit hDer_rest, ?_, ?_, ?_⟩
            · intro r hr
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hCells_f r hr₁
              · exact hCells_Lrest r hr₂
            · intro r hr w' hw'
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hEx_f r hr₁ w' hw'
              · exact hEx_rest r hr₂ w' hw'
            · intro v
              rw [values_append, List.count_append, hCount_f v, hCount_rest v]
              have hne : GroundTy.encodeVal (G := .bool) false ≠
                  GroundTy.encodeVal (G := .bool) true := by decide
              simp only [values, List.filterMap_cons, List.count_cons, beq_self_eq_true,
                ↓reduceIte, beq_iff_eq, hne, Nat.add_mul, Nat.one_mul]
              omega
          · obtain ⟨L_t, hDer_t, hCells_t, hEx_t, hCount_t⟩ := ihT σ hσ_cells
            have hMissHit :
                Derives P
                  (.eval σ (GroundTy.encodeVal (G := .bool) true :: ρ)
                    (.caseCon (.var 0) symFalse 0 cFalse
                      (.caseCon (.var 0) symTrue 0 cTrue .fail)))
                  L_t := .caseConMiss rfl (.caseConHit (args := []) rfl hDer_t)
            refine ⟨L_t ++ L_rest, .seqKOk hMissHit hDer_rest, ?_, ?_, ?_⟩
            · intro r hr
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hCells_t r hr₁
              · exact hCells_Lrest r hr₂
            · intro r hr w' hw'
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hEx_t r hr₁ w' hw'
              · exact hEx_rest r hr₂ w' hw'
            · intro v
              rw [values_append, List.count_append, hCount_t v, hCount_rest v]
              have hne : GroundTy.encodeVal (G := .bool) true ≠
                  GroundTy.encodeVal (G := .bool) false := by decide
              simp only [values, List.filterMap_cons, List.count_cons, beq_self_eq_true,
                ↓reduceIte, beq_iff_eq, hne, Nat.add_mul, Nat.one_mul]
              omega

/-- **Phase 1 (Cached / Done Phase, `derives_needScope_done`):**
For any `b : NeedScopeComp G`, when cell `ℓ` is bound at `ρ[depth]? = some (.need ℓ)`
and its store entry `σ.cells[ℓ]? = some c` already has `c.memo = .done (encodeVal a₀)`,
evaluating `b.toCompAt depth` preserves `r.2.cells = σ.cells` on every branch and
produces each `v : G.Web` with exact multiplicity
`b.denoteRel Nat none v + b.denoteRel Nat (some a₀) v`. -/
theorem derives_needScope_done {G : GroundTy} (b : NeedScopeComp G)
    (P : Program) (ℓ : Nat) (a₀ : Bool) (depth : Nat)
    (σ : Store) (ρ : List (Val Nat)) (c : Suspension)
    (hEnv : ρ[depth]? = some (.need ℓ))
    (hLookup : σ.cells[ℓ]? = some c)
    (hMemo : c.memo = .done (GroundTy.encodeVal (G := .bool) a₀)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (b.toCompAt depth)) L ∧
      (∀ r ∈ L, r.2.cells = σ.cells) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          b.denoteRel Nat none v + b.denoteRel Nat (some a₀) v) := by
  induction b generalizing depth σ ρ with
  | ret v₀ =>
      refine ⟨[(.ok (GroundTy.encodeVal v₀), σ)], ?_, ?_, ?_, ?_⟩
      · simpa only [NeedScopeComp.toCompAt, GroundTy.eval_encodeVExp] using
          (Derives.ret (P := P) (σ := σ) (ρ := ρ) (v := GroundTy.encodeVExp v₀))
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr
        injection hw with hw'
        exact ⟨v₀, hw'.symm⟩
      · intro v
        simp only [values, List.filterMap_cons, List.filterMap_nil, List.count_singleton',
          NeedScopeComp.denoteRel, needCounit]
        by_cases h : v₀ = v
        · subst h; simp
        · have hne : GroundTy.encodeVal v₀ ≠ GroundTy.encodeVal v :=
            fun heq => h (GroundTy.encodeVal_injective heq)
          simp [h, hne]
  | force =>
      have hw_cell : (GroundTy.encodeVal (G := .bool) a₀).isCell = false := by
        cases a₀ <;> rfl
      have hD := derives_force_var_done (P := P) hEnv hLookup hMemo hw_cell
      refine ⟨[(.ok (GroundTy.encodeVal (G := .bool) a₀), σ)], hD, ?_, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr
        injection hw with hw'
        exact ⟨a₀, hw'.symm⟩
      · intro v
        simp only [values, List.filterMap_cons, List.filterMap_nil, List.count_singleton',
          NeedScopeComp.denoteRel, forceNeedRel]
        cases a₀ <;> cases v <;> decide
  | choose b₁ b₂ ih₁ ih₂ =>
      obtain ⟨L₁, hD₁, hCells₁, hEx₁, hC₁⟩ := ih₁ depth σ ρ hEnv hLookup
      obtain ⟨L₂, hD₂, hCells₂, hEx₂, hC₂⟩ := ih₂ depth σ ρ hEnv hLookup
      refine ⟨L₁ ++ L₂, .choose hD₁ hD₂, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr₁ | hr₂
        · exact hCells₁ r hr₁
        · exact hCells₂ r hr₂
      · intro r hr w hw
        rcases List.mem_append.mp hr with hr₁ | hr₂
        · exact hEx₁ r hr₁ w hw
        · exact hEx₂ r hr₂ w hw
      · intro v
        rw [values_append, List.count_append, hC₁ v, hC₂ v]
        simp only [NeedScopeComp.denoteRel]
        omega
  | fail =>
      refine ⟨[(.fail, σ)], .fail, ?_, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr; cases hw
      · intro v
        simp [values, NeedScopeComp.denoteRel]
  | emit e b₁ ih =>
      obtain ⟨L, hD, hCells, hEx, hC⟩ := ih depth (σ.emit e) ρ hEnv hLookup
      exact ⟨L, .emit hD, hCells, hEx, hC⟩
  | seqBool b₁ k ih₁ ihk =>
      obtain ⟨L₁, hD₁, hCells₁, hEx₁, hC₁⟩ := ih₁ depth σ ρ hEnv hLookup
      have hBoolL₁ : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true := by
        intro r hr w hw
        obtain ⟨b₀, hb₀⟩ := hEx₁ r hr w hw
        cases b₀
        · exact Or.inl hb₀
        · exact Or.inr hb₀
      obtain ⟨L, hD_seqK, hCells_L, hEx_L, hCount_L⟩ :=
        derives_seqK_bool_gen
          ((k false).toCompAt (depth + 1))
          ((k true).toCompAt (depth + 1))
          (fun v => (k false).denoteRel Nat none v + (k false).denoteRel Nat (some a₀) v)
          (fun v => (k true).denoteRel Nat none v + (k true).denoteRel Nat (some a₀) v)
          σ.cells ρ L₁ hCells₁ hBoolL₁
          (fun σ' hσ' => by
            have hLookup' : σ'.cells[ℓ]? = some c := by rw [hσ']; exact hLookup
            obtain ⟨L_f, hDf, hCf, hExf, hCntf⟩ :=
              ihk false (depth + 1) σ' (GroundTy.encodeVal (G := .bool) false :: ρ)
                (by simpa using hEnv) hLookup'
            refine ⟨L_f, hDf, ?_, hExf, hCntf⟩
            intro r hr; rw [hCf r hr, hσ'])
          (fun σ' hσ' => by
            have hLookup' : σ'.cells[ℓ]? = some c := by rw [hσ']; exact hLookup
            obtain ⟨L_t, hDt, hCt, hExt, hCntt⟩ :=
              ihk true (depth + 1) σ' (GroundTy.encodeVal (G := .bool) true :: ρ)
                (by simpa using hEnv) hLookup'
            refine ⟨L_t, hDt, ?_, hExt, hCntt⟩
            intro r hr; rw [hCt r hr, hσ'])
      refine ⟨L, .seq hD₁ hD_seqK, hCells_L, hEx_L, ?_⟩
      intro v
      rw [hCount_L v, hC₁ false, hC₁ true, denoteRel_seqBool_done_sum]

/-- First-force commitment lemma preserving all cell slots `j > ℓ`:
running `commitK ℓ` over a producer result list `L_prod` where every branch has
cell `c₀` at `ℓ`, preserves `cells₁[j]?` for all `j > ℓ`, and returns encoded Booleans
produces a committed result list `L_commit` that preserves `cells₁[j]?` for all `j > ℓ`
and commits `.done w` at cell `ℓ` on every successful branch. -/
theorem derives_commitK_bool_ge {P : Program} (ℓ : Nat) (c₀ : Suspension)
    (cells₁ : List Suspension)
    (L_prod : List Result)
    (hCell_at : ∀ r ∈ L_prod, r.2.cells[ℓ]? = some c₀)
    (hCells_gt : ∀ r ∈ L_prod, ∀ j > ℓ, r.2.cells[j]? = cells₁[j]?)
    (hBool : ∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
      w = GroundTy.encodeVal (G := .bool) false ∨
      w = GroundTy.encodeVal (G := .bool) true) :
    ∃ L_commit : List Result,
      Derives P (.commitK ℓ L_prod) L_commit ∧
      values L_commit = values L_prod ∧
      (∀ r ∈ L_commit, ∀ j > ℓ, r.2.cells[j]? = cells₁[j]?) ∧
      (∀ r ∈ L_commit, ∀ w, r.1 = .ok w →
        (w = GroundTy.encodeVal (G := .bool) false ∨
         w = GroundTy.encodeVal (G := .bool) true) ∧
        r.2.cells[ℓ]? = some { c₀ with memo := .done w }) := by
  induction L_prod with
  | nil =>
      refine ⟨[], .commitNil, rfl, ?_, ?_⟩
      · intro r hr; cases hr
      · intro r hr; cases hr
  | cons r rest ih =>
      rcases r with ⟨o, σ⟩
      have hAt_rest : ∀ r ∈ rest, r.2.cells[ℓ]? = some c₀ :=
        fun r hr => hCell_at r (List.mem_cons_of_mem _ hr)
      have hGt_rest : ∀ r ∈ rest, ∀ j > ℓ, r.2.cells[j]? = cells₁[j]? :=
        fun r hr => hCells_gt r (List.mem_cons_of_mem _ hr)
      have hBool_rest : ∀ r ∈ rest, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true :=
        fun r hr => hBool r (List.mem_cons_of_mem _ hr)
      obtain ⟨L_rest, hDer_rest, hVals_rest, hGt_Lrest, hPost_rest⟩ :=
        ih hAt_rest hGt_rest hBool_rest
      have hσ_gt : ∀ j > ℓ, σ.cells[j]? = cells₁[j]? :=
        hCells_gt (o, σ) List.mem_cons_self
      cases o with
      | fail =>
          refine ⟨(.fail, σ.setMemo ℓ .pending) :: L_rest, .commitStop rfl hDer_rest, ?_, ?_, ?_⟩
          · simpa [values] using hVals_rest
          · intro r hr j hj
            rcases List.mem_cons.mp hr with rfl | hr'
            · rw [cells_setMemo_getElem?_ne σ ℓ j .pending (Nat.ne_of_lt hj)]
              exact hσ_gt j hj
            · exact hGt_Lrest r hr' j hj
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hPost_rest r hr' w hw
      | blackhole =>
          refine ⟨(.blackhole, σ.setMemo ℓ .pending) :: L_rest, .commitStop rfl hDer_rest, ?_, ?_, ?_⟩
          · simpa [values] using hVals_rest
          · intro r hr j hj
            rcases List.mem_cons.mp hr with rfl | hr'
            · rw [cells_setMemo_getElem?_ne σ ℓ j .pending (Nat.ne_of_lt hj)]
              exact hσ_gt j hj
            · exact hGt_Lrest r hr' j hj
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hPost_rest r hr' w hw
      | ok w =>
          have hw := hBool (.ok w, σ) List.mem_cons_self w rfl
          have hσ_at : σ.cells[ℓ]? = some c₀ := hCell_at (.ok w, σ) List.mem_cons_self
          have hw_cell : w.isCell = false := by
            rcases hw with rfl | rfl <;> rfl
          have hWhnf :
              Derives P (.forceVal (σ.setMemo ℓ (.done w)) w)
                [(.ok w, σ.setMemo ℓ (.done w))] :=
            .forceWhnf hw_cell
          refine ⟨(.ok w, σ.setMemo ℓ (.done w)) :: L_rest,
            .commitOk hWhnf hDer_rest, ?_, ?_, ?_⟩
          · simpa [values] using hVals_rest
          · intro r hr j hj
            rcases List.mem_cons.mp hr with rfl | hr'
            · rw [cells_setMemo_getElem?_ne σ ℓ j (.done w) (Nat.ne_of_lt hj)]
              exact hσ_gt j hj
            · exact hGt_Lrest r hr' j hj
          · intro r hr w' hw'
            rcases List.mem_cons.mp hr with rfl | hr'
            · injection hw' with hw_eq
              subst hw_eq
              exact ⟨hw, cells_setMemo_getElem?_eq σ ℓ c₀ (.done w) hσ_at⟩
            · exact hPost_rest r hr' w' hw'

/-- Indicator on `(w, σ')` testing `w = encodeVal v` and `σ'.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩`. -/
def indPending {G : GroundTy} (ℓ : Nat) (code_p : Comp) (ρ₀ : List (Val Nat))
    (v : G.Web) (w : Val Nat) (σ' : Store) : Nat :=
  if w = GroundTy.encodeVal v ∧ σ'.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ then 1 else 0

/-- Indicator on `(w, σ')` testing `w = encodeVal v` and
`σ'.cells[ℓ]? = some ⟨code_p, ρ₀, .done (encodeVal a)⟩`. -/
def indDone {G : GroundTy} (ℓ : Nat) (code_p : Comp) (ρ₀ : List (Val Nat))
    (a : Bool) (v : G.Web) (w : Val Nat) (σ' : Store) : Nat :=
  if w = GroundTy.encodeVal v ∧
     σ'.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩ then 1 else 0

/-- Partition of `(values L).count (encodeVal v)` into `indPending` and `indDone false` + `indDone true`
whenever every successful branch in `L` has cell `ℓ` either `.pending` or `.done (encodeVal a)`. -/
theorem values_count_eq_indPending_add_indDone {G : GroundTy}
    (ℓ : Nat) (code_p : Comp) (ρ₀ : List (Val Nat)) (L : List Result) (v : G.Web)
    (hDisj : ∀ r ∈ L, ∀ w, r.1 = .ok w →
      r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ ∨
      ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩) :
    (values L).count (GroundTy.encodeVal v) =
      resultSum L (indPending ℓ code_p ρ₀ v) +
      (resultSum L (indDone ℓ code_p ρ₀ false v) +
       resultSum L (indDone ℓ code_p ρ₀ true v)) := by
  rw [← resultSum_add, ← resultSum_add, ← resultSum_indicator_eq_values_count]
  refine resultSum_congr_mem fun r hr w hw => ?_
  dsimp [indPending, indDone]
  rcases hDisj r hr w hw with hP | ⟨a, hD⟩
  · rw [hP]
    by_cases hwv : w = GroundTy.encodeVal v <;> simp [hwv]
  · rw [hD]
    cases a <;>
    · by_cases hwv : w = GroundTy.encodeVal v <;>
      simp [hwv, GroundTy.encodeVal, symFalse, symTrue]

/-- Algebraic identity for `NeedScopeComp.denoteRel` across `seqBool` on `none` (unforced path). -/
theorem denoteRel_seqBool_pending_none {G : GroundTy}
    (b₁ : NeedScopeComp .bool) (k : Bool → NeedScopeComp G) (v : G.Web) :
    b₁.denoteRel Nat none false * (k false).denoteRel Nat none v +
    b₁.denoteRel Nat none true * (k true).denoteRel Nat none v =
    (NeedScopeComp.seqBool b₁ k).denoteRel Nat none v := by
  simp [NeedScopeComp.denoteRel, Fintype.sum_option, needComult]
  omega

/-- Algebraic identity for `NeedScopeComp.denoteRel` across `seqBool` on `some a` (forced path). -/
theorem denoteRel_seqBool_pending_some {G : GroundTy}
    (w_c : Bool → Nat) (b₁ : NeedScopeComp .bool) (k : Bool → NeedScopeComp G)
    (a : Bool) (v : G.Web) :
    (b₁.denoteRel Nat none false * (w_c a * (k false).denoteRel Nat (some a) v) +
     (w_c a * b₁.denoteRel Nat (some a) false) *
       ((k false).denoteRel Nat none v + (k false).denoteRel Nat (some a) v)) +
    (b₁.denoteRel Nat none true * (w_c a * (k true).denoteRel Nat (some a) v) +
     (w_c a * b₁.denoteRel Nat (some a) true) *
       ((k true).denoteRel Nat none v + (k true).denoteRel Nat (some a) v)) =
    w_c a * (NeedScopeComp.seqBool b₁ k).denoteRel Nat (some a) v := by
  have h1 : b₁.denoteRel Nat none false * (w_c a * (k false).denoteRel Nat (some a) v) =
      w_c a * b₁.denoteRel Nat none false * (k false).denoteRel Nat (some a) v := by
    rw [← Nat.mul_assoc, Nat.mul_comm _ (w_c a)]
  have h2 : b₁.denoteRel Nat none true * (w_c a * (k true).denoteRel Nat (some a) v) =
      w_c a * b₁.denoteRel Nat none true * (k true).denoteRel Nat (some a) v := by
    rw [← Nat.mul_assoc, Nat.mul_comm _ (w_c a)]
  rw [h1, h2]
  cases a <;>
  · simp [NeedScopeComp.denoteRel, Fintype.sum_option, needComult,
      Nat.mul_add, ← Nat.mul_assoc]
    omega

/-- Store-threading `seqK` lemma for `NeedScopeComp` in the pending phase:
threads a first-stage result list `L₁` (whose successful branches are either still
unforced with `r.2.cells = σ.cells` or committed to `.done (encodeVal a₀)` at `ℓ`)
into the continuation `k`. -/
theorem derives_needScope_pending_seqK {P : Program} {G : GroundTy}
    (ℓ depth : Nat) (code_p : Comp) (ρ₀ : List (Val Nat)) (w_c : Bool → Nat)
    (k : Bool → NeedScopeComp G)
    (σ : Store) (ρ : List (Val Nat)) (L₁ : List Result)
    (hPending_σ : σ.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩)
    (hEnv : ρ[depth]? = some (.need ℓ))
    (hGt₁ : ∀ r ∈ L₁, ∀ j > ℓ, r.2.cells[j]? = σ.cells[j]?)
    (hBranch₁ : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
      (w = GroundTy.encodeVal (G := .bool) false ∨
       w = GroundTy.encodeVal (G := .bool) true) ∧
      (r.2.cells = σ.cells ∨
       ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩))
    (ihk_pending : ∀ (mid : Bool) (σ' : Store),
      σ'.cells = σ.cells →
      ∃ L_k : List Result,
        Derives P (.eval σ' (GroundTy.encodeVal (G := .bool) mid :: ρ) ((k mid).toCompAt (depth + 1))) L_k ∧
        (∀ r ∈ L_k, ∀ j > ℓ, r.2.cells[j]? = σ'.cells[j]?) ∧
        (∀ r ∈ L_k, ∀ w, r.1 = .ok w →
          (∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
          (r.2.cells = σ'.cells ∨
           ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩)) ∧
        (∀ v : G.Web,
          resultSum L_k (indPending ℓ code_p ρ₀ v) = (k mid).denoteRel Nat none v) ∧
        (∀ (a : Bool) (v : G.Web),
          resultSum L_k (indDone ℓ code_p ρ₀ a v) = w_c a * (k mid).denoteRel Nat (some a) v)) :
    ∃ L : List Result,
      Derives P
        (.seqK
          (.caseCon (.var 0) symFalse 0 ((k false).toCompAt (depth + 1))
            (.caseCon (.var 0) symTrue 0 ((k true).toCompAt (depth + 1)) .fail))
          ρ L₁)
        L ∧
      (∀ r ∈ L, ∀ j > ℓ, r.2.cells[j]? = σ.cells[j]?) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        (∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
        (r.2.cells = σ.cells ∨
         ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩)) ∧
      (∀ v : G.Web,
        resultSum L (indPending ℓ code_p ρ₀ v) =
          resultSum L₁ (indPending (G := .bool) ℓ code_p ρ₀ false) * (k false).denoteRel Nat none v +
          resultSum L₁ (indPending (G := .bool) ℓ code_p ρ₀ true) * (k true).denoteRel Nat none v) ∧
      (∀ (a : Bool) (v : G.Web),
        resultSum L (indDone ℓ code_p ρ₀ a v) =
          (resultSum L₁ (indPending (G := .bool) ℓ code_p ρ₀ false) * (w_c a * (k false).denoteRel Nat (some a) v) +
           resultSum L₁ (indDone (G := .bool) ℓ code_p ρ₀ a false) *
             ((k false).denoteRel Nat none v + (k false).denoteRel Nat (some a) v)) +
          (resultSum L₁ (indPending (G := .bool) ℓ code_p ρ₀ true) * (w_c a * (k true).denoteRel Nat (some a) v) +
           resultSum L₁ (indDone (G := .bool) ℓ code_p ρ₀ a true) *
             ((k true).denoteRel Nat none v + (k true).denoteRel Nat (some a) v))) := by
  induction L₁ with
  | nil =>
      refine ⟨[], .seqKNil, ?_, ?_, ?_, ?_⟩
      · intro r hr; cases hr
      · intro r hr; cases hr
      · intro v; simp [resultSum]
      · intro a v; simp [resultSum]
  | cons r rest ih =>
      rcases r with ⟨o, σ'⟩
      have hGt_rest : ∀ r ∈ rest, ∀ j > ℓ, r.2.cells[j]? = σ.cells[j]? :=
        fun r hr => hGt₁ r (List.mem_cons_of_mem _ hr)
      have hBranch_rest : ∀ r ∈ rest, ∀ w, r.1 = .ok w →
          (w = GroundTy.encodeVal (G := .bool) false ∨
           w = GroundTy.encodeVal (G := .bool) true) ∧
          (r.2.cells = σ.cells ∨
           ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩) :=
        fun r hr => hBranch₁ r (List.mem_cons_of_mem _ hr)
      obtain ⟨L_rest, hDer_rest, hGt_Lrest, hBr_Lrest, hPend_rest, hDone_rest⟩ :=
        ih hGt_rest hBranch_rest
      have hσ'_gt : ∀ j > ℓ, σ'.cells[j]? = σ.cells[j]? :=
        hGt₁ (o, σ') List.mem_cons_self
      cases o with
      | fail =>
          refine ⟨(.fail, σ') :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_, ?_, ?_⟩
          · intro r hr j hj
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hσ'_gt j hj
            · exact hGt_Lrest r hr' j hj
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hBr_Lrest r hr' w hw
          · intro v; simpa [resultSum] using hPend_rest v
          · intro a v; simpa [resultSum] using hDone_rest a v
      | blackhole =>
          refine ⟨(.blackhole, σ') :: L_rest, .seqKStop rfl hDer_rest, ?_, ?_, ?_, ?_⟩
          · intro r hr j hj
            rcases List.mem_cons.mp hr with rfl | hr'
            · exact hσ'_gt j hj
            · exact hGt_Lrest r hr' j hj
          · intro r hr w hw
            rcases List.mem_cons.mp hr with rfl | hr'
            · cases hw
            · exact hBr_Lrest r hr' w hw
          · intro v; simpa [resultSum] using hPend_rest v
          · intro a v; simpa [resultSum] using hDone_rest a v
      | ok w =>
          obtain ⟨hw_bool, hState⟩ := hBranch₁ (.ok w, σ') List.mem_cons_self w rfl
          -- Establish continuation evaluation for mid : Bool in σ'
          have hCont : ∀ (mid : Bool), w = GroundTy.encodeVal (G := .bool) mid →
              ∃ L_k : List Result,
                Derives P
                  (.eval σ' (GroundTy.encodeVal (G := .bool) mid :: ρ)
                    (.caseCon (.var 0) symFalse 0 ((k false).toCompAt (depth + 1))
                      (.caseCon (.var 0) symTrue 0 ((k true).toCompAt (depth + 1)) .fail)))
                  L_k ∧
                (∀ r ∈ L_k, ∀ j > ℓ, r.2.cells[j]? = σ.cells[j]?) ∧
                (∀ r ∈ L_k, ∀ w', r.1 = .ok w' →
                  (∃ v₀ : G.Web, w' = GroundTy.encodeVal v₀) ∧
                  (r.2.cells = σ.cells ∨
                   ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩)) ∧
                (∀ v : G.Web,
                  resultSum L_k (indPending ℓ code_p ρ₀ v) =
                    indPending (G := .bool) ℓ code_p ρ₀ mid w σ' * (k mid).denoteRel Nat none v) ∧
                (∀ (a : Bool) (v : G.Web),
                  resultSum L_k (indDone ℓ code_p ρ₀ a v) =
                    indPending (G := .bool) ℓ code_p ρ₀ mid w σ' * (w_c a * (k mid).denoteRel Nat (some a) v) +
                    indDone (G := .bool) ℓ code_p ρ₀ a mid w σ' *
                      ((k mid).denoteRel Nat none v + (k mid).denoteRel Nat (some a) v)) := by
            intro mid hmid
            subst hmid
            rcases hState with hCells_eq | ⟨a₀, hDone_a₀⟩
            · -- Subcase 1: σ' is still pending (`σ'.cells = σ.cells`)
              obtain ⟨L_k, hDk, hGtk, hBrk, hPendk, hDonek⟩ := ihk_pending mid σ' hCells_eq
              have hCase :
                  Derives P
                    (.eval σ' (GroundTy.encodeVal (G := .bool) mid :: ρ)
                      (.caseCon (.var 0) symFalse 0 ((k false).toCompAt (depth + 1))
                        (.caseCon (.var 0) symTrue 0 ((k true).toCompAt (depth + 1)) .fail)))
                    L_k := by
                cases mid
                · exact .caseConHit (args := []) rfl hDk
                · exact .caseConMiss rfl (.caseConHit (args := []) rfl hDk)
              have hLookup_σ' : σ'.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ := by
                rw [hCells_eq]; exact hPending_σ
              have hIndP : indPending (G := .bool) ℓ code_p ρ₀ mid (GroundTy.encodeVal (G := .bool) mid) σ' = 1 := by
                simp [indPending, hLookup_σ']
              have hIndD (a : Bool) :
                  indDone (G := .bool) ℓ code_p ρ₀ a mid (GroundTy.encodeVal (G := .bool) mid) σ' = 0 := by
                simp [indDone, hLookup_σ']
              refine ⟨L_k, hCase, ?_, ?_, ?_, ?_⟩
              · intro r hr j hj
                rw [hGtk r hr j hj, hCells_eq]
              · intro r hr w' hw'
                obtain ⟨hEx, hSt⟩ := hBrk r hr w' hw'
                rw [hCells_eq] at hSt
                exact ⟨hEx, hSt⟩
              · intro v
                rw [hPendk v, hIndP, Nat.one_mul]
              · intro a v
                rw [hDonek a v, hIndP, hIndD a, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
            · -- Subcase 2: σ' is already committed to `a₀` (`hDone_a₀`)
              have hEnv' : (GroundTy.encodeVal (G := .bool) mid :: ρ)[depth + 1]? = some (.need ℓ) := by
                simpa using hEnv
              obtain ⟨L_k, hDk, hCellsk, hExk, hCountk⟩ :=
                derives_needScope_done (k mid) P ℓ a₀ (depth + 1)
                  σ' (GroundTy.encodeVal (G := .bool) mid :: ρ)
                  ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a₀)⟩
                  hEnv' hDone_a₀ rfl
              have hCase :
                  Derives P
                    (.eval σ' (GroundTy.encodeVal (G := .bool) mid :: ρ)
                      (.caseCon (.var 0) symFalse 0 ((k false).toCompAt (depth + 1))
                        (.caseCon (.var 0) symTrue 0 ((k true).toCompAt (depth + 1)) .fail)))
                    L_k := by
                cases mid
                · exact .caseConHit (args := []) rfl hDk
                · exact .caseConMiss rfl (.caseConHit (args := []) rfl hDk)
              have hIndP : indPending (G := .bool) ℓ code_p ρ₀ mid (GroundTy.encodeVal (G := .bool) mid) σ' = 0 := by
                simp [indPending, hDone_a₀]
              refine ⟨L_k, hCase, ?_, ?_, ?_, ?_⟩
              · intro r hr j hj
                rw [hCellsk r hr]
                exact hσ'_gt j hj
              · intro r hr w' hw'
                refine ⟨hExk r hr w' hw', Or.inr ⟨a₀, ?_⟩⟩
                rw [hCellsk r hr]
                exact hDone_a₀
              · intro v
                rw [hIndP, Nat.zero_mul]
                refine resultSum_eq_zero fun r hr w' _ => ?_
                have hCell_r : r.2.cells[ℓ]? =
                    some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a₀)⟩ := by
                  rw [hCellsk r hr]; exact hDone_a₀
                simp [indPending, hCell_r]
              · intro a v
                rw [hIndP, Nat.zero_mul, Nat.zero_add]
                by_cases ha : a = a₀
                · subst ha
                  have hIndD : indDone (G := .bool) ℓ code_p ρ₀ a mid (GroundTy.encodeVal (G := .bool) mid) σ' = 1 := by
                    simp [indDone, hDone_a₀]
                  rw [hIndD, Nat.one_mul, ← hCountk v, ← resultSum_indicator_eq_values_count]
                  refine resultSum_congr_mem fun r hr w' _ => ?_
                  have hCell_r : r.2.cells[ℓ]? =
                      some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩ := by
                    rw [hCellsk r hr]; exact hDone_a₀
                  simp [indDone, hCell_r]
                · have hne_val : GroundTy.encodeVal (G := .bool) a₀ ≠
                      GroundTy.encodeVal (G := .bool) a :=
                    fun heq => ha (GroundTy.encodeVal_injective heq).symm
                  have hIndD : indDone (G := .bool) ℓ code_p ρ₀ a mid (GroundTy.encodeVal (G := .bool) mid) σ' = 0 := by
                    simp [indDone, hDone_a₀, hne_val]
                  rw [hIndD, Nat.zero_mul]
                  refine resultSum_eq_zero fun r hr w' _ => ?_
                  have hCell_r : r.2.cells[ℓ]? =
                      some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a₀)⟩ := by
                    rw [hCellsk r hr]; exact hDone_a₀
                  simp [indDone, hCell_r, hne_val]
          rcases hw_bool with rfl | rfl
          · obtain ⟨L_k, hCase, hGtk, hBrk, hPendk, hDonek⟩ := hCont false rfl
            have hOtherP : indPending (G := .bool) ℓ code_p ρ₀ true (GroundTy.encodeVal (G := .bool) false) σ' = 0 := by
              simp [indPending, GroundTy.encodeVal, symFalse, symTrue]
            have hOtherD (a : Bool) : indDone (G := .bool) ℓ code_p ρ₀ a true (GroundTy.encodeVal (G := .bool) false) σ' = 0 := by
              simp [indDone, GroundTy.encodeVal, symFalse, symTrue]
            refine ⟨L_k ++ L_rest, .seqKOk hCase hDer_rest, ?_, ?_, ?_, ?_⟩
            · intro r hr j hj
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hGtk r hr₁ j hj
              · exact hGt_Lrest r hr₂ j hj
            · intro r hr w' hw'
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hBrk r hr₁ w' hw'
              · exact hBr_Lrest r hr₂ w' hw'
            · intro v
              rw [resultSum_append, hPendk v, hPend_rest v]
              simp only [resultSum_ok, hOtherP, Nat.add_mul, Nat.zero_mul]
              omega
            · intro a v
              rw [resultSum_append, hDonek a v, hDone_rest a v]
              simp only [resultSum_ok, hOtherP, hOtherD a, Nat.add_mul, Nat.zero_mul]
              omega
          · obtain ⟨L_k, hCase, hGtk, hBrk, hPendk, hDonek⟩ := hCont true rfl
            have hOtherP : indPending (G := .bool) ℓ code_p ρ₀ false (GroundTy.encodeVal (G := .bool) true) σ' = 0 := by
              simp [indPending, GroundTy.encodeVal, symFalse, symTrue]
            have hOtherD (a : Bool) : indDone (G := .bool) ℓ code_p ρ₀ a false (GroundTy.encodeVal (G := .bool) true) σ' = 0 := by
              simp [indDone, GroundTy.encodeVal, symFalse, symTrue]
            refine ⟨L_k ++ L_rest, .seqKOk hCase hDer_rest, ?_, ?_, ?_, ?_⟩
            · intro r hr j hj
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hGtk r hr₁ j hj
              · exact hGt_Lrest r hr₂ j hj
            · intro r hr w' hw'
              rcases List.mem_append.mp hr with hr₁ | hr₂
              · exact hBrk r hr₁ w' hw'
              · exact hBr_Lrest r hr₂ w' hw'
            · intro v
              rw [resultSum_append, hPendk v, hPend_rest v]
              simp only [resultSum_ok, hOtherP, Nat.add_mul, Nat.zero_mul]
              omega
            · intro a v
              rw [resultSum_append, hDonek a v, hDone_rest a v]
              simp only [resultSum_ok, hOtherP, hOtherD a, Nat.add_mul, Nat.zero_mul]
              omega

/-- **Phase 2 (Pending Phase, `derives_needScope_pending`):**
For any `b : NeedScopeComp G`, when cell `ℓ` is bound at `ρ[depth]? = some (.need ℓ)`
and its initial store entry in `σ` is `⟨code_p, ρ₀, .pending⟩` for a Boolean producer
`code_p` with distribution `w_c : Bool → Nat` that preserves cells `≥ ℓ`:
evaluating `b.toCompAt depth` derives a complete result list `L` that
1. preserves all cells `j > ℓ` on every branch (`r.2.cells[j]? = σ.cells[j]?`),
2. leaves `r.2.cells = σ.cells` on unforced branches (multiplicity `b.denoteRel Nat none v`)
   and commits `.done (encodeVal a)` at cell `ℓ` on forced branches
   (multiplicity `w_c a * b.denoteRel Nat (some a) v`), and
3. produces each `v : G.Web` with total multiplicity
   `NeedScopeComp.denoteNeedClosed Nat w_c b v = bindNeed w_c (b.denoteRel Nat) v`. -/
theorem derives_needScope_pending {G : GroundTy} (b : NeedScopeComp G)
    (P : Program) (ℓ : Nat) (code_p : Comp) (ρ₀ : List (Val Nat)) (w_c : Bool → Nat)
    (cells₀ : List Suspension)
    (hPending₀ : cells₀[ℓ]? = some ⟨code_p, ρ₀, .pending⟩)
    (hProd : ∀ σ_eval : Store,
      (∀ j ≤ ℓ, σ_eval.cells[j]? = (cells₀.modify ℓ fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval ρ₀ code_p) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ ℓ, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = w_c a))
    (depth : Nat) (σ : Store) (ρ : List (Val Nat))
    (hCells_le : ∀ j ≤ ℓ, σ.cells[j]? = cells₀[j]?)
    (hEnv : ρ[depth]? = some (.need ℓ)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (b.toCompAt depth)) L ∧
      (∀ r ∈ L, ∀ j > ℓ, r.2.cells[j]? = σ.cells[j]?) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w →
        (∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
        (r.2.cells = σ.cells ∨
         ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩)) ∧
      (∀ v : G.Web,
        resultSum L (indPending ℓ code_p ρ₀ v) = b.denoteRel Nat none v) ∧
      (∀ (a : Bool) (v : G.Web),
        resultSum L (indDone ℓ code_p ρ₀ a v) = w_c a * b.denoteRel Nat (some a) v) := by
  induction b generalizing depth σ ρ with
  | ret v₀ =>
      have hLookup_σ : σ.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ := by
        rw [hCells_le ℓ (Nat.le_refl ℓ)]; exact hPending₀
      refine ⟨[(.ok (GroundTy.encodeVal v₀), σ)], ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [NeedScopeComp.toCompAt, GroundTy.eval_encodeVExp] using
          (Derives.ret (P := P) (σ := σ) (ρ := ρ) (v := GroundTy.encodeVExp v₀))
      · intro r hr j _
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr
        injection hw with hw'
        exact ⟨⟨v₀, hw'.symm⟩, Or.inl rfl⟩
      · intro v
        simp only [resultSum_ok, resultSum_nil, Nat.add_zero, indPending, hLookup_σ,
          and_true, NeedScopeComp.denoteRel, needCounit, Nat.one_mul]
        by_cases h : v₀ = v
        · subst h; simp
        · have hne : GroundTy.encodeVal v₀ ≠ GroundTy.encodeVal v :=
            fun heq => h (GroundTy.encodeVal_injective heq)
          simp [h, hne]
      · intro a v
        simp [resultSum_ok, resultSum_nil, indDone, hLookup_σ,
          NeedScopeComp.denoteRel, needCounit]
  | force =>
      have hLookup_σ : σ.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ := by
        rw [hCells_le ℓ (Nat.le_refl ℓ)]; exact hPending₀
      let σ₁ := σ.setMemo ℓ .evaluating
      have hσ₁_le : ∀ j ≤ ℓ,
          σ₁.cells[j]? = (cells₀.modify ℓ fun c => { c with memo := .evaluating })[j]? := by
        intro j hj
        simp only [σ₁, Store.setMemo, List.getElem?_modify]
        rw [hCells_le j hj]
      obtain ⟨L_prod, hD_prod, hGe_prod, hBool_prod, hCount_prod⟩ := hProd σ₁ hσ₁_le
      have hLookup_σ₁ : σ₁.cells[ℓ]? = some ⟨code_p, ρ₀, .evaluating⟩ :=
        cells_setMemo_getElem?_eq σ ℓ ⟨code_p, ρ₀, .pending⟩ .evaluating hLookup_σ
      have hAt_prod : ∀ r ∈ L_prod, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .evaluating⟩ := by
        intro r hr
        rw [hGe_prod r hr ℓ (Nat.le_refl ℓ)]
        exact hLookup_σ₁
      have hGt_prod : ∀ r ∈ L_prod, ∀ j > ℓ, r.2.cells[j]? = σ.cells[j]? := by
        intro r hr j hj
        rw [hGe_prod r hr j (Nat.le_of_lt hj)]
        exact cells_setMemo_getElem?_ne σ ℓ j .evaluating (Nat.ne_of_lt hj)
      obtain ⟨L₁, hD_commit, hVals_eq, hGt_L₁, hPost_L₁⟩ :=
        derives_commitK_bool_ge ℓ ⟨code_p, ρ₀, .evaluating⟩ σ.cells L_prod
          hAt_prod hGt_prod hBool_prod
      have hForceVal : Derives P (.forceVal σ ((VExp.var depth).eval ρ)) L₁ := by
        rw [vexp_eval_var_of_getElem? hEnv]
        exact .forcePending hLookup_σ rfl hD_prod hD_commit
      refine ⟨L₁, .force hForceVal, hGt_L₁, ?_, ?_, ?_⟩
      · intro r hr w hw
        obtain ⟨hw_bool, hCell_r⟩ := hPost_L₁ r hr w hw
        rcases hw_bool with rfl | rfl
        · exact ⟨⟨false, rfl⟩, Or.inr ⟨false, hCell_r⟩⟩
        · exact ⟨⟨true, rfl⟩, Or.inr ⟨true, hCell_r⟩⟩
      · intro v
        simp only [NeedScopeComp.denoteRel, forceNeedRel]
        refine resultSum_eq_zero fun r hr w hw => ?_
        obtain ⟨_, hCell_r⟩ := hPost_L₁ r hr w hw
        simp [indPending, hCell_r]
      · intro a v
        simp only [NeedScopeComp.denoteRel, forceNeedRel]
        by_cases hav : a = v
        · subst hav
          simp only [↓reduceIte, Nat.mul_one,
              ← hCount_prod a, ← hVals_eq, ← resultSum_indicator_eq_values_count]
          refine resultSum_congr_mem fun r hr w hw => ?_
          obtain ⟨_, hCell_r⟩ := hPost_L₁ r hr w hw
          dsimp [indDone]
          rw [hCell_r]
          by_cases hw_eq : w = GroundTy.encodeVal (G := .bool) a
          · subst hw_eq; simp
          · simp [hw_eq]
        · simp only [hav, ↓reduceIte, Nat.mul_zero]
          refine resultSum_eq_zero fun r hr w hw => ?_
          obtain ⟨_, hCell_r⟩ := hPost_L₁ r hr w hw
          dsimp [indDone]
          rw [hCell_r]
          by_cases hw_eq : w = GroundTy.encodeVal (G := .bool) v
          · subst hw_eq
            have hne_val : GroundTy.encodeVal (G := .bool) v ≠
                GroundTy.encodeVal (G := .bool) a :=
              fun heq => hav (GroundTy.encodeVal_injective heq).symm
            simp [hne_val]
          · simp [hw_eq]
  | choose b₁ b₂ ih₁ ih₂ =>
      obtain ⟨L₁, hD₁, hGt₁, hBr₁, hP₁, hDn₁⟩ := ih₁ depth σ ρ hCells_le hEnv
      obtain ⟨L₂, hD₂, hGt₂, hBr₂, hP₂, hDn₂⟩ := ih₂ depth σ ρ hCells_le hEnv
      refine ⟨L₁ ++ L₂, .choose hD₁ hD₂, ?_, ?_, ?_, ?_⟩
      · intro r hr j hj
        rcases List.mem_append.mp hr with hr₁ | hr₂
        · exact hGt₁ r hr₁ j hj
        · exact hGt₂ r hr₂ j hj
      · intro r hr w hw
        rcases List.mem_append.mp hr with hr₁ | hr₂
        · exact hBr₁ r hr₁ w hw
        · exact hBr₂ r hr₂ w hw
      · intro v
        rw [resultSum_append, hP₁ v, hP₂ v]
        rfl
      · intro a v
        rw [resultSum_append, hDn₁ a v, hDn₂ a v]
        simp only [NeedScopeComp.denoteRel, Nat.mul_add]
  | fail =>
      refine ⟨[(.fail, σ)], .fail, ?_, ?_, ?_, ?_⟩
      · intro r hr j _
        simp only [List.mem_singleton] at hr
        subst hr; rfl
      · intro r hr w hw
        simp only [List.mem_singleton] at hr
        subst hr; cases hw
      · intro v; simp [resultSum, NeedScopeComp.denoteRel]
      · intro a v; simp [resultSum, NeedScopeComp.denoteRel]
  | emit e b₁ ih =>
      obtain ⟨L, hD, hGt, hBr, hP, hDn⟩ := ih depth (σ.emit e) ρ hCells_le hEnv
      exact ⟨L, .emit hD, hGt, hBr, hP, hDn⟩
  | seqBool b₁ k ih₁ ihk =>
      have hLookup_σ : σ.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ := by
        rw [hCells_le ℓ (Nat.le_refl ℓ)]; exact hPending₀
      obtain ⟨L₁, hD₁, hGt₁, hBr₁, hP₁, hDn₁⟩ := ih₁ depth σ ρ hCells_le hEnv
      have hBranch₁ : ∀ r ∈ L₁, ∀ w, r.1 = .ok w →
          (w = GroundTy.encodeVal (G := .bool) false ∨
           w = GroundTy.encodeVal (G := .bool) true) ∧
          (r.2.cells = σ.cells ∨
           ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩) := by
        intro r hr w hw
        obtain ⟨⟨b₀, hb₀⟩, hSt⟩ := hBr₁ r hr w hw
        refine ⟨?_, hSt⟩
        cases b₀
        · exact Or.inl hb₀
        · exact Or.inr hb₀
      obtain ⟨L, hD_seqK, hGt_L, hBr_L, hPend_L, hDone_L⟩ :=
        derives_needScope_pending_seqK ℓ depth code_p ρ₀ w_c k σ ρ L₁
          hLookup_σ hEnv hGt₁ hBranch₁
          (fun mid σ' hσ' => by
            have hCells_le' : ∀ j ≤ ℓ, σ'.cells[j]? = cells₀[j]? := by
              intro j hj; rw [hσ']; exact hCells_le j hj
            exact ihk mid (depth + 1) σ' (GroundTy.encodeVal (G := .bool) mid :: ρ)
              hCells_le' (by simpa using hEnv))
      refine ⟨L, .seq hD₁ hD_seqK, hGt_L, hBr_L, ?_, ?_⟩
      · intro v
        rw [hPend_L v, hP₁ false, hP₁ true, denoteRel_seqBool_pending_none]
      · intro a v
        rw [hDone_L a v, hP₁ false, hP₁ true, hDn₁ a false, hDn₁ a true,
            denoteRel_seqBool_pending_some]

/-- **General Single-Cell Adequacy Theorem (`derives_needScope_adequacy`):**
For **every** finite Boolean producer `p : GroundComp .bool` and **every** body
`b : NeedScopeComp G` (with arbitrary control flow, branching, events, and any number
of `force` sites), `Comp.need p.toComp b.toComp` derives a complete result list `L`
under `CallTimeChoice.Derives` such that:
1. every successful outcome in `L` is an encoded value `encodeVal v₀` (`v₀ : G.Web`),
2. for every `v : G.Web`, the operational multiplicity `(values L).count (encodeVal v)`
   equals `NeedScopeComp.denoteNeedClosed Nat (p.denote Nat) b v`, and
3. by `denoteNeedClosed_eq_bindNeed`, this equals the `WeightedRelNeedModel` composition
   `bindNeed (p.denote Nat) (b.denoteRel Nat) v`. -/
theorem derives_needScope_adequacy {G : GroundTy}
    (p : GroundComp .bool) (b : NeedScopeComp G)
    (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (.need p.toComp b.toComp)) L ∧
      (∀ r ∈ L, ∀ j > σ.cells.length, r.2.cells[j]? = (σ.alloc p.toComp ρ).cells[j]?) ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          NeedScopeComp.denoteNeedClosed Nat (p.denote Nat) b v) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          bindNeed (p.denote Nat) (b.denoteRel Nat) v) := by
  let ℓ := σ.cells.length
  let σ₀ := σ.alloc p.toComp ρ
  have hPending₀ : σ₀.cells[ℓ]? = some ⟨p.toComp, ρ, .pending⟩ :=
    cells_alloc_getElem?_length σ p.toComp ρ
  have hProd : ∀ σ_eval : Store,
      (∀ j ≤ ℓ, σ_eval.cells[j]? = (σ₀.cells.modify ℓ fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval ρ p.toComp) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ ℓ, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = p.denote Nat a) := by
    intro σ_eval _
    obtain ⟨L_prod, hD_prod, hCells_prod, hEx_prod, hCount_prod⟩ :=
      GroundComp.derives_groundComp_adequacy p P σ_eval ρ
    refine ⟨L_prod, hD_prod, ?_, ?_, hCount_prod⟩
    · intro r hr j _
      rw [hCells_prod r hr]
    · intro r hr w hw
      obtain ⟨b₀, hb₀⟩ := hEx_prod r hr w hw
      cases b₀
      · exact Or.inl hb₀
      · exact Or.inr hb₀
  obtain ⟨L, hD_body, hGt_L, hBr_L, hPend_L, hDone_L⟩ :=
    derives_needScope_pending b P ℓ p.toComp ρ (p.denote Nat) σ₀.cells hPending₀ hProd
      0 σ₀ (.need ℓ :: ρ) (fun _ _ => rfl) rfl
  refine ⟨L, .need hD_body, hGt_L, ?_, ?_, ?_⟩
  · intro r hr w hw
    exact (hBr_L r hr w hw).1
  · intro v
    have hDisj : ∀ r ∈ L, ∀ w, r.1 = .ok w →
        r.2.cells[ℓ]? = some ⟨p.toComp, ρ, .pending⟩ ∨
        ∃ a : Bool, r.2.cells[ℓ]? = some ⟨p.toComp, ρ, .done (GroundTy.encodeVal (G := .bool) a)⟩ := by
      intro r hr w hw
      rcases (hBr_L r hr w hw).2 with hEq | hDone
      · left; rw [hEq]; exact hPending₀
      · right; exact hDone
    rw [values_count_eq_indPending_add_indDone ℓ p.toComp ρ L v hDisj,
        hPend_L v, hDone_L false v, hDone_L true v]
    simp only [NeedScopeComp.denoteNeedClosed, Fintype.sum_bool]
    omega
  · intro v
    rw [← NeedScopeComp.denoteNeedClosed_eq_bindNeed]
    have hDisj : ∀ r ∈ L, ∀ w, r.1 = .ok w →
        r.2.cells[ℓ]? = some ⟨p.toComp, ρ, .pending⟩ ∨
        ∃ a : Bool, r.2.cells[ℓ]? = some ⟨p.toComp, ρ, .done (GroundTy.encodeVal (G := .bool) a)⟩ := by
      intro r hr w hw
      rcases (hBr_L r hr w hw).2 with hEq | hDone
      · left; rw [hEq]; exact hPending₀
      · right; exact hDone
    rw [values_count_eq_indPending_add_indDone ℓ p.toComp ρ L v hDisj,
        hPend_L v, hDone_L false v, hDone_L true v]
    simp only [NeedScopeComp.denoteNeedClosed, Fintype.sum_bool]
    omega

/-- **General Dependent Two-Cell Chain Adequacy Theorem (`derives_need_twoCell_chain_adequacy`, Task 5c):**
For **every** ground producer `p₁ : GroundComp .bool` (cell $c_1$), **every** dependent
producer `p₂ : NeedScopeComp .bool` (cell $c_2$, which is in the scope of $c_1$ and may
`force` $c_1$ zero, one, or many times), and **every** body `b₂ : NeedScopeComp G`
(in the scope of $c_2$, which may `force` $c_2$ zero, one, or many times):
`Comp.need p₁.toComp (.need p₂.toComp b₂.toComp)` derives a complete result list `L`
under `CallTimeChoice.Derives` whose exact answer multiplicity for every `v : G.Web` is
`bindNeed (bindNeed (p₁.denote Nat) (p₂.denoteRel Nat)) (b₂.denoteRel Nat) v`! -/
theorem derives_need_twoCell_chain_adequacy {G : GroundTy}
    (p₁ : GroundComp .bool) (p₂ : NeedScopeComp .bool) (b₂ : NeedScopeComp G)
    (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (.need p₁.toComp (.need p₂.toComp b₂.toComp))) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          bindNeed (bindNeed (p₁.denote Nat) (p₂.denoteRel Nat)) (b₂.denoteRel Nat) v) := by
  let ℓ₁ := σ.cells.length
  let σ₁ := σ.alloc p₁.toComp ρ
  let ρ₁ := Val.need ℓ₁ :: ρ
  let ℓ₂ := σ₁.cells.length
  let σ₂ := σ₁.alloc p₂.toComp ρ₁
  let ρ₂ := Val.need ℓ₂ :: ρ₁
  have hℓ₁_lt_ℓ₂ : ℓ₁ < ℓ₂ := by
    simp [ℓ₁, ℓ₂, σ₁, Store.alloc]
  have hPending₁ : σ₁.cells[ℓ₁]? = some ⟨p₁.toComp, ρ, .pending⟩ :=
    cells_alloc_getElem?_length σ p₁.toComp ρ
  have hPending₂ : σ₂.cells[ℓ₂]? = some ⟨p₂.toComp, ρ₁, .pending⟩ :=
    cells_alloc_getElem?_length σ₁ p₂.toComp ρ₁
  -- Cell 1 producer obligation
  have hProd₁ : ∀ σ_eval : Store,
      (∀ j ≤ ℓ₁, σ_eval.cells[j]? = (σ₁.cells.modify ℓ₁ fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval ρ p₁.toComp) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ ℓ₁, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = p₁.denote Nat a) := by
    intro σ_eval _
    obtain ⟨L_prod, hD_prod, hCells_prod, hEx_prod, hCount_prod⟩ :=
      GroundComp.derives_groundComp_adequacy p₁ P σ_eval ρ
    refine ⟨L_prod, hD_prod, ?_, ?_, hCount_prod⟩
    · intro r hr j _
      rw [hCells_prod r hr]
    · intro r hr w hw
      obtain ⟨b₀, hb₀⟩ := hEx_prod r hr w hw
      cases b₀
      · exact Or.inl hb₀
      · exact Or.inr hb₀
  -- Cell 2 producer obligation (derived from `derives_needScope_pending` applied to `p₂` at cell `ℓ₁`!)
  let w₂ : Bool → Nat := bindNeed (p₁.denote Nat) (p₂.denoteRel Nat)
  have hProd₂ : ∀ σ_eval : Store,
      (∀ j ≤ ℓ₂, σ_eval.cells[j]? = (σ₂.cells.modify ℓ₂ fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval ρ₁ p₂.toComp) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ ℓ₂, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = w₂ a) := by
    intro σ_eval hσ_eval_le
    have hσ_eval_le₁ : ∀ j ≤ ℓ₁, σ_eval.cells[j]? = σ₁.cells[j]? := by
      intro j hj
      have hj_lt_ℓ₂ : j < ℓ₂ := Nat.lt_of_le_of_lt hj hℓ₁_lt_ℓ₂
      rw [hσ_eval_le j (Nat.le_of_lt hj_lt_ℓ₂)]
      have hne : ℓ₂ ≠ j := Nat.ne_of_gt hj_lt_ℓ₂
      simp only [List.getElem?_modify, hne, ↓reduceIte, Option.map_eq_map, Option.map_id']
      exact cells_alloc_getElem?_lt σ₁ p₂.toComp ρ₁ hj_lt_ℓ₂
    obtain ⟨L_prod, hD_p₂, hGt_p₂, hBr_p₂, hPend_p₂, hDone_p₂⟩ :=
      derives_needScope_pending p₂ P ℓ₁ p₁.toComp ρ (p₁.denote Nat) σ₁.cells hPending₁ hProd₁
        0 σ_eval ρ₁ hσ_eval_le₁ rfl
    refine ⟨L_prod, hD_p₂, ?_, ?_, ?_⟩
    · intro r hr j hj
      exact hGt_p₂ r hr j (Nat.lt_of_lt_of_le hℓ₁_lt_ℓ₂ hj)
    · intro r hr w hw
      obtain ⟨⟨b₀, hb₀⟩, _⟩ := hBr_p₂ r hr w hw
      cases b₀
      · exact Or.inl hb₀
      · exact Or.inr hb₀
    · intro a
      have hDisj : ∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          r.2.cells[ℓ₁]? = some ⟨p₁.toComp, ρ, .pending⟩ ∨
          ∃ a₁ : Bool, r.2.cells[ℓ₁]? = some ⟨p₁.toComp, ρ, .done (GroundTy.encodeVal (G := .bool) a₁)⟩ := by
        intro r hr w hw
        rcases (hBr_p₂ r hr w hw).2 with hEq | hDone
        · left; rw [hEq, hσ_eval_le₁ ℓ₁ (Nat.le_refl ℓ₁)]; exact hPending₁
        · right; exact hDone
      rw [values_count_eq_indPending_add_indDone (G := .bool) ℓ₁ p₁.toComp ρ L_prod a hDisj,
          hPend_p₂ a, hDone_p₂ false a, hDone_p₂ true a]
      simp only [w₂, bindNeed, Fintype.sum_bool]
      omega
  -- Now evaluate `b₂` at cell `ℓ₂` using `derives_needScope_pending`!
  obtain ⟨L, hD_b₂, _, hBr_b₂, hPend_b₂, hDone_b₂⟩ :=
    derives_needScope_pending b₂ P ℓ₂ p₂.toComp ρ₁ w₂ σ₂.cells hPending₂ hProd₂
      0 σ₂ ρ₂ (fun _ _ => rfl) rfl
  refine ⟨L, .need (.need hD_b₂), ?_, ?_⟩
  · intro r hr w hw
    exact (hBr_b₂ r hr w hw).1
  · intro v
    have hDisj : ∀ r ∈ L, ∀ w, r.1 = .ok w →
        r.2.cells[ℓ₂]? = some ⟨p₂.toComp, ρ₁, .pending⟩ ∨
        ∃ a₂ : Bool, r.2.cells[ℓ₂]? = some ⟨p₂.toComp, ρ₁, .done (GroundTy.encodeVal (G := .bool) a₂)⟩ := by
      intro r hr w hw
      rcases (hBr_b₂ r hr w hw).2 with hEq | hDone
      · left; rw [hEq]; exact hPending₂
      · right; exact hDone
    rw [values_count_eq_indPending_add_indDone ℓ₂ p₂.toComp ρ₁ L v hDisj,
        hPend_b₂ v, hDone_b₂ false v, hDone_b₂ true v]
    simp only [w₂, bindNeed, Fintype.sum_bool]
    omega

/-- Compile an arbitrary $n$-cell telescope of dependent `NeedScopeComp .bool` producers
`ps : List (NeedScopeComp .bool)` followed by a final body `b : NeedScopeComp G`:
each `p ∈ ps` is allocated by `Comp.need p.toComp (...)` in the scope of the previous cell. -/
def compileNeedChainAux {G : GroundTy} :
    List (NeedScopeComp .bool) → NeedScopeComp G → Comp
  | [], b => b.toComp
  | p :: ps, b => .need p.toComp (compileNeedChainAux ps b)

/-- Top-level compilation of an initial ground producer `p₀ : GroundComp .bool`,
a telescope `ps : List (NeedScopeComp .bool)` of dependent cell producers, and
a final body `b : NeedScopeComp G`. -/
def compileNeedChain {G : GroundTy} (p₀ : GroundComp .bool)
    (ps : List (NeedScopeComp .bool)) (b : NeedScopeComp G) : Comp :=
  .need p₀.toComp (compileNeedChainAux ps b)

/-- Compositional `Rel_S` weight distribution after a telescope `ps` of dependent
`NeedScopeComp .bool` cell producers starting from initial producer distribution `w₀`. -/
def denoteNeedChain (S : Type*) [CommSemiring S] (w₀ : WState S Bool) :
    List (NeedScopeComp .bool) → WState S Bool
  | [] => w₀
  | p :: ps => denoteNeedChain S (bindNeed w₀ (p.denoteRel S)) ps

/-- Inductive telescope step for an arbitrary chain `ps : List (NeedScopeComp .bool)`
starting from an already-allocated pending cell `ℓ` with producer `(code_p, ρ₀)` and
weight distribution `w_c`. -/
theorem derives_needChainAux_adequacy {G : GroundTy}
    (ps : List (NeedScopeComp .bool)) (b : NeedScopeComp G)
    (P : Program) (ℓ : Nat) (code_p : Comp) (ρ₀ : List (Val Nat)) (w_c : Bool → Nat)
    (σ : Store) (ρ : List (Val Nat))
    (hLen : ℓ < σ.cells.length)
    (hPending : σ.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩)
    (hEnv : ρ[0]? = some (.need ℓ))
    (hProd : ∀ σ_eval : Store,
      (∀ j ≤ ℓ, σ_eval.cells[j]? = (σ.cells.modify ℓ fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval ρ₀ code_p) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ ℓ, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = w_c a)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (compileNeedChainAux ps b)) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          bindNeed (denoteNeedChain Nat w_c ps) (b.denoteRel Nat) v) := by
  induction ps generalizing ℓ code_p ρ₀ w_c σ ρ with
  | nil =>
      obtain ⟨L, hD, _, hBr, hPend, hDone⟩ :=
        derives_needScope_pending b P ℓ code_p ρ₀ w_c σ.cells hPending hProd
          0 σ ρ (fun _ _ => rfl) hEnv
      refine ⟨L, hD, ?_, ?_⟩
      · intro r hr w hw
        exact (hBr r hr w hw).1
      · intro v
        have hDisj : ∀ r ∈ L, ∀ w, r.1 = .ok w →
            r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ ∨
            ∃ a : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a)⟩ := by
          intro r hr w hw
          rcases (hBr r hr w hw).2 with hEq | hDone_r
          · left; rw [hEq]; exact hPending
          · right; exact hDone_r
        rw [values_count_eq_indPending_add_indDone ℓ code_p ρ₀ L v hDisj,
            hPend v, hDone false v, hDone true v]
        simp only [denoteNeedChain, bindNeed, Fintype.sum_bool]
        omega
  | cons p₁ ps' ih =>
      let ℓ₁ := σ.cells.length
      let σ₁ := σ.alloc p₁.toComp ρ
      let ρ₁ := Val.need ℓ₁ :: ρ
      have hLen₁ : ℓ₁ < σ₁.cells.length := by
        simp [ℓ₁, σ₁, Store.alloc]
      have hPending₁ : σ₁.cells[ℓ₁]? = some ⟨p₁.toComp, ρ, .pending⟩ :=
        cells_alloc_getElem?_length σ p₁.toComp ρ
      let w₁ : Bool → Nat := bindNeed w_c (p₁.denoteRel Nat)
      have hProd₁ : ∀ σ_eval : Store,
          (∀ j ≤ ℓ₁, σ_eval.cells[j]? = (σ₁.cells.modify ℓ₁ fun c => { c with memo := .evaluating })[j]?) →
          ∃ L_prod : List Result,
            Derives P (.eval σ_eval ρ p₁.toComp) L_prod ∧
            (∀ r ∈ L_prod, ∀ j ≥ ℓ₁, r.2.cells[j]? = σ_eval.cells[j]?) ∧
            (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
              w = GroundTy.encodeVal (G := .bool) false ∨
              w = GroundTy.encodeVal (G := .bool) true) ∧
            (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = w₁ a) := by
        intro σ_eval hσ_eval_le
        have hσ_eval_le₀ : ∀ j ≤ ℓ, σ_eval.cells[j]? = σ.cells[j]? := by
          intro j hj
          have hj_lt_ℓ₁ : j < ℓ₁ := Nat.lt_of_le_of_lt hj hLen
          rw [hσ_eval_le j (Nat.le_of_lt hj_lt_ℓ₁)]
          have hne : ℓ₁ ≠ j := Nat.ne_of_gt hj_lt_ℓ₁
          simp only [List.getElem?_modify, hne, ↓reduceIte, Option.map_eq_map, Option.map_id']
          exact cells_alloc_getElem?_lt σ p₁.toComp ρ hj_lt_ℓ₁
        obtain ⟨L_prod, hD_p₁, hGt_p₁, hBr_p₁, hPend_p₁, hDone_p₁⟩ :=
          derives_needScope_pending p₁ P ℓ code_p ρ₀ w_c σ.cells hPending hProd
            0 σ_eval ρ hσ_eval_le₀ hEnv
        refine ⟨L_prod, hD_p₁, ?_, ?_, ?_⟩
        · intro r hr j hj
          exact hGt_p₁ r hr j (Nat.lt_of_lt_of_le hLen hj)
        · intro r hr w hw
          obtain ⟨⟨b₀, hb₀⟩, _⟩ := hBr_p₁ r hr w hw
          cases b₀
          · exact Or.inl hb₀
          · exact Or.inr hb₀
        · intro a
          have hDisj : ∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
              r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .pending⟩ ∨
              ∃ a₀ : Bool, r.2.cells[ℓ]? = some ⟨code_p, ρ₀, .done (GroundTy.encodeVal (G := .bool) a₀)⟩ := by
            intro r hr w hw
            rcases (hBr_p₁ r hr w hw).2 with hEq | hDone_r
            · left; rw [hEq, hσ_eval_le₀ ℓ (Nat.le_refl ℓ)]; exact hPending
            · right; exact hDone_r
          rw [values_count_eq_indPending_add_indDone (G := .bool) ℓ code_p ρ₀ L_prod a hDisj,
              hPend_p₁ a, hDone_p₁ false a, hDone_p₁ true a]
          simp only [w₁, bindNeed, Fintype.sum_bool]
          omega
      obtain ⟨L, hD, hEx, hCount⟩ :=
        ih ℓ₁ p₁.toComp ρ w₁ σ₁ ρ₁ hLen₁ hPending₁ rfl hProd₁
      exact ⟨L, .need hD, hEx, hCount⟩

/-- **General $n$-Cell Dependent Telescope Adequacy Theorem (`derives_needChain_adequacy`):**
For every initial ground producer `p₀ : GroundComp .bool`, every list `ps : List (NeedScopeComp .bool)`
of $n$ chained dependent `need` cell producers (where cell $k+1$'s producer may force cell $k$
arbitrarily many times), and every final body `b : NeedScopeComp G`:
`compileNeedChain p₀ ps b` derives a complete result list `L` under `CallTimeChoice.Derives`
whose answer multiplicity for every `v : G.Web` is
`bindNeed (denoteNeedChain Nat (p₀.denote Nat) ps) (b.denoteRel Nat) v`! -/
theorem derives_needChain_adequacy {G : GroundTy}
    (p₀ : GroundComp .bool) (ps : List (NeedScopeComp .bool)) (b : NeedScopeComp G)
    (P : Program) (σ : Store) (ρ : List (Val Nat)) :
    ∃ L : List Result,
      Derives P (.eval σ ρ (compileNeedChain p₀ ps b)) L ∧
      (∀ r ∈ L, ∀ w, r.1 = .ok w → ∃ v₀ : G.Web, w = GroundTy.encodeVal v₀) ∧
      (∀ v : G.Web,
        (values L).count (GroundTy.encodeVal v) =
          bindNeed (denoteNeedChain Nat (p₀.denote Nat) ps) (b.denoteRel Nat) v) := by
  let ℓ₀ := σ.cells.length
  let σ₀ := σ.alloc p₀.toComp ρ
  let ρ₀ := Val.need ℓ₀ :: ρ
  have hLen₀ : ℓ₀ < σ₀.cells.length := by
    simp [ℓ₀, σ₀, Store.alloc]
  have hPending₀ : σ₀.cells[ℓ₀]? = some ⟨p₀.toComp, ρ, .pending⟩ :=
    cells_alloc_getElem?_length σ p₀.toComp ρ
  have hProd₀ : ∀ σ_eval : Store,
      (∀ j ≤ ℓ₀, σ_eval.cells[j]? = (σ₀.cells.modify ℓ₀ fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval ρ p₀.toComp) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ ℓ₀, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) = p₀.denote Nat a) := by
    intro σ_eval _
    obtain ⟨L_prod, hD_prod, hCells_prod, hEx_prod, hCount_prod⟩ :=
      GroundComp.derives_groundComp_adequacy p₀ P σ_eval ρ
    refine ⟨L_prod, hD_prod, ?_, ?_, hCount_prod⟩
    · intro r hr j _
      rw [hCells_prod r hr]
    · intro r hr w hw
      obtain ⟨b₀, hb₀⟩ := hEx_prod r hr w hw
      cases b₀
      · exact Or.inl hb₀
      · exact Or.inr hb₀
  obtain ⟨L, hD, hEx, hCount⟩ :=
    derives_needChainAux_adequacy ps b P ℓ₀ p₀.toComp ρ (p₀.denote Nat) σ₀ ρ₀
      hLen₀ hPending₀ rfl hProd₀
  exact ⟨L, .need hD, hEx, hCount⟩

end GeneralNeedAdequacy

end Mettapedia.Machines.BranchLocalNeed.Weighted

