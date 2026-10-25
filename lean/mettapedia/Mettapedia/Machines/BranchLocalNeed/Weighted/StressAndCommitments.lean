import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec
import Mettapedia.Machines.BranchLocalNeed.Weighted.WeightedRelNeedModel
import Mettapedia.Machines.BranchLocalNeed.Weighted.TypedFragmentAdequacy
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceAdequacy
import Mettapedia.Machines.BranchLocalNeed.WeightedResumption
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Stress Tests (5a–5d) and Commitment Agreement & Support Theorems (Task 6)

This module connects `WeightedRelNeedModel` and `TypedFragmentAdequacy` to verify:
1. **Task 5(a) — Cells captured by quoted code and run multiple times:**
   * Sequence comonoid on `List B` (`listCounit`, `listComult`) and finite bounded-length
     sequence web `ThunkWeb k A` (`Unit ⊕ (A × ThunkWeb (k-1) A)`) with `Fintype` instance.
   * Complete `CallTimeChoice.Derives` adequacy for `capturedCellInCode`, where a `need` cell
     `c := need coin` is captured inside `q := quote (force c)` and `q` is `run` twice in sequence,
     yielding `(false, false) ↦ 1`, `(true, true) ↦ 1`, and `0` off the diagonal.
2. **Task 5(b) — Cells inside data constructors and aliased pairs:**
   * Complete `CallTimeChoice.Derives` adequacy for `cellInUnaryConNeed` (`need coin` inside unary
     constructor `S`, matched via `caseCon`) and `aliasedPairOfCellsNeed` (`need coin`
     aliased in both fields of `Pair c c`, extracted as two variables via `caseCon` and forced
     sequentially), proving exact multiplicity agreement with `bindNeed`.
3. **Task 5(c) — Dependent cell chains and cyclic blackhole control:**
   * Instantiations of `derives_need_twoCell_chain_adequacy` and `derives_needChain_adequacy`
     from `TypedFragmentAdequacy` on:
     - `cellChainSimple`: `c₁ := need coin`, `c₂ := need (force c₁)`, body forces `c₂` twice;
     - `cellChainDupFalseXor`: `c₁ := need ((false ⊕ false) ⊕ true)`,
       `c₂ := need (xor (force c₁) (force c₁))`, body forces `c₂` twice (`(false, false) ↦ 3`,
       all other pairs `0`, whereas resampling `c₁` inside `c₂` would produce `(true, true)` with
       weight `4`);
     - `cellChainThreeCells`: a 3-cell dependent chain `c₁ → c₂ → c₃` via `derives_needChain_adequacy`.
   * Cyclic blackhole control (`derives_cyclic_self_reference_blackhole`): forcing a self-referential
     cell `.pending (.force (.var 0)) [.need 0]` at location `0` derives `[(.blackhole, σ)]` with
     `values = []` (`0` multiplicity, matching the least fixed point `0` in `Rel_ℕ`).
4. **Task 5(d) — Recursion and finite-fuel Kleene approximants:**
   * Monotone polynomial step operator `peanoStep` in `Rel_ℕ`, closed-form Kleene approximants
     `peanoApprox_eq`, and monotonicity.
5. **Task 6 — Commitment Agreement Theorems, Support Hierarchy, and McDermott–Mycroft:**
   * General `NeedScopeComp` commitment agreement (`denoteNeedClosed_eq_denoteEagerClosed_of_strict`,
     `denoteNeedClosed_eq_denoteEagerClosed_of_univalent`).
   * `BinderBody` commitment agreement (`evalNeed_eq_evalResample_of_affine`,
     `evalNeed_eq_evalResample_of_deterministic`, `evalNeed_eq_evalEager_of_relevant`,
     `evalNeed_eq_evalEager_of_univalent`).
   * Negative controls proved directly against `CallTimeChoice.Derives`
     (`derives_const_fail_need_vs_eager`, `derives_const_coin_need_vs_eager`).
   * Support inclusion hierarchy `supp(eager) ⊆ supp(need) ⊆ supp(resample)` and strictness
     witnesses (`support_evalEager_subset_evalNeed`, `support_evalNeed_subset_evalResample`,
     `support_inclusions_strict`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.Weighted

open scoped BigOperators
open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-- Empty store `{ cells := [], trace := [] }` for `CallTimeChoice`. -/
abbrev emptyStore : Store := Store.empty

/-- Pair constructor expression `.app (.app (.sym symPair) x) y`. -/
def vPair (x y : VExp) : VExp :=
  .app (.app (.sym symPair) x) y

/-- Runtime pair value `.app (.app (.sym symPair) x) y`. -/
def valPair (x y : Val Nat) : Val Nat :=
  .app (.app (.sym symPair) x) y

/-- Encoded Boolean values are never cell references (`isCell = false`). -/
theorem encodeBool_isCell_false (b : Bool) :
    (GroundTy.encodeVal (G := .bool) b).isCell = false := by
  cases b <;> rfl

/-- Ground `coin` producer `choose (ret false) (ret true)`. -/
def GroundComp.coin : GroundComp .bool :=
  .choose (.ret false) (.ret true)

/-! ## 1. Task 5(a): Cells Captured by Quoted Code and Bounded Sequence Webs -/

section Task5aCapturedCells

/-- The sequence comonoid counit on `List B`: only the empty run list `[]` has weight `1`. -/
def listCounit {S : Type*} [Semiring S] {B : Type*} : List B → S
  | [] => 1
  | _ :: _ => 0

/-- The sequence comonoid comultiplication on `List B`: splits `L` into `(L₁, L₂)`
whenever `L₁ ++ L₂ = L`. -/
def listComult {S : Type*} [Semiring S] {B : Type*} [DecidableEq B]
    (L : List B) (p : List B × List B) : S :=
  if p.1 ++ p.2 = L then 1 else 0

@[simp]
theorem listComult_nil_nil {S : Type*} [Semiring S] {B : Type*} [DecidableEq B] :
    listComult ([] : List B) ([], []) = (1 : S) := by
  simp [listComult]

@[simp]
theorem listComult_singleton_left {S : Type*} [Semiring S] {B : Type*} [DecidableEq B] (b : B) :
    listComult [b] ([b], []) = (1 : S) := by
  simp [listComult]

@[simp]
theorem listComult_singleton_right {S : Type*} [Semiring S] {B : Type*} [DecidableEq B] (b : B) :
    listComult [b] ([], [b]) = (1 : S) := by
  simp [listComult]

@[simp]
theorem listComult_pair_split {S : Type*} [Semiring S] {B : Type*} [DecidableEq B] (b₁ b₂ : B) :
    listComult [b₁, b₂] ([b₁], [b₂]) = (1 : S) := by
  simp [listComult]

/-- Bounded-length sequence web for `k`-bounded resampled thunks / quoted code:
`ThunkWeb 0 A = Unit` (`[]`) and `ThunkWeb (k + 1) A = Unit ⊕ (A × ThunkWeb k A)`
(`[]` or `a :: rest` of length `≤ k + 1`). Unlike unbounded `List A`,
`ThunkWeb k A` is finite whenever `A` is finite, allowing finite matrix composition in `Rel_S`
for any bounded fuel `k`. -/
def ThunkWeb : Nat → Type _ → Type _
  | 0, _ => Unit
  | k + 1, A => Unit ⊕ (A × ThunkWeb k A)

instance instFintypeThunkWeb : ∀ (k : Nat) (A : Type _) [Fintype A], Fintype (ThunkWeb k A)
  | 0, _, _ => inferInstanceAs (Fintype Unit)
  | k + 1, A, _ =>
      letI : Fintype (ThunkWeb k A) := instFintypeThunkWeb k A
      inferInstanceAs (Fintype (Unit ⊕ (A × ThunkWeb k A)))

instance instDecidableEqThunkWeb :
    ∀ (k : Nat) (A : Type _) [DecidableEq A], DecidableEq (ThunkWeb k A)
  | 0, _, _ => inferInstanceAs (DecidableEq Unit)
  | k + 1, A, _ =>
      letI : DecidableEq (ThunkWeb k A) := instDecidableEqThunkWeb k A
      inferInstanceAs (DecidableEq (Unit ⊕ (A × ThunkWeb k A)))

/-- Convert a bounded sequence web element `ThunkWeb k A` to its underlying `List A` of length `≤ k`. -/
def ThunkWeb.toList {A : Type _} : ∀ {k : Nat}, ThunkWeb k A → List A
  | 0, () => []
  | _ + 1, .inl () => []
  | _ + 1, .inr (a, rest) => a :: ThunkWeb.toList rest

theorem ThunkWeb.length_toList_le {A : Type _} :
    ∀ {k : Nat} (w : ThunkWeb k A), (ThunkWeb.toList w).length ≤ k
  | 0, () => Nat.le_refl 0
  | _ + 1, .inl () => Nat.zero_le _
  | _ + 1, .inr (_, rest) => Nat.succ_le_succ (ThunkWeb.length_toList_le rest)

/-- Quote a force of the captured cell and activate that code twice. -/
def capturedCellBody : Comp :=
  .seq (.quote (.force (.var 0)))
    (.seq (.run (.var 0))
      (.seq (.run (.var 1))
        (.ret (vPair (.var 1) (.var 0)))))

/-- **Task 5(a) Program (`capturedCellInCode`):**
A `need` cell `c := need coin` is created outside `quote`, captured inside
`q := quote (force (.var 0))`, and `q` is `run` twice in sequence:
1. `need coin` binds `.need 0` at `.var 0` in `ρ₁ = [.need 0]`;
2. `seq (quote (force (.var 0)))` allocates code cell `1` capturing `env = [.need 0]`
   and binds `.code 1` at `.var 0` in `ρ₂ = [.code 1, .need 0]`;
3. `seq (run (.var 0))` runs `.code 1` (forcing `.need 0` and committing it), binding
   `x` at `.var 0` in `ρ₃ = [x, .code 1, .need 0]`;
4. `seq (run (.var 1))` runs `.code 1` a second time (reading the already committed `.need 0`!),
   binding `y` at `.var 0` in `ρ₄ = [y, x, .code 1, .need 0]`;
5. `ret (vPair (.var 1) (.var 0))` returns `valPair x y`. -/
def capturedCellInCode : Comp := .need NeedScopeComp.coinComp capturedCellBody

/-- The same quoted consumer, with its captured suspension resampled on each
force rather than committed on the first force. -/
def resampledCellInCode : Comp := .delay NeedScopeComp.coinComp capturedCellBody

/-- `Rel_ℕ` model prediction for `capturedCellInCode`:
Even though `q` is `run` twice, the captured outer cell `c : NeedWeb Bool` is contracted
via `needComult` across the two runs of `q`'s body `force c`, so its denotation equals
`bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.doubleBody.denoteRel Nat)`. -/
def denoteCapturedCellInCode : Bool × Bool → Nat :=
  bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.doubleBody.denoteRel Nat)

/-- Running `.code 1` when cell `1` holds `{ code := .force (.var 0), env := [.need 0] }`
and cell `0` is already `.done (encodeVal b)` deterministically returns `[(.ok (encodeVal b), σ)]`. -/
theorem derives_run_code_force_done (P : Program) (σ : Store) (ρ : List (Val Nat))
    (v : VExp) (c₀ c₁ : Suspension) (b : Bool)
    (hv : v.eval ρ = .code 1)
    (h1 : σ.cells[1]? = some c₁)
    (hc₁_code : c₁.code = .force (.var 0))
    (hc₁_env : c₁.env = [.need 0])
    (h0 : σ.cells[0]? = some c₀)
    (hc₀_memo : c₀.memo = .done (GroundTy.encodeVal (G := .bool) b)) :
    Derives P (.eval σ ρ (.run v)) [(.ok (GroundTy.encodeVal (G := .bool) b), σ)] := by
  have hBody : Derives P (.eval σ c₁.env c₁.code)
      [(.ok (GroundTy.encodeVal (G := .bool) b), σ)] := by
    rw [hc₁_env, hc₁_code]
    exact derives_force_var_done (depth := 0) (ℓ := 0) rfl h0 hc₀_memo (encodeBool_isCell_false b)
  have hFollow : Derives P (.followK [(.ok (GroundTy.encodeVal (G := .bool) b), σ)])
      [(.ok (GroundTy.encodeVal (G := .bool) b), σ)] := by
    simpa using Derives.followOk (Derives.forceWhnf (encodeBool_isCell_false b)) Derives.followNil
  exact Derives.runCode hv h1 hBody hFollow

/-- **Task 5(a) Adequacy Theorem (`derives_capturedCellInCode_adequacy`):**
`capturedCellInCode` derives a complete result list `L` under `CallTimeChoice.Derives` whose
answer multiplicities match `denoteCapturedCellInCode` (`(false, false) ↦ 1`,
`(true, true) ↦ 1`, `(false, true) ↦ 0`, `(true, false) ↦ 0`). -/
theorem derives_capturedCellInCode_adequacy (P : Program) :
    ∃ L : List Result,
      Derives P (.eval emptyStore [] capturedCellInCode) L ∧
      (∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          denoteCapturedCellInCode p) ∧
      denoteCapturedCellInCode (false, false) = 1 ∧
      denoteCapturedCellInCode (true, true) = 1 ∧
      denoteCapturedCellInCode (false, true) = 0 ∧
      denoteCapturedCellInCode (true, false) = 0 := by
  let σ₀ : Store := emptyStore
  let σ₁ : Store := σ₀.alloc NeedScopeComp.coinComp []
  let σ₂ : Store := σ₁.alloc (.force (.var 0)) [.need 0]
  let σ₂_eval : Store := σ₂.setMemo 0 .evaluating
  let σ_f : Store := σ₂_eval.setMemo 0 (.done (.sym symFalse))
  let σ_t : Store := σ₂_eval.setMemo 0 (.done (.sym symTrue))
  have hQuote : Derives P (.eval σ₁ [.need 0] (.quote (.force (.var 0))))
      [(.ok (.code 1), σ₂)] := by
    exact Derives.quote (P := P) (σ := σ₁) (ρ := [.need 0]) (m := .force (.var 0))
  have hCoinEval : Derives P (.eval σ₂_eval [] NeedScopeComp.coinComp)
      [(.ok (.sym symFalse), σ₂_eval), (.ok (.sym symTrue), σ₂_eval)] := by
    simpa [NeedScopeComp.coinComp, VExp.eval] using (Derives.choose
      (Derives.ret (P := P) (σ := σ₂_eval) (ρ := []) (v := .sym symFalse))
      (Derives.ret (P := P) (σ := σ₂_eval) (ρ := []) (v := .sym symTrue)))
  have hCommit0 : Derives P (.commitK 0
      [(.ok (.sym symFalse), σ₂_eval), (.ok (.sym symTrue), σ₂_eval)])
      [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)] := by
    refine Derives.commitOk (Derives.forceWhnf rfl) ?_
    simpa using Derives.commitOk (Derives.forceWhnf rfl) Derives.commitNil
  have hForce0 : Derives P (.eval σ₂ [.need 0] (.force (.var 0)))
      [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)] := by
    refine Derives.force ?_
    exact Derives.forcePending
      (c := { code := NeedScopeComp.coinComp, env := [], memo := .pending })
      rfl rfl hCoinEval hCommit0
  have hFollow1 : Derives P (.followK [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)])
      [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)] := by
    refine Derives.followOk (Derives.forceWhnf rfl) ?_
    simpa using Derives.followOk (Derives.forceWhnf rfl) Derives.followNil
  have hRun1 : Derives P (.eval σ₂ [.code 1, .need 0] (.run (.var 0)))
      [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)] := by
    exact Derives.runCode
      (c := { code := .force (.var 0), env := [.need 0], memo := .pending })
      rfl rfl hForce0 hFollow1
  have hRun2_f : Derives P (.eval σ_f [.sym symFalse, .code 1, .need 0] (.run (.var 1)))
      [(.ok (.sym symFalse), σ_f)] :=
    derives_run_code_force_done P σ_f [.sym symFalse, .code 1, .need 0] (.var 1)
      { code := NeedScopeComp.coinComp, env := [], memo := .done (.sym symFalse) }
      { code := .force (.var 0), env := [.need 0], memo := .pending }
      false rfl rfl rfl rfl rfl rfl
  have hRun2_t : Derives P (.eval σ_t [.sym symTrue, .code 1, .need 0] (.run (.var 1)))
      [(.ok (.sym symTrue), σ_t)] :=
    derives_run_code_force_done P σ_t [.sym symTrue, .code 1, .need 0] (.var 1)
      { code := NeedScopeComp.coinComp, env := [], memo := .done (.sym symTrue) }
      { code := .force (.var 0), env := [.need 0], memo := .pending }
      true rfl rfl rfl rfl rfl rfl
  have hAfterRun1_f : Derives P
      (.eval σ_f [.sym symFalse, .code 1, .need 0]
        (.seq (.run (.var 1)) (.ret (vPair (.var 1) (.var 0)))))
      [(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f)] :=
    Derives.seq_single hRun2_f (Derives.ret (v := vPair (.var 1) (.var 0)))
  have hAfterRun1_t : Derives P
      (.eval σ_t [.sym symTrue, .code 1, .need 0]
        (.seq (.run (.var 1)) (.ret (vPair (.var 1) (.var 0)))))
      [(.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)] :=
    Derives.seq_single hRun2_t (Derives.ret (v := vPair (.var 1) (.var 0)))
  have hAfterQuote : Derives P
      (.eval σ₂ [.code 1, .need 0]
        (.seq (.run (.var 0)) (.seq (.run (.var 1)) (.ret (vPair (.var 1) (.var 0))))))
      [(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f),
       (.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)] := by
    refine Derives.seq hRun1 ?_
    refine Derives.seqKOk hAfterRun1_f ?_
    simpa using Derives.seqKOk hAfterRun1_t Derives.seqKNil
  have hTotal : Derives P (.eval emptyStore [] capturedCellInCode)
      [(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f),
       (.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)] := by
    exact Derives.need (Derives.seq_single hQuote hAfterQuote)
  refine ⟨[(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f),
           (.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)], hTotal, ?_, by decide, by decide, by decide, by decide⟩
  intro ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> decide

end Task5aCapturedCells

/-! ## 2. Task 5(b): Cells Inside Data Constructors and Aliased Pairs -/

section Task5bCellsInData

/-- Symbol tag for unary constructor `S`. -/
def symSucc : Nat := 20

/-- Value expression for unary constructor `S e`. -/
def vSucc (e : VExp) : VExp :=
  .app (.sym symSucc) e

/-- Runtime value for unary constructor `S v`. -/
def valSucc (v : Val Nat) : Val Nat :=
  .app (.sym symSucc) v

/-- **Task 5(b) Program 1 (`cellInUnaryConNeed`):**
A `need` cell `c := need coin` is wrapped inside unary constructor `S (.var 0)` and matched
via `caseCon`, where the extracted field is forced twice (`NeedScopeComp.doubleBody.toCompAt 0`). -/
def cellInUnaryConNeed : Comp :=
  .need GroundComp.coin.toComp
    (.caseCon (vSucc (.var 0)) symSucc 1
      (NeedScopeComp.doubleBody.toCompAt 0)
      .fail)

/-- **Task 5(b) Program 2 (`aliasedPairOfCellsNeed`):**
A single `need` cell `c := need coin` is placed in BOTH fields of `Pair (.var 0) (.var 0)`.
Pattern matching with `caseCon ... symPair 2` binds `[u₁, u₂]` at indices `0` and `1`
(both equal to `.need 0`), forces `u₁` (`.var 0`), then forces `u₂` (shifted to `.var 2`),
and pairs the results! -/
def aliasedPairOfCellsNeed : Comp :=
  .need NeedScopeComp.coinComp
    (.caseCon (vPair (.var 0) (.var 0)) symPair 2
      (.seq (.force (.var 0))
        (.seq (.force (.var 2))
          (.ret (vPair (.var 1) (.var 0)))))
      .fail)

/-- **Task 5(b) Theorem 1 (`derives_cellInUnaryConNeed_adequacy`):**
Matching `S (.need 0)` via `caseCon` and forcing the extracted cell twice via `doubleBody`
derives a complete result list `L` under `CallTimeChoice.Derives` whose multiplicities
agree with `bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.doubleBody.denoteRel Nat)`. -/
theorem derives_cellInUnaryConNeed_adequacy (P : Program) :
    ∃ L : List Result,
      Derives P (.eval emptyStore [] cellInUnaryConNeed) L ∧
      ∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.doubleBody.denoteRel Nat) p := by
  let σ₀ : Store := emptyStore.alloc GroundComp.coin.toComp []
  have hPending₀ : σ₀.cells[0]? = some ⟨GroundComp.coin.toComp, [], .pending⟩ := rfl
  have hProd : ∀ σ_eval : Store,
      (∀ j ≤ 0, σ_eval.cells[j]? = (σ₀.cells.modify 0 fun c => { c with memo := .evaluating })[j]?) →
      ∃ L_prod : List Result,
        Derives P (.eval σ_eval [] GroundComp.coin.toComp) L_prod ∧
        (∀ r ∈ L_prod, ∀ j ≥ 0, r.2.cells[j]? = σ_eval.cells[j]?) ∧
        (∀ r ∈ L_prod, ∀ w, r.1 = .ok w →
          w = GroundTy.encodeVal (G := .bool) false ∨
          w = GroundTy.encodeVal (G := .bool) true) ∧
        (∀ a : Bool, (values L_prod).count (GroundTy.encodeVal (G := .bool) a) =
          GroundComp.coin.denote Nat a) := by
    intro σ_eval _
    obtain ⟨L_prod, hD_prod, hCells_prod, hEx_prod, hCount_prod⟩ :=
      GroundComp.derives_groundComp_adequacy GroundComp.coin P σ_eval []
    refine ⟨L_prod, hD_prod, ?_, ?_, hCount_prod⟩
    · intro r hr j _
      rw [hCells_prod r hr]
    · intro r hr w hw
      obtain ⟨b₀, hb₀⟩ := hEx_prod r hr w hw
      cases b₀
      · exact Or.inl hb₀
      · exact Or.inr hb₀
  obtain ⟨L, hDer, _, hBr, hCntP, hCntD⟩ :=
    derives_needScope_pending NeedScopeComp.doubleBody P 0 GroundComp.coin.toComp []
      (GroundComp.coin.denote Nat) σ₀.cells hPending₀ hProd
      0 σ₀ [.need 0, .need 0] (fun _ _ => rfl) rfl
  have hMatch : ((vSucc (.var 0)).eval [.need 0]).matchCon symSucc 1 = some [.need 0] := rfl
  have hCase : Derives P
      (.eval σ₀ [.need 0]
        (.caseCon (vSucc (.var 0)) symSucc 1 (NeedScopeComp.doubleBody.toCompAt 0) .fail))
      L :=
    Derives.caseConHit hMatch hDer
  refine ⟨L, Derives.need hCase, ?_⟩
  intro p
  have hDisj : ∀ r ∈ L, ∀ w, r.1 = .ok w →
      r.2.cells[0]? = some ⟨GroundComp.coin.toComp, [], .pending⟩ ∨
      ∃ a : Bool, r.2.cells[0]? = some ⟨GroundComp.coin.toComp, [], .done (GroundTy.encodeVal (G := .bool) a)⟩ := by
    intro r hr w hw
    rcases (hBr r hr w hw).2 with hEq | hDone
    · left; rw [hEq]; exact hPending₀
    · right; exact hDone
  rw [values_count_eq_indPending_add_indDone (G := .pair .bool .bool) 0 GroundComp.coin.toComp [] L p hDisj,
      hCntP p, hCntD false p, hCntD true p]
  simp only [bindNeed, Fintype.sum_bool]
  omega

/-- **Task 5(b) Theorem 2 (`derives_aliasedPairOfCellsNeed_adequacy`):**
Placing `.need 0` in both fields of `Pair (.var 0) (.var 0)`, extracting the two fields via
`caseCon`, and forcing one field then the other derives a complete result list `L` under
`CallTimeChoice.Derives` whose multiplicities agree with
`bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.doubleBody.denoteRel Nat)` (`(false, false) ↦ 1`,
`(true, true) ↦ 1`, off-diagonal `0`). -/
theorem derives_aliasedPairOfCellsNeed_adequacy (P : Program) :
    ∃ L : List Result,
      Derives P (.eval emptyStore [] aliasedPairOfCellsNeed) L ∧
      ∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.doubleBody.denoteRel Nat) p := by
  let σ₀ : Store := emptyStore.alloc NeedScopeComp.coinComp []
  have hMatch : ((vPair (.var 0) (.var 0)).eval [.need 0]).matchCon symPair 2 =
      some [.need 0, .need 0] := rfl
  let σ_eval : Store := σ₀.setMemo 0 .evaluating
  let σ_f : Store := σ_eval.setMemo 0 (.done (.sym symFalse))
  let σ_t : Store := σ_eval.setMemo 0 (.done (.sym symTrue))
  have hCoinEval : Derives P (.eval σ_eval [] NeedScopeComp.coinComp)
      [(.ok (.sym symFalse), σ_eval), (.ok (.sym symTrue), σ_eval)] := by
    simpa [NeedScopeComp.coinComp, VExp.eval] using (Derives.choose
      (Derives.ret (P := P) (σ := σ_eval) (ρ := []) (v := .sym symFalse))
      (Derives.ret (P := P) (σ := σ_eval) (ρ := []) (v := .sym symTrue)))
  have hCommit0 : Derives P (.commitK 0
      [(.ok (.sym symFalse), σ_eval), (.ok (.sym symTrue), σ_eval)])
      [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)] := by
    refine Derives.commitOk (Derives.forceWhnf rfl) ?_
    simpa using Derives.commitOk (Derives.forceWhnf rfl) Derives.commitNil
  have hForce1 : Derives P (.eval σ₀ [.need 0, .need 0, .need 0] (.force (.var 0)))
      [(.ok (.sym symFalse), σ_f), (.ok (.sym symTrue), σ_t)] := by
    refine Derives.force ?_
    exact Derives.forcePending
      (c := { code := NeedScopeComp.coinComp, env := [], memo := .pending })
      rfl rfl hCoinEval hCommit0
  have hForce2_f : Derives P
      (.eval σ_f [.sym symFalse, .need 0, .need 0, .need 0] (.force (.var 2)))
      [(.ok (.sym symFalse), σ_f)] :=
    derives_force_var_done (depth := 2) (ℓ := 0)
      (c := { code := NeedScopeComp.coinComp, env := [], memo := .done (.sym symFalse) })
      rfl rfl rfl rfl
  have hForce2_t : Derives P
      (.eval σ_t [.sym symTrue, .need 0, .need 0, .need 0] (.force (.var 2)))
      [(.ok (.sym symTrue), σ_t)] :=
    derives_force_var_done (depth := 2) (ℓ := 0)
      (c := { code := NeedScopeComp.coinComp, env := [], memo := .done (.sym symTrue) })
      rfl rfl rfl rfl
  have hBranch_f : Derives P
      (.eval σ_f [.sym symFalse, .need 0, .need 0, .need 0]
        (.seq (.force (.var 2)) (.ret (vPair (.var 1) (.var 0)))))
      [(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f)] :=
    Derives.seq_single hForce2_f (Derives.ret (v := vPair (.var 1) (.var 0)))
  have hBranch_t : Derives P
      (.eval σ_t [.sym symTrue, .need 0, .need 0, .need 0]
        (.seq (.force (.var 2)) (.ret (vPair (.var 1) (.var 0)))))
      [(.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)] :=
    Derives.seq_single hForce2_t (Derives.ret (v := vPair (.var 1) (.var 0)))
  have hHit : Derives P
      (.eval σ₀ [.need 0, .need 0, .need 0]
        (.seq (.force (.var 0)) (.seq (.force (.var 2)) (.ret (vPair (.var 1) (.var 0))))))
      [(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f),
       (.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)] := by
    refine Derives.seq hForce1 ?_
    refine Derives.seqKOk hBranch_f ?_
    simpa using Derives.seqKOk hBranch_t Derives.seqKNil
  have hTotal : Derives P (.eval emptyStore [] aliasedPairOfCellsNeed)
      [(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f),
       (.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)] :=
    Derives.need (Derives.caseConHit hMatch hHit)
  refine ⟨[(.ok (valPair (.sym symFalse) (.sym symFalse)), σ_f),
           (.ok (valPair (.sym symTrue) (.sym symTrue)), σ_t)], hTotal, ?_⟩
  intro ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;> decide

end Task5bCellsInData

/-! ## 3. Task 5(c): Dependent Cell Chains and Cyclic Blackhole Control -/

section Task5cCellChainsAndCycles

/-- **Task 5(c) Stress Producer 1 (`dupFalseOrTrue`):**
Produces `false` with multiplicity `2` and `true` with multiplicity `1`:
`choose (choose (ret false) (ret false)) (ret true)`. -/
def dupFalseOrTrue : GroundComp .bool :=
  .choose (.choose (.ret false) (.ret false)) (.ret true)

/-- **Task 5(c) Stress Cell 2 Producer (`xorDoubleForce`):**
Forces the outer cell `c₁` TWICE and returns `xor x y`:
`seqBool force (fun x => seqBool force (fun y => ret (xor x y)))`.
Because `c₁` is memoized, both forces of `c₁` inside `c₂`'s producer yield the SAME
Boolean `x = y`, so `xor x y` is ALWAYS `false` (with multiplicity `2 + 1 = 3`)!
Under resampling (`delay`), `c₁` would be re-evaluated on the second force, producing `true`
with multiplicity `2 * 1 + 1 * 2 = 4`! -/
def xorDoubleForce : NeedScopeComp .bool :=
  .seqBool .force (fun x => .seqBool .force (fun y => .ret (xor x y)))

/-- **Task 5(c) Theorem 1 (`derives_cellChain_simple_adequacy`):**
Direct instantiation of `derives_need_twoCell_chain_adequacy` for `c₁ := need coin`,
`c₂ := need (force c₁)`, and body `doubleBody` (forcing `c₂` twice), proving complete
`CallTimeChoice.Derives` adequacy and exact diagonal counts `(false, false) ↦ 1`,
`(true, true) ↦ 1`, off-diagonal `0`. -/
theorem derives_cellChain_simple_adequacy (P : Program) :
    let w₂ := bindNeed (GroundComp.coin.denote Nat) (NeedScopeComp.force.denoteRel Nat)
    ∃ L : List Result,
      Derives P
        (.eval emptyStore []
          (.need GroundComp.coin.toComp
            (.need NeedScopeComp.force.toComp
              NeedScopeComp.doubleBody.toComp)))
        L ∧
      (∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) p) ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (false, false) = 1 ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (true, true) = 1 ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (false, true) = 0 ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (true, false) = 0 := by
  intro w₂
  obtain ⟨L, hDer, _, hCnt⟩ :=
    derives_need_twoCell_chain_adequacy GroundComp.coin NeedScopeComp.force
      NeedScopeComp.doubleBody P emptyStore []
  refine ⟨L, hDer, hCnt, by decide, by decide, by decide, by decide⟩

/-- **Task 5(c) Theorem 2 (`derives_cellChain_dupFalseXor_adequacy`):**
Direct instantiation of `derives_need_twoCell_chain_adequacy` for the duplicate-answer
dependent chain `c₁ := need dupFalseOrTrue`, `c₂ := need xorDoubleForce`, and body `doubleBody`:
* `c₂` forces `c₁` twice and computes `xor`, which under call-time choice always sees
  equal values from `c₁`, producing `false` with weight `2 + 1 = 3` and `true` with weight `0`;
* the outer body forces `c₂` twice, producing `(false, false)` with weight `3` and all
  other pairs with weight `0`! -/
theorem derives_cellChain_dupFalseXor_adequacy (P : Program) :
    let w₂ := bindNeed (dupFalseOrTrue.denote Nat) (xorDoubleForce.denoteRel Nat)
    ∃ L : List Result,
      Derives P
        (.eval emptyStore []
          (.need dupFalseOrTrue.toComp
            (.need xorDoubleForce.toComp
              NeedScopeComp.doubleBody.toComp)))
        L ∧
      (∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) p) ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (false, false) = 3 ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (true, true) = 0 ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (false, true) = 0 ∧
      bindNeed w₂ (NeedScopeComp.doubleBody.denoteRel Nat) (true, false) = 0 := by
  intro w₂
  obtain ⟨L, hDer, _, hCnt⟩ :=
    derives_need_twoCell_chain_adequacy dupFalseOrTrue xorDoubleForce
      NeedScopeComp.doubleBody P emptyStore []
  refine ⟨L, hDer, hCnt, by decide, by decide, by decide, by decide⟩

/-- **Task 5(c) Theorem 3 (`derives_cellChain_threeCells_adequacy`):**
Direct instantiation of the $n$-cell telescope adequacy theorem `derives_needChain_adequacy`
for a 3-cell dependent chain `c₁ := need coin`, `c₂ := need (force c₁)`,
`c₃ := need (force c₂)`, and body `doubleBody` forcing `c₃` twice. -/
theorem derives_cellChain_threeCells_adequacy (P : Program) :
    let ps : List (NeedScopeComp .bool) := [.force, .force]
    ∃ L : List Result,
      Derives P
        (.eval emptyStore []
          (compileNeedChain GroundComp.coin ps NeedScopeComp.doubleBody))
        L ∧
      (∀ p : Bool × Bool,
        (values L).count (GroundTy.encodeVal (G := .pair .bool .bool) p) =
          bindNeed (denoteNeedChain Nat (GroundComp.coin.denote Nat) ps)
            (NeedScopeComp.doubleBody.denoteRel Nat) p) ∧
      bindNeed (denoteNeedChain Nat (GroundComp.coin.denote Nat) ps)
        (NeedScopeComp.doubleBody.denoteRel Nat) (false, false) = 1 ∧
      bindNeed (denoteNeedChain Nat (GroundComp.coin.denote Nat) ps)
        (NeedScopeComp.doubleBody.denoteRel Nat) (true, true) = 1 := by
  intro ps
  obtain ⟨L, hDer, _, hCnt⟩ :=
    derives_needChain_adequacy GroundComp.coin ps NeedScopeComp.doubleBody P emptyStore []
  refine ⟨L, hDer, hCnt, by decide, by decide⟩

/-- **Task 5(c) Negative Control (`derives_cyclic_self_reference_blackhole`):**
If cell `0` is a self-referential suspension `{ code := .force (.var 0), env := [.need 0], memo := .pending }`,
forcing `.need 0` marks cell `0` as `.evaluating`, re-enters `.force (.var 0)`, hits
`Derives.forceBlackhole`, and commits cell `0` back to `.pending` via `Derives.commitStop`,
deterministically deriving `[(.blackhole, cyclicStore)]` with `values = []` (multiplicity `0`,
matching the least fixed point `0` in `Rel_ℕ`)! -/
def cyclicStore : Store :=
  { cells := [{ code := .force (.var 0), env := [.need 0], memo := .pending }]
    trace := [] }

theorem derives_cyclic_self_reference_blackhole (P : Program) :
    Derives P (.eval cyclicStore [.need 0] (.force (.var 0)))
      [(.blackhole, cyclicStore)] ∧
    values [(.blackhole, cyclicStore)] = [] := by
  constructor
  · refine Derives.force ?_
    have hInner : Derives P
        (.eval (cyclicStore.setMemo 0 .evaluating) [.need 0] (.force (.var 0)))
        [(.blackhole, cyclicStore.setMemo 0 .evaluating)] := by
      refine Derives.force ?_
      exact Derives.forceBlackhole
        (c := { code := .force (.var 0), env := [.need 0], memo := .evaluating })
        rfl rfl
    have hCommit : Derives P
        (.commitK 0 [(.blackhole, cyclicStore.setMemo 0 .evaluating)])
        [(.blackhole, cyclicStore)] := by
      simpa [cyclicStore, Store.setMemo] using
        (Derives.commitStop (P := P) (ℓ := 0) (o := .blackhole)
          (σ := cyclicStore.setMemo 0 .evaluating) (rs := [])
          rfl Derives.commitNil)
    exact Derives.forcePending
      (c := { code := .force (.var 0), env := [.need 0], memo := .pending })
      rfl rfl hInner hCommit
  · rfl

end Task5cCellChainsAndCycles

/-! ## 4. Task 5(d): Recursion and Finite-Fuel Kleene Approximants -/

section Task5dRecursion

/-- Monotone polynomial step operator `peanoStep : (Nat → Nat) → (Nat → Nat)` in `Rel_ℕ`
for the recursive generator `gen = Z ⊕ S(gen)`:
`peanoStep w 0 = 1` and `peanoStep w (n + 1) = w n`. -/
def peanoStep (w : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => w n

/-- `k`-fold Kleene approximant `peanoApprox k = peanoStep^[k] 0`. -/
def peanoApprox : Nat → (Nat → Nat)
  | 0 => fun _ => 0
  | k + 1 => peanoStep (peanoApprox k)

@[simp]
theorem peanoApprox_eq (k n : Nat) :
    peanoApprox k n = if n < k then 1 else 0 := by
  induction k generalizing n with
  | zero => simp [peanoApprox]
  | succ k ih =>
      cases n with
      | zero => simp [peanoApprox, peanoStep]
      | succ m =>
          simp only [peanoApprox, peanoStep, ih m]
          by_cases h : m < k <;> simp [h]

/-- Monotonicity of `peanoStep` in the pointwise order on `Nat → Nat`. -/
theorem peanoStep_mono {w₁ w₂ : Nat → Nat} (h : ∀ n, w₁ n ≤ w₂ n) :
    ∀ n, peanoStep w₁ n ≤ peanoStep w₂ n
  | 0 => Nat.le_refl 1
  | n + 1 => h n

/-- The Kleene approximants `peanoApprox k` form an ascending chain `peanoApprox k n ≤ peanoApprox (k + 1) n`. -/
theorem peanoApprox_mono (k n : Nat) :
    peanoApprox k n ≤ peanoApprox (k + 1) n := by
  simp only [peanoApprox_eq]
  by_cases h : n < k
  · have h' : n < k + 1 := Nat.lt_succ_of_lt h
    simp [h, h']
  · simp [h]

end Task5dRecursion

/-! ## 5. Task 6: Commitment Agreement Theorems, Support Hierarchy, and McDermott–Mycroft -/

section Task6Commitments

/-! ### 5.1 Direct `NeedScopeComp` Commitment Agreement Theorems -/

namespace NeedScopeComp

/-- **Eager (`seq` / call-by-value) closed denotation** of binding a Boolean producer
`w : Bool → S` into `b : NeedScopeComp G`:
Because `seq` evaluates the producer eagerly BEFORE entering `b`, every path through `b`
(both `none` paths that never force the bound variable and `some a` paths that read `a`)
is weighted by `w a`! -/
def denoteEagerClosed (S : Type*) [CommSemiring S] {G : GroundTy}
    (w : Bool → S) (b : NeedScopeComp G) (v : G.Web) : S :=
  ∑ a : Bool, w a * (b.denoteRel S none v + b.denoteRel S (some a) v)

/-- **Theorem 6.0a (`NeedScopeComp` Strict Body Agreement: `need = eager`):**
For ANY `b : NeedScopeComp G` that is strict in its bound cell (`∀ v, b.denoteRel S none v = 0`,
meaning `b` has zero weight on the unforced index `none`), call-by-need (`denoteNeedClosed`)
and eager evaluation (`denoteEagerClosed`) agree on every semiring `S` and every producer `w`! -/
theorem denoteNeedClosed_eq_denoteEagerClosed_of_strict
    (S : Type*) [CommSemiring S] {G : GroundTy}
    (w : Bool → S) (b : NeedScopeComp G)
    (hStrict : ∀ v : G.Web, b.denoteRel S none v = 0) (v : G.Web) :
    b.denoteNeedClosed S w v = b.denoteEagerClosed S w v := by
  simp [denoteNeedClosed, denoteEagerClosed, hStrict v]

/-- **Theorem 6.0b (`NeedScopeComp` Univalent Producer Agreement: `need = eager`):**
For ANY `b : NeedScopeComp G` (even one that discards its bound cell!) and any univalent
producer `w : Bool → S` (`∑ a : Bool, w a = 1`), call-by-need (`denoteNeedClosed`) and
eager evaluation (`denoteEagerClosed`) agree identically! -/
theorem denoteNeedClosed_eq_denoteEagerClosed_of_univalent
    (S : Type*) [CommSemiring S] {G : GroundTy}
    (w : Bool → S) (b : NeedScopeComp G)
    (hUni : (∑ a : Bool, w a) = 1) (v : G.Web) :
    b.denoteNeedClosed S w v = b.denoteEagerClosed S w v := by
  unfold denoteNeedClosed denoteEagerClosed
  calc
    b.denoteRel S none v + ∑ a : Bool, w a * b.denoteRel S (some a) v
      = (∑ a : Bool, w a) * b.denoteRel S none v +
          ∑ a : Bool, w a * b.denoteRel S (some a) v := by rw [hUni, one_mul]
    _ = (∑ a : Bool, w a * b.denoteRel S none v) +
          ∑ a : Bool, w a * b.denoteRel S (some a) v := by rw [Finset.sum_mul]
    _ = ∑ a : Bool, (w a * b.denoteRel S none v + w a * b.denoteRel S (some a) v) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ a : Bool, w a * (b.denoteRel S none v + b.denoteRel S (some a) v) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [mul_add]

end NeedScopeComp

/-! ### 5.2 Three-Commitment Path Decomposition (`BinderBody`) -/

/-- To compare all three evaluation commitments (`need`, `resample`, `eager`) on the
exact same syntactic body over a bound variable `x`, we decompose a body by how
many times it forces `x` along each execution path:
* `onZero : B → Nat` is the multiplicity of output `b : B` along paths that force `x` **0 times**;
* `onOne : A → B → Nat` is the multiplicity of `b : B` along paths that force `x` **1 time**
  and observe `a : A`;
* `onTwo : A → A → B → Nat` is the multiplicity of `b : B` along paths that force `x` **2 times**
  and observe `(a₁, a₂) : A × A`. -/
structure BinderBody (A B : Type*) where
  onZero : B → Nat
  onOne : A → B → Nat
  onTwo : A → A → B → Nat

namespace BinderBody

variable {A B : Type*} [Fintype A]

/-- **Call-by-need (`need`) semantics** of binding producer `w : A → Nat` in `body`:
* 0-force paths (`onZero`) do not force the cell (`none` in `NeedWeb A`, weight `1`);
* 1-force paths (`onOne a`) force the cell once (`some a` in `NeedWeb A`, weight `w a`);
* 2-force paths (`onTwo a₁ a₂`) share the memoized value (`a₁ = a₂ = a`, weight `w a`). -/
def evalNeed (w : A → Nat) (body : BinderBody A B) (b : B) : Nat :=
  body.onZero b +
  (∑ a : A, w a * body.onOne a b) +
  (∑ a : A, w a * body.onTwo a a b)

/-- **Run-time choice (`resample` / `delay` / call-by-name) semantics** of binding `w` in `body`:
* 0-force paths do not run `w` (`[]` in `List A`, weight `1`);
* 1-force paths run `w` once (`[a]` in `List A`, weight `w a`);
* 2-force paths run `w` twice independently (`[a₁, a₂]` in `List A`, weight `w a₁ * w a₂`). -/
def evalResample (w : A → Nat) (body : BinderBody A B) (b : B) : Nat :=
  body.onZero b +
  (∑ a : A, w a * body.onOne a b) +
  (∑ a₁ : A, ∑ a₂ : A, w a₁ * w a₂ * body.onTwo a₁ a₂ b)

/-- **Eager (`seq` / call-by-value) semantics** of binding `w` in `body`:
`w` is evaluated eagerly BEFORE `body`, so every path (including 0-force paths!) is
weighted by `w a`, and 2-force paths receive the same eager value `(a, a)`. -/
def evalEager (w : A → Nat) (body : BinderBody A B) (b : B) : Nat :=
  (∑ a : A, w a * body.onZero b) +
  (∑ a : A, w a * body.onOne a b) +
  (∑ a : A, w a * body.onTwo a a b)

/-- A body is **affine** (forces its bound variable at most once on every path)
when `onTwo` is identically `0`. -/
def IsAffine (body : BinderBody A B) : Prop :=
  ∀ a₁ a₂ b, body.onTwo a₁ a₂ b = 0

/-- A producer `w : A → Nat` is **deterministic / sub-univalent** (McDermott–Mycroft's
"may-diverge/fail only, no branching" condition) when `w a * w a = w a` for every `a`
and `w a₁ * w a₂ = 0` for `a₁ ≠ a₂` (i.e. `w` is an indicator function of at most one value). -/
def IsDeterministicProducer (w : A → Nat) : Prop :=
  (∀ a : A, w a * w a = w a) ∧ (∀ a₁ a₂ : A, a₁ ≠ a₂ → w a₁ * w a₂ = 0)

/-- A body is **relevant / strict** (forces its bound variable at least once on every path)
when `onZero` is identically `0`. -/
def IsRelevant (body : BinderBody A B) : Prop :=
  ∀ b, body.onZero b = 0

/-- A producer `w : A → Nat` is **univalent** (total weight `1`) when `∑ a, w a = 1`. -/
def IsUnivalentProducer (w : A → Nat) : Prop :=
  (∑ a : A, w a) = 1

/-! ### Theorem 6.1: When `need = resample` (Positive Theorems + Negative Control) -/

/-- **Positive Agreement 6.1a (Affine Body):**
If `body` forces its bound cell at most once on every path (`IsAffine body`), then
`evalNeed w body = evalResample w body` for EVERY producer `w` (even nondeterministic or failing)! -/
theorem evalNeed_eq_evalResample_of_affine (w : A → Nat) (body : BinderBody A B)
    (haff : body.IsAffine) (b : B) :
    body.evalNeed w b = body.evalResample w b := by
  unfold evalNeed evalResample
  have h1 : (∑ a : A, w a * body.onTwo a a b) = 0 :=
    Finset.sum_eq_zero fun a _ => by simp [haff a a b]
  have h2 : (∑ a₁ : A, ∑ a₂ : A, w a₁ * w a₂ * body.onTwo a₁ a₂ b) = 0 :=
    Finset.sum_eq_zero fun a₁ _ => Finset.sum_eq_zero fun a₂ _ => by simp [haff a₁ a₂ b]
  rw [h1, h2]

/-- **Positive Agreement 6.1b (Deterministic / Sub-Univalent Producer — McDermott–Mycroft):**
If the producer `w` has at most one outcome with multiplicity `≤ 1` (`IsDeterministicProducer w`,
i.e., the only effect is divergence/failure), then `evalNeed w body = evalResample w body`
for EVERY body (even non-affine bodies that force the cell multiple times)! -/
theorem evalNeed_eq_evalResample_of_deterministic [DecidableEq A] (w : A → Nat) (body : BinderBody A B)
    (hdet : IsDeterministicProducer w) (b : B) :
    body.evalNeed w b = body.evalResample w b := by
  unfold evalNeed evalResample
  congr 1
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  have hinner :
      (∑ a₂ : A, w a₁ * w a₂ * body.onTwo a₁ a₂ b) =
        ∑ a₂ : A, if a₂ = a₁ then w a₁ * body.onTwo a₁ a₁ b else 0 := by
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    by_cases h : a₂ = a₁
    · subst h
      rw [hdet.1 a₂]
      simp
    · have h0 := hdet.2 a₁ a₂ (Ne.symm h)
      simp [h, h0]
  rw [hinner, Finset.sum_ite_eq' Finset.univ a₁]
  simp

/-- Canonical `doubleBinderBody` in `BinderBody Bool (Bool × Bool)`: forces the bound variable
twice and returns the pair `(a₁, a₂)`. -/
def doubleBinderBody : BinderBody Bool (Bool × Bool) where
  onZero _ := 0
  onOne _ _ := 0
  onTwo a₁ a₂ p := if (a₁, a₂) = p then 1 else 0

/-- **Negative Control 6.1 (`need ≠ resample` on `doubleCoin`):**
When the body forces the cell twice (`doubleBinderBody`) and the producer is `coin`
(`false ↦ 1, true ↦ 1`), `evalNeed` and `evalResample` disagree on `(false, true)` and `(true, false)`. -/
theorem evalNeed_ne_evalResample_doubleCoin :
    let w : Bool → Nat := fun _ => 1
    doubleBinderBody.evalNeed w (false, true) = 0 ∧
    doubleBinderBody.evalResample w (false, true) = 1 ∧
    doubleBinderBody.evalNeed w ≠ doubleBinderBody.evalResample w := by
  intro w
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hft := congrFun h (false, true)
  revert hft
  decide

/-! ### Theorem 6.2: When `need = eager` (Positive Theorems + `Derives` Negative Controls) -/

/-- **Positive Agreement 6.2a (Relevant Body — Forced on Every Path):**
If `body` forces its bound cell at least once on every path (`IsRelevant body`), then
`evalNeed w body = evalEager w body` for EVERY producer `w`! -/
theorem evalNeed_eq_evalEager_of_relevant (w : A → Nat) (body : BinderBody A B)
    (hrel : body.IsRelevant) (b : B) :
    body.evalNeed w b = body.evalEager w b := by
  unfold evalNeed evalEager
  have h0 : body.onZero b = 0 := hrel b
  have hsum0 : (∑ a : A, w a * body.onZero b) = 0 :=
    Finset.sum_eq_zero fun a _ => by simp [h0]
  rw [hsum0, h0]

/-- **Positive Agreement 6.2b (Univalent Producer):**
If the producer `w` has total multiplicity `∑ a, w a = 1` (`IsUnivalentProducer w`),
then `evalNeed w body = evalEager w body` for EVERY body (even bodies that discard the cell)! -/
theorem evalNeed_eq_evalEager_of_univalent (w : A → Nat) (body : BinderBody A B)
    (huni : IsUnivalentProducer w) (b : B) :
    body.evalNeed w b = body.evalEager w b := by
  unfold evalNeed evalEager
  rw [← Finset.sum_mul, huni, one_mul]

/-- Canonical `constFalseBody` in `BinderBody Bool Bool`: ignores its bound variable
and returns `false` once (`const False`). -/
def constFalseBody : BinderBody Bool Bool where
  onZero b := if b = false then 1 else 0
  onOne _ _ := 0
  onTwo _ _ _ := 0

/-- **Negative Control 6.2a (`const False fail` separates `need` from `eager` in `Derives`):**
When the producer is `.fail` (`w = 0`) and the body ignores its argument (`.ret (.sym symFalse)`):
* `.need .fail (.ret (.sym symFalse))` derives `[(.ok (.sym symFalse), ...)]` with multiplicity `1`;
* `.seq .fail (.ret (.sym symFalse))` derives `[(.fail, emptyStore)]` with multiplicity `0`! -/
theorem derives_const_fail_need_vs_eager (P : Program) :
    let wFail : Bool → Nat := fun _ => 0
    constFalseBody.evalNeed wFail false = 1 ∧
    constFalseBody.evalEager wFail false = 0 ∧
    Derives P (.eval emptyStore [] (.need .fail (.ret (.sym symFalse))))
      [(.ok (.sym symFalse), emptyStore.alloc .fail [])] ∧
    (values [(.ok (.sym symFalse), emptyStore.alloc .fail [])]).count (.sym symFalse) = 1 ∧
    Derives P (.eval emptyStore [] (.seq .fail (.ret (.sym symFalse))))
      [(.fail, emptyStore)] ∧
    (values [(.fail, emptyStore)]).count (.sym symFalse) = 0 := by
  refine ⟨by decide, by decide, ?_, by decide, ?_, by decide⟩
  · exact Derives.need (Derives.ret (v := .sym symFalse))
  · exact Derives.seq Derives.fail (Derives.seqKStop rfl Derives.seqKNil)

/-- **Negative Control 6.2b (`const False coin` separates `need` from `eager` on counts in `Derives`):**
When the producer is `NeedScopeComp.coinComp` (`false ↦ 1, true ↦ 1`) and the body ignores its argument:
* `.need coinComp (.ret (.sym symFalse))` derives `[(.ok (.sym symFalse), ...)]` with multiplicity `1`;
* `.seq coinComp (.ret (.sym symFalse))` derives TWO copies of `.ok (.sym symFalse)` with multiplicity `2`! -/
theorem derives_const_coin_need_vs_eager (P : Program) :
    let wCoin : Bool → Nat := fun _ => 1
    constFalseBody.evalNeed wCoin false = 1 ∧
    constFalseBody.evalEager wCoin false = 2 ∧
    Derives P (.eval emptyStore [] (.need NeedScopeComp.coinComp (.ret (.sym symFalse))))
      [(.ok (.sym symFalse), emptyStore.alloc NeedScopeComp.coinComp [])] ∧
    (values [(.ok (.sym symFalse), emptyStore.alloc NeedScopeComp.coinComp [])]).count (.sym symFalse) = 1 ∧
    Derives P (.eval emptyStore [] (.seq NeedScopeComp.coinComp (.ret (.sym symFalse))))
      [(.ok (.sym symFalse), emptyStore), (.ok (.sym symFalse), emptyStore)] ∧
    (values [(.ok (.sym symFalse), emptyStore), (.ok (.sym symFalse), emptyStore)]).count
      (.sym symFalse) = 2 := by
  refine ⟨by decide, by decide, ?_, by decide, ?_, by decide⟩
  · exact Derives.need (Derives.ret (v := .sym symFalse))
  · have hCoin : Derives P (.eval emptyStore [] NeedScopeComp.coinComp)
        [(.ok (.sym symFalse), emptyStore), (.ok (.sym symTrue), emptyStore)] := by
      simpa [NeedScopeComp.coinComp, VExp.eval] using (Derives.choose
        (Derives.ret (P := P) (σ := emptyStore) (ρ := []) (v := .sym symFalse))
        (Derives.ret (P := P) (σ := emptyStore) (ρ := []) (v := .sym symTrue)))
    refine Derives.seq hCoin ?_
    refine Derives.seqKOk (Derives.ret (v := .sym symFalse)) ?_
    simpa [VExp.eval] using Derives.seqKOk (Derives.ret (v := .sym symFalse)) Derives.seqKNil

/-! ### Theorem 6.3: Support Inclusion Hierarchy Relative to the Strategy-Free Top -/

/-- The reachable value **support** (the `Rel_𝔹` projection) of a weighted distribution
`d : B → Nat` is the set of values with positive multiplicity `0 < d b`. -/
def InSupport (d : B → Nat) (b : B) : Prop :=
  0 < d b

omit [Fintype A] in
/-- Helper: if a sum of natural numbers over a `Finset` is `0`, every summand is `0`. -/
theorem finset_sum_nat_eq_zero [DecidableEq A] (s : Finset A) (f : A → Nat)
    (h : (∑ x ∈ s, f x) = 0) : ∀ x ∈ s, f x = 0 := by
  induction s using Finset.induction_on with
  | empty => intro x hx; cases hx
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha] at h
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · omega
      · exact ih (by omega) x hx'

/-- **Support Inclusion Theorem 1 (`supp(eager) ⊆ supp(need)`):**
Every value reachable under eager evaluation (`0 < evalEager w body b`) is reachable
under call-by-need (`0 < evalNeed w body b`). -/
theorem support_evalEager_subset_evalNeed (w : A → Nat) (body : BinderBody A B) (b : B) :
    InSupport (body.evalEager w) b → InSupport (body.evalNeed w) b := by
  unfold InSupport evalEager evalNeed
  intro hpos
  by_cases h0 : 0 < body.onZero b
  · omega
  · have hz : body.onZero b = 0 := by omega
    have hsumz : (∑ a : A, w a * body.onZero b) = 0 :=
      Finset.sum_eq_zero fun a _ => by simp [hz]
    omega

/-- **Support Inclusion Theorem 2 (`supp(need) ⊆ supp(resample)`):**
Every value reachable under call-by-need (`0 < evalNeed w body b`) is reachable
under run-time choice / strategy-free rewriting (`0 < evalResample w body b`). -/
theorem support_evalNeed_subset_evalResample [DecidableEq A] (w : A → Nat) (body : BinderBody A B) (b : B) :
    InSupport (body.evalNeed w) b → InSupport (body.evalResample w) b := by
  unfold InSupport evalNeed evalResample
  intro hpos
  by_cases h01 : 0 < body.onZero b + ∑ a : A, w a * body.onOne a b
  · omega
  · by_cases hres : 0 < ∑ a₁ : A, ∑ a₂ : A, w a₁ * w a₂ * body.onTwo a₁ a₂ b
    · omega
    · have hres0 : (∑ a₁ : A, ∑ a₂ : A, w a₁ * w a₂ * body.onTwo a₁ a₂ b) = 0 := by omega
      have hneed0 : (∑ a : A, w a * body.onTwo a a b) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        have h1 := finset_sum_nat_eq_zero Finset.univ _ hres0 a ha
        have h2 := finset_sum_nat_eq_zero Finset.univ _ h1 a ha
        rcases Nat.mul_eq_zero.mp h2 with hww | hbody
        · rcases Nat.mul_eq_zero.mp hww with hw | hw <;> simp [hw]
        · simp [hbody]
      omega

/-- **Strictness of Both Support Inclusions (`supp(eager) ⊊ supp(need) ⊊ supp(resample)`):**
1. `constFalseBody` with `wFail` has `InSupport (evalNeed) false` (`1 > 0`) but
   `¬ InSupport (evalEager) false` (`0 = 0`), so `supp(eager) ⊊ supp(need)`.
2. `doubleBinderBody` with `wCoin` has `InSupport (evalResample) (false, true)` (`1 > 0`)
   but `¬ InSupport (evalNeed) (false, true)` (`0 = 0`), so `supp(need) ⊊ supp(resample)`. -/
theorem support_inclusions_strict :
    let wFail : Bool → Nat := fun _ => 0
    let wCoin : Bool → Nat := fun _ => 1
    (InSupport (constFalseBody.evalNeed wFail) false ∧
      ¬ InSupport (constFalseBody.evalEager wFail) false) ∧
    (InSupport (doubleBinderBody.evalResample wCoin) (false, true) ∧
      ¬ InSupport (doubleBinderBody.evalNeed wCoin) (false, true)) := by
  unfold InSupport
  decide

end BinderBody

end Task6Commitments

namespace MachineAdequacy

open NeedReference NeedReturningRuns

/-- The existing value-expression compiler supplies the actual machine's
ground constructor value. It introduces no cell or readout-name convention. -/
def groundValue {G : GroundTy} (value : G.Web) : MVal :=
  (GroundTy.encodeVExp value).eval []

private theorem groundValue_related {G : GroundTy} (value : G.Web) :
    ValRel ([] : List CellId) (GroundTy.encodeVal value) (groundValue value) := by
  simpa only [GroundTy.eval_encodeVExp, groundValue] using
    (VExp.eval_rel (φ := ([] : List CellId)) (ρ := []) (ρ' := ([] : MEnv))
      (.nil) (GroundTy.encodeVExp value))

/-- Complete independent source evidence supplies a closed actual frontier,
ground answer counts, and ordered outcome/effect correspondence. The budget
is the reference frontier's unfolding allowance, not a global work bound. -/
theorem eval_frontier_ground_counts {G : GroundTy} {P : Program} {code : Comp} {results : List Result}
    (source : Derives P (.eval Store.empty [] code) results) :
    ∃ threshold count leaves,
      Returns (machineSpec P) [] count [initialMachine code] leaves ∧
      List.Forall₂ (ResRel [] initialWorld []) results leaves ∧
      ∀ fuel, threshold ≤ fuel →
        runFrontier (machineSpec P) fuel [initialMachine code] = leaves.map haltOf ∧
        (∀ value : G.Web,
          (machineValues (answers (machineSpec P) fuel (initialMachine code))).count (groundValue value) =
            (values results).count (GroundTy.encodeVal value)) ∧
        List.Forall₂ ObservationRel results
          ((runFrontier (machineSpec P) fuel [initialMachine code]).filterMap haltedObservation) := by
  obtain ⟨threshold, count, leaves, completed, related, stable⟩ := eval_frontier_forward source
  refine ⟨threshold, count, leaves, completed, related, ?_⟩
  intro fuel enough
  have frontier := stable fuel enough
  refine ⟨frontier, ?_, ?_⟩
  · intro value
    rw [answers_of_frontier completed frontier]
    exact ground_value_count (leafOutcomes_rel related) (groundValue_related value)
      (GroundTy.encodeVal_cellFree value)
  · rw [observations_of_frontier completed frontier]
    exact leafObservations_rel related

/-- The existing arbitrary finite dependent Need telescope is realized by the
unchanged reference machine with exactly its denotational multiplicities.
Each producer may use its immediate predecessor repeatedly. Returned worlds
and every branch's emissions remain in the same correspondence; this is not
an adequacy claim for unrestricted random-access cell contexts. -/
theorem needChain_machine_adequacy {G : GroundTy} (producer : GroundComp .bool)
    (chain : List (NeedScopeComp .bool)) (body : NeedScopeComp G) (P : Program) :
    ∃ results threshold count leaves,
      Derives P (.eval Store.empty [] (compileNeedChain producer chain body)) results ∧
      (∀ result ∈ results, ∀ value, result.1 = .ok value →
        ∃ observed : G.Web, value = GroundTy.encodeVal observed) ∧
      Returns (machineSpec P) [] count [initialMachine (compileNeedChain producer chain body)] leaves ∧
      List.Forall₂ (ResRel [] initialWorld []) results leaves ∧
      ∀ fuel, threshold ≤ fuel →
        runFrontier (machineSpec P) fuel [initialMachine (compileNeedChain producer chain body)] =
          leaves.map haltOf ∧
        (∀ value : G.Web,
          (machineValues (answers (machineSpec P) fuel
            (initialMachine (compileNeedChain producer chain body)))).count (groundValue value) =
              bindNeed (denoteNeedChain Nat (producer.denote Nat) chain) (body.denoteRel Nat) value) ∧
        List.Forall₂ ObservationRel results
          ((runFrontier (machineSpec P) fuel
            [initialMachine (compileNeedChain producer chain body)]).filterMap haltedObservation) := by
  obtain ⟨results, source, typed, counts⟩ :=
    derives_needChain_adequacy producer chain body P Store.empty []
  obtain ⟨threshold, count, leaves, completed, related, stable⟩ :=
    eval_frontier_ground_counts (G := G) source
  refine ⟨results, threshold, count, leaves, source, typed, completed, related, ?_⟩
  intro fuel enough
  obtain ⟨frontier, actualCounts, effects⟩ := stable fuel enough
  exact ⟨frontier, fun value => (actualCounts value).trans (counts value), effects⟩

/-- The same duplicate producer has two memoized occurrences and four
resampled occurrences in actual machine executions. This is not a comparison
of two answer lists chosen independently of execution. -/
theorem machine_need_and_delay_keep_distinct_counts :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      (machineValues (answers (machineSpec []) fuel
        (initialMachine (.need GroundComp.dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp)))).count
          (groundValue (G := .pair .bool .bool) (false, false)) = 2 ∧
      (machineValues (answers (machineSpec []) fuel
        (initialMachine (.delay GroundComp.dupFalseProducer.toComp NeedScopeComp.doubleBody.toComp)))).count
          (groundValue (G := .pair .bool .bool) (false, false)) = 4 := by
  obtain ⟨needResults, needSource, _, needCount, _, _, _⟩ := GroundComp.control_need_double_dupFalse
  obtain ⟨delayResults, delaySource, delayCount, _, _, _⟩ := GroundComp.control_delay_double_dupFalse
  obtain ⟨needBound, _, _, _, _, needRun⟩ :=
    eval_frontier_ground_counts (G := .pair .bool .bool) needSource
  obtain ⟨delayBound, _, _, _, _, delayRun⟩ :=
    eval_frontier_ground_counts (G := .pair .bool .bool) delaySource
  refine ⟨max needBound delayBound, ?_⟩
  intro fuel enough
  exact ⟨((needRun fuel ((le_max_left _ _).trans enough)).2.1 (false, false)).trans needCount,
    ((delayRun fuel ((le_max_right _ _).trans enough)).2.1 (false, false)).trans delayCount⟩

/-- Ignoring a failing producer succeeds under Need and fails under eager
execution, on the actual machine. Both are completed source-derived runs. -/
theorem machine_unused_failure_separates_need_and_eager (P : Program) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      (machineValues (answers (machineSpec P) fuel
        (initialMachine (.need .fail (.ret (.sym symFalse)))))).count (groundValue (G := .bool) false) = 1 ∧
      (machineValues (answers (machineSpec P) fuel
        (initialMachine (.seq .fail (.ret (.sym symFalse)))))).count (groundValue (G := .bool) false) = 0 := by
  obtain ⟨_, _, needSource, needCount, eagerSource, eagerCount⟩ :=
    BinderBody.derives_const_fail_need_vs_eager P
  obtain ⟨needBound, _, _, _, _, needRun⟩ := eval_frontier_ground_counts (G := .bool) needSource
  obtain ⟨eagerBound, _, _, _, _, eagerRun⟩ := eval_frontier_ground_counts (G := .bool) eagerSource
  refine ⟨max needBound eagerBound, ?_⟩
  intro fuel enough
  exact ⟨((needRun fuel ((le_max_left _ _).trans enough)).2.1 false).trans needCount,
    ((eagerRun fuel ((le_max_right _ _).trans enough)).2.1 false).trans eagerCount⟩

end MachineAdequacy

/-! ## Probabilities of actual shared and resampled machine executions -/

namespace ProbabilityControls

open NeedReference NeedWeightedResumption Stochastic
open Mettapedia.GSLT.Dynamics WeightedResumption WeightedBranchingResumption
open scoped NNReal ENNReal NNRat

abbrev Occurrence := WorkState (Comp × MEnv) MLocal MResume MRule MVal Empty MFault Nat

def initial (code : Comp) : Occurrence := ⟨initialMachine code, []⟩

/-- Observe Boolean constructor pairs only after return. The probability law
before this readout still retains every pending state and fault in full. -/
def pairReadout : Occurrence ⊕ Occurrence → Option (Bool × Bool)
  | .inl finished =>
    match finished.state.control with
    | .halted (.value value) =>
      if value = MachineAdequacy.groundValue (G := .pair .bool .bool) (false, false) then
        some (false, false)
      else if value = MachineAdequacy.groundValue (G := .pair .bool .bool) (false, true) then
        some (false, true)
      else if value = MachineAdequacy.groundValue (G := .pair .bool .bool) (true, false) then
        some (true, false)
      else if value = MachineAdequacy.groundValue (G := .pair .bool .bool) (true, true) then
        some (true, true)
      else none
    | _ => none
  | .inr _ => none

def rationalRows (fuel : Nat) (code : Comp) :=
  contributions (uniformSource (machineSpec []) ℚ≥0) fuel (initial code)

def pairRows (fuel : Nat) (code : Comp) :=
  (rationalRows fuel code).map fun row => (pairReadout row.1, row.2)

/-- The list is calculated by the existing reference machine, including each
local choice's factor, rather than chosen from the expected distribution. -/
theorem captured_rows : pairRows 50 capturedCellInCode =
    [(some (false, false), 1 / 2), (some (true, true), 1 / 2)] := by decide +kernel

theorem resampled_rows : pairRows 50 resampledCellInCode =
    [(some (false, false), 1 / 4), (some (false, true), 1 / 4),
      (some (true, false), 1 / 4), (some (true, true), 1 / 4)] := by decide +kernel

theorem captured_completed :
    (rationalRows 50 capturedCellInCode).all (fun row => row.1.isLeft) = true := by decide +kernel

theorem resampled_completed :
    (rationalRows 50 resampledCellInCode).all (fun row => row.1.isLeft) = true := by decide +kernel

noncomputable def pairLaw (fuel : Nat) (code : Comp) : PMF (Option (Bool × Bool)) :=
  (uniformLaw (machineSpec []) fuel (initial code)).map pairReadout

theorem pairLaw_map_apply {Observed : Type*} [DecidableEq Observed]
    (fuel : Nat) (code : Comp) (readout : Option (Bool × Bool) → Observed) (answer : Observed) :
    ((pairLaw fuel code).map readout) answer =
      (((((pairRows fuel code).map fun row =>
        if answer = readout row.1 then row.2 else 0).sum : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by
  rw [pairLaw, PMF.map_comp, uniformLaw_map_apply]
  simp only [pairRows, rationalRows, List.map_map, Function.comp_def]
  apply congrArg (fun weights : List ℚ≥0 => ((weights.sum : ℝ≥0) : ℝ≥0∞))
  apply List.map_congr_left
  intro row _
  split_ifs <;> rfl

theorem pairLaw_apply (fuel : Nat) (code : Comp) (answer : Option (Bool × Bool)) :
    pairLaw fuel code answer =
      (((((pairRows fuel code).map fun row =>
        if answer = row.1 then row.2 else 0).sum : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by
  simpa only [PMF.map_id, id_eq] using pairLaw_map_apply fuel code id answer

private theorem pairLaw_stable (code : Comp)
    (completed : (rationalRows 50 code).all (fun row => row.1.isLeft) = true)
    (fuel : Nat) (enough : 50 ≤ fuel) : pairLaw fuel code = pairLaw 50 code := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  exact congrArg (fun probability => probability.map pairReadout)
    (uniformLaw_stable (machineSpec []) 50 extra (initial code) completed)

/-- All sufficiently large budgets give the correlated diagonal law. -/
theorem captured_probability (fuel : Nat) (enough : 50 ≤ fuel) (first second : Bool) :
    pairLaw fuel capturedCellInCode (some (first, second)) =
      if first = second then 1 / 2 else 0 := by
  rw [pairLaw_stable _ captured_completed fuel enough, pairLaw_apply, captured_rows]
  cases first <;> cases second <;> norm_num

/-- The same quoted consumer with a resampled capture gives four equal masses. -/
theorem resampled_probability (fuel : Nat) (enough : 50 ≤ fuel) (first second : Bool) :
    pairLaw fuel resampledCellInCode (some (first, second)) = 1 / 4 := by
  rw [pairLaw_stable _ resampled_completed fuel enough, pairLaw_apply, resampled_rows]
  cases first <;> cases second <;> norm_num

theorem no_unreturned_mass (fuel : Nat) (enough : 50 ≤ fuel) :
    pairLaw fuel capturedCellInCode none = 0 ∧ pairLaw fuel resampledCellInCode none = 0 := by
  rw [pairLaw_stable _ captured_completed fuel enough,
    pairLaw_stable _ resampled_completed fuel enough]
  simp only [pairLaw_apply, captured_rows, resampled_rows]
  norm_num
  decide

def coordinate (first : Bool) : Option (Bool × Bool) → Option Bool :=
  Option.map fun pair => if first then pair.1 else pair.2

/-- Each individual observation is fair under both programs. This does not
determine their joint law or authorize replacing a retained capture. -/
theorem same_marginals (fuel : Nat) (enough : 50 ≤ fuel) (first : Bool) :
    (pairLaw fuel capturedCellInCode).map (coordinate first) =
      (pairLaw fuel resampledCellInCode).map (coordinate first) := by
  rw [pairLaw_stable _ captured_completed fuel enough,
    pairLaw_stable _ resampled_completed fuel enough]
  ext answer
  rw [pairLaw_map_apply, pairLaw_map_apply, captured_rows, resampled_rows]
  cases first <;> cases answer with
  | none => simp [coordinate]
  | some value => cases value <;> norm_num [coordinate]

theorem different_joint (fuel : Nat) (enough : 50 ≤ fuel) :
    pairLaw fuel capturedCellInCode ≠ pairLaw fuel resampledCellInCode := by
  intro same
  have different := congrArg (fun probability => probability (some (false, true))) same
  rw [captured_probability fuel enough, resampled_probability fuel enough] at different
  have realDifferent := congrArg ENNReal.toReal different
  norm_num at realDifferent

/-- The existing distinction-theoretic nonfactorization criterion applies to
actual machine observations: no function of one marginal recovers every joint. -/
theorem joint_not_factors_marginal (fuel : Nat) (enough : 50 ≤ fuel) (first : Bool) :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors
      (fun code => (pairLaw fuel code).map (coordinate first)) (pairLaw fuel) := by
  apply Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors
  exact ⟨capturedCellInCode, resampledCellInCode,
    same_marginals fuel enough first, different_joint fuel enough⟩

/-- The full retained-machine resumption law specializes to every cut of
these programs, including cuts before and after the first shared production. -/
theorem resumed_pairLaw (code : Comp) (first second : Nat) :
    ((uniformLaw (machineSpec []) first (initial code)).bind
      (Mettapedia.GSLT.Dynamics.ProbabilisticResumption.resumeLaw
        (uniformSource (machineSpec []) ℝ≥0) (uniformSource_normalized (machineSpec [])) second)).map
        pairReadout = pairLaw (first + second) code := by
  rw [← uniformLaw_resume]
  rfl

theorem resumed_captured_probability (first second : Nat) (enough : 50 ≤ first + second)
    (left right : Bool) :
    (((uniformLaw (machineSpec []) first (initial capturedCellInCode)).bind
      (Mettapedia.GSLT.Dynamics.ProbabilisticResumption.resumeLaw
        (uniformSource (machineSpec []) ℝ≥0) (uniformSource_normalized (machineSpec [])) second)).map
        pairReadout) (some (left, right)) = if left = right then 1 / 2 else 0 := by
  rw [resumed_pairLaw]
  exact captured_probability _ enough left right

theorem resumed_resampled_probability (first second : Nat) (enough : 50 ≤ first + second)
    (left right : Bool) :
    (((uniformLaw (machineSpec []) first (initial resampledCellInCode)).bind
      (Mettapedia.GSLT.Dynamics.ProbabilisticResumption.resumeLaw
        (uniformSource (machineSpec []) ℝ≥0) (uniformSource_normalized (machineSpec [])) second)).map
        pairReadout) (some (left, right)) = 1 / 4 := by
  rw [resumed_pairLaw]
  exact resampled_probability _ enough left right

end ProbabilityControls

end Mettapedia.Machines.BranchLocalNeed.Weighted
