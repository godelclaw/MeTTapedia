import Mettapedia.Languages.MeTTa.PrimeCandidates.CallSharingTournament
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceWitnesses

/-!
# Which call-sharing policy is call-time choice

The tournament's four identity policies for call arguments (`perUse`,
`perCandidate`, `perSource`, `perOrigin`) are realized here on the
call-by-push-value core of call-time choice, at one call `f m₁ … mₙ` whose
argument computations `mᵢ` are closed:

* `perSource`: one memoized cell per argument occurrence, allocated before the
  candidates are entered and shared by all of them (`perSourceCall`);
* `perCandidate`: each candidate equation allocates its own cells after the
  fork into candidates (`perCandidateCall`);
* `perUse`: every use draws afresh (`perUseCall`, resampling suspensions);
* `perOrigin`: argument occurrences with equal origin share one cell
  (`perOriginCall`).

Results.

* Call-time choice is `perSource` sharing: the call-time choice translation of
  a call binds exactly `perSourceCall` (`toCore_call_need`); run-time choice
  binds `perUseCall` (`toCore_call_name`).
* `perCandidate` and `perSource` derive the same result lists from every
  configuration, for every program and every call
  (`perCandidate_iff_perSource`): the candidates of a call are branches of one
  fork, each starting from the store of the call, so a cell shared by candidates
  is never observed by two of them.
* `perUse` and `perOrigin` differ from call-time choice on the answers:
  `same pick` and the residual discriminator separate `perUse`, and
  `pairOf pick pick` separates `perOrigin` (`verdict`).
* The residual discriminator gives 2/3/3 answers under call-time choice and
  4/9/9 under `perUse`. The 4/9/7 pattern is produced by no policy; it is the
  loss of the branch's own world at an unmatched return (see the controls of
  the call-time choice specification).

This module concerns the operational face: the typed judgment does not see the
sharing policy, and the extensional face sees only the answer lists compared
here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.CallSharingVerdict

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
open CallSharingTournament (SharingPolicy)

/-! ## The four policies at one call -/

/-- Bind computations as memoized cells, in order. -/
def needChain : List Comp → Comp → Comp
  | [], k => k
  | m :: ms, k => .need m (needChain ms k)

/-- Bind computations as resampling suspensions, in order. -/
def delayChain : List Comp → Comp → Comp
  | [], k => k
  | m :: ms, k => .delay m (delayChain ms k)

/-- Alternatives over a nonempty list of computations; no alternative fails. -/
def chooseAll : List Comp → Comp
  | [] => .fail
  | [m] => m
  | m :: ms => .choose m (chooseAll ms)

/-- Program positions, from `i` on, of the rules with head `f` and arity `n`. -/
def candidateIndicesFrom (f n : Nat) : Nat → List Rule → List Nat
  | _, [] => []
  | i, r :: rs =>
      if (r.head == f && r.arity == n) = true then i :: candidateIndicesFrom f n (i + 1) rs
      else candidateIndicesFrom f n (i + 1) rs

/-- Program positions of the candidates of a call `f` with `n` arguments. -/
def candidateIndices (P : Program) (f n : Nat) : List Nat :=
  candidateIndicesFrom f n 0 P

/-- `perSource`: one cell per argument occurrence, shared by all candidates. -/
def perSourceCall (f : Nat) (ms : List Comp) : Comp :=
  needChain ms (.call f (varsDesc ms.length))

/-- `perCandidate`: every candidate allocates its own cells after the fork. -/
def perCandidateCall (P : Program) (f : Nat) (ms : List Comp) : Comp :=
  match candidateIndices P f ms.length with
  | [] => perSourceCall f ms
  | i :: is => chooseAll ((i :: is).map fun j => needChain ms (.callRule j (varsDesc ms.length)))

/-- `perUse`: every use runs its argument afresh. -/
def perUseCall (f : Nat) (ms : List Comp) : Comp :=
  delayChain ms (.call f (varsDesc ms.length))

/-- The distinct computations of a list, in order of first occurrence. -/
def firstOccurrences (ms : List Comp) : List Comp :=
  ms.foldl (fun acc m => if m ∈ acc then acc else acc ++ [m]) []

/-- `perOrigin`: equal closed argument computations (equal origins) share one
cell. -/
def perOriginCall (f : Nat) (ms : List Comp) : Comp :=
  let ds := firstOccurrences ms
  needChain ds (.call f (ms.map fun m => .var (ds.length - 1 - ds.idxOf m)))

/-- A call under a sharing policy, in the program `P` it runs in. -/
def policyCall (P : Program) : SharingPolicy → Nat → List Comp → Comp
  | .perUse => perUseCall
  | .perCandidate => perCandidateCall P
  | .perSource => perSourceCall
  | .perOrigin => perOriginCall

/-! ## Call-time choice is `perSource`; run-time choice is `perUse` -/

theorem args_toCore_need (r : Nat → Nat) (k : Nat → Comp) :
    ∀ (args : Args) (done : Nat), Args.toCore .need r done args k =
      needChain (args.strictComps .need r done) (k (done + (args.strictComps .need r done).length))
  | .nil, done => by simp [Args.toCore, Args.strictComps, needChain]
  | .cons a rest, done => by
      have hlen : done + 1 + (rest.strictComps .need r (done + 1)).length =
          done + ((rest.strictComps .need r (done + 1)).length + 1) := by omega
      simp only [Args.toCore, Args.strictComps, needChain, bindFor, List.length_cons,
        args_toCore_need r k rest (done + 1), hlen]

theorem args_toCore_name (r : Nat → Nat) (k : Nat → Comp) :
    ∀ (args : Args) (done : Nat), Args.toCore .name r done args k =
      delayChain (args.strictComps .name r done)
        (k (done + (args.strictComps .name r done).length))
  | .nil, done => by simp [Args.toCore, Args.strictComps, delayChain]
  | .cons a rest, done => by
      have hlen : done + 1 + (rest.strictComps .name r (done + 1)).length =
          done + ((rest.strictComps .name r (done + 1)).length + 1) := by omega
      simp only [Args.toCore, Args.strictComps, delayChain, bindFor, List.length_cons,
        args_toCore_name r k rest (done + 1), hlen]

/-- **Call-time choice binds `perSource`.** The call-time choice translation of
a call allocates one memoized cell per argument occurrence and passes the same
cells to every candidate. -/
theorem toCore_call_need (r : Nat → Nat) (f : Nat) (args : Args) :
    (Expr.call f args).toCore .need r = perSourceCall (f + 1) (args.strictComps .need r 0) := by
  simp [Expr.toCore, args_toCore_need, perSourceCall]

/-- **Run-time choice binds `perUse`.** -/
theorem toCore_call_name (r : Nat → Nat) (f : Nat) (args : Args) :
    (Expr.call f args).toCore .name r = perUseCall (f + 1) (args.strictComps .name r 0) := by
  simp [Expr.toCore, args_toCore_name, perUseCall]

/-! ## `perCandidate` derives what `perSource` derives -/

variable (P : Program)

/-- The store and environment after binding a chain of cells. -/
def chainState : Store → List (Val Nat) → List Comp → Store × List (Val Nat)
  | σ, ρ, [] => (σ, ρ)
  | σ, ρ, m :: ms => chainState (σ.alloc m ρ) (.need σ.cells.length :: ρ) ms

theorem needChain_iff : ∀ (ms : List Comp) (σ : Store) (ρ : List (Val Nat)) (k : Comp)
    (L : List Result), Derives P (.eval σ ρ (needChain ms k)) L ↔
      Derives P (.eval (chainState σ ρ ms).1 (chainState σ ρ ms).2 k) L
  | [], σ, ρ, k, L => Iff.rfl
  | m :: ms, σ, ρ, k, L => by
      rw [needChain, chainState, ← needChain_iff ms]
      exact ⟨fun h => by cases h with | need h => exact h, fun h => .need h⟩

theorem chooseAll_iff (ρ : List (Val Nat)) : ∀ (cs : List Comp), cs ≠ [] → ∀ (σ : Store)
    (L : List Result), Derives P (.eval σ ρ (chooseAll cs)) L ↔
      Derives P (.alts σ (cs.map fun c => (c, ρ))) L
  | [], h, _, _ => absurd rfl h
  | [c], _, σ, L => by
      simp only [chooseAll, List.map_cons, List.map_nil]
      constructor
      · intro h; simpa using Derives.altsCons h .altsNil
      · intro h
        cases h with
        | altsCons h₁ h₂ => cases h₂; simpa using h₁
  | c :: c' :: cs, _, σ, L => by
      have ih := chooseAll_iff ρ (c' :: cs) (by simp) σ
      show Derives P (.eval σ ρ (.choose c (chooseAll (c' :: cs)))) L ↔
        Derives P (.alts σ ((c, ρ) :: (c' :: cs).map fun c => (c, ρ))) L
      constructor
      · intro h
        cases h with
        | choose h₁ h₂ => exact .altsCons h₁ ((ih _).mp h₂)
      · intro h
        cases h with
        | altsCons h₁ h₂ => exact .choose h₁ ((ih _).mpr h₂)

/-- Alternatives whose branches derive the same results derive the same
results, whatever their parent stores. -/
theorem alts_congr {σ σ' : Store} :
    ∀ {bs bs' : List (Comp × List (Val Nat))},
      List.Forall₂
        (fun b b' => ∀ L, Derives P (.eval σ b.2 b.1) L ↔ Derives P (.eval σ' b'.2 b'.1) L)
        bs bs' → ∀ L, Derives P (.alts σ bs) L ↔ Derives P (.alts σ' bs') L := by
  intro bs bs' h
  induction h with
  | nil =>
      intro L
      exact ⟨fun h => by cases h; exact .altsNil, fun h => by cases h; exact .altsNil⟩
  | @cons b b' bs bs' hb _ ih =>
      intro L
      obtain ⟨m, ρ⟩ := b
      obtain ⟨m', ρ'⟩ := b'
      constructor
      · intro h
        cases h with
        | altsCons h₁ h₂ => exact .altsCons ((hb _).mp h₁) ((ih _).mp h₂)
      · intro h
        cases h with
        | altsCons h₁ h₂ => exact .altsCons ((hb _).mpr h₁) ((ih _).mpr h₂)

theorem candidateIndicesFrom_spec (f n : Nat) :
    ∀ (pre rs : List Rule),
      List.Forall₂ (fun j r => (pre ++ rs)[j]? = some r ∧ r.arity = n)
        (candidateIndicesFrom f n pre.length rs) (rs.filter fun r => r.head == f && r.arity == n)
  | _, [] => by simp [candidateIndicesFrom]
  | pre, r :: rs => by
      have ih := candidateIndicesFrom_spec f n (pre ++ [r]) rs
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at ih
      by_cases hr : (r.head == f && r.arity == n) = true
      · rw [candidateIndicesFrom, if_pos hr,
          List.filter_cons_of_pos (p := fun (x : Rule) => x.head == f && x.arity == n) hr]
        refine .cons ⟨by simp, ?_⟩ ih
        simp only [Bool.and_eq_true, beq_iff_eq] at hr
        exact hr.2
      · rw [candidateIndicesFrom, if_neg hr,
          List.filter_cons_of_neg (p := fun (x : Rule) => x.head == f && x.arity == n) hr]
        exact ih

theorem candidateIndices_spec (f n : Nat) :
    List.Forall₂ (fun j r => P[j]? = some r ∧ r.arity = n) (candidateIndices P f n)
      (candidates P f n) := by
  have h := candidateIndicesFrom_spec f n [] P
  simp only [List.nil_append, List.length_nil] at h
  exact h

theorem callRule_iff {σ : Store} {ρ : List (Val Nat)} {i : Nat} {args : List VExp} {r : Rule}
    {L : List Result} (hr : P[i]? = some r) (ha : r.arity = args.length) :
    Derives P (.eval σ ρ (.callRule i args)) L ↔
      Derives P (.eval σ (args.map (·.eval ρ)) r.body) L := by
  constructor
  · intro h
    cases h with
    | callRule hr' _ h => rw [hr] at hr'; cases hr'; exact h
    | callRuleNone hn => exact absurd ha (hn r hr)
  · intro h
    exact .callRule hr ha h

/-- **`perCandidate` derives exactly what `perSource` derives**, from every
configuration, for every program and every call. -/
theorem perCandidate_iff_perSource (f : Nat) (ms : List Comp) (σ : Store)
    (ρ : List (Val Nat)) (L : List Result) :
    Derives P (.eval σ ρ (perCandidateCall P f ms)) L ↔
      Derives P (.eval σ ρ (perSourceCall f ms)) L := by
  unfold perCandidateCall
  have hspec := candidateIndices_spec P f ms.length
  cases hidx : candidateIndices P f ms.length with
  | nil => exact Iff.rfl
  | cons i is =>
      rw [hidx] at hspec
      have hlen : (varsDesc ms.length).length = ms.length := by simp [varsDesc]
      have hcands : candidates P f (varsDesc ms.length).length ≠ [] := by
        rw [hlen]; intro h; rw [h] at hspec; cases hspec
      have hrel : List.Forall₂
          (fun b b' => ∀ L, Derives P (.eval σ b.2 b.1) L ↔
            Derives P (.eval (chainState σ ρ ms).1 b'.2 b'.1) L)
          (((i :: is).map fun j => needChain ms (.callRule j (varsDesc ms.length))).map
            fun c => (c, ρ))
          ((candidates P f (varsDesc ms.length).length).map
            fun r => (r.body, (varsDesc ms.length).map (·.eval (chainState σ ρ ms).2))) := by
        rw [List.map_map, hlen]
        refine List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (hspec.imp ?_))
        intro j r ⟨hj, harity⟩ L'
        simp only [Function.comp_apply]
        rw [needChain_iff]
        exact callRule_iff P hj (by rw [harity, hlen])
      rw [chooseAll_iff P ρ ((i :: is).map fun j => needChain ms (.callRule j (varsDesc ms.length)))
        (by simp), perSourceCall, needChain_iff]
      constructor
      · intro h
        exact .call hcands ((alts_congr P hrel L).mp h)
      · intro h
        cases h with
        | call _ h => exact (alts_congr P hrel L).mpr h
        | callNone hc => exact absurd hc hcands

/-! ## Separating witnesses -/

namespace Witness

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Witnesses.Core

/-- The observed answers of a call under a policy. -/
def answers (pol : SharingPolicy) (f : Nat) (ms : List Comp) : Option (List (Val Nat)) :=
  observeValues program 200 (policyCall (observed program) pol f ms)

theorem same_perSource :
    answers .perSource fSame [pickC] = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem same_perUse :
    answers .perUse fSame [pickC] = some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

theorem pairOf_perSource :
    answers .perSource fPairOf [pickC, pickC] =
      some [pair vA vA, pair vA vB, pair vB vA, pair vB vB] := by
  decide +kernel

theorem pairOf_perOrigin :
    answers .perOrigin fPairOf [pickC, pickC] = some [pair vA vA, pair vB vB] := by
  decide +kernel

theorem keep_perSource :
    answers .perSource fKeep [.call fSp1 []] =
      some [pair (residual (tagged symB sym1)) (tagged symB sym1),
        pair (residual (tagged symB sym2)) (tagged symB sym2)] ∧
    (answers .perSource fKeep [.call fSp2 []]).map List.length = some 3 ∧
    answers .perSource fKeep [.call fSp3 []] =
      some [pair (.app (.sym symOK) (.sym sym3)) (tagged symA sym3),
        pair (residual (tagged symB sym1)) (tagged symB sym1),
        pair (residual (tagged symB sym2)) (tagged symB sym2)] := by
  decide +kernel

/-- Resampling every use gives 4/9/9 answers on the residual discriminator. -/
theorem keep_perUse :
    (answers .perUse fKeep [.call fSp1 []]).map List.length = some 4 ∧
    (answers .perUse fKeep [.call fSp2 []]).map List.length = some 9 ∧
    (answers .perUse fKeep [.call fSp3 []]).map List.length = some 9 := by
  decide +kernel

/-- Two candidate equations sharing the argument cell, or each with its own:
the same answers, in the same order. -/
theorem twoWay_perCandidate :
    answers .perCandidate fTwoWay [pickC] = answers .perSource fTwoWay [pickC] ∧
    answers .perSource fTwoWay [pickC] =
      some [pair vA vA, pair vB vB, pair vA vA, pair vB vA] := by
  decide +kernel

/-- No sharing policy gives the 4/9/7 answer counts on the residual
discriminator. -/
theorem keep_no_policy_gives_4_9_7 (pol : SharingPolicy) :
    ((answers pol fKeep [.call fSp1 []]).map List.length,
      (answers pol fKeep [.call fSp2 []]).map List.length,
      (answers pol fKeep [.call fSp3 []]).map List.length) ≠ (some 4, some 9, some 7) := by
  cases pol <;> decide +kernel

def witnesses : List (Nat × List Comp) :=
  [(fSame, [pickC]), (fPairOf, [pickC, pickC]), (fKeep, [.call fSp1 []]),
    (fKeep, [.call fSp2 []]), (fKeep, [.call fSp3 []]), (fTwoWay, [pickC])]

/-- **The policy verdict.** On the separating witnesses, a sharing policy gives
the call-time choice answers (`perSource`) exactly when it is `perSource` or
`perCandidate`. With `perCandidate_iff_perSource`, `perCandidate` agrees on
every call; `perUse` and `perOrigin` do not. -/
theorem verdict (pol : SharingPolicy) :
    (∀ w ∈ witnesses, answers pol w.1 w.2 = answers .perSource w.1 w.2) ↔
      pol = .perSource ∨ pol = .perCandidate := by
  cases pol <;> decide +kernel

end Witness

end Mettapedia.Languages.MeTTa.PrimeCandidates.CallSharingVerdict
