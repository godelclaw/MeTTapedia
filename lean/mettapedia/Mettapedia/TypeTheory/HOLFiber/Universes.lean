import Mathlib.Computability.Halting
import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.Computability.ArithmeticalHierarchy.Basic
import Mettapedia.TypeTheory.HOLFiber.PropositionalDecision

/-!
# The verification universe and the computational universe

Two universes meet at the HOL fiber.

* **Verification.** A judgment is checked from a finite certificate by a total
  Boolean checker (`KernelAuthority.Checker`); an exact authority identifies
  the judgment with the existence of an accepted certificate.
* **Computation.** A computation is a machine whose single step is an
  effectful program of the contextual effect syntax (`Program`: choice, state
  reads and writes, deferred intents), returning either the next machine state
  or an answer. One step is a finite program, since `Program` is an inductive
  type; nontermination enters only by iterating steps. A machine state paired
  with its machine is the thunk that CBPV's `U` makes into data.

**Observations.** The `k`-fuel unfolding of a machine is one finite program,
and the isolated-world handler `runWorlds` evaluates it to a finite list of
worlds. Whether some world answers within `k` steps is therefore a Boolean
computed by the handler (`Machine.observe`). It is monotone in the fuel
(`Machine.observe_mono`), so "eventually answers" is an existential over a
decided, upward-closed prefix observation, and "never answers" is the dual
universal (`Machine.Answers`, `Machine.NeverAnswers`).

**The arithmetic classification**, for deterministic machines whose step and
halting test are primitive recursive (`PrimMachine`):

* "halts" is recursively enumerable (`PrimMachine.halts_re`), "never halts" has
  a recursively enumerable complement, and "infinitely often good" is a
  universal-existential statement over a primitive recursive matrix
  (`PrimMachine.infOften_iff`); on the numbers these are the tree's `Σ⁰₁`,
  `Π⁰₁` and `Π⁰₂` predicates (`halts_sigma01`, `neverHalts_pi01`,
  `infOften_pi02`);
* the first two classifications are exact for the machine that runs bounded
  evaluation of partial recursive codes (`haltingMachine`): halting is not
  computable (`haltingMachine_halts_not_computable`), and never halting is not
  recursively enumerable (`haltingMachine_neverHalts_not_re`).

No lower bound is claimed for the `Π⁰₂` observation.

**Checkers are computations.** For a checker and an enumeration of its
certificates, the search machine tries certificates in order and answers with
the index of the first accepted one (`searchMachine`). In the computational
universe it eventually answers exactly when an accepted certificate exists
(`searchMachine_answers_iff`), every answer it gives indexes an accepted
certificate (`searchMachine_answer_accepted`), and under an exact authority it
eventually answers exactly when the judgment holds
(`searchMachine_reflects`). With a computable checker over encodable claims and
certificates the judgment is recursively enumerable (`authority_re`). The
instances are the bounded-evaluation checker of halting
(`haltingSearch_reflects`) and the decision kernel of the propositional bubble
of the HOL fiber (`propositionalSearch_reflects`), whose search answers at
fuel one or never.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HOLFiber.Universes

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
universe uS uSt uA uI

/-! ## Machines of the computational universe -/

/-- A machine: one step is an effectful program that returns the next state or
an answer. -/
structure Machine (S : Type uS) (St : Type uSt) (A : Type uA) (I : Type uI) where
  step : S → Program St (S ⊕ A) I

namespace Machine

variable {S : Type uS} {St : Type uSt} {A : Type uA} {I : Type uI}

/-- The continuation after one step: continue with the given unfolding, or
return the answer. -/
def resume (next : S → Program St (Option A) I) : S ⊕ A → Program St (Option A) I
  | .inl s => next s
  | .inr a => .pure (some a)

/-- The unfolding with `k` steps of fuel: one finite program. `none` marks
exhausted fuel. -/
def unfold (m : Machine S St A I) : ℕ → S → Program St (Option A) I
  | 0, _ => .pure none
  | k + 1, s => Program.bind (m.step s) (resume (m.unfold k))

/-- Some isolated world of the `k`-fuel unfolding, from branch `branch`,
returns an answer satisfying `P`. -/
def observeAt (m : Machine S St A I) (P : A → Bool) (k : ℕ) (s : S) (σ : St)
    (branch : BranchTrace) : Bool :=
  (runWorldsAt (m.unfold k s) σ branch).any fun w => w.answer.any P

/-- The rooted observation. -/
def observe (m : Machine S St A I) (P : A → Bool) (k : ℕ) (s : S) (σ : St) : Bool :=
  m.observeAt P k s σ []

/-! ### Sequencing and the handler -/

/-- The handler sees through sequencing: a world of `bind p f` satisfies an
answer test exactly when some world of `p` continues into one that does. -/
theorem any_runWorldsAt_bind {B : Type uA} (Q : B → Bool)
    (f : (S ⊕ A) → Program St B I) :
    ∀ (p : Program St (S ⊕ A) I) (σ : St) (branch : BranchTrace),
      (runWorldsAt (Program.bind p f) σ branch).any (fun w => Q w.answer) = true ↔
        ∃ w ∈ runWorldsAt p σ branch,
          (runWorldsAt (f w.answer) w.state w.branch).any (fun w => Q w.answer) = true
  | .pure a, σ, branch => by simp [Program.bind, runWorldsAt]
  | .choose l r, σ, branch => by
      simp only [Program.bind, runWorldsAt, List.any_append, Bool.or_eq_true,
        List.mem_append]
      rw [any_runWorldsAt_bind Q f l, any_runWorldsAt_bind Q f r]
      constructor
      · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
        · exact ⟨w, .inl hw, h⟩
        · exact ⟨w, .inr hw, h⟩
      · rintro ⟨w, hw | hw, h⟩
        · exact .inl ⟨w, hw, h⟩
        · exact .inr ⟨w, hw, h⟩
  | .read next, σ, branch => by
      simp only [Program.bind, runWorldsAt]
      exact any_runWorldsAt_bind Q f (next σ) σ branch
  | .write newState next, σ, branch => by
      simp only [Program.bind, runWorldsAt]
      exact any_runWorldsAt_bind Q f next newState branch
  | .intent request next, σ, branch => by
      simp only [Program.bind, runWorldsAt, List.any_map]
      have h := any_runWorldsAt_bind Q f next σ branch
      simp only [Function.comp_def] at h ⊢
      rw [h]
      simp only [List.mem_map]
      constructor
      · rintro ⟨w, hw, h⟩
        exact ⟨{ w with intents := request :: w.intents }, ⟨w, hw, rfl⟩, h⟩
      · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
        exact ⟨w, hw, h⟩

/-- **More fuel never loses an answer.** -/
theorem observeAt_mono (m : Machine S St A I) (P : A → Bool) :
    ∀ (k : ℕ) (s : S) (σ : St) (branch : BranchTrace),
      m.observeAt P k s σ branch = true → m.observeAt P (k + 1) s σ branch = true
  | 0, s, σ, branch, h => by
      simp [observeAt, unfold, runWorldsAt] at h
  | k + 1, s, σ, branch, h => by
      unfold observeAt at h ⊢
      simp only [unfold] at h ⊢
      rw [any_runWorldsAt_bind (Option.any P)] at h
      rw [any_runWorldsAt_bind (Option.any P)]
      obtain ⟨w, hw, hcont⟩ := h
      refine ⟨w, hw, ?_⟩
      cases hanswer : w.answer with
      | inl s' =>
          rw [hanswer] at hcont
          exact observeAt_mono m P k s' w.state w.branch hcont
      | inr a =>
          rw [hanswer] at hcont
          exact hcont

theorem observe_mono (m : Machine S St A I) (P : A → Bool) {k k' : ℕ} (le : k ≤ k')
    {s : S} {σ : St} (h : m.observe P k s σ = true) : m.observe P k' s σ = true := by
  induction le with
  | refl => exact h
  | step _ ih => exact observeAt_mono m P _ s σ [] ih

/-- Eventually some world answers with an answer satisfying `P`: an
existential over a decided prefix observation. -/
def Answers (m : Machine S St A I) (P : A → Bool) (s : S) (σ : St) : Prop :=
  ∃ k, m.observe P k s σ = true

/-- No world ever answers with an answer satisfying `P`: the dual universal. -/
def NeverAnswers (m : Machine S St A I) (P : A → Bool) (s : S) (σ : St) : Prop :=
  ∀ k, m.observe P k s σ = false

theorem neverAnswers_iff_not_answers (m : Machine S St A I) (P : A → Bool) (s : S) (σ : St) :
    m.NeverAnswers P s σ ↔ ¬ m.Answers P s σ := by
  simp [NeverAnswers, Answers]

/-! ### Deterministic machines -/

/-- A machine whose step makes no choice and no effect. -/
def ofFun (f : S → S ⊕ A) : Machine S St A I where
  step s := .pure (f s)

/-- The deterministic run with `k` steps of fuel. -/
def detRun (f : S → S ⊕ A) : ℕ → S → Option A
  | 0, _ => none
  | k + 1, s => match f s with
    | .inl s' => detRun f k s'
    | .inr a => some a

theorem runWorldsAt_unfold_ofFun (f : S → S ⊕ A) :
    ∀ (k : ℕ) (s : S) (σ : St) (branch : BranchTrace),
      runWorldsAt ((ofFun (I := I) f).unfold k s) σ branch =
        [{ branch := branch, answer := detRun f k s, state := σ, intents := [] }]
  | 0, s, σ, branch => rfl
  | k + 1, s, σ, branch => by
      simp only [unfold, ofFun, Program.pure_bind, detRun]
      cases f s with
      | inl s' => exact runWorldsAt_unfold_ofFun f k s' σ branch
      | inr a => rfl

theorem observe_ofFun (f : S → S ⊕ A) (P : A → Bool) (k : ℕ) (s : S) (σ : St) :
    (ofFun (I := I) f).observe P k s σ = (detRun f k s).any P := by
  simp [observe, observeAt, runWorldsAt_unfold_ofFun]

end Machine

/-! ## Checkers are computations -/

section Search

variable {Claim : Type uS} {Certificate : Type uA}

/-- The search step: accept index `k` when its certificate is accepted,
otherwise move to `k + 1`. -/
def searchStep (checker : Checker Claim Certificate) (enum : ℕ → Certificate) (claim : Claim)
    (k : ℕ) : ℕ ⊕ ℕ :=
  if checker.check claim (enum k) then .inr k else .inl (k + 1)

/-- The search machine of a checker and an enumeration of its certificates. -/
def searchMachine (St : Type uSt) (I : Type uI) (checker : Checker Claim Certificate)
    (enum : ℕ → Certificate) (claim : Claim) : Machine ℕ St ℕ I :=
  Machine.ofFun (searchStep checker enum claim)

theorem detRun_search_accepted (checker : Checker Claim Certificate) (enum : ℕ → Certificate)
    (claim : Claim) :
    ∀ (k j a : ℕ), Machine.detRun (searchStep checker enum claim) k j = some a →
      checker.check claim (enum a) = true
  | 0, _, _, h => by cases h
  | k + 1, j, a, h => by
      simp only [Machine.detRun, searchStep] at h
      by_cases accepted : checker.check claim (enum j) = true
      · rw [if_pos accepted] at h
        cases h
        exact accepted
      · rw [if_neg accepted] at h
        exact detRun_search_accepted checker enum claim k (j + 1) a h

theorem detRun_search_isSome (checker : Checker Claim Certificate) (enum : ℕ → Certificate)
    (claim : Claim) :
    ∀ (d j : ℕ), checker.check claim (enum (j + d)) = true →
      (Machine.detRun (searchStep checker enum claim) (d + 1) j).isSome = true
  | 0, j, h => by
      simp only [Machine.detRun, searchStep, Nat.add_zero] at h ⊢
      rw [if_pos h]
      rfl
  | d + 1, j, h => by
      simp only [Machine.detRun, searchStep]
      by_cases accepted : checker.check claim (enum j) = true
      · rw [if_pos accepted]; rfl
      · rw [if_neg accepted]
        have shifted : j + 1 + d = j + (d + 1) := by omega
        exact detRun_search_isSome checker enum claim d (j + 1) (by rw [shifted]; exact h)

/-- Every answer of the search indexes an accepted certificate. -/
theorem searchMachine_answer_accepted
    (checker : Checker Claim Certificate) (enum : ℕ → Certificate) (claim : Claim)
    {k : ℕ} {a : ℕ}
    (h : Machine.detRun (searchStep checker enum claim) k 0 = some a) :
    checker.check claim (enum a) = true :=
  detRun_search_accepted checker enum claim k 0 a h

/-- **The search eventually answers exactly when an enumerated certificate is
accepted.** -/
theorem searchMachine_answers_iff {St : Type uSt} {I : Type uI}
    (checker : Checker Claim Certificate) (enum : ℕ → Certificate) (claim : Claim) (σ : St) :
    (searchMachine St I checker enum claim).Answers (fun _ => true) 0 σ ↔
      ∃ k, checker.check claim (enum k) = true := by
  unfold Machine.Answers searchMachine
  simp only [Machine.observe_ofFun]
  constructor
  · rintro ⟨k, h⟩
    cases hrun : Machine.detRun (searchStep checker enum claim) k 0 with
    | none => rw [hrun] at h; cases h
    | some a => exact ⟨a, detRun_search_accepted checker enum claim k 0 a hrun⟩
  · rintro ⟨k, h⟩
    refine ⟨k + 1, ?_⟩
    have isSome := detRun_search_isSome checker enum claim k 0 (by rwa [Nat.zero_add])
    cases hrun : Machine.detRun (searchStep checker enum claim) (k + 1) 0 with
    | none => rw [hrun] at isSome; cases isSome
    | some a => rfl

/-- **Checker reflection.** Under an exact authority and a surjective
enumeration of certificates, running the search in the computational universe
eventually answers exactly when the judgment holds in the verification
universe. -/
theorem searchMachine_reflects {St : Type uSt} {I : Type uI}
    {checker : Checker Claim Certificate} {Meaning : Claim → Prop}
    (authority : checker.Authority Meaning) {enum : ℕ → Certificate}
    (onto : Function.Surjective enum) (claim : Claim) (σ : St) :
    (searchMachine St I checker enum claim).Answers (fun _ => true) 0 σ ↔ Meaning claim := by
  rw [searchMachine_answers_iff, authority.meaning_iff_exists_certificate]
  constructor
  · rintro ⟨k, h⟩
    exact ⟨enum k, h⟩
  · rintro ⟨certificate, h⟩
    obtain ⟨k, rfl⟩ := onto certificate
    exact ⟨k, h⟩

end Search

/-! ## Recursive enumerability of certificate authority -/

/-- An existential over a computable Boolean matrix is recursively enumerable. -/
theorem rePred_exists {α : Type uS} [Primcodable α] {f : α → ℕ → Bool} (hf : Computable₂ f) :
    REPred fun a => ∃ k, f a k = true := by
  let p : α → ℕ →. Bool := fun a k => Part.some (f a k)
  have hp : Partrec fun a => Nat.rfind (p a) := Partrec.rfind hf.partrec₂
  refine (Partrec.dom_re hp).of_eq fun a => Nat.rfind_dom.trans ?_
  constructor
  · rintro ⟨n, hn, -⟩
    exact ⟨n, (Part.mem_some_iff.mp hn).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun _ => trivial⟩

/-- **Theoremhood is recursively enumerable.** A judgment with an exact
authority whose checker is computable, over encodable claims and certificates,
is recursively enumerable. -/
theorem authority_re {Claim : Type uS} {Certificate : Type uA} [Primcodable Claim]
    [Primcodable Certificate] {checker : Checker Claim Certificate} {Meaning : Claim → Prop}
    (authority : checker.Authority Meaning)
    (computable : Computable fun input : Claim × Certificate => checker.check input.1 input.2) :
    REPred Meaning := by
  have hcheck : Computable₂ fun (input : Claim × ℕ) (certificate : Certificate) =>
      checker.check input.1 certificate := by
    have pairing : Computable fun x : (Claim × ℕ) × Certificate => (x.1.1, x.2) :=
      (Computable.fst.comp Computable.fst).pair Computable.snd
    exact (computable.comp pairing).of_eq fun _ => rfl
  have hdecode : Computable fun input : Claim × ℕ => Encodable.decode (α := Certificate) input.2 :=
    Computable.decode.comp Computable.snd
  have hg : Computable₂ fun (claim : Claim) (n : ℕ) =>
      (Option.casesOn (motive := fun _ => Bool) (Encodable.decode (α := Certificate) n) false
        (checker.check claim) : Bool) :=
    Computable.option_casesOn hdecode (Computable.const false) hcheck
  refine (rePred_exists hg).of_eq fun claim => ?_
  rw [authority.meaning_iff_exists_certificate]
  constructor
  · rintro ⟨n, h⟩
    revert h
    cases Encodable.decode (α := Certificate) n with
    | none => intro h; cases h
    | some certificate => intro h; exact ⟨certificate, h⟩
  · rintro ⟨certificate, h⟩
    refine ⟨Encodable.encode certificate, ?_⟩
    simp only [Encodable.encodek]
    exact h

/-! ## Deterministic primitive recursive machines and the hierarchy -/

/-- A deterministic machine whose step and halting test are primitive
recursive. -/
structure PrimMachine (σ : Type uS) [Primcodable σ] where
  step : σ → σ
  halted : σ → Bool
  step_primrec : Primrec step
  halted_primrec : Primrec halted

namespace PrimMachine

variable {σ : Type uS} [Primcodable σ] (m : PrimMachine σ)

/-- The prefix observation: halted after exactly `k` steps. -/
def haltedAt (s : σ) (k : ℕ) : Bool := m.halted (m.step^[k] s)

theorem iterate_primrec : Primrec fun p : σ × ℕ => m.step^[p.2] p.1 :=
  Primrec.nat_iterate Primrec.snd Primrec.fst (m.step_primrec.comp Primrec.snd).to₂

theorem haltedAt_primrec : Primrec₂ m.haltedAt :=
  m.halted_primrec.comp m.iterate_primrec

def Halts (s : σ) : Prop := ∃ k, m.haltedAt s k = true

def NeverHalts (s : σ) : Prop := ∀ k, m.haltedAt s k = false

/-- Infinitely often in a primitive recursive set of states. -/
def InfOften (good : σ → Bool) (s : σ) : Prop := ∀ j, ∃ k, j ≤ k ∧ good (m.step^[k] s) = true

/-- **Halting is recursively enumerable.** -/
theorem halts_re : REPred m.Halts :=
  rePred_exists m.haltedAt_primrec.to_comp

/-- **Never halting has a recursively enumerable complement.** -/
theorem neverHalts_compl_re : REPred fun s => ¬ m.NeverHalts s :=
  m.halts_re.of_eq fun s => by simp [Halts, NeverHalts]

/-- **Infinitely often is universal-existential over a primitive recursive
matrix.** -/
theorem infOften_iff (good : σ → Bool) (s : σ) :
    m.InfOften good s ↔
      ∀ j, ∃ k, (decide (j ≤ k) && good (m.step^[k] s)) = true := by
  simp [InfOften]

end PrimMachine

/-! ### On the numbers: the tree's arithmetical classes -/

namespace PrimMachine

open Mettapedia.Computability.ArithmeticalHierarchy

variable (m : PrimMachine ℕ)

/-- Halting is a `Σ⁰₁` predicate. -/
def halts_sigma01 : Sigma01Predicate m.Halts where
  approx := m.haltedAt
  approx_computable := m.haltedAt_primrec.to_comp.of_eq fun _ => rfl
  converges _ := Iff.rfl

/-- Never halting is a `Π⁰₁` predicate. -/
def neverHalts_pi01 : Pi01Predicate m.NeverHalts where
  approx s k := !m.haltedAt s k
  approx_computable :=
    (Primrec.not.comp m.haltedAt_primrec).to_comp.of_eq fun _ => rfl
  converges s := by simp [NeverHalts]

/-- Visiting a primitive recursive set infinitely often is a `Π⁰₂` predicate. -/
def infOften_pi02 {good : ℕ → Bool} (hgood : Primrec good) : Pi02Predicate (m.InfOften good) where
  approx s k := good (m.step^[k] s)
  approx_computable := (hgood.comp m.iterate_primrec).to_comp
  converges _ := by simp [InfOften]

end PrimMachine

/-! ### Exactness at the halting machine -/

/-- Bounded evaluation of a partial recursive code on input zero, one more step
of budget per machine step. -/
def haltingMachine : PrimMachine (Nat.Partrec.Code × ℕ) where
  step p := (p.1, p.2 + 1)
  halted p := (Nat.Partrec.Code.evaln p.2 p.1 0).isSome
  step_primrec := Primrec.fst.pair (Primrec.succ.comp Primrec.snd)
  halted_primrec := Primrec.option_isSome.comp
    (Nat.Partrec.Code.primrec_evaln.comp ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)))

theorem haltingMachine_iterate (c : Nat.Partrec.Code) (k : ℕ) :
    ∀ j, haltingMachine.step^[j] (c, k) = (c, k + j)
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', haltingMachine_iterate c k j]
      rfl

theorem haltingMachine_halts_iff (c : Nat.Partrec.Code) :
    haltingMachine.Halts (c, 0) ↔ HaltingMeaning c := by
  rw [haltingTrustBoundaryAuthority.meaning_iff_exists_certificate]
  simp only [PrimMachine.Halts, PrimMachine.haltedAt, haltingMachine_iterate, Nat.zero_add]
  rfl

/-- **Halting of the machine is not computable**: the `Σ⁰₁` classification is
not `Δ⁰₁`. -/
theorem haltingMachine_halts_not_computable : ¬ ComputablePred haltingMachine.Halts := by
  intro decidable
  apply haltingMeaning_not_computable
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.mp decidable
  rw [ComputablePred.computable_iff]
  refine ⟨fun c => f (c, 0), hf.comp (Computable.id.pair (Computable.const 0)), ?_⟩
  funext c
  exact propext ((haltingMachine_halts_iff c).symm.trans (by rw [hfeq]))

/-- **Never halting is not recursively enumerable**: the `Π⁰₁` classification
is not `Σ⁰₁`. -/
theorem haltingMachine_neverHalts_not_re : ¬ REPred haltingMachine.NeverHalts := by
  intro enumerable
  apply ComputablePred.halting_problem_not_re 0
  have composed : REPred fun c : Nat.Partrec.Code => haltingMachine.NeverHalts (c, 0) :=
    Partrec.comp (show Partrec _ from enumerable) (Computable.id.pair (Computable.const 0))
  refine composed.of_eq fun c => ?_
  have := haltingMachine_halts_iff c
  simp only [PrimMachine.Halts, PrimMachine.NeverHalts] at this ⊢
  rw [HaltingMeaning] at this
  constructor
  · intro never halts
    obtain ⟨k, hk⟩ := this.mpr halts
    rw [never k] at hk
    cases hk
  · intro notHalts k
    cases h : haltingMachine.haltedAt (c, 0) k with
    | false => rfl
    | true => exact (notHalts (this.mp ⟨k, h⟩)).elim

/-! ## Instances of checker reflection -/

/-- The bounded-evaluation checker, run as a search over budgets, eventually
answers exactly when the code halts on zero. -/
theorem haltingSearch_reflects {St : Type uSt} {I : Type uI} (c : Nat.Partrec.Code) (σ : St) :
    (searchMachine St I haltingTrustBoundaryChecker id c).Answers (fun _ => true) 0 σ ↔
      HaltingMeaning c :=
  searchMachine_reflects haltingTrustBoundaryAuthority Function.surjective_id c σ

open Mettapedia.Logic.HOL Mettapedia.Logic.HOL.PropositionalSlice in
/-- The decision kernel of the propositional bubble, run as a search over its
trivial certificates, eventually answers exactly when HOL with excluded middle
proves the image of the formula. -/
theorem propositionalSearch_reflects {St : Type uSt} {I : Type uI}
    (φ : PropFormula) (σ : St) :
    (searchMachine St I PropositionalDecision.decisionKernel.toChecker (fun _ => ()) φ).Answers
        (fun _ => true) 0 σ ↔
      ClosedTheorySet.Provable (EMSchema Atom) (embedP φ) :=
  searchMachine_reflects PropositionalDecision.decisionKernel_authority
    (fun () => ⟨0, rfl⟩) φ σ

/-! ## Axiom audit -/

#print axioms Machine.observe_mono
#print axioms searchMachine_reflects
#print axioms authority_re
#print axioms PrimMachine.halts_re
#print axioms PrimMachine.halts_sigma01
#print axioms PrimMachine.neverHalts_pi01
#print axioms PrimMachine.infOften_pi02
#print axioms haltingMachine_halts_not_computable
#print axioms haltingMachine_neverHalts_not_re
#print axioms haltingSearch_reflects
#print axioms propositionalSearch_reflects

end Mettapedia.TypeTheory.HOLFiber.Universes
