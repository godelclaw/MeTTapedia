import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSentences
import Mettapedia.Logic.HOL.ProofSyntaxModuloStructural

/-!
# Derivations about hereditarily finite sets from the laws of the empty set, the power set and separation

The checker of the package of set theory reads proofs of implication and universal quantification modulo conversion
(`ProofSyntaxModulo`). This module builds such proofs, from three laws of the sets with their connectives written
out (`lawEmpty`, `lawPower`, `lawSeparation`), about the descriptions of hereditary terms (`describes`).

- **Plumbing.** Laws are available in every context, under binders and new hypotheses (`HasLaws`); a law's
  quantifiers are instantiated by terms (`allInstance`, `emptyAt`, `powerAt`, `separationAt`).
- **Descriptions** are used and introduced member by member (`describesForward`, `describesBackward`,
  `oneIntro`, `oneCases`).
- **Every hereditary term describes a set** (`describedExists`): the set of what its members describe, separated from
  an iterated power set of the empty set (`witness`, `inPowerIter`).
- **Presentations of one set describe the same sets** (`describesSame`), and **terms of different sets describe no
  common set** (`describesDistinct`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename
  ProofSyntaxModulo DefiningEquation weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member separate)

/-- Proofs of the checker modulo β-conversion, with no defining equations. -/
abbrev Proof {Γ : Ctx Unit} (Δ : List (Term Symbol Γ .prop)) (φ : Term Symbol Γ .prop) : Type :=
  ProofSyntaxModulo ([] : List (DefiningEquation Symbol)) Δ φ

/-! ## Renaming as substitution -/

section Renaming

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

theorem rename_eq_subst {Γ Δ : Ctx Base} : ∀ {τ : Ty Base} (ρ : Rename Base Γ Δ) (t : Term Const Γ τ),
    rename ρ t = subst (fun index => .var (ρ index)) t := by
  intro τ ρ t
  induction t generalizing Δ with
  | var => rfl
  | const => rfl
  | app _ _ ihf iht => simp only [rename, subst, ihf, iht]
  | lam _ ih =>
    simp only [rename, subst, ih]
    congr 1
    apply Mettapedia.Logic.HOL.subst_ext
    intro _ index
    cases index <;> rfl
  | top => rfl
  | bot => rfl
  | and _ _ ihp ihq | or _ _ ihp ihq | imp _ _ ihp ihq | eq _ _ ihp ihq => simp only [rename, subst, ihp, ihq]
  | not _ ih => simp only [rename, subst, ih]
  | all _ ih | ex _ ih =>
    simp only [rename, subst, ih]
    congr 1
    apply Mettapedia.Logic.HOL.subst_ext
    intro _ index
    cases index <;> rfl

end Renaming

/-! ## Moving proofs -/

section Moving

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- A proof stays a proof under a new hypothesis. -/
def Proof.prepend {φ : Term Symbol Γ .prop} (ψ : Term Symbol Γ .prop) (proof : Proof Δ φ) : Proof (ψ :: Δ) φ :=
  ProofSyntaxModulo.mono (Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap.prepend ψ) proof

/-- A proof stays a proof under a new variable. -/
def Proof.lift {φ : Term Symbol Γ .prop} {σ : Ty Unit} (proof : Proof Δ φ) :
    Proof (weakenHyps (σ := σ) Δ) (weaken φ) :=
  ProofSyntaxModulo.weaken proof

/-- Retyping along an equality of formulas. -/
def Proof.cast {φ ψ : Term Symbol Γ .prop} (same : φ = ψ) (proof : Proof Δ φ) : Proof Δ ψ :=
  Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo.cast same proof

/-- The newest hypothesis. -/
def Proof.newest (φ : Term Symbol Γ .prop) : Proof (φ :: Δ) φ := .hyp ⟨0, by simp⟩

/-- `⊥` proves everything. -/
def Proof.absurd {φ : Term Symbol Γ .prop} (proof : Proof Δ falsity) : Proof Δ φ :=
  .allE (σ := .prop) φ proof

/-- The forward half of an equivalence. -/
def Proof.iffForward {φ ψ : Term Symbol Γ .prop} (equivalence : Proof Δ (iffCore φ ψ)) (proof : Proof Δ φ) :
    Proof Δ ψ :=
  .impE (conjunctionLeft equivalence) proof

/-- The backward half of an equivalence. -/
def Proof.iffBackward {φ ψ : Term Symbol Γ .prop} (equivalence : Proof Δ (iffCore φ ψ)) (proof : Proof Δ ψ) :
    Proof Δ φ :=
  .impE (conjunctionRight equivalence) proof

/-- An equivalence from its two halves, each under its premise. -/
def Proof.iffIntro {φ ψ : Term Symbol Γ .prop} (forward : Proof (φ :: Δ) ψ) (backward : Proof (ψ :: Δ) φ) :
    Proof Δ (iffCore φ ψ) :=
  conjunctionIntro (.impI forward) (.impI backward)

end Moving

/-! ## Weakening the formulas -/

theorem weaken_eq_subst {Γ : Ctx Unit} {σ τ : Ty Unit} (t : Term Symbol Γ τ) :
    weaken (σ := σ) t = subst (fun index => .var (Var.vs index)) t :=
  rename_eq_subst _ t

theorem weaken_describes {Γ : Ctx Unit} {σ : Ty Unit} (term : Pattern) (x : Term Symbol Γ setTy) :
    weaken (σ := σ) (describes term x) = describes term (weaken x) := by
  rw [weaken_eq_subst, subst_describes, ← weaken_eq_subst]

theorem weaken_describesOne {Γ : Ctx Unit} {σ : Ty Unit} (values : List Pattern) (y : Term Symbol Γ setTy) :
    weaken (σ := σ) (describesOne values y) = describesOne values (weaken y) := by
  rw [weaken_eq_subst, subst_describesOne, ← weaken_eq_subst]

theorem weaken_typedFormula {Γ : Ctx Unit} {σ : Ty Unit} (type : TypeExpr) (x : Term Symbol Γ setTy) :
    weaken (σ := σ) (typedFormula type x) = typedFormula type (weaken x) := by
  rw [weaken_eq_subst, subst_typedFormula, ← weaken_eq_subst]

theorem weaken_nativeFormula {Γ : Ctx Unit} {σ : Ty Unit} {n : ℕ} (formula : Formula n) (modal : formula.modal = true)
    (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    weaken (σ := σ) (nativeFormula formula x env) = nativeFormula formula (weaken x) fun index => weaken (env index) := by
  rw [weaken_eq_subst, subst_nativeFormula _ formula modal]
  simp only [← weaken_eq_subst]

theorem weaken_nativeFormula_regional {Γ : Ctx Unit} {σ : Ty Unit} {n : ℕ} (formula : Formula n)
    (regional : formula.regional = true) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    weaken (σ := σ) (nativeFormula formula x env) = nativeFormula formula (weaken x) fun index => weaken (env index) := by
  rw [weaken_eq_subst, subst_nativeFormula_regional _ formula regional]
  simp only [← weaken_eq_subst]

theorem instantiate_describes {Γ : Ctx Unit} {σ : Ty Unit} (term : Pattern) (t : Term Symbol Γ σ)
    (x : Term Symbol Γ setTy) : instantiate t (describes term (weaken x)) = describes term x := by
  unfold instantiate
  rw [subst_describes, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_describesOne {Γ : Ctx Unit} (values : List Pattern) (y : Term Symbol Γ setTy) :
    instantiate y (describesOne values (.var .vz)) = describesOne values y := by
  unfold instantiate
  rw [subst_describesOne]
  rfl

/-! ## The laws -/

/-- The law of the empty set, written out: `∀ x. x ∈ Empty → ⊥`. -/
def lawEmpty : ClosedFormula Symbol :=
  .all (negCore (member (.var .vz) (.const .empty)))

/-- The law of the power set, written out: `∀ a b. b ∈ Power a ↔ ∀ z. z ∈ b → z ∈ a`. -/
def lawPower : ClosedFormula Symbol :=
  .all (.all (iffCore (member (.var .vz) (.app (.const .power) (.var (.vs .vz))))
    (.all (.imp (member (.var .vz) (.var (.vs .vz))) (member (.var .vz) (.var (.vs (.vs .vz))))))))

/-- The law of separation, written out: `∀ a p z. z ∈ Sep a p ↔ z ∈ a ∧ p z`. -/
def lawSeparation : ClosedFormula Symbol :=
  .all (.all (.all (iffCore (member (.var .vz) (separate (.var (.vs (.vs .vz))) (.var (.vs .vz))))
    (conjunctionFormula (member (.var .vz) (.var (.vs (.vs .vz)))) (.app (.var (.vs .vz)) (.var .vz))))))

open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (emptyLaw powerLaw separationLaw) in
theorem lawEmpty_eq : lawEmpty = Mettapedia.Logic.HOL.ImpredicativeConnectives.expandInline emptyLaw := rfl

open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (emptyLaw powerLaw separationLaw) in
theorem lawPower_eq : lawPower = Mettapedia.Logic.HOL.ImpredicativeConnectives.expandInline powerLaw := rfl

open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (emptyLaw powerLaw separationLaw) in
theorem lawSeparation_eq :
    lawSeparation = Mettapedia.Logic.HOL.ImpredicativeConnectives.expandInline separationLaw := rfl

/-- The substitution of the empty context into a context. -/
def emptySubst (Γ : Ctx Unit) : Subst Symbol [] Γ := fun index => nomatch index

/-- A closed formula read in a context. -/
def atContext (Γ : Ctx Unit) (φ : ClosedFormula Symbol) : Term Symbol Γ .prop := subst (emptySubst Γ) φ

theorem weaken_atContext {Γ : Ctx Unit} {σ : Ty Unit} (φ : ClosedFormula Symbol) :
    weaken (σ := σ) (atContext Γ φ) = atContext (σ :: Γ) φ := by
  unfold atContext weaken
  rw [Mettapedia.Logic.HOL.rename_subst]
  congr 1
  funext _ index
  exact nomatch index

/-- One more term for the newest variable of a substitution. -/
def extendSubst {Γ₀ Γ : Ctx Unit} {σ : Ty Unit} (θ : Subst Symbol Γ₀ Γ) (t : Term Symbol Γ σ) : Subst Symbol (σ :: Γ₀) Γ
  | _, .vz => t
  | _, .vs index => θ index

theorem instantiate_lift {Γ₀ Γ : Ctx Unit} {σ : Ty Unit} (θ : Subst Symbol Γ₀ Γ) (t : Term Symbol Γ σ)
    (body : Term Symbol (σ :: Γ₀) .prop) :
    instantiate t (subst (Subst.lift θ) body) = subst (extendSubst θ t) body := by
  unfold instantiate
  rw [Mettapedia.Logic.HOL.subst_comp]
  apply Mettapedia.Logic.HOL.subst_ext
  intro _ index
  cases index with
  | vz => rfl
  | vs index => exact Mettapedia.Logic.HOL.instantiate_weaken t (θ index)

/-- **A law's quantifier instantiated by a term.** -/
def allInstance {Γ₀ Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {σ : Ty Unit} {θ : Subst Symbol Γ₀ Γ}
    {body : Term Symbol (σ :: Γ₀) .prop} (t : Term Symbol Γ σ) (proof : Proof Δ (subst θ (.all body))) :
    Proof Δ (subst (extendSubst θ t) body) :=
  Proof.cast (instantiate_lift θ t body) (.allE t proof)

/-- **The three laws, available in a context.** -/
structure HasLaws {Γ : Ctx Unit} (Δ : List (Term Symbol Γ .prop)) where
  empty : Proof Δ (atContext Γ lawEmpty)
  power : Proof Δ (atContext Γ lawPower)
  separation : Proof Δ (atContext Γ lawSeparation)

namespace HasLaws

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- The laws under a new hypothesis. -/
def prepend (laws : HasLaws Δ) (ψ : Term Symbol Γ .prop) : HasLaws (ψ :: Δ) where
  empty := laws.empty.prepend ψ
  power := laws.power.prepend ψ
  separation := laws.separation.prepend ψ

/-- The laws under a new variable. -/
def lift (laws : HasLaws Δ) (σ : Ty Unit) : HasLaws (weakenHyps (σ := σ) Δ) where
  empty := Proof.cast (weaken_atContext _) laws.empty.lift
  power := Proof.cast (weaken_atContext _) laws.power.lift
  separation := Proof.cast (weaken_atContext _) laws.separation.lift

/-- **Nothing is a member of the empty set.** -/
def emptyAt (laws : HasLaws Δ) (y : Term Symbol Γ setTy) : Proof Δ (negCore (member y (.const .empty))) :=
  allInstance y laws.empty

/-- **The power set's members are the subsets.** -/
def powerAt (laws : HasLaws Δ) (a b : Term Symbol Γ setTy) :
    Proof Δ (iffCore (member b (.app (.const .power) a))
      (.all (.imp (member (.var .vz) (weaken b)) (member (.var .vz) (weaken a))))) :=
  Proof.cast (by simp only [subst_iffCore]; rfl) (allInstance b (allInstance (body := .all _) a laws.power))

/-- **Separation.** -/
def separationAt (laws : HasLaws Δ) (a : Term Symbol Γ setTy) (p : Term Symbol Γ predTy) (z : Term Symbol Γ setTy) :
    Proof Δ (iffCore (member z (separate a p)) (conjunctionFormula (member z a) (.app p z))) :=
  Proof.cast (by simp only [subst_iffCore, subst_conjunctionFormula]; rfl)
    (allInstance z (allInstance (body := .all _) p (allInstance (body := .all (.all _)) a laws.separation)))

end HasLaws

/-! ## Core formulas and β-conversion -/

open Mettapedia.Logic.HOL.Term (isCore isCore_rename)

theorem isCore_falsity {Γ : Ctx Unit} : (falsity : Term Symbol Γ .prop).isCore = true := rfl

theorem isCore_member {Γ : Ctx Unit} {y x : Term Symbol Γ setTy} (coreY : y.isCore = true) (coreX : x.isCore = true) :
    (member y x).isCore = true := by
  simp only [member, isCore, coreY, coreX, Bool.and_self]

theorem isCore_conjunctionFormula {Γ : Ctx Unit} {p q : Term Symbol Γ .prop} (coreP : p.isCore = true)
    (coreQ : q.isCore = true) : (conjunctionFormula p q).isCore = true := by
  simp only [conjunctionFormula, isCore, weaken, isCore_rename, coreP, coreQ, Bool.and_self]

theorem isCore_disjunctionFormula {Γ : Ctx Unit} {p q : Term Symbol Γ .prop} (coreP : p.isCore = true)
    (coreQ : q.isCore = true) : (disjunctionFormula p q).isCore = true := by
  simp only [disjunctionFormula, isCore, weaken, isCore_rename, coreP, coreQ, Bool.and_self]

theorem isCore_iffCore {Γ : Ctx Unit} {p q : Term Symbol Γ .prop} (coreP : p.isCore = true)
    (coreQ : q.isCore = true) : (iffCore p q).isCore = true :=
  isCore_conjunctionFormula (by simp only [isCore, coreP, coreQ, Bool.and_self])
    (by simp only [isCore, coreP, coreQ, Bool.and_self])

mutual
theorem isCore_describes {Γ : Ctx Unit} : ∀ (term : Pattern) {x : Term Symbol Γ setTy}, x.isCore = true →
    (describes term x).isCore = true
  | .collection _ values _, x, coreX => by
    change (iffCore (member (.var .vz) (weaken x)) (describesOne values (.var .vz))).isCore = true
    exact isCore_iffCore (isCore_member rfl (by simp only [weaken, isCore_rename, coreX]))
      (isCore_describesOne values rfl)
  | .bvar _, _, _ | .fvar _, _, _ | .apply _ _, _, _ | .lambda _ _, _, _ | .multiLambda _ _ _, _, _
  | .subst _ _, _, _ => rfl

theorem isCore_describesOne {Γ : Ctx Unit} : ∀ (values : List Pattern) {y : Term Symbol Γ setTy}, y.isCore = true →
    (describesOne values y).isCore = true
  | [], _, _ => rfl
  | value :: values, _, coreY => isCore_disjunctionFormula (isCore_describes value coreY) (isCore_describesOne values coreY)
end

section Beta

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {σ : Ty Unit}

theorem coreStep_beta {body : Term Symbol (σ :: Γ) .prop} {t : Term Symbol Γ σ} (coreBody : body.isCore = true)
    (coreT : t.isCore = true) :
    Mettapedia.Logic.HOL.CoreStep ([] : List (DefiningEquation Symbol)) (.app (.lam body) t) (instantiate t body) :=
  ⟨by simp only [isCore, coreBody, coreT, Bool.and_self],
    Mettapedia.Logic.HOL.Term.isCore_subst (Mettapedia.Logic.HOL.CoreSubst.single coreT) coreBody, .beta body t⟩

/-- From the body at the argument to the abstraction applied to it. -/
def Proof.betaExpand {body : Term Symbol (σ :: Γ) .prop} {t : Term Symbol Γ σ} (coreBody : body.isCore = true)
    (coreT : t.isCore = true) (proof : Proof Δ (instantiate t body)) : Proof Δ (.app (.lam body) t) :=
  .convert (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (coreStep_beta coreBody coreT))) proof

/-- From the abstraction applied to the argument to the body at it. -/
def Proof.betaReduce {body : Term Symbol (σ :: Γ) .prop} {t : Term Symbol Γ σ} (coreBody : body.isCore = true)
    (coreT : t.isCore = true) (proof : Proof Δ (.app (.lam body) t)) : Proof Δ (instantiate t body) :=
  .convert (Relation.EqvGen.rel _ _ (coreStep_beta coreBody coreT)) proof

end Beta

/-! ## Using and introducing descriptions -/

section Descriptions

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- A hypothesis inserted below the newest one. -/
def Proof.insertSecond {φ χ : Term Symbol Γ .prop} (ψ : Term Symbol Γ .prop) (proof : Proof (φ :: Δ) χ) :
    Proof (φ :: ψ :: Δ) χ :=
  ProofSyntaxModulo.mono ((Mettapedia.Logic.HOL.ProofSyntax.OccurrenceMap.prepend ψ).lift φ) proof

theorem instantiate_describesBody (values : List Pattern) (x y : Term Symbol Γ setTy) :
    instantiate y (iffCore (member (.var .vz) (weaken x)) (describesOne values (.var .vz))) =
      iffCore (member y x) (describesOne values y) := by
  unfold instantiate
  rw [subst_iffCore, subst_describesOne]
  congr 1
  show member y (subst (Subst.single y) (weaken x)) = member y x
  rw [← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

/-- The equivalence a description gives at one set. -/
def describesAt {values : List Pattern} {x : Term Symbol Γ setTy} (described : Proof Δ (describes (set values) x))
    (y : Term Symbol Γ setTy) : Proof Δ (iffCore (member y x) (describesOne values y)) :=
  Proof.cast (instantiate_describesBody values x y) (.allE (φ := iffCore (member (.var .vz) (weaken x))
    (describesOne values (.var .vz))) y described)

/-- **A member of a described set is described by one of the term's members.** -/
def describesForward {values : List Pattern} {x y : Term Symbol Γ setTy} (described : Proof Δ (describes (set values) x))
    (isMember : Proof Δ (member y x)) : Proof Δ (describesOne values y) :=
  (describesAt described y).iffForward isMember

/-- **What one of the term's members describes is a member of the described set.** -/
def describesBackward {values : List Pattern} {x y : Term Symbol Γ setTy} (described : Proof Δ (describes (set values) x))
    (one : Proof Δ (describesOne values y)) : Proof Δ (member y x) :=
  (describesAt described y).iffBackward one

/-- **A set described by one member is described by one of the members.** -/
def oneIntro {y : Term Symbol Γ setTy} : ∀ (values : List Pattern) (index : Fin values.length),
    Proof Δ (describes (values.get index) y) → Proof Δ (describesOne values y)
  | _ :: _, ⟨0, _⟩, proof => disjunctionLeft proof
  | _ :: values, ⟨index + 1, bound⟩, proof =>
    disjunctionRight (oneIntro values ⟨index, Nat.lt_of_succ_lt_succ bound⟩ proof)

/-- **Case analysis over the members that may describe a set.** -/
def oneCases {y : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop} : ∀ {Δ : List (Term Symbol Γ .prop)}
    (values : List Pattern), Proof Δ (describesOne values y) →
      (∀ index : Fin values.length, Proof (describes (values.get index) y :: Δ) goal) → Proof Δ goal
  | _, [], one, _ => Proof.absurd one
  | Δ, _ :: values, one, branch =>
    disjunctionElim one (branch ⟨0, Nat.succ_pos _⟩)
      (oneCases (Δ := describesOne values y :: Δ) values (Proof.newest _) fun index =>
        Proof.insertSecond _ (branch index.succ))

end Descriptions

/-! ## Heights and iterated power sets -/

/-- The members of a set term. -/
def membersOf : Pattern → List Pattern
  | .collection _ values _ => values
  | _ => []

theorem hf_eq_set {term : Pattern} (holds : IsHF term) : term = set (membersOf term) := by
  obtain ⟨values, rfl, -⟩ := hf_set holds
  rfl

theorem hf_members {term : Pattern} (holds : IsHF term) : ∀ value ∈ membersOf term, IsHF value := by
  obtain ⟨values, rfl, inside⟩ := hf_set holds
  exact inside

theorem height_member {term : Pattern} (index : Fin (membersOf term).length) :
    height ((membersOf term).get index) < height term := by
  cases term with
  | collection kind values rest =>
    exact Nat.lt_succ_of_le (height_le_heightList (List.get_mem _ _))
  | _ => exact index.elim0

theorem hf_height_pos {term : Pattern} (holds : IsHF term) : 0 < height term := by
  rw [hf_eq_set holds]
  exact Nat.succ_pos _

/-- `Power (Power ⋯ Empty)`, `k` times. -/
def powerIter {Γ : Ctx Unit} : ℕ → Term Symbol Γ setTy
  | 0 => .const .empty
  | k + 1 => .app (.const .power) (powerIter k)

theorem weaken_powerIter {Γ : Ctx Unit} {σ : Ty Unit} : ∀ k : ℕ, weaken (σ := σ) (powerIter (Γ := Γ) k) = powerIter k
  | 0 => rfl
  | k + 1 => by
    change Term.app (.const .power) (weaken (powerIter k)) = _
    rw [weaken_powerIter k]
    rfl

theorem isCore_powerIter {Γ : Ctx Unit} : ∀ k : ℕ, (powerIter (Γ := Γ) k).isCore = true
  | 0 => rfl
  | k + 1 => by simp only [powerIter, isCore, isCore_powerIter k, Bool.and_self]

/-! ## Every hereditary term describes a set -/

section Existence

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **What a hereditary term of height at most `k` describes is a member of the `k`-th iterated power set.** -/
def inPowerIter : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ → ∀ (k : ℕ) (term : Pattern),
    IsHF term → height term ≤ k → ∀ y : Term Symbol Γ setTy, Proof Δ (describes term y) → Proof Δ (member y (powerIter k))
  | _, _, _, 0, _, holds, bound, _, _ => False.elim (Nat.not_lt_zero _ (bound.trans_lt' (hf_height_pos holds)))
  | Γ, Δ, laws, k + 1, term, holds, bound, y, described => by
    have described' : Proof Δ (describes (set (membersOf term)) y) := hf_eq_set holds ▸ described
    refine (laws.powerAt (powerIter k) y).iffBackward (.allI (.impI ?_))
    have lifted : Proof (member (.var .vz) (weaken y) :: weakenHyps (σ := setTy) Δ)
        (describes (set (membersOf term)) (weaken y)) :=
      (Proof.cast (weaken_describes _ _) described'.lift).prepend _
    refine oneCases (membersOf term) (describesForward lifted (Proof.newest _)) fun index => ?_
    refine Proof.cast (by rw [weaken_powerIter]) (inPowerIter ((laws.lift setTy).prepend _ |>.prepend _) k
      ((membersOf term).get index) (hf_members holds _ (List.get_mem _ _)) ?_ (.var .vz) (Proof.newest _))
    have below := height_member (term := term) index
    omega

/-- **The witness of a hereditary term**: the members of its iterated power set that its members describe. -/
def witness {Γ : Ctx Unit} (term : Pattern) : Term Symbol Γ setTy :=
  separate (powerIter (height term)) (.lam (describesOne (membersOf term) (.var .vz)))

theorem instantiate_lift_weaken_newest {Γ : Ctx Unit} (body : Term Symbol (setTy :: Γ) .prop) :
    instantiate (.var .vz) (rename (Rename.lift (Rename.weaken (σ := setTy))) body) = body := by
  unfold instantiate
  rw [Mettapedia.Logic.HOL.subst_rename]
  calc subst (fun {_} index => Subst.single (.var .vz) (Rename.lift Rename.weaken index)) body
      = subst Subst.id body := by
        apply Mettapedia.Logic.HOL.subst_ext
        intro _ index
        cases index <;> rfl
    _ = body := Mettapedia.Logic.HOL.subst_id body

/-- **A hereditary term describes its witness.** -/
def describedWitness (laws : HasLaws Δ) (term : Pattern) (holds : IsHF term) :
    Proof Δ (describes term (witness term)) := by
  refine Proof.cast (congrArg (fun t => describes t (witness term)) (hf_eq_set holds).symm) ?_
  change Proof Δ (.all (iffCore (member (.var .vz) (weaken (witness term)))
    (describesOne (membersOf term) (.var .vz))))
  have core : (rename (Rename.lift (Rename.weaken (σ := setTy)))
      (describesOne (Γ := setTy :: Γ) (membersOf term) (.var .vz))).isCore = true := by
    rw [isCore_rename]
    exact isCore_describesOne _ rfl
  have unbeta := instantiate_lift_weaken_newest (Γ := Γ) (describesOne (membersOf term) (.var .vz))
  let laws' := laws.lift setTy
  refine .allI (Proof.iffIntro ?_ ?_)
  · have separated := ((laws'.prepend _).separationAt (weaken (powerIter (height term)))
      (weaken (.lam (describesOne (membersOf term) (.var .vz)))) (.var .vz)).iffForward (Proof.newest _)
    exact Proof.cast unbeta (Proof.betaReduce core rfl (conjunctionRight separated))
  · refine ((laws'.prepend _).separationAt (weaken (powerIter (height term)))
      (weaken (.lam (describesOne (membersOf term) (.var .vz)))) (.var .vz)).iffBackward (conjunctionIntro ?_ ?_)
    · refine Proof.cast (by rw [weaken_powerIter]) (oneCases (membersOf term) (Proof.newest _) fun index => ?_)
      exact inPowerIter ((laws'.prepend _).prepend _) (height term) ((membersOf term).get index)
        (hf_members holds _ (List.get_mem _ _)) (height_member index).le (.var .vz) (Proof.newest _)
    · exact Proof.betaExpand core rfl (Proof.cast unbeta.symm (Proof.newest _))

/-- **Every hereditary term describes a set.** -/
def describedExists (laws : HasLaws Δ) (term : Pattern) (holds : IsHF term) :
    Proof Δ (existentialInline (describes term (.var .vz))) :=
  existentialIntro (witness term) (Proof.cast (by unfold instantiate; rw [subst_describes]; rfl)
    (describedWitness laws term holds))

end Existence

/-! ## Presentations of one set, and different sets -/

theorem zfOf_member_index {term : Pattern} (holds : IsHF term) (index : Fin (membersOf term).length) :
    zfOf ((membersOf term).get index) ∈ zfOf term := by
  obtain ⟨values, rfl, -⟩ := hf_set holds
  rw [zfOf_set]
  exact mem_zfOfList.mpr ⟨_, List.get_mem _ _, rfl⟩

theorem matching_member {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other)
    (same : zfOf term = zfOf other) (index : Fin (membersOf term).length) :
    ∃ index' : Fin (membersOf other).length, zfOf ((membersOf term).get index) = zfOf ((membersOf other).get index') := by
  have inside := zfOf_member_index holds index
  rw [same, hf_eq_set holdsOther, zfOf_set] at inside
  obtain ⟨value, valueMember, valueSame⟩ := mem_zfOfList.mp inside
  obtain ⟨index', rfl⟩ := List.mem_iff_get.mp valueMember
  exact ⟨index', valueSame.symm⟩

theorem height_lt_of_mem {term value : Pattern} (member : value ∈ membersOf term) : height value < height term := by
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  exact height_member index

/-- **Whether two terms present one set**, compared member by member. -/
def sameSet (term other : Pattern) : Bool :=
  (membersOf term).attach.all (fun value => (membersOf other).any (sameSet value.1)) &&
    (membersOf other).all (fun value' => (membersOf term).attach.any (fun value => sameSet value.1 value'))
termination_by height term
decreasing_by all_goals exact height_lt_of_mem value.2

theorem zfOf_eq_iff_members {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other) :
    zfOf term = zfOf other ↔ (∀ value ∈ membersOf term, ∃ value' ∈ membersOf other, zfOf value = zfOf value') ∧
      ∀ value' ∈ membersOf other, ∃ value ∈ membersOf term, zfOf value = zfOf value' := by
  conv_lhs => rw [hf_eq_set holds, hf_eq_set holdsOther, zfOf_set, zfOf_set]
  constructor
  · intro same
    refine ⟨fun value member => ?_, fun value' member' => ?_⟩
    · have inside : zfOf value ∈ zfOfList (membersOf other) := same ▸ mem_zfOfList.mpr ⟨value, member, rfl⟩
      obtain ⟨value', member', found⟩ := mem_zfOfList.mp inside
      exact ⟨value', member', found.symm⟩
    · have inside : zfOf value' ∈ zfOfList (membersOf term) := same.symm ▸ mem_zfOfList.mpr ⟨value', member', rfl⟩
      exact mem_zfOfList.mp inside
  · rintro ⟨forth, back⟩
    apply ZFSet.ext
    intro z
    rw [mem_zfOfList, mem_zfOfList]
    constructor
    · rintro ⟨value, member, rfl⟩
      obtain ⟨value', member', found⟩ := forth value member
      exact ⟨value', member', found.symm⟩
    · rintro ⟨value', member', rfl⟩
      exact back value' member'

/-- **Two hereditary terms present one set exactly when the comparison says so.** -/
theorem sameSet_iff : ∀ (term : Pattern), IsHF term → ∀ (other : Pattern), IsHF other →
    (sameSet term other = true ↔ zfOf term = zfOf other)
  | term, holds, other, holdsOther => by
    rw [sameSet, zfOf_eq_iff_members holds holdsOther, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    have recurse : ∀ value ∈ membersOf term, ∀ value', IsHF value' →
        (sameSet value value' = true ↔ zfOf value = zfOf value') :=
      fun value member value' holds' => sameSet_iff value (hf_members holds value member) value' holds'
    constructor
    · rintro ⟨forth, back⟩
      refine ⟨fun value member => ?_, fun value' member' => ?_⟩
      · obtain ⟨value', member', found⟩ := List.any_eq_true.mp (forth ⟨value, member⟩ (List.mem_attach _ _))
        exact ⟨value', member', (recurse value member value' (hf_members holdsOther _ member')).mp found⟩
      · obtain ⟨⟨value, member⟩, -, found⟩ := List.any_eq_true.mp (back value' member')
        exact ⟨value, member, (recurse value member value' (hf_members holdsOther _ member')).mp found⟩
    · rintro ⟨forth, back⟩
      refine ⟨fun ⟨value, member⟩ _ => ?_, fun value' member' => ?_⟩
      · obtain ⟨value', member', found⟩ := forth value member
        exact List.any_eq_true.mpr ⟨value', member', (recurse value member value' (hf_members holdsOther _ member')).mpr found⟩
      · obtain ⟨value, member, found⟩ := back value' member'
        exact List.any_eq_true.mpr ⟨⟨value, member⟩, List.mem_attach _ _,
          (recurse value member value' (hf_members holdsOther _ member')).mpr found⟩
termination_by term => height term
decreasing_by all_goals exact height_lt_of_mem member

/-- **The first position of a list that passes a test**, given that some element passes it. -/
def chooseIndex {α : Type} (values : List α) (test : α → Bool) (found : ∃ value ∈ values, test value = true) :
    {index : Fin values.length // test (values.get index) = true} :=
  ⟨⟨values.findIdx test, List.findIdx_lt_length_of_exists found⟩,
    List.findIdx_getElem (w := List.findIdx_lt_length_of_exists found)⟩

theorem matching_exists {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other)
    (same : zfOf term = zfOf other) (index : Fin (membersOf term).length) :
    ∃ value ∈ membersOf other, sameSet ((membersOf term).get index) value = true := by
  obtain ⟨index', found⟩ := matching_member holds holdsOther same index
  exact ⟨_, List.get_mem _ index', (sameSet_iff _ (hf_members holds _ (List.get_mem _ _)) _
    (hf_members holdsOther _ (List.get_mem _ _))).mpr found⟩

/-- The position of a member of `other` that presents the same set as a given member of `term`. -/
def matchingIndex {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other)
    (same : zfOf term = zfOf other) (index : Fin (membersOf term).length) :
    {index' : Fin (membersOf other).length //
      zfOf ((membersOf term).get index) = zfOf ((membersOf other).get index')} :=
  ⟨(chooseIndex (membersOf other) (sameSet ((membersOf term).get index)) (matching_exists holds holdsOther same index)).1,
    (sameSet_iff _ (hf_members holds _ (List.get_mem _ _)) _ (hf_members holdsOther _ (List.get_mem _ _))).mp
      (chooseIndex (membersOf other) (sameSet ((membersOf term).get index)) (matching_exists holds holdsOther same index)).2⟩

/-- **Presentations of one set describe the same sets.** -/
def describesSame : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} (term other : Pattern), IsHF term →
    IsHF other → zfOf term = zfOf other → ∀ x : Term Symbol Γ setTy, Proof Δ (describes term x) →
      Proof Δ (describes other x)
  | Γ, Δ, term, other, holds, holdsOther, same, x, described => by
    have described' : Proof Δ (describes (set (membersOf term)) x) :=
      Proof.cast (congrArg (describes · x) (hf_eq_set holds)) described
    refine Proof.cast (congrArg (describes · x) (hf_eq_set holdsOther).symm) ?_
    change Proof Δ (.all (iffCore (member (.var .vz) (weaken x)) (describesOne (membersOf other) (.var .vz))))
    have lifted : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes (set (membersOf term)) (weaken x)) :=
      fun ψ => (Proof.cast (weaken_describes _ _) described'.lift).prepend ψ
    refine .allI (Proof.iffIntro ?_ ?_)
    · refine oneCases (membersOf term) (describesForward (lifted _) (Proof.newest _)) fun index => ?_
      exact oneIntro (membersOf other) (matchingIndex holds holdsOther same index).1
        (describesSame ((membersOf term).get index) ((membersOf other).get (matchingIndex holds holdsOther same index).1)
          (hf_members holds _ (List.get_mem _ _)) (hf_members holdsOther _ (List.get_mem _ _))
          (matchingIndex holds holdsOther same index).2 (.var .vz) (Proof.newest _))
    · refine oneCases (membersOf other) (Proof.newest _) fun index' => ?_
      exact describesBackward ((lifted _).prepend _) (oneIntro (membersOf term)
        (matchingIndex holdsOther holds same.symm index').1
        (describesSame ((membersOf other).get index') ((membersOf term).get (matchingIndex holdsOther holds same.symm index').1)
          (hf_members holdsOther _ (List.get_mem _ _)) (hf_members holds _ (List.get_mem _ _))
          (matchingIndex holdsOther holds same.symm index').2 (.var .vz) (Proof.newest _)))
termination_by _ _ term other => height term + height other
decreasing_by
  · have first := height_member (term := term) index
    have second := height_member (term := other) (matchingIndex holds holdsOther same index).1
    omega
  · have first := height_member (term := other) index'
    have second := height_member (term := term) (matchingIndex holdsOther holds same.symm index').1
    omega

theorem unmatched_member {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other)
    (differ : zfOf term ≠ zfOf other)
    (matched : ¬ ∃ index : Fin (membersOf term).length, ∀ index' : Fin (membersOf other).length,
      zfOf ((membersOf term).get index) ≠ zfOf ((membersOf other).get index')) :
    ∃ index' : Fin (membersOf other).length, ∀ index : Fin (membersOf term).length,
      zfOf ((membersOf term).get index) ≠ zfOf ((membersOf other).get index') := by
  by_contra none
  push Not at matched none
  apply differ
  rw [hf_eq_set holds, hf_eq_set holdsOther, zfOf_set, zfOf_set]
  apply ZFSet.ext
  intro z
  rw [mem_zfOfList, mem_zfOfList]
  constructor
  · rintro ⟨value, member, rfl⟩
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    obtain ⟨index', same⟩ := matched index
    exact ⟨_, List.get_mem _ _, same.symm⟩
  · rintro ⟨value, member, rfl⟩
    obtain ⟨index', rfl⟩ := List.mem_iff_get.mp member
    obtain ⟨index, same⟩ := none index'
    exact ⟨_, List.get_mem _ _, same⟩

/-- Whether a term presents a set that no member of `other` presents. -/
def apartFrom (other value : Pattern) : Bool := (membersOf other).all fun value' => !sameSet value value'

theorem apartFrom_iff {other value : Pattern} (holds : IsHF value) (holdsOther : IsHF other) :
    apartFrom other value = true ↔ ∀ index' : Fin (membersOf other).length, zfOf value ≠ zfOf ((membersOf other).get index') := by
  rw [apartFrom, List.all_eq_true]
  constructor
  · intro all index' same
    have found := all _ (List.get_mem _ index')
    rw [(sameSet_iff _ holds _ (hf_members holdsOther _ (List.get_mem _ _))).mpr same] at found
    exact Bool.false_ne_true found
  · intro apart value' member'
    obtain ⟨index', rfl⟩ := List.mem_iff_get.mp member'
    cases found : sameSet value ((membersOf other).get index')
    · rfl
    · exact absurd ((sameSet_iff _ holds _ (hf_members holdsOther _ (List.get_mem _ _))).mp found) (apart index')

/-- **Terms of different sets describe no common set.** -/
def describesDistinct : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ →
    ∀ (term other : Pattern), IsHF term → IsHF other → zfOf term ≠ zfOf other → ∀ x : Term Symbol Γ setTy,
      Proof Δ (describes term x) → Proof Δ (describes other x) → Proof Δ falsity
  | Γ, Δ, laws, term, other, holds, holdsOther, differ, x, described, describedOther => by
    have described' : Proof Δ (describes (set (membersOf term)) x) :=
      Proof.cast (congrArg (describes · x) (hf_eq_set holds)) described
    have describedOther' : Proof Δ (describes (set (membersOf other)) x) :=
      Proof.cast (congrArg (describes · x) (hf_eq_set holdsOther)) describedOther
    have lifted : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes (set (membersOf term)) (weaken x)) :=
      fun ψ => (Proof.cast (weaken_describes _ _) described'.lift).prepend ψ
    have liftedOther : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes (set (membersOf other)) (weaken x)) :=
      fun ψ => (Proof.cast (weaken_describes _ _) describedOther'.lift).prepend ψ
    refine if left : (membersOf term).any (apartFrom other) = true then ?_ else ?_
    · let index := (chooseIndex (membersOf term) (apartFrom other) (List.any_eq_true.mp left)).1
      have apart := (apartFrom_iff (hf_members holds _ (List.get_mem _ index)) holdsOther).mp
        (chooseIndex (membersOf term) (apartFrom other) (List.any_eq_true.mp left)).2
      refine existentialElim (describedExists laws ((membersOf term).get index)
        (hf_members holds _ (List.get_mem _ _))) (Proof.cast rfl ?_)
      have isMember := describesBackward (y := .var .vz) (lifted _) (oneIntro (membersOf term) index (Proof.newest _))
      refine oneCases (membersOf other) (describesForward (liftedOther _) isMember) fun index' => ?_
      exact describesDistinct (((laws.lift setTy).prepend _).prepend _) ((membersOf term).get index)
        ((membersOf other).get index') (hf_members holds _ (List.get_mem _ _))
        (hf_members holdsOther _ (List.get_mem _ _)) (apart index') (.var .vz)
        ((Proof.newest _).prepend _) (Proof.newest _)
    · have matched : ¬ ∃ index : Fin (membersOf term).length, ∀ index' : Fin (membersOf other).length,
          zfOf ((membersOf term).get index) ≠ zfOf ((membersOf other).get index') := by
        rintro ⟨index, apart⟩
        exact left (List.any_eq_true.mpr ⟨_, List.get_mem _ index,
          (apartFrom_iff (hf_members holds _ (List.get_mem _ _)) holdsOther).mpr apart⟩)
      have exists' : ∃ value ∈ membersOf other, apartFrom term value = true := by
        obtain ⟨index', apart⟩ := unmatched_member holds holdsOther differ matched
        exact ⟨_, List.get_mem _ index', (apartFrom_iff (hf_members holdsOther _ (List.get_mem _ _)) holds).mpr
          fun index same => apart index same.symm⟩
      let index' := (chooseIndex (membersOf other) (apartFrom term) exists').1
      have apart := (apartFrom_iff (hf_members holdsOther _ (List.get_mem _ index')) holds).mp
        (chooseIndex (membersOf other) (apartFrom term) exists').2
      refine existentialElim (describedExists laws ((membersOf other).get index')
        (hf_members holdsOther _ (List.get_mem _ _))) (Proof.cast rfl ?_)
      have isMember := describesBackward (y := .var .vz) (liftedOther _)
        (oneIntro (membersOf other) index' (Proof.newest _))
      refine oneCases (membersOf term) (describesForward (lifted _) isMember) fun index => ?_
      exact describesDistinct (((laws.lift setTy).prepend _).prepend _) ((membersOf term).get index)
        ((membersOf other).get index') (hf_members holds _ (List.get_mem _ _))
        (hf_members holdsOther _ (List.get_mem _ _)) (fun same => apart index same.symm) (.var .vz)
        (Proof.newest _) ((Proof.newest _).prepend _)
termination_by _ _ _ term other => height term + height other
decreasing_by
  · have first := height_member (term := term) (chooseIndex (membersOf term) (apartFrom other) (List.any_eq_true.mp left)).1
    have second := height_member (term := other) index'
    omega
  · have first := height_member (term := term) index
    have second := height_member (term := other) (chooseIndex (membersOf other) (apartFrom term) exists').1
    omega

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
