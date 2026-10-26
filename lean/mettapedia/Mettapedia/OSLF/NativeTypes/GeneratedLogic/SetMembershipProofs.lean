import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSomeDescriptions

/-!
# Proofs of decided native types from the laws of the sets

For every native type of the regional fragment that holds at a hereditary term, this module builds a proof, in the
checker's calculus modulo conversion and from the laws of the empty set, the power set and separation, that the set
the term describes has the native type (`proveNative`); for every one that fails, a proof that it does not
(`refuteNative`). The proofs follow the meaning on a region closed under membership and under parts
(`SetMembershipRegions`):

- **Subjects** are described forward and existentially (`describesSome`): their members are among what the term's
  members describe, and each member of the term describes one of theirs. Members carry full descriptions, which the
  forward half hands over. Nothing moves membership on the left of a described set.
- **Steps** are members, met through the forward half; a member that a step reaches is one the existential half
  provides (`someMember`).
- **Named terms** are compared by presentation (`describesSomeSame`) and told apart when they differ
  (`describesSomeDistinct`).
- **Least fixed points** are proved stage by stage from below (`lfpKnowledge`); greatest ones by the predicate
  "described by a set of the stable stage", which the body preserves. A failing least fixed point is refuted by the
  predicate "not described by a set outside the stable stage"; a failing greatest one stage by stage from above
  (`gfpRefusal`).
- **One-element sets and counting** go through a member and the members presenting other sets (`onlyProof`,
  `describesWithout`, `proveCount`, `refuteCount`), with shared descriptions as hypotheses, so that proofs grow
  linearly.
- **Splits.** A proved split separates its parts from the set by a covering the decision chooses (`partTerm`,
  `partsSplit`, `partDescribed`); a refuted every-split uses the same parts as witnesses. A refuted split goes
  through every way the members can land in two arbitrary parts (`coverBranches`). Its goal is falsity, so from
  `P → ⊥` and `(P → ⊥) → ⊥` it gets falsity with no excluded middle (`falsityByCases`); in each branch the parts are
  described forward and existentially, and the decision chooses which part fails. A proved every-split takes the same
  branches with a disjunctive goal, by excluded middle. When both parts have upward shapes it needs none: the union
  says which part each member lies in (`sideOf`, `branchSplits`), the compiler proves the part formula at the part
  the branch knows (`partDescribedOfEach`), and an upward formula carries to the whole part (`upwardMono`).

**Profiles.** The prover works from the laws of a profile (`Laws`): the three laws, and excluded middle when the
profile is classical; the core profile's fragment keeps only every-splits with upward parts (`Formula.regionalWith`).
The refuter
needs only the three laws for every regional native type: the compiler is uniform in polarity, so a refutation never
proves a part, and no refutation case uses excluded middle.

What is known about the fixed-point variables, positively or negatively, at the sets of the region, travels with
the proofs under binders and hypotheses (`PosKnowledge`, `NegKnowledge`).

Both compilers are programs. Every branch and witness is chosen by deciding native types on the region
(`decideOn`), with the fixed-point variables decided alongside the sets they stand for (`Agrees`); members, parts and
presentations are found by comparing terms (`chooseIndex`, `presenterIndex`).
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

/-! ## Knowledge about predicates -/

section Knowledge

variable {Γ : Ctx Unit}

/-- `∀ y. y is described by the term, forward and existentially → P y`. -/
def knowsAt (predicate : Term Symbol Γ predTy) (term : Pattern) : Term Symbol Γ .prop :=
  .all (.imp (describesSome (membersOf term) (.var .vz)) (.app (weaken predicate) (.var .vz)))

/-- `∀ y. y is described by the term, forward and existentially → ¬ P y`. -/
def refusesAt (predicate : Term Symbol Γ predTy) (term : Pattern) : Term Symbol Γ .prop :=
  .all (.imp (describesSome (membersOf term) (.var .vz)) (negCore (.app (weaken predicate) (.var .vz))))

theorem rename_describes {Γ' : Ctx Unit} (ρ : Rename Unit Γ Γ') (term : Pattern) (x : Term Symbol Γ setTy) :
    rename ρ (describes term x) = describes term (rename ρ x) := by
  rw [rename_eq_subst, subst_describes, ← rename_eq_subst]

theorem rename_describesSome {Γ' : Ctx Unit} (ρ : Rename Unit Γ Γ') (values : List Pattern) (x : Term Symbol Γ setTy) :
    rename ρ (describesSome values x) = describesSome values (rename ρ x) := by
  rw [rename_eq_subst, subst_describesSome, ← rename_eq_subst]

theorem weaken_knowsAt {σ : Ty Unit} (predicate : Term Symbol Γ predTy) (term : Pattern) :
    weaken (σ := σ) (knowsAt predicate term) = knowsAt (weaken predicate) term := by
  change Term.all (.imp (rename (Rename.lift Rename.weaken) (describesSome (membersOf term) (.var .vz)))
    (.app (rename (Rename.lift Rename.weaken) (weaken predicate)) (.var .vz))) = _
  rw [rename_describesSome, weaken, Mettapedia.Logic.HOL.rename_lift_weaken]
  rfl

theorem weaken_refusesAt {σ : Ty Unit} (predicate : Term Symbol Γ predTy) (term : Pattern) :
    weaken (σ := σ) (refusesAt predicate term) = refusesAt (weaken predicate) term := by
  change Term.all (.imp (rename (Rename.lift Rename.weaken) (describesSome (membersOf term) (.var .vz)))
    (.imp (.app (rename (Rename.lift Rename.weaken) (weaken predicate)) (.var .vz)) falsity)) = _
  rw [rename_describesSome, weaken, Mettapedia.Logic.HOL.rename_lift_weaken]
  rfl

theorem instantiate_knows (predicate : Term Symbol Γ predTy) (term : Pattern) (y : Term Symbol Γ setTy) :
    instantiate y (.imp (describesSome (membersOf term) (.var .vz)) (.app (weaken predicate) (.var .vz))) =
      .imp (describesSome (membersOf term) y) (.app predicate y) := by
  change Term.imp (subst (Subst.single y) (describesSome (membersOf term) (.var .vz)))
    (.app (instantiate y (weaken predicate)) y) = _
  rw [subst_describesSome, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

theorem instantiate_refuses (predicate : Term Symbol Γ predTy) (term : Pattern) (y : Term Symbol Γ setTy) :
    instantiate y (.imp (describesSome (membersOf term) (.var .vz)) (negCore (.app (weaken predicate) (.var .vz)))) =
      .imp (describesSome (membersOf term) y) (negCore (.app predicate y)) := by
  change Term.imp (subst (Subst.single y) (describesSome (membersOf term) (.var .vz)))
    (.imp (.app (instantiate y (weaken predicate)) y) falsity) = _
  rw [subst_describesSome, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

variable {Δ : List (Term Symbol Γ .prop)}

/-- Knowledge used at a described set. -/
def useKnows {predicate : Term Symbol Γ predTy} {term : Pattern} {y : Term Symbol Γ setTy}
    (know : Proof Δ (knowsAt predicate term)) (described : Proof Δ (describesSome (membersOf term) y)) :
    Proof Δ (.app predicate y) :=
  .impE (Proof.cast (instantiate_knows predicate term y) (.allE y know)) described

/-- Negative knowledge used at a described set. -/
def useRefuses {predicate : Term Symbol Γ predTy} {term : Pattern} {y : Term Symbol Γ setTy}
    (refuse : Proof Δ (refusesAt predicate term)) (described : Proof Δ (describesSome (membersOf term) y)) :
    Proof Δ (negCore (.app predicate y)) :=
  .impE (Proof.cast (instantiate_refuses predicate term y) (.allE y refuse)) described

/-- **Positive knowledge**: at every set of the region in the environment's set, a proof that the predicate term
holds at what describes it. -/
def PosKnowledge {n : ℕ} (Δ : List (Term Symbol Γ .prop)) (env : Fin n → Term Symbol Γ predTy)
    (sets : Env ZFSet.{0} n) (region : Set ZFSet.{0}) : Type :=
  ∀ (index : Fin n) (term : Pattern), IsHF term → zfOf term ∈ region → zfOf term ∈ sets index →
    Proof Δ (knowsAt (env index) term)

/-- **Negative knowledge**: at every set of the region outside the environment's set, a proof that the predicate
term fails at what describes it. -/
def NegKnowledge {n : ℕ} (Δ : List (Term Symbol Γ .prop)) (env : Fin n → Term Symbol Γ predTy)
    (sets : Env ZFSet.{0} n) (region : Set ZFSet.{0}) : Type :=
  ∀ (index : Fin n) (term : Pattern), IsHF term → zfOf term ∈ region → zfOf term ∉ sets index →
    Proof Δ (refusesAt (env index) term)

variable {n : ℕ} {env : Fin n → Term Symbol Γ predTy} {sets : Env ZFSet.{0} n} {region : Set ZFSet.{0}}

def PosKnowledge.prepend (know : PosKnowledge Δ env sets region) (ψ : Term Symbol Γ .prop) :
    PosKnowledge (ψ :: Δ) env sets region :=
  fun index term holds inside member => (know index term holds inside member).prepend ψ

def PosKnowledge.lift (know : PosKnowledge Δ env sets region) (σ : Ty Unit) :
    PosKnowledge (weakenHyps (σ := σ) Δ) (fun index => weaken (env index)) sets region :=
  fun index term holds inside member => Proof.cast (weaken_knowsAt _ _) (know index term holds inside member).lift

def NegKnowledge.prepend (refuse : NegKnowledge Δ env sets region) (ψ : Term Symbol Γ .prop) :
    NegKnowledge (ψ :: Δ) env sets region :=
  fun index term holds inside missing => (refuse index term holds inside missing).prepend ψ

def NegKnowledge.lift (refuse : NegKnowledge Δ env sets region) (σ : Ty Unit) :
    NegKnowledge (weakenHyps (σ := σ) Δ) (fun index => weaken (env index)) sets region :=
  fun index term holds inside missing => Proof.cast (weaken_refusesAt _ _) (refuse index term holds inside missing).lift

end Knowledge

/-! ## Profiles: the laws a compiler works from -/

section Profiles

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- **Excluded middle**: `∀ p. p ∨ ¬ p`. -/
def middleLaw : ClosedFormula Symbol := .all (σ := .prop) (disjunctionFormula (.var .vz) (negCore (.var .vz)))

/-- **The laws a compiler works from**: the laws of the empty set, the power set and separation, and excluded middle
when the profile is classical. -/
structure Laws (classical : Bool) {Γ : Ctx Unit} (Δ : List (Term Symbol Γ .prop)) extends HasLaws Δ where
  middle : classical = true → Proof Δ (atContext Γ middleLaw)

instance {classical : Bool} : CoeOut (Laws classical Δ) (HasLaws Δ) := ⟨Laws.toHasLaws⟩

/-- The laws under a new hypothesis. -/
def Laws.prepend {classical : Bool} (laws : Laws classical Δ) (ψ : Term Symbol Γ .prop) : Laws classical (ψ :: Δ) where
  toHasLaws := laws.toHasLaws.prepend ψ
  middle := fun classic => (laws.middle classic).prepend ψ

/-- The laws under a new variable. -/
def Laws.lift {classical : Bool} (laws : Laws classical Δ) (σ : Ty Unit) : Laws classical (weakenHyps (σ := σ) Δ) where
  toHasLaws := laws.toHasLaws.lift σ
  middle := fun classic => Proof.cast (weaken_atContext _) (laws.middle classic).lift

/-- The core profile's laws: the three laws of the sets. -/
def HasLaws.core (laws : HasLaws Δ) : Laws false Δ where
  toHasLaws := laws
  middle := fun classic => absurd classic Bool.false_ne_true

theorem instantiate_middle (p : Term Symbol Γ .prop) :
    instantiate p (disjunctionFormula (.var .vz) (negCore (.var .vz))) = disjunctionFormula p (negCore p) := by
  unfold instantiate
  rw [subst_disjunctionFormula, subst_negCore]
  rfl

/-- **Excluded middle at a proposition**, in a classical profile. -/
def Laws.excludedMiddle {classical : Bool} (laws : Laws classical Δ) (classic : classical = true)
    (p : Term Symbol Γ .prop) : Proof Δ (disjunctionFormula p (negCore p)) :=
  Proof.cast (instantiate_middle p) (.allE (φ := disjunctionFormula (.var .vz) (negCore (.var .vz))) p
    (Proof.cast (by rfl) (laws.middle classic)))

/-- **Case analysis with a goal of falsity**, which needs no excluded middle: from `P → ⊥` and `(P → ⊥) → ⊥`. -/
def falsityByCases {P : Term Symbol Γ .prop} (yes : Proof (P :: Δ) falsity) (no : Proof (negCore P :: Δ) falsity) :
    Proof Δ falsity :=
  .impE (.impI no) (.impI yes)

/-- A proof under more hypotheses. -/
def Proof.prependAll {φ : Term Symbol Γ .prop} : ∀ (extra : List (Term Symbol Γ .prop)), Proof Δ φ → Proof (extra ++ Δ) φ
  | [], proof => proof
  | ψ :: extra, proof => (Proof.prependAll extra proof).prepend ψ

/-- The three laws under more hypotheses. -/
def HasLaws.prependAll : ∀ (extra : List (Term Symbol Γ .prop)), HasLaws Δ → HasLaws (extra ++ Δ)
  | [], laws => laws
  | ψ :: extra, laws => (HasLaws.prependAll extra laws).prepend ψ

/-- The laws under more hypotheses. -/
def Laws.prependAll {classical : Bool} : ∀ (extra : List (Term Symbol Γ .prop)), Laws classical Δ →
    Laws classical (extra ++ Δ)
  | [], laws => laws
  | ψ :: extra, laws => (Laws.prependAll extra laws).prepend ψ

/-- Positive knowledge under more hypotheses. -/
def PosKnowledge.prependAll {n : ℕ} {env : Fin n → Term Symbol Γ predTy} {sets : Env ZFSet.{0} n}
    {region : Set ZFSet.{0}} : ∀ (extra : List (Term Symbol Γ .prop)), PosKnowledge Δ env sets region →
      PosKnowledge (extra ++ Δ) env sets region
  | [], know => know
  | ψ :: extra, know => (PosKnowledge.prependAll extra know).prepend ψ

/-- Negative knowledge under more hypotheses. -/
def NegKnowledge.prependAll {n : ℕ} {env : Fin n → Term Symbol Γ predTy} {sets : Env ZFSet.{0} n}
    {region : Set ZFSet.{0}} : ∀ (extra : List (Term Symbol Γ .prop)), NegKnowledge Δ env sets region →
      NegKnowledge (extra ++ Δ) env sets region
  | [], refuse => refuse
  | ψ :: extra, refuse => (NegKnowledge.prependAll extra refuse).prepend ψ

end Profiles

/-! ## Moving descriptions -/

section Moving

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- A description under a new variable and a new hypothesis. -/
def describesUnder {term : Pattern} {x : Term Symbol Γ setTy} (described : Proof Δ (describes term x)) (σ : Ty Unit)
    (ψ : Term Symbol (σ :: Γ) .prop) : Proof (ψ :: weakenHyps (σ := σ) Δ) (describes term (weaken x)) :=
  (Proof.cast (weaken_describes _ _) described.lift).prepend ψ

/-- A description of a hereditary term, as a description of its set of members. -/
def describesAsSet {term : Pattern} (holds : IsHF term) {x : Term Symbol Γ setTy} (described : Proof Δ (describes term x)) :
    Proof Δ (describes (set (membersOf term)) x) :=
  Proof.cast (congrArg (describes · x) (hf_eq_set holds)) described

theorem weaken_falsity {σ : Ty Unit} : weaken (σ := σ) (falsity : Term Symbol Γ .prop) = falsity := rfl

end Moving

/-! ## Same members -/

section SameMembersProofs

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem weaken_sameMembers {σ : Ty Unit} (y z : Term Symbol Γ setTy) :
    weaken (σ := σ) (sameMembers y z) = sameMembers (weaken y) (weaken z) := by
  simp only [weaken, rename_eq_subst, subst_sameMembers]

theorem weaken_onlyMember {σ : Ty Unit} (x y : Term Symbol Γ setTy) :
    weaken (σ := σ) (onlyMember x y) = onlyMember (weaken x) (weaken y) := by
  simp only [weaken, rename_eq_subst, subst_onlyMember]

theorem instantiate_sameBody (w a b : Term Symbol Γ setTy) :
    instantiate w (iffCore (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b))) =
      iffCore (member w a) (member w b) := by
  unfold instantiate
  rw [subst_iffCore]
  change iffCore (member w (instantiate w (weaken a))) (member w (instantiate w (weaken b))) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_onlyBody (w x y : Term Symbol Γ setTy) :
    instantiate w (.imp (member (.var .vz) (weaken x)) (sameMembers (.var .vz) (weaken y))) =
      .imp (member w x) (sameMembers w y) := by
  change Term.imp (member w (instantiate w (weaken x))) (subst (Subst.single w) (sameMembers (.var .vz) (weaken y))) = _
  rw [subst_sameMembers]
  change Term.imp (member w (instantiate w (weaken x))) (sameMembers w (instantiate w (weaken y))) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken]

/-- Same members, at a set. -/
def sameAt {a b : Term Symbol Γ setTy} (same : Proof Δ (sameMembers a b)) (w : Term Symbol Γ setTy) :
    Proof Δ (iffCore (member w a) (member w b)) :=
  Proof.cast (instantiate_sameBody w a b)
    (.allE (φ := iffCore (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b))) w same)

/-- A member of `x`, when every member of `x` is `y`, has the members of `y`. -/
def onlyAt {x y : Term Symbol Γ setTy} (only : Proof Δ (onlyMember x y)) (w : Term Symbol Γ setTy)
    (isMember : Proof Δ (member w x)) : Proof Δ (sameMembers w y) :=
  .impE (Proof.cast (instantiate_onlyBody w x y)
    (.allE (φ := .imp (member (.var .vz) (weaken x)) (sameMembers (.var .vz) (weaken y))) w only)) isMember

/-- **A description moves along same members.** -/
def describesAlong {term : Pattern} (holds : IsHF term) {a b : Term Symbol Γ setTy}
    (described : Proof Δ (describes term a)) (same : Proof Δ (sameMembers a b)) : Proof Δ (describes term b) := by
  refine Proof.cast (congrArg (describes · b) (hf_eq_set holds).symm) ?_
  change Proof Δ (.all (iffCore (member (.var .vz) (weaken b)) (describesOne (membersOf term) (.var .vz))))
  have liftedA : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes (set (membersOf term)) (weaken a)) :=
    fun ψ => (Proof.cast (weaken_describes _ _) (describesAsSet holds described).lift).prepend ψ
  have liftedSame : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ)
      (iffCore (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b))) :=
    fun ψ => sameAt ((Proof.cast (weaken_sameMembers a b) same.lift).prepend ψ) (.var .vz)
  refine .allI (Proof.iffIntro ?_ ?_)
  · exact describesForward (liftedA _) ((liftedSame _).iffBackward (Proof.newest _))
  · exact (liftedSame _).iffForward (describesBackward (liftedA _) (Proof.newest _))

/-- **What two presentations of one set describe has the same members.** -/
def sameOfDescribes {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other) (same : zfOf term = zfOf other)
    {a b : Term Symbol Γ setTy} (describedA : Proof Δ (describes term a)) (describedB : Proof Δ (describes other b)) :
    Proof Δ (sameMembers a b) := by
  have liftedA : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes (set (membersOf term)) (weaken a)) :=
    fun ψ => (Proof.cast (weaken_describes _ _) (describesAsSet holds describedA).lift).prepend ψ
  have liftedB : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes (set (membersOf term)) (weaken b)) :=
    fun ψ => (Proof.cast (weaken_describes _ _) (describesAsSet holds
      (describesSame other term holdsOther holds same.symm b describedB)).lift).prepend ψ
  change Proof Δ (.all (iffCore (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b))))
  refine .allI (Proof.iffIntro ?_ ?_)
  · exact describesBackward (liftedB _) (describesForward (liftedA _) (Proof.newest _))
  · exact describesBackward (liftedA _) (describesForward (liftedB _) (Proof.newest _))

/-- **Every member of a one-element set is what describes its element.** -/
def onlyProof {term first : Pattern} (holds : IsHF term) (firstHolds : IsHF first)
    (allSame : ∀ index : Fin (membersOf term).length, zfOf ((membersOf term).get index) = zfOf first)
    {x y : Term Symbol Γ setTy} (describedX : Proof Δ (describesSome (membersOf term) x))
    (describedY : Proof Δ (describes first y)) : Proof Δ (onlyMember x y) := by
  change Proof Δ (.all (.imp (member (.var .vz) (weaken x)) (sameMembers (.var .vz) (weaken y))))
  refine .allI (.impI ?_)
  refine oneCases (membersOf term) (describesSome_forward (describesSomeUnder describedX setTy _) (Proof.newest _))
    fun index => ?_
  exact sameOfDescribes (hf_members holds _ (List.get_mem _ _)) firstHolds (allSame index) (Proof.newest _)
    ((describesUnder describedY setTy _).prepend _)

end SameMembersProofs


/-! ## Small facts about members -/

theorem instantiate_newest_lifted {Γ : Ctx Unit} {σ : Ty Unit} (body : Term Symbol (σ :: Γ) .prop) :
    instantiate (.var .vz) (rename (Rename.lift (Rename.weaken (σ := σ))) body) = body := by
  unfold instantiate
  rw [Mettapedia.Logic.HOL.subst_rename]
  calc subst (fun {_} index => Subst.single (.var .vz) (Rename.lift Rename.weaken index)) body
      = subst Subst.id body := by
        apply Mettapedia.Logic.HOL.subst_ext
        intro _ index
        cases index <;> rfl
    _ = body := Mettapedia.Logic.HOL.subst_id body

/-- A weakened universal statement at the newest variable. -/
def Proof.atNewest {Γ : Ctx Unit} {σ : Ty Unit} {Δ : List (Term Symbol (σ :: Γ) .prop)} {body : Term Symbol (σ :: Γ) .prop}
    (proof : Proof Δ (weaken (σ := σ) (.all body))) : Proof Δ body :=
  Proof.cast (instantiate_newest_lifted body) (.allE (φ := rename (Rename.lift Rename.weaken) body) (.var .vz) proof)

theorem exists_member_index {term : Pattern} (holds : IsHF term) {z : ZFSet.{0}} (member : z ∈ zfOf term) :
    ∃ index : Fin (membersOf term).length, zfOf ((membersOf term).get index) = z := by
  rw [hf_eq_set holds, zfOf_set] at member
  obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp valueMember
  exact ⟨index, rfl⟩

theorem members_nil_of_empty {term : Pattern} (holds : IsHF term) (isEmpty : zfOf term = ∅) : membersOf term = [] := by
  cases found : membersOf term with
  | nil => rfl
  | cons value values =>
    have inside := zfOf_member_index holds (⟨0, by rw [found]; exact Nat.succ_pos _⟩ : Fin (membersOf term).length)
    rw [isEmpty] at inside
    exact absurd inside (ZFSet.notMem_empty _)

/-- The newest hypothesis is a member of a described set by one of the term's members. -/
def memberByIndex {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {term : Pattern} (holds : IsHF term)
    {x : Term Symbol Γ setTy} (described : Proof Δ (describes term x)) (index : Fin (membersOf term).length)
    {Δ' : List (Term Symbol (setTy :: Γ) .prop)} (transport : Proof (weakenHyps (σ := setTy) Δ) (describes term (weaken x)) →
      Proof Δ' (describes term (weaken x))) (newest : Proof Δ' (describes ((membersOf term).get index) (.var .vz))) :
    Proof Δ' (member (.var .vz) (weaken x)) :=
  describesBackward (describesAsSet holds (transport (Proof.cast (weaken_describes _ _) described.lift)))
    (oneIntro (membersOf term) index newest)

/-! ## Types -/

/-- **A typed hereditary term's set has the type**, proved member by member. -/
def proveTyped : ∀ (type : TypeExpr) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} (term : Pattern),
    IsHF term → SetTyped (zfOf term) type → ∀ x : Term Symbol Γ setTy, Proof Δ (describes term x) →
      Proof Δ (typedFormula type x)
  | .base sort, _, _, _, _, typed, _, _ => Proof.cast (by simp only [typedFormula, if_pos (show sort = "Set" from typed)])
      truthIntro
  | .collection kind element, Γ, Δ, term, holds, typed, x, described => by
    obtain ⟨set, members⟩ := typed
    rw [show typedFormula (.collection kind element) x =
      .all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))) by simp only [typedFormula, if_pos set]]
    refine .allI (.impI ?_)
    refine oneCases (membersOf term) (describesForward (describesAsSet holds (describesUnder described setTy _))
      (Proof.newest _)) fun index => ?_
    exact proveTyped element ((membersOf term).get index) (hf_members holds _ (List.get_mem _ _))
      (members _ (zfOf_member_index holds index)) (.var .vz) (Proof.newest _)
  | .arrow _ _, _, _, _, _, typed, _, _ => typed.elim
  | .multiBinder _, _, _, _, _, typed, _, _ => typed.elim

/-- **An untyped hereditary term's set lacks the type**, refuted at a member that lacks it. -/
def refuteTyped : ∀ (type : TypeExpr) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ →
    ∀ (term : Pattern), IsHF term → ¬ SetTyped (zfOf term) type → ∀ x : Term Symbol Γ setTy,
      Proof Δ (describes term x) → Proof Δ (negCore (typedFormula type x))
  | .base sort, _, _, _, _, _, fails, _, _ =>
    Proof.cast (by simp only [typedFormula, if_neg (show ¬ sort = "Set" from fails)]; rfl) (.impI (Proof.newest _))
  | .collection kind element, Γ, Δ, laws, term, holds, fails, x, described => by
    refine if set : kind = .hashSet then ?_ else ?_
    · have notAll : (membersOf term).all (decideTyped element) = false := by
        have rejected := (decideTyped_iff (.collection kind element) holds).not.mpr fails
        simp only [decideTyped, Bool.and_eq_true, decide_eq_true_eq, not_and] at rejected
        exact Bool.eq_false_iff.mpr (rejected set)
      have bad : ∃ value ∈ membersOf term, (!decideTyped element value) = true := by
        obtain ⟨value, member, untyped⟩ := List.all_eq_false.mp notAll
        exact ⟨value, member, by simpa using untyped⟩
      let index := (chooseIndex (membersOf term) (fun value => !decideTyped element value) bad).1
      have failsThere : ¬ SetTyped (zfOf ((membersOf term).get index)) element := fun typed => by
        have chosen : (!decideTyped element ((membersOf term).get index)) = true :=
          (chooseIndex (membersOf term) (fun value => !decideTyped element value) bad).2
        rw [(decideTyped_iff element (hf_members holds _ (List.get_mem _ _))).mpr typed] at chosen
        simp at chosen
      rw [show typedFormula (.collection kind element) x =
        .all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))) by simp only [typedFormula, if_pos set]]
      refine .impI ?_
      refine existentialElim (describedExists (laws.prepend _) ((membersOf term).get index)
        (hf_members holds _ (List.get_mem _ _))) ?_
      have typedThere : Proof (describes ((membersOf term).get index) (.var .vz) :: weakenHyps (σ := setTy)
          (.all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))) :: Δ))
          (typedFormula element (.var .vz)) :=
        ProofSyntaxModulo.impE (Proof.atNewest (((Proof.newest _).lift (σ := setTy)).prepend _))
          (memberByIndex holds (described.prepend _) index (fun proof => proof.prepend _) (Proof.newest _))
      exact ProofSyntaxModulo.impE (refuteTyped element ((laws.prepend _).lift setTy |>.prepend _) ((membersOf term).get index)
        (hf_members holds _ (List.get_mem _ _)) failsThere (.var .vz) (Proof.newest _)) typedThere
    · exact Proof.cast (by simp only [typedFormula, if_neg set]; rfl) (.impI (Proof.newest _))
  | .arrow _ _, _, _, _, _, _, _, _, _ => .impI (Proof.newest _)
  | .multiBinder _, _, _, _, _, _, _, _, _ => .impI (Proof.newest _)

/-- **A typed hereditary term's set has the type**, for a set described forward and existentially: each member, by
its full description. -/
def proveTypedSome : ∀ (type : TypeExpr) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} (term : Pattern),
    IsHF term → SetTyped (zfOf term) type → ∀ x : Term Symbol Γ setTy, Proof Δ (describesSome (membersOf term) x) →
      Proof Δ (typedFormula type x)
  | .base sort, _, _, _, _, typed, _, _ => Proof.cast (by simp only [typedFormula, if_pos (show sort = "Set" from typed)])
      truthIntro
  | .collection kind element, Γ, Δ, term, holds, typed, x, described => by
    obtain ⟨set, members⟩ := typed
    rw [show typedFormula (.collection kind element) x =
      .all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))) by simp only [typedFormula, if_pos set]]
    refine .allI (.impI ?_)
    refine oneCases (membersOf term) (describesSome_forward (describesSomeUnder described setTy _) (Proof.newest _))
      fun index => ?_
    exact proveTyped element ((membersOf term).get index) (hf_members holds _ (List.get_mem _ _))
      (members _ (zfOf_member_index holds index)) (.var .vz) (Proof.newest _)
  | .arrow _ _, _, _, _, _, typed, _, _ => typed.elim
  | .multiBinder _, _, _, _, _, typed, _, _ => typed.elim

/-- **An untyped hereditary term's set lacks the type**, for a set described forward and existentially: at a member
that lacks it. -/
def refuteTypedSome : ∀ (type : TypeExpr) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ →
    ∀ (term : Pattern), IsHF term → ¬ SetTyped (zfOf term) type → ∀ x : Term Symbol Γ setTy,
      Proof Δ (describesSome (membersOf term) x) → Proof Δ (negCore (typedFormula type x))
  | .base sort, _, _, _, _, _, fails, _, _ =>
    Proof.cast (by simp only [typedFormula, if_neg (show ¬ sort = "Set" from fails)]; rfl) (.impI (Proof.newest _))
  | .collection kind element, Γ, Δ, laws, term, holds, fails, x, described => by
    refine if set : kind = .hashSet then ?_ else ?_
    · have notAll : (membersOf term).all (decideTyped element) = false := by
        have rejected := (decideTyped_iff (.collection kind element) holds).not.mpr fails
        simp only [decideTyped, Bool.and_eq_true, decide_eq_true_eq, not_and] at rejected
        exact Bool.eq_false_iff.mpr (rejected set)
      have bad : ∃ value ∈ membersOf term, (!decideTyped element value) = true := by
        obtain ⟨value, member, untyped⟩ := List.all_eq_false.mp notAll
        exact ⟨value, member, by simpa using untyped⟩
      let index := (chooseIndex (membersOf term) (fun value => !decideTyped element value) bad).1
      have failsThere : ¬ SetTyped (zfOf ((membersOf term).get index)) element := fun typed => by
        have chosen : (!decideTyped element ((membersOf term).get index)) = true :=
          (chooseIndex (membersOf term) (fun value => !decideTyped element value) bad).2
        rw [(decideTyped_iff element (hf_members holds _ (List.get_mem _ _))).mpr typed] at chosen
        simp at chosen
      rw [show typedFormula (.collection kind element) x =
        .all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))) by simp only [typedFormula, if_pos set]]
      refine .impI (someMemberHyps (Proof.prepend _ described) index ?_)
      exact ProofSyntaxModulo.impE (refuteTyped element ((((laws.prepend _).lift setTy).prepend _).prepend _ |>.prepend _)
        ((membersOf term).get index) (hf_members holds _ (List.get_mem _ _)) failsThere (.var .vz) (Proof.newest _))
        (ProofSyntaxModulo.impE (Proof.atNewest (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
          ((Proof.newest (Δ := Δ) (.all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))))).lift
            (σ := setTy)))))) (Proof.prepend _ (Proof.newest _)))
    · exact Proof.cast (by simp only [typedFormula, if_neg set]; rfl) (.impI (Proof.newest _))
  | .arrow _ _, _, _, _, _, _, _, _, _ => .impI (Proof.newest _)
  | .multiBinder _, _, _, _, _, _, _, _, _ => .impI (Proof.newest _)

/-! ## Instantiating the bodies of the formers -/

section Instances

variable {Γ : Ctx Unit}

theorem instantiate_underElement {n : ℕ} (t : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    (fun index => subst (Subst.single t) (underElement env index)) = env := by
  funext index
  exact Mettapedia.Logic.HOL.instantiate_weaken t (env index)

theorem instantiate_possiblyBody {n : ℕ} {inner : Formula n} (modal : inner.regional = true) (t x : Term Symbol Γ setTy)
    (env : Fin n → Term Symbol Γ predTy) :
    instantiate t (conjunctionFormula (member (.var .vz) (weaken x)) (nativeFormula inner (.var .vz) (underElement env))) =
      conjunctionFormula (member t x) (nativeFormula inner t env) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_nativeFormula_regional _ inner modal, instantiate_underElement]
  congr 1
  show member t (instantiate t (weaken x)) = member t x
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_singleBody {n : ℕ} {inner : Formula n} (modal : inner.regional = true) (t x : Term Symbol Γ setTy)
    (env : Fin n → Term Symbol Γ predTy) :
    instantiate t (conjunctionFormula (member (.var .vz) (weaken x))
      (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env)) (onlyMember (weaken x) (.var .vz)))) =
      conjunctionFormula (member t x) (conjunctionFormula (nativeFormula inner t env) (onlyMember x t)) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_conjunctionFormula, subst_nativeFormula_regional _ inner modal, instantiate_underElement,
    subst_onlyMember]
  change conjunctionFormula (member t (instantiate t (weaken x)))
    (conjunctionFormula (nativeFormula inner t env) (onlyMember (instantiate t (weaken x)) t)) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

/-- A predicate: described, forward and existentially, by one of a list of terms. -/
def describedPredicate (terms : List Pattern) {Γ : Ctx Unit} : Term Symbol Γ predTy := .lam (someOne terms (.var .vz))

theorem weaken_describedPredicate {σ : Ty Unit} (terms : List Pattern) :
    weaken (σ := σ) (describedPredicate terms (Γ := Γ)) = describedPredicate terms := by
  change Term.lam (rename (Rename.lift Rename.weaken) (someOne terms (.var .vz))) = _
  rw [rename_eq_subst, subst_someOne]
  rfl

theorem isCore_predicateBody (terms : List Pattern) : (someOne terms (.var .vz : Term Symbol (setTy :: Γ) setTy)).isCore = true :=
  isCore_someOne terms rfl

theorem instantiate_nuBody {n : ℕ} {inner : Formula (n + 1)} (modal : inner.regional = true) (predicate : Term Symbol Γ predTy)
    (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate predicate (conjunctionFormula (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
        (nativeFormula inner (.var .vz) (underFixedPoint env)))) (.app (.var .vz) (weaken x))) =
      conjunctionFormula (.all (σ := setTy) (.imp (.app (weaken predicate) (.var .vz))
        (nativeFormula inner (.var .vz) (Fin.cons (weaken predicate) (underElement env))))) (.app predicate x) := by
  unfold instantiate
  rw [subst_conjunctionFormula]
  congr 1
  · change Term.all (.imp (.app (weaken predicate) (.var .vz))
      (subst (Subst.lift (Subst.single predicate)) (nativeFormula inner (.var .vz) (underFixedPoint env)))) = _
    rw [subst_nativeFormula_regional _ inner modal]
    congr 3
    funext index
    refine Fin.cases rfl (fun index => ?_) index
    change subst (Subst.lift (Subst.single predicate)) (weaken (weaken (env index))) = weaken (env index)
    rw [Mettapedia.Logic.HOL.subst_weaken, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]
  · show Term.app predicate (instantiate predicate (weaken x)) = _
    rw [Mettapedia.Logic.HOL.instantiate_weaken]

/-- The first member of a hereditary term with members. -/
def firstIndex {term : Pattern} (holds : IsHF term) (nonempty : zfOf term ≠ ∅) : Fin (membersOf term).length :=
  ⟨0, List.length_pos_iff.mpr fun none => nonempty ((zfOf_eq_empty_iff holds).mpr none)⟩

theorem presenter_exists (values : List Pattern) (hereditary : ∀ value ∈ values, IsHF value) {term : Pattern}
    (holds : IsHF term) (found : ∃ value ∈ values, zfOf value = zfOf term) :
    ∃ value ∈ values, sameSet term value = true := by
  obtain ⟨value, member, same⟩ := found
  exact ⟨value, member, (sameSet_iff term holds value (hereditary value member)).mpr same.symm⟩

/-- **A listed term presenting the same set as a given term**, found by comparison. -/
def presenterIndex (values : List Pattern) (hereditary : ∀ value ∈ values, IsHF value) {term : Pattern}
    (holds : IsHF term) (found : ∃ value ∈ values, zfOf value = zfOf term) :
    {index : Fin values.length // zfOf term = zfOf (values.get index)} :=
  ⟨(chooseIndex values (sameSet term) (presenter_exists values hereditary holds found)).1,
    (sameSet_iff term holds _ (hereditary _ (List.get_mem _ _))).mp
      (chooseIndex values (sameSet term) (presenter_exists values hereditary holds found)).2⟩

end Instances

/-! ## The members other than one -/

section Without

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem weaken_withoutSame {σ : Ty Unit} (x y : Term Symbol Γ setTy) :
    weaken (σ := σ) (withoutSame x y) = withoutSame (weaken x) (weaken y) := by
  rw [weaken_eq_subst, subst_withoutSame, ← weaken_eq_subst, ← weaken_eq_subst]

theorem isCore_sameMembers {y z : Term Symbol Γ setTy} (coreY : y.isCore = true) (coreZ : z.isCore = true) :
    (sameMembers y z).isCore = true := by
  change (iffCore (member (.var .vz) (weaken y)) (member (.var .vz) (weaken z))).isCore = true
  exact isCore_iffCore (isCore_member rfl (by simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, coreY]))
    (isCore_member rfl (by simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, coreZ]))

theorem isCore_withoutBody {y : Term Symbol Γ setTy} (coreY : y.isCore = true) :
    (negCore (sameMembers (.var .vz) (weaken (σ := setTy) y))).isCore = true := by
  simp only [negCore, Mettapedia.Logic.HOL.Term.isCore, isCore_falsity, Bool.and_true]
  exact isCore_sameMembers rfl (by simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, coreY])

theorem instantiate_withoutBody (w y : Term Symbol Γ setTy) :
    instantiate w (negCore (sameMembers (.var .vz) (weaken y))) = negCore (sameMembers w y) := by
  change subst (Subst.single w) (negCore (sameMembers (.var .vz) (weaken y))) = _
  rw [subst_negCore, subst_sameMembers]
  change negCore (sameMembers w (instantiate w (weaken y))) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

/-- The members other than one, described forward and existentially, from a forward and existential description of
the set and a description of the one. -/
def describesWithoutAt (laws : HasLaws Δ) {values : List Pattern} (hereditary : ∀ value ∈ values, IsHF value)
    {term : Pattern} (holds : IsHF term) {x y : Term Symbol Γ setTy} (coreY : y.isCore = true)
    (describedX : Proof Δ (describesSome values x)) (describedY : Proof Δ (describes term y)) :
    Proof Δ (describesSome (values.filter fun other => !sameSet other term) (withoutSame x y)) := by
  have restHereditary : ∀ value ∈ values.filter (fun other => !sameSet other term), IsHF value :=
    fun value member => hereditary value (List.mem_filter.mp member).1
  have coreBody : (negCore (sameMembers (.var .vz) (weaken (σ := setTy) (weaken (σ := setTy) y)))).isCore = true :=
    isCore_withoutBody (by simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, coreY])
  have liftedY : ∀ ψ, Proof (ψ :: weakenHyps (σ := setTy) Δ) (describes term (weaken y)) :=
    fun ψ => (Proof.cast (weaken_describes _ _) describedY.lift).prepend ψ
  refine conjunctionIntro ?_ (eachDescribedOfComponents fun index => ?_)
  · change Proof Δ (.all (.imp (member (.var .vz) (weaken (withoutSame x y)))
      (describesOne (values.filter fun other => !sameSet other term) (.var .vz))))
    rw [weaken_withoutSame]
    refine .allI (.impI ?_)
    have both := (((laws.lift setTy).prepend _).separationAt (weaken x)
      (.lam (negCore (sameMembers (.var .vz) (weaken (weaken y))))) (.var .vz)).iffForward (Proof.newest _)
    have apart := Proof.cast (instantiate_withoutBody _ _) (Proof.betaReduce coreBody rfl (conjunctionRight both))
    refine oneCases values (describesSome_forward (describesSomeUnder describedX setTy _) (conjunctionLeft both))
      fun index => ?_
    have indexHolds := hereditary _ (List.get_mem values index)
    refine if same : sameSet (values.get index) term = true then ?_ else ?_
    · exact Proof.absurd (.impE (Proof.prepend _ apart) (sameOfDescribes indexHolds holds
        ((sameSet_iff _ indexHolds _ holds).mp same) (Proof.newest _) (Proof.prepend _ (liftedY _))))
    · have found : ∃ value ∈ values.filter (fun other => !sameSet other term), zfOf value = zfOf (values.get index) :=
        ⟨values.get index, List.mem_filter.mpr ⟨List.get_mem _ _, by simpa using same⟩, rfl⟩
      exact oneIntro _ (presenterIndex _ restHereditary indexHolds found).1
        (describesSame _ _ indexHolds (restHereditary _ (List.get_mem _ _))
          (presenterIndex _ restHereditary indexHolds found).2 _ (Proof.newest _))
  · have filtered := List.mem_filter.mp (List.get_mem (values.filter fun other => !sameSet other term) index)
    have indexHolds := hereditary _ filtered.1
    have found : ∃ value ∈ values, zfOf value = zfOf ((values.filter fun other => !sameSet other term).get index) :=
      ⟨_, filtered.1, rfl⟩
    let source := presenterIndex values hereditary indexHolds found
    have sourceHolds := hereditary _ (List.get_mem values source.1)
    have apartTerm : zfOf (values.get source.1) ≠ zfOf term := fun same => by
      have test := filtered.2
      rw [(sameSet_iff _ indexHolds _ holds).mpr (source.2.trans same)] at test
      simp at test
    refine someMember describedX source.1 ?_
    rw [weaken_someMemberFormula, weaken_withoutSame]
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_someMember _ _ _).symm (conjunctionIntro ?_ ?_))
    · have laws2 := (laws.lift setTy).prepend (conjunctionFormula (member (.var .vz) (weaken x))
        (describes (values.get source.1) (.var .vz)))
      refine (laws2.separationAt (weaken x) (.lam (negCore (sameMembers (.var .vz) (weaken (weaken y)))))
        (.var .vz)).iffBackward (conjunctionIntro (conjunctionLeft (Proof.newest _))
          (Proof.betaExpand coreBody rfl (Proof.cast (instantiate_withoutBody _ _).symm (.impI ?_))))
      exact describesDistinct (laws2.prepend _) _ term sourceHolds holds apartTerm _
        (describesAlong sourceHolds (Proof.prepend _ (conjunctionRight (Proof.newest _))) (Proof.newest _))
        (Proof.prepend _ (liftedY _))
    · exact describesSame _ _ sourceHolds indexHolds source.2.symm _ (conjunctionRight (Proof.newest _))

/-- **The members other than one, described forward and existentially**: by the listed terms presenting other
sets. The two descriptions are proved once and used as hypotheses. -/
def describesWithout (laws : HasLaws Δ) {values : List Pattern} (hereditary : ∀ value ∈ values, IsHF value)
    {term : Pattern} (holds : IsHF term) {x y : Term Symbol Γ setTy} (coreY : y.isCore = true)
    (describedX : Proof Δ (describesSome values x)) (describedY : Proof Δ (describes term y)) :
    Proof Δ (describesSome (values.filter fun other => !sameSet other term) (withoutSame x y)) :=
  .impE (.impE (.impI (.impI (describesWithoutAt ((laws.prepend _).prepend _) hereditary holds coreY
    (Proof.prepend (describes term y) (Proof.newest (describesSome values x))) (Proof.newest _)))) describedX)
    describedY

end Without

/-! ## Counting -/

section Counting

variable {n : ℕ}
  {point : ∀ {Γ : Ctx Unit}, Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) → Term Symbol Γ .prop}

theorem weaken_countWith {Γ : Ctx Unit} {σ : Ty Unit}
    (natural : ∀ {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (y : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (point y env) = point (subst θ y) fun index => subst θ (env index))
    (k : ℕ) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    weaken (σ := σ) (countWith point k x env) = countWith point k (weaken x) fun index => weaken (env index) := by
  rw [weaken_eq_subst, subst_countWith natural]
  simp only [← weaken_eq_subst]

theorem instantiate_countBody {Γ : Ctx Unit}
    (natural : ∀ {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (y : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (point y env) = point (subst θ y) fun index => subst θ (env index))
    (k : ℕ) (t x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate t (conjunctionFormula (member (.var .vz) (weaken x)) (conjunctionFormula (point (.var .vz) (underElement env))
      (countWith point k (withoutSame (weaken x) (.var .vz)) (underElement env)))) =
      conjunctionFormula (member t x) (conjunctionFormula (point t env) (countWith point k (withoutSame x t) env)) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_conjunctionFormula, natural, subst_countWith natural, subst_withoutSame,
    instantiate_underElement]
  change conjunctionFormula (member t (instantiate t (weaken x)))
    (conjunctionFormula (point t env) (countWith point k (withoutSame (instantiate t (weaken x)) t) env)) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

/-- **A proof that at least `k` of the listed members have a property**, at a set the list describes: a member that
has it, and the members presenting other sets, counted again. -/
def proveCount (region : Region) {classical : Bool}
    (natural : ∀ {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (y : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (point y env) = point (subst θ y) fun index => subst θ (env index))
    (Knowledge : ∀ {Γ : Ctx Unit}, List (Term Symbol Γ .prop) → (Fin n → Term Symbol Γ predTy) → Type)
    (prependKnowledge : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {env : Fin n → Term Symbol Γ predTy},
      Knowledge Δ env → ∀ ψ, Knowledge (ψ :: Δ) env)
    (liftKnowledge : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {env : Fin n → Term Symbol Γ predTy},
      Knowledge Δ env → Knowledge (weakenHyps (σ := setTy) Δ) (underElement env))
    (good : Pattern → Bool)
    (pointProof : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, Laws classical Δ → ∀ env : Fin n → Term Symbol Γ predTy,
      Knowledge Δ env → ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets → good term = true →
        ∀ y : Term Symbol Γ setTy, y.isCore = true → Proof Δ (describes term y) → Proof Δ (point y env)) :
    ∀ (k : ℕ) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, Laws classical Δ → ∀ env : Fin n → Term Symbol Γ predTy,
      Knowledge Δ env → ∀ values : List Pattern, (∀ value ∈ values, IsHF value) →
        (∀ value ∈ values, zfOf value ∈ region.sets) → countDecide good k values = true →
          ∀ x : Term Symbol Γ setTy, Proof Δ (describesSome values x) → Proof Δ (countWith point k x env)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => truthIntro
  | k + 1, Γ, Δ, laws₀, env, know₀, values, hereditary, inside, counted, x, described₀ => by
    refine .impE (.impI ?_) described₀
    have laws := laws₀.prepend (describesSome values x)
    have know := prependKnowledge know₀ (describesSome values x)
    have described := Proof.newest (Δ := Δ) (describesSome values x)
    have found : ∃ value ∈ values,
        (good value && countDecide good k (values.filter fun other => !sameSet other value)) = true :=
      List.any_eq_true.mp counted
    let index := (chooseIndex values _ found).1
    have chosen := Bool.and_eq_true_iff.mp (chooseIndex values _ found).2
    have termHolds := hereditary _ (List.get_mem values index)
    have termInside := inside _ (List.get_mem values index)
    refine someMemberHyps described index ?_
    rw [weaken_countWith natural]
    change Proof _ (existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken (weaken x)))
      (conjunctionFormula (point (.var .vz) (underElement (underElement env)))
        (countWith point k (withoutSame (weaken (weaken x)) (.var .vz)) (underElement (underElement env))))))
    have laws3 := (((laws.lift setTy).prepend (conjunctionFormula (member (.var .vz) (weaken x))
      (describes (values.get index) (.var .vz)))).prepend (member (.var .vz) (weaken x))).prepend
        (describes (values.get index) (.var .vz))
    have know3 := prependKnowledge (prependKnowledge (prependKnowledge (liftKnowledge know)
      (conjunctionFormula (member (.var .vz) (weaken x)) (describes (values.get index) (.var .vz))))
        (member (.var .vz) (weaken x))) (describes (values.get index) (.var .vz))
    have describedLifted := Proof.prepend (describes (values.get index) (.var .vz))
      (Proof.prepend (member (.var .vz) (weaken x)) (describesSomeUnder described setTy
        (conjunctionFormula (member (.var .vz) (weaken x)) (describes (values.get index) (.var .vz)))))
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_countBody natural k _ _ _).symm
      (conjunctionIntro ?_ (conjunctionIntro ?_ ?_)))
    · exact Proof.prepend _ (Proof.newest _)
    · exact pointProof laws3 (underElement env) know3 _ termHolds termInside chosen.1 (.var .vz) rfl (Proof.newest _)
    · exact proveCount region natural Knowledge prependKnowledge liftKnowledge good pointProof k laws3 (underElement env)
        know3 (values.filter fun other => !sameSet other (values.get index))
        (fun value member => hereditary value (List.mem_filter.mp member).1)
        (fun value member => inside value (List.mem_filter.mp member).1) chosen.2 _
        (describesWithout laws3 hereditary termHolds rfl describedLifted (Proof.newest _))

/-- **A proof that fewer than `k` of the listed members have a property**, at a set the list describes: whichever
member is offered either lacks it or leaves too few among the members presenting other sets. -/
def refuteCount (region : Region) {classical : Bool}
    (natural : ∀ {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (y : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (point y env) = point (subst θ y) fun index => subst θ (env index))
    (Knowledge : ∀ {Γ : Ctx Unit}, List (Term Symbol Γ .prop) → (Fin n → Term Symbol Γ predTy) → Type)
    (prependKnowledge : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {env : Fin n → Term Symbol Γ predTy},
      Knowledge Δ env → ∀ ψ, Knowledge (ψ :: Δ) env)
    (liftKnowledge : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)} {env : Fin n → Term Symbol Γ predTy},
      Knowledge Δ env → Knowledge (weakenHyps (σ := setTy) Δ) (underElement env))
    (good : Pattern → Bool)
    (pointRefute : ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, Laws classical Δ → ∀ env : Fin n → Term Symbol Γ predTy,
      Knowledge Δ env → ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets → good term = false →
        ∀ y : Term Symbol Γ setTy, y.isCore = true → Proof Δ (describes term y) → Proof Δ (negCore (point y env))) :
    ∀ (k : ℕ) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, Laws classical Δ → ∀ env : Fin n → Term Symbol Γ predTy,
      Knowledge Δ env → ∀ values : List Pattern, (∀ value ∈ values, IsHF value) →
        (∀ value ∈ values, zfOf value ∈ region.sets) → countDecide good k values = false →
          ∀ x : Term Symbol Γ setTy, Proof Δ (describesSome values x) → Proof Δ (negCore (countWith point k x env))
  | 0, _, _, _, _, _, _, _, _, refused, _, _ => absurd refused (by simp [countDecide])
  | k + 1, Γ, Δ, laws₀, env, know₀, values, hereditary, inside, refused, x, described₀ => by
    refine .impE (.impI ?_) described₀
    have laws := laws₀.prepend (describesSome values x)
    have know := prependKnowledge know₀ (describesSome values x)
    have described := Proof.newest (Δ := Δ) (describesSome values x)
    let offered : Term Symbol (setTy :: Γ) .prop := conjunctionFormula (member (.var .vz) (weaken x))
      (conjunctionFormula (point (.var .vz) (underElement env)) (countWith point k (withoutSame (weaken x) (.var .vz))
        (underElement env)))
    change Proof (describesSome values x :: Δ) (negCore (existentialInline (σ := setTy) offered))
    refine .impI (existentialElim (Proof.newest _) ?_)
    have describedX := describesSomeUnder (described.prepend (existentialInline (σ := setTy) offered)) setTy offered
    refine oneCases values (describesSome_forward describedX (conjunctionLeft (Proof.newest _))) fun index => ?_
    have termHolds := hereditary _ (List.get_mem values index)
    have termInside := inside _ (List.get_mem values index)
    have laws2 := (((laws.prepend (existentialInline (σ := setTy) offered)).lift setTy).prepend offered).prepend
      (describes (values.get index) (.var .vz))
    have know2 := prependKnowledge (prependKnowledge (liftKnowledge (prependKnowledge know
      (existentialInline (σ := setTy) offered))) offered) (describes (values.get index) (.var .vz))
    refine if accepted : good (values.get index) = true then ?_ else ?_
    · have rest : countDecide good k (values.filter fun other => !sameSet other (values.get index)) = false :=
        Bool.eq_false_iff.mpr fun counted => List.any_eq_false.mp refused _ (List.get_mem _ _)
          (Bool.and_eq_true_iff.mpr ⟨accepted, counted⟩)
      exact .impE (refuteCount region natural Knowledge prependKnowledge liftKnowledge good pointRefute k laws2 (underElement env) know2
        (values.filter fun other => !sameSet other (values.get index))
        (fun value member => hereditary value (List.mem_filter.mp member).1)
        (fun value member => inside value (List.mem_filter.mp member).1) rest _
        (describesWithout laws2 hereditary termHolds rfl (Proof.prepend _ describedX) (Proof.newest _)))
        (Proof.prepend _ (conjunctionRight (conjunctionRight (Proof.newest _))))
    · exact .impE (pointRefute laws2 (underElement env) know2 _ termHolds termInside (Bool.eq_false_iff.mpr accepted)
        (.var .vz) rfl (Proof.newest _)) (Proof.prepend _ (conjunctionLeft (conjunctionRight (Proof.newest _))))

end Counting



/-! ## Parts of a described set -/

section Parts

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- `∀ z. z ∈ x → z is described by one of the terms`: the forward half of a description. -/
abbrev upperFormula (values : List Pattern) (x : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (.imp (member (.var .vz) (weaken x)) (describesOne values (.var .vz)))

/-- **The part of `x` that the terms describe**: `{z ∈ x | z is described by one of the terms}`. -/
def partTerm (x : Term Symbol Γ setTy) (values : List Pattern) : Term Symbol Γ setTy :=
  separate x (.lam (describesOne values (.var .vz)))

theorem isCore_partTerm {x : Term Symbol Γ setTy} (coreX : x.isCore = true) (values : List Pattern) :
    (partTerm x values).isCore = true := by
  simp only [partTerm, separate, Mettapedia.Logic.HOL.Term.isCore, coreX, isCore_describesOne values
    (y := (.var .vz : Term Symbol (setTy :: Γ) setTy)) rfl, Bool.and_self]

theorem weaken_partTerm {σ : Ty Unit} (x : Term Symbol Γ setTy) (values : List Pattern) :
    weaken (σ := σ) (partTerm x values) = partTerm (weaken x) values := by
  rw [weaken_eq_subst, weaken_eq_subst]
  simp only [partTerm, separate, subst, subst_describesOne]
  rfl

/-- Membership in a part: a member of `x` that the terms describe. -/
def partMember (laws : HasLaws Δ) (x : Term Symbol Γ setTy) (values : List Pattern) {z : Term Symbol Γ setTy}
    (coreZ : z.isCore = true) : Proof Δ (iffCore (member z (partTerm x values)) (conjunctionFormula (member z x) (describesOne values z))) := by
  have law := laws.separationAt x (.lam (describesOne values (.var .vz))) z
  refine Proof.iffIntro ?_ ?_
  · have both := (Proof.prepend _ law).iffForward (Proof.newest _)
    exact conjunctionIntro (conjunctionLeft both) (Proof.cast (instantiate_describesOne values z)
      (Proof.betaReduce (isCore_describesOne values rfl) coreZ (conjunctionRight both)))
  · exact (Proof.prepend _ law).iffBackward (conjunctionIntro (conjunctionLeft (Proof.newest _))
      (Proof.betaExpand (isCore_describesOne values rfl) coreZ (Proof.cast (instantiate_describesOne values z).symm
        (conjunctionRight (Proof.newest _)))))

/-- A member that a term describes, found by membership of the term. -/
def someMemberOfMem {x : Term Symbol Γ setTy} {value : Pattern} : ∀ {values : List Pattern}, value ∈ values →
    Proof Δ (eachDescribed values x) → Proof Δ (someMemberFormula value x)
  | [], found, _ => absurd found List.not_mem_nil
  | head :: _, found, each =>
    if same : value = head then same ▸ conjunctionLeft each
    else someMemberOfMem ((List.mem_cons.mp found).resolve_left same) (conjunctionRight each)

/-- **The part of a described set that a sublist describes is described by it**, forward and existentially. -/
def partDescribed (laws : HasLaws Δ) {values : List Pattern} {x : Term Symbol Γ setTy}
    (described : Proof Δ (describesSome values x)) (part : List Pattern) (sub : ∀ value ∈ part, value ∈ values) :
    Proof Δ (describesSome part (partTerm x part)) := by
  refine conjunctionIntro ?_ (eachDescribedOfComponents fun index => ?_)
  · change Proof Δ (upperFormula part (partTerm x part))
    rw [upperFormula, weaken_partTerm]
    exact .allI (.impI (conjunctionRight ((partMember ((laws.lift setTy).prepend _) (weaken x) part (z := .var .vz) rfl).iffForward
      (Proof.newest _))))
  · refine existentialElim (someMemberOfMem (sub _ (List.get_mem _ index)) (conjunctionRight described)) ?_
    rw [weaken_someMemberFormula, weaken_partTerm]
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_someMember _ _ _).symm
      (conjunctionIntro ?_ (conjunctionRight (Proof.newest _))))
    exact (partMember ((laws.lift setTy).prepend _) (weaken x) part (z := .var .vz) rfl).iffBackward
      (conjunctionIntro (conjunctionLeft (Proof.newest _))
        (oneIntroOfMem (conjunctionRight (Proof.newest _)) part (List.get_mem _ index)))

theorem instantiate_splitCoreBody (x a b z : Term Symbol Γ setTy) :
    instantiate z (iffCore (member (.var .vz) (weaken x))
      (disjunctionFormula (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b)))) =
      iffCore (member z x) (disjunctionFormula (member z a) (member z b)) := by
  unfold instantiate
  rw [subst_iffCore, subst_disjunctionFormula]
  change iffCore (member z (instantiate z (weaken x)))
    (disjunctionFormula (member z (instantiate z (weaken a))) (member z (instantiate z (weaken b)))) = _
  rw [Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken,
    Mettapedia.Logic.HOL.instantiate_weaken]

/-- A split at one set. -/
def splitAt {x a b : Term Symbol Γ setTy} (union : Proof Δ (splitCore x a b)) (z : Term Symbol Γ setTy) :
    Proof Δ (iffCore (member z x) (disjunctionFormula (member z a) (member z b))) :=
  Proof.cast (instantiate_splitCoreBody x a b z) (.allE z union)

theorem weaken_splitCore {σ : Ty Unit} (x a b : Term Symbol Γ setTy) :
    weaken (σ := σ) (splitCore x a b) = splitCore (weaken x) (weaken a) (weaken b) := by
  rw [weaken_eq_subst, subst_splitCore, ← weaken_eq_subst, ← weaken_eq_subst, ← weaken_eq_subst]

/-- **A described set is the union of the parts a covering describes.** -/
def partsSplit (laws : HasLaws Δ) {values : List Pattern} {x : Term Symbol Γ setTy}
    (described : Proof Δ (describesSome values x)) (left right : List Pattern)
    (covered : ∀ value ∈ values, value ∈ left ∨ value ∈ right) :
    Proof Δ (splitCore x (partTerm x left) (partTerm x right)) := by
  change Proof Δ (.all (iffCore (member (.var .vz) (weaken x)) (disjunctionFormula
    (member (.var .vz) (weaken (partTerm x left))) (member (.var .vz) (weaken (partTerm x right))))))
  rw [weaken_partTerm, weaken_partTerm]
  refine .allI (Proof.iffIntro ?_ ?_)
  · refine oneCases values (describesSome_forward (describesSomeUnder described setTy _) (Proof.newest _))
      fun index => ?_
    have laws' := ((laws.lift setTy).prepend (member (.var .vz) (weaken x))).prepend
      (describes (values.get index) (.var .vz))
    have isMember := Proof.prepend (describes (values.get index) (.var .vz))
      (Proof.newest (Δ := weakenHyps (σ := setTy) Δ) (member (.var .vz) (weaken x)))
    exact if inLeft : values.get index ∈ left then
        disjunctionLeft ((partMember laws' (weaken x) left (z := .var .vz) rfl).iffBackward
          (conjunctionIntro isMember (oneIntroOfMem (Proof.newest _) left inLeft)))
      else
        disjunctionRight ((partMember laws' (weaken x) right (z := .var .vz) rfl).iffBackward
          (conjunctionIntro isMember (oneIntroOfMem (Proof.newest _) right
            ((covered _ (List.get_mem _ index)).resolve_left inLeft))))
  · refine disjunctionElim (Proof.newest _) ?_ ?_
    · exact conjunctionLeft ((partMember (((laws.lift setTy).prepend _).prepend _) (weaken x) left (z := .var .vz) rfl).iffForward
        (Proof.newest _))
    · exact conjunctionLeft ((partMember (((laws.lift setTy).prepend _).prepend _) (weaken x) right (z := .var .vz) rfl).iffForward
        (Proof.newest _))

end Parts

/-! ## Branching on which members land in two parts -/

section Branching

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- A set described by one of the listed terms, but not by a dropped one, is described by one of the rest. -/
def describesOneDrop {z : Term Symbol Γ setTy} {value : Pattern} : ∀ {Δ : List (Term Symbol Γ .prop)}
    (front : List Pattern) {back : List Pattern}, Proof Δ (negCore (describes value z)) →
      Proof Δ (describesOne (front ++ value :: back) z) → Proof Δ (describesOne (front ++ back) z)
  | _, [], _, kill, one =>
    disjunctionElim one (Proof.absurd (.impE (Proof.prepend _ kill) (Proof.newest _))) (Proof.newest _)
  | _, _ :: front, _, kill, one =>
    disjunctionElim one (disjunctionLeft (Proof.newest _))
      (disjunctionRight (describesOneDrop front (Proof.prepend _ kill) (Proof.newest _)))

/-- Each listed term describing a member, with one more at the end. -/
def eachDescribedSnoc {x : Term Symbol Γ setTy} {value : Pattern} : ∀ {values : List Pattern},
    Proof Δ (eachDescribed values x) → Proof Δ (someMemberFormula value x) →
      Proof Δ (eachDescribed (values ++ [value]) x)
  | [], _, found => conjunctionIntro found truthIntro
  | _ :: _, each, found => conjunctionIntro (conjunctionLeft each) (eachDescribedSnoc (conjunctionRight each) found)

/-- A member of `a` that a term describes. -/
def presentAt {a z : Term Symbol Γ setTy} {value : Pattern} (isMember : Proof Δ (member z a))
    (described : Proof Δ (describes value z)) : Proof Δ (someMemberFormula value a) :=
  existentialIntro z (Proof.cast (instantiate_someMember value a z).symm (conjunctionIntro isMember described))

theorem weaken_negSomeMember {σ : Ty Unit} (value : Pattern) (a : Term Symbol Γ setTy) :
    weaken (σ := σ) (negCore (someMemberFormula value a)) = negCore (someMemberFormula value (weaken a)) := by
  change Term.imp (weaken (someMemberFormula value a)) (weaken falsity) = _
  rw [weaken_someMemberFormula]
  rfl

/-- That no member of `a` is described by a term, under a new variable and a new hypothesis. -/
def absentUnder {a : Term Symbol Γ setTy} {value : Pattern} (absent : Proof Δ (negCore (someMemberFormula value a)))
    (ψ : Term Symbol (setTy :: Γ) .prop) :
    Proof (ψ :: weakenHyps (σ := setTy) Δ) (negCore (someMemberFormula value (weaken a))) :=
  Proof.prepend ψ (Proof.cast (weaken_negSomeMember value a) absent.lift)

/-- **The forward half of a part's description loses a term no member of the part has.** -/
def upperDrop {a : Term Symbol Γ setTy} {value : Pattern} (front : List Pattern) {back : List Pattern}
    (upper : Proof Δ (upperFormula (front ++ value :: back) a)) (absent : Proof Δ (negCore (someMemberFormula value a))) :
    Proof Δ (upperFormula (front ++ back) a) := by
  refine .allI (.impI ?_)
  refine describesOneDrop front (.impI (.impE (Proof.prepend _ (absentUnder absent _)) ?_))
    (.impE (Proof.atNewest (Proof.prepend _ upper.lift)) (Proof.newest _))
  exact presentAt (Proof.prepend _ (Proof.newest _)) (Proof.newest _)

/-- **A member of the set lands in a part**: when it lands in neither, falsity. -/
def bothAbsent {values : List Pattern} {x a b : Term Symbol Γ setTy} {value : Pattern} (inValues : value ∈ values)
    (describedX : Proof Δ (describesSome values x)) (union : Proof Δ (splitCore x a b))
    (absentA : Proof Δ (negCore (someMemberFormula value a))) (absentB : Proof Δ (negCore (someMemberFormula value b))) :
    Proof Δ falsity :=
  existentialElim (someMemberOfMem inValues (conjunctionRight describedX))
    (disjunctionElim ((splitAt (Proof.prepend _ (Proof.cast (weaken_splitCore _ _ _) union.lift)) (.var .vz)).iffForward
        (conjunctionLeft (Proof.newest _)))
      (.impE (Proof.prepend _ (absentUnder absentA _))
        (presentAt (Proof.newest _) (Proof.prepend _ (conjunctionRight (Proof.newest _)))))
      (.impE (Proof.prepend _ (absentUnder absentB _))
        (presentAt (Proof.newest _) (Proof.prepend _ (conjunctionRight (Proof.newest _))))))

theorem upper_snoc (left rest : List Pattern) (value : Pattern) (a : Term Symbol Γ setTy) :
    upperFormula (left ++ value :: rest) a = upperFormula ((left ++ [value]) ++ rest) a := by
  rw [List.append_assoc, List.singleton_append]

/-- **Branching on which members land in two parts**: for a set described by `values` and split into `a` and `b`,
members are taken one by one, each split into whether some member of `a` it describes exists, and the same for `b`.
A member in neither part closes its branch by falsity; at the end, the members found in each part describe it,
forward and existentially, and the branch is finished by `leaf`. The case analysis is given (`analyze`): with a goal
of falsity it needs no excluded middle. -/
def coverBranches {values : List Pattern} {x a b : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop}
    (describedX : Proof Δ (describesSome values x)) (union : Proof Δ (splitCore x a b))
    (analyze : ∀ (extra : List (Term Symbol Γ .prop)) (P : Term Symbol Γ .prop),
      Proof (P :: (extra ++ Δ)) goal → Proof (negCore P :: (extra ++ Δ)) goal → Proof (extra ++ Δ) goal)
    (leaf : ∀ (extra : List (Term Symbol Γ .prop)) (left right : List Pattern), (∀ value ∈ left, value ∈ values) →
      (∀ value ∈ right, value ∈ values) → (∀ value ∈ values, value ∈ left ∨ value ∈ right) →
        Proof (extra ++ Δ) (describesSome left a) → Proof (extra ++ Δ) (describesSome right b) →
          Proof (extra ++ Δ) goal) :
    ∀ (rest left right : List Pattern) (extra : List (Term Symbol Γ .prop)),
      (∀ value ∈ rest, value ∈ values) → (∀ value ∈ left, value ∈ values) → (∀ value ∈ right, value ∈ values) →
        (∀ value ∈ values, value ∈ left ∨ value ∈ right ∨ value ∈ rest) →
          Proof (extra ++ Δ) (upperFormula (left ++ rest) a) → Proof (extra ++ Δ) (eachDescribed left a) →
            Proof (extra ++ Δ) (upperFormula (right ++ rest) b) → Proof (extra ++ Δ) (eachDescribed right b) →
              Proof (extra ++ Δ) goal
  | [], left, right, extra, _, inLeft, inRight, covered, upperA, eachA, upperB, eachB =>
    leaf extra left right inLeft inRight
      (fun value found => ((covered value found).imp_right fun rest => rest.resolve_right List.not_mem_nil))
      (conjunctionIntro (Proof.cast (by rw [List.append_nil]) upperA) eachA)
      (conjunctionIntro (Proof.cast (by rw [List.append_nil]) upperB) eachB)
  | value :: rest, left, right, extra, inRest, inLeft, inRight, covered, upperA, eachA, upperB, eachB =>
    have valueIn : value ∈ values := inRest value List.mem_cons_self
    have restIn : ∀ other ∈ rest, other ∈ values := fun other found => inRest other (List.mem_cons_of_mem _ found)
    have leftIn : ∀ other ∈ left ++ [value], other ∈ values := fun other found =>
      (List.mem_append.mp found).elim (inLeft other) fun single => (List.mem_singleton.mp single) ▸ valueIn
    have rightIn : ∀ other ∈ right ++ [value], other ∈ values := fun other found =>
      (List.mem_append.mp found).elim (inRight other) fun single => (List.mem_singleton.mp single) ▸ valueIn
    have step : ∀ other ∈ values, other ∈ left ∨ other ∈ right ∨ other = value ∨ other ∈ rest := fun other found =>
      (covered other found).imp_right (Or.imp_right fun inCons => List.mem_cons.mp inCons)
    analyze extra (someMemberFormula value a)
      (analyze (someMemberFormula value a :: extra) (someMemberFormula value b)
        (coverBranches describedX union analyze leaf rest (left ++ [value]) (right ++ [value])
          (someMemberFormula value b :: someMemberFormula value a :: extra) restIn leftIn rightIn
          (fun other found => by
            rcases step other found with inL | inR | rfl | inRest'
            · exact Or.inl (List.mem_append_left _ inL)
            · exact Or.inr (Or.inl (List.mem_append_left _ inR))
            · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
            · exact Or.inr (Or.inr inRest'))
          (Proof.prepend _ (Proof.prepend _ (Proof.cast (upper_snoc left rest value a) upperA)))
          (Proof.prepend _ (eachDescribedSnoc (Proof.prepend _ eachA) (Proof.newest _)))
          (Proof.cast (upper_snoc right rest value b) (Proof.prepend _ (Proof.prepend _ upperB)))
          (eachDescribedSnoc (Proof.prepend _ (Proof.prepend _ eachB)) (Proof.newest _)))
        (coverBranches describedX union analyze leaf rest (left ++ [value]) right
          (negCore (someMemberFormula value b) :: someMemberFormula value a :: extra) restIn leftIn inRight
          (fun other found => by
            rcases step other found with inL | inR | rfl | inRest'
            · exact Or.inl (List.mem_append_left _ inL)
            · exact Or.inr (Or.inl inR)
            · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
            · exact Or.inr (Or.inr inRest'))
          (Proof.prepend _ (Proof.prepend _ (Proof.cast (upper_snoc left rest value a) upperA)))
          (Proof.prepend _ (eachDescribedSnoc (Proof.prepend _ eachA) (Proof.newest _)))
          (upperDrop right (Proof.prepend _ (Proof.prepend _ upperB)) (Proof.newest _))
          (Proof.prepend _ (Proof.prepend _ eachB))))
      (analyze (negCore (someMemberFormula value a) :: extra) (someMemberFormula value b)
        (coverBranches describedX union analyze leaf rest left (right ++ [value])
          (someMemberFormula value b :: negCore (someMemberFormula value a) :: extra) restIn inLeft rightIn
          (fun other found => by
            rcases step other found with inL | inR | rfl | inRest'
            · exact Or.inl inL
            · exact Or.inr (Or.inl (List.mem_append_left _ inR))
            · exact Or.inr (Or.inl (List.mem_append_right _ (List.mem_singleton_self _)))
            · exact Or.inr (Or.inr inRest'))
          (upperDrop left (Proof.prepend _ upperA) (Proof.newest _) |>.prepend _)
          (Proof.prepend _ (Proof.prepend _ eachA))
          (Proof.cast (upper_snoc right rest value b) (Proof.prepend _ (Proof.prepend _ upperB)))
          (eachDescribedSnoc (Proof.prepend _ (Proof.prepend _ eachB)) (Proof.newest _)))
        (Proof.absurd (bothAbsent valueIn (Proof.prepend _ (Proof.prepend _ (Proof.prependAll extra describedX)))
          (Proof.prepend _ (Proof.prepend _ (Proof.prependAll extra union))) (Proof.prepend _ (Proof.newest _))
          (Proof.newest _))))

end Branching

/-! ## Upward every-splits, constructively -/

section Upward

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- `x` has no member. -/
abbrev emptyFormula (x : Term Symbol Γ setTy) : Term Symbol Γ .prop := .all (negCore (member (.var .vz) (weaken x)))

theorem weaken_negCore {σ : Ty Unit} (p : Term Symbol Γ .prop) : weaken (σ := σ) (negCore p) = negCore (weaken p) := by
  rw [weaken_eq_subst, subst_negCore, ← weaken_eq_subst]

theorem weaken_emptyFormula {σ : Ty Unit} (x : Term Symbol Γ setTy) :
    weaken (σ := σ) (emptyFormula x) = emptyFormula (weaken x) := by
  rw [weaken_eq_subst (emptyFormula x), weaken_eq_subst x]
  simp only [emptyFormula, subst, subst_negCore, member, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem instantiate_negMember (y x : Term Symbol Γ setTy) :
    instantiate y (negCore (member (.var .vz) (weaken x))) = negCore (member y x) := by
  unfold instantiate
  rw [subst_negCore]
  show negCore (member y (subst (Subst.single y) (weaken x))) = negCore (member y x)
  rw [← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

/-- No member of an empty set is `y`. -/
def noMemberAt {x : Term Symbol Γ setTy} (empty : Proof Δ (emptyFormula x)) (y : Term Symbol Γ setTy) :
    Proof Δ (negCore (member y x)) :=
  Proof.cast (instantiate_negMember y x) (.allE (φ := negCore (member (.var .vz) (weaken x))) y empty)

/-- `small ⊆ large`. -/
abbrev subsetFormula (small large : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (.imp (member (.var .vz) (weaken small)) (member (.var .vz) (weaken large)))

theorem instantiate_subsetBody (z small large : Term Symbol Γ setTy) :
    instantiate z (.imp (member (.var .vz) (weaken small)) (member (.var .vz) (weaken large))) =
      .imp (member z small) (member z large) := by
  unfold instantiate
  show Term.imp (member z (subst (Subst.single z) (weaken small))) (member z (subst (Subst.single z) (weaken large))) =
    _
  rw [← instantiate, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken, Mettapedia.Logic.HOL.instantiate_weaken]

theorem weaken_subsetFormula {σ : Ty Unit} (small large : Term Symbol Γ setTy) :
    weaken (σ := σ) (subsetFormula small large) = subsetFormula (weaken small) (weaken large) := by
  rw [weaken_eq_subst (subsetFormula small large), weaken_eq_subst small, weaken_eq_subst large]
  simp only [subsetFormula, subst, member, Mettapedia.Logic.HOL.subst_weaken]
  rfl

/-- A member of the smaller set is a member of the larger. -/
def subsetAt {small large : Term Symbol Γ setTy} (sub : Proof Δ (subsetFormula small large)) (z : Term Symbol Γ setTy)
    (inside : Proof Δ (member z small)) : Proof Δ (member z large) :=
  .impE (Proof.cast (instantiate_subsetBody z small large)
    (.allE (φ := .imp (member (.var .vz) (weaken small)) (member (.var .vz) (weaken large))) z sub)) inside

/-- The part of `a` that the terms describe lies inside `a`. -/
def partSubset (laws : HasLaws Δ) (a : Term Symbol Γ setTy) (part : List Pattern) :
    Proof Δ (subsetFormula (partTerm a part) a) := by
  change Proof Δ (.all (.imp (member (.var .vz) (weaken (partTerm a part))) (member (.var .vz) (weaken a))))
  rw [weaken_partTerm]
  exact .allI (.impI (conjunctionLeft ((partMember ((laws.lift setTy).prepend _) (weaken a) part (z := .var .vz) rfl).iffForward
    (Proof.newest _))))

/-- **The part of `a` that some terms describe is described by them**, forward and existentially, when each describes a
member of `a`. -/
def partDescribedOfEach (laws : HasLaws Δ) {part : List Pattern} {a : Term Symbol Γ setTy}
    (each : Proof Δ (eachDescribed part a)) : Proof Δ (describesSome part (partTerm a part)) := by
  refine conjunctionIntro ?_ (eachDescribedOfComponents fun index => ?_)
  · change Proof Δ (upperFormula part (partTerm a part))
    rw [upperFormula, weaken_partTerm]
    exact .allI (.impI (conjunctionRight ((partMember ((laws.lift setTy).prepend _) (weaken a) part (z := .var .vz) rfl).iffForward
      (Proof.newest _))))
  · refine existentialElim (eachDescribed_get index each) ?_
    rw [weaken_someMemberFormula, weaken_partTerm]
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_someMember _ _ _).symm
      (conjunctionIntro ?_ (conjunctionRight (Proof.newest _))))
    exact (partMember ((laws.lift setTy).prepend _) (weaken a) part (z := .var .vz) rfl).iffBackward
      (conjunctionIntro (conjunctionLeft (Proof.newest _))
        (oneIntroOfMem (conjunctionRight (Proof.newest _)) part (List.get_mem _ index)))

/-- **An upward formula carries from a set to a larger one.** -/
def upwardMono : ∀ {Δ : List (Term Symbol Γ .prop)} {n : ℕ} (formula : Formula n), formula.upwardShape = true →
    formula.regional = true → ∀ (env : Fin n → Term Symbol Γ predTy) {small large : Term Symbol Γ setTy},
      Proof Δ (subsetFormula small large) → Proof Δ (nativeFormula formula small env) →
        Proof Δ (nativeFormula formula large env)
  | _, _, .top, _, _, _, _, _, _, _ => truthIntro
  | _, _, .and left right, shape, regional, env, _, _, sub, proof => by
    simp only [Formula.upwardShape, Bool.and_eq_true] at shape
    simp only [Formula.regional, Bool.and_eq_true] at regional
    exact conjunctionIntro (upwardMono left shape.1 regional.1 env sub (conjunctionLeft proof))
      (upwardMono right shape.2 regional.2 env sub (conjunctionRight proof))
  | _, _, .or left right, shape, regional, env, _, _, sub, proof => by
    simp only [Formula.upwardShape, Bool.and_eq_true] at shape
    simp only [Formula.regional, Bool.and_eq_true] at regional
    exact disjunctionElim proof
      (disjunctionLeft (upwardMono left shape.1 regional.1 env (Proof.prepend _ sub) (Proof.newest _)))
      (disjunctionRight (upwardMono right shape.2 regional.2 env (Proof.prepend _ sub) (Proof.newest _)))
  | Δ, _, .nonEmpty kind, shape, _, env, small, large, sub, proof => by
    have isSet : kind = .hashSet := of_decide_eq_true shape
    subst isSet
    change Proof Δ (negCore (emptyFormula large))
    change Proof Δ (negCore (emptyFormula small)) at proof
    refine .impI (.impE (Proof.prepend _ proof) (.allI (.impI ?_)))
    have subHere : Proof (member (.var .vz) (weaken small) :: weakenHyps (emptyFormula large :: Δ))
        (subsetFormula (weaken small) (weaken large)) :=
      Proof.prepend _ (Proof.cast (weaken_subsetFormula _ _)
        (Proof.lift (σ := setTy) (Proof.prepend (emptyFormula large) sub)))
    have emptyHere : Proof (member (.var .vz) (weaken small) :: weakenHyps (emptyFormula large :: Δ))
        (emptyFormula (weaken large)) :=
      Proof.prepend _ (Proof.cast (weaken_emptyFormula _)
        (Proof.lift (σ := setTy) (Proof.newest (Δ := Δ) (emptyFormula large))))
    exact .impE (noMemberAt emptyHere (.var .vz)) (subsetAt subHere (.var .vz) (Proof.newest _))
  | Δ, _, .possibly label inner, _, regional, env, small, large, sub, proof => by
    have regionalInner : inner.regional = true := regional
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.possibly label inner) small env = existentialInline (σ := setTy) (conjunctionFormula
        (member (.var .vz) (weaken small)) (nativeFormula inner (.var .vz) (underElement env))) by
        simp only [nativeFormula, if_pos labelled]] at proof
      refine existentialElim proof ?_
      rw [weaken_nativeFormula_regional (.possibly label inner) regional]
      rw [show nativeFormula (.possibly label inner) (weaken large) (fun index => weaken (env index)) =
        existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken (weaken large)))
          (nativeFormula inner (.var .vz) (underElement fun index => weaken (env index)))) by
        simp only [nativeFormula, if_pos labelled]]
      let found : Term Symbol (setTy :: Γ) .prop :=
        conjunctionFormula (member (.var .vz) (weaken small)) (nativeFormula inner (.var .vz) (underElement env))
      have subHere : Proof (found :: weakenHyps Δ) (subsetFormula (weaken small) (weaken large)) :=
        Proof.prepend _ (Proof.cast (weaken_subsetFormula _ _) (Proof.lift (σ := setTy) sub))
      refine existentialIntro (.var .vz) (Proof.cast (instantiate_possiblyBody regionalInner _ _ _).symm
        (conjunctionIntro (subsetAt subHere (.var .vz) (conjunctionLeft (Proof.newest found)))
          (conjunctionRight (Proof.newest found))))
    · rw [show nativeFormula (.possibly label inner) small env = falsity by simp only [nativeFormula, if_neg labelled]]
        at proof
      exact Proof.absurd proof
  | _, _, .bot, shape, _, _, _, _, _, _ | _, _, .var _, shape, _, _, _, _, _, _ | _, _, .is _, shape, _, _, _, _, _, _
  | _, _, .isNot _, shape, _, _, _, _, _, _ | _, _, .empty _, shape, _, _, _, _, _, _ | _, _, .typed _, shape, _, _, _, _, _, _
  | _, _, .untyped _, shape, _, _, _, _, _, _ | _, _, .mu _, shape, _, _, _, _, _, _ | _, _, .nu _, shape, _, _, _, _, _, _
  | _, _, .necessarily _ _, shape, _, _, _, _, _, _ | _, _, .single _ _, shape, _, _, _, _, _, _
  | _, _, .everySingle _ _, shape, _, _, _, _, _, _ | _, _, .atLeast _ _ _ _, shape, _, _, _, _, _, _
  | _, _, .allButFewer _ _ _ _, shape, _, _, _, _, _, _ | _, _, .sometimeBefore _ _, shape, _, _, _, _, _, _
  | _, _, .alwaysBefore _ _, shape, _, _, _, _, _, _ | _, _, .built _ _, shape, _, _, _, _, _, _
  | _, _, .everyBuilt _ _, shape, _, _, _, _, _, _ | _, _, .split _ _ _, shape, _, _, _, _, _, _
  | _, _, .everySplit _ _ _, shape, _, _, _, _, _, _ | _, _, .body _, shape, _, _, _, _, _, _
  | _, _, .everyBody _, shape, _, _, _, _, _, _ | _, _, .multiBody _ _, shape, _, _, _, _, _, _
  | _, _, .everyMultiBody _ _, shape, _, _, _, _, _, _ | _, _, .bound _, shape, _, _, _, _, _, _
  | _, _, .notBound _, shape, _, _, _, _, _, _ | _, _, .mapsAll _ _, shape, _, _, _, _, _, _
  | _, _, .mapsSome _ _, shape, _, _, _, _, _, _ | _, _, .someOf _ _, shape, _, _, _, _, _, _
  | _, _, .everyOf _ _, shape, _, _, _, _, _, _ => absurd shape Bool.false_ne_true

theorem weaken_disjunction {σ : Ty Unit} (p q : Term Symbol Γ .prop) :
    weaken (σ := σ) (disjunctionFormula p q) = disjunctionFormula (weaken p) (weaken q) := by
  rw [weaken_eq_subst, subst_disjunctionFormula, ← weaken_eq_subst, ← weaken_eq_subst]

/-- **Each member lies in a part**: a member of `x = a ∪ b` described by `v` is a member of `a` or of `b` described by
`v`, constructively, since the union is a disjunction. -/
def sideOf {x a b : Term Symbol Γ setTy} {value : Pattern} (union : Proof Δ (splitCore x a b))
    (some : Proof Δ (someMemberFormula value x)) :
    Proof Δ (disjunctionFormula (someMemberFormula value a) (someMemberFormula value b)) := by
  refine existentialElim some ?_
  rw [weaken_disjunction, weaken_someMemberFormula, weaken_someMemberFormula]
  refine disjunctionElim ((splitAt (Proof.prepend _ (Proof.cast (weaken_splitCore _ _ _) union.lift)) (.var .vz)).iffForward
      (conjunctionLeft (Proof.newest _))) ?_ ?_
  · exact disjunctionLeft (presentAt (Proof.newest _) (Proof.prepend _ (conjunctionRight (Proof.newest _))))
  · exact disjunctionRight (presentAt (Proof.newest _) (Proof.prepend _ (conjunctionRight (Proof.newest _))))

/-- **Branching on the parts the members lie in**: each branch knows lists of terms describing members of `a` and of
`b`, which together cover the listed terms. No excluded middle is used: each case split is the union's. -/
def branchSplits {Δ₀ : List (Term Symbol Γ .prop)} {x a b : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop}
    (values : List Pattern)
    (leaf : ∀ (extra : List (Term Symbol Γ .prop)) (first second : List Pattern),
      (∀ value ∈ values, value ∈ first ∨ value ∈ second) → (∀ value ∈ first, value ∈ values) →
        (∀ value ∈ second, value ∈ values) → Proof (extra ++ Δ₀) (eachDescribed first a) →
          Proof (extra ++ Δ₀) (eachDescribed second b) → Proof (extra ++ Δ₀) goal) :
    ∀ (extra : List (Term Symbol Γ .prop)) (pending first second : List Pattern),
      (∀ value ∈ values, value ∈ pending ∨ value ∈ first ∨ value ∈ second) → (∀ value ∈ pending, value ∈ values) →
        (∀ value ∈ first, value ∈ values) → (∀ value ∈ second, value ∈ values) →
          Proof (extra ++ Δ₀) (splitCore x a b) → Proof (extra ++ Δ₀) (eachDescribed pending x) →
            Proof (extra ++ Δ₀) (eachDescribed first a) → Proof (extra ++ Δ₀) (eachDescribed second b) →
              Proof (extra ++ Δ₀) goal
  | extra, [], first, second, covers, _, firstSub, secondSub, _, _, knownFirst, knownSecond =>
    leaf extra first second (fun value member => (covers value member).resolve_left List.not_mem_nil) firstSub
      secondSub knownFirst knownSecond
  | extra, value :: rest, first, second, covers, pendingSub, firstSub, secondSub, union, each, knownFirst,
      knownSecond =>
    disjunctionElim (sideOf union (conjunctionLeft each))
      (branchSplits values leaf (someMemberFormula value a :: extra) rest (value :: first) second
        (fun other member => by
          rcases covers other member with inPending | inFirst | inSecond
          · rcases List.mem_cons.mp inPending with rfl | inRest
            · exact Or.inr (Or.inl List.mem_cons_self)
            · exact Or.inl inRest
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ inFirst))
          · exact Or.inr (Or.inr inSecond))
        (fun other member => pendingSub other (List.mem_cons_of_mem _ member))
        (fun other member => (List.mem_cons.mp member).elim (fun same => same ▸ pendingSub _ List.mem_cons_self)
          (firstSub other))
        secondSub (Proof.prepend _ union) (Proof.prepend _ (conjunctionRight each))
        (conjunctionIntro (Proof.newest _) (Proof.prepend _ knownFirst)) (Proof.prepend _ knownSecond))
      (branchSplits values leaf (someMemberFormula value b :: extra) rest first (value :: second)
        (fun other member => by
          rcases covers other member with inPending | inFirst | inSecond
          · rcases List.mem_cons.mp inPending with rfl | inRest
            · exact Or.inr (Or.inr List.mem_cons_self)
            · exact Or.inl inRest
          · exact Or.inr (Or.inl inFirst)
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ inSecond)))
        (fun other member => pendingSub other (List.mem_cons_of_mem _ member))
        firstSub
        (fun other member => (List.mem_cons.mp member).elim (fun same => same ▸ pendingSub _ List.mem_cons_self)
          (secondSub other))
        (Proof.prepend _ union) (Proof.prepend _ (conjunctionRight each)) (Proof.prepend _ knownFirst)
        (conjunctionIntro (Proof.newest _) (Proof.prepend _ knownSecond)))

end Upward

/-! ## Splits from their parts -/

section SplitParts

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

theorem subst_single_weaken {σ τ : Ty Unit} (a : Term Symbol Γ σ) (t : Term Symbol Γ τ) :
    subst (Subst.single a) (weaken t) = t :=
  Mettapedia.Logic.HOL.instantiate_weaken a t

theorem single_underElement {n : ℕ} (a : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    (fun index => subst (Subst.single a) (underElement env index)) = env := by
  funext index
  exact subst_single_weaken a (env index)

theorem single_lift_single_older (a b : Term Symbol Γ setTy) :
    subst (Subst.single b) (subst (Subst.lift (Subst.single a)) (.var (.vs .vz) : Term Symbol (setTy :: setTy :: Γ) setTy)) =
      a :=
  subst_single_weaken b a

theorem single_lift_single_newest (a b : Term Symbol Γ setTy) :
    subst (Subst.single b) (subst (Subst.lift (Subst.single a)) (.var .vz : Term Symbol (setTy :: setTy :: Γ) setTy)) =
      b :=
  rfl

/-- The body of a split, with its two parts instantiated. -/
theorem instantiate_splitBody {n : ℕ} {left right : Formula n} (leftRegional : left.regional = true)
    (rightRegional : right.regional = true) (x a b : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate b (subst (Subst.lift (Subst.single a)) (conjunctionFormula
      (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
      (conjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
        (nativeFormula right (.var .vz) (underElement (underElement env)))))) =
      conjunctionFormula (splitCore x a b) (conjunctionFormula (nativeFormula left a env) (nativeFormula right b env)) := by
  unfold instantiate
  simp only [subst_conjunctionFormula, subst_splitCore, subst_nativeFormula_regional _ left leftRegional,
    subst_nativeFormula_regional _ right rightRegional, subst_underElement, Mettapedia.Logic.HOL.subst_weaken,
    subst_single_weaken, single_underElement, single_lift_single_older, single_lift_single_newest]

/-- The body of an every-split, with its two parts instantiated. -/
theorem instantiate_everySplitBody {n : ℕ} {left right : Formula n} (leftRegional : left.regional = true)
    (rightRegional : right.regional = true) (x a b : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate b (subst (Subst.lift (Subst.single a)) (.imp (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
      (disjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
        (nativeFormula right (.var .vz) (underElement (underElement env)))))) =
      .imp (splitCore x a b) (disjunctionFormula (nativeFormula left a env) (nativeFormula right b env)) := by
  unfold instantiate
  show Term.imp _ _ = _
  simp only [subst_disjunctionFormula, subst_splitCore, subst_nativeFormula_regional _ left leftRegional,
    subst_nativeFormula_regional _ right rightRegional, subst_underElement, Mettapedia.Logic.HOL.subst_weaken,
    subst_single_weaken, single_underElement, single_lift_single_older, single_lift_single_newest]

/-- **A split from its parts**: the union, and the two native types at the parts. -/
def splitIntro {n : ℕ} {left right : Formula n} (leftRegional : left.regional = true)
    (rightRegional : right.regional = true) {x : Term Symbol Γ setTy} {env : Fin n → Term Symbol Γ predTy}
    (a b : Term Symbol Γ setTy) (union : Proof Δ (splitCore x a b)) (atLeft : Proof Δ (nativeFormula left a env))
    (atRight : Proof Δ (nativeFormula right b env)) : Proof Δ (nativeFormula (.split .hashSet left right) x env) := by
  simp only [nativeFormula]
  refine existentialIntro a (Proof.cast (subst_existentialInline _ _).symm (existentialIntro b ?_))
  exact Proof.cast (instantiate_splitBody leftRegional rightRegional x a b env).symm
    (conjunctionIntro union (conjunctionIntro atLeft atRight))

/-- Every member of the first part is described as the members of the set are. -/
def upperOfLeft {values : List Pattern} {x a b : Term Symbol Γ setTy} (described : Proof Δ (describesSome values x))
    (union : Proof Δ (splitCore x a b)) : Proof Δ (upperFormula values a) :=
  .allI (.impI (describesSome_forward (describesSomeUnder described setTy _)
    ((splitAt (Proof.prepend _ (Proof.cast (weaken_splitCore _ _ _) union.lift)) (.var .vz)).iffBackward
      (disjunctionLeft (Proof.newest _)))))

/-- Every member of the second part is described as the members of the set are. -/
def upperOfRight {values : List Pattern} {x a b : Term Symbol Γ setTy} (described : Proof Δ (describesSome values x))
    (union : Proof Δ (splitCore x a b)) : Proof Δ (upperFormula values b) :=
  .allI (.impI (describesSome_forward (describesSomeUnder described setTy _)
    ((splitAt (Proof.prepend _ (Proof.cast (weaken_splitCore _ _ _) union.lift)) (.var .vz)).iffBackward
      (disjunctionRight (Proof.newest _)))))

end SplitParts

/-- **Two sublists covering a hereditary term's members present a split of its set.** -/
theorem zfOf_eq_union_of_cover {term : Pattern} (holds : IsHF term) {left right : List Pattern}
    (inLeft : ∀ value ∈ left, value ∈ membersOf term) (inRight : ∀ value ∈ right, value ∈ membersOf term)
    (covered : ∀ value ∈ membersOf term, value ∈ left ∨ value ∈ right) :
    zfOf term = zfOf (set left) ∪ zfOf (set right) := by
  rw [zfOf_eq_zfOfList holds, zfOf_set, zfOf_set]
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_union, mem_zfOfList, mem_zfOfList, mem_zfOfList]
  constructor
  · rintro ⟨value, found, rfl⟩
    rcases covered value found with inL | inR
    · exact Or.inl ⟨value, inL, rfl⟩
    · exact Or.inr ⟨value, inR, rfl⟩
  · rintro (⟨value, found, rfl⟩ | ⟨value, found, rfl⟩)
    · exact ⟨value, inLeft value found, rfl⟩
    · exact ⟨value, inRight value found, rfl⟩

/-! ## Proving the native types that hold -/

/-- The closure hypothesis of a least fixed point. -/
def closureHyp {n : ℕ} (inner : Formula (n + 1)) {Γ : Ctx Unit} (env : Fin n → Term Symbol Γ predTy) :
    Term Symbol (predTy :: Γ) .prop :=
  .all (σ := setTy) (.imp (nativeFormula inner (.var .vz) (underFixedPoint env)) (.app (.var (.vs .vz)) (.var .vz)))

/-- A prover for a formula, in every context. -/
abbrev Prover (region : Region) (classical : Bool) {n : ℕ} (formula : Formula n) : Type 1 :=
  ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, Laws classical Δ → ∀ (env : Fin n → Term Symbol Γ predTy)
    (sets : Env ZFSet.{0} n) (decision : Fin n → Pattern → Bool), Agrees region decision sets →
      PosKnowledge Δ env sets region.sets → ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
        extensional.sat sets formula (zfOf term) → ∀ x : Term Symbol Γ setTy, x.isCore = true →
          Proof Δ (describesSome (membersOf term) x) → Proof Δ (nativeFormula formula x env)

/-- The decisions of the stages of a least fixed point from below, on the region's terms. -/
def lfpDecision (region : Region) {n : ℕ} (inner : Formula (n + 1)) (decision : Fin n → Pattern → Bool) (k : ℕ) :
    Pattern → Bool :=
  presentedIn (stagesOn region.terms (fun stage => decideOn region.terms inner (Fin.cons (presentedIn stage) decision))
    [] k)

/-- The decisions of the stages of a greatest fixed point from above, on the region's terms. -/
def gfpDecision (region : Region) {n : ℕ} (inner : Formula (n + 1)) (decision : Fin n → Pattern → Bool) (k : ℕ) :
    Pattern → Bool :=
  presentedIn (stagesOn region.terms (fun stage => decideOn region.terms inner (Fin.cons (presentedIn stage) decision))
    region.terms k)

theorem lfpDecision_agrees (region : Region) {n : ℕ} {inner : Formula (n + 1)} (regional : inner.regional = true)
    (parts : PartsClosed region.sets) {decision : Fin n → Pattern → Bool} {sets : Env ZFSet.{0} n}
    (agree : Agrees region decision sets) (k : ℕ) :
    ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
      (lfpDecision region inner decision k term = true ↔ zfOf term ∈ lfpStage sets inner region.sets k) :=
  stagesOn_lfp region sets inner (fun _ _ same other member => decideOn_iff_regional region inner regional
    (Or.inr parts) (agree.extend same) other (region.hereditary _ member) (region.inside _ member)) k

theorem gfpDecision_agrees (region : Region) {n : ℕ} {inner : Formula (n + 1)} (regional : inner.regional = true)
    (parts : PartsClosed region.sets) {decision : Fin n → Pattern → Bool} {sets : Env ZFSet.{0} n}
    (agree : Agrees region decision sets) (k : ℕ) :
    ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
      (gfpDecision region inner decision k term = true ↔ zfOf term ∈ gfpStage sets inner region.sets k) :=
  stagesOn_gfp region sets inner (fun _ _ same other member => decideOn_iff_regional region inner regional
    (Or.inr parts) (agree.extend same) other (region.hereditary _ member) (region.inside _ member)) k

/-- **The stages of a least fixed point, as knowledge about its predicate variable**, under the closure
hypothesis. -/
def lfpKnowledge (region : Region) (parts : PartsClosed region.sets) {classical : Bool} {n : ℕ}
    {inner : Formula (n + 1)} (modal : inner.regionalWith classical = true)
    (proveInner : Prover region classical inner) {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}
    (laws : Laws classical Δ)
    (env : Fin n → Term Symbol Γ predTy) (sets : Env ZFSet.{0} n) (decision : Fin n → Pattern → Bool)
    (agree : Agrees region decision sets) (know : PosKnowledge Δ env sets region.sets) :
    ∀ (k : ℕ) (term : Pattern), IsHF term → zfOf term ∈ region.sets → zfOf term ∈ lfpStage sets inner region.sets k →
      Proof (closureHyp inner env :: weakenHyps (σ := predTy) Δ) (knowsAt (.var .vz) term)
  | 0, _, _, _, member => False.elim (Set.notMem_empty _ member)
  | k + 1, term, holds, inside, member => by
    refine .allI (.impI ?_)
    have closure : Proof (describesSome (membersOf term) (.var .vz) :: weakenHyps (σ := setTy)
        (closureHyp inner env :: weakenHyps (σ := predTy) Δ))
        (.imp (nativeFormula inner (.var .vz) (underFixedPoint env)) (.app (.var (.vs .vz)) (.var .vz))) :=
      Proof.atNewest (((Proof.newest (closureHyp inner env)).lift (σ := setTy)).prepend _)
    refine .impE closure (proveInner ((((laws.lift predTy).prepend _).lift setTy).prepend _) (underFixedPoint env)
      (sets.extend (lfpStage sets inner region.sets k)) (Fin.cons (lfpDecision region inner decision k) decision)
      (agree.extend (lfpDecision_agrees region (Formula.regional_of_regionalWith _ modal) parts agree k)) (fun index => ?_) term holds inside member.2 (.var .vz) rfl
      (Proof.newest _))
    refine Fin.cases (motive := fun index => ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
      zfOf term ∈ (sets.extend (lfpStage sets inner region.sets k)) index →
        Proof (describesSome (membersOf _) (.var .vz) :: weakenHyps (σ := setTy)
          (closureHyp inner env :: weakenHyps (σ := predTy) Δ))
          (knowsAt (underFixedPoint env index) term)) ?_ (fun index => ?_) index
    · intro other otherHolds otherInside otherMember
      exact (Proof.cast (weaken_knowsAt _ _) (lfpKnowledge region parts modal proveInner laws env sets decision agree know k
        other otherHolds otherInside otherMember).lift).prepend _
    · exact (((know.lift predTy).prepend _).lift setTy).prepend _ index

/-- **A proof that a modal native type holds**, at the set a hereditary term describes, whenever it holds. Branches
and witnesses are chosen by deciding the type on the region (`decideOn`). -/
def proveNative (region : Region) (parts : PartsClosed region.sets) (classical : Bool) :
    ∀ {n : ℕ} (formula : Formula n), formula.regionalWith classical = true →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, Laws classical Δ → ∀ (env : Fin n → Term Symbol Γ predTy)
      (sets : Env ZFSet.{0} n) (decision : Fin n → Pattern → Bool), Agrees region decision sets →
        PosKnowledge Δ env sets region.sets → ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
          extensional.sat sets formula (zfOf term) → ∀ x : Term Symbol Γ setTy, x.isCore = true →
            Proof Δ (describesSome (membersOf term) x) → Proof Δ (nativeFormula formula x env)
  | _, .top, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => truthIntro
  | _, .bot, _, _, _, _, _, _, _, _, _, _, _, _, holdsAt, _, _, _ => False.elim holdsAt
  | _, .and left right, modal, _, _, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x, coreX,
      described => by
    simp only [Formula.regionalWith, Bool.and_eq_true] at modal
    exact conjunctionIntro (proveNative region parts classical left modal.1 laws env sets decision agree know term holds inside holdsAt.1
      x coreX described)
      (proveNative region parts classical right modal.2 laws env sets decision agree know term holds inside holdsAt.2 x coreX described)
  | _, .or left right, modal, _, _, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x, coreX,
      described => by
    simp only [Formula.regionalWith, Bool.and_eq_true] at modal
    refine if first : decideOn region.terms left decision term = true then ?_ else ?_
    · exact disjunctionLeft (proveNative region parts classical left modal.1 laws env sets decision agree know term holds inside
        ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1) (Or.inr parts) agree term holds inside).mp first) x coreX described)
    · exact disjunctionRight (proveNative region parts classical right modal.2 laws env sets decision agree know term holds inside
        (holdsAt.resolve_left fun holdsLeft => first ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1) (Or.inr parts) agree term holds inside).mpr
          holdsLeft)) x coreX described)
  | _, .var index, _, _, _, _, _, _, _, _, know, term, holds, inside, holdsAt, _, _, described =>
    useKnows (know index term holds inside holdsAt) described
  | _, .mu inner, modal, _, _, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x, coreX,
      described => by
    have modalInner : inner.regionalWith classical = true := modal
    have member := (sat_mu_iff_regional sets (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) region.finite region.closed region.ncard_le inside).mp holdsAt
    change Proof _ (.all (σ := predTy) (.imp (closureHyp inner env) (.app (.var .vz) (weaken x))))
    exact .allI (.impI (useKnows (lfpKnowledge region parts modalInner (fun laws' env' sets' decision' agree' know' =>
      proveNative region parts classical inner modalInner laws' env' sets' decision' agree' know') laws env sets decision agree know _
      term holds inside member) (describesSomeUnder described predTy _)))
  | _, .nu inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x, coreX,
      described => by
    have modalInner : inner.regionalWith classical = true := modal
    let stable := gfpStage sets inner region.sets region.terms.length
    have stableIff : ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets →
        (decideOn region.terms (.nu inner) decision other = true ↔ zfOf other ∈ stable) :=
      fun other otherHolds otherInside => (decideOn_iff_regional region (.nu inner) (Formula.regional_of_regionalWith _ modal) (Or.inr parts) agree other otherHolds otherInside).trans
        (sat_nu_iff_regional sets (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) region.finite region.closed region.ncard_le otherInside)
    have member : zfOf term ∈ stable :=
      (sat_nu_iff_regional sets (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) region.finite region.closed region.ncard_le inside).mp holdsAt
    let chosen := region.terms.filter (decideOn region.terms (.nu inner) decision)
    have chosenHereditary : ∀ value ∈ chosen, IsHF value :=
      fun value inChosen => region.hereditary _ (List.mem_filter.mp inChosen).1
    have chosenFound : ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets → zfOf other ∈ stable →
        ∃ value ∈ chosen, zfOf value = zfOf other := by
      intro other otherHolds otherInside otherMember
      obtain ⟨value, valueIn, same⟩ := region.covers _ otherInside
      exact ⟨value, List.mem_filter.mpr ⟨valueIn, (stableIff value (region.hereditary _ valueIn)
        (region.inside _ valueIn)).mpr (same ▸ otherMember)⟩, same⟩
    have knows : ∀ {Γ' : Ctx Unit} {Δ' : List (Term Symbol Γ' .prop)} (other : Pattern), IsHF other →
        zfOf other ∈ region.sets → zfOf other ∈ stable → Proof Δ' (knowsAt (describedPredicate chosen) other) := by
      intro Γ' Δ' other otherHolds otherInside otherMember
      refine .allI (.impI ?_)
      rw [weaken_describedPredicate]
      refine Proof.betaExpand (isCore_predicateBody chosen) rfl (Proof.cast (instantiate_someOne chosen _).symm ?_)
      exact someOneIntro chosen (presenterIndex chosen chosenHereditary otherHolds
          (chosenFound other otherHolds otherInside otherMember)).1
        (describesSomeSame otherHolds (chosenHereditary _ (List.get_mem _ _))
          (presenterIndex chosen chosenHereditary otherHolds (chosenFound other otherHolds otherInside otherMember)).2
          (Proof.newest _))
    change Proof _ (existentialInline (σ := predTy) (conjunctionFormula (.all (σ := setTy)
      (.imp (.app (.var (.vs .vz)) (.var .vz)) (nativeFormula inner (.var .vz) (underFixedPoint env))))
        (.app (.var .vz) (weaken x))))
    refine existentialIntro (describedPredicate chosen) (Proof.cast (instantiate_nuBody (Formula.regional_of_regionalWith _ modalInner) _ x env).symm
      (conjunctionIntro (.allI (.impI ?_)) ?_))
    · have unfolded : Proof (.app (weaken (describedPredicate chosen)) (.var .vz) :: weakenHyps (σ := setTy) Δ)
          (someOne chosen (.var .vz)) := by
        refine Proof.cast (instantiate_newest_lifted (someOne chosen (.var .vz))) ?_
        exact Proof.betaReduce (by rw [Mettapedia.Logic.HOL.Term.isCore_rename]; exact isCore_predicateBody chosen) rfl
          (Proof.newest _)
      refine someOneCases chosen unfolded fun index => ?_
      have inChosen := List.mem_filter.mp (List.get_mem chosen index)
      have chosenHolds := region.hereditary _ inChosen.1
      have chosenInside := region.inside _ inChosen.1
      have chosenMember : zfOf (chosen.get index) ∈ stable := (stableIff _ chosenHolds chosenInside).mp inChosen.2
      refine proveNative region parts classical inner modalInner ((laws.lift setTy).prepend _ |>.prepend _)
        (Fin.cons (weaken (describedPredicate chosen)) (underElement env)) (sets.extend stable)
        (Fin.cons (decideOn region.terms (.nu inner) decision) decision) (agree.extend stableIff) (fun index' => ?_)
        (chosen.get index) chosenHolds chosenInside
        ((gfpStage_fixed sets inner region.sets region.finite region.ncard_le chosenInside).mp chosenMember) (.var .vz)
        rfl (Proof.newest _)
      refine Fin.cases (motive := fun index' => ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets →
        zfOf other ∈ (sets.extend stable) index' → Proof _ (knowsAt ((Fin.cons (weaken (describedPredicate chosen))
          (underElement env) : Fin _ → Term Symbol (setTy :: Γ) predTy) index') other)) ?_ (fun index' => ?_) index'
      · intro other otherHolds otherInside otherMember
        rw [Fin.cons_zero, weaken_describedPredicate]
        exact knows other otherHolds otherInside otherMember
      · exact ((know.lift setTy).prepend _ |>.prepend _) index'
    · refine Proof.betaExpand (isCore_predicateBody chosen) coreX (Proof.cast (instantiate_someOne chosen x).symm ?_)
      exact someOneIntro chosen (presenterIndex chosen chosenHereditary holds (chosenFound term holds inside member)).1
        (describesSomeSame holds (chosenHereditary _ (List.get_mem _ _))
          (presenterIndex chosen chosenHereditary holds (chosenFound term holds inside member)).2 described)
  | _, .possibly label inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x,
      coreX, described => by
    have modalInner : inner.regionalWith classical = true := modal
    have labelled : memberLabel label := by
      obtain ⟨_, ⟨found, _⟩, _⟩ := holdsAt
      exact found
    have found : ∃ value ∈ membersOf term, decideOn region.terms inner decision value = true := by
      obtain ⟨next, ⟨_, member⟩, holdsNext⟩ := holdsAt
      obtain ⟨value, valueMember, rfl⟩ := (mem_zfOf_iff holds).mp member
      exact ⟨value, valueMember, (decideOn_iff_regional region inner (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) agree value (hf_members holds value valueMember)
        (region.closed _ inside _ member)).mpr holdsNext⟩
    let index := (chooseIndex (membersOf term) (decideOn region.terms inner decision) found).1
    have memberHolds := hf_members holds _ (List.get_mem (membersOf term) index)
    have memberInside := region.closed _ inside _ (zfOf_member_index holds index)
    have holdsThere : extensional.sat sets inner (zfOf ((membersOf term).get index)) :=
      (decideOn_iff_regional region inner (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) agree _ memberHolds memberInside).mp
        (chooseIndex (membersOf term) (decideOn region.terms inner decision) found).2
    refine someMemberHyps described index ?_
    rw [weaken_nativeFormula_regional _ (Formula.regional_of_regionalWith _ modal)]
    rw [show nativeFormula (.possibly label inner) (weaken x) (fun index => weaken (env index)) =
      existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken (weaken x)))
        (nativeFormula inner (.var .vz) (underElement fun index => weaken (env index)))) by
      simp only [nativeFormula, if_pos labelled]]
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_possiblyBody (Formula.regional_of_regionalWith _ modalInner) _ _ _).symm
      (conjunctionIntro (Proof.prepend _ (Proof.newest _)) ?_))
    exact proveNative region parts classical inner modalInner ((((laws.lift setTy).prepend _).prepend _).prepend _)
      (fun index => weaken (env index)) sets decision agree ((((know.lift setTy).prepend _).prepend _).prepend _) _
      memberHolds memberInside holdsThere (.var .vz) rfl
      (describesSomeOfTerm (((((laws.lift setTy).prepend _).prepend _).prepend _)).toHasLaws memberHolds (Proof.newest _))
  | _, .necessarily label inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x,
      coreX, described => by
    have modalInner : inner.regionalWith classical = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.necessarily label inner) x env = .all (σ := setTy) (.imp (member (.var .vz) (weaken x))
        (nativeFormula inner (.var .vz) (underElement env))) by simp only [nativeFormula, if_pos labelled]]
      refine .allI (.impI ?_)
      refine oneCases (membersOf term) (describesSome_forward (describesSomeUnder described setTy _)
        (Proof.newest _)) fun index => ?_
      exact proveNative region parts classical inner modalInner ((laws.lift setTy).prepend _ |>.prepend _) (underElement env) sets
        decision agree ((know.lift setTy).prepend _ |>.prepend _) _ (hf_members holds _ (List.get_mem _ _))
        (region.closed _ inside _ (zfOf_member_index holds index))
        (holdsAt _ ⟨labelled, zfOf_member_index holds index⟩) (.var .vz) rfl
        (describesSomeOfTerm (((laws.lift setTy).prepend _ |>.prepend _)).toHasLaws (hf_members holds _ (List.get_mem _ _))
          (Proof.newest _))
    · rw [show nativeFormula (.necessarily label inner) x env = truth by simp only [nativeFormula, if_neg labelled]]
      exact truthIntro
  | _, .is name, _, _, _, _, _, _, _, _, _, term, holds, _, holdsAt, x, coreX, described => by
    rw [show nativeFormula (.is name) x _ = describesSomeOf name x by
      simp only [nativeFormula, if_pos ((hereditary_iff _).mpr holdsAt.1)], describesSomeOf_set holdsAt.1]
    exact describesSomeSame holds holdsAt.1 holdsAt.2 described
  | _, .isNot name, _, _, _, laws, _, _, _, _, _, term, holds, _, holdsAt, x, coreX, described => by
    refine if named : hereditary membership hfRule.category name = true then ?_ else ?_
    · rw [show nativeFormula (.isNot name) x _ = negCore (describesSomeOf name x) by
        simp only [nativeFormula, if_pos named], describesSomeOf_set ((hereditary_iff _).mp named)]
      exact .impI (describesSomeDistinct ((laws.prepend _)).toHasLaws holds ((hereditary_iff _).mp named)
        (fun same => holdsAt ⟨(hereditary_iff _).mp named, same⟩) (described.prepend _) (Proof.newest _))
    · rw [show nativeFormula (.isNot name) x _ = truth by simp only [nativeFormula, if_neg named]]
      exact truthIntro
  | _, .empty kind, _, _, _, _, _, _, _, _, _, term, holds, _, holdsAt, x, coreX, described => by
    rw [show nativeFormula (.empty kind) x _ = .all (negCore (member (.var .vz) (weaken x))) by
      simp only [nativeFormula, if_pos holdsAt.1]]
    refine .allI (.impI ?_)
    refine oneCases (membersOf term) (describesSome_forward (describesSomeUnder described setTy _)
      (Proof.newest _)) fun index => ?_
    exact Fin.elim0 (index.cast (by rw [members_nil_of_empty holds holdsAt.2]; rfl))
  | _, .nonEmpty kind, _, _, _, laws, _, _, _, _, _, term, holds, _, holdsAt, x, coreX, described => by
    refine if set : kind = .hashSet then ?_ else ?_
    · rw [show nativeFormula (.nonEmpty kind) x _ = negCore (.all (negCore (member (.var .vz) (weaken x)))) by
        simp only [nativeFormula, if_pos set]]
      have nonempty : zfOf term ≠ ∅ := fun isEmpty => holdsAt ⟨set, isEmpty⟩
      refine .impI (someMemberHyps (Proof.prepend _ described) (firstIndex holds nonempty) ?_)
      exact .impE (Proof.atNewest (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
        ((Proof.newest _).lift (σ := setTy)))))) (Proof.prepend _ (Proof.newest _))
    · rw [show nativeFormula (.nonEmpty kind) x _ = truth by simp only [nativeFormula, if_neg set]]
      exact truthIntro
  | _, .typed type, _, _, _, _, _, _, _, _, _, term, holds, _, holdsAt, x, coreX, described =>
    proveTypedSome type term holds holdsAt x described
  | _, .untyped type, _, _, _, laws, _, _, _, _, _, term, holds, _, holdsAt, x, coreX, described =>
    refuteTypedSome type laws term holds holdsAt x described
  | _, .atLeast count .forward label inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside,
      holdsAt, x, coreX, described => by
    have modalInner : inner.regionalWith classical = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.atLeast count .forward label inner) x env =
        countWith (fun {_} y env => nativeFormula inner y env) count x env by simp only [nativeFormula, if_pos labelled]]
      have counted : countDecide (decideOn region.terms inner decision) count (membersOf term) = true := by
        have accepted := (decideOn_iff_regional region (.atLeast count .forward label inner) (Formula.regional_of_regionalWith _ modal) (Or.inr parts) agree term holds inside).mpr
          holdsAt
        rwa [decideOn, if_pos labelled] at accepted
      exact proveCount region (point := fun {_} y env => nativeFormula inner y env)
        (fun θ y env => subst_nativeFormula_regional θ inner (Formula.regional_of_regionalWith _ modalInner) y env)
        (fun {_} Δ env => PosKnowledge Δ env sets region.sets) (fun know ψ => know.prepend ψ)
        (fun know => know.lift setTy) (decideOn region.terms inner decision)
        (fun laws' env' know' value valueHolds valueInside accepted y coreY describedY =>
          proveNative region parts classical inner modalInner laws' env' sets decision agree know' value valueHolds valueInside
            ((decideOn_iff_regional region inner (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) agree value valueHolds valueInside).mp accepted) y coreY
            (describesSomeOfTerm (laws').toHasLaws valueHolds describedY))
        count laws env know (membersOf term) (hf_members holds)
        (fun value member => region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩)) counted x
        described
    · rw [show nativeFormula (.atLeast count .forward label inner) x env = if count = 0 then truth else falsity by
        simp only [nativeFormula, if_neg labelled]]
      rw [if_pos ((atLeast_unlabelled labelled (zfOf term) _).mp holdsAt)]
      exact truthIntro
  | _, .allButFewer count .forward label inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds,
      inside, holdsAt, x, coreX, described => by
    have modalInner : inner.regionalWith classical = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.allButFewer count .forward label inner) x env =
        negCore (countWith (fun {_} y env => negCore (nativeFormula inner y env)) count x env) by
        simp only [nativeFormula, if_pos labelled]]
      have refused : countDecide (fun value => !decideOn region.terms inner decision value) count (membersOf term) =
          false := by
        have accepted := (decideOn_iff_regional region (.allButFewer count .forward label inner) (Formula.regional_of_regionalWith _ modal) (Or.inr parts) agree term holds
          inside).mpr holdsAt
        rw [decideOn, if_pos labelled, Bool.not_eq_true'] at accepted
        exact accepted
      exact refuteCount region (point := fun {_} y env => negCore (nativeFormula inner y env))
        (fun θ y env => by rw [subst_negCore, subst_nativeFormula_regional θ inner (Formula.regional_of_regionalWith _ modalInner) y env])
        (fun {_} Δ env => PosKnowledge Δ env sets region.sets) (fun know ψ => know.prepend ψ)
        (fun know => know.lift setTy) (fun value => !decideOn region.terms inner decision value)
        (fun laws' env' know' value valueHolds valueInside rejected y coreY describedY =>
          .impI (.impE (Proof.newest _) (proveNative region parts classical inner modalInner (laws'.prepend _) env' sets decision agree
            (know'.prepend _) value valueHolds valueInside
            ((decideOn_iff_regional region inner (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) agree value valueHolds valueInside).mp (by simpa using rejected)) y
            coreY (describesSomeOfTerm ((laws'.prepend _)).toHasLaws valueHolds (Proof.prepend _ describedY)))))
        count laws env know (membersOf term) (hf_members holds)
        (fun value member => region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩)) refused x
        described
    · rw [show nativeFormula (.allButFewer count .forward label inner) x env = if count = 0 then falsity else truth by
        simp only [nativeFormula, if_neg labelled]]
      rw [if_neg fun zero => holdsAt ((atLeast_unlabelled labelled (zfOf term) _).mpr zero)]
      exact truthIntro
  | _, .single kind inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x, coreX,
      described => by
    have modalInner : inner.regionalWith classical = true := modal
    have set : kind = .hashSet := by
      obtain ⟨_, ⟨found, _⟩, _⟩ := holdsAt
      exact found
    have nonempty : zfOf term ≠ ∅ := by
      obtain ⟨element, ⟨_, single⟩, _⟩ := holdsAt
      intro isEmpty
      rw [single] at isEmpty
      exact ZFSet.notMem_empty element (isEmpty ▸ ZFSet.mem_singleton.mpr rfl)
    let first := firstIndex holds nonempty
    have firstHolds := hf_members holds _ (List.get_mem (membersOf term) first)
    have firstInside := region.closed _ inside _ (zfOf_member_index holds first)
    have allSame : ∀ index : Fin (membersOf term).length,
        zfOf ((membersOf term).get index) = zfOf ((membersOf term).get first) := by
      obtain ⟨element, ⟨_, single⟩, _⟩ := holdsAt
      intro index
      rw [((zfOf_eq_singleton_iff holds).mp single).2 _ (List.get_mem _ index),
        ((zfOf_eq_singleton_iff holds).mp single).2 _ (List.get_mem _ first)]
    have holdsFirst : extensional.sat sets inner (zfOf ((membersOf term).get first)) := by
      obtain ⟨element, ⟨_, single⟩, holdsElement⟩ := holdsAt
      rwa [((zfOf_eq_singleton_iff holds).mp single).2 _ (List.get_mem _ first)]
    refine someMemberHyps described first ?_
    rw [weaken_nativeFormula_regional _ (Formula.regional_of_regionalWith _ modal)]
    rw [show nativeFormula (.single kind inner) (weaken x) (fun index => weaken (env index)) =
      existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken (weaken x)))
        (conjunctionFormula (nativeFormula inner (.var .vz) (underElement fun index => weaken (env index)))
          (onlyMember (weaken (weaken x)) (.var .vz)))) by simp only [nativeFormula, if_pos set]]
    refine existentialIntro (.var .vz) (Proof.cast (instantiate_singleBody (Formula.regional_of_regionalWith _ modalInner) _ _ _).symm
      (conjunctionIntro (Proof.prepend _ (Proof.newest _)) (conjunctionIntro ?_ ?_)))
    · exact proveNative region parts classical inner modalInner ((((laws.lift setTy).prepend _).prepend _).prepend _)
        (fun index => weaken (env index)) sets decision agree ((((know.lift setTy).prepend _).prepend _).prepend _) _
        firstHolds firstInside holdsFirst (.var .vz) rfl
        (describesSomeOfTerm (((((laws.lift setTy).prepend _).prepend _).prepend _)).toHasLaws firstHolds (Proof.newest _))
    · exact onlyProof holds firstHolds allSame (Proof.prepend _ (Proof.prepend _ (describesSomeUnder described setTy _)))
        (Proof.newest _)
  | _, .everySingle kind inner, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x,
      coreX, described => by
    have modalInner : inner.regionalWith classical = true := modal
    refine if set : kind = .hashSet then ?_ else ?_
    · rw [show nativeFormula (.everySingle kind inner) x env = .all (σ := setTy) (.imp (member (.var .vz) (weaken x))
        (.imp (onlyMember (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) (underElement env)))) by
        simp only [nativeFormula, if_pos set]]
      refine .allI (.impI (.impI ?_))
      have describedX := (describesSomeUnder described setTy (member (.var .vz) (weaken x))).prepend
        (onlyMember (weaken x) (.var .vz))
      refine oneCases (membersOf term) (describesSome_forward describedX ((Proof.newest _).prepend _))
        fun index => ?_
      have indexHolds := hf_members holds _ (List.get_mem (membersOf term) index)
      have indexInside := region.closed _ inside _ (zfOf_member_index holds index)
      refine if good : decideOn region.terms inner decision ((membersOf term).get index) = true then ?_ else ?_
      · exact proveNative region parts classical inner modalInner ((((laws.lift setTy).prepend _).prepend _).prepend _) (underElement env)
          sets decision agree ((((know.lift setTy).prepend _).prepend _).prepend _) _ indexHolds indexInside
          ((decideOn_iff_regional region inner (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) agree _ indexHolds indexInside).mp good) (.var .vz) rfl
          (describesSomeOfTerm (((((laws.lift setTy).prepend _).prepend _).prepend _)).toHasLaws indexHolds (Proof.newest _))
      · have other : ∃ value ∈ membersOf term, (!sameSet ((membersOf term).get index) value) = true := by
          by_contra none
          apply good
          refine (decideOn_iff_regional region inner (Formula.regional_of_regionalWith _ modalInner) (Or.inr parts) agree _ indexHolds indexInside).mpr (holdsAt _ ⟨set,
            (zfOf_eq_singleton_iff holds).mpr ⟨⟨_, List.get_mem _ index, rfl⟩, fun value member => ?_⟩⟩)
          cases same : sameSet ((membersOf term).get index) value
          · exact absurd ⟨value, member, by rw [same]; rfl⟩ none
          · exact ((sameSet_iff _ indexHolds value (hf_members holds value member)).mp same).symm
        let otherIndex := (chooseIndex (membersOf term) (fun value => !sameSet ((membersOf term).get index) value) other).1
        have otherHolds := hf_members holds _ (List.get_mem (membersOf term) otherIndex)
        have differ : zfOf ((membersOf term).get index) ≠ zfOf ((membersOf term).get otherIndex) := fun same => by
          have apart : (!sameSet ((membersOf term).get index) ((membersOf term).get otherIndex)) = true :=
            (chooseIndex (membersOf term) (fun value => !sameSet ((membersOf term).get index) value) other).2
          rw [(sameSet_iff _ indexHolds _ otherHolds).mpr same] at apart
          simp at apart
        have laws' : HasLaws (describes ((membersOf term).get index) (.var .vz) :: onlyMember (weaken x) (.var .vz) ::
            member (.var .vz) (weaken x) :: weakenHyps (σ := setTy) Δ) :=
          ((((laws.lift setTy).prepend _).prepend _).prepend _).toHasLaws
        have only2 : Proof (describes ((membersOf term).get index) (.var .vz) :: onlyMember (weaken x) (.var .vz) ::
            member (.var .vz) (weaken x) :: weakenHyps (σ := setTy) Δ) (onlyMember (weaken x) (.var .vz)) :=
          Proof.prepend _ (Proof.newest _)
        have index2 : Proof (describes ((membersOf term).get index) (.var .vz) :: onlyMember (weaken x) (.var .vz) ::
            member (.var .vz) (weaken x) :: weakenHyps (σ := setTy) Δ) (describes ((membersOf term).get index) (.var .vz)) :=
          Proof.newest _
        refine someMemberHyps (Proof.prepend (describes ((membersOf term).get index) (.var .vz)) describedX) otherIndex ?_
        exact Proof.absurd (describesDistinct ((((laws'.lift setTy).prepend _).prepend _).prepend _)
          ((membersOf term).get index) ((membersOf term).get otherIndex) indexHolds otherHolds differ _
          (Proof.prepend _ (Proof.prepend _ (Proof.prepend _ (Proof.cast (weaken_describes _ _) index2.lift))))
          (describesAlong otherHolds (Proof.newest _) (onlyAt (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
            (Proof.cast (weaken_onlyMember _ _) only2.lift)))) (.var .vz) (Proof.prepend _ (Proof.newest _)))))
    · rw [show nativeFormula (.everySingle kind inner) x env = truth by simp only [nativeFormula, if_neg set]]
      exact truthIntro
  | _, .split kind left right, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside, holdsAt, x,
      coreX, described => by
    simp only [Formula.regionalWith, Bool.and_eq_true] at modal
    have isSet : kind = .hashSet := by
      obtain ⟨_, _, ⟨isSet, _⟩, _⟩ := holdsAt
      exact isSet
    subst isSet
    have found : ∃ cover ∈ coverings (membersOf term), (decideOn region.terms left decision (set cover.1) &&
        decideOn region.terms right decision (set cover.2)) = true := by
      obtain ⟨first, second, ⟨-, union⟩, holdsLeft, holdsRight⟩ := holdsAt
      obtain ⟨cover, member, firstEq, secondEq⟩ := split_covering holds union
      obtain ⟨leftHolds, rightHolds, coverUnion⟩ := covering_split holds member
      refine ⟨cover, member, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
      · exact (decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1) (Or.inr parts) agree _
          leftHolds (parts _ inside _ (part_left coverUnion))).mpr (firstEq ▸ holdsLeft)
      · exact (decideOn_iff_regional region right (Formula.regional_of_regionalWith _ modal.2) (Or.inr parts) agree _
          rightHolds (parts _ inside _ (part_right coverUnion))).mpr (secondEq ▸ holdsRight)
    let chosen := chooseIndex (coverings (membersOf term)) (fun cover => decideOn region.terms left decision
      (set cover.1) && decideOn region.terms right decision (set cover.2)) found
    have member : (coverings (membersOf term)).get chosen.1 ∈ coverings (membersOf term) := List.get_mem _ _
    have accepted := Bool.and_eq_true_iff.mp chosen.2
    have coverHolds := covering_split holds member
    have coverParts := mem_coverings_parts member
    exact splitIntro (Formula.regional_of_regionalWith _ modal.1) (Formula.regional_of_regionalWith _ modal.2) _ _
      (partsSplit laws described _ _ coverParts.2.2)
      (proveNative region parts classical left modal.1 laws env sets decision agree know _ coverHolds.1
        (parts _ inside _ (part_left coverHolds.2.2))
        ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1) (Or.inr parts) agree _
          coverHolds.1 (parts _ inside _ (part_left coverHolds.2.2))).mp accepted.1)
        _ (isCore_partTerm coreX _) (partDescribed laws described _ coverParts.1))
      (proveNative region parts classical right modal.2 laws env sets decision agree know _ coverHolds.2.1
        (parts _ inside _ (part_right coverHolds.2.2))
        ((decideOn_iff_regional region right (Formula.regional_of_regionalWith _ modal.2) (Or.inr parts) agree _
          coverHolds.2.1 (parts _ inside _ (part_right coverHolds.2.2))).mp accepted.2)
        _ (isCore_partTerm coreX _) (partDescribed laws described _ coverParts.2.1))
  | _, .everySplit kind left right, modal, Γ, Δ, laws, env, sets, decision, agree, know, term, holds, inside,
      holdsAt, x, coreX, described => by
    simp only [Formula.regionalWith, Bool.and_eq_true] at modal
    refine if isSet : kind = .hashSet then ?_ else ?_
    · subst isSet
      let body : Term Symbol (setTy :: setTy :: Γ) .prop := .imp (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (disjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))
      change Proof Δ (.all (σ := setTy) (.all (σ := setTy) body))
      refine .allI (.allI (.impI ?_))
      let Δ3 : List (Term Symbol (setTy :: setTy :: Γ) .prop) :=
        splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz) :: weakenHyps (σ := setTy) (weakenHyps (σ := setTy) Δ)
      have laws3 : Laws classical Δ3 := ((laws.lift setTy).lift setTy).prepend _
      have know3 : PosKnowledge Δ3 (underElement (underElement env)) sets region.sets :=
        ((know.lift setTy).lift setTy).prepend _
      have described3 : Proof Δ3 (describesSome (membersOf term) (weaken (weaken x))) :=
        Proof.prepend _ (Proof.cast (weaken_describesSome _ _) (Proof.cast (weaken_describesSome _ _) described.lift).lift)
      refine if classic : classical = true then ?_ else ?_
      swap
      · have shapes : left.upwardShape = true ∧ right.upwardShape = true := by
          have choice := modal.1.1
          simp only [Bool.or_eq_true, Bool.and_eq_true] at choice
          exact choice.resolve_left classic
        refine branchSplits (Δ₀ := Δ3) (membersOf term) ?_ [] (membersOf term) [] [] (fun _ found => Or.inl found)
          (fun _ found => found) (fun _ found => absurd found List.not_mem_nil)
          (fun _ found => absurd found List.not_mem_nil) (Proof.newest _) (conjunctionRight described3) truthIntro
          truthIntro
        intro extra first second covered inFirst inSecond knownFirst knownSecond
        have union := zfOf_eq_union_of_cover holds inFirst inSecond covered
        have firstHolds : IsHF (set first) := .members fun value found => hf_members holds value (inFirst value found)
        have secondHolds : IsHF (set second) :=
          .members fun value found => hf_members holds value (inSecond value found)
        have firstInside := parts _ inside _ (part_left union)
        have secondInside := parts _ inside _ (part_right union)
        have lawsHere : Laws classical (extra ++ Δ3) := Laws.prependAll extra laws3
        have knowHere := PosKnowledge.prependAll extra know3
        refine if leftGood : decideOn region.terms left decision (set first) = true then ?_ else ?_
        · have atPart := proveNative region parts classical left modal.1.2 lawsHere (underElement (underElement env))
            sets decision agree knowHere (set first) firstHolds firstInside
            ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1.2) (Or.inr parts) agree _
              firstHolds firstInside).mp leftGood) (partTerm (.var (.vs .vz)) first) (isCore_partTerm rfl first)
            (partDescribedOfEach lawsHere.toHasLaws knownFirst)
          exact disjunctionLeft (upwardMono left shapes.1
            (Formula.regional_of_regionalWith _ modal.1.2) _ (partSubset lawsHere.toHasLaws _ first) atPart)
        · have holdsRight : extensional.sat sets right (zfOf (set second)) :=
            (holdsAt _ _ ⟨rfl, union⟩).resolve_left fun holdsLeft => leftGood
              ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1.2) (Or.inr parts) agree _
                firstHolds firstInside).mpr holdsLeft)
          have atPart := proveNative region parts classical right modal.2 lawsHere (underElement (underElement env))
            sets decision agree knowHere (set second) secondHolds secondInside holdsRight (partTerm (.var .vz) second)
            (isCore_partTerm rfl second) (partDescribedOfEach lawsHere.toHasLaws knownSecond)
          exact disjunctionRight (upwardMono right shapes.2
            (Formula.regional_of_regionalWith _ modal.2) _ (partSubset lawsHere.toHasLaws _ second) atPart)
      refine coverBranches described3 (Proof.newest _)
        (fun extra P yes no => disjunctionElim ((Laws.prependAll extra laws3).excludedMiddle classic P) yes no) ?_
        (membersOf term) [] [] [] (fun _ found => found) (fun _ found => absurd found List.not_mem_nil)
        (fun _ found => absurd found List.not_mem_nil) (fun _ found => Or.inr (Or.inr found))
        (upperOfLeft described3 (Proof.newest _)) truthIntro (upperOfRight described3 (Proof.newest _)) truthIntro
      intro extra chosenLeft chosenRight inLeft inRight covered describedA describedB
      have union := zfOf_eq_union_of_cover holds inLeft inRight covered
      have leftHolds : IsHF (set chosenLeft) := .members fun value found => hf_members holds value (inLeft value found)
      have rightHolds : IsHF (set chosenRight) := .members fun value found => hf_members holds value (inRight value found)
      have leftInside := parts _ inside _ (part_left union)
      have rightInside := parts _ inside _ (part_right union)
      refine if leftGood : decideOn region.terms left decision (set chosenLeft) = true then ?_ else ?_
      · exact disjunctionLeft (proveNative region parts classical left modal.1.2 (Laws.prependAll extra laws3)
          (underElement (underElement env)) sets decision agree (PosKnowledge.prependAll extra know3) (set chosenLeft)
          leftHolds leftInside ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1.2)
            (Or.inr parts) agree _ leftHolds leftInside).mp leftGood) (.var (.vs .vz)) rfl describedA)
      · have holdsRight : extensional.sat sets right (zfOf (set chosenRight)) :=
          (holdsAt _ _ ⟨rfl, union⟩).resolve_left fun holdsLeft => leftGood
            ((decideOn_iff_regional region left (Formula.regional_of_regionalWith _ modal.1.2) (Or.inr parts) agree _
              leftHolds leftInside).mpr holdsLeft)
        exact disjunctionRight (proveNative region parts classical right modal.2 (Laws.prependAll extra laws3)
          (underElement (underElement env)) sets decision agree (PosKnowledge.prependAll extra know3) (set chosenRight)
          rightHolds rightInside holdsRight (.var .vz) rfl describedB)
    · rw [show nativeFormula (.everySplit kind left right) x env = truth by simp only [nativeFormula, if_neg isSet]]
      exact truthIntro
  | _, .sometimeBefore _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .alwaysBefore _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .atLeast _ .backward _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .allButFewer _ .backward _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .built _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBuilt _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .body _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBody _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .multiBody _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyMultiBody _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .bound _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .notBound _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsAll _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsSome _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .someOf _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyOf _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd modal Bool.false_ne_true

/-! ## Refuting the native types that fail -/

section RefusalInstances

variable {Γ : Ctx Unit}

/-- A predicate that fails at what the listed terms describe. -/
def refusalOf (terms : List Pattern) {Γ : Ctx Unit} : Term Symbol Γ predTy :=
  .lam (negCore (someOne terms (.var .vz)))

theorem weaken_refusalOf {σ : Ty Unit} (terms : List Pattern) :
    weaken (σ := σ) (refusalOf terms (Γ := Γ)) = refusalOf terms := by
  change Term.lam (.imp (rename (Rename.lift Rename.weaken) (someOne terms (.var .vz))) falsity) = _
  rw [rename_eq_subst, subst_someOne]
  rfl

theorem isCore_refusalBody (terms : List Pattern) :
    (negCore (someOne terms (.var .vz : Term Symbol (setTy :: Γ) setTy))).isCore = true := by
  simp only [negCore, Mettapedia.Logic.HOL.Term.isCore,
    isCore_someOne terms (y := (.var .vz : Term Symbol (setTy :: Γ) setTy)) rfl, isCore_falsity,
    Bool.and_true]

theorem instantiate_refusalBody (terms : List Pattern) (y : Term Symbol Γ setTy) :
    instantiate y (negCore (someOne terms (.var .vz))) = negCore (someOne terms y) := by
  change Term.imp (instantiate y (someOne terms (.var .vz))) falsity = _
  rw [instantiate_someOne]
  rfl

theorem instantiate_muBody {n : ℕ} {inner : Formula (n + 1)} (modal : inner.regional = true) (predicate : Term Symbol Γ predTy)
    (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    instantiate predicate (.imp (closureHyp inner env) (.app (.var .vz) (weaken x))) =
      .imp (.all (σ := setTy) (.imp (nativeFormula inner (.var .vz) (Fin.cons (weaken predicate) (underElement env)))
        (.app (weaken predicate) (.var .vz)))) (.app predicate x) := by
  change Term.imp (.all (.imp (subst (Subst.lift (Subst.single predicate)) (nativeFormula inner (.var .vz) (underFixedPoint env)))
    (.app (weaken predicate) (.var .vz)))) (.app predicate (instantiate predicate (weaken x))) = _
  rw [subst_nativeFormula_regional _ inner modal, Mettapedia.Logic.HOL.instantiate_weaken]
  congr 4
  funext index
  refine Fin.cases rfl (fun index => ?_) index
  change subst (Subst.lift (Subst.single predicate)) (weaken (weaken (env index))) = weaken (env index)
  rw [Mettapedia.Logic.HOL.subst_weaken, ← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

end RefusalInstances

/-- The invariance hypothesis of a greatest fixed point. -/
def invariantHyp {n : ℕ} (inner : Formula (n + 1)) {Γ : Ctx Unit} (env : Fin n → Term Symbol Γ predTy) :
    Term Symbol (predTy :: Γ) .prop :=
  .all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz)) (nativeFormula inner (.var .vz) (underFixedPoint env)))

/-- A refuter for a formula, in every context. -/
abbrev Refuter (region : Region) {n : ℕ} (formula : Formula n) : Type 1 :=
  ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ → ∀ (env : Fin n → Term Symbol Γ predTy)
    (sets : Env ZFSet.{0} n) (decision : Fin n → Pattern → Bool), Agrees region decision sets →
      NegKnowledge Δ env sets region.sets → ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
        ¬ extensional.sat sets formula (zfOf term) → ∀ x : Term Symbol Γ setTy, x.isCore = true →
          Proof Δ (describesSome (membersOf term) x) → Proof Δ (negCore (nativeFormula formula x env))

/-- **The stages of a greatest fixed point from above, as negative knowledge about an invariant predicate.** -/
def gfpRefusal (region : Region) (parts : PartsClosed region.sets) {n : ℕ}
    {inner : Formula (n + 1)} (modal : inner.regional = true)
    (refuteInner : Refuter region inner) {Γ : Ctx Unit} (env : Fin n → Term Symbol Γ predTy)
    (sets : Env ZFSet.{0} n) (decision : Fin n → Pattern → Bool) (agree : Agrees region decision sets)
    {Δ : List (Term Symbol (predTy :: Γ) .prop)} (laws : HasLaws Δ)
    (refuse : NegKnowledge Δ (fun index => weaken (env index)) sets region.sets)
    (invariant : Proof Δ (invariantHyp inner env)) :
    ∀ (k : ℕ) (term : Pattern), IsHF term → zfOf term ∈ region.sets → zfOf term ∉ gfpStage sets inner region.sets k →
      Proof Δ (refusesAt (.var .vz) term)
  | 0, _, _, inside, missing => False.elim (missing inside)
  | k + 1, term, holds, inside, missing => by
    have fails : ¬ extensional.sat (sets.extend (gfpStage sets inner region.sets k)) inner (zfOf term) :=
      fun holdsAt => missing ⟨inside, holdsAt⟩
    refine .allI (.impI (.impI ?_))
    have preserved : Proof (.app (.var (.vs .vz)) (.var .vz) :: describesSome (membersOf term) (.var .vz) ::
        weakenHyps (σ := setTy) Δ)
        (.imp (.app (.var (.vs .vz)) (.var .vz)) (nativeFormula inner (.var .vz) (underFixedPoint env))) :=
      Proof.atNewest ((invariant.lift (σ := setTy)).prepend _ |>.prepend _)
    refine .impE (refuteInner (((laws.lift setTy).prepend _).prepend _) (underFixedPoint env)
      (sets.extend (gfpStage sets inner region.sets k)) (Fin.cons (gfpDecision region inner decision k) decision)
      (agree.extend (gfpDecision_agrees region modal parts agree k)) (fun index => ?_) term holds inside fails (.var .vz) rfl
      ((Proof.newest _).prepend _)) (.impE preserved (Proof.newest _))
    refine Fin.cases (motive := fun index => ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets →
      zfOf other ∉ (sets.extend (gfpStage sets inner region.sets k)) index →
        Proof (.app (.var (.vs .vz)) (.var .vz) :: describesSome (membersOf term) (.var .vz) ::
          weakenHyps (σ := setTy) Δ) (refusesAt (underFixedPoint env index) other)) ?_ (fun index => ?_) index
    · intro other otherHolds otherInside otherMissing
      exact ((Proof.cast (weaken_refusesAt _ _) (gfpRefusal region parts modal refuteInner env sets decision agree laws refuse
        invariant k other otherHolds otherInside otherMissing).lift).prepend _).prepend _
    · exact ((refuse.lift setTy).prepend _ |>.prepend _) index

/-- **A proof that a modal native type fails**, at the set a hereditary term describes, whenever it fails. Branches
and witnesses are chosen by deciding the type on the region (`decideOn`). -/
def refuteNative (region : Region) (parts : PartsClosed region.sets) :
    ∀ {n : ℕ} (formula : Formula n), formula.regional = true →
    ∀ {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}, HasLaws Δ → ∀ (env : Fin n → Term Symbol Γ predTy)
      (sets : Env ZFSet.{0} n) (decision : Fin n → Pattern → Bool), Agrees region decision sets →
        NegKnowledge Δ env sets region.sets → ∀ term : Pattern, IsHF term → zfOf term ∈ region.sets →
          ¬ extensional.sat sets formula (zfOf term) → ∀ x : Term Symbol Γ setTy, x.isCore = true →
            Proof Δ (describesSome (membersOf term) x) → Proof Δ (negCore (nativeFormula formula x env))
  | _, .top, _, _, _, _, _, _, _, _, _, _, _, _, fails, _, _, _ => False.elim (fails trivial)
  | _, .bot, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => .impI (Proof.newest _)
  | _, .and left right, modal, _, _, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x, coreX,
      described => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    refine if first : decideOn region.terms left decision term = true then ?_ else ?_
    · exact .impI (.impE ((refuteNative region parts right modal.2 laws env sets decision agree refuse term holds inside
        (fun second => fails ⟨(decideOn_iff_regional region left modal.1 (Or.inr parts) agree term holds inside).mp first, second⟩) x coreX
        described).prepend _) (conjunctionRight (Proof.newest _)))
    · exact .impI (.impE ((refuteNative region parts left modal.1 laws env sets decision agree refuse term holds inside
        (fun holdsLeft => first ((decideOn_iff_regional region left modal.1 (Or.inr parts) agree term holds inside).mpr holdsLeft)) x coreX
        described).prepend _) (conjunctionLeft (Proof.newest _)))
  | _, .or left right, modal, _, _, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x, coreX,
      described => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    exact .impI (disjunctionElim (Proof.newest _)
      (.impE (((refuteNative region parts left modal.1 laws env sets decision agree refuse term holds inside
        (fun h => fails (Or.inl h)) x coreX described).prepend _).prepend _) (Proof.newest _))
      (.impE (((refuteNative region parts right modal.2 laws env sets decision agree refuse term holds inside
        (fun h => fails (Or.inr h)) x coreX described).prepend _).prepend _) (Proof.newest _)))
  | _, .var index, _, _, _, _, _, _, _, _, refuse, term, holds, inside, fails, _, _, described =>
    useRefuses (refuse index term holds inside fails) described
  | _, .mu inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x, coreX,
      described => by
    have modalInner : inner.regional = true := modal
    let stable := lfpStage sets inner region.sets region.terms.length
    have stableIff : ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets →
        (decideOn region.terms (.mu inner) decision other = true ↔ zfOf other ∈ stable) :=
      fun other otherHolds otherInside => (decideOn_iff_regional region (.mu inner) modal (Or.inr parts) agree other otherHolds otherInside).trans
        (sat_mu_iff_regional sets modalInner (Or.inr parts) region.finite region.closed region.ncard_le otherInside)
    have missing : zfOf term ∉ stable := fun member =>
      fails ((sat_mu_iff_regional sets modalInner (Or.inr parts) region.finite region.closed region.ncard_le inside).mpr member)
    let outside := region.terms.filter fun other => !decideOn region.terms (.mu inner) decision other
    have outsideHereditary : ∀ value ∈ outside, IsHF value :=
      fun value inOutside => region.hereditary _ (List.mem_filter.mp inOutside).1
    have outsideFound : ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets → zfOf other ∉ stable →
        ∃ value ∈ outside, zfOf value = zfOf other := by
      intro other otherHolds otherInside otherMissing
      obtain ⟨value, valueIn, same⟩ := region.covers _ otherInside
      refine ⟨value, List.mem_filter.mpr ⟨valueIn, ?_⟩, same⟩
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact fun accepted => otherMissing (same ▸ (stableIff value (region.hereditary _ valueIn)
        (region.inside _ valueIn)).mp accepted)
    have outsideIntro : ∀ {Γ' : Ctx Unit} {Δ' : List (Term Symbol Γ' .prop)} (other : Pattern), IsHF other →
        zfOf other ∈ region.sets → zfOf other ∉ stable → ∀ y : Term Symbol Γ' setTy,
          Proof Δ' (describesSome (membersOf other) y) → Proof Δ' (someOne outside y) := by
      intro Γ' Δ' other otherHolds otherInside otherMissing y describedOther
      exact someOneIntro outside (presenterIndex outside outsideHereditary otherHolds
          (outsideFound other otherHolds otherInside otherMissing)).1
        (describesSomeSame otherHolds (outsideHereditary _ (List.get_mem _ _))
          (presenterIndex outside outsideHereditary otherHolds (outsideFound other otherHolds otherInside otherMissing)).2
          describedOther)
    have refusalKnows : ∀ {Γ' : Ctx Unit} {Δ' : List (Term Symbol Γ' .prop)} (other : Pattern), IsHF other →
        zfOf other ∈ region.sets → zfOf other ∉ stable → Proof Δ' (refusesAt (refusalOf outside) other) := by
      intro Γ' Δ' other otherHolds otherInside otherMissing
      refine .allI (.impI (.impI ?_))
      have applied := Proof.cast (congrArg (Term.app · (.var .vz)) (weaken_refusalOf (Γ := Γ') outside))
        (Proof.newest (Δ := describesSome (membersOf other) (.var .vz) :: weakenHyps (σ := setTy) Δ')
          (.app (weaken (refusalOf outside)) (.var .vz)))
      have unfolded := Proof.cast (instantiate_refusalBody outside (.var .vz))
        (Proof.betaReduce (isCore_refusalBody outside) rfl applied)
      exact .impE unfolded (outsideIntro other otherHolds otherInside otherMissing (.var .vz) ((Proof.newest _).prepend _))
    let hypothesis : Term Symbol Γ .prop := .all (σ := predTy) (.imp (closureHyp inner env) (.app (.var .vz) (weaken x)))
    change Proof Δ (negCore hypothesis)
    refine .impI ?_
    have instance' : Proof (hypothesis :: Δ) (.imp (.all (σ := setTy) (.imp (nativeFormula inner (.var .vz)
        (Fin.cons (weaken (refusalOf outside)) (underElement env))) (.app (weaken (refusalOf outside)) (.var .vz))))
        (.app (refusalOf outside) x)) :=
      Proof.cast (instantiate_muBody modalInner (refusalOf outside) x env) (.allE (refusalOf outside) (Proof.newest hypothesis))
    have closedness : Proof (hypothesis :: Δ)
        (.all (σ := setTy) (.imp (nativeFormula inner (.var .vz) (Fin.cons (weaken (refusalOf outside)) (underElement env)))
          (.app (weaken (refusalOf outside)) (.var .vz)))) := by
      refine .allI (.impI ?_)
      refine Proof.cast (congrArg (Term.app · (.var .vz)) (weaken_refusalOf outside).symm) ?_
      refine Proof.betaExpand (isCore_refusalBody outside) rfl
        (Proof.cast (instantiate_refusalBody outside (.var .vz)).symm (.impI ?_))
      refine someOneCases outside (Proof.newest _) fun index => ?_
      have inOutside := List.mem_filter.mp (List.get_mem outside index)
      have outsideHolds := region.hereditary _ inOutside.1
      have outsideInside := region.inside _ inOutside.1
      have outsideMissing : zfOf (outside.get index) ∉ stable := fun member => by
        have rejected : (!decideOn region.terms (.mu inner) decision (outside.get index)) = true := inOutside.2
        rw [(stableIff _ outsideHolds outsideInside).mpr member] at rejected
        simp at rejected
      have bodyFails : ¬ extensional.sat (sets.extend stable) inner (zfOf (outside.get index)) := fun holdsAt =>
        outsideMissing ((lfpStage_fixed sets inner region.sets region.finite region.ncard_le outsideInside).mpr holdsAt)
      refine .impE (refuteNative region parts inner modalInner ((((laws.prepend _).lift setTy).prepend _ |>.prepend _).prepend _)
        (Fin.cons (weaken (refusalOf outside)) (underElement env)) (sets.extend stable)
        (Fin.cons (decideOn region.terms (.mu inner) decision) decision) (agree.extend stableIff) (fun index' => ?_)
        (outside.get index) outsideHolds outsideInside bodyFails (.var .vz) rfl (Proof.newest _))
        (((Proof.newest _).prepend _).prepend _)
      refine Fin.cases (motive := fun index' => ∀ other : Pattern, IsHF other → zfOf other ∈ region.sets →
        zfOf other ∉ (sets.extend stable) index' → Proof _ (refusesAt ((Fin.cons (weaken (refusalOf outside))
          (underElement env) : Fin _ → Term Symbol (setTy :: Γ) predTy) index') other)) ?_ (fun index' => ?_) index'
      · intro other otherHolds otherInside otherMissing
        exact Proof.cast (congrArg (refusesAt · other) (weaken_refusalOf outside).symm)
          (refusalKnows other otherHolds otherInside otherMissing)
      · exact (((((refuse.prepend _).lift setTy).prepend _).prepend _).prepend _) index'
    have atTerm := Proof.cast (instantiate_refusalBody outside x)
      (Proof.betaReduce (isCore_refusalBody outside) coreX (.impE instance' closedness))
    exact .impE atTerm (outsideIntro term holds inside missing x (described.prepend _))
  | _, .nu inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x, coreX,
      described => by
    have modalInner : inner.regional = true := modal
    have missing : zfOf term ∉ gfpStage sets inner region.sets region.terms.length :=
      fun member => fails ((sat_nu_iff_regional sets modalInner (Or.inr parts) region.finite region.closed region.ncard_le inside).mpr member)
    change Proof Δ (negCore (existentialInline (σ := predTy) (conjunctionFormula (invariantHyp inner env)
      (.app (.var .vz) (weaken x)))))
    refine .impI (existentialElim (Proof.newest _) ?_)
    let hypotheses := conjunctionFormula (invariantHyp inner env) (.app (.var .vz) (weaken x)) ::
      weakenHyps (σ := predTy) (existentialInline (σ := predTy) (conjunctionFormula (invariantHyp inner env)
        (.app (.var .vz) (weaken x))) :: Δ)
    have refusal : Proof hypotheses (refusesAt (.var .vz) term) :=
      gfpRefusal region parts modalInner (fun laws' env' sets' decision' agree' refuse' => refuteNative region parts inner modalInner
        laws' env' sets' decision' agree' refuse') env sets decision agree (((laws.prepend _).lift predTy).prepend _)
        (((refuse.prepend _).lift predTy).prepend _) (conjunctionLeft (Proof.newest _)) _ term holds inside missing
    exact .impE (useRefuses refusal (describesSomeUnder (described.prepend _) predTy _)) (conjunctionRight (Proof.newest _))
  | _, .possibly label inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x, _,
      described => by
    have modalInner : inner.regional = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.possibly label inner) x env = existentialInline (σ := setTy) (conjunctionFormula
        (member (.var .vz) (weaken x)) (nativeFormula inner (.var .vz) (underElement env))) by
        simp only [nativeFormula, if_pos labelled]]
      refine .impI (existentialElim (Proof.newest _) ?_)
      refine oneCases (membersOf term) (describesSome_forward (describesSomeUnder (described.prepend _) setTy _)
        (conjunctionLeft (Proof.newest _))) fun index => ?_
      exact .impE (refuteNative region parts inner modalInner (((laws.prepend _).lift setTy).prepend _ |>.prepend _)
        (underElement env) sets decision agree (((refuse.prepend _).lift setTy).prepend _ |>.prepend _) _
        (hf_members holds _ (List.get_mem _ _)) (region.closed _ inside _ (zfOf_member_index holds index))
        (fun holdsAt => fails ⟨_, ⟨labelled, zfOf_member_index holds index⟩, holdsAt⟩) (.var .vz) rfl
        (describesSomeOfTerm ((((laws.prepend _).lift setTy).prepend _ |>.prepend _)) (hf_members holds _ (List.get_mem _ _))
          (Proof.newest _)))
        (Proof.prepend _ (conjunctionRight (Proof.newest _)))
    · rw [show nativeFormula (.possibly label inner) x env = falsity by simp only [nativeFormula, if_neg labelled]]
      exact .impI (Proof.newest _)
  | _, .necessarily label inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x,
      _, described => by
    have modalInner : inner.regional = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · have notAll : (membersOf term).all (decideOn region.terms inner decision) = false := by
        have rejected := (decideOn_iff_regional region (.necessarily label inner) modal (Or.inr parts) agree term holds inside).not.mpr fails
        simp only [decideOn, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or, not_not] at rejected
        exact Bool.eq_false_iff.mpr rejected.2
      have bad : ∃ value ∈ membersOf term, (!decideOn region.terms inner decision value) = true := by
        obtain ⟨value, member, rejected⟩ := List.all_eq_false.mp notAll
        exact ⟨value, member, by simpa using rejected⟩
      let index := (chooseIndex (membersOf term) (fun value => !decideOn region.terms inner decision value) bad).1
      have memberHolds := hf_members holds _ (List.get_mem (membersOf term) index)
      have memberInside := region.closed _ inside _ (zfOf_member_index holds index)
      have failsThere : ¬ extensional.sat sets inner (zfOf ((membersOf term).get index)) := fun holdsAt => by
        have rejected : (!decideOn region.terms inner decision ((membersOf term).get index)) = true :=
          (chooseIndex (membersOf term) (fun value => !decideOn region.terms inner decision value) bad).2
        rw [(decideOn_iff_regional region inner modalInner (Or.inr parts) agree _ memberHolds memberInside).mpr holdsAt] at rejected
        simp at rejected
      rw [show nativeFormula (.necessarily label inner) x env = .all (σ := setTy) (.imp (member (.var .vz) (weaken x))
        (nativeFormula inner (.var .vz) (underElement env))) by simp only [nativeFormula, if_pos labelled]]
      refine .impI (someMemberHyps (Proof.prepend _ described) index ?_)
      exact .impE (refuteNative region parts inner modalInner ((((laws.prepend _).lift setTy).prepend _).prepend _ |>.prepend _)
        (underElement env) sets decision agree ((((refuse.prepend _).lift setTy).prepend _).prepend _ |>.prepend _) _
        memberHolds memberInside failsThere (.var .vz) rfl
        (describesSomeOfTerm (((((laws.prepend _).lift setTy).prepend _).prepend _ |>.prepend _)) memberHolds
          (Proof.newest _)))
        (ProofSyntaxModulo.impE (Proof.atNewest (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
          ((Proof.newest _).lift (σ := setTy)))))) (Proof.prepend _ (Proof.newest _)))
    · exact False.elim (fails fun _ step => (labelled step.1).elim)
  | _, .is name, _, _, _, laws, _, _, _, _, _, term, holds, _, fails, x, _, described => by
    refine if named : hereditary membership hfRule.category name = true then ?_ else ?_
    · rw [show nativeFormula (.is name) x _ = describesSomeOf name x by simp only [nativeFormula, if_pos named],
        describesSomeOf_set ((hereditary_iff _).mp named)]
      exact .impI (describesSomeDistinct ((laws.prepend _)) holds ((hereditary_iff _).mp named)
        (fun same => fails ⟨(hereditary_iff _).mp named, same⟩) (described.prepend _) (Proof.newest _))
    · rw [show nativeFormula (.is name) x _ = falsity by simp only [nativeFormula, if_neg named]]
      exact .impI (Proof.newest _)
  | _, .isNot name, _, _, _, _, _, _, _, _, _, term, holds, _, fails, x, _, described => by
    have both : IsHF name ∧ zfOf term = zfOf name := by
      by_contra none
      exact fails none
    rw [show nativeFormula (.isNot name) x _ = negCore (describesSomeOf name x) by
      simp only [nativeFormula, if_pos ((hereditary_iff _).mpr both.1)], describesSomeOf_set both.1]
    exact .impI (.impE (Proof.newest _) (describesSomeSame holds both.1 both.2 (described.prepend _)))
  | _, .empty kind, _, _, _, laws, _, _, _, _, _, term, holds, _, fails, x, _, described => by
    refine if set : kind = .hashSet then ?_ else ?_
    · rw [show nativeFormula (.empty kind) x _ = .all (negCore (member (.var .vz) (weaken x))) by
        simp only [nativeFormula, if_pos set]]
      have nonempty : zfOf term ≠ ∅ := fun isEmpty => fails ⟨set, isEmpty⟩
      refine .impI (someMemberHyps (Proof.prepend _ described) (firstIndex holds nonempty) ?_)
      exact .impE (Proof.atNewest (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
        ((Proof.newest _).lift (σ := setTy)))))) (Proof.prepend _ (Proof.newest _))
    · rw [show nativeFormula (.empty kind) x _ = falsity by simp only [nativeFormula, if_neg set]]
      exact .impI (Proof.newest _)
  | _, .nonEmpty kind, _, _, _, _, _, _, _, _, _, term, holds, _, fails, x, _, described => by
    have both : kind = .hashSet ∧ zfOf term = ∅ := by
      by_contra none
      exact fails none
    rw [show nativeFormula (.nonEmpty kind) x _ = negCore (.all (negCore (member (.var .vz) (weaken x)))) by
      simp only [nativeFormula, if_pos both.1]]
    refine .impI (.impE (Proof.newest _) (.allI (.impI ?_)))
    refine oneCases (membersOf term) (describesSome_forward (describesSomeUnder (described.prepend _) setTy _)
      (Proof.newest _)) fun index => ?_
    exact Fin.elim0 (index.cast (by rw [members_nil_of_empty holds both.2]; rfl))
  | _, .typed type, _, _, _, laws, _, _, _, _, _, term, holds, _, fails, x, _, described =>
    refuteTypedSome type laws term holds fails x described
  | _, .untyped type, _, _, _, _, _, _, _, _, _, term, holds, _, fails, x, _, described => by
    have typed : SetTyped (zfOf term) type := by
      by_contra none
      exact fails none
    exact .impI (.impE (Proof.newest _) (proveTypedSome type term holds typed x (described.prepend _)))
  | _, .atLeast count .forward label inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside,
      fails, x, coreX, described => by
    have modalInner : inner.regional = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.atLeast count .forward label inner) x env =
        countWith (fun {_} y env => nativeFormula inner y env) count x env by simp only [nativeFormula, if_pos labelled]]
      have refused : countDecide (decideOn region.terms inner decision) count (membersOf term) = false := by
        have rejected := (decideOn_iff_regional region (.atLeast count .forward label inner) modal (Or.inr parts) agree term holds inside).not.mpr
          fails
        rw [decideOn, if_pos labelled] at rejected
        exact Bool.eq_false_iff.mpr rejected
      exact refuteCount region (point := fun {_} y env => nativeFormula inner y env)
        (fun θ y env => subst_nativeFormula_regional θ inner modalInner y env)
        (fun {_} Δ env => NegKnowledge Δ env sets region.sets) (fun refuse ψ => refuse.prepend ψ)
        (fun refuse => refuse.lift setTy) (decideOn region.terms inner decision)
        (fun laws' env' refuse' value valueHolds valueInside rejected y coreY describedY =>
          refuteNative region parts inner modalInner laws'.toHasLaws env' sets decision agree refuse' value valueHolds valueInside
            (fun holdsThere => by
              rw [(decideOn_iff_regional region inner modalInner (Or.inr parts) agree value valueHolds valueInside).mpr holdsThere] at rejected
              exact Bool.noConfusion rejected) y coreY (describesSomeOfTerm laws'.toHasLaws valueHolds describedY))
        count laws.core env refuse (membersOf term) (hf_members holds)
        (fun value member => region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩)) refused x
        described
    · rw [show nativeFormula (.atLeast count .forward label inner) x env = if count = 0 then truth else falsity by
        simp only [nativeFormula, if_neg labelled]]
      rw [if_neg fun zero => fails ((atLeast_unlabelled labelled (zfOf term) _).mpr zero)]
      exact .impI (Proof.newest _)
  | _, .allButFewer count .forward label inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds,
      inside, fails, x, coreX, described => by
    have modalInner : inner.regional = true := modal
    refine if labelled : memberLabel label then ?_ else ?_
    · rw [show nativeFormula (.allButFewer count .forward label inner) x env =
        negCore (countWith (fun {_} y env => negCore (nativeFormula inner y env)) count x env) by
        simp only [nativeFormula, if_pos labelled]]
      have counted : countDecide (fun value => !decideOn region.terms inner decision value) count (membersOf term) =
          true := by
        have rejected := (decideOn_iff_regional region (.allButFewer count .forward label inner) modal (Or.inr parts) agree term holds
          inside).not.mpr fails
        rw [decideOn, if_pos labelled, Bool.not_eq_true', Bool.eq_false_iff, not_not] at rejected
        exact rejected
      have many := proveCount region (point := fun {_} y env => negCore (nativeFormula inner y env))
        (fun θ y env => by rw [subst_negCore, subst_nativeFormula_regional θ inner modalInner y env])
        (fun {_} Δ env => NegKnowledge Δ env sets region.sets) (fun refuse ψ => refuse.prepend ψ)
        (fun refuse => refuse.lift setTy) (fun value => !decideOn region.terms inner decision value)
        (fun laws' env' refuse' value valueHolds valueInside accepted y coreY describedY =>
          refuteNative region parts inner modalInner laws'.toHasLaws env' sets decision agree refuse' value valueHolds valueInside
            (fun holdsThere => by
              rw [(decideOn_iff_regional region inner modalInner (Or.inr parts) agree value valueHolds valueInside).mpr holdsThere] at accepted
              exact Bool.noConfusion accepted) y coreY (describesSomeOfTerm laws'.toHasLaws valueHolds describedY))
        count laws.core env refuse (membersOf term) (hf_members holds)
        (fun value member => region.closed _ inside _ ((mem_zfOf_iff holds).mpr ⟨value, member, rfl⟩)) counted x
        described
      exact .impI (.impE (Proof.newest _) (Proof.prepend _ many))
    · rw [show nativeFormula (.allButFewer count .forward label inner) x env = if count = 0 then falsity else truth by
        simp only [nativeFormula, if_neg labelled]]
      rw [if_pos (by_contra fun nonzero => fails fun many => nonzero ((atLeast_unlabelled labelled (zfOf term) _).mp many))]
      exact .impI (Proof.newest _)
  | _, .single kind inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x, _,
      described => by
    have modalInner : inner.regional = true := modal
    refine if set : kind = .hashSet then ?_ else ?_
    · rw [show nativeFormula (.single kind inner) x env = existentialInline (σ := setTy) (conjunctionFormula
        (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env))
          (onlyMember (weaken x) (.var .vz)))) by simp only [nativeFormula, if_pos set]]
      refine .impI (existentialElim (Proof.newest _) ?_)
      have describedX := describesSomeUnder (described.prepend (existentialInline (σ := setTy) (conjunctionFormula
        (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env))
          (onlyMember (weaken x) (.var .vz)))))) setTy (conjunctionFormula (member (.var .vz) (weaken x))
        (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env)) (onlyMember (weaken x) (.var .vz))))
      refine oneCases (membersOf term) (describesSome_forward describedX
        (conjunctionLeft (Proof.newest _))) fun index => ?_
      have indexHolds := hf_members holds _ (List.get_mem (membersOf term) index)
      have indexInside := region.closed _ inside _ (zfOf_member_index holds index)
      refine if good : decideOn region.terms inner decision ((membersOf term).get index) = true then ?_ else ?_
      · have other : ∃ value ∈ membersOf term, (!sameSet ((membersOf term).get index) value) = true := by
          by_contra none
          apply fails
          refine ⟨zfOf ((membersOf term).get index), ⟨set, (zfOf_eq_singleton_iff holds).mpr
            ⟨⟨_, List.get_mem _ index, rfl⟩, fun value member => ?_⟩⟩,
            (decideOn_iff_regional region inner modalInner (Or.inr parts) agree _ indexHolds indexInside).mp good⟩
          cases same : sameSet ((membersOf term).get index) value
          · exact absurd ⟨value, member, by rw [same]; rfl⟩ none
          · exact ((sameSet_iff _ indexHolds value (hf_members holds value member)).mp same).symm
        let otherIndex := (chooseIndex (membersOf term) (fun value => !sameSet ((membersOf term).get index) value) other).1
        have otherHolds := hf_members holds _ (List.get_mem (membersOf term) otherIndex)
        have differ : zfOf ((membersOf term).get index) ≠ zfOf ((membersOf term).get otherIndex) := fun same => by
          have apart : (!sameSet ((membersOf term).get index) ((membersOf term).get otherIndex)) = true :=
            (chooseIndex (membersOf term) (fun value => !sameSet ((membersOf term).get index) value) other).2
          rw [(sameSet_iff _ indexHolds _ otherHolds).mpr same] at apart
          simp at apart
        have laws' : HasLaws (describes ((membersOf term).get index) (.var .vz) :: conjunctionFormula
            (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env))
              (onlyMember (weaken x) (.var .vz))) :: weakenHyps (σ := setTy) (existentialInline (σ := setTy)
                (conjunctionFormula (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz)
                  (underElement env)) (onlyMember (weaken x) (.var .vz)))) :: Δ)) :=
          ((((laws.prepend _).lift setTy).prepend _).prepend _)
        have only2 : Proof (describes ((membersOf term).get index) (.var .vz) :: conjunctionFormula
            (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env))
              (onlyMember (weaken x) (.var .vz))) :: weakenHyps (σ := setTy) (existentialInline (σ := setTy)
                (conjunctionFormula (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz)
                  (underElement env)) (onlyMember (weaken x) (.var .vz)))) :: Δ)) (onlyMember (weaken x) (.var .vz)) :=
          Proof.prepend _ (conjunctionRight (conjunctionRight (Proof.newest _)))
        have index2 : Proof (describes ((membersOf term).get index) (.var .vz) :: conjunctionFormula
            (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env))
              (onlyMember (weaken x) (.var .vz))) :: weakenHyps (σ := setTy) (existentialInline (σ := setTy)
                (conjunctionFormula (member (.var .vz) (weaken x)) (conjunctionFormula (nativeFormula inner (.var .vz)
                  (underElement env)) (onlyMember (weaken x) (.var .vz)))) :: Δ))
            (describes ((membersOf term).get index) (.var .vz)) :=
          Proof.newest _
        refine someMemberHyps (Proof.prepend (describes ((membersOf term).get index) (.var .vz)) describedX) otherIndex ?_
        exact describesDistinct ((((laws'.lift setTy).prepend _).prepend _).prepend _)
          ((membersOf term).get index) ((membersOf term).get otherIndex) indexHolds otherHolds differ _
          (Proof.prepend _ (Proof.prepend _ (Proof.prepend _ (Proof.cast (weaken_describes _ _) index2.lift))))
          (describesAlong otherHolds (Proof.newest _) (onlyAt (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
            (Proof.cast (weaken_onlyMember _ _) only2.lift)))) (.var .vz) (Proof.prepend _ (Proof.newest _))))
      · have failsThere : ¬ extensional.sat sets inner (zfOf ((membersOf term).get index)) := fun holdsAt =>
          good ((decideOn_iff_regional region inner modalInner (Or.inr parts) agree _ indexHolds indexInside).mpr holdsAt)
        exact .impE (refuteNative region parts inner modalInner ((((laws.prepend _).lift setTy).prepend _).prepend _)
          (underElement env) sets decision agree ((((refuse.prepend _).lift setTy).prepend _).prepend _) _ indexHolds
          indexInside failsThere (.var .vz) rfl
          (describesSomeOfTerm (((((laws.prepend _).lift setTy).prepend _).prepend _)) indexHolds (Proof.newest _)))
          (Proof.prepend _ (conjunctionLeft (conjunctionRight (Proof.newest _))))
    · rw [show nativeFormula (.single kind inner) x env = falsity by simp only [nativeFormula, if_neg set]]
      exact .impI (Proof.newest _)
  | _, .everySingle kind inner, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x,
      _, described => by
    have modalInner : inner.regional = true := modal
    have info : kind = .hashSet ∧ ∃ element, zfOf term = {element} ∧ ¬ extensional.sat sets inner element := by
      by_contra none
      apply fails
      rintro element ⟨set, single⟩
      by_contra notHolds
      exact none ⟨set, element, single, notHolds⟩
    have set := info.1
    have nonempty : zfOf term ≠ ∅ := by
      obtain ⟨element, single, _⟩ := info.2
      intro isEmpty
      rw [single] at isEmpty
      exact ZFSet.notMem_empty element (isEmpty ▸ ZFSet.mem_singleton.mpr rfl)
    let first := firstIndex holds nonempty
    have firstHolds := hf_members holds _ (List.get_mem (membersOf term) first)
    have firstInside := region.closed _ inside _ (zfOf_member_index holds first)
    have allSame : ∀ index : Fin (membersOf term).length,
        zfOf ((membersOf term).get index) = zfOf ((membersOf term).get first) := by
      obtain ⟨element, single, _⟩ := info.2
      intro index
      rw [((zfOf_eq_singleton_iff holds).mp single).2 _ (List.get_mem _ index),
        ((zfOf_eq_singleton_iff holds).mp single).2 _ (List.get_mem _ first)]
    have failsFirst : ¬ extensional.sat sets inner (zfOf ((membersOf term).get first)) := by
      obtain ⟨element, single, notHolds⟩ := info.2
      rwa [((zfOf_eq_singleton_iff holds).mp single).2 _ (List.get_mem _ first)]
    rw [show nativeFormula (.everySingle kind inner) x env = .all (σ := setTy) (.imp (member (.var .vz) (weaken x))
      (.imp (onlyMember (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) (underElement env)))) by
      simp only [nativeFormula, if_pos set]]
    let hypothesis : Term Symbol Γ .prop := .all (σ := setTy) (.imp (member (.var .vz) (weaken x))
      (.imp (onlyMember (weaken x) (.var .vz)) (nativeFormula inner (.var .vz) (underElement env))))
    refine .impI (someMemberHyps (Proof.prepend hypothesis described) first ?_)
    exact .impE (refuteNative region parts inner modalInner ((((laws.prepend hypothesis).lift setTy).prepend _).prepend _ |>.prepend _)
      (underElement env) sets decision agree ((((refuse.prepend hypothesis).lift setTy).prepend _).prepend _ |>.prepend _) _
      firstHolds firstInside failsFirst (.var .vz) rfl
      (describesSomeOfTerm (((((laws.prepend hypothesis).lift setTy).prepend _).prepend _ |>.prepend _)) firstHolds
        (Proof.newest _)))
      (.impE (.impE (Proof.atNewest (Proof.prepend _ (Proof.prepend _ (Proof.prepend _
          ((Proof.newest (Δ := Δ) hypothesis).lift (σ := setTy)))))) (Proof.prepend _ (Proof.newest _)))
        (onlyProof holds firstHolds allSame
          (Proof.prepend _ (Proof.prepend _ (describesSomeUnder (Proof.prepend hypothesis described) setTy _)))
          (Proof.newest _)))
  | _, .split kind left right, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails, x,
      _, described => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    refine if isSet : kind = .hashSet then ?_ else ?_
    · subst isSet
      let body : Term Symbol (setTy :: setTy :: Γ) .prop := conjunctionFormula
        (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (conjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))
      change Proof Δ (negCore (existentialInline (σ := setTy) (existentialInline (σ := setTy) body)))
      refine .impI (existentialElim (Proof.newest _) (existentialElim (Proof.newest _) ?_))
      let Δ3 : List (Term Symbol (setTy :: setTy :: Γ) .prop) := body :: weakenHyps (σ := setTy)
        (existentialInline (σ := setTy) body :: weakenHyps (σ := setTy)
          (existentialInline (σ := setTy) (existentialInline (σ := setTy) body) :: Δ))
      have laws3 : HasLaws Δ3 := ((((laws.prepend _).lift setTy).prepend _).lift setTy).prepend _
      have refuse3 : NegKnowledge Δ3 (underElement (underElement env)) sets region.sets :=
        ((((refuse.prepend _).lift setTy).prepend _).lift setTy).prepend _
      have described3 : Proof Δ3 (describesSome (membersOf term) (weaken (weaken x))) :=
        describesSomeUnder (describesSomeUnder (described.prepend _) setTy _) setTy _
      have union3 : Proof Δ3 (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz)) :=
        conjunctionLeft (Proof.newest _)
      have atLeft3 : Proof Δ3 (nativeFormula left (.var (.vs .vz)) (underElement (underElement env))) :=
        conjunctionLeft (conjunctionRight (Proof.newest _))
      have atRight3 : Proof Δ3 (nativeFormula right (.var .vz) (underElement (underElement env))) :=
        conjunctionRight (conjunctionRight (Proof.newest _))
      refine coverBranches described3 union3 (fun _ _ yes no => falsityByCases yes no) ?_
        (membersOf term) [] [] [] (fun _ found => found) (fun _ found => absurd found List.not_mem_nil)
        (fun _ found => absurd found List.not_mem_nil) (fun _ found => Or.inr (Or.inr found))
        (upperOfLeft described3 union3) truthIntro (upperOfRight described3 union3) truthIntro
      intro extra chosenLeft chosenRight inLeft inRight covered describedA describedB
      have union := zfOf_eq_union_of_cover holds inLeft inRight covered
      have leftHolds : IsHF (set chosenLeft) := .members fun value found => hf_members holds value (inLeft value found)
      have rightHolds : IsHF (set chosenRight) := .members fun value found => hf_members holds value (inRight value found)
      have leftInside := parts _ inside _ (part_left union)
      have rightInside := parts _ inside _ (part_right union)
      refine if leftGood : decideOn region.terms left decision (set chosenLeft) = true then ?_ else ?_
      · have rightFails : ¬ extensional.sat sets right (zfOf (set chosenRight)) := fun holdsRight =>
          fails ⟨_, _, ⟨rfl, union⟩, (decideOn_iff_regional region left modal.1
            (Or.inr parts) agree _ leftHolds leftInside).mp leftGood, holdsRight⟩
        exact .impE (refuteNative region parts right modal.2 (HasLaws.prependAll extra laws3)
          (underElement (underElement env)) sets decision agree (NegKnowledge.prependAll extra refuse3)
          (set chosenRight) rightHolds rightInside rightFails (.var .vz) rfl describedB)
          (Proof.prependAll extra atRight3)
      · exact .impE (refuteNative region parts left modal.1 (HasLaws.prependAll extra laws3)
          (underElement (underElement env)) sets decision agree (NegKnowledge.prependAll extra refuse3)
          (set chosenLeft) leftHolds leftInside (fun holdsLeft => leftGood
            ((decideOn_iff_regional region left modal.1 (Or.inr parts) agree _
              leftHolds leftInside).mpr holdsLeft)) (.var (.vs .vz)) rfl describedA)
          (Proof.prependAll extra atLeft3)
    · rw [show nativeFormula (.split kind left right) x env = falsity by simp only [nativeFormula, if_neg isSet]]
      exact .impI (Proof.newest _)
  | _, .everySplit kind left right, modal, Γ, Δ, laws, env, sets, decision, agree, refuse, term, holds, inside, fails,
      x, coreX, described => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    refine if isSet : kind = .hashSet then ?_ else ?_
    · subst isSet
      have found : ∃ cover ∈ coverings (membersOf term), (!decideOn region.terms left decision (set cover.1) &&
          !decideOn region.terms right decision (set cover.2)) = true := by
        by_contra none
        apply fails
        rintro first second ⟨-, union⟩
        obtain ⟨cover, member, firstEq, secondEq⟩ := split_covering holds union
        obtain ⟨leftHolds, rightHolds, coverUnion⟩ := covering_split holds member
        by_contra neither
        refine none ⟨cover, member, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
        · rw [Bool.not_eq_true', Bool.eq_false_iff]
          exact fun good => neither (Or.inl (firstEq ▸ (decideOn_iff_regional region left
            modal.1 (Or.inr parts) agree _ leftHolds
            (parts _ inside _ (part_left coverUnion))).mp good))
        · rw [Bool.not_eq_true', Bool.eq_false_iff]
          exact fun good => neither (Or.inr (secondEq ▸ (decideOn_iff_regional region right
            modal.2 (Or.inr parts) agree _ rightHolds
            (parts _ inside _ (part_right coverUnion))).mp good))
      let chosen := chooseIndex (coverings (membersOf term)) (fun cover => !decideOn region.terms left decision
        (set cover.1) && !decideOn region.terms right decision (set cover.2)) found
      have member : (coverings (membersOf term)).get chosen.1 ∈ coverings (membersOf term) := List.get_mem _ _
      have refused := Bool.and_eq_true_iff.mp chosen.2
      have coverHolds := covering_split holds member
      have coverParts := mem_coverings_parts member
      have leftFails : ¬ extensional.sat sets left (zfOf (set ((coverings (membersOf term)).get chosen.1).1)) :=
        fun holdsLeft => by
          have rejected := refused.1
          rw [(decideOn_iff_regional region left modal.1 (Or.inr parts) agree _
            coverHolds.1 (parts _ inside _ (part_left coverHolds.2.2))).mpr holdsLeft] at rejected
          exact Bool.noConfusion rejected
      have rightFails : ¬ extensional.sat sets right (zfOf (set ((coverings (membersOf term)).get chosen.1).2)) :=
        fun holdsRight => by
          have rejected := refused.2
          rw [(decideOn_iff_regional region right modal.2 (Or.inr parts) agree _
            coverHolds.2.1 (parts _ inside _ (part_right coverHolds.2.2))).mpr holdsRight] at rejected
          exact Bool.noConfusion rejected
      let body : Term Symbol (setTy :: setTy :: Γ) .prop := .imp (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (disjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))
      change Proof Δ (negCore (.all (σ := setTy) (.all (σ := setTy) body)))
      refine .impI ?_
      have instance' := Proof.cast (instantiate_everySplitBody modal.1
        modal.2 x (partTerm x ((coverings (membersOf term)).get chosen.1).1)
        (partTerm x ((coverings (membersOf term)).get chosen.1).2) env)
        (.allE (partTerm x ((coverings (membersOf term)).get chosen.1).2) (Proof.cast rfl
          (.allE (partTerm x ((coverings (membersOf term)).get chosen.1).1)
            (Proof.newest (Δ := Δ) (.all (σ := setTy) (.all (σ := setTy) body))))))
      have either := ProofSyntaxModulo.impE instance' (partsSplit (laws.prepend _) (described.prepend _) _ _ coverParts.2.2)
      exact disjunctionElim either
        (.impE (Proof.prepend _ (refuteNative region parts left modal.1 (laws.prepend _) env sets decision
          agree (refuse.prepend _) _ coverHolds.1 (parts _ inside _ (part_left coverHolds.2.2)) leftFails _
          (isCore_partTerm coreX _) (partDescribed (laws.prepend _) (described.prepend _) _ coverParts.1)))
          (Proof.newest _))
        (.impE (Proof.prepend _ (refuteNative region parts right modal.2 (laws.prepend _) env sets decision
          agree (refuse.prepend _) _ coverHolds.2.1 (parts _ inside _ (part_right coverHolds.2.2)) rightFails _
          (isCore_partTerm coreX _) (partDescribed (laws.prepend _) (described.prepend _) _ coverParts.2.1)))
          (Proof.newest _))
    · exact False.elim (fails fun _ _ split => absurd split.1 isSet)
  | _, .sometimeBefore _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .alwaysBefore _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .atLeast _ .backward _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .allButFewer _ .backward _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .built _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBuilt _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .body _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyBody _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .multiBody _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyMultiBody _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .bound _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .notBound _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsAll _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .mapsSome _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .someOf _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _, .everyOf _ _, modal, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd modal Bool.false_ne_true

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
