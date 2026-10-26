import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipProofTerms

/-!
# How much excluded middle the every-splits need

The certificate compiler proves every regional native type that holds from the laws of the empty set, the power set
and separation, and excluded middle; it needs excluded middle only for every-splits. This module shows that no
profile does better: some every-splits are excluded middle, said about sets.

- **Two principles**: excluded middle (`middleLaw`, `∀ p. p ∨ ¬ p`) and weak excluded middle (`weakMiddleLaw`,
  `∀ p. ¬ p ∨ ¬¬ p`).
- **Two native types**: every split has a first part that is empty or has a member (`emptyOrInhabited`), and every
  split has a first part that is empty or not empty (`emptyOrNonEmpty`). Both hold of every set.
- **The split that decides a proposition**: a set `z` is the union of `{w ∈ z | p}` and `z` (`guardSplit`). When `z`
  has a member, the first part is empty exactly when `¬ p`, and has a member exactly when `p`.
- **So, at a term with a member, over the three laws:**
  - the sentence of `emptyOrInhabited` gives excluded middle (`middleOfEmptyOrInhabited`), and excluded middle gives it
    (`emptyOrInhabitedOfMiddle`);
  - the sentence of `emptyOrNonEmpty` gives weak excluded middle (`weakMiddleOfEmptyOrNonEmpty`), and weak excluded
    middle gives it (`emptyOrNonEmptyOfWeakMiddle`).
- **Bounded excluded middle is the full one here** (`middleOfBoundedMiddle`): excluded middle for "`{w ∈ z | p}` has a
  member", a formula bounded by the set, gives `p ∨ ¬ p`, since separation takes any predicate.
- **Completeness for the regional fragment is excluded middle** (`regionalComplete_iff_middle`): hypotheses with the
  three laws prove the sentence of every regional native type that holds exactly when they prove excluded middle.
- **At the empty set the inhabitant is missing**: the sentence of `emptyOrInhabited` at `0` is proved from the three
  laws alone (`emptyOrInhabitedAtZero`), since a split of the empty set has an empty first part.
- **Each equivalence is a pair of closed terms in the package of set theory** (`emptyOrInhabited_middle_proofTerms`,
  `emptyOrNonEmpty_weakMiddle_proofTerms`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula weaken rename subst instantiate Subst Rename
  ProofSyntaxModulo weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member separate)

/-! ## Two principles and two native types -/

/-- **Weak excluded middle**: `∀ p. ¬ p ∨ ¬¬ p`. -/
def weakMiddleLaw : ClosedFormula Symbol :=
  .all (σ := .prop) (disjunctionFormula (negCore (.var .vz)) (negCore (negCore (.var .vz))))

/-- **Every split has a first part that is empty or has a member.** -/
def emptyOrInhabited : Formula 0 := .everySplit .hashSet (.or (.empty .hashSet) (.possibly .any .top)) .bot

/-- **Every split has a first part that is empty or not empty.** -/
def emptyOrNonEmpty : Formula 0 := .everySplit .hashSet (.or (.empty .hashSet) (.nonEmpty .hashSet)) .bot

theorem emptyOrInhabited_regional : emptyOrInhabited.regional = true := rfl

theorem emptyOrNonEmpty_regional : emptyOrNonEmpty.regional = true := rfl

/-- Both lie outside the core profile's fragment. -/
theorem emptyOrInhabited_not_core : emptyOrInhabited.regionalWith false = false := rfl

theorem emptyOrNonEmpty_not_core : emptyOrNonEmpty.regionalWith false = false := rfl

section Derivations

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-! ## Empty, inhabited and not empty -/

/-- `x` has a member. -/
abbrev inhabitedFormula (x : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken x)) truth)

theorem nativeFormula_emptyOrInhabitedPart {n : ℕ} (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    nativeFormula (.or (.empty .hashSet) (.possibly .any .top)) x env =
      disjunctionFormula (emptyFormula x) (inhabitedFormula x) := rfl

theorem nativeFormula_emptyOrNonEmptyPart {n : ℕ} (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    nativeFormula (.or (.empty .hashSet) (.nonEmpty .hashSet)) x env =
      disjunctionFormula (emptyFormula x) (negCore (emptyFormula x)) := rfl

theorem weaken_inhabitedFormula {σ : Ty Unit} (x : Term Symbol Γ setTy) :
    weaken (σ := σ) (inhabitedFormula x) = inhabitedFormula (weaken x) := by
  rw [weaken_eq_subst (inhabitedFormula x), weaken_eq_subst x]
  simp only [inhabitedFormula, subst_existentialInline, subst_conjunctionFormula, member, subst,
    Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem instantiate_inhabitedBody (y x : Term Symbol Γ setTy) :
    instantiate y (conjunctionFormula (member (.var .vz) (weaken x)) truth) = conjunctionFormula (member y x) truth := by
  unfold instantiate
  rw [subst_conjunctionFormula]
  show conjunctionFormula (member y (subst (Subst.single y) (weaken x))) (subst (Subst.single y) truth) = _
  rw [← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]
  rfl

/-- **A set that is not not empty is empty.** -/
def emptyOfDoubleNegation {x : Term Symbol Γ setTy} (proof : Proof Δ (negCore (negCore (emptyFormula x)))) :
    Proof Δ (emptyFormula x) := by
  have lifted : Proof (weakenHyps (σ := setTy) Δ) (negCore (negCore (emptyFormula (weaken x)))) :=
    Proof.cast (by rw [weaken_negCore, weaken_negCore, weaken_emptyFormula]) proof.lift
  exact .allI (.impI (.impE (lifted.prepend _)
    (.impI (.impE (noMemberAt (Proof.newest _) (.var .vz)) ((Proof.newest _).prepend _)))))

/-- **A set with no member is empty.** -/
def emptyOfNotInhabited {x : Term Symbol Γ setTy} (proof : Proof Δ (negCore (inhabitedFormula x))) :
    Proof Δ (emptyFormula x) := by
  have lifted : Proof (weakenHyps (σ := setTy) Δ) (negCore (inhabitedFormula (weaken x))) :=
    Proof.cast (by rw [weaken_negCore, weaken_inhabitedFormula]) proof.lift
  exact .allI (.impI (.impE (lifted.prepend _) (existentialIntro (.var .vz)
    (Proof.cast (instantiate_inhabitedBody _ _).symm (conjunctionIntro (Proof.newest _) truthIntro)))))

/-! ## The split that decides a proposition -/

/-- **The members of `z` if `p`**: `{w ∈ z | p}`. -/
def guardTerm (z : Term Symbol Γ setTy) (p : Term Symbol Γ .prop) : Term Symbol Γ setTy :=
  separate z (.lam (weaken p))

theorem weaken_guardTerm {σ : Ty Unit} (z : Term Symbol Γ setTy) (p : Term Symbol Γ .prop) :
    weaken (σ := σ) (guardTerm z p) = guardTerm (weaken z) (weaken p) := by
  rw [weaken_eq_subst (guardTerm z p), weaken_eq_subst z, weaken_eq_subst p]
  simp only [guardTerm, separate, subst, Mettapedia.Logic.HOL.subst_weaken]

theorem isCore_weaken {σ τ : Ty Unit} {t : Term Symbol Γ τ} (core : t.isCore = true) :
    (weaken (σ := σ) t).isCore = true := by
  simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, core]

/-- **Membership in `{w ∈ z | p}`**: membership in `z`, and `p`. -/
def guardMember (laws : HasLaws Δ) (z : Term Symbol Γ setTy) {p : Term Symbol Γ .prop} (coreP : p.isCore = true)
    {w : Term Symbol Γ setTy} (coreW : w.isCore = true) :
    Proof Δ (iffCore (member w (guardTerm z p)) (conjunctionFormula (member w z) p)) := by
  have law := laws.separationAt z (.lam (weaken p)) w
  refine Proof.iffIntro ?_ ?_
  · have both := (Proof.prepend _ law).iffForward (Proof.newest _)
    exact conjunctionIntro (conjunctionLeft both) (Proof.cast (Mettapedia.Logic.HOL.instantiate_weaken w p)
      (Proof.betaReduce (isCore_weaken coreP) coreW (conjunctionRight both)))
  · exact (Proof.prepend _ law).iffBackward (conjunctionIntro (conjunctionLeft (Proof.newest _))
      (Proof.betaExpand (isCore_weaken coreP) coreW (Proof.cast (Mettapedia.Logic.HOL.instantiate_weaken w p).symm
        (conjunctionRight (Proof.newest _)))))

/-- **`z` is the union of `{w ∈ z | p}` and `z`.** -/
def guardSplit (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {p : Term Symbol Γ .prop} (coreP : p.isCore = true) :
    Proof Δ (splitCore z (guardTerm z p) z) := by
  refine .allI ?_
  rw [weaken_guardTerm]
  refine Proof.iffIntro (disjunctionRight (Proof.newest _)) (disjunctionElim (Proof.newest _) ?_ (Proof.newest _))
  exact conjunctionLeft ((guardMember (((laws.lift setTy).prepend _).prepend _) (weaken z) (isCore_weaken coreP)
    (w := .var .vz) rfl).iffForward (Proof.newest _))

/-- **If `z` has a member and `{w ∈ z | p}` is empty, then `¬ p`.** -/
def notOfEmptyGuard (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {χ : Term Symbol (setTy :: Γ) .prop}
    (inhabitant : Proof Δ (existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken z)) χ)))
    {p : Term Symbol Γ .prop} (coreP : p.isCore = true) (empty : Proof Δ (emptyFormula (guardTerm z p))) :
    Proof Δ (negCore p) := by
  refine .impI (existentialElim (inhabitant.prepend _) ?_)
  have emptyPart : Proof _ (emptyFormula (guardTerm (weaken z) (weaken p))) :=
    Proof.cast (by rw [weaken_emptyFormula, weaken_guardTerm]) ((empty.prepend p).lift (σ := setTy))
  let found : Term Symbol (setTy :: Γ) .prop := conjunctionFormula (member (.var .vz) (weaken z)) χ
  have inGuard := (guardMember (((laws.prepend p).lift setTy).prepend found) (weaken z) (isCore_weaken coreP)
    (w := .var .vz) rfl).iffBackward
      (conjunctionIntro (conjunctionLeft (Proof.newest found)) ((Proof.newest (Δ := Δ) p).lift.prepend found))
  exact .impE (noMemberAt (emptyPart.prepend found) (.var .vz)) inGuard

/-- **If `{w ∈ z | p}` has a member, then `p`.** -/
def ofInhabitedGuard (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {p : Term Symbol Γ .prop} (coreP : p.isCore = true)
    (inhabited : Proof Δ (inhabitedFormula (guardTerm z p))) : Proof Δ p := by
  refine existentialElim inhabited ?_
  exact conjunctionRight ((guardMember ((laws.lift setTy).prepend _) (weaken z) (isCore_weaken coreP)
    (w := .var .vz) rfl).iffForward (Proof.cast (by rw [weaken_guardTerm]) (conjunctionLeft (Proof.newest _))))

/-- **If `{w ∈ z | p}` is not empty, then `¬¬ p`.** -/
def notNotOfNonEmptyGuard (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {p : Term Symbol Γ .prop}
    (coreP : p.isCore = true) (nonEmpty : Proof Δ (negCore (emptyFormula (guardTerm z p)))) :
    Proof Δ (negCore (negCore p)) := by
  refine .impI (.impE (nonEmpty.prepend _) (.allI (.impI ?_)))
  have inGuard : Proof _ (member (.var .vz) (guardTerm (weaken z) (weaken p))) :=
    Proof.cast (by rw [weaken_guardTerm])
      (Proof.newest (Δ := weakenHyps (negCore p :: Δ)) (member (.var .vz) (weaken (guardTerm z p))))
  have holdsP := conjunctionRight ((guardMember (((laws.prepend _).lift setTy).prepend _) (weaken z)
    (isCore_weaken coreP) (w := .var .vz) rfl).iffForward inGuard)
  exact .impE (Proof.cast (weaken_negCore p) (Proof.newest (negCore p)).lift |>.prepend _) holdsP

/-- **Excluded middle for a bounded formula gives excluded middle**: "`{w ∈ z | p}` has a member" is bounded by the set,
and excluded middle for it, at a set `z` with a member, gives `p ∨ ¬ p`. Separation takes any predicate, so the bounded
law is the full one here. -/
def middleOfBoundedMiddle (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {χ : Term Symbol (setTy :: Γ) .prop}
    (inhabitant : Proof Δ (existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken z)) χ)))
    {p : Term Symbol Γ .prop} (coreP : p.isCore = true)
    (bounded : Proof Δ (disjunctionFormula (inhabitedFormula (guardTerm z p))
      (negCore (inhabitedFormula (guardTerm z p))))) :
    Proof Δ (disjunctionFormula p (negCore p)) :=
  disjunctionElim bounded (disjunctionLeft (ofInhabitedGuard (laws.prepend _) coreP (Proof.newest _)))
    (disjunctionRight (notOfEmptyGuard (laws.prepend _) (inhabitant.prepend _) coreP
      (emptyOfNotInhabited (Proof.newest _))))

/-! ## Every-splits at two parts -/

/-- **An every-split at two parts.** -/
def everySplitAt {n : ℕ} {left right : Formula n} (leftRegional : left.regional = true)
    (rightRegional : right.regional = true) {x : Term Symbol Γ setTy} {env : Fin n → Term Symbol Γ predTy}
    (every : Proof Δ (nativeFormula (.everySplit .hashSet left right) x env)) (a b : Term Symbol Γ setTy) :
    Proof Δ (.imp (splitCore x a b) (disjunctionFormula (nativeFormula left a env) (nativeFormula right b env))) :=
  Proof.cast (instantiate_everySplitBody leftRegional rightRegional x a b env)
    (.allE b (Proof.cast rfl (.allE a (Proof.cast rfl every))))

/-- **An every-split from its body**, for arbitrary parts. -/
def everySplitIntro {n : ℕ} {left right : Formula n} {x : Term Symbol Γ setTy} {env : Fin n → Term Symbol Γ predTy}
    (body : Proof (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz) :: weakenHyps (weakenHyps Δ))
      (disjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
        (nativeFormula right (.var .vz) (underElement (underElement env))))) :
    Proof Δ (nativeFormula (.everySplit .hashSet left right) x env) :=
  Proof.cast rfl (.allI (.allI (.impI body)))

/-! ## Excluded middle from the every-split, and back -/

/-- **Excluded middle at `p`, from `emptyOrInhabited` at a set with a member**: the first part of the split of `z`
into `{w ∈ z | p}` and `z` is empty, so `¬ p`, or has a member, so `p`. -/
def middleAt (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {χ : Term Symbol (setTy :: Γ) .prop}
    (inhabitant : Proof Δ (existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken z)) χ)))
    (every : Proof Δ (nativeFormula emptyOrInhabited z Fin.elim0)) {p : Term Symbol Γ .prop} (coreP : p.isCore = true) :
    Proof Δ (disjunctionFormula p (negCore p)) := by
  have cases := ProofSyntaxModulo.impE (everySplitAt rfl rfl every (guardTerm z p) z) (guardSplit laws coreP)
  rw [nativeFormula_emptyOrInhabitedPart] at cases
  refine disjunctionElim cases (disjunctionElim (Proof.newest _) ?_ ?_) (Proof.absurd (Proof.newest _))
  · exact disjunctionRight (notOfEmptyGuard ((laws.prepend _).prepend _) ((inhabitant.prepend _).prepend _) coreP
      (Proof.newest _))
  · exact disjunctionLeft (ofInhabitedGuard ((laws.prepend _).prepend _) coreP (Proof.newest _))

/-- **Weak excluded middle at `p`, from `emptyOrNonEmpty` at a set with a member.** -/
def weakMiddleAt (laws : HasLaws Δ) {z : Term Symbol Γ setTy} {χ : Term Symbol (setTy :: Γ) .prop}
    (inhabitant : Proof Δ (existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken z)) χ)))
    (every : Proof Δ (nativeFormula emptyOrNonEmpty z Fin.elim0)) {p : Term Symbol Γ .prop} (coreP : p.isCore = true) :
    Proof Δ (disjunctionFormula (negCore p) (negCore (negCore p))) := by
  have cases := ProofSyntaxModulo.impE (everySplitAt rfl rfl every (guardTerm z p) z) (guardSplit laws coreP)
  rw [nativeFormula_emptyOrNonEmptyPart] at cases
  refine disjunctionElim cases (disjunctionElim (Proof.newest _) ?_ ?_) (Proof.absurd (Proof.newest _))
  · exact disjunctionLeft (notOfEmptyGuard ((laws.prepend _).prepend _) ((inhabitant.prepend _).prepend _) coreP
      (Proof.newest _))
  · exact disjunctionRight (notNotOfNonEmptyGuard ((laws.prepend _).prepend _) coreP (Proof.newest _))

theorem instantiate_weakMiddle (p : Term Symbol Γ .prop) :
    instantiate p (disjunctionFormula (negCore (.var .vz)) (negCore (negCore (.var .vz)))) =
      disjunctionFormula (negCore p) (negCore (negCore p)) := by
  unfold instantiate
  rw [subst_disjunctionFormula, subst_negCore, subst_negCore, subst_negCore]
  rfl

/-- Excluded middle at a proposition, from the law in a context. -/
def middleInstance (middle : Proof Δ (atContext Γ middleLaw)) (p : Term Symbol Γ .prop) :
    Proof Δ (disjunctionFormula p (negCore p)) :=
  Proof.cast (instantiate_middle p) (.allE (φ := disjunctionFormula (.var .vz) (negCore (.var .vz))) p
    (Proof.cast (by rfl) middle))

/-- Weak excluded middle at a proposition, from the law in a context. -/
def weakMiddleInstance (weakMiddle : Proof Δ (atContext Γ weakMiddleLaw)) (p : Term Symbol Γ .prop) :
    Proof Δ (disjunctionFormula (negCore p) (negCore (negCore p))) :=
  Proof.cast (instantiate_weakMiddle p)
    (.allE (φ := disjunctionFormula (negCore (.var .vz)) (negCore (negCore (.var .vz)))) p
      (Proof.cast (by rfl) weakMiddle))

/-- A closed law under two new variables and a new hypothesis. -/
def lawUnder {φ : ClosedFormula Symbol} (law : Proof Δ (atContext Γ φ)) (ψ : Term Symbol (setTy :: setTy :: Γ) .prop) :
    Proof (ψ :: weakenHyps (σ := setTy) (weakenHyps (σ := setTy) Δ)) (atContext (setTy :: setTy :: Γ) φ) :=
  (Proof.cast (weaken_atContext _) (Proof.cast (weaken_atContext _) law.lift).lift).prepend ψ

/-- **`emptyOrInhabited` at every set, from excluded middle.** -/
def emptyOrInhabitedFrom (middle : Proof Δ (atContext Γ middleLaw)) (x : Term Symbol Γ setTy) :
    Proof Δ (nativeFormula emptyOrInhabited x Fin.elim0) := by
  refine everySplitIntro (disjunctionLeft ?_)
  rw [nativeFormula_emptyOrInhabitedPart]
  exact disjunctionElim (middleInstance (lawUnder middle _) (inhabitedFormula (.var (.vs .vz))))
    (disjunctionRight (Proof.newest _)) (disjunctionLeft (emptyOfNotInhabited (Proof.newest _)))

/-- **`emptyOrNonEmpty` at every set, from weak excluded middle**: at `x` empty, `¬ x empty` is not empty, and
`¬¬ x empty` is empty. -/
def emptyOrNonEmptyFrom (weakMiddle : Proof Δ (atContext Γ weakMiddleLaw)) (x : Term Symbol Γ setTy) :
    Proof Δ (nativeFormula emptyOrNonEmpty x Fin.elim0) := by
  refine everySplitIntro (disjunctionLeft ?_)
  rw [nativeFormula_emptyOrNonEmptyPart]
  exact disjunctionElim (weakMiddleInstance (lawUnder weakMiddle _) (emptyFormula (.var (.vs .vz))))
    (disjunctionRight (Proof.newest _)) (disjunctionLeft (emptyOfDoubleNegation (Proof.newest _)))

/-- **`emptyOrInhabited` at a set described by `0`, from no law**: a member of the first part of a split would be a
member of the set. -/
def emptyOrInhabitedOfEmpty {x : Term Symbol Γ setTy} (described : Proof Δ (describes zero x)) :
    Proof Δ (nativeFormula emptyOrInhabited x Fin.elim0) := by
  refine everySplitIntro (disjunctionLeft ?_)
  rw [nativeFormula_emptyOrInhabitedPart]
  refine disjunctionLeft (.allI (.impI ?_))
  let split : Term Symbol (setTy :: setTy :: Γ) .prop := splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz)
  let found : Term Symbol (setTy :: setTy :: setTy :: Γ) .prop := member (.var .vz) (weaken (.var (.vs .vz)))
  have describedHere : Proof (found :: weakenHyps (split :: weakenHyps (weakenHyps Δ)))
      (describes zero (weaken (weaken (weaken x)))) :=
    ((Proof.cast (by rw [weaken_describes, weaken_describes, weaken_describes]) described.lift.lift.lift).prepend
      (weaken split)).prepend found
  have union := splitAt ((Proof.cast (weaken_splitCore _ _ _)
    (Proof.newest (Δ := weakenHyps (weakenHyps Δ)) split).lift).prepend found) (.var .vz)
  exact Proof.absurd (describesForward describedHere (union.iffBackward (disjunctionLeft (Proof.newest found))))

end Derivations

/-! ## The sentences -/

section Sentences

variable {Δ : List (Term Symbol [] .prop)}

theorem weaken_nativeTypeSentence {σ : Ty Unit} {formula : Formula 0} (regional : formula.regional = true)
    (term : Pattern) :
    weaken (σ := σ) (nativeTypeSentence formula term) =
      existentialInline (σ := setTy) (conjunctionFormula (describes term (.var .vz))
        (nativeFormula formula (.var .vz) Fin.elim0)) := by
  rw [weaken_eq_subst, nativeTypeSentence, subst_existentialInline, subst_conjunctionFormula, subst_describes,
    subst_nativeFormula_regional _ formula regional]
  congr 2
  congr 1
  funext index
  exact index.elim0

/-- The sentence of a native type from its proof at the witness of the term. -/
def sentenceAtWitness (laws : HasLaws Δ) {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) (atWitness : Proof Δ (nativeFormula formula (witness term) Fin.elim0)) :
    Proof Δ (nativeTypeSentence formula term) :=
  existentialIntro (witness term) (Proof.cast (instantiate_sentenceBody regional term (witness term)).symm
    (conjunctionIntro (describedWitness laws term holds) atWitness))

/-- **The sentence of a native type at a term with a member gives a principle**, when the native type gives the
principle at each proposition about a set with a member. -/
def principleOfSentence (laws : HasLaws Δ) {formula : Formula 0} (regional : formula.regional = true)
    {term : Pattern} (holds : IsHF term) {value : Pattern} (found : value ∈ membersOf term)
    {body : Term Symbol [.prop] .prop}
    (atProposition : ∀ {Δ' : List (Term Symbol [setTy, .prop] .prop)}, HasLaws Δ' →
      Proof Δ' (someMemberFormula value (.var .vz)) → Proof Δ' (nativeFormula formula (.var .vz) Fin.elim0) →
        Proof Δ' (weaken (instantiate (.var .vz) (weaken body)))) :
    Proof Δ (.imp (nativeTypeSentence formula term) (.all body)) := by
  refine .impI (.allI (existentialElim (Proof.cast (weaken_nativeTypeSentence regional term)
    ((Proof.newest (Δ := Δ) (nativeTypeSentence formula term)).lift (σ := .prop))) ?_))
  have laws' := (((laws.prepend (nativeTypeSentence formula term)).lift .prop).lift setTy).prepend
    (conjunctionFormula (describes term (.var .vz)) (nativeFormula formula (.var .vz) Fin.elim0))
  refine Proof.cast ?_ (atProposition laws' (someMemberOfMem found (conjunctionRight (describesSomeOfTerm laws' holds
    (conjunctionLeft (Proof.newest _))))) (conjunctionRight (Proof.newest _)))
  rw [Mettapedia.Logic.HOL.instantiate_weaken]

/-- **The sentence of `emptyOrInhabited` at a term with a member gives excluded middle**, over the three laws. -/
def middleOfEmptyOrInhabited (laws : HasLaws Δ) {term : Pattern} (holds : IsHF term) {value : Pattern}
    (found : value ∈ membersOf term) : Proof Δ (.imp (nativeTypeSentence emptyOrInhabited term) middleLaw) :=
  principleOfSentence laws emptyOrInhabited_regional holds found fun laws' inhabitant every =>
    Proof.cast rfl (middleAt laws' inhabitant every (p := .var (.vs .vz)) rfl)

/-- **The sentence of `emptyOrNonEmpty` at a term with a member gives weak excluded middle**, over the three laws. -/
def weakMiddleOfEmptyOrNonEmpty (laws : HasLaws Δ) {term : Pattern} (holds : IsHF term) {value : Pattern}
    (found : value ∈ membersOf term) : Proof Δ (.imp (nativeTypeSentence emptyOrNonEmpty term) weakMiddleLaw) :=
  principleOfSentence laws emptyOrNonEmpty_regional holds found fun laws' inhabitant every =>
    Proof.cast rfl (weakMiddleAt laws' inhabitant every (p := .var (.vs .vz)) rfl)

/-- **Excluded middle gives the sentence of `emptyOrInhabited` at every hereditary term.** -/
def emptyOrInhabitedOfMiddle (laws : HasLaws Δ) {term : Pattern} (holds : IsHF term) :
    Proof Δ (.imp middleLaw (nativeTypeSentence emptyOrInhabited term)) :=
  .impI (sentenceAtWitness (laws.prepend _) emptyOrInhabited_regional holds
    (emptyOrInhabitedFrom (Proof.cast (atContext_middle).symm (Proof.newest _)) _))

/-- **Weak excluded middle gives the sentence of `emptyOrNonEmpty` at every hereditary term.** -/
def emptyOrNonEmptyOfWeakMiddle (laws : HasLaws Δ) {term : Pattern} (holds : IsHF term) :
    Proof Δ (.imp weakMiddleLaw (nativeTypeSentence emptyOrNonEmpty term)) :=
  .impI (sentenceAtWitness (laws.prepend _) emptyOrNonEmpty_regional holds
    (emptyOrNonEmptyFrom (Proof.cast (atContext_nil _).symm (Proof.newest _)) _))

/-- **Excluded middle gives weak excluded middle.** -/
def weakMiddleOfMiddle : Proof Δ (.imp middleLaw weakMiddleLaw) :=
  .impI (.allI (Proof.cast rfl (middleInstance (Proof.cast (weaken_atContext middleLaw)
    (Proof.cast atContext_middle.symm (Proof.newest (Δ := Δ) middleLaw)).lift) (negCore (.var .vz)))))

/-! ## Completeness for the regional fragment is excluded middle -/

theorem one_isHF : IsHF one := (hereditary_iff _).mp (by decide +kernel)

theorem emptyOrInhabited_one : Membership.sat Env.closed emptyOrInhabited one :=
  (decideRegional_iff emptyOrInhabited_regional one_isHF).mp (by decide +kernel)

/-- **Hypotheses with the three laws prove the sentence of every regional native type that holds exactly when they
prove excluded middle.** -/
theorem regionalComplete_iff_middle (laws : HasLaws Δ) :
    (∀ formula : Formula 0, formula.regional = true → ∀ term : Pattern, IsHF term →
      Membership.sat Env.closed formula term → Nonempty (Proof Δ (nativeTypeSentence formula term))) ↔
      Nonempty (Proof Δ middleLaw) := by
  constructor
  · intro complete
    obtain ⟨sentence⟩ := complete emptyOrInhabited emptyOrInhabited_regional one one_isHF emptyOrInhabited_one
    exact ⟨.impE (middleOfEmptyOrInhabited laws one_isHF (value := zero) (List.mem_singleton.mpr rfl)) sentence⟩
  · rintro ⟨middle⟩ formula regional term holds holdsAt
    exact ⟨sentenceProofIn (classical := true)
      { toHasLaws := laws, middle := fun _ => Proof.cast atContext_middle.symm middle }
      (Formula.regionalWith_true formula regional) holds holdsAt⟩

/-! ## At the empty set -/

theorem zero_isHF : IsHF zero := (hereditary_iff _).mp (by decide +kernel)

/-- **At the empty set, the sentence of `emptyOrInhabited` needs no excluded middle**: the first part of a split of a
set described by `0` is empty. -/
def emptyOrInhabitedAtZero (laws : HasLaws Δ) : Proof Δ (nativeTypeSentence emptyOrInhabited zero) :=
  sentenceAtWitness laws emptyOrInhabited_regional zero_isHF
    (emptyOrInhabitedOfEmpty (describedWitness laws zero zero_isHF))

end Sentences


/-! ## In the package of set theory -/

section Package

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseInterpretation (embed)

variable {L : Type} [LevelOrder L]

/-- **In the package of set theory, the sentence of `emptyOrInhabited` at a term with a member and excluded middle
imply each other**, by closed terms. -/
theorem emptyOrInhabited_middle_proofTerms {term : Pattern} (holds : IsHF term) {value : Pattern}
    (found : value ∈ membersOf term) :
    (∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
      (cHolds (trTerm (embed (.imp (nativeTypeSentence emptyOrInhabited term) middleLaw))))) ∧
    (∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
      (cHolds (trTerm (embed (.imp middleLaw (nativeTypeSentence emptyOrInhabited term)))))) :=
  ⟨⟨packageTerm (middleOfEmptyOrInhabited lawsOfList holds found), packageTerm_typed _⟩,
    ⟨packageTerm (emptyOrInhabitedOfMiddle lawsOfList holds), packageTerm_typed _⟩⟩

/-- **In the package of set theory, the sentence of `emptyOrNonEmpty` at a term with a member and weak excluded
middle imply each other**, by closed terms. -/
theorem emptyOrNonEmpty_weakMiddle_proofTerms {term : Pattern} (holds : IsHF term) {value : Pattern}
    (found : value ∈ membersOf term) :
    (∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
      (cHolds (trTerm (embed (.imp (nativeTypeSentence emptyOrNonEmpty term) weakMiddleLaw))))) ∧
    (∃ proofTerm : CTm (Head L) 0, CTyped (setLaws L) .nil proofTerm
      (cHolds (trTerm (embed (.imp weakMiddleLaw (nativeTypeSentence emptyOrNonEmpty term)))))) :=
  ⟨⟨packageTerm (weakMiddleOfEmptyOrNonEmpty lawsOfList holds found), packageTerm_typed _⟩,
    ⟨packageTerm (emptyOrNonEmptyOfWeakMiddle lawsOfList holds), packageTerm_typed _⟩⟩

end Package

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
