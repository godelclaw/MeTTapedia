import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDerivations

/-!
# Working with descriptions said forward and existentially

`describes s x` says that the members of `x` are exactly the sets the members of `s` describe. Its reverse half,
that every set a member describes is in `x`, moves membership on the left of `∈`, which the checker cannot do across
sets with the same members: its calculus has no rule for `=`. The forward and existential form (`describesSome`,
defined with the sentences) says instead that every member of `x` is described by a member of `s`, and that each
member of `s` describes some member of `x`: a back-and-forth between the term's members and the set's, in which every
quantifier is bounded by `x`.

The certificate compiler describes its subjects this way, and their members by full descriptions, which the forward
half hands over. Everything it needs holds of the weaker form:

- it is used member by member (`describesSome_forward`, `describesSome_member`, `someMember`);
- a full description gives it (`describesSome_of_describes`);
- it moves between presentations of one set (`describesSomeSame`);
- two forms of different sets cannot hold of one set (`describesSomeDistinct`).

None of these moves membership on the left of a described set; the reverse half is used only for members.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term weaken rename subst instantiate Subst Rename weakenHyps)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.ImpredicativeConnectives.Modulo (truthIntro conjunctionIntro conjunctionLeft
  conjunctionRight disjunctionLeft disjunctionRight disjunctionElim existentialIntro existentialElim)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member)

section Using

variable {Γ : Ctx Unit} {Δ : List (Term Symbol Γ .prop)}

/-- `∃ z ∈ x. z is described by the term`. -/
abbrev someMemberFormula (value : Pattern) (x : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken x)) (describes value (.var .vz)))

theorem weaken_describesSome {σ : Ty Unit} (values : List Pattern) (x : Term Symbol Γ setTy) :
    weaken (σ := σ) (describesSome values x) = describesSome values (weaken x) := by
  rw [weaken_eq_subst, subst_describesSome, ← weaken_eq_subst]

theorem weaken_someMemberFormula {σ : Ty Unit} (value : Pattern) (x : Term Symbol Γ setTy) :
    weaken (σ := σ) (someMemberFormula value x) = someMemberFormula value (weaken x) := by
  rw [weaken_eq_subst]
  simp only [someMemberFormula, subst_existentialInline, subst_conjunctionFormula, member, subst, subst_describes,
    Mettapedia.Logic.HOL.subst_weaken, ← weaken_eq_subst]
  rfl

theorem describesSomeOf_set {term : Pattern} (holds : IsHF term) (x : Term Symbol Γ setTy) :
    describesSomeOf term x = describesSome (membersOf term) x := by
  conv_lhs => rw [hf_eq_set holds]
  rfl

/-- A forward and existential description under a new variable and a new hypothesis. -/
def describesSomeUnder {values : List Pattern} {x : Term Symbol Γ setTy} (described : Proof Δ (describesSome values x))
    (σ : Ty Unit) (ψ : Term Symbol (σ :: Γ) .prop) : Proof (ψ :: weakenHyps (σ := σ) Δ) (describesSome values (weaken x)) :=
  (Proof.cast (weaken_describesSome _ _) described.lift).prepend ψ

theorem instantiate_someForward (values : List Pattern) (x y : Term Symbol Γ setTy) :
    instantiate y (.imp (member (.var .vz) (weaken x)) (describesOne values (.var .vz))) =
      .imp (member y x) (describesOne values y) := by
  unfold instantiate
  simp only [subst, subst_describesOne]
  congr 1
  show member y (subst (Subst.single y) (weaken x)) = member y x
  rw [← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

theorem instantiate_someMember (value : Pattern) (x w : Term Symbol Γ setTy) :
    instantiate w (conjunctionFormula (member (.var .vz) (weaken x)) (describes value (.var .vz))) =
      conjunctionFormula (member w x) (describes value w) := by
  unfold instantiate
  rw [subst_conjunctionFormula, subst_describes]
  congr 1
  show member w (subst (Subst.single w) (weaken x)) = member w x
  rw [← instantiate, Mettapedia.Logic.HOL.instantiate_weaken]

/-- **Every member of `x` is described by a listed term.** -/
def describesSome_forward {values : List Pattern} {x y : Term Symbol Γ setTy}
    (described : Proof Δ (describesSome values x)) (isMember : Proof Δ (member y x)) : Proof Δ (describesOne values y) :=
  .impE (Proof.cast (instantiate_someForward values x y) (.allE y (conjunctionLeft described))) isMember

def eachDescribed_get : ∀ {values : List Pattern} (index : Fin values.length) {x : Term Symbol Γ setTy},
    Proof Δ (eachDescribed values x) → Proof Δ (someMemberFormula (values.get index) x)
  | _ :: _, ⟨0, _⟩, _, each => conjunctionLeft each
  | _ :: _, ⟨k + 1, small⟩, _, each => eachDescribed_get ⟨k, Nat.lt_of_succ_lt_succ small⟩ (conjunctionRight each)

/-- **Each listed term describes some member of `x`.** -/
def describesSome_member {values : List Pattern} {x : Term Symbol Γ setTy} (described : Proof Δ (describesSome values x))
    (index : Fin values.length) : Proof Δ (someMemberFormula (values.get index) x) :=
  eachDescribed_get index (conjunctionRight described)

/-- **Using a member that a listed term describes**: the goal, proved from a new member of `x` and its description. -/
def someMember {values : List Pattern} {x : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop}
    (described : Proof Δ (describesSome values x)) (index : Fin values.length)
    (use : Proof (conjunctionFormula (member (.var .vz) (weaken x)) (describes (values.get index) (.var .vz)) ::
      weakenHyps (σ := setTy) Δ) (weaken goal)) : Proof Δ goal :=
  existentialElim (describesSome_member described index) use

/-- Each listed term describing a member, assembled from one proof per term. -/
def eachDescribedOfComponents {x : Term Symbol Γ setTy} : ∀ {values : List Pattern},
    (∀ index : Fin values.length, Proof Δ (someMemberFormula (values.get index) x)) → Proof Δ (eachDescribed values x)
  | [], _ => truthIntro
  | _ :: _, each => conjunctionIntro (each ⟨0, Nat.succ_pos _⟩) (eachDescribedOfComponents fun index => each index.succ)

/-- A member described by one term is described by another, when the second describes what the first does. -/
def someMemberMap {value other : Pattern} {x : Term Symbol Γ setTy} (found : Proof Δ (someMemberFormula value x))
    (along : ∀ {Γ' : Ctx Unit} {Δ' : List (Term Symbol Γ' .prop)} (z : Term Symbol Γ' setTy),
      Proof Δ' (describes value z) → Proof Δ' (describes other z)) : Proof Δ (someMemberFormula other x) :=
  existentialElim found (Proof.cast (weaken_someMemberFormula other x).symm
    (existentialIntro (.var .vz) (Proof.cast (instantiate_someMember other (weaken x) (.var .vz)).symm
      (conjunctionIntro (conjunctionLeft (Proof.newest _)) (along _ (conjunctionRight (Proof.newest _)))))))

/-- A set described by a listed term is described by one of the list. -/
def oneIntroOfMem {y : Term Symbol Γ setTy} {value : Pattern} (proof : Proof Δ (describes value y)) :
    ∀ (values : List Pattern), value ∈ values → Proof Δ (describesOne values y)
  | [], member => absurd member List.not_mem_nil
  | head :: rest, member =>
    if same : value = head then disjunctionLeft (same ▸ proof)
    else disjunctionRight (oneIntroOfMem proof rest ((List.mem_cons.mp member).resolve_left same))

def eachDescribedOf (laws : HasLaws Δ) {all : List Pattern} {x : Term Symbol Γ setTy}
    (described : Proof Δ (describes (set all) x)) :
    ∀ (values : List Pattern), (∀ value ∈ values, IsHF value) → (∀ value ∈ values, value ∈ all) →
      Proof Δ (eachDescribed values x)
  | [], _, _ => truthIntro
  | value :: values, hereditary, inside =>
    conjunctionIntro
      (existentialIntro (witness value) (Proof.cast (instantiate_someMember value x (witness value)).symm
        (conjunctionIntro
          (describesBackward described (oneIntroOfMem (describedWitness laws value (hereditary value List.mem_cons_self))
            all (inside value List.mem_cons_self)))
          (describedWitness laws value (hereditary value List.mem_cons_self)))))
      (eachDescribedOf laws described values (fun other member => hereditary other (List.mem_cons_of_mem _ member))
        fun other member => inside other (List.mem_cons_of_mem _ member))

/-- **A description gives the forward and existential form.** -/
def describesSome_of_describes (laws : HasLaws Δ) {values : List Pattern} (hereditary : ∀ value ∈ values, IsHF value)
    {x : Term Symbol Γ setTy} (described : Proof Δ (describes (set values) x)) : Proof Δ (describesSome values x) :=
  conjunctionIntro (.allI (.impI (describesForward ((Proof.cast (weaken_describes _ _) described.lift).prepend _)
      (Proof.newest _))))
    (eachDescribedOf laws described values hereditary fun _ member => member)

/-- **A description of a hereditary term gives the forward and existential form of its members.** -/
def describesSomeOfTerm (laws : HasLaws Δ) {term : Pattern} (holds : IsHF term) {x : Term Symbol Γ setTy}
    (described : Proof Δ (describes term x)) : Proof Δ (describesSome (membersOf term) x) :=
  describesSome_of_describes laws (hf_members holds)
    (Proof.cast (congrArg (describes · x) (hf_eq_set holds)) described)

/-- **The forward and existential form moves between presentations of one set.** -/
def describesSomeSame {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other)
    (same : zfOf term = zfOf other) {x : Term Symbol Γ setTy} (described : Proof Δ (describesSome (membersOf term) x)) :
    Proof Δ (describesSome (membersOf other) x) :=
  conjunctionIntro
    (.allI (.impI (oneCases (membersOf term) (describesSome_forward (describesSomeUnder described setTy _)
      (Proof.newest _)) fun index => oneIntro (membersOf other) (matchingIndex holds holdsOther same index).1
        (describesSame _ _ (hf_members holds _ (List.get_mem _ _)) (hf_members holdsOther _ (List.get_mem _ _))
          (matchingIndex holds holdsOther same index).2 (.var .vz) (Proof.newest _)))))
    (eachDescribedOfComponents fun index' =>
      someMemberMap (describesSome_member described (matchingIndex holdsOther holds same.symm index').1)
        fun z found => describesSame _ _ (hf_members holds _ (List.get_mem _ _))
          (hf_members holdsOther _ (List.get_mem _ _)) (matchingIndex holdsOther holds same.symm index').2.symm z found)

/-- **Forward and existential forms of different sets hold of no common set.** -/
def describesSomeDistinct (laws : HasLaws Δ) {term other : Pattern} (holds : IsHF term) (holdsOther : IsHF other)
    (differ : zfOf term ≠ zfOf other) {x : Term Symbol Γ setTy} (described : Proof Δ (describesSome (membersOf term) x))
    (describedOther : Proof Δ (describesSome (membersOf other) x)) : Proof Δ falsity :=
  if left : (membersOf term).any (apartFrom other) = true then
    have apart := (apartFrom_iff (hf_members holds _ (List.get_mem _ _)) holdsOther).mp
      (chooseIndex (membersOf term) (apartFrom other) (List.any_eq_true.mp left)).2
    someMember described (chooseIndex (membersOf term) (apartFrom other) (List.any_eq_true.mp left)).1
      (oneCases (membersOf other) (describesSome_forward (describesSomeUnder describedOther setTy _)
        (conjunctionLeft (Proof.newest _))) fun index' =>
          describesDistinct (((laws.lift setTy).prepend _).prepend _) _ ((membersOf other).get index')
            (hf_members holds _ (List.get_mem _ _)) (hf_members holdsOther _ (List.get_mem _ _)) (apart index')
            (.var .vz) (Proof.prepend _ (conjunctionRight (Proof.newest _))) (Proof.newest _))
  else
    have matched : ¬ ∃ index : Fin (membersOf term).length, ∀ index' : Fin (membersOf other).length,
        zfOf ((membersOf term).get index) ≠ zfOf ((membersOf other).get index') := by
      rintro ⟨index, apart⟩
      exact left (List.any_eq_true.mpr ⟨_, List.get_mem _ index,
        (apartFrom_iff (hf_members holds _ (List.get_mem _ _)) holdsOther).mpr apart⟩)
    have exists' : ∃ value ∈ membersOf other, apartFrom term value = true := by
      obtain ⟨index', apart⟩ := unmatched_member holds holdsOther differ matched
      exact ⟨_, List.get_mem _ index', (apartFrom_iff (hf_members holdsOther _ (List.get_mem _ _)) holds).mpr
        fun index same => apart index same.symm⟩
    have apart := (apartFrom_iff (hf_members holdsOther _ (List.get_mem _ _)) holds).mp
      (chooseIndex (membersOf other) (apartFrom term) exists').2
    someMember describedOther (chooseIndex (membersOf other) (apartFrom term) exists').1
      (oneCases (membersOf term) (describesSome_forward (describesSomeUnder described setTy _)
        (conjunctionLeft (Proof.newest _))) fun index =>
          describesDistinct (((laws.lift setTy).prepend _).prepend _) ((membersOf term).get index) _
            (hf_members holds _ (List.get_mem _ _)) (hf_members holdsOther _ (List.get_mem _ _))
            (fun same => apart index same.symm) (.var .vz) (Proof.newest _)
            (Proof.prepend _ (conjunctionRight (Proof.newest _))))

/-- A member a listed term describes, with its membership and its description as separate hypotheses. -/
def someMemberHyps {values : List Pattern} {x : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop}
    (described : Proof Δ (describesSome values x)) (index : Fin values.length)
    (use : Proof (describes (values.get index) (.var .vz) :: member (.var .vz) (weaken x) ::
      conjunctionFormula (member (.var .vz) (weaken x)) (describes (values.get index) (.var .vz)) ::
        weakenHyps (σ := setTy) Δ) (weaken goal)) : Proof Δ goal :=
  someMember described index
    (.impE (.impE (.impI (.impI use)) (conjunctionLeft (Proof.newest _))) (conjunctionRight (Proof.newest _)))

/-! ## Described by one of a list of terms, forward and existentially -/

theorem isCore_existentialInline {σ : Ty Unit} {body : Term Symbol (σ :: Γ) .prop} (core : body.isCore = true) :
    (existentialInline body).isCore = true := by
  simp only [existentialInline, Mettapedia.Logic.HOL.Term.isCore, Mettapedia.Logic.HOL.Term.isCore_rename, core,
    Bool.and_self]

theorem isCore_eachDescribed : ∀ (values : List Pattern) {x : Term Symbol Γ setTy}, x.isCore = true →
    (eachDescribed values x).isCore = true
  | [], _, _ => rfl
  | value :: values, x, coreX => isCore_conjunctionFormula
      (isCore_existentialInline (isCore_conjunctionFormula
        (isCore_member rfl (by simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, coreX]))
        (isCore_describes value rfl)))
      (isCore_eachDescribed values coreX)

theorem isCore_describesSome (values : List Pattern) {x : Term Symbol Γ setTy} (coreX : x.isCore = true) :
    (describesSome values x).isCore = true :=
  isCore_conjunctionFormula
    (by
      have memberCore : (member (.var .vz) (weaken x) : Term Symbol (setTy :: Γ) .prop).isCore = true :=
        isCore_member rfl (by simp only [weaken, Mettapedia.Logic.HOL.Term.isCore_rename, coreX])
      have oneCore := isCore_describesOne values (y := (.var .vz : Term Symbol (setTy :: Γ) setTy)) rfl
      simp only [Mettapedia.Logic.HOL.Term.isCore, memberCore, oneCore, Bool.and_self])
    (isCore_eachDescribed values coreX)

/-- **The set term is described, forward and existentially, by one of the terms.** -/
def someOne : List Pattern → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | [], _, _ => falsity
  | term :: terms, _, y => disjunctionFormula (describesSome (membersOf term) y) (someOne terms y)

theorem subst_someOne {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (terms : List Pattern) (y : Term Symbol Γ setTy), subst θ (someOne terms y) = someOne terms (subst θ y)
  | [], _ => rfl
  | term :: terms, y => by
    simp only [someOne, subst_disjunctionFormula, subst_describesSome, subst_someOne θ terms y]

theorem weaken_someOne {σ : Ty Unit} (terms : List Pattern) (y : Term Symbol Γ setTy) :
    weaken (σ := σ) (someOne terms y) = someOne terms (weaken y) := by
  rw [weaken_eq_subst, subst_someOne, ← weaken_eq_subst]

theorem instantiate_someOne (terms : List Pattern) (y : Term Symbol Γ setTy) :
    instantiate y (someOne terms (.var .vz)) = someOne terms y := by
  unfold instantiate
  rw [subst_someOne]
  rfl

theorem isCore_someOne : ∀ (terms : List Pattern) {y : Term Symbol Γ setTy}, y.isCore = true →
    (someOne terms y).isCore = true
  | [], _, _ => rfl
  | _ :: terms, _, coreY => isCore_disjunctionFormula (isCore_describesSome _ coreY) (isCore_someOne terms coreY)

/-- A set described by one listed term is described by one of the list. -/
def someOneIntro {y : Term Symbol Γ setTy} : ∀ (terms : List Pattern) (index : Fin terms.length),
    Proof Δ (describesSome (membersOf (terms.get index)) y) → Proof Δ (someOne terms y)
  | _ :: _, ⟨0, _⟩, proof => disjunctionLeft proof
  | _ :: terms, ⟨k + 1, small⟩, proof => disjunctionRight (someOneIntro terms ⟨k, Nat.lt_of_succ_lt_succ small⟩ proof)

/-- Cases on which listed term describes a set. -/
def someOneCases {y : Term Symbol Γ setTy} {goal : Term Symbol Γ .prop} : ∀ {Δ : List (Term Symbol Γ .prop)}
    (terms : List Pattern), Proof Δ (someOne terms y) →
      (∀ index : Fin terms.length, Proof (describesSome (membersOf (terms.get index)) y :: Δ) goal) → Proof Δ goal
  | _, [], one, _ => Proof.absurd one
  | Δ, _ :: terms, one, branch =>
    disjunctionElim one (branch ⟨0, Nat.succ_pos _⟩)
      (someOneCases (Δ := someOne terms y :: Δ) terms (Proof.newest _) fun index =>
        Proof.insertSecond _ (branch index.succ))

end Using

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
