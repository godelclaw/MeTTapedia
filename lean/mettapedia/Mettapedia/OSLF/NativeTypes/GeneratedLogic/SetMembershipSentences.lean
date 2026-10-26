import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipKernel
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# Native types of the membership language as core sentences of set theory

The checker of the package of set theory reads proofs of implication and universal quantification, modulo
conversion; the other connectives are their impredicative definitions. This module writes the native types of the
membership language in that grammar directly, about a given set term, with no abstraction applied to an argument,
so that proofs can be built for them (`SetMembershipProofs`).

- **Description of a hereditary term** (`describes s x`): the members of `x` are exactly the sets the members of
  `s` describe. It holds of exactly the set the term denotes (`denote_describes`).
- **Types** (`typedFormula`): every set is a `Set`, and a set is a set-collection of elements of a type when each
  member is (`denote_typedFormula`).
- **Same members** (`sameMembers`, `onlyMember`): equality of sets is written extensionally, by membership, since the
  checker has no rules for the primitive equality of the extensionality law.
- **Counting** (`countWith`): at least `k` members have a property when some member has it and at least `k - 1` of
  the members other than it do, the others being separated out (`withoutSame`). It means counting distinct members
  (`denote_countWith`, `countIn_iff_atLeast`).
- **Native types** (`nativeFormula φ x θ`), for the modal fragment (`Formula.modal`): conjunction, disjunction,
  fixed points, steps by label, named terms, emptiness, types, one-element sets, and counting of the members, with
  their duals. A fixed-point variable is a predicate term, applied to the subject. On the fragment the formula is true
  exactly where the native type holds on the ZF sets (`denote_nativeFormula`).
- **Splits** (`splitCore`): the regional fragment (`Formula.regional`) adds splits and their duals; a split of `x` is
  a pair of sets whose union it is. The formulas of the regional fragment are true exactly where their native types
  hold (`denote_nativeFormula_regional`).
- **The sentence of a native type of a term** (`nativeTypeSentence`): some set is described by the term and has the
  native type. For a regional formula and a hereditary term it is true in the model of the sets exactly when the term
  has the native type (`models_nativeTypeSentence`, `denote_nativeTypeSentence_regional`).
- **Substitution** commutes with all of them (`subst_describes`, `subst_typedFormula`, `subst_countWith`,
  `subst_nativeFormula_regional`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula HenkinModel weaken rename subst instantiate Subst Rename)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (truth falsity conjunctionFormula disjunctionFormula
  existentialInline subst_conjunctionFormula subst_disjunctionFormula subst_existentialInline)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol model member separate)

/-- Predicates on sets. -/
abbrev predTy : Ty Unit := Ty.arr setTy .prop

/-! ## Core connectives -/

section Connectives

variable {Γ : Ctx Unit}

/-- `¬p`, as `p → ⊥`. -/
def negCore (p : Term Symbol Γ .prop) : Term Symbol Γ .prop := .imp p falsity

/-- `p ↔ q`, as a conjunction of implications. -/
def iffCore (p q : Term Symbol Γ .prop) : Term Symbol Γ .prop := conjunctionFormula (.imp p q) (.imp q p)

theorem subst_negCore {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (p : Term Symbol Γ .prop) :
    subst θ (negCore p) = negCore (subst θ p) := rfl

theorem subst_iffCore {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (p q : Term Symbol Γ .prop) :
    subst θ (iffCore p q) = iffCore (subst θ p) (subst θ q) := by
  simp only [iffCore, subst_conjunctionFormula]
  rfl

variable {M : HenkinModel.{0, 0, 1} Unit Symbol} (valuation : M.Valuation Γ)

theorem denote_truth : (M.denote (truth : Term Symbol Γ .prop) valuation).down :=
  fun _ _ inside => inside

theorem denote_falsity : (M.denote (falsity : Term Symbol Γ .prop) valuation).down ↔ False :=
  ⟨fun every => every (.up False) (M.prop_mem _), False.elim⟩

theorem denote_conjunctionFormula (p q : Term Symbol Γ .prop) :
    (M.denote (conjunctionFormula p q) valuation).down ↔ (M.denote p valuation).down ∧ (M.denote q valuation).down := by
  change (∀ r, M.adm .prop r → ((M.denote (weaken p) (M.extend valuation r)).down →
    (M.denote (weaken q) (M.extend valuation r)).down → r.down) → r.down) ↔ _
  simp only [Mettapedia.Logic.HOL.Soundness.denote_weaken]
  exact ⟨fun every => every (.up _) (M.prop_mem _) And.intro, fun ⟨left, right⟩ _ _ use => use left right⟩

theorem denote_disjunctionFormula (p q : Term Symbol Γ .prop) :
    (M.denote (disjunctionFormula p q) valuation).down ↔ (M.denote p valuation).down ∨ (M.denote q valuation).down := by
  change (∀ r, M.adm .prop r → ((M.denote (weaken p) (M.extend valuation r)).down → r.down) →
    ((M.denote (weaken q) (M.extend valuation r)).down → r.down) → r.down) ↔ _
  simp only [Mettapedia.Logic.HOL.Soundness.denote_weaken]
  exact ⟨fun every => every (.up _) (M.prop_mem _) Or.inl Or.inr, fun found _ _ left right => found.elim left right⟩

theorem denote_existentialInline {σ : Ty Unit} (body : Term Symbol (σ :: Γ) .prop) :
    (M.denote (existentialInline body) valuation).down ↔
      ∃ value, M.adm σ value ∧ (M.denote body (M.extend valuation value)).down := by
  change (∀ r, M.adm .prop r → (∀ value, M.adm σ value →
    (M.denote (rename (Rename.lift Rename.weaken) body) (M.extend (M.extend valuation r) value)).down → r.down) →
      r.down) ↔ _
  have unweakened : ∀ (r : Ty.denote M.Carrier .prop) (value : Ty.denote M.Carrier σ),
      M.denote (rename (Rename.lift (Rename.weaken (σ := .prop))) body) (M.extend (M.extend valuation r) value) =
        M.denote body (M.extend valuation value) := by
    intro r value
    rw [Mettapedia.Logic.HOL.Soundness.denote_rename]
    congr 1
    funext τ index
    cases index <;> rfl
  simp only [unweakened]
  exact ⟨fun every => every (.up _) (M.prop_mem _) fun value admitted inside => ⟨value, admitted, inside⟩,
    fun ⟨value, admitted, inside⟩ _ _ use => use value admitted inside⟩

theorem denote_negCore (p : Term Symbol Γ .prop) :
    (M.denote (negCore p) valuation).down ↔ ¬ (M.denote p valuation).down := by
  change ((M.denote p valuation).down → (M.denote falsity valuation).down) ↔ _
  rw [denote_falsity]

theorem denote_iffCore (p q : Term Symbol Γ .prop) :
    (M.denote (iffCore p q) valuation).down ↔ ((M.denote p valuation).down ↔ (M.denote q valuation).down) := by
  rw [iffCore, denote_conjunctionFormula]
  exact ⟨fun ⟨forward, backward⟩ => ⟨forward, backward⟩, fun same => ⟨same.1, same.2⟩⟩

end Connectives

/-! ## Values of set terms -/

/-- The set a set term denotes at a valuation of the model of the sets. -/
noncomputable def setValue {Γ : Ctx Unit} (x : Term Symbol Γ setTy) (valuation : model.{0}.Valuation Γ) : ZFSet.{0} :=
  model.denote x valuation

theorem denote_member {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (y x : Term Symbol Γ setTy) :
    (model.denote (member y x) valuation).down ↔ setValue y valuation ∈ setValue x valuation := Iff.rfl

theorem setValue_weaken {Γ : Ctx Unit} {σ : Ty Unit} (x : Term Symbol Γ setTy) (valuation : model.{0}.Valuation Γ)
    (value : Ty.denote model.{0}.Carrier σ) :
    setValue (weaken x) (model.extend valuation value) = setValue x valuation :=
  Mettapedia.Logic.HOL.Soundness.denote_weaken model x valuation value

@[simp] theorem setValue_weaken_set {Γ : Ctx Unit} (x : Term Symbol Γ setTy) (valuation : model.{0}.Valuation Γ)
    (z : ZFSet.{0}) : setValue (weaken x) (model.extend (σ := setTy) valuation z) = setValue x valuation :=
  setValue_weaken (σ := setTy) x valuation z

@[simp] theorem setValue_weaken_pred {Γ : Ctx Unit} (x : Term Symbol Γ setTy) (valuation : model.{0}.Valuation Γ)
    (value : Ty.denote model.{0}.Carrier predTy) :
    setValue (weaken x) (model.extend (σ := predTy) valuation value) = setValue x valuation :=
  setValue_weaken x valuation value

theorem setValue_newest {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (z : ZFSet.{0}) :
    setValue (.var .vz) (model.extend (σ := setTy) valuation z) = z := rfl

/-! ## Descriptions of hereditary terms -/

mutual
/-- **The set term `x` is the set `s` denotes**: its members are exactly the sets the members of `s` describe. -/
def describes : Pattern → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | .collection _ values _, _, x => .all (iffCore (member (.var .vz) (weaken x)) (describesOne values (.var .vz)))
  | .bvar _, _, _ => falsity
  | .fvar _, _, _ => falsity
  | .apply _ _, _, _ => falsity
  | .lambda _ _, _, _ => falsity
  | .multiLambda _ _ _, _, _ => falsity
  | .subst _ _, _, _ => falsity

/-- The set term is described by one of the terms. -/
def describesOne : List Pattern → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | [], _, _ => falsity
  | value :: values, _, y => disjunctionFormula (describes value y) (describesOne values y)
end

mutual
theorem subst_describes {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (term : Pattern) (x : Term Symbol Γ setTy), subst θ (describes term x) = describes term (subst θ x)
  | .collection _ values _, x => by
    simp only [describes, subst, subst_iffCore, member, Mettapedia.Logic.HOL.subst_weaken, subst_describesOne]
    rfl
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ _, _ => rfl
  | .lambda _ _, _ => rfl
  | .multiLambda _ _ _, _ => rfl
  | .subst _ _, _ => rfl

theorem subst_describesOne {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (values : List Pattern) (y : Term Symbol Γ setTy),
      subst θ (describesOne values y) = describesOne values (subst θ y)
  | [], _ => rfl
  | value :: values, y => by
    simp only [describesOne, subst_disjunctionFormula, subst_describes θ value y, subst_describesOne θ values y]
end

theorem denote_describesOne {values : List Pattern}
    (inside : ∀ value ∈ values, ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy),
      (model.denote (describes value x) valuation).down ↔ setValue x valuation = zfOf value)
    {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (y : Term Symbol Γ setTy) :
    (model.denote (describesOne values y) valuation).down ↔ ∃ value ∈ values, setValue y valuation = zfOf value := by
  induction values with
  | nil => exact (denote_falsity valuation).trans ⟨False.elim, fun ⟨_, member, _⟩ => nomatch member⟩
  | cons value values ih =>
    rw [describesOne, denote_disjunctionFormula, inside value List.mem_cons_self valuation y,
      ih fun other member => inside other (List.mem_cons_of_mem _ member)]
    constructor
    · rintro (same | ⟨other, member, same⟩)
      · exact ⟨value, List.mem_cons_self, same⟩
      · exact ⟨other, List.mem_cons_of_mem _ member, same⟩
    · rintro ⟨other, member, same⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl same
      · exact Or.inr ⟨other, member, same⟩

/-- **A hereditary term's description holds exactly at the set the term denotes.** -/
theorem denote_describes {term : Pattern} (holds : IsHF term) :
    ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy),
      (model.denote (describes term x) valuation).down ↔ setValue x valuation = zfOf term := by
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values _ inside =>
    intro Γ valuation x
    change (∀ z : ZFSet.{0}, True → (model.denote (iffCore (member (.var .vz) (weaken x)) (describesOne values (.var .vz)))
      (model.extend (σ := setTy) valuation z)).down) ↔ _
    simp only [denote_iffCore, true_implies, denote_member, setValue_weaken_set, setValue_newest,
      denote_describesOne inside, zfOf_set]
    constructor
    · intro every
      apply ZFSet.ext
      intro z
      rw [every z, mem_zfOfList]
      exact ⟨fun ⟨value, member, same⟩ => ⟨value, member, same.symm⟩,
        fun ⟨value, member, same⟩ => ⟨value, member, same.symm⟩⟩
    · intro same z
      rw [same, mem_zfOfList]
      exact ⟨fun ⟨value, member, same⟩ => ⟨value, member, same.symm⟩,
        fun ⟨value, member, same⟩ => ⟨value, member, same.symm⟩⟩

/-! ## Descriptions said forward and existentially -/

/-- **Each listed term describes a member of `x`.** -/
def eachDescribed : List Pattern → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | [], _, _ => truth
  | value :: values, _, x => conjunctionFormula
      (existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken x)) (describes value (.var .vz))))
      (eachDescribed values x)

/-- **`x` has the members the listed terms describe, said forward and existentially**: every member of `x` is
described by a listed term, and each listed term describes some member of `x`. Every quantifier is bounded by `x`,
and nothing moves membership on the left of a described set. -/
def describesSome {Γ : Ctx Unit} (values : List Pattern) (x : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  conjunctionFormula (.all (.imp (member (.var .vz) (weaken x)) (describesOne values (.var .vz))))
    (eachDescribed values x)

/-- The forward and existential description of a term's set. -/
def describesSomeOf : Pattern → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | .collection _ values _, _, x => describesSome values x
  | _, _, _ => falsity

theorem subst_eachDescribed {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (values : List Pattern) (x : Term Symbol Γ setTy), subst θ (eachDescribed values x) = eachDescribed values (subst θ x)
  | [], _ => rfl
  | value :: values, x => by
    simp only [eachDescribed, subst_conjunctionFormula, subst_existentialInline, member, subst, subst_describes,
      Mettapedia.Logic.HOL.subst_weaken, subst_eachDescribed θ values x]
    rfl

theorem subst_describesSome {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (values : List Pattern) (x : Term Symbol Γ setTy) :
    subst θ (describesSome values x) = describesSome values (subst θ x) := by
  simp only [describesSome, subst_conjunctionFormula, member, subst, subst_describesOne,
    Mettapedia.Logic.HOL.subst_weaken, subst_eachDescribed]
  rfl

theorem subst_describesSomeOf {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (term : Pattern) (x : Term Symbol Γ setTy), subst θ (describesSomeOf term x) = describesSomeOf term (subst θ x)
  | .collection _ values _, x => subst_describesSome θ values x
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ _, _ => rfl
  | .lambda _ _, _ => rfl
  | .multiLambda _ _ _, _ => rfl
  | .subst _ _, _ => rfl

theorem denote_eachDescribed {values : List Pattern} (inside : ∀ value ∈ values, IsHF value) {Γ : Ctx Unit}
    (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) :
    (model.denote (eachDescribed values x) valuation).down ↔ ∀ value ∈ values, zfOf value ∈ setValue x valuation := by
  induction values with
  | nil => exact ⟨fun _ _ member => (nomatch member), fun _ => denote_truth valuation⟩
  | cons value values ih =>
    rw [eachDescribed, denote_conjunctionFormula, denote_existentialInline,
      ih fun other member => inside other (List.mem_cons_of_mem _ member)]
    simp only [denote_conjunctionFormula, denote_member, denote_describes (inside value List.mem_cons_self),
      List.forall_mem_cons]
    constructor
    · rintro ⟨⟨z, -, member, rfl⟩, rest⟩
      refine ⟨?_, rest⟩
      rw [← setValue_weaken_set x valuation (zfOf value)]
      exact member
    · rintro ⟨member, rest⟩
      refine ⟨⟨zfOf value, trivial, ?_, rfl⟩, rest⟩
      show zfOf value ∈ setValue (weaken x) (model.extend (σ := setTy) valuation (zfOf value))
      rw [setValue_weaken_set]
      exact member

/-- **Among the sets, the forward and existential form says that `x` is the set of the listed terms.** -/
theorem denote_describesSome {values : List Pattern} (inside : ∀ value ∈ values, IsHF value) {Γ : Ctx Unit}
    (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) :
    (model.denote (describesSome values x) valuation).down ↔ setValue x valuation = zfOfList values := by
  rw [describesSome, denote_conjunctionFormula, denote_eachDescribed inside]
  change (∀ z : ZFSet.{0}, True → (model.denote (.imp (member (.var .vz) (weaken x)) (describesOne values (.var .vz)))
    (model.extend (σ := setTy) valuation z)).down) ∧ _ ↔ _
  simp only [true_implies]
  change (∀ z : ZFSet.{0}, (model.denote (member (.var .vz) (weaken x)) (model.extend (σ := setTy) valuation z)).down →
    (model.denote (describesOne values (.var .vz)) (model.extend (σ := setTy) valuation z)).down) ∧ _ ↔ _
  simp only [denote_member, setValue_weaken_set, setValue_newest,
    denote_describesOne (fun value member => denote_describes (inside value member))]
  constructor
  · rintro ⟨forward, each⟩
    apply ZFSet.ext
    intro z
    rw [mem_zfOfList]
    exact ⟨fun member => (forward z member).imp fun _ found => ⟨found.1, found.2.symm⟩,
      fun ⟨value, member, same⟩ => same ▸ each value member⟩
  · intro same
    refine ⟨fun z member => ?_, fun value member => ?_⟩
    · rw [same, mem_zfOfList] at member
      exact member.imp fun _ found => ⟨found.1, found.2.symm⟩
    · rw [same]
      exact mem_zfOfList.mpr ⟨value, member, rfl⟩

/-- **A hereditary term's forward and existential description holds exactly at its set.** -/
theorem denote_describesSomeOf {term : Pattern} (holds : IsHF term) {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ)
    (x : Term Symbol Γ setTy) :
    (model.denote (describesSomeOf term x) valuation).down ↔ setValue x valuation = zfOf term := by
  cases holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values inside =>
    change (model.denote (describesSome values x) valuation).down ↔ _
    rw [denote_describesSome inside, zfOf_set]

/-! ## Types -/

/-- **The set term has the type**: every set is a `Set`; a set is a set-collection of elements of a type when each
member has that type. -/
def typedFormula : TypeExpr → {Γ : Ctx Unit} → Term Symbol Γ setTy → Term Symbol Γ .prop
  | .base sort, _, _ => if sort = "Set" then truth else falsity
  | .collection kind element, _, x =>
    if kind = .hashSet then .all (.imp (member (.var .vz) (weaken x)) (typedFormula element (.var .vz))) else falsity
  | .arrow _ _, _, _ => falsity
  | .multiBinder _, _, _ => falsity

theorem subst_typedFormula {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ (type : TypeExpr) (x : Term Symbol Γ setTy), subst θ (typedFormula type x) = typedFormula type (subst θ x)
  | .base sort, _ => by
    unfold typedFormula
    split_ifs <;> rfl
  | .collection kind element, x => by
    unfold typedFormula
    split_ifs
    · simp only [subst, member, Mettapedia.Logic.HOL.subst_weaken, subst_typedFormula _ element]
      rfl
    · rfl
  | .arrow _ _, _ => rfl
  | .multiBinder _, _ => rfl

theorem denote_typedFormula : ∀ (type : TypeExpr) {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ)
    (x : Term Symbol Γ setTy), (model.denote (typedFormula type x) valuation).down ↔ SetTyped (setValue x valuation) type
  | .base sort, _, valuation, x => by
    by_cases named : sort = "Set"
    · simp only [typedFormula, if_pos named]
      exact iff_of_true (denote_truth valuation) named
    · simp only [typedFormula, if_neg named]
      exact (denote_falsity valuation).trans (iff_of_false id named)
  | .collection kind element, _, valuation, x => by
    by_cases set : kind = .hashSet
    · simp only [typedFormula, if_pos set]
      change (∀ z : ZFSet.{0}, True → (model.denote (member (.var .vz) (weaken x)) (model.extend (σ := setTy) valuation z)).down →
        (model.denote (typedFormula element (.var .vz)) (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_implies, denote_member, setValue_weaken_set, setValue_newest, denote_typedFormula element]
      exact ⟨fun every => ⟨set, every⟩, fun found => found.2⟩
    · simp only [typedFormula, if_neg set]
      exact (denote_falsity valuation).trans (iff_of_false id fun found => set found.1)
  | .arrow _ _, _, valuation, _ => (denote_falsity valuation).trans (iff_of_false id id)
  | .multiBinder _, _, valuation, _ => (denote_falsity valuation).trans (iff_of_false id id)

/-! ## Same members -/

section SameMembers

variable {Γ : Ctx Unit}

/-- `∀ w. w ∈ y ↔ w ∈ z`: the two sets have the same members. -/
def sameMembers (y z : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (σ := setTy) (iffCore (member (.var .vz) (weaken y)) (member (.var .vz) (weaken z)))

/-- `∀ z. z ∈ x → z has the members of y`: every member of `x` is `y`, extensionally. -/
def onlyMember (x y : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (σ := setTy) (.imp (member (.var .vz) (weaken x)) (sameMembers (.var .vz) (weaken y)))

theorem subst_sameMembers {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (y z : Term Symbol Γ setTy) :
    subst θ (sameMembers y z) = sameMembers (subst θ y) (subst θ z) := by
  simp only [sameMembers, subst, subst_iffCore, member, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem subst_onlyMember {Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (x y : Term Symbol Γ setTy) :
    subst θ (onlyMember x y) = onlyMember (subst θ x) (subst θ y) := by
  simp only [onlyMember, subst, subst_sameMembers, member, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem denote_sameMembers (valuation : model.{0}.Valuation Γ) (y z : Term Symbol Γ setTy) :
    (model.denote (sameMembers y z) valuation).down ↔ setValue y valuation = setValue z valuation := by
  change (∀ w : ZFSet.{0}, True → (model.denote (iffCore (member (.var .vz) (weaken y)) (member (.var .vz) (weaken z)))
    (model.extend (σ := setTy) valuation w)).down) ↔ _
  simp only [true_implies, denote_iffCore, denote_member, setValue_weaken_set, setValue_newest]
  exact ⟨fun same => ZFSet.ext fun w => same w, fun same w => same ▸ Iff.rfl⟩

theorem denote_onlyMember (valuation : model.{0}.Valuation Γ) (x y : Term Symbol Γ setTy) :
    (model.denote (onlyMember x y) valuation).down ↔ ∀ z ∈ setValue x valuation, z = setValue y valuation := by
  change (∀ z : ZFSet.{0}, True → (model.denote (member (.var .vz) (weaken x)) (model.extend (σ := setTy) valuation z)).down →
    (model.denote (sameMembers (.var .vz) (weaken y)) (model.extend (σ := setTy) valuation z)).down) ↔ _
  simp only [true_implies, denote_member, denote_sameMembers, setValue_weaken_set, setValue_newest]

end SameMembers

/-! ## Native types -/

/-- **The modal fragment**: conjunction, disjunction, fixed points, steps, named terms, emptiness and types, with
their duals. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.modal : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ | _, .empty _ | _, .nonEmpty _ | _, .typed _
  | _, .untyped _ => true
  | _, .and left right | _, .or left right => Formula.modal left && Formula.modal right
  | _, .mu inner | _, .nu inner => Formula.modal inner
  | _, .possibly _ inner | _, .necessarily _ inner => Formula.modal inner
  | _, .single _ inner | _, .everySingle _ inner => Formula.modal inner
  | _, .atLeast _ .forward _ inner | _, .allButFewer _ .forward _ inner => Formula.modal inner
  | _, _ => false

/-- A modal formula is forward. -/
theorem _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.forward_of_modal :
    ∀ {n : ℕ} (formula : Formula n), formula.modal = true → formula.forward = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ | _, .empty _, _ | _, .nonEmpty _, _
  | _, .typed _, _ | _, .untyped _, _ => rfl
  | _, .and left right, modal | _, .or left right, modal => by
    simp only [Formula.modal, Bool.and_eq_true] at modal
    simp only [Formula.forward, Formula.forward_of_modal left modal.1, Formula.forward_of_modal right modal.2,
      Bool.and_self]
  | _, .mu inner, modal | _, .nu inner, modal => by
    simp only [Formula.modal] at modal
    simp only [Formula.forward, Formula.forward_of_modal inner modal]
  | _, .possibly _ inner, modal | _, .necessarily _ inner, modal => by
    simp only [Formula.modal] at modal
    simp only [Formula.forward, Formula.forward_of_modal inner modal]
  | _, .single _ inner, modal | _, .everySingle _ inner, modal => by
    simp only [Formula.modal] at modal
    simp only [Formula.forward, Formula.forward_of_modal inner modal]
  | _, .atLeast _ .forward _ inner, modal | _, .allButFewer _ .forward _ inner, modal => by
    simp only [Formula.modal] at modal
    simp only [Formula.forward, Formula.forward_of_modal inner modal]
  | _, .sometimeBefore _ _, modal | _, .alwaysBefore _ _, modal | _, .atLeast _ .backward _ _, modal | _, .allButFewer _ .backward _ _, modal | _, .built _ _, modal | _, .everyBuilt _ _, modal | _, .split _ _ _, modal | _, .everySplit _ _ _, modal | _, .body _, modal | _, .everyBody _, modal | _, .multiBody _ _, modal | _, .everyMultiBody _ _, modal | _, .bound _, modal | _, .notBound _, modal | _, .mapsAll _ _, modal | _, .mapsSome _ _, modal | _, .someOf _ _, modal | _, .everyOf _ _, modal => absurd modal Bool.false_ne_true

/-! ## The regional fragment -/

/-- **The regional fragment**: the modal fragment and splits, with their duals. A native type in it looks only at
members and at parts. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.regional : {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ | _, .empty _ | _, .nonEmpty _ | _, .typed _
  | _, .untyped _ => true
  | _, .and left right | _, .or left right => Formula.regional left && Formula.regional right
  | _, .split _ left right | _, .everySplit _ left right => Formula.regional left && Formula.regional right
  | _, .mu inner | _, .nu inner => Formula.regional inner
  | _, .possibly _ inner | _, .necessarily _ inner => Formula.regional inner
  | _, .single _ inner | _, .everySingle _ inner => Formula.regional inner
  | _, .atLeast _ .forward _ inner | _, .allButFewer _ .forward _ inner => Formula.regional inner
  | _, _ => false

/-- A modal formula is regional. -/
theorem _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.regional_of_modal :
    ∀ {n : ℕ} (formula : Formula n), formula.modal = true → formula.regional = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ | _, .empty _, _ | _, .nonEmpty _, _
  | _, .typed _, _ | _, .untyped _, _ => rfl
  | _, .and left right, modal | _, .or left right, modal => by
    simp only [Formula.modal, Bool.and_eq_true] at modal
    simp only [Formula.regional, Formula.regional_of_modal left modal.1, Formula.regional_of_modal right modal.2,
      Bool.and_self]
  | _, .mu inner, modal | _, .nu inner, modal | _, .possibly _ inner, modal | _, .necessarily _ inner, modal
  | _, .single _ inner, modal | _, .everySingle _ inner, modal | _, .atLeast _ .forward _ inner, modal
  | _, .allButFewer _ .forward _ inner, modal => Formula.regional_of_modal inner modal
  | _, .sometimeBefore _ _, modal | _, .alwaysBefore _ _, modal | _, .atLeast _ .backward _ _, modal
  | _, .allButFewer _ .backward _ _, modal | _, .built _ _, modal | _, .everyBuilt _ _, modal
  | _, .split _ _ _, modal | _, .everySplit _ _ _, modal | _, .body _, modal | _, .everyBody _, modal
  | _, .multiBody _ _, modal | _, .everyMultiBody _ _, modal | _, .bound _, modal | _, .notBound _, modal
  | _, .mapsAll _ _, modal | _, .mapsSome _ _, modal | _, .someOf _ _, modal | _, .everyOf _ _, modal =>
    absurd modal Bool.false_ne_true

/-- **Upward shapes**: truth, "not empty" and "has a member with φ", with conjunctions and disjunctions. A formula of
this shape holds of a set as soon as it holds of a set of some of its members. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.upwardShape : {n : ℕ} → Formula n → Bool
  | _, .top => true
  | _, .nonEmpty kind => decide (kind = .hashSet)
  | _, .and left right | _, .or left right => Formula.upwardShape left && Formula.upwardShape right
  | _, .possibly _ _ => true
  | _, _ => false

/-- **The regional fragment of a profile**: every-splits when the profile is classical, since proving one classifies
an arbitrary part, and in the core profile when both parts have upward shapes, since the union already says which part
each member lies in. -/
def _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.regionalWith (classical : Bool) :
    {n : ℕ} → Formula n → Bool
  | _, .top | _, .bot | _, .var _ | _, .is _ | _, .isNot _ | _, .empty _ | _, .nonEmpty _ | _, .typed _
  | _, .untyped _ => true
  | _, .and left right | _, .or left right | _, .split _ left right =>
    Formula.regionalWith classical left && Formula.regionalWith classical right
  | _, .everySplit _ left right =>
    (classical || (Formula.upwardShape left && Formula.upwardShape right)) && Formula.regionalWith classical left &&
      Formula.regionalWith classical right
  | _, .mu inner | _, .nu inner => Formula.regionalWith classical inner
  | _, .possibly _ inner | _, .necessarily _ inner => Formula.regionalWith classical inner
  | _, .single _ inner | _, .everySingle _ inner => Formula.regionalWith classical inner
  | _, .atLeast _ .forward _ inner | _, .allButFewer _ .forward _ inner => Formula.regionalWith classical inner
  | _, _ => false

/-- A formula of a profile's regional fragment is regional. -/
theorem _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.regional_of_regionalWith {classical : Bool} :
    ∀ {n : ℕ} (formula : Formula n), formula.regionalWith classical = true → formula.regional = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ | _, .empty _, _ | _, .nonEmpty _, _
  | _, .typed _, _ | _, .untyped _, _ => rfl
  | _, .and left right, fragment | _, .or left right, fragment | _, .split _ left right, fragment => by
    simp only [Formula.regionalWith, Bool.and_eq_true] at fragment
    simp only [Formula.regional, Formula.regional_of_regionalWith left fragment.1,
      Formula.regional_of_regionalWith right fragment.2, Bool.and_self]
  | _, .everySplit _ left right, fragment => by
    simp only [Formula.regionalWith, Bool.and_eq_true] at fragment
    simp only [Formula.regional, Formula.regional_of_regionalWith left fragment.1.2,
      Formula.regional_of_regionalWith right fragment.2, Bool.and_self]
  | _, .mu inner, fragment | _, .nu inner, fragment | _, .possibly _ inner, fragment
  | _, .necessarily _ inner, fragment | _, .single _ inner, fragment | _, .everySingle _ inner, fragment
  | _, .atLeast _ .forward _ inner, fragment | _, .allButFewer _ .forward _ inner, fragment =>
    Formula.regional_of_regionalWith (classical := classical) inner fragment
  | _, .sometimeBefore _ _, fragment | _, .alwaysBefore _ _, fragment | _, .atLeast _ .backward _ _, fragment
  | _, .allButFewer _ .backward _ _, fragment | _, .built _ _, fragment | _, .everyBuilt _ _, fragment
  | _, .body _, fragment | _, .everyBody _, fragment | _, .multiBody _ _, fragment
  | _, .everyMultiBody _ _, fragment | _, .bound _, fragment | _, .notBound _, fragment
  | _, .mapsAll _ _, fragment | _, .mapsSome _ _, fragment | _, .someOf _ _, fragment
  | _, .everyOf _ _, fragment => absurd fragment Bool.false_ne_true

/-- The classical profile's regional fragment is the whole regional fragment. -/
theorem _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.regionalWith_true :
    ∀ {n : ℕ} (formula : Formula n), formula.regional = true → formula.regionalWith true = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ | _, .empty _, _ | _, .nonEmpty _, _
  | _, .typed _, _ | _, .untyped _, _ => rfl
  | _, .and left right, regional | _, .or left right, regional | _, .split _ left right, regional
  | _, .everySplit _ left right, regional => by
    simp only [Formula.regional, Bool.and_eq_true] at regional
    simp only [Formula.regionalWith, Formula.regionalWith_true left regional.1,
      Formula.regionalWith_true right regional.2, Bool.and_self, Bool.true_or]
  | _, .mu inner, regional | _, .nu inner, regional | _, .possibly _ inner, regional
  | _, .necessarily _ inner, regional | _, .single _ inner, regional | _, .everySingle _ inner, regional
  | _, .atLeast _ .forward _ inner, regional | _, .allButFewer _ .forward _ inner, regional =>
    Formula.regionalWith_true inner regional
  | _, .sometimeBefore _ _, regional | _, .alwaysBefore _ _, regional | _, .atLeast _ .backward _ _, regional
  | _, .allButFewer _ .backward _ _, regional | _, .built _ _, regional | _, .everyBuilt _ _, regional
  | _, .body _, regional | _, .everyBody _, regional | _, .multiBody _ _, regional
  | _, .everyMultiBody _ _, regional | _, .bound _, regional | _, .notBound _, regional
  | _, .mapsAll _ _, regional | _, .mapsSome _ _, regional | _, .someOf _ _, regional
  | _, .everyOf _ _, regional => absurd regional Bool.false_ne_true

/-- A modal formula is in every profile's regional fragment. -/
theorem _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.regionalWith_of_modal {classical : Bool} :
    ∀ {n : ℕ} (formula : Formula n), formula.modal = true → formula.regionalWith classical = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ | _, .empty _, _ | _, .nonEmpty _, _
  | _, .typed _, _ | _, .untyped _, _ => rfl
  | _, .and left right, modal | _, .or left right, modal => by
    simp only [Formula.modal, Bool.and_eq_true] at modal
    simp only [Formula.regionalWith, Formula.regionalWith_of_modal left modal.1,
      Formula.regionalWith_of_modal right modal.2, Bool.and_self]
  | _, .mu inner, modal | _, .nu inner, modal | _, .possibly _ inner, modal | _, .necessarily _ inner, modal
  | _, .single _ inner, modal | _, .everySingle _ inner, modal | _, .atLeast _ .forward _ inner, modal
  | _, .allButFewer _ .forward _ inner, modal => Formula.regionalWith_of_modal (classical := classical) inner modal
  | _, .sometimeBefore _ _, modal | _, .alwaysBefore _ _, modal | _, .atLeast _ .backward _ _, modal
  | _, .allButFewer _ .backward _ _, modal | _, .built _ _, modal | _, .everyBuilt _ _, modal
  | _, .split _ _ _, modal | _, .everySplit _ _ _, modal | _, .body _, modal | _, .everyBody _, modal
  | _, .multiBody _ _, modal | _, .everyMultiBody _ _, modal | _, .bound _, modal | _, .notBound _, modal
  | _, .mapsAll _ _, modal | _, .mapsSome _ _, modal | _, .someOf _ _, modal | _, .everyOf _ _, modal =>
    absurd modal Bool.false_ne_true

/-- A regional formula is forward. -/
theorem _root_.Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula.forward_of_regional :
    ∀ {n : ℕ} (formula : Formula n), formula.regional = true → formula.forward = true
  | _, .top, _ | _, .bot, _ | _, .var _, _ | _, .is _, _ | _, .isNot _, _ | _, .empty _, _ | _, .nonEmpty _, _
  | _, .typed _, _ | _, .untyped _, _ => rfl
  | _, .and left right, regional | _, .or left right, regional | _, .split _ left right, regional
  | _, .everySplit _ left right, regional => by
    simp only [Formula.regional, Bool.and_eq_true] at regional
    simp only [Formula.forward, Formula.forward_of_regional left regional.1,
      Formula.forward_of_regional right regional.2, Bool.and_self]
  | _, .mu inner, regional | _, .nu inner, regional | _, .possibly _ inner, regional
  | _, .necessarily _ inner, regional | _, .single _ inner, regional | _, .everySingle _ inner, regional
  | _, .atLeast _ .forward _ inner, regional | _, .allButFewer _ .forward _ inner, regional => by
    simp only [Formula.regional] at regional
    simp only [Formula.forward, Formula.forward_of_regional inner regional]
  | _, .sometimeBefore _ _, regional | _, .alwaysBefore _ _, regional | _, .atLeast _ .backward _ _, regional
  | _, .allButFewer _ .backward _ _, regional | _, .built _ _, regional | _, .everyBuilt _ _, regional
  | _, .body _, regional | _, .everyBody _, regional | _, .multiBody _ _, regional
  | _, .everyMultiBody _ _, regional | _, .bound _, regional | _, .notBound _, regional
  | _, .mapsAll _ _, regional | _, .mapsSome _ _, regional | _, .someOf _ _, regional
  | _, .everyOf _ _, regional => absurd regional Bool.false_ne_true

/-- The fixed-point variables of an enclosing context, read under one more element binder. -/
def underElement {n : ℕ} {Γ : Ctx Unit} (env : Fin n → Term Symbol Γ predTy) : Fin n → Term Symbol (setTy :: Γ) predTy :=
  fun index => weaken (env index)

/-- The fixed-point variables under a predicate binder and an element binder, the new predicate newest. -/
def underFixedPoint {n : ℕ} {Γ : Ctx Unit} (env : Fin n → Term Symbol Γ predTy) :
    Fin (n + 1) → Term Symbol (setTy :: predTy :: Γ) predTy :=
  Fin.cons (.var (.vs .vz)) fun index => weaken (weaken (env index))

/-- `{z ∈ x | z does not have the members of y}`: the members of `x` other than `y`. -/
def withoutSame {Γ : Ctx Unit} (x y : Term Symbol Γ setTy) : Term Symbol Γ setTy :=
  separate x (.lam (negCore (sameMembers (.var .vz) (weaken y))))

/-- **At least `k` members of `x` have the property `point`, told apart by their members**: some member has it, and
at least `k - 1` of the members other than it do. -/
def countWith {n : ℕ}
    (point : ∀ {Γ : Ctx Unit}, Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) → Term Symbol Γ .prop) :
    ℕ → {Γ : Ctx Unit} → Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) → Term Symbol Γ .prop
  | 0, _, _, _ => truth
  | k + 1, _, x, env => existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken x))
    (conjunctionFormula (point (.var .vz) (underElement env))
      (countWith point k (withoutSame (weaken x) (.var .vz)) (underElement env))))

/-- **`x` is the union of `a` and `b`**: its members are those of `a` and those of `b`. -/
def splitCore {Γ : Ctx Unit} (x a b : Term Symbol Γ setTy) : Term Symbol Γ .prop :=
  .all (σ := setTy) (iffCore (member (.var .vz) (weaken x))
    (disjunctionFormula (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b))))

theorem subst_splitCore {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (x a b : Term Symbol Γ setTy) :
    subst θ (splitCore x a b) = splitCore (subst θ x) (subst θ a) (subst θ b) := by
  simp only [splitCore, subst, subst_iffCore, subst_disjunctionFormula, member, Mettapedia.Logic.HOL.subst_weaken]
  rfl

/-- **A native type of the regional fragment, about the set term `x`**, with its fixed-point variables read as the
predicate terms `env`. Outside the fragment it is falsity. A split of `x` is a pair of sets whose union it is. -/
def nativeFormula : {n : ℕ} → Formula n → {Γ : Ctx Unit} → Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) →
    Term Symbol Γ .prop
  | _, .top, _, _, _ => truth
  | _, .bot, _, _, _ => falsity
  | _, .and left right, _, x, env => conjunctionFormula (nativeFormula left x env) (nativeFormula right x env)
  | _, .or left right, _, x, env => disjunctionFormula (nativeFormula left x env) (nativeFormula right x env)
  | _, .var index, _, x, env => .app (env index) x
  | _, .mu inner, _, x, env =>
    .all (σ := predTy) (.imp (.all (σ := setTy) (.imp (nativeFormula inner (.var .vz) (underFixedPoint env))
      (.app (.var (.vs .vz)) (.var .vz)))) (.app (.var .vz) (weaken x)))
  | _, .nu inner, _, x, env =>
    existentialInline (σ := predTy) (conjunctionFormula (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz))
      (nativeFormula inner (.var .vz) (underFixedPoint env)))) (.app (.var .vz) (weaken x)))
  | _, .possibly label inner, _, x, env =>
    if memberLabel label then
      existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken x))
        (nativeFormula inner (.var .vz) (underElement env)))
    else falsity
  | _, .necessarily label inner, _, x, env =>
    if memberLabel label then
      .all (σ := setTy) (.imp (member (.var .vz) (weaken x)) (nativeFormula inner (.var .vz) (underElement env)))
    else truth
  | _, .is term, _, x, _ => if hereditary membership hfRule.category term then describesSomeOf term x else falsity
  | _, .isNot term, _, x, _ =>
    if hereditary membership hfRule.category term then negCore (describesSomeOf term x) else truth
  | _, .empty kind, _, x, _ => if kind = .hashSet then .all (negCore (member (.var .vz) (weaken x))) else falsity
  | _, .nonEmpty kind, _, x, _ =>
    if kind = .hashSet then negCore (.all (negCore (member (.var .vz) (weaken x)))) else truth
  | _, .typed type, _, x, _ => typedFormula type x
  | _, .untyped type, _, x, _ => negCore (typedFormula type x)
  | _, .single kind inner, _, x, env =>
    if kind = .hashSet then
      existentialInline (σ := setTy) (conjunctionFormula (member (.var .vz) (weaken x))
        (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env)) (onlyMember (weaken x) (.var .vz))))
    else falsity
  | _, .everySingle kind inner, _, x, env =>
    if kind = .hashSet then
      .all (σ := setTy) (.imp (member (.var .vz) (weaken x)) (.imp (onlyMember (weaken x) (.var .vz))
        (nativeFormula inner (.var .vz) (underElement env))))
    else truth
  | _, .atLeast count .forward label inner, _, x, env =>
    if memberLabel label then countWith (fun {_} y env => nativeFormula inner y env) count x env
    else if count = 0 then truth else falsity
  | _, .allButFewer count .forward label inner, _, x, env =>
    if memberLabel label then negCore (countWith (fun {_} y env => negCore (nativeFormula inner y env)) count x env)
    else if count = 0 then falsity else truth
  | _, .split kind left right, _, x, env =>
    if kind = .hashSet then
      existentialInline (σ := setTy) (existentialInline (σ := setTy) (conjunctionFormula
        (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (conjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))))
    else falsity
  | _, .everySplit kind left right, _, x, env =>
    if kind = .hashSet then
      .all (σ := setTy) (.all (σ := setTy) (.imp (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (disjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))))
    else truth
  | _, _, _, _, _ => falsity

theorem subst_underElement {n : ℕ} {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (env : Fin n → Term Symbol Γ predTy) :
    (fun index => subst (Subst.lift θ) (underElement env index)) = underElement fun index => subst θ (env index) := by
  funext index
  exact Mettapedia.Logic.HOL.subst_weaken θ (env index)

theorem subst_underFixedPoint {n : ℕ} {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (env : Fin n → Term Symbol Γ predTy) :
    (fun index => subst (Subst.lift (Subst.lift θ)) (underFixedPoint env index)) =
      underFixedPoint fun index => subst θ (env index) := by
  funext index
  refine Fin.cases rfl (fun index => ?_) index
  simp only [underFixedPoint, Fin.cons_succ, Mettapedia.Logic.HOL.subst_weaken]

theorem subst_withoutSame {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (x y : Term Symbol Γ setTy) :
    subst θ (withoutSame x y) = withoutSame (subst θ x) (subst θ y) := by
  simp only [withoutSame, separate, subst, subst_negCore, subst_sameMembers, Mettapedia.Logic.HOL.subst_weaken]
  rfl

theorem subst_countWith {n : ℕ}
    {point : ∀ {Γ : Ctx Unit}, Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) → Term Symbol Γ .prop}
    (natural : ∀ {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (y : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (point y env) = point (subst θ y) fun index => subst θ (env index)) :
    ∀ (k : ℕ) {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (countWith point k x env) = countWith point k (subst θ x) fun index => subst θ (env index)
  | 0, _, _, _, _, _ => rfl
  | k + 1, _, _, θ, x, env => by
    simp only [countWith, subst_existentialInline, subst_conjunctionFormula, natural, subst_countWith natural k,
      subst_withoutSame, subst_underElement, member, subst, Mettapedia.Logic.HOL.subst_weaken]
    rfl

/-- **Substitution commutes with native types of the regional fragment.** -/
theorem subst_nativeFormula_regional {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') :
    ∀ {n : ℕ} (formula : Formula n), formula.regional = true → ∀ (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy),
      subst θ (nativeFormula formula x env) = nativeFormula formula (subst θ x) fun index => subst θ (env index)
  | _, .top, _, _, _ => rfl
  | _, .bot, _, _, _ => rfl
  | _, .and left right, modal, x, env => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    simp only [nativeFormula, subst_conjunctionFormula, subst_nativeFormula_regional θ left modal.1,
      subst_nativeFormula_regional θ right modal.2]
  | _, .or left right, modal, x, env => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    simp only [nativeFormula, subst_disjunctionFormula, subst_nativeFormula_regional θ left modal.1,
      subst_nativeFormula_regional θ right modal.2]
  | _, .var index, _, x, env => rfl
  | _, .mu inner, modal, x, env => by
    simp only [Formula.regional] at modal
    simp only [nativeFormula, subst, subst_nativeFormula_regional (Subst.lift (Subst.lift θ)) inner modal,
      subst_underFixedPoint, Mettapedia.Logic.HOL.subst_weaken]
    rfl
  | _, .nu inner, modal, x, env => by
    simp only [Formula.regional] at modal
    simp only [nativeFormula, subst_existentialInline, subst_conjunctionFormula, subst,
      subst_nativeFormula_regional (Subst.lift (Subst.lift θ)) inner modal, subst_underFixedPoint,
      Mettapedia.Logic.HOL.subst_weaken]
    rfl
  | _, .possibly label inner, modal, x, env => by
    simp only [Formula.regional] at modal
    unfold nativeFormula
    split_ifs
    · simp only [subst_existentialInline, subst_conjunctionFormula, subst, member, Mettapedia.Logic.HOL.subst_weaken,
        subst_nativeFormula_regional (Subst.lift θ) inner modal, subst_underElement]
      rfl
    · rfl
  | _, .necessarily label inner, modal, x, env => by
    simp only [Formula.regional] at modal
    unfold nativeFormula
    split_ifs
    · simp only [subst, member, Mettapedia.Logic.HOL.subst_weaken, subst_nativeFormula_regional (Subst.lift θ) inner modal,
        subst_underElement]
      rfl
    · rfl
  | _, .is term, _, x, _ => by
    unfold nativeFormula
    split_ifs
    · exact subst_describesSomeOf θ term x
    · rfl
  | _, .isNot term, _, x, _ => by
    unfold nativeFormula
    split_ifs
    · exact congrArg negCore (subst_describesSomeOf θ term x)
    · rfl
  | _, .empty kind, _, x, _ => by
    unfold nativeFormula
    split_ifs
    · simp only [subst, negCore, member, Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · rfl
  | _, .nonEmpty kind, _, x, _ => by
    unfold nativeFormula
    split_ifs
    · simp only [subst, negCore, member, Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · rfl
  | _, .typed type, _, x, _ => subst_typedFormula θ type x
  | _, .untyped type, _, x, _ => congrArg negCore (subst_typedFormula θ type x)
  | _, .single kind inner, modal, x, env => by
    simp only [Formula.regional] at modal
    unfold nativeFormula
    split_ifs
    · simp only [subst_existentialInline, subst_conjunctionFormula, subst, member, Mettapedia.Logic.HOL.subst_weaken,
        subst_nativeFormula_regional (Subst.lift θ) inner modal, subst_underElement, subst_onlyMember]
      rfl
    · rfl
  | _, .everySingle kind inner, modal, x, env => by
    simp only [Formula.regional] at modal
    unfold nativeFormula
    split_ifs
    · simp only [subst, member, Mettapedia.Logic.HOL.subst_weaken, subst_nativeFormula_regional (Subst.lift θ) inner modal,
        subst_underElement, subst_onlyMember]
      rfl
    · rfl
  | _, .atLeast count .forward label inner, modal, x, env => by
    simp only [Formula.regional] at modal
    unfold nativeFormula
    split_ifs
    · exact subst_countWith (fun θ' y env' => subst_nativeFormula_regional θ' inner modal y env') count θ x env
    · rfl
    · rfl
  | _, .allButFewer count .forward label inner, modal, x, env => by
    simp only [Formula.regional] at modal
    unfold nativeFormula
    split_ifs
    · exact congrArg negCore (subst_countWith (fun θ' y env' => by
        rw [subst_negCore, subst_nativeFormula_regional θ' inner modal y env']) count θ x env)
    · rfl
    · rfl
  | _, .split kind left right, modal, x, env => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    by_cases isSet : kind = .hashSet
    · simp only [nativeFormula, if_pos isSet, subst_existentialInline, subst_conjunctionFormula, subst_splitCore,
        subst_nativeFormula_regional (Subst.lift (Subst.lift θ)) left modal.1,
        subst_nativeFormula_regional (Subst.lift (Subst.lift θ)) right modal.2, subst_underElement,
        Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · simp only [nativeFormula, if_neg isSet]
      rfl
  | _, .everySplit kind left right, modal, x, env => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    by_cases isSet : kind = .hashSet
    · simp only [nativeFormula, if_pos isSet, subst, subst_disjunctionFormula, subst_splitCore,
        subst_nativeFormula_regional (Subst.lift (Subst.lift θ)) left modal.1,
        subst_nativeFormula_regional (Subst.lift (Subst.lift θ)) right modal.2, subst_underElement,
        Mettapedia.Logic.HOL.subst_weaken]
      rfl
    · simp only [nativeFormula, if_neg isSet]
      rfl
  | _, .sometimeBefore _ _, modal, _, _ | _, .alwaysBefore _ _, modal, _, _ | _, .atLeast _ .backward _ _, modal, _, _ | _, .allButFewer _ .backward _ _, modal, _, _ | _, .built _ _, modal, _, _ | _, .everyBuilt _ _, modal, _, _ | _, .body _, modal, _, _ | _, .everyBody _, modal, _, _ | _, .multiBody _ _, modal, _, _ | _, .everyMultiBody _ _, modal, _, _ | _, .bound _, modal, _, _ | _, .notBound _, modal, _, _ | _, .mapsAll _ _, modal, _, _ | _, .mapsSome _ _, modal, _, _ | _, .someOf _ _, modal, _, _ | _, .everyOf _ _, modal, _, _ => absurd modal Bool.false_ne_true

theorem subst_nativeFormula {Γ Γ' : Ctx Unit} (θ : Subst Symbol Γ Γ') {n : ℕ} (formula : Formula n)
    (modal : formula.modal = true) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy) :
    subst θ (nativeFormula formula x env) = nativeFormula formula (subst θ x) fun index => subst θ (env index) :=
  subst_nativeFormula_regional θ formula (Formula.regional_of_modal formula modal) x env

/-! ## What native types mean -/

section Meaning

variable {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ)

/-- Predicate terms whose values hold exactly on the sets of an environment. -/
def EnvAgrees {n : ℕ} (env : Fin n → Term Symbol Γ predTy) (sets : Env ZFSet.{0} n) : Prop :=
  ∀ (index : Fin n) (z : ZFSet.{0}), (model.denote (env index) valuation z).down ↔ z ∈ sets index

theorem envAgrees_underElement {n : ℕ} {env : Fin n → Term Symbol Γ predTy} {sets : Env ZFSet.{0} n}
    (agrees : EnvAgrees valuation env sets) (z : ZFSet.{0}) :
    EnvAgrees (model.extend (σ := setTy) valuation z) (underElement env) sets := by
  intro index w
  have unweakened : model.denote (underElement env index) (model.extend (σ := setTy) valuation z) =
      model.denote (env index) valuation :=
    Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := setTy) model (env index) valuation z
  rw [unweakened]
  exact agrees index w

theorem envAgrees_underFixedPoint {n : ℕ} {env : Fin n → Term Symbol Γ predTy} {sets : Env ZFSet.{0} n}
    (agrees : EnvAgrees valuation env sets) (predicate : Ty.denote model.{0}.Carrier predTy) (z : ZFSet.{0}) :
    EnvAgrees (model.extend (σ := setTy) (model.extend (σ := predTy) valuation predicate) z) (underFixedPoint env)
      (sets.extend {w | (predicate w).down}) := by
  intro index w
  refine Fin.cases Iff.rfl (fun index => ?_) index
  have unweakened : model.denote (underFixedPoint env index.succ)
      (model.extend (σ := setTy) (model.extend (σ := predTy) valuation predicate) z) = model.denote (env index) valuation :=
    (Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := setTy) model (weaken (env index))
      (model.extend (σ := predTy) valuation predicate) z).trans
      (Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := predTy) model (env index) valuation predicate)
  rw [unweakened]
  exact agrees index w

end Meaning

theorem setValue_withoutSame {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x y : Term Symbol Γ setTy) :
    setValue (withoutSame x y) valuation = ZFSet.sep (fun z => z ≠ setValue y valuation) (setValue x valuation) := by
  apply ZFSet.ext
  intro z
  show z ∈ ZFSet.sep (fun w => (model.denote (Term.lam (negCore (sameMembers (.var .vz) (weaken y)))) valuation w).down)
    (setValue x valuation) ↔ _
  rw [ZFSet.mem_sep, ZFSet.mem_sep]
  refine and_congr_right fun _ => ?_
  change (model.denote (negCore (sameMembers (.var .vz) (weaken y))) (model.extend (σ := setTy) valuation z)).down ↔ _
  rw [denote_negCore, denote_sameMembers, setValue_newest, setValue_weaken_set]

/-- At least `k` members of a set have the property: some member has it, and at least `k - 1` of the others do. -/
def CountIn (P : ZFSet.{0} → Prop) : ℕ → ZFSet.{0} → Prop
  | 0, _ => True
  | k + 1, whole => ∃ y ∈ whole, P y ∧ CountIn P k (ZFSet.sep (fun z => z ≠ y) whole)

theorem countIn_iff_atLeast (P : ZFSet.{0} → Prop) : ∀ (k : ℕ) (whole : ZFSet.{0}),
    CountIn P k whole ↔ extensional.AtLeast k fun other => other ∈ whole ∧ P other
  | 0, _ => ⟨fun _ => ⟨[], rfl, List.Pairwise.nil, fun _ none => absurd none List.not_mem_nil⟩, fun _ => trivial⟩
  | k + 1, whole => by
    rw [CountIn]
    constructor
    · rintro ⟨y, member, holds, rest⟩
      obtain ⟨witnesses, length, distinct, all⟩ := (countIn_iff_atLeast P k _).mp rest
      refine ⟨y :: witnesses, by simp [length], List.pairwise_cons.mpr ⟨fun other inside same => ?_, distinct⟩, ?_⟩
      · obtain ⟨found, -⟩ := all other inside
        rw [ZFSet.mem_sep] at found
        exact found.2 same.symm
      · intro other inside
        rcases List.mem_cons.mp inside with rfl | inside
        · exact ⟨member, holds⟩
        · obtain ⟨found, holdsOther⟩ := all other inside
          rw [ZFSet.mem_sep] at found
          exact ⟨found.1, holdsOther⟩
    · rintro ⟨witnesses, length, distinct, all⟩
      cases witnesses with
      | nil => simp at length
      | cons y rest =>
        obtain ⟨apart, distinct⟩ := List.pairwise_cons.mp distinct
        refine ⟨y, (all y List.mem_cons_self).1, (all y List.mem_cons_self).2,
          (countIn_iff_atLeast P k _).mpr ⟨rest, by simpa using length, distinct, fun other inside => ?_⟩⟩
        exact ⟨ZFSet.mem_sep.mpr ⟨(all other (List.mem_cons_of_mem _ inside)).1, fun same => apart other inside same.symm⟩,
          (all other (List.mem_cons_of_mem _ inside)).2⟩

theorem atLeast_unlabelled {label : StepLabel} (labelled : ¬ memberLabel label) (whole : ZFSet.{0})
    (holds : ZFSet.{0} → Prop) {k : ℕ} :
    extensional.AtLeast k (fun other => (memberLabel label ∧ other ∈ whole) ∧ holds other) ↔ k = 0 := by
  constructor
  · rintro ⟨witnesses, length, -, all⟩
    cases witnesses with
    | nil => exact length.symm
    | cons first _ => exact absurd (all first List.mem_cons_self).1.1 labelled
  · rintro rfl
    exact ⟨[], rfl, List.Pairwise.nil, fun _ none => absurd none List.not_mem_nil⟩

theorem denote_countWith {n : ℕ}
    {point : ∀ {Γ : Ctx Unit}, Term Symbol Γ setTy → (Fin n → Term Symbol Γ predTy) → Term Symbol Γ .prop}
    (sets : Env ZFSet.{0} n) (P : ZFSet.{0} → Prop)
    (meaning : ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (y : Term Symbol Γ setTy)
      (env : Fin n → Term Symbol Γ predTy), EnvAgrees valuation env sets →
        ((model.denote (point y env) valuation).down ↔ P (setValue y valuation))) :
    ∀ (k : ℕ) {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy)
      (env : Fin n → Term Symbol Γ predTy), EnvAgrees valuation env sets →
        ((model.denote (countWith point k x env) valuation).down ↔ CountIn P k (setValue x valuation))
  | 0, _, valuation, _, _, _ => iff_of_true (denote_truth valuation) trivial
  | k + 1, _, valuation, x, env, agrees => by
    rw [countWith, denote_existentialInline]
    change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (member (.var .vz) (weaken x))
      (conjunctionFormula (point (.var .vz) (underElement env)) (countWith point k (withoutSame (weaken x) (.var .vz))
        (underElement env)))) (model.extend (σ := setTy) valuation z)).down) ↔ _
    simp only [true_and, denote_conjunctionFormula, denote_member, setValue_weaken_set, setValue_newest]
    rw [CountIn]
    refine exists_congr fun z => ?_
    simp only [meaning _ _ _ (envAgrees_underElement valuation agrees z),
      denote_countWith sets P meaning k _ _ _ (envAgrees_underElement valuation agrees z), setValue_withoutSame,
      setValue_weaken_set, setValue_newest]

theorem denote_splitCore {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x a b : Term Symbol Γ setTy) :
    (model.denote (splitCore x a b) valuation).down ↔
      setValue x valuation = setValue a valuation ∪ setValue b valuation := by
  change (∀ z : ZFSet.{0}, True → (model.denote (iffCore (member (.var .vz) (weaken x))
    (disjunctionFormula (member (.var .vz) (weaken a)) (member (.var .vz) (weaken b))))
      (model.extend (σ := setTy) valuation z)).down) ↔ _
  simp only [true_implies, denote_iffCore, denote_disjunctionFormula, denote_member, setValue_weaken_set,
    setValue_newest]
  constructor
  · intro every
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union]
    exact every z
  · intro same z
    rw [same, ZFSet.mem_union]

/-- **A native type of the modal fragment is true exactly where it holds on the ZF sets**, for predicate terms that
agree with the fixed-point environment. -/
theorem denote_nativeFormula_regional : ∀ {n : ℕ} (formula : Formula n), formula.regional = true →
    ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy)
      (sets : Env ZFSet.{0} n), EnvAgrees valuation env sets →
      ((model.denote (nativeFormula formula x env) valuation).down ↔ extensional.sat sets formula (setValue x valuation))
  | _, .top, _, _, valuation, _, _, _, _ => iff_of_true (denote_truth valuation) trivial
  | _, .bot, _, _, valuation, _, _, _, _ => denote_falsity valuation
  | _, .and left right, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    rw [nativeFormula, denote_conjunctionFormula, denote_nativeFormula_regional left modal.1 valuation x env sets agrees,
      denote_nativeFormula_regional right modal.2 valuation x env sets agrees]
    rfl
  | _, .or left right, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    rw [nativeFormula, denote_disjunctionFormula, denote_nativeFormula_regional left modal.1 valuation x env sets agrees,
      denote_nativeFormula_regional right modal.2 valuation x env sets agrees]
    rfl
  | _, .var index, _, _, valuation, x, env, sets, agrees => agrees index (setValue x valuation)
  | _, .mu inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    change (∀ predicate : Ty.denote model.{0}.Carrier predTy, True →
      (∀ z : ZFSet.{0}, True → (model.denote (nativeFormula inner (.var .vz) (underFixedPoint env))
          (model.extend (σ := setTy) (model.extend (σ := predTy) valuation predicate) z)).down → (predicate z).down) →
        (predicate (setValue (weaken x) (model.extend (σ := predTy) valuation predicate))).down) ↔ _
    simp only [true_implies, setValue_weaken_pred]
    constructor
    · intro holds closed isClosed
      have reads : ∀ z : ZFSet.{0}, ((fun w : ZFSet.{0} => (ULift.up (w ∈ closed) : ULift.{1} Prop)) z).down ↔
          z ∈ closed := fun _ => Iff.rfl
      exact holds (fun w => ULift.up (w ∈ closed)) fun z inside => isClosed z
        ((denote_nativeFormula_regional inner modal _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees (fun w => ULift.up (w ∈ closed)) z)).mp inside)
    · intro holds predicate isClosed
      exact holds {w | (predicate w).down} fun z inside => isClosed z
        ((denote_nativeFormula_regional inner modal _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees predicate z)).mpr inside)
  | _, .nu inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    rw [nativeFormula, denote_existentialInline]
    change (∃ predicate : Ty.denote model.{0}.Carrier predTy, True ∧ (model.denote (conjunctionFormula
      (.all (σ := setTy) (.imp (.app (.var (.vs .vz)) (.var .vz)) (nativeFormula inner (.var .vz) (underFixedPoint env))))
      (.app (.var .vz) (weaken x))) (model.extend (σ := predTy) valuation predicate)).down) ↔ _
    simp only [true_and, denote_conjunctionFormula]
    change (∃ predicate : Ty.denote model.{0}.Carrier predTy,
      (∀ z : ZFSet.{0}, True → (predicate z).down → (model.denote (nativeFormula inner (.var .vz) (underFixedPoint env))
          (model.extend (σ := setTy) (model.extend (σ := predTy) valuation predicate) z)).down) ∧
        (predicate (setValue (weaken x) (model.extend (σ := predTy) valuation predicate))).down) ↔ _
    simp only [true_implies, setValue_weaken_pred]
    constructor
    · rintro ⟨predicate, preserved, inside⟩
      exact ⟨{w | (predicate w).down}, inside, fun z member =>
        (denote_nativeFormula_regional inner modal _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees predicate z)).mp (preserved z member)⟩
    · rintro ⟨invariant, inside, preserved⟩
      exact ⟨fun w => ULift.up (w ∈ invariant), fun z member =>
        (denote_nativeFormula_regional inner modal _ (.var .vz) (underFixedPoint env) _
          (envAgrees_underFixedPoint valuation agrees (fun w => ULift.up (w ∈ invariant)) z)).mpr (preserved z member),
        inside⟩
  | _, .possibly label inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    by_cases labelled : memberLabel label
    · simp only [nativeFormula, if_pos labelled]
      rw [denote_existentialInline]
      change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (member (.var .vz) (weaken x))
        (nativeFormula inner (.var .vz) (underElement env))) (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_and, denote_conjunctionFormula, denote_member, setValue_weaken_set, setValue_newest]
      refine exists_congr fun z => ?_
      rw [denote_nativeFormula_regional inner modal _ (.var .vz) (underElement env) sets (envAgrees_underElement valuation agrees z)]
      exact ⟨fun ⟨member, holds⟩ => ⟨⟨labelled, member⟩, holds⟩, fun ⟨⟨_, member⟩, holds⟩ => ⟨member, holds⟩⟩
    · simp only [nativeFormula, if_neg labelled]
      exact (denote_falsity valuation).trans (iff_of_false id fun ⟨_, ⟨found, _⟩, _⟩ => labelled found)
  | _, .necessarily label inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    by_cases labelled : memberLabel label
    · simp only [nativeFormula, if_pos labelled]
      change (∀ z : ZFSet.{0}, True → (model.denote (member (.var .vz) (weaken x)) (model.extend (σ := setTy) valuation z)).down →
        (model.denote (nativeFormula inner (.var .vz) (underElement env)) (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_implies, denote_member, setValue_weaken_set, setValue_newest]
      refine forall_congr' fun z => ?_
      rw [denote_nativeFormula_regional inner modal _ (.var .vz) (underElement env) sets (envAgrees_underElement valuation agrees z)]
      exact ⟨fun holds step => holds step.2, fun holds member => holds ⟨labelled, member⟩⟩
    · simp only [nativeFormula, if_neg labelled]
      exact iff_of_true (denote_truth valuation) fun _ step => (labelled step.1).elim
  | _, .is term, _, _, valuation, x, _, _, _ => by
    by_cases holds : hereditary membership hfRule.category term = true
    · simp only [nativeFormula, if_pos holds]
      rw [denote_describesSomeOf ((hereditary_iff _).mp holds)]
      exact ⟨fun same => ⟨(hereditary_iff _).mp holds, same⟩, fun found => found.2⟩
    · simp only [nativeFormula, if_neg holds]
      exact (denote_falsity valuation).trans (iff_of_false id fun found => holds ((hereditary_iff _).mpr found.1))
  | _, .isNot term, _, _, valuation, x, _, _, _ => by
    by_cases holds : hereditary membership hfRule.category term = true
    · simp only [nativeFormula, if_pos holds]
      rw [denote_negCore, denote_describesSomeOf ((hereditary_iff _).mp holds)]
      exact not_congr ⟨fun same => ⟨(hereditary_iff _).mp holds, same⟩, fun found => found.2⟩
    · simp only [nativeFormula, if_neg holds]
      exact iff_of_true (denote_truth valuation) fun found => holds ((hereditary_iff _).mpr found.1)
  | _, .empty kind, _, _, valuation, x, _, _, _ => by
    by_cases set : kind = .hashSet
    · simp only [nativeFormula, if_pos set]
      change (∀ z : ZFSet.{0}, True → (model.denote (negCore (member (.var .vz) (weaken x)))
        (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_implies, denote_negCore, denote_member, setValue_weaken_set, setValue_newest]
      constructor
      · intro none
        exact ⟨set, ZFSet.ext fun z => ⟨fun member => (none z member).elim, fun member => (ZFSet.notMem_empty z member).elim⟩⟩
      · rintro ⟨-, isEmpty⟩ z member
        rw [show setValue x valuation = ∅ from isEmpty] at member
        exact ZFSet.notMem_empty z member
    · simp only [nativeFormula, if_neg set]
      exact (denote_falsity valuation).trans (iff_of_false id fun found => set found.1)
  | _, .nonEmpty kind, _, _, valuation, x, _, _, _ => by
    by_cases set : kind = .hashSet
    · simp only [nativeFormula, if_pos set]
      rw [denote_negCore]
      refine not_congr ?_
      change (∀ z : ZFSet.{0}, True → (model.denote (negCore (member (.var .vz) (weaken x)))
        (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_implies, denote_negCore, denote_member, setValue_weaken_set, setValue_newest]
      constructor
      · intro none
        exact ⟨set, ZFSet.ext fun z => ⟨fun member => (none z member).elim, fun member => (ZFSet.notMem_empty z member).elim⟩⟩
      · rintro ⟨-, isEmpty⟩ z member
        rw [show setValue x valuation = ∅ from isEmpty] at member
        exact ZFSet.notMem_empty z member
    · simp only [nativeFormula, if_neg set]
      exact iff_of_true (denote_truth valuation) fun found => set found.1
  | _, .typed type, _, _, valuation, x, _, _, _ => denote_typedFormula type valuation x
  | _, .untyped type, _, _, valuation, x, _, _, _ => by
    rw [nativeFormula, denote_negCore, denote_typedFormula]
    rfl
  | _, .single kind inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    by_cases set : kind = .hashSet
    · simp only [nativeFormula, if_pos set]
      rw [denote_existentialInline]
      change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (member (.var .vz) (weaken x))
        (conjunctionFormula (nativeFormula inner (.var .vz) (underElement env)) (onlyMember (weaken x) (.var .vz))))
        (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_and, denote_conjunctionFormula, denote_member, denote_onlyMember, setValue_weaken_set,
        setValue_newest]
      change _ ↔ ∃ z, (kind = .hashSet ∧ setValue x valuation = {z}) ∧ extensional.sat sets inner z
      refine exists_congr fun z => ?_
      rw [denote_nativeFormula_regional inner modal _ (.var .vz) (underElement env) sets (envAgrees_underElement valuation agrees z)]
      constructor
      · rintro ⟨member, holds, only⟩
        refine ⟨⟨set, ZFSet.ext fun w => ⟨fun inside => ?_, fun inside => ?_⟩⟩, holds⟩
        · rw [only w inside]
          exact ZFSet.mem_singleton.mpr rfl
        · rw [ZFSet.mem_singleton.mp inside]
          exact member
      · rintro ⟨⟨-, single⟩, holds⟩
        refine ⟨?_, holds, fun w inside => ?_⟩
        · rw [single]
          exact ZFSet.mem_singleton.mpr rfl
        · rw [single] at inside
          exact ZFSet.mem_singleton.mp inside
    · simp only [nativeFormula, if_neg set]
      exact (denote_falsity valuation).trans (iff_of_false id fun ⟨_, ⟨found, _⟩, _⟩ => set found)
  | _, .everySingle kind inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    by_cases set : kind = .hashSet
    · simp only [nativeFormula, if_pos set]
      change (∀ z : ZFSet.{0}, True → (model.denote (member (.var .vz) (weaken x)) (model.extend (σ := setTy) valuation z)).down →
        (model.denote (onlyMember (weaken x) (.var .vz)) (model.extend (σ := setTy) valuation z)).down →
        (model.denote (nativeFormula inner (.var .vz) (underElement env)) (model.extend (σ := setTy) valuation z)).down) ↔ _
      simp only [true_implies, denote_member, denote_onlyMember, setValue_weaken_set, setValue_newest]
      change _ ↔ ∀ z, (kind = .hashSet ∧ setValue x valuation = {z}) → extensional.sat sets inner z
      refine forall_congr' fun z => ?_
      rw [denote_nativeFormula_regional inner modal _ (.var .vz) (underElement env) sets (envAgrees_underElement valuation agrees z)]
      constructor
      · rintro holds ⟨-, single⟩
        refine holds ?_ fun w inside => ?_
        · rw [single]
          exact ZFSet.mem_singleton.mpr rfl
        · rw [single] at inside
          exact ZFSet.mem_singleton.mp inside
      · intro holds member only
        exact holds ⟨set, ZFSet.ext fun w => ⟨fun inside => by rw [only w inside]; exact ZFSet.mem_singleton.mpr rfl,
          fun inside => by rw [ZFSet.mem_singleton.mp inside]; exact member⟩⟩
    · simp only [nativeFormula, if_neg set]
      exact iff_of_true (denote_truth valuation) fun _ found => (set found.1).elim
  | _, .atLeast count .forward label inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    change _ ↔ extensional.AtLeast count fun other =>
      (memberLabel label ∧ other ∈ setValue x valuation) ∧ extensional.sat sets inner other
    by_cases labelled : memberLabel label
    · simp only [nativeFormula, if_pos labelled]
      rw [denote_countWith sets (extensional.sat sets inner) (fun valuation' y env' agrees' =>
        denote_nativeFormula_regional inner modal valuation' y env' sets agrees') count valuation x env agrees, countIn_iff_atLeast]
      exact ⟨fun many => many.mono fun _ found => ⟨⟨labelled, found.1⟩, found.2⟩,
        fun many => many.mono fun _ found => ⟨found.1.2, found.2⟩⟩
    · simp only [nativeFormula, if_neg labelled]
      rw [atLeast_unlabelled labelled]
      split_ifs with zero
      · exact iff_of_true (denote_truth valuation) zero
      · exact (denote_falsity valuation).trans (iff_of_false id zero)
  | _, .allButFewer count .forward label inner, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional] at modal
    change _ ↔ ¬ extensional.AtLeast count fun other =>
      (memberLabel label ∧ other ∈ setValue x valuation) ∧ ¬ extensional.sat sets inner other
    by_cases labelled : memberLabel label
    · simp only [nativeFormula, if_pos labelled]
      rw [denote_negCore, denote_countWith sets (fun z => ¬ extensional.sat sets inner z) (fun valuation' y env' agrees' => by
        rw [denote_negCore, denote_nativeFormula_regional inner modal valuation' y env' sets agrees']) count valuation x env agrees,
        countIn_iff_atLeast]
      exact not_congr ⟨fun many => many.mono fun _ found => ⟨⟨labelled, found.1⟩, found.2⟩,
        fun many => many.mono fun _ found => ⟨found.1.2, found.2⟩⟩
    · simp only [nativeFormula, if_neg labelled]
      rw [atLeast_unlabelled labelled]
      split_ifs with zero
      · exact (denote_falsity valuation).trans (iff_of_false id (not_not.mpr zero))
      · exact iff_of_true (denote_truth valuation) zero
  | _, .split kind left right, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    by_cases isSet : kind = .hashSet
    · simp only [nativeFormula, if_pos isSet]
      rw [denote_existentialInline]
      change (∃ a : ZFSet.{0}, True ∧ (model.denote (existentialInline (σ := setTy) (conjunctionFormula
        (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (conjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))))
        (model.extend (σ := setTy) valuation a)).down) ↔
          ∃ a b, (kind = .hashSet ∧ setValue x valuation = a ∪ b) ∧ extensional.sat sets left a ∧
            extensional.sat sets right b
      simp only [true_and]
      refine exists_congr fun a => ?_
      rw [denote_existentialInline]
      change (∃ b : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula
        (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
        (conjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env)))))
        (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b)).down) ↔ _
      simp only [true_and, denote_conjunctionFormula, denote_splitCore]
      refine exists_congr fun b => ?_
      have agreesTwo := envAgrees_underElement (model.extend (σ := setTy) valuation a)
        (envAgrees_underElement valuation agrees a) b
      rw [denote_nativeFormula_regional left modal.1 _ (.var (.vs .vz)) _ sets agreesTwo,
        denote_nativeFormula_regional right modal.2 _ (.var .vz) _ sets agreesTwo]
      simp only [setValue_weaken_set]
      exact ⟨fun ⟨union, holdsLeft, holdsRight⟩ => ⟨⟨isSet, union⟩, holdsLeft, holdsRight⟩,
        fun ⟨⟨_, union⟩, holdsLeft, holdsRight⟩ => ⟨union, holdsLeft, holdsRight⟩⟩
    · simp only [nativeFormula, if_neg isSet]
      exact (denote_falsity valuation).trans (iff_of_false id fun ⟨_, _, ⟨found, _⟩, _⟩ => isSet found)
  | _, .everySplit kind left right, modal, _, valuation, x, env, sets, agrees => by
    simp only [Formula.regional, Bool.and_eq_true] at modal
    by_cases isSet : kind = .hashSet
    · simp only [nativeFormula, if_pos isSet]
      change (∀ a : ZFSet.{0}, True → ∀ b : ZFSet.{0}, True →
        (model.denote (splitCore (weaken (weaken x)) (.var (.vs .vz)) (.var .vz))
          (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b)).down →
        (model.denote (disjunctionFormula (nativeFormula left (.var (.vs .vz)) (underElement (underElement env)))
          (nativeFormula right (.var .vz) (underElement (underElement env))))
          (model.extend (σ := setTy) (model.extend (σ := setTy) valuation a) b)).down) ↔
          ∀ a b, (kind = .hashSet ∧ setValue x valuation = a ∪ b) →
            extensional.sat sets left a ∨ extensional.sat sets right b
      simp only [true_implies, denote_splitCore, denote_disjunctionFormula]
      refine forall_congr' fun a => forall_congr' fun b => ?_
      have agreesTwo := envAgrees_underElement (model.extend (σ := setTy) valuation a)
        (envAgrees_underElement valuation agrees a) b
      rw [denote_nativeFormula_regional left modal.1 _ (.var (.vs .vz)) _ sets agreesTwo,
        denote_nativeFormula_regional right modal.2 _ (.var .vz) _ sets agreesTwo]
      simp only [setValue_weaken_set]
      exact ⟨fun holds split => holds split.2, fun holds union => holds ⟨isSet, union⟩⟩
    · simp only [nativeFormula, if_neg isSet]
      exact iff_of_true (denote_truth valuation) fun _ _ split => absurd split.1 isSet
  | _, .sometimeBefore _ _, modal, _, _, _, _, _, _ | _, .alwaysBefore _ _, modal, _, _, _, _, _, _ | _, .atLeast _ .backward _ _, modal, _, _, _, _, _, _ | _, .allButFewer _ .backward _ _, modal, _, _, _, _, _, _ | _, .built _ _, modal, _, _, _, _, _, _ | _, .everyBuilt _ _, modal, _, _, _, _, _, _ | _, .body _, modal, _, _, _, _, _, _ | _, .everyBody _, modal, _, _, _, _, _, _ | _, .multiBody _ _, modal, _, _, _, _, _, _ | _, .everyMultiBody _ _, modal, _, _, _, _, _, _ | _, .bound _, modal, _, _, _, _, _, _ | _, .notBound _, modal, _, _, _, _, _, _ | _, .mapsAll _ _, modal, _, _, _, _, _, _ | _, .mapsSome _ _, modal, _, _, _, _, _, _ | _, .someOf _ _, modal, _, _, _, _, _, _ | _, .everyOf _ _, modal, _, _, _, _, _, _ => absurd modal Bool.false_ne_true

/-! ## The sentence of a native type of a term -/

theorem denote_nativeFormula {n : ℕ} (formula : Formula n) (modal : formula.modal = true) {Γ : Ctx Unit}
    (valuation : model.{0}.Valuation Γ) (x : Term Symbol Γ setTy) (env : Fin n → Term Symbol Γ predTy)
    (sets : Env ZFSet.{0} n) (agrees : EnvAgrees valuation env sets) :
    (model.denote (nativeFormula formula x env) valuation).down ↔ extensional.sat sets formula (setValue x valuation) :=
  denote_nativeFormula_regional formula (Formula.regional_of_modal formula modal) valuation x env sets agrees

/-- **The native type `formula` of `term`, as a core sentence of set theory**: some set is described by the term
and has the native type. -/
def nativeTypeSentence (formula : Formula 0) (term : Pattern) : ClosedFormula Symbol :=
  existentialInline (σ := setTy) (conjunctionFormula (describes term (.var .vz)) (nativeFormula formula (.var .vz) Fin.elim0))

theorem denote_nativeTypeSentence {formula : Formula 0} (modal : formula.modal = true) {term : Pattern}
    (holds : IsHF term) (valuation : model.{0}.Valuation []) :
    (model.denote (nativeTypeSentence formula term) valuation).down ↔ Membership.sat Env.closed formula term := by
  rw [nativeTypeSentence, denote_existentialInline]
  change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (describes term (.var .vz))
    (nativeFormula formula (.var .vz) Fin.elim0)) (model.extend (σ := setTy) valuation z)).down) ↔ _
  simp only [true_and, denote_conjunctionFormula, denote_describes holds, setValue_newest]
  rw [sat_iff_extensional (Formula.forward_of_modal formula modal) holds]
  constructor
  · rintro ⟨z, rfl, inside⟩
    exact (denote_nativeFormula formula modal _ (.var .vz) Fin.elim0 Env.closed (fun index => index.elim0)).mp inside
  · intro inside
    exact ⟨zfOf term, rfl,
      (denote_nativeFormula formula modal _ (.var .vz) Fin.elim0 Env.closed (fun index => index.elim0)).mpr inside⟩

/-- **A modal native type holds at a hereditary term exactly when its core sentence is true in the model of the
sets.** -/
theorem models_nativeTypeSentence {formula : Formula 0} (modal : formula.modal = true) {term : Pattern}
    (holds : IsHF term) : model.{0}.models (nativeTypeSentence formula term) ↔ Membership.sat Env.closed formula term :=
  denote_nativeTypeSentence modal holds _

/-- **A regional native type holds at a hereditary term exactly when its core sentence is true in the model of the
sets**: splits included. -/
theorem denote_nativeTypeSentence_regional {formula : Formula 0} (regional : formula.regional = true) {term : Pattern}
    (holds : IsHF term) (valuation : model.{0}.Valuation []) :
    (model.denote (nativeTypeSentence formula term) valuation).down ↔ Membership.sat Env.closed formula term := by
  rw [nativeTypeSentence, denote_existentialInline]
  change (∃ z : ZFSet.{0}, True ∧ (model.denote (conjunctionFormula (describes term (.var .vz))
    (nativeFormula formula (.var .vz) Fin.elim0)) (model.extend (σ := setTy) valuation z)).down) ↔ _
  simp only [true_and, denote_conjunctionFormula, denote_describes holds, setValue_newest]
  rw [sat_iff_extensional (Formula.forward_of_regional formula regional) holds]
  constructor
  · rintro ⟨z, rfl, inside⟩
    exact (denote_nativeFormula_regional formula regional _ (.var .vz) Fin.elim0 Env.closed
      (fun index => index.elim0)).mp inside
  · intro inside
    exact ⟨zfOf term, rfl, (denote_nativeFormula_regional formula regional _ (.var .vz) Fin.elim0 Env.closed
      (fun index => index.elim0)).mpr inside⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
