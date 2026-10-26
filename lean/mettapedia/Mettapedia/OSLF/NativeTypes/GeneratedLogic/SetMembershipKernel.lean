import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExtensional
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RelationalTranslation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetLaws

/-!
# Native types of the membership language as propositions of the set package

The membership language's states are the hereditarily finite sets (`SetMembership`), and its forward native types
are native types of ZF sets (`SetMembershipExtensional`). This module states them in the higher-order logic of the
sets, `In`, `Empty`, `Union`, `Power`, `Sep` and `Repl`, and through it as propositions of the package of set theory
over the tower inside the sets.

- **Definitions in set theory** (`zfRelations`): a step from `x` to `y` is `y ∈ x`; a split of `x` into `a` and
  `b` says that the members of `x` are those of `a` and of `b`; `x` is empty when it is `Empty`, and the singleton
  of `m` when its members are exactly `m`; the types of a set are read from its members (`typedDef`); a term names
  the set whose members are the sets its members name (`isSet`). Nothing is built by a constructor or has a body.
- **They define the relations of the ZF sets** (`zfRelations_interprets`) in the model whose individuals are all
  the sets.
- **A native type of a term becomes a sentence** (`nativeSentence`): some set is the one the term denotes and has
  the translation of the formula. For a forward formula and a hereditary term, the sentence is true in the model
  exactly when the term has the native type (`models_nativeSentence`).
- **In the package** (`kernel_holds_iff`): the type of the proofs of the sentence's proposition has a proof in the
  package's set model exactly when the term has the native type; and in every package over the set theory that
  proposition is a type of the least universe (`nativeSentence_typed`), the native type itself a predicate on the
  sets (`nativePredicate_typed`).
- **The front door's verdicts are propositions of the package** (`kernel_verdicts`): every descent from `3` ends
  and `0 ∈ 2` have proofs in the model, and `3 ∈ 3` has none.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula HenkinModel weaken)
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol model member iffFormula fullDomains)
open Relational (Relations Interprets relationTy translate applyRel)

/-- The type of sets in the logic of the sets. -/
abbrev setTy : Ty Unit := ZFSetHenkinInterpretation.set

/-! ## Terms, read as sets -/

mutual
/-- **The newest variable is the set a term denotes**: its members are the sets the term's members denote. -/
def isSet : Pattern → {Γ : Ctx Unit} → Term Symbol (setTy :: Γ) .prop
  | .collection .hashSet values none, _ => .all (iffFormula (member (.var .vz) (.var (.vs .vz))) (oneOf values))
  | _, _ => .bot

/-- The newest variable is the set one of the terms denotes. -/
def oneOf : List Pattern → {Γ : Ctx Unit} → Term Symbol (setTy :: Γ) .prop
  | [], _ => .bot
  | value :: values, _ => .or (isSet value) (oneOf values)
end

theorem denote_oneOf {values : List Pattern}
    (inside : ∀ value ∈ values, ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : ZFSet.{0}),
      (model.denote (isSet value) (model.extend (σ := setTy) valuation x)).down ↔ x = zfOf value)
    {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : ZFSet.{0}) :
    (model.denote (oneOf values) (model.extend (σ := setTy) valuation x)).down ↔ ∃ value ∈ values, x = zfOf value := by
  induction values with
  | nil => exact ⟨False.elim, fun ⟨_, member, _⟩ => nomatch member⟩
  | cons value values ih =>
    change (model.denote (isSet value) (model.extend (σ := setTy) valuation x)).down ∨
      (model.denote (oneOf values) (model.extend (σ := setTy) valuation x)).down ↔ _
    rw [inside value List.mem_cons_self valuation x,
      ih fun other member => inside other (List.mem_cons_of_mem _ member)]
    constructor
    · rintro (rfl | ⟨other, member, rfl⟩)
      · exact ⟨value, List.mem_cons_self, rfl⟩
      · exact ⟨other, List.mem_cons_of_mem _ member, rfl⟩
    · rintro ⟨other, member, rfl⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr ⟨other, member, rfl⟩

/-- **A hereditary term's formula holds exactly at the set the term denotes.** -/
theorem denote_isSet {term : Pattern} (holds : IsHF term) :
    ∀ {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : ZFSet.{0}),
      (model.denote (isSet term) (model.extend (σ := setTy) valuation x)).down ↔ x = zfOf term := by
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values _ inside =>
    intro Γ valuation x
    change (∀ z : ZFSet.{0}, True → ((z ∈ x → (model.denote (oneOf values)
      (model.extend (σ := setTy) (model.extend (σ := setTy) valuation x) z)).down) ∧
      ((model.denote (oneOf values) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation x) z)).down → z ∈ x))) ↔ _
    simp only [denote_oneOf inside, true_implies, zfOf_set]
    constructor
    · intro every
      apply ZFSet.ext
      intro z
      rw [mem_zfOfList]
      exact ⟨fun member => (every z).1 member |>.imp fun _ found => ⟨found.1, found.2.symm⟩,
        fun ⟨value, member, same⟩ => (every z).2 ⟨value, member, same.symm⟩⟩
    · rintro rfl z
      rw [mem_zfOfList]
      exact ⟨fun ⟨value, member, same⟩ => ⟨value, member, same.symm⟩,
        fun ⟨value, member, same⟩ => ⟨value, member, same.symm⟩⟩

/-! ## Types, read from members -/

/-- **The newest variable has the type**: every set is a `Set`, and a set is a set-collection of elements of a
type when each member has that type. -/
def typedDef : TypeExpr → {Γ : Ctx Unit} → Term Symbol (setTy :: Γ) .prop
  | .base sort, _ => if sort = "Set" then .top else .bot
  | .collection kind element, _ =>
    if kind = .hashSet then .all (.imp (member (.var .vz) (.var (.vs .vz))) (typedDef element)) else .bot
  | .arrow _ _, _ => .bot
  | .multiBinder _, _ => .bot

theorem denote_typedDef : ∀ (type : TypeExpr) {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (x : ZFSet.{0}),
    (model.denote (typedDef type) (model.extend (σ := setTy) valuation x)).down ↔ SetTyped x type
  | .base sort, _, valuation, x => by
    by_cases named : sort = "Set"
    · simp only [typedDef, if_pos named]
      exact iff_of_true trivial named
    · simp only [typedDef, if_neg named]
      exact iff_of_false id named
  | .collection kind element, _, valuation, x => by
    by_cases set : kind = .hashSet
    · simp only [typedDef, if_pos set]
      change (∀ z : ZFSet.{0}, True → z ∈ x →
        (model.denote (typedDef element) (model.extend (σ := setTy) (model.extend (σ := setTy) valuation x) z)).down) ↔ _
      simp only [denote_typedDef element, true_implies]
      exact ⟨fun every => ⟨set, every⟩, fun found => found.2⟩
    · simp only [typedDef, if_neg set]
      exact iff_of_false id fun found => set found.1
  | .arrow _ _, _, _, _ => iff_of_false id id
  | .multiBinder _, _, _, _ => iff_of_false id id

/-! ## The relations, defined in set theory -/

/-- A relation of the given arity that holds of nothing. -/
def noRelation : (arity : ℕ) → {Γ : Ctx Unit} → Term Symbol Γ (relationTy setTy arity)
  | 0, _ => .bot
  | arity + 1, _ => .lam (noRelation arity)

theorem applyRel_noRelation : ∀ (arity : ℕ) {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ) (parts : List ZFSet.{0}),
    ¬ applyRel model.{0} (Equiv.refl _) arity (model.denote (noRelation arity) valuation) parts
  | 0, _, _, [] => id
  | 0, _, _, _ :: _ => id
  | _ + 1, _, _, [] => id
  | arity + 1, _, valuation, first :: rest => applyRel_noRelation arity (model.extend (σ := setTy) valuation first) rest

/-- **The relations of the membership language, defined in set theory.** -/
def zfRelations : Relations Symbol setTy where
  step label := if memberLabel label then .lam (.lam (member (.var .vz) (.var (.vs .vz)))) else .lam (.lam .bot)
  built _ arity := .lam (noRelation arity)
  split kind := if kind = .hashSet then
      .lam (.lam (.lam (.all (iffFormula (member (.var .vz) (.var (.vs (.vs (.vs .vz)))))
        (.or (member (.var .vz) (.var (.vs (.vs .vz)))) (member (.var .vz) (.var (.vs .vz))))))))
    else .lam (.lam (.lam .bot))
  empty kind := if kind = .hashSet then .lam (.eq (.var .vz) (.const .empty)) else .lam .bot
  single kind := if kind = .hashSet then
      .lam (.lam (.all (iffFormula (member (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz))))))
    else .lam (.lam .bot)
  body := .lam (.lam .bot)
  multiBody _ := .lam (.lam .bot)
  bound _ := .lam .bot
  typed type := .lam (typedDef type)
  named term := if hereditary membership hfRule.category term then .lam (isSet term) else .lam .bot
  apply := .lam (.lam (.var (.vs .vz)))
  same := .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))

section Denotations

variable {Γ : Ctx Unit} (valuation : model.{0}.Valuation Γ)

theorem denote_step (label : StepLabel) (source target : ZFSet.{0}) :
    (model.denote (zfRelations.step label) valuation source target).down ↔ extensional.step source label target := by
  by_cases labelled : memberLabel label
  · simp only [zfRelations, if_pos labelled]
    exact ⟨fun member => ⟨labelled, member⟩, fun found => found.2⟩
  · simp only [zfRelations, if_neg labelled]
    exact iff_of_false id fun found => labelled found.1

theorem denote_split (kind : CollType) (whole first second : ZFSet.{0}) :
    (model.denote (zfRelations.split kind) valuation whole first second).down ↔
      extensional.split whole kind first second := by
  by_cases set : kind = .hashSet
  · simp only [zfRelations, if_pos set]
    change (∀ z : ZFSet.{0}, True → ((z ∈ whole → z ∈ first ∨ z ∈ second) ∧
      (z ∈ first ∨ z ∈ second → z ∈ whole))) ↔ _
    simp only [true_implies]
    constructor
    · intro every
      exact ⟨set, ZFSet.ext fun z => by rw [ZFSet.mem_union]; exact ⟨(every z).1, (every z).2⟩⟩
    · rintro ⟨-, rfl⟩ z
      rw [ZFSet.mem_union]
      exact ⟨id, id⟩
  · simp only [zfRelations, if_neg set]
    exact iff_of_false id fun found => set found.1

theorem denote_empty (kind : CollType) (whole : ZFSet.{0}) :
    (model.denote (zfRelations.empty kind) valuation whole).down ↔ extensional.empty whole kind := by
  by_cases set : kind = .hashSet
  · simp only [zfRelations, if_pos set]
    exact ⟨fun same => ⟨set, same⟩, fun found => found.2⟩
  · simp only [zfRelations, if_neg set]
    exact iff_of_false id fun found => set found.1

theorem denote_single (kind : CollType) (whole member : ZFSet.{0}) :
    (model.denote (zfRelations.single kind) valuation whole member).down ↔ extensional.single whole kind member := by
  by_cases set : kind = .hashSet
  · simp only [zfRelations, if_pos set]
    change (∀ z : ZFSet.{0}, True → ((z ∈ whole → z = member) ∧ (z = member → z ∈ whole))) ↔ _
    simp only [true_implies]
    constructor
    · intro every
      exact ⟨set, ZFSet.ext fun z => by rw [ZFSet.mem_singleton]; exact ⟨(every z).1, (every z).2⟩⟩
    · rintro ⟨-, rfl⟩ z
      rw [ZFSet.mem_singleton]
      exact ⟨id, id⟩
  · simp only [zfRelations, if_neg set]
    exact iff_of_false id fun found => set found.1

theorem denote_named (term : Pattern) (whole : ZFSet.{0}) :
    (model.denote (zfRelations.named term) valuation whole).down ↔ extensional.named whole term := by
  by_cases holds : hereditary membership hfRule.category term = true
  · simp only [zfRelations, if_pos holds]
    change (model.denote (isSet term) (model.extend (σ := setTy) valuation whole)).down ↔ _
    rw [denote_isSet ((hereditary_iff _).mp holds)]
    exact ⟨fun same => ⟨(hereditary_iff _).mp holds, same⟩, fun found => found.2⟩
  · simp only [zfRelations, if_neg holds]
    exact iff_of_false id fun found => holds ((hereditary_iff _).mpr found.1)

theorem denote_typed (type : TypeExpr) (whole : ZFSet.{0}) :
    (model.denote (zfRelations.typed type) valuation whole).down ↔ extensional.typed whole type :=
  denote_typedDef type valuation whole

end Denotations

/-- **The definitions denote the relations of the ZF sets** in the model whose individuals are all the sets. -/
theorem zfRelations_interprets : Interprets model.{0} (Equiv.refl _) zfRelations extensional where
  step valuation label source target := denote_step valuation label source target
  built valuation _ arity whole parts :=
    iff_of_false (applyRel_noRelation arity (model.extend (σ := setTy) valuation whole) parts) fun found => found.1
  split valuation kind whole first second := denote_split valuation kind whole first second
  empty valuation kind whole := denote_empty valuation kind whole
  single valuation kind whole member := denote_single valuation kind whole member
  body _ _ _ := Iff.rfl
  multiBody _ _ _ _ := Iff.rfl
  bound _ _ _ := Iff.rfl
  typed valuation type whole := denote_typed valuation type whole
  named valuation term whole := denote_named valuation term whole
  apply _ _ _ := rfl
  same _ _ _ := Iff.rfl

/-! ## Native types as sentences of set theory -/

/-- **The native type `formula` of `term`, as a sentence of set theory**: some set is the one the term denotes,
and it has the translation of the formula. -/
def nativeSentence (formula : Formula 0) (term : Pattern) : ClosedFormula Symbol :=
  .ex (.and (isSet term) (.app (weaken (translate zfRelations formula)) (.var .vz)))

/-- The sentence of a forward native type of a hereditary term holds, at any valuation, exactly when the term has
the native type. -/
theorem denote_nativeSentence {formula : Formula 0} (forward : formula.forward = true) {term : Pattern}
    (holds : IsHF term) (valuation : model.{0}.Valuation []) :
    (model.denote (nativeSentence formula term) valuation).down ↔ Membership.sat Env.closed formula term := by
  change (∃ x : ZFSet.{0}, True ∧ (model.denote (isSet term) (model.extend (σ := setTy) valuation x)).down ∧
    (model.denote (weaken (translate zfRelations formula)) (model.extend (σ := setTy) valuation x) x).down) ↔ _
  simp only [denote_isSet holds, true_and]
  rw [sat_iff_extensional forward holds]
  have unweakened : (model.denote (weaken (translate zfRelations formula))
      (model.extend (σ := setTy) valuation (zfOf term)) (zfOf term)).down =
        (model.denote (translate zfRelations formula) valuation (zfOf term)).down :=
    congrArg (fun value : Ty.denote model.{0}.Carrier (Ty.arr setTy .prop) => ULift.down (value (zfOf term)))
      (Mettapedia.Logic.HOL.Soundness.denote_weaken (σ := setTy) model (translate zfRelations formula) valuation
        (zfOf term))
  constructor
  · rintro ⟨x, rfl, inside⟩
    exact (Relational.denote_translate_closed fullDomains zfRelations_interprets formula valuation _).mp
      (unweakened ▸ inside)
  · intro inside
    exact ⟨zfOf term, rfl, unweakened ▸
      (Relational.denote_translate_closed fullDomains zfRelations_interprets formula valuation _).mpr inside⟩

/-- **A forward native type holds at a hereditary term exactly when its sentence is true in the model of the
sets.** -/
theorem models_nativeSentence {formula : Formula 0} (forward : formula.forward = true) {term : Pattern}
    (holds : IsHF term) : model.{0}.models (nativeSentence formula term) ↔ Membership.sat Env.closed formula term :=
  denote_nativeSentence forward holds _

/-! ## In the package of set theory -/

section Kernel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetUniverseInterpretation (embed)
open ZFSetUniverseClosure (CofinalInaccessibles)

variable {L : Type} [LevelOrder L]

/-- **The native type as a predicate of the package**: in every package over the set theory, the term of its
translation is a function from the sets to the propositions. -/
theorem nativePredicate_typed {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
    (formula : Formula 0) :
    CTyped Q (ctxTm []) (trTerm (embed (translate zfRelations formula))) (tyTm (Ty.arr setTy .prop)) :=
  trTerm_typed covers (embed (translate zfRelations formula))

/-- **The native type of a term as a proposition of the package**: in every package over the set theory, the
proofs of its sentence form a type of the least universe. -/
theorem nativeSentence_typed {R' : Rules (Head L)} {Q : ChurchRules R'} (covers : OverSetTheory Q)
    (formula : Formula 0) (term : Pattern) :
    CTyped Q .nil (cHolds (trTerm (embed (nativeSentence formula term)))) MegalodonHOTG.U0 :=
  holds_trTerm_typed covers (embed (nativeSentence formula term))

variable (large : CofinalInaccessibles.{1}) {ground : ZFSet.{1}} {ν : Nat → Above L}
  {consts : DeclName → ZFSet.{1}} {around : ZFSet.{1} → ZFSet.{1}}

/-- **A forward native type holds at a hereditary term exactly when the type of the proofs of its sentence has a
proof in the set model of the package**, at every reading of the constants of set theory. -/
theorem kernel_holds_iff
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1)) around consts)
    {formula : Formula 0} (forward : formula.forward = true) {term : Pattern} (holds : IsHF term) :
    (∅ : ZFSet.{1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (trTerm (embed (nativeSentence formula term)))) Fin.elim0 ↔
      Membership.sat Env.closed formula term := by
  rw [ev_holds_embed large reads, Square.square_truth_iff]
  exact models_nativeSentence forward holds

/-- **The front door's verdicts are propositions of the package**: every descent from `3` ends and `0 ∈ 2` have
proofs in the set model of the package, and `3 ∈ 3` has none. -/
theorem kernel_verdicts
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1)) around consts) :
    (∅ : ZFSet.{1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (trTerm (embed (nativeSentence (.mu (.necessarily .any (.var 0))) three)))) Fin.elim0 ∧
      (∅ : ZFSet.{1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (trTerm (embed (nativeSentence (.possibly .any (.is zero)) two)))) Fin.elim0 ∧
      (∅ : ZFSet.{1}) ∉ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (trTerm (embed (nativeSentence (.possibly .any (.is three)) three)))) Fin.elim0 :=
  ⟨(kernel_holds_iff large reads rfl three_holds).mpr (ask_proved three_wellFounded_answer),
    (kernel_holds_iff large reads rfl two_holds).mpr (ask_proved zero_mem_two_answer),
    fun inside => ask_refuted three_not_mem_self_answer ((kernel_holds_iff large reads rfl three_holds).mp inside)⟩

end Kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
