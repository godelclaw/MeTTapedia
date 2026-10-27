import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembership
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BoundedMorphism

/-!
# The membership language on ZF sets

The membership language `Set ::= {Set*}` with `{x, ...rest} ⇒ x` has a native structure on its terms. This module
gives the same relations on ZF sets (`extensional`) and shows that the denotation of terms carries one onto the
other, so its forward native types are native types of ZF sets.

- **On ZF sets** a step goes from a set to each of its members, by every label that admits the language's one rule
  (`memberLabel`). A set splits into two sets whose union it is, is empty when it is `∅`, and is a singleton
  `{y}` with member `y`. Nothing is built by a constructor or has a body. A term names the set it denotes, and the
  types of a set are read from its members (`SetTyped`): every set is a `Set`, and it is a collection of elements of
  a type when every member has that type.
- **The hereditary terms are a generated substructure** (`hereditary_generated`): what a hereditary term steps
  to, splits into and has as members is hereditary.
- **Denotation is a bounded morphism** (`toZF`) from that substructure to the ZF sets: each step, split and member
  of the set a term denotes comes from one of the term, and emptiness, types and names are reflected.
- **So a forward native type holds at a hereditary term exactly when it holds at the set the term denotes**
  (`sat_iff_extensional`). Forward formulas leave out the past modalities and the quantifiers over a type, which
  reach sets that are not hereditarily finite.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted FreeTypeContext HasType ElementsHaveType)

variable {relEnv : RelationEnv}

/-- A hereditary term of the membership language: a hereditarily finite set. -/
abbrev IsHF (term : Pattern) : Prop := Hereditary membership hfRule.category term

/-! ## Steps by label -/

/-- **The labels of the membership language's steps**: all steps, and the steps of its one rule. -/
def memberLabel : StepLabel → Prop
  | .any => True
  | .rule index => index = 0
  | .under _ _ => False
  | .context _ _ _ => False

/-- The labels of the membership language's steps are its own. -/
theorem memberLabel_own {label : StepLabel} (labelled : memberLabel label) : label.isContext = false := by
  cases label with
  | context => exact labelled.elim
  | any => rfl
  | rule => rfl
  | under => rfl

instance : DecidablePred memberLabel := fun label => by
  cases label <;> unfold memberLabel <;> infer_instance

/-- Every step of the membership language fires its one rule, with no premise evidence. -/
theorem witness_of_valid {source target : Pattern} {witness : Witness}
    (valid : StepValid relEnv membership source witness target) : ∃ initial, witness = .rule 0 initial [] := by
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    match index, found with
    | 0, found =>
      have isMember : rule = memberRule := (Option.some.inj found).symm
      subst isMember
      cases premises
      exact ⟨initial, rfl⟩
    | _ + 1, found => simp [membership] at found

theorem admits_iff {initial : Bindings} (label : StepLabel) :
    label.admits (.rule 0 initial []) = true ↔ memberLabel label := by
  cases label with
  | any => exact iff_of_true rfl trivial
  | rule index =>
    show (ruleOf (.rule 0 initial []) == some index) = true ↔ index = 0
    simp only [ruleOf, beq_iff_eq, Option.some.injEq]
    exact eq_comm
  | under index label =>
    show ((0 == index) && (premiseStepsList []).any label.admits) = true ↔ False
    simp only [premiseStepsList, List.any_nil, Bool.and_false, Bool.false_eq_true]
  | context => exact iff_of_false Bool.false_ne_true id

/-- **A step with a label of the term's own has it exactly when the label admits the one rule.** -/
theorem step_label_iff {first second : Pattern} {label : StepLabel} (own : label.isContext = false) :
    (referenceStructure relEnv membership).step first label second ↔
      memberLabel label ∧ (referenceStructure relEnv membership).step first .any second := by
  constructor
  · rintro ⟨firstState, secondState, redex, contractum, witness, before, redexState, valid, contractumState, after,
      admitted⟩
    obtain ⟨initial, rfl⟩ := witness_of_valid valid
    exact ⟨(admits_iff label).mp (StepLabel.admits_of_base own admitted), firstState, secondState, redex, contractum, _,
      (placed_iff rfl).mpr ((placed_iff own).mp before), redexState, valid, contractumState, after, rfl⟩
  · rintro ⟨labelled, firstState, secondState, redex, contractum, witness, before, redexState, valid, contractumState,
      after, -⟩
    obtain ⟨initial, rfl⟩ := witness_of_valid valid
    exact ⟨firstState, secondState, redex, contractum, _, (placed_iff own).mpr ((placed_iff rfl).mp before), redexState,
      valid, contractumState, after, StepLabel.base_admits ((admits_iff label).mpr labelled)⟩

/-! ## Hereditary terms -/

theorem hf_state {term : Pattern} (holds : IsHF term) : IsState term :=
  (holds.typed membership_hereditary.setCarrier).2

theorem hf_set {term : Pattern} (holds : IsHF term) : ∃ values, term = set values ∧ ∀ value ∈ values, IsHF value := by
  rcases holds.cases with ⟨label, -, atom⟩ | found
  · exact absurd atom (membership_pure _)
  · exact found

/-- A hereditary collection is a set of hereditary terms with no open tail. -/
theorem hf_collection {kind : CollType} {elements : List Pattern} {rest : Option String}
    (holds : IsHF (.collection kind elements rest)) : kind = .hashSet ∧ rest = none ∧ ∀ value ∈ elements, IsHF value := by
  obtain ⟨values, same, inside⟩ := hf_set holds
  simp only [set, Pattern.collection.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  exact ⟨rfl, rfl, inside⟩

/-- Equivalence keeps a term hereditary. -/
theorem hf_of_equivalent {first second : Pattern} (holds : IsHF first)
    (equivalent : ObjectEquivalent relEnv membership .syntax first second) : IsHF second :=
  (hereditary_iff _).mp ((hereditary_canonical (relEnv := relEnv) membership_hereditary).invariant
    ((hereditary_iff _).mpr holds) equivalent)

theorem hf_not_apply {constructor : String} {arguments : List Pattern} : ¬ IsHF (.apply constructor arguments) := by
  intro holds
  obtain ⟨values, same, -⟩ := hf_set holds
  simp [set] at same

theorem hf_not_lambda {name : Option String} {inner : Pattern} : ¬ IsHF (.lambda name inner) := by
  intro holds
  obtain ⟨values, same, -⟩ := hf_set holds
  simp [set] at same

theorem hf_not_multiLambda {arity : ℕ} {names : List String} {inner : Pattern} :
    ¬ IsHF (.multiLambda arity names inner) := by
  intro holds
  obtain ⟨values, same, -⟩ := hf_set holds
  simp [set] at same

theorem hf_not_bvar {index : ℕ} : ¬ IsHF (.bvar index) := by
  intro holds
  obtain ⟨values, same, -⟩ := hf_set holds
  simp [set] at same

theorem hf_binderMetadata {term : Pattern} (holds : IsHF term) : term.hasCanonicalBinderMetadata = true := by
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values _ inside =>
    simp only [set, Pattern.hasCanonicalBinderMetadata,
      Mettapedia.GSLT.LanguageDef.BagNormalForm.hasCanonicalBinderMetadataList_iff]
    exact inside

theorem zfOfList_append (first second : List Pattern) :
    zfOfList (first ++ second) = zfOfList first ∪ zfOfList second := by
  apply ZFSet.ext
  intro element
  simp only [ZFSet.mem_union, mem_zfOfList, List.mem_append]
  constructor
  · rintro ⟨value, member | member, rfl⟩
    · exact Or.inl ⟨value, member, rfl⟩
    · exact Or.inr ⟨value, member, rfl⟩
  · rintro (⟨value, member, rfl⟩ | ⟨value, member, rfl⟩)
    · exact ⟨value, Or.inl member, rfl⟩
    · exact ⟨value, Or.inr member, rfl⟩

/-! ## Types -/

/-- **The types of a ZF set, read from its members**: every set is a `Set`, and it is a set-collection of
elements of a type when each member has that type. -/
def SetTyped : ZFSet.{0} → TypeExpr → Prop
  | _, .base sort => sort = "Set"
  | whole, .collection kind element => kind = .hashSet ∧ ∀ member ∈ whole, SetTyped member element
  | _, .arrow _ _ => False
  | _, .multiBinder _ => False

theorem elementsHaveType_iff {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} :
    ∀ {values : List Pattern}, ElementsHaveType membership free bound values type ↔
      ∀ value ∈ values, HasType membership free bound value type
  | [] => ⟨(fun _ _ member => nomatch member), fun _ => .nil _ _⟩
  | value :: values => by
    constructor
    · intro typed
      cases typed with
      | cons head tail =>
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact elementsHaveType_iff.mp tail other member
    · intro typed
      exact .cons (typed value List.mem_cons_self) (elementsHaveType_iff.mpr fun other member =>
        typed other (List.mem_cons_of_mem _ member))

/-- **A hereditary term has a type exactly when the set it denotes does.** -/
theorem hasType_iff {term : Pattern} (holds : IsHF term) :
    ∀ type : TypeExpr, HasType membership FreeTypeContext.empty [] term type ↔ SetTyped (zfOf term) type := by
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values valuesHold inside =>
    intro type
    constructor
    · intro typed
      cases typed with
      | collection elements =>
        refine ⟨rfl, fun member isMember => ?_⟩
        rw [zfOf_set] at isMember
        obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp isMember
        exact (inside value valueMember _).mp (elementsHaveType_iff.mp elements value valueMember)
      | collectionConstructor declared _ _ =>
        rw [show membership.terms = [hfRule] from rfl, List.mem_singleton] at declared
        subst declared
        rfl
    · intro typed
      cases type with
      | base sort =>
        change sort = "Set" at typed
        subst typed
        exact ((Hereditary.members valuesHold).typed membership_hereditary.setCarrier).1 _ _
      | collection kind element =>
        obtain ⟨rfl, members⟩ := typed
        refine .collection (elementsHaveType_iff.mpr fun value valueMember => ?_)
        refine (inside value valueMember _).mpr (members _ ?_)
        rw [zfOf_set]
        exact mem_zfOfList.mpr ⟨value, valueMember, rfl⟩
      | arrow _ _ => exact typed.elim
      | multiBinder _ => exact typed.elim

/-- **A hereditary term has a type in the language's native structure exactly when the set it denotes does.** -/
theorem typed_iff {term : Pattern} (holds : IsHF term) (type : TypeExpr) :
    (referenceStructure relEnv membership).typed term type ↔ SetTyped (zfOf term) type := by
  constructor
  · rintro ⟨-, representative, equivalent, typedRepresentative⟩
    have wellSorted := (wellSorted_of_carrierTyped (by decide) typedRepresentative).1
    have representativeHolds := hf_of_equivalent holds equivalent
    rw [(membership_equivalent holds representativeHolds).mp equivalent]
    exact (hasType_iff representativeHolds type).mp wellSorted
  · intro typed
    have state := hf_state holds
    exact ⟨state.2, term, Relation.EqvGen.refl _,
      carrierTyped_of_wellSorted ⟨(hasType_iff holds type).mpr typed, hf_binderMetadata holds, state.2, state.1⟩⟩

/-! ## The ZF sets as a native structure -/

/-- **The membership language on ZF sets.** A set steps to each of its members, splits into two sets whose union
it is, is empty when it is `∅`, and is the singleton of its one member. A term names the set it denotes. Sets have
no bodies, so application, which only bodies reach, leaves its first argument as it is. -/
def extensional : NativeStructure ZFSet.{0} where
  step source label target := memberLabel label ∧ target ∈ source
  built _ _ _ := False
  split whole kind first second := kind = .hashSet ∧ whole = first ∪ second
  empty whole kind := kind = .hashSet ∧ whole = ∅
  single whole kind member := kind = .hashSet ∧ whole = {member}
  body _ _ := False
  multiBody _ _ _ := False
  bound _ _ := False
  typed whole type := SetTyped whole type
  named whole term := IsHF term ∧ whole = zfOf term
  same first second := first = second
  apply inner _ := inner
  inRelation _ _ := False

/-- **The hereditary terms are generated**: what one steps to, splits into and has as members is hereditary, and
it is no constructor term, abstraction or bound variable. -/
theorem hereditary_generated : Membership.Generated IsHF where
  step own holds step := step_hereditary holds ((step_label_iff own).mp step).2
  built holds built := (hf_not_apply (hf_of_equivalent holds built.2)).elim
  split holds split := by
    obtain ⟨-, left, right, equivalent, rfl, rfl⟩ := split
    obtain ⟨rfl, -, inside⟩ := hf_collection (hf_of_equivalent holds equivalent)
    exact ⟨.members fun value member => inside value (List.mem_append_left _ member),
      .members fun value member => inside value (List.mem_append_right _ member)⟩
  single holds single := (hf_collection (hf_of_equivalent holds single.2)).2.2 _ List.mem_cons_self
  body holds body := by
    obtain ⟨-, name, equivalent⟩ := body
    exact (hf_not_lambda (hf_of_equivalent holds equivalent)).elim
  multiBody holds body := by
    obtain ⟨-, names, equivalent⟩ := body
    exact (hf_not_multiLambda (hf_of_equivalent holds equivalent)).elim
  apply holds _ := by
    show IsHF (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar _ _)
    rw [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar,
      Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt_eq_self_of_isWellScopedAt (hf_state holds).1]
    exact holds

/-- The hereditary terms with the relations among them. -/
abbrev HFNative := NativeStructure.restrict hereditary_generated

/-- **Denotation is a bounded morphism** from the hereditary terms to the ZF sets. -/
def toZF : BoundedMorphism HFNative extensional where
  map term := zfOf term.1
  step {source _ target} own step := by
    obtain ⟨labelled, step⟩ := (step_label_iff own).mp step
    exact ⟨labelled, (member_step_iff source.2 target.2).mp step⟩
  built built := (hf_not_apply (hf_of_equivalent (Subtype.prop _) built.2)).elim
  split {element _ first second} split := by
    obtain ⟨-, left, right, equivalent, firstEq, secondEq⟩ := split
    have joined := hf_of_equivalent element.2 equivalent
    obtain ⟨rfl, -, -⟩ := hf_collection joined
    refine ⟨rfl, ?_⟩
    rw [(membership_equivalent element.2 joined).mp equivalent, firstEq, secondEq]
    exact zfOfList_append left right
  empty {element _} empty := by
    obtain ⟨-, equivalent⟩ := empty
    have isEmpty := hf_of_equivalent element.2 equivalent
    obtain ⟨rfl, -, -⟩ := hf_collection isEmpty
    exact ⟨rfl, (membership_equivalent element.2 isEmpty).mp equivalent⟩
  single {element _ member} single := by
    obtain ⟨-, equivalent⟩ := single
    have isSingle := hf_of_equivalent element.2 equivalent
    obtain ⟨rfl, -, -⟩ := hf_collection isSingle
    refine ⟨rfl, ?_⟩
    rw [(membership_equivalent element.2 isSingle).mp equivalent]
    apply ZFSet.ext
    intro other
    simp [zfOf, zfOfList]
  body body := by
    obtain ⟨-, name, equivalent⟩ := body
    exact (hf_not_lambda (hf_of_equivalent (Subtype.prop _) equivalent)).elim
  multiBody body := by
    obtain ⟨-, names, equivalent⟩ := body
    exact (hf_not_multiLambda (hf_of_equivalent (Subtype.prop _) equivalent)).elim
  bound bound := (hf_not_bvar (hf_of_equivalent (Subtype.prop _) bound.2)).elim
  typed {element type} typed := (typed_iff element.2 type).mp typed
  named {element term} named := by
    obtain ⟨-, equivalent⟩ := named
    have termHolds := hf_of_equivalent element.2 equivalent
    exact ⟨termHolds, (membership_equivalent element.2 termHolds).mp equivalent⟩
  inRelation isIn := not_inRelation_empty isIn
  stepBack {source label target'} own step := by
    obtain ⟨labelled, member⟩ := step
    obtain ⟨values, same, inside⟩ := hf_set source.2
    have member' : target' ∈ zfOfList values := by
      rw [← zfOf_set, ← same]
      exact member
    obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp member'
    refine ⟨⟨value, inside value valueMember⟩, (step_label_iff own).mpr ⟨labelled, ?_⟩, rfl⟩
    rw [member_step_iff source.2 (inside value valueMember), same, zfOf_set]
    exact mem_zfOfList.mpr ⟨value, valueMember, rfl⟩
  builtBack built := built.elim
  splitBack {element kind first' second'} split := by
    classical
    obtain ⟨rfl, union⟩ := split
    obtain ⟨values, same, inside⟩ := hf_set element.2
    have whole : zfOfList values = first' ∪ second' := by
      rw [← zfOf_set, ← same]
      exact union
    let left := values.filter fun value => zfOf value ∈ first'
    let right := values.filter fun value => zfOf value ∈ second'
    have leftHolds : IsHF (set left) := .members fun value member => inside value (List.mem_of_mem_filter member)
    have rightHolds : IsHF (set right) := .members fun value member => inside value (List.mem_of_mem_filter member)
    have part : ∀ (chosen : ZFSet.{0}), chosen ⊆ zfOfList values →
        zfOfList (values.filter fun value => zfOf value ∈ chosen) = chosen := by
      intro chosen within
      apply ZFSet.ext
      intro other
      rw [mem_zfOfList]
      constructor
      · rintro ⟨value, member, rfl⟩
        simpa using (List.mem_filter.mp member).2
      · intro isMember
        obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp (within isMember)
        exact ⟨value, List.mem_filter.mpr ⟨valueMember, by simpa using isMember⟩, rfl⟩
    have leftValue : zfOfList left = first' :=
      part first' fun other member => whole ▸ ZFSet.mem_union.mpr (Or.inl member)
    have rightValue : zfOfList right = second' :=
      part second' fun other member => whole ▸ ZFSet.mem_union.mpr (Or.inr member)
    have joinedHolds : IsHF (set (left ++ right)) := .members fun value member => by
      rcases List.mem_append.mp member with member | member
      · exact inside value (List.mem_of_mem_filter member)
      · exact inside value (List.mem_of_mem_filter member)
    refine ⟨⟨set left, leftHolds⟩, ⟨set right, rightHolds⟩, ⟨(hf_state element.2).2, left, right, ?_, rfl, rfl⟩,
      by simp only [zfOf_set, leftValue], by simp only [zfOf_set, rightValue]⟩
    refine (membership_equivalent element.2 joinedHolds).mpr ?_
    rw [zfOf_set, zfOfList_append, leftValue, rightValue, ← union]
  emptyBack {element kind} empty := by
    obtain ⟨rfl, isEmpty⟩ := empty
    have emptyHolds : IsHF (set []) := .members fun _ member => nomatch member
    exact ⟨(hf_state element.2).2, (membership_equivalent element.2 emptyHolds).mpr (isEmpty.trans rfl)⟩
  singleBack {element kind member'} single := by
    obtain ⟨rfl, isSingle⟩ := single
    obtain ⟨values, same, inside⟩ := hf_set element.2
    have member : member' ∈ zfOfList values := by
      rw [← zfOf_set, ← same, isSingle]
      exact ZFSet.mem_singleton.mpr rfl
    obtain ⟨value, valueMember, rfl⟩ := mem_zfOfList.mp member
    have singleHolds : IsHF (set [value]) := .members fun other member => by
      rw [List.mem_singleton.mp member]
      exact inside value valueMember
    refine ⟨⟨value, inside value valueMember⟩, ⟨(hf_state element.2).2, ?_⟩, rfl⟩
    refine (membership_equivalent element.2 singleHolds).mpr ?_
    rw [isSingle, zfOf_set]
    apply ZFSet.ext
    intro other
    simp [zfOfList]
  bodyBack body := body.elim
  multiBodyBack body := body.elim
  boundBack bound := bound.elim
  typedBack {element type} typed := (typed_iff element.2 type).mpr typed
  namedBack {element term} named := by
    obtain ⟨termHolds, same⟩ := named
    exact ⟨(hf_state element.2).2, (membership_equivalent element.2 termHolds).mpr same⟩
  inRelationBack isIn := isIn.elim
  sameIff first second := membership_equivalent first.2 second.2

/-- **A forward native type holds at a hereditary term exactly when it holds at the set the term denotes.** -/
theorem sat_iff_extensional {formula : Formula 0} (forward : formula.forward = true) {term : Pattern}
    (holds : IsHF term) :
    Membership.sat Env.closed formula term ↔ extensional.sat Env.closed formula (zfOf term) :=
  ((NativeStructure.Generated.inclusion hereditary_generated).sat_iff formula forward
      (BoundedMorphism.envPreimage_closed _) ⟨term, holds⟩).symm.trans
    (toZF.sat_iff formula forward (BoundedMorphism.envPreimage_closed _) ⟨term, holds⟩)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
