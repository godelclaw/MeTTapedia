import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference

/-!
# Native types do not depend on the representative

Every generated formula is monotone in its fixed-point environment (`sat_mono`), since formulas in
negation normal form have no negation.

A structure is saturated by an equivalence when each of its relations reads the element through it
(`Saturated`). Then every formula holds alike at equivalent elements, once the environment's sets are
closed under the equivalence (`sat_congr`). For least fixed points this passes through the interior of
a closed set, and for greatest fixed points through the closure of an invariant set.

The native structure of a language is saturated by the terms it cannot tell apart: equal patterns, or
object terms equivalent modulo the equations that are both closed or both open
(`referenceStructure_saturated`). So a closed generated formula holds alike at equivalent states: it is
a native type of the language modulo its equations (`sat_respects_equivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula

universe u

/-! ## Environments -/

namespace Env

variable {Carrier : Type u}

theorem extend_mono {n : ℕ} {small large : Env Carrier n} (sub : ∀ index, small index ⊆ large index)
    {set : Set Carrier} : ∀ index, small.extend set index ⊆ large.extend set index := by
  intro index
  refine Fin.cases ?_ (fun index' => ?_) index
  · exact le_rfl
  · exact sub index'

theorem extend_sub {n : ℕ} (env : Env Carrier n) {small large : Set Carrier} (sub : small ⊆ large) :
    ∀ index, env.extend small index ⊆ env.extend large index := by
  intro index
  refine Fin.cases ?_ (fun index' => ?_) index
  · exact sub
  · exact le_rfl

/-- An environment whose sets are closed under the equivalence. -/
def Respects (equivalent : Carrier → Carrier → Prop) {n : ℕ} (env : Env Carrier n) : Prop :=
  ∀ index first second, equivalent first second → first ∈ env index → second ∈ env index

theorem Respects.extend {equivalent : Carrier → Carrier → Prop} {n : ℕ} {env : Env Carrier n}
    (respects : env.Respects equivalent) {set : Set Carrier}
    (setRespects : ∀ first second, equivalent first second → first ∈ set → second ∈ set) :
    (env.extend set).Respects equivalent := by
  intro index first second related
  refine Fin.cases (fun member => ?_) (fun index' member => ?_) index
  · exact setRespects first second related member
  · exact respects index' first second related member

theorem respects_closed (equivalent : Carrier → Carrier → Prop) : (closed : Env Carrier 0).Respects equivalent :=
  fun index => index.elim0

end Env

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

/-! ## Monotonicity -/

mutual
/-- **Every formula is monotone in its environment.** -/
theorem sat_mono : ∀ {n : ℕ} (formula : Formula n) {small large : Env Carrier n}, (∀ index, small index ⊆ large index) →
    ∀ element, S.sat small formula element → S.sat large formula element
  | _, .top, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, holds => holds
  | _, .and left right, _, _, sub, element, holds =>
    ⟨sat_mono left sub element holds.1, sat_mono right sub element holds.2⟩
  | _, .or left right, _, _, sub, element, holds =>
    holds.imp (sat_mono left sub element) (sat_mono right sub element)
  | _, .var index, _, _, sub, _, holds => sub index holds
  | _, .mu inner, _, _, sub, element, holds => fun closed closedHolds =>
    holds closed fun other otherHolds => closedHolds other (sat_mono inner (Env.extend_mono sub) other otherHolds)
  | _, .nu inner, _, _, sub, element, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    exact ⟨invariant, member, fun other otherMember =>
      sat_mono inner (Env.extend_mono sub) other (preserved other otherMember)⟩
  | _, .possibly _ formula, _, _, sub, _, holds => by
    obtain ⟨next, step, nextHolds⟩ := holds
    exact ⟨next, step, sat_mono formula sub next nextHolds⟩
  | _, .necessarily _ formula, _, _, sub, _, holds => fun next step => sat_mono formula sub next (holds next step)
  | _, .sometimeBefore _ formula, _, _, sub, _, holds => by
    obtain ⟨previous, step, previousHolds⟩ := holds
    exact ⟨previous, step, sat_mono formula sub previous previousHolds⟩
  | _, .alwaysBefore _ formula, _, _, sub, _, holds => fun previous step =>
    sat_mono formula sub previous (holds previous step)
  | _, .atLeast _ _ _ formula, _, _, sub, _, holds =>
    holds.mono fun other ⟨step, otherHolds⟩ => ⟨step, sat_mono formula sub other otherHolds⟩
  | _, .allButFewer _ _ _ formula, _, _, sub, _, holds => fun many =>
    holds (many.mono fun other ⟨step, fails⟩ => ⟨step, fun otherHolds => fails (sat_mono formula sub other otherHolds)⟩)
  | _, .built _ arguments, _, _, sub, _, holds => by
    obtain ⟨parts, isBuilt, all⟩ := holds
    exact ⟨parts, isBuilt, satAll_mono arguments sub parts all⟩
  | _, .everyBuilt _ arguments, _, _, sub, _, holds => fun parts isBuilt =>
    satSome_mono arguments sub parts (holds parts isBuilt)
  | _, .split _ left right, _, _, sub, _, holds => by
    obtain ⟨first, second, isSplit, firstHolds, secondHolds⟩ := holds
    exact ⟨first, second, isSplit, sat_mono left sub first firstHolds, sat_mono right sub second secondHolds⟩
  | _, .everySplit _ left right, _, _, sub, _, holds => fun first second isSplit =>
    (holds first second isSplit).imp (sat_mono left sub first) (sat_mono right sub second)
  | _, .empty _, _, _, _, _, holds => holds
  | _, .nonEmpty _, _, _, _, _, holds => holds
  | _, .single _ formula, _, _, sub, _, holds => by
    obtain ⟨member, isSingle, memberHolds⟩ := holds
    exact ⟨member, isSingle, sat_mono formula sub member memberHolds⟩
  | _, .everySingle _ formula, _, _, sub, _, holds => fun member isSingle =>
    sat_mono formula sub member (holds member isSingle)
  | _, .body formula, _, _, sub, _, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    exact ⟨inner, isBody, sat_mono formula sub inner innerHolds⟩
  | _, .everyBody formula, _, _, sub, _, holds => fun inner isBody => sat_mono formula sub inner (holds inner isBody)
  | _, .multiBody _ formula, _, _, sub, _, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    exact ⟨inner, isBody, sat_mono formula sub inner innerHolds⟩
  | _, .everyMultiBody _ formula, _, _, sub, _, holds => fun inner isBody =>
    sat_mono formula sub inner (holds inner isBody)
  | _, .bound _, _, _, _, _, holds => holds
  | _, .notBound _, _, _, _, _, holds => holds
  | _, .typed _, _, _, _, _, holds => holds
  | _, .untyped _, _, _, _, _, holds => holds
  | _, .is _, _, _, _, _, holds => holds
  | _, .isNot _, _, _, _, _, holds => holds
  | _, .inRelation _, _, _, _, _, holds => holds
  | _, .notInRelation _, _, _, _, _, holds => holds
  | _, .mapsAll argument result, _, _, sub, _, holds => by
    obtain ⟨inner, isBody, every⟩ := holds
    exact ⟨inner, isBody, fun value => (every value).imp (sat_mono argument sub value) (sat_mono result sub _)⟩
  | _, .mapsSome argument result, _, _, sub, _, holds => fun inner isBody => by
    obtain ⟨value, argumentHolds, resultHolds⟩ := holds inner isBody
    exact ⟨value, sat_mono argument sub value argumentHolds, sat_mono result sub _ resultHolds⟩
  | _, .someOf _ formula, _, _, sub, _, holds => by
    obtain ⟨witness, isTyped, witnessHolds⟩ := holds
    exact ⟨witness, isTyped, sat_mono formula sub witness witnessHolds⟩
  | _, .everyOf _ formula, _, _, sub, _, holds => fun witness isTyped =>
    sat_mono formula sub witness (holds witness isTyped)

theorem satAll_mono : ∀ {n : ℕ} (formulas : Formulas n) {small large : Env Carrier n},
    (∀ index, small index ⊆ large index) → ∀ parts, S.satAll small formulas parts → S.satAll large formulas parts
  | _, .nil, _, _, _, [], _ => trivial
  | _, .cons formula formulas, _, _, sub, part :: parts, holds =>
    ⟨sat_mono formula sub part holds.1, satAll_mono formulas sub parts holds.2⟩
  | _, .nil, _, _, _, _ :: _, holds => holds.elim
  | _, .cons _ _, _, _, _, [], holds => holds.elim

theorem satSome_mono : ∀ {n : ℕ} (formulas : Formulas n) {small large : Env Carrier n},
    (∀ index, small index ⊆ large index) → ∀ parts, S.satSome small formulas parts → S.satSome large formulas parts
  | _, .nil, _, _, _, [], holds => holds
  | _, .cons formula formulas, _, _, sub, part :: parts, holds =>
    holds.imp (sat_mono formula sub part) (satSome_mono formulas sub parts)
  | _, .nil, _, _, _, _ :: _, _ => trivial
  | _, .cons _ _, _, _, _, [], _ => trivial
end

/-! ## Invariance under a saturating equivalence -/

/-- **A structure saturated by an equivalence**: each relation reads the element through it. -/
structure Saturated (equivalent : Carrier → Carrier → Prop) : Prop where
  equivalence : Equivalence equivalent
  stepSource : ∀ {first second : Carrier} {label next},
    equivalent first second → S.step first label next → S.step second label next
  stepTarget : ∀ {previous label} {first second : Carrier},
    equivalent first second → S.step previous label first → S.step previous label second
  built : ∀ {first second : Carrier} {constructor parts},
    equivalent first second → S.built first constructor parts → S.built second constructor parts
  split : ∀ {first second : Carrier} {kind left right},
    equivalent first second → S.split first kind left right → S.split second kind left right
  empty : ∀ {first second : Carrier} {kind}, equivalent first second → S.empty first kind → S.empty second kind
  single : ∀ {first second : Carrier} {kind member},
    equivalent first second → S.single first kind member → S.single second kind member
  body : ∀ {first second : Carrier} {inner}, equivalent first second → S.body first inner → S.body second inner
  multiBody : ∀ {first second : Carrier} {arity inner},
    equivalent first second → S.multiBody first arity inner → S.multiBody second arity inner
  bound : ∀ {first second : Carrier} {index}, equivalent first second → S.bound first index → S.bound second index
  typed : ∀ {first second : Carrier} {type}, equivalent first second → S.typed first type → S.typed second type
  named : ∀ {first second : Carrier} {term}, equivalent first second → S.named first term → S.named second term
  inRelation : ∀ {first second : Carrier} {relation},
    equivalent first second → S.inRelation first relation → S.inRelation second relation

variable {S} {equivalent : Carrier → Carrier → Prop}

/-- A step in either direction reads the element through the equivalence. -/
theorem Saturated.stepIn (saturated : S.Saturated equivalent) {direction : Direction} {first second : Carrier}
    {label : StepLabel} {other : Carrier} (related : equivalent first second)
    (step : S.stepIn direction first label other) : S.stepIn direction second label other := by
  cases direction
  · exact saturated.stepSource related step
  · exact saturated.stepTarget related step

/-- **Formulas hold alike at equivalent elements**, in environments closed under the equivalence. -/
theorem sat_congr (saturated : S.Saturated equivalent) : ∀ {n : ℕ} (formula : Formula n) {env : Env Carrier n},
    env.Respects equivalent → ∀ {first second : Carrier}, equivalent first second →
      S.sat env formula first → S.sat env formula second
  | _, .top, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, holds => holds
  | _, .and left right, _, respects, _, _, related, holds =>
    ⟨sat_congr saturated left respects related holds.1, sat_congr saturated right respects related holds.2⟩
  | _, .or left right, _, respects, _, _, related, holds =>
    holds.imp (sat_congr saturated left respects related) (sat_congr saturated right respects related)
  | _, .var index, _, respects, first, second, related, holds => respects index first second related holds
  | _, .mu inner, env, respects, first, second, related, holds => by
    intro closed closedHolds
    let interior : Set Carrier := {element | ∀ other, equivalent element other → other ∈ closed}
    have interiorClosed : ∀ a b, equivalent a b → a ∈ interior → b ∈ interior :=
      fun a b ab member other bOther => member other (saturated.equivalence.trans ab bOther)
    have inside : interior ⊆ closed := fun element member => member element (saturated.equivalence.refl element)
    have interiorHolds := holds interior fun element elementHolds other related' =>
      closedHolds other (S.sat_mono inner (env.extend_sub inside) other
        (sat_congr saturated inner (respects.extend interiorClosed) related' elementHolds))
    exact interiorHolds second related
  | _, .nu inner, env, respects, first, second, related, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    let closure : Set Carrier := {element | ∃ origin ∈ invariant, equivalent origin element}
    have closureClosed : ∀ a b, equivalent a b → a ∈ closure → b ∈ closure := by
      rintro a b ab ⟨origin, originMember, originA⟩
      exact ⟨origin, originMember, saturated.equivalence.trans originA ab⟩
    have contains : invariant ⊆ closure := fun element member => ⟨element, member, saturated.equivalence.refl element⟩
    refine ⟨closure, ⟨first, member, related⟩, ?_⟩
    rintro element ⟨origin, originMember, originRelated⟩
    exact sat_congr saturated inner (respects.extend closureClosed) originRelated
      (S.sat_mono inner (env.extend_sub contains) origin (preserved origin originMember))
  | _, .possibly _ formula, _, _, _, _, related, holds => by
    obtain ⟨next, step, nextHolds⟩ := holds
    exact ⟨next, saturated.stepSource related step, nextHolds⟩
  | _, .necessarily _ _, _, _, _, _, related, holds => fun next step =>
    holds next (saturated.stepSource (saturated.equivalence.symm related) step)
  | _, .sometimeBefore _ _, _, _, _, _, related, holds => by
    obtain ⟨previous, step, previousHolds⟩ := holds
    exact ⟨previous, saturated.stepTarget related step, previousHolds⟩
  | _, .alwaysBefore _ _, _, _, _, _, related, holds => fun previous step =>
    holds previous (saturated.stepTarget (saturated.equivalence.symm related) step)
  | _, .atLeast _ _ _ _, _, _, _, _, related, holds =>
    holds.mono fun _ ⟨step, otherHolds⟩ => ⟨saturated.stepIn related step, otherHolds⟩
  | _, .allButFewer _ _ _ _, _, _, _, _, related, holds => fun many =>
    holds (many.mono fun _ ⟨step, fails⟩ => ⟨saturated.stepIn (saturated.equivalence.symm related) step, fails⟩)
  | _, .built _ _, _, _, _, _, related, holds => by
    obtain ⟨parts, isBuilt, all⟩ := holds
    exact ⟨parts, saturated.built related isBuilt, all⟩
  | _, .everyBuilt _ _, _, _, _, _, related, holds => fun parts isBuilt =>
    holds parts (saturated.built (saturated.equivalence.symm related) isBuilt)
  | _, .split _ _ _, _, _, _, _, related, holds => by
    obtain ⟨left, right, isSplit, leftHolds, rightHolds⟩ := holds
    exact ⟨left, right, saturated.split related isSplit, leftHolds, rightHolds⟩
  | _, .everySplit _ _ _, _, _, _, _, related, holds => fun left right isSplit =>
    holds left right (saturated.split (saturated.equivalence.symm related) isSplit)
  | _, .empty _, _, _, _, _, related, holds => saturated.empty related holds
  | _, .nonEmpty _, _, _, _, _, related, holds => fun isEmpty =>
    holds (saturated.empty (saturated.equivalence.symm related) isEmpty)
  | _, .single _ _, _, _, _, _, related, holds => by
    obtain ⟨member, isSingle, memberHolds⟩ := holds
    exact ⟨member, saturated.single related isSingle, memberHolds⟩
  | _, .everySingle _ _, _, _, _, _, related, holds => fun member isSingle =>
    holds member (saturated.single (saturated.equivalence.symm related) isSingle)
  | _, .body _, _, _, _, _, related, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    exact ⟨inner, saturated.body related isBody, innerHolds⟩
  | _, .everyBody _, _, _, _, _, related, holds => fun inner isBody =>
    holds inner (saturated.body (saturated.equivalence.symm related) isBody)
  | _, .multiBody _ _, _, _, _, _, related, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    exact ⟨inner, saturated.multiBody related isBody, innerHolds⟩
  | _, .everyMultiBody _ _, _, _, _, _, related, holds => fun inner isBody =>
    holds inner (saturated.multiBody (saturated.equivalence.symm related) isBody)
  | _, .bound _, _, _, _, _, related, holds => saturated.bound related holds
  | _, .notBound _, _, _, _, _, related, holds => fun isBound =>
    holds (saturated.bound (saturated.equivalence.symm related) isBound)
  | _, .typed _, _, _, _, _, related, holds => saturated.typed related holds
  | _, .untyped _, _, _, _, _, related, holds => fun isTyped =>
    holds (saturated.typed (saturated.equivalence.symm related) isTyped)
  | _, .is _, _, _, _, _, related, holds => saturated.named related holds
  | _, .isNot _, _, _, _, _, related, holds => fun isNamed =>
    holds (saturated.named (saturated.equivalence.symm related) isNamed)
  | _, .inRelation _, _, _, _, _, related, holds => saturated.inRelation related holds
  | _, .notInRelation _, _, _, _, _, related, holds => fun isIn =>
    holds (saturated.inRelation (saturated.equivalence.symm related) isIn)
  | _, .mapsAll _ _, _, _, _, _, related, holds => by
    obtain ⟨inner, isBody, every⟩ := holds
    exact ⟨inner, saturated.body related isBody, every⟩
  | _, .mapsSome _ _, _, _, _, _, related, holds => fun inner isBody =>
    holds inner (saturated.body (saturated.equivalence.symm related) isBody)
  | _, .someOf _ _, _, _, _, _, _, holds => holds
  | _, .everyOf _ _, _, _, _, _, _, holds => holds

end NativeStructure

/-! ## The native structure of a language -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-- A closed pattern. -/
abbrev IsClosed (pattern : Pattern) : Prop := pattern.isWellScopedAt 0 = true

/-- **Terms a language's structure cannot tell apart**: the same pattern, or object terms equivalent
modulo the equations, in a reading, that are both closed or both open. -/
def Indistinct (relEnv : RelationEnv) (language : LanguageDef) (reading : LanguageReading) (first second : Pattern) :
    Prop :=
  first = second ∨
    (IsObject first ∧ IsObject second ∧ (IsClosed first ↔ IsClosed second) ∧
      ObjectEquivalent relEnv language reading first second)

namespace Indistinct

variable {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}

theorem equivalence : Equivalence (Indistinct relEnv language reading) where
  refl _ := Or.inl rfl
  symm := by
    rintro first second (rfl | ⟨firstObject, secondObject, closed, equivalent⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨secondObject, firstObject, closed.symm, ObjectEquivalent.equivalence.symm equivalent⟩
  trans := by
    rintro first second third (rfl | ⟨firstObject, secondObject, closed, equivalent⟩) second'
    · exact second'
    · rcases second' with rfl | ⟨-, thirdObject, closed', equivalent'⟩
      · exact Or.inr ⟨firstObject, secondObject, closed, equivalent⟩
      · exact Or.inr ⟨firstObject, thirdObject, closed.trans closed',
          ObjectEquivalent.equivalence.trans equivalent equivalent'⟩

theorem objectEquivalent {first second : Pattern} (related : Indistinct relEnv language reading first second) :
    ObjectEquivalent relEnv language reading first second := by
  rcases related with rfl | ⟨-, -, -, equivalent⟩
  · exact Relation.EqvGen.refl _
  · exact equivalent

theorem object {first second : Pattern} (related : Indistinct relEnv language reading first second)
    (object : IsObject first) : IsObject second := by
  rcases related with rfl | ⟨-, secondObject, -, -⟩
  · exact object
  · exact secondObject

theorem state {first second : Pattern} (related : Indistinct relEnv language reading first second)
    (state : IsState first) : IsState second := by
  rcases related with rfl | ⟨-, secondObject, closed, -⟩
  · exact state
  · exact ⟨closed.mp state.1, secondObject⟩

/-- Equivalent states are indistinct. -/
theorem of_states {first second : Pattern} (firstState : IsState first) (secondState : IsState second)
    (equivalent : ObjectEquivalent relEnv language reading first second) :
    Indistinct relEnv language reading first second :=
  Or.inr ⟨firstState.2, secondState.2, iff_of_true firstState.1 secondState.1, equivalent⟩

end Indistinct

/-- **A language's structure reads every term modulo its equations.** -/
theorem referenceStructure_saturated (relEnv : RelationEnv) (language : LanguageDef)
    (reading : LanguageReading := .syntax) :
    (referenceStructure relEnv language reading).Saturated (Indistinct relEnv language reading) := by
  have equivalence : Equivalence (ObjectEquivalent relEnv language reading) := ObjectEquivalent.equivalence
  refine ⟨Indistinct.equivalence, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro first second label next related
      ⟨firstState, nextState, redex, contractum, witness, before, redexState, valid, contractumState, after, admits⟩
    exact ⟨related.state firstState, nextState, redex, contractum, witness,
      before.of_equivalent (equivalence.symm related.objectEquivalent), redexState, valid, contractumState, after,
      admits⟩
  · rintro previous label first second related
      ⟨previousState, firstState, redex, contractum, witness, before, redexState, valid, contractumState, after, admits⟩
    exact ⟨previousState, related.state firstState, redex, contractum, witness, before, redexState, valid,
      contractumState, equivalence.trans after related.objectEquivalent, admits⟩
  · rintro first second constructor parts related ⟨object, isBuilt⟩
    exact ⟨related.object object, equivalence.trans (equivalence.symm related.objectEquivalent) isBuilt⟩
  · rintro first second kind left right related ⟨object, leftElements, rightElements, isSplit, rfl, rfl⟩
    exact ⟨related.object object, leftElements, rightElements,
      equivalence.trans (equivalence.symm related.objectEquivalent) isSplit, rfl, rfl⟩
  · rintro first second kind related ⟨object, isEmpty⟩
    exact ⟨related.object object, equivalence.trans (equivalence.symm related.objectEquivalent) isEmpty⟩
  · rintro first second kind member related ⟨object, isSingle⟩
    exact ⟨related.object object, equivalence.trans (equivalence.symm related.objectEquivalent) isSingle⟩
  · rintro first second inner related ⟨object, name, isBody⟩
    exact ⟨related.object object, name, equivalence.trans (equivalence.symm related.objectEquivalent) isBody⟩
  · rintro first second arity inner related ⟨object, names, isBody⟩
    exact ⟨related.object object, names, equivalence.trans (equivalence.symm related.objectEquivalent) isBody⟩
  · rintro first second index related ⟨object, isBound⟩
    exact ⟨related.object object, equivalence.trans (equivalence.symm related.objectEquivalent) isBound⟩
  · rintro first second type related ⟨object, representative, isRepresentative, isTyped⟩
    exact ⟨related.object object, representative,
      equivalence.trans (equivalence.symm related.objectEquivalent) isRepresentative, isTyped⟩
  · rintro first second term related ⟨object, isNamed⟩
    exact ⟨related.object object, equivalence.trans (equivalence.symm related.objectEquivalent) isNamed⟩
  · rintro first second relation related ⟨object, representative, isRepresentative, inTuples⟩
    exact ⟨related.object object, representative,
      equivalence.trans (equivalence.symm related.objectEquivalent) isRepresentative, inTuples⟩

/-- **Formulas hold alike at terms the structure cannot tell apart.** -/
theorem sat_respects_indistinct (relEnv : RelationEnv) (language : LanguageDef) (formula : Formula 0)
    {reading : LanguageReading} {first second : Pattern} (related : Indistinct relEnv language reading first second) :
    (referenceStructure relEnv language reading).sat Env.closed formula first ↔
      (referenceStructure relEnv language reading).sat Env.closed formula second := by
  have saturated := referenceStructure_saturated relEnv language reading
  exact ⟨NativeStructure.sat_congr saturated formula (Env.respects_closed _) related,
    NativeStructure.sat_congr saturated formula (Env.respects_closed _) (saturated.equivalence.symm related)⟩

/-- **A closed generated formula is a native type of the language modulo its equations**: it holds alike
at equivalent states. -/
theorem sat_respects_equivalent (relEnv : RelationEnv) (language : LanguageDef) (formula : Formula 0)
    {reading : LanguageReading} {first second : Pattern} (firstState : IsState first) (secondState : IsState second)
    (equivalent : ObjectEquivalent relEnv language reading first second) :
    (referenceStructure relEnv language reading).sat Env.closed formula first ↔
      (referenceStructure relEnv language reading).sat Env.closed formula second :=
  sat_respects_indistinct relEnv language formula (Indistinct.of_states firstState secondState equivalent)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
