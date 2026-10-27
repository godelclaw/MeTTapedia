import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Equivalence

/-!
# Structural bisimilarity

The first-order formulas (`Formula.firstOrder`) use every former except the hom formers and the
quantifiers over a type: steps forward and backward; constructors, collections and bodies; the atoms
(emptiness, bound variables, types and names); `∧`, `∨`, μ and ν.

A **structural bisimulation** (`StructuralBisimulation`) is a forward-backward bisimulation that also
matches each side's decompositions into related parts, splits into related halves, members and
bodies, and that agrees on the atoms.

- Structurally bisimilar elements satisfy the same first-order formulas
  (`sat_of_structurallyBisimilar`).
- On a structure that is finitely branching in every relation (`FullyImageFinite`), elements that agree
  on every closed first-order formula are structurally bisimilar
  (`firstOrderEquivalent_iff_structurallyBisimilar`).

The second item is the Hennessy–Milner argument once more, with one witness formula per former. A
decomposition is separated position by position: for each of the second element's decompositions,
some position differs, and that position's separator goes into the formula for that position.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

namespace Formula

mutual
/-- **The first-order formulas**: every former except the hom formers, the quantifiers over a type and
counting. -/
def firstOrder : {n : ℕ} → Formula n → Bool
  | _, .mapsAll _ _ | _, .mapsSome _ _ | _, .someOf _ _ | _, .everyOf _ _ | _, .atLeast _ _ _ _
  | _, .allButFewer _ _ _ _ => false
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ | _, .inRelation _ | _, .notInRelation _ => true
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right =>
    firstOrder left && firstOrder right
  | _, .mu inner | _, .nu inner => firstOrder inner
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula | _, .single _ formula | _, .everySingle _ formula | _, .body formula
  | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula => firstOrder formula
  | _, .built _ arguments | _, .everyBuilt _ arguments => firstOrderList arguments

/-- Every formula of the list is first-order. -/
def firstOrderList : {n : ℕ} → Formulas n → Bool
  | _, .nil => true
  | _, .cons formula formulas => firstOrder formula && firstOrderList formulas
end

mutual
theorem firstOrder_dual : ∀ {n : ℕ} (formula : Formula n), (dual formula).firstOrder = formula.firstOrder
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ | _, .mapsAll _ _ | _, .mapsSome _ _
  | _, .someOf _ _ | _, .everyOf _ _ | _, .atLeast _ _ _ _ | _, .allButFewer _ _ _ _
  | _, .inRelation _ | _, .notInRelation _ => by simp [dual, firstOrder]
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right => by
    simp only [dual, firstOrder, firstOrder_dual left, firstOrder_dual right]
  | _, .mu inner | _, .nu inner => by simp only [dual, firstOrder, firstOrder_dual inner]
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula | _, .single _ formula | _, .everySingle _ formula | _, .body formula
  | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula => by
    simp only [dual, firstOrder, firstOrder_dual formula]
  | _, .built _ arguments | _, .everyBuilt _ arguments => by
    simp only [dual, firstOrder, firstOrderList_dualList arguments]

theorem firstOrderList_dualList : ∀ {n : ℕ} (formulas : Formulas n),
    firstOrderList (dualList formulas) = firstOrderList formulas
  | _, .nil => rfl
  | _, .cons formula formulas => by
    simp only [dualList, firstOrderList, firstOrder_dual formula, firstOrderList_dualList formulas]
end

theorem firstOrder_conj {n : ℕ} : ∀ formulas : List (Formula n), (∀ formula ∈ formulas, formula.firstOrder = true) →
    (conj formulas).firstOrder = true
  | [], _ => rfl
  | formula :: formulas, every => by
    simp only [conj, List.foldr_cons, firstOrder, Bool.and_eq_true]
    exact ⟨every formula (List.mem_cons_self ..),
      firstOrder_conj formulas fun other member => every other (List.mem_cons_of_mem _ member)⟩

end Formula

/-- A list of formulas as the arguments of a structural former. -/
def Formulas.ofList {n : ℕ} : List (Formula n) → Formulas n
  | [] => .nil
  | formula :: formulas => .cons formula (ofList formulas)

theorem Formulas.length_ofList {n : ℕ} : ∀ formulas : List (Formula n), (ofList formulas).length = formulas.length
  | [] => rfl
  | _ :: formulas => by simp only [ofList, length, List.length_cons, length_ofList formulas]

theorem Formula.firstOrderList_ofList {n : ℕ} : ∀ formulas : List (Formula n),
    (∀ formula ∈ formulas, formula.firstOrder = true) → firstOrderList (Formulas.ofList formulas) = true
  | [], _ => rfl
  | formula :: formulas, every => by
    simp only [Formulas.ofList, firstOrderList, Bool.and_eq_true]
    exact ⟨every formula (List.mem_cons_self ..),
      firstOrderList_ofList formulas fun other member => every other (List.mem_cons_of_mem _ member)⟩

/-- The first-order fragment, closed under the dual. -/
theorem firstOrder_closed : FragmentClosed fun formula => formula.firstOrder where
  dual := Formula.firstOrder_dual
  top := rfl
  conj := Formula.firstOrder_conj

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

theorem satAll_ofList {n : ℕ} (env : Env Carrier n) : ∀ (formulas : List (Formula n)) (parts : List Carrier),
    S.satAll env (Formulas.ofList formulas) parts ↔ List.Forall₂ (fun formula part => S.sat env formula part) formulas parts
  | [], [] => by simp [Formulas.ofList, satAll]
  | [], _ :: _ => by simp [Formulas.ofList, satAll]
  | _ :: _, [] => by simp [Formulas.ofList, satAll]
  | formula :: formulas, part :: parts => by
    simp only [Formulas.ofList, satAll, List.forall₂_cons, satAll_ofList env formulas parts]

/-! ## Structural bisimulation -/

/-- **A structural bisimulation**: a forward-backward bisimulation that also matches decompositions into
related parts, splits into related halves, members and bodies, and agrees on the atoms. -/
structure StructuralBisimulation (relation : Carrier → Carrier → Prop) : Prop where
  steps : S.Bisimulation relation
  builtForth : ∀ {first second constructor parts}, relation first second → S.built first constructor parts →
    ∃ parts', S.built second constructor parts' ∧ List.Forall₂ relation parts parts'
  builtBack : ∀ {first second constructor parts'}, relation first second → S.built second constructor parts' →
    ∃ parts, S.built first constructor parts ∧ List.Forall₂ relation parts parts'
  splitForth : ∀ {first second kind left right}, relation first second → S.split first kind left right →
    ∃ left' right', S.split second kind left' right' ∧ relation left left' ∧ relation right right'
  splitBack : ∀ {first second kind left' right'}, relation first second → S.split second kind left' right' →
    ∃ left right, S.split first kind left right ∧ relation left left' ∧ relation right right'
  singleForth : ∀ {first second kind member}, relation first second → S.single first kind member →
    ∃ member', S.single second kind member' ∧ relation member member'
  singleBack : ∀ {first second kind member'}, relation first second → S.single second kind member' →
    ∃ member, S.single first kind member ∧ relation member member'
  bodyForth : ∀ {first second inner}, relation first second → S.body first inner →
    ∃ inner', S.body second inner' ∧ relation inner inner'
  bodyBack : ∀ {first second inner'}, relation first second → S.body second inner' →
    ∃ inner, S.body first inner ∧ relation inner inner'
  multiBodyForth : ∀ {first second arity inner}, relation first second → S.multiBody first arity inner →
    ∃ inner', S.multiBody second arity inner' ∧ relation inner inner'
  multiBodyBack : ∀ {first second arity inner'}, relation first second → S.multiBody second arity inner' →
    ∃ inner, S.multiBody first arity inner ∧ relation inner inner'
  empty : ∀ {first second kind}, relation first second → (S.empty first kind ↔ S.empty second kind)
  bound : ∀ {first second index}, relation first second → (S.bound first index ↔ S.bound second index)
  typed : ∀ {first second type}, relation first second → (S.typed first type ↔ S.typed second type)
  named : ∀ {first second term}, relation first second → (S.named first term ↔ S.named second term)
  inRelation : ∀ {first second name}, relation first second → (S.inRelation first name ↔ S.inRelation second name)

/-- **Structural bisimilarity**: related by some structural bisimulation. -/
def StructurallyBisimilar (first second : Carrier) : Prop :=
  ∃ relation, S.StructuralBisimulation relation ∧ relation first second

theorem forall₂_lift {first second : Carrier → Carrier → Prop} (lift : ∀ {a b}, first a b → second a b) :
    ∀ {left right : List Carrier}, List.Forall₂ first left right → List.Forall₂ second left right
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (lift head) (forall₂_lift lift tail)

theorem forall₂_compose {first second : Carrier → Carrier → Prop} :
    ∀ {left middle right : List Carrier}, List.Forall₂ first left middle → List.Forall₂ second middle right →
      List.Forall₂ (fun a c => ∃ b, first a b ∧ second b c) left right
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons head tail, .cons head' tail' => .cons ⟨_, head, head'⟩ (forall₂_compose tail tail')

theorem structuralBisimulation_structurallyBisimilar : S.StructuralBisimulation S.StructurallyBisimilar := by
  have pack : ∀ {relation} {a b : Carrier}, S.StructuralBisimulation relation → relation a b →
      S.StructurallyBisimilar a b := fun bisimulation related => ⟨_, bisimulation, related⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro first second label next ⟨relation, bisimulation, related⟩ step
    obtain ⟨next', step', relatedNext⟩ := bisimulation.steps.forth related step
    exact ⟨next', step', pack bisimulation relatedNext⟩
  · rintro first second label next' ⟨relation, bisimulation, related⟩ step
    obtain ⟨next, step', relatedNext⟩ := bisimulation.steps.back related step
    exact ⟨next, step', pack bisimulation relatedNext⟩
  · rintro first second label previous ⟨relation, bisimulation, related⟩ step
    obtain ⟨previous', step', relatedPrevious⟩ := bisimulation.steps.pastForth related step
    exact ⟨previous', step', pack bisimulation relatedPrevious⟩
  · rintro first second label previous' ⟨relation, bisimulation, related⟩ step
    obtain ⟨previous, step', relatedPrevious⟩ := bisimulation.steps.pastBack related step
    exact ⟨previous, step', pack bisimulation relatedPrevious⟩
  · rintro first second constructor parts ⟨relation, bisimulation, related⟩ isBuilt
    obtain ⟨parts', isBuilt', relatedParts⟩ := bisimulation.builtForth related isBuilt
    exact ⟨parts', isBuilt', forall₂_lift (pack bisimulation) relatedParts⟩
  · rintro first second constructor parts' ⟨relation, bisimulation, related⟩ isBuilt
    obtain ⟨parts, isBuilt', relatedParts⟩ := bisimulation.builtBack related isBuilt
    exact ⟨parts, isBuilt', forall₂_lift (pack bisimulation) relatedParts⟩
  · rintro first second kind left right ⟨relation, bisimulation, related⟩ isSplit
    obtain ⟨left', right', isSplit', relatedLeft, relatedRight⟩ := bisimulation.splitForth related isSplit
    exact ⟨left', right', isSplit', pack bisimulation relatedLeft, pack bisimulation relatedRight⟩
  · rintro first second kind left' right' ⟨relation, bisimulation, related⟩ isSplit
    obtain ⟨left, right, isSplit', relatedLeft, relatedRight⟩ := bisimulation.splitBack related isSplit
    exact ⟨left, right, isSplit', pack bisimulation relatedLeft, pack bisimulation relatedRight⟩
  · rintro first second kind member ⟨relation, bisimulation, related⟩ isSingle
    obtain ⟨member', isSingle', relatedMember⟩ := bisimulation.singleForth related isSingle
    exact ⟨member', isSingle', pack bisimulation relatedMember⟩
  · rintro first second kind member' ⟨relation, bisimulation, related⟩ isSingle
    obtain ⟨member, isSingle', relatedMember⟩ := bisimulation.singleBack related isSingle
    exact ⟨member, isSingle', pack bisimulation relatedMember⟩
  · rintro first second inner ⟨relation, bisimulation, related⟩ isBody
    obtain ⟨inner', isBody', relatedInner⟩ := bisimulation.bodyForth related isBody
    exact ⟨inner', isBody', pack bisimulation relatedInner⟩
  · rintro first second inner' ⟨relation, bisimulation, related⟩ isBody
    obtain ⟨inner, isBody', relatedInner⟩ := bisimulation.bodyBack related isBody
    exact ⟨inner, isBody', pack bisimulation relatedInner⟩
  · rintro first second arity inner ⟨relation, bisimulation, related⟩ isBody
    obtain ⟨inner', isBody', relatedInner⟩ := bisimulation.multiBodyForth related isBody
    exact ⟨inner', isBody', pack bisimulation relatedInner⟩
  · rintro first second arity inner' ⟨relation, bisimulation, related⟩ isBody
    obtain ⟨inner, isBody', relatedInner⟩ := bisimulation.multiBodyBack related isBody
    exact ⟨inner, isBody', pack bisimulation relatedInner⟩
  · rintro first second kind ⟨relation, bisimulation, related⟩
    exact bisimulation.empty related
  · rintro first second index ⟨relation, bisimulation, related⟩
    exact bisimulation.bound related
  · rintro first second type ⟨relation, bisimulation, related⟩
    exact bisimulation.typed related
  · rintro first second term ⟨relation, bisimulation, related⟩
    exact bisimulation.named related
  · rintro first second name ⟨relation, bisimulation, related⟩
    exact bisimulation.inRelation related

/-- **Structural bisimilarity is an equivalence.** -/
theorem structurallyBisimilar_equivalence : Equivalence S.StructurallyBisimilar where
  refl element := by
    refine ⟨Eq, ⟨⟨fun related step => ⟨_, related ▸ step, rfl⟩, fun related step => ⟨_, related ▸ step, rfl⟩,
      fun related step => ⟨_, related ▸ step, rfl⟩, fun related step => ⟨_, related ▸ step, rfl⟩⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩ <;>
    first
    | (intro first second _ parts related isBuilt; subst related
       exact ⟨parts, isBuilt, List.forall₂_same.mpr fun _ _ => rfl⟩)
    | (intro first second _ _ _ related isSplit; subst related; exact ⟨_, _, isSplit, rfl, rfl⟩)
    | (intro first second _ _ related isSingle; subst related; exact ⟨_, isSingle, rfl⟩)
    | (intro first second _ related isBody; subst related; exact ⟨_, isBody, rfl⟩)
    | (intro first second _ related; subst related; exact Iff.rfl)
  symm := by
    rintro first second ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => relation right left, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩, related⟩
    · intro first second label next related step
      exact bisimulation.steps.back related step
    · intro first second label next' related step
      exact bisimulation.steps.forth related step
    · intro first second label previous related step
      exact bisimulation.steps.pastBack related step
    · intro first second label previous' related step
      exact bisimulation.steps.pastForth related step
    · intro first second constructor parts related isBuilt
      obtain ⟨parts', isBuilt', relatedParts⟩ := bisimulation.builtBack related isBuilt
      exact ⟨parts', isBuilt', relatedParts.flip⟩
    · intro first second constructor parts' related isBuilt
      obtain ⟨parts, isBuilt', relatedParts⟩ := bisimulation.builtForth related isBuilt
      exact ⟨parts, isBuilt', relatedParts.flip⟩
    · intro first second kind left right related isSplit
      obtain ⟨left', right', isSplit', relatedLeft, relatedRight⟩ := bisimulation.splitBack related isSplit
      exact ⟨left', right', isSplit', relatedLeft, relatedRight⟩
    · intro first second kind left' right' related isSplit
      obtain ⟨left, right, isSplit', relatedLeft, relatedRight⟩ := bisimulation.splitForth related isSplit
      exact ⟨left, right, isSplit', relatedLeft, relatedRight⟩
    · intro first second kind member related isSingle
      exact bisimulation.singleBack related isSingle
    · intro first second kind member' related isSingle
      exact bisimulation.singleForth related isSingle
    · intro first second inner related isBody
      exact bisimulation.bodyBack related isBody
    · intro first second inner' related isBody
      exact bisimulation.bodyForth related isBody
    · intro first second arity inner related isBody
      exact bisimulation.multiBodyBack related isBody
    · intro first second arity inner' related isBody
      exact bisimulation.multiBodyForth related isBody
    · intro first second kind related
      exact (bisimulation.empty related).symm
    · intro first second index related
      exact (bisimulation.bound related).symm
    · intro first second type related
      exact (bisimulation.typed related).symm
    · intro first second term related
      exact (bisimulation.named related).symm
    · intro first second name related
      exact (bisimulation.inRelation related).symm
  trans := by
    rintro first second third ⟨relation, bisimulation, related⟩ ⟨relation', bisimulation', related'⟩
    refine ⟨fun left right => ∃ middle, relation left middle ∧ relation' middle right, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, second, related, related'⟩
    · rintro first third label next ⟨middle, left, right⟩ step
      obtain ⟨next', step', relatedNext⟩ := bisimulation.steps.forth left step
      obtain ⟨next'', step'', relatedNext'⟩ := bisimulation'.steps.forth right step'
      exact ⟨next'', step'', next', relatedNext, relatedNext'⟩
    · rintro first third label next'' ⟨middle, left, right⟩ step
      obtain ⟨next', step', relatedNext'⟩ := bisimulation'.steps.back right step
      obtain ⟨next, stepFirst, relatedNext⟩ := bisimulation.steps.back left step'
      exact ⟨next, stepFirst, next', relatedNext, relatedNext'⟩
    · rintro first third label previous ⟨middle, left, right⟩ step
      obtain ⟨previous', step', relatedPrevious⟩ := bisimulation.steps.pastForth left step
      obtain ⟨previous'', step'', relatedPrevious'⟩ := bisimulation'.steps.pastForth right step'
      exact ⟨previous'', step'', previous', relatedPrevious, relatedPrevious'⟩
    · rintro first third label previous'' ⟨middle, left, right⟩ step
      obtain ⟨previous', step', relatedPrevious'⟩ := bisimulation'.steps.pastBack right step
      obtain ⟨previous, stepFirst, relatedPrevious⟩ := bisimulation.steps.pastBack left step'
      exact ⟨previous, stepFirst, previous', relatedPrevious, relatedPrevious'⟩
    · rintro first third constructor parts ⟨middle, left, right⟩ isBuilt
      obtain ⟨parts', isBuilt', relatedParts⟩ := bisimulation.builtForth left isBuilt
      obtain ⟨parts'', isBuilt'', relatedParts'⟩ := bisimulation'.builtForth right isBuilt'
      exact ⟨parts'', isBuilt'', forall₂_compose relatedParts relatedParts'⟩
    · rintro first third constructor parts'' ⟨middle, left, right⟩ isBuilt
      obtain ⟨parts', isBuilt', relatedParts'⟩ := bisimulation'.builtBack right isBuilt
      obtain ⟨parts, isBuilt'', relatedParts⟩ := bisimulation.builtBack left isBuilt'
      exact ⟨parts, isBuilt'', forall₂_compose relatedParts relatedParts'⟩
    · rintro first third kind leftPart rightPart ⟨middle, left, right⟩ isSplit
      obtain ⟨left', right', isSplit', relatedLeft, relatedRight⟩ := bisimulation.splitForth left isSplit
      obtain ⟨left'', right'', isSplit'', relatedLeft', relatedRight'⟩ := bisimulation'.splitForth right isSplit'
      exact ⟨left'', right'', isSplit'', ⟨left', relatedLeft, relatedLeft'⟩, ⟨right', relatedRight, relatedRight'⟩⟩
    · rintro first third kind leftPart rightPart ⟨middle, left, right⟩ isSplit
      obtain ⟨left', right', isSplit', relatedLeft', relatedRight'⟩ := bisimulation'.splitBack right isSplit
      obtain ⟨left'', right'', isSplit'', relatedLeft, relatedRight⟩ := bisimulation.splitBack left isSplit'
      exact ⟨left'', right'', isSplit'', ⟨left', relatedLeft, relatedLeft'⟩, ⟨right', relatedRight, relatedRight'⟩⟩
    · rintro first third kind member ⟨middle, left, right⟩ isSingle
      obtain ⟨member', isSingle', relatedMember⟩ := bisimulation.singleForth left isSingle
      obtain ⟨member'', isSingle'', relatedMember'⟩ := bisimulation'.singleForth right isSingle'
      exact ⟨member'', isSingle'', member', relatedMember, relatedMember'⟩
    · rintro first third kind member'' ⟨middle, left, right⟩ isSingle
      obtain ⟨member', isSingle', relatedMember'⟩ := bisimulation'.singleBack right isSingle
      obtain ⟨member, isSingle'', relatedMember⟩ := bisimulation.singleBack left isSingle'
      exact ⟨member, isSingle'', member', relatedMember, relatedMember'⟩
    · rintro first third inner ⟨middle, left, right⟩ isBody
      obtain ⟨inner', isBody', relatedInner⟩ := bisimulation.bodyForth left isBody
      obtain ⟨inner'', isBody'', relatedInner'⟩ := bisimulation'.bodyForth right isBody'
      exact ⟨inner'', isBody'', inner', relatedInner, relatedInner'⟩
    · rintro first third inner'' ⟨middle, left, right⟩ isBody
      obtain ⟨inner', isBody', relatedInner'⟩ := bisimulation'.bodyBack right isBody
      obtain ⟨inner, isBody'', relatedInner⟩ := bisimulation.bodyBack left isBody'
      exact ⟨inner, isBody'', inner', relatedInner, relatedInner'⟩
    · rintro first third arity inner ⟨middle, left, right⟩ isBody
      obtain ⟨inner', isBody', relatedInner⟩ := bisimulation.multiBodyForth left isBody
      obtain ⟨inner'', isBody'', relatedInner'⟩ := bisimulation'.multiBodyForth right isBody'
      exact ⟨inner'', isBody'', inner', relatedInner, relatedInner'⟩
    · rintro first third arity inner'' ⟨middle, left, right⟩ isBody
      obtain ⟨inner', isBody', relatedInner'⟩ := bisimulation'.multiBodyBack right isBody
      obtain ⟨inner, isBody'', relatedInner⟩ := bisimulation.multiBodyBack left isBody'
      exact ⟨inner, isBody'', inner', relatedInner, relatedInner'⟩
    · rintro first third kind ⟨middle, left, right⟩
      exact (bisimulation.empty left).trans (bisimulation'.empty right)
    · rintro first third index ⟨middle, left, right⟩
      exact (bisimulation.bound left).trans (bisimulation'.bound right)
    · rintro first third type ⟨middle, left, right⟩
      exact (bisimulation.typed left).trans (bisimulation'.typed right)
    · rintro first third term ⟨middle, left, right⟩
      exact (bisimulation.named left).trans (bisimulation'.named right)
    · rintro first third name ⟨middle, left, right⟩
      exact (bisimulation.inRelation left).trans (bisimulation'.inRelation right)

/-! ## Structurally bisimilar elements satisfy the same first-order formulas -/

variable {S}

mutual
/-- **First-order formulas hold alike at structurally bisimilar elements**, in environments closed under
structural bisimilarity. -/
theorem sat_of_structurallyBisimilar : ∀ {n : ℕ} (formula : Formula n), formula.firstOrder = true →
    ∀ {env : Env Carrier n}, env.Respects S.StructurallyBisimilar → ∀ {first second : Carrier},
      S.StructurallyBisimilar first second → S.sat env formula first → S.sat env formula second
  | _, .top, _, _, _, _, _, _, _ => trivial
  | _, .bot, _, _, _, _, _, _, holds => holds
  | _, .and left right, firstOrder, _, respects, _, _, related, holds => by
    simp only [Formula.firstOrder, Bool.and_eq_true] at firstOrder
    exact ⟨sat_of_structurallyBisimilar left firstOrder.1 respects related holds.1,
      sat_of_structurallyBisimilar right firstOrder.2 respects related holds.2⟩
  | _, .or left right, firstOrder, _, respects, _, _, related, holds => by
    simp only [Formula.firstOrder, Bool.and_eq_true] at firstOrder
    exact holds.imp (sat_of_structurallyBisimilar left firstOrder.1 respects related)
      (sat_of_structurallyBisimilar right firstOrder.2 respects related)
  | _, .var index, _, _, respects, first, second, related, holds => respects index first second related holds
  | _, .mu inner, firstOrder, env, respects, first, second, related, holds => by
    intro closed closedHolds
    let interior : Set Carrier := {element | ∀ other, S.StructurallyBisimilar element other → other ∈ closed}
    have interiorRespects : ∀ a b, S.StructurallyBisimilar a b → a ∈ interior → b ∈ interior :=
      fun a b ab member other bOther => member other (S.structurallyBisimilar_equivalence.trans ab bOther)
    have inside : interior ⊆ closed :=
      fun element member => member element (S.structurallyBisimilar_equivalence.refl element)
    have interiorHolds := holds interior fun element elementHolds other related' =>
      closedHolds other (S.sat_mono inner (env.extend_sub inside) other
        (sat_of_structurallyBisimilar inner firstOrder (respects.extend interiorRespects) related' elementHolds))
    exact interiorHolds second related
  | _, .nu inner, firstOrder, env, respects, first, second, related, holds => by
    obtain ⟨invariant, member, preserved⟩ := holds
    let closure : Set Carrier := {element | ∃ origin ∈ invariant, S.StructurallyBisimilar origin element}
    have closureRespects : ∀ a b, S.StructurallyBisimilar a b → a ∈ closure → b ∈ closure := by
      rintro a b ab ⟨origin, originMember, originA⟩
      exact ⟨origin, originMember, S.structurallyBisimilar_equivalence.trans originA ab⟩
    have contains : invariant ⊆ closure :=
      fun element member => ⟨element, member, S.structurallyBisimilar_equivalence.refl element⟩
    refine ⟨closure, ⟨first, member, related⟩, ?_⟩
    rintro element ⟨origin, originMember, originRelated⟩
    exact sat_of_structurallyBisimilar inner firstOrder (respects.extend closureRespects) originRelated
      (S.sat_mono inner (env.extend_sub contains) origin (preserved origin originMember))
  | _, .possibly _ formula, firstOrder, _, respects, _, _, related, holds => by
    obtain ⟨next, step, nextHolds⟩ := holds
    obtain ⟨next', step', relatedNext⟩ := S.structuralBisimulation_structurallyBisimilar.steps.forth related step
    exact ⟨next', step', sat_of_structurallyBisimilar formula firstOrder respects relatedNext nextHolds⟩
  | _, .necessarily _ formula, firstOrder, _, respects, _, _, related, holds => fun next' step' => by
    obtain ⟨next, step, relatedNext⟩ := S.structuralBisimulation_structurallyBisimilar.steps.back related step'
    exact sat_of_structurallyBisimilar formula firstOrder respects relatedNext (holds next step)
  | _, .sometimeBefore _ formula, firstOrder, _, respects, _, _, related, holds => by
    obtain ⟨previous, step, previousHolds⟩ := holds
    obtain ⟨previous', step', relatedPrevious⟩ :=
      S.structuralBisimulation_structurallyBisimilar.steps.pastForth related step
    exact ⟨previous', step', sat_of_structurallyBisimilar formula firstOrder respects relatedPrevious previousHolds⟩
  | _, .alwaysBefore _ formula, firstOrder, _, respects, _, _, related, holds => fun previous' step' => by
    obtain ⟨previous, step, relatedPrevious⟩ :=
      S.structuralBisimulation_structurallyBisimilar.steps.pastBack related step'
    exact sat_of_structurallyBisimilar formula firstOrder respects relatedPrevious (holds previous step)
  | _, .built _ arguments, firstOrder, _, respects, _, _, related, holds => by
    obtain ⟨parts, isBuilt, all⟩ := holds
    obtain ⟨parts', isBuilt', relatedParts⟩ := S.structuralBisimulation_structurallyBisimilar.builtForth related isBuilt
    exact ⟨parts', isBuilt', satAll_of_structurallyBisimilar arguments firstOrder respects relatedParts all⟩
  | _, .everyBuilt _ arguments, firstOrder, _, respects, _, _, related, holds => fun parts' isBuilt' => by
    obtain ⟨parts, isBuilt, relatedParts⟩ := S.structuralBisimulation_structurallyBisimilar.builtBack related isBuilt'
    exact satSome_of_structurallyBisimilar arguments firstOrder respects relatedParts (holds parts isBuilt)
  | _, .split _ left right, firstOrder, _, respects, _, _, related, holds => by
    simp only [Formula.firstOrder, Bool.and_eq_true] at firstOrder
    obtain ⟨leftPart, rightPart, isSplit, leftHolds, rightHolds⟩ := holds
    obtain ⟨leftPart', rightPart', isSplit', relatedLeft, relatedRight⟩ :=
      S.structuralBisimulation_structurallyBisimilar.splitForth related isSplit
    exact ⟨leftPart', rightPart', isSplit', sat_of_structurallyBisimilar left firstOrder.1 respects relatedLeft leftHolds,
      sat_of_structurallyBisimilar right firstOrder.2 respects relatedRight rightHolds⟩
  | _, .everySplit _ left right, firstOrder, _, respects, _, _, related, holds => fun leftPart' rightPart' isSplit' => by
    simp only [Formula.firstOrder, Bool.and_eq_true] at firstOrder
    obtain ⟨leftPart, rightPart, isSplit, relatedLeft, relatedRight⟩ :=
      S.structuralBisimulation_structurallyBisimilar.splitBack related isSplit'
    exact (holds leftPart rightPart isSplit).imp
      (sat_of_structurallyBisimilar left firstOrder.1 respects relatedLeft)
      (sat_of_structurallyBisimilar right firstOrder.2 respects relatedRight)
  | _, .empty _, _, _, _, _, _, related, holds =>
    (S.structuralBisimulation_structurallyBisimilar.empty related).mp holds
  | _, .nonEmpty _, _, _, _, _, _, related, holds => fun isEmpty =>
    holds ((S.structuralBisimulation_structurallyBisimilar.empty related).mpr isEmpty)
  | _, .single _ formula, firstOrder, _, respects, _, _, related, holds => by
    obtain ⟨member, isSingle, memberHolds⟩ := holds
    obtain ⟨member', isSingle', relatedMember⟩ := S.structuralBisimulation_structurallyBisimilar.singleForth related isSingle
    exact ⟨member', isSingle', sat_of_structurallyBisimilar formula firstOrder respects relatedMember memberHolds⟩
  | _, .everySingle _ formula, firstOrder, _, respects, _, _, related, holds => fun member' isSingle' => by
    obtain ⟨member, isSingle, relatedMember⟩ := S.structuralBisimulation_structurallyBisimilar.singleBack related isSingle'
    exact sat_of_structurallyBisimilar formula firstOrder respects relatedMember (holds member isSingle)
  | _, .body formula, firstOrder, _, respects, _, _, related, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    obtain ⟨inner', isBody', relatedInner⟩ := S.structuralBisimulation_structurallyBisimilar.bodyForth related isBody
    exact ⟨inner', isBody', sat_of_structurallyBisimilar formula firstOrder respects relatedInner innerHolds⟩
  | _, .everyBody formula, firstOrder, _, respects, _, _, related, holds => fun inner' isBody' => by
    obtain ⟨inner, isBody, relatedInner⟩ := S.structuralBisimulation_structurallyBisimilar.bodyBack related isBody'
    exact sat_of_structurallyBisimilar formula firstOrder respects relatedInner (holds inner isBody)
  | _, .multiBody _ formula, firstOrder, _, respects, _, _, related, holds => by
    obtain ⟨inner, isBody, innerHolds⟩ := holds
    obtain ⟨inner', isBody', relatedInner⟩ :=
      S.structuralBisimulation_structurallyBisimilar.multiBodyForth related isBody
    exact ⟨inner', isBody', sat_of_structurallyBisimilar formula firstOrder respects relatedInner innerHolds⟩
  | _, .everyMultiBody _ formula, firstOrder, _, respects, _, _, related, holds => fun inner' isBody' => by
    obtain ⟨inner, isBody, relatedInner⟩ :=
      S.structuralBisimulation_structurallyBisimilar.multiBodyBack related isBody'
    exact sat_of_structurallyBisimilar formula firstOrder respects relatedInner (holds inner isBody)
  | _, .bound _, _, _, _, _, _, related, holds =>
    (S.structuralBisimulation_structurallyBisimilar.bound related).mp holds
  | _, .notBound _, _, _, _, _, _, related, holds => fun isBound =>
    holds ((S.structuralBisimulation_structurallyBisimilar.bound related).mpr isBound)
  | _, .typed _, _, _, _, _, _, related, holds =>
    (S.structuralBisimulation_structurallyBisimilar.typed related).mp holds
  | _, .untyped _, _, _, _, _, _, related, holds => fun isTyped =>
    holds ((S.structuralBisimulation_structurallyBisimilar.typed related).mpr isTyped)
  | _, .is _, _, _, _, _, _, related, holds =>
    (S.structuralBisimulation_structurallyBisimilar.named related).mp holds
  | _, .isNot _, _, _, _, _, _, related, holds => fun isNamed =>
    holds ((S.structuralBisimulation_structurallyBisimilar.named related).mpr isNamed)
  | _, .inRelation _, _, _, _, _, _, related, holds =>
    (S.structuralBisimulation_structurallyBisimilar.inRelation related).mp holds
  | _, .notInRelation _, _, _, _, _, _, related, holds => fun isIn =>
    holds ((S.structuralBisimulation_structurallyBisimilar.inRelation related).mpr isIn)
  | _, .mapsAll _ _, firstOrder, _, _, _, _, _, _ | _, .mapsSome _ _, firstOrder, _, _, _, _, _, _
  | _, .someOf _ _, firstOrder, _, _, _, _, _, _ | _, .everyOf _ _, firstOrder, _, _, _, _, _, _ => by
    simp [Formula.firstOrder] at firstOrder

theorem satAll_of_structurallyBisimilar : ∀ {n : ℕ} (formulas : Formulas n), Formula.firstOrderList formulas = true →
    ∀ {env : Env Carrier n}, env.Respects S.StructurallyBisimilar → ∀ {parts parts' : List Carrier},
      List.Forall₂ S.StructurallyBisimilar parts parts' → S.satAll env formulas parts → S.satAll env formulas parts'
  | _, .nil, _, _, _, _, _, .nil, _ => trivial
  | _, .cons formula formulas, firstOrder, _, respects, _, _, .cons head tail, holds => by
    simp only [Formula.firstOrderList, Bool.and_eq_true] at firstOrder
    exact ⟨sat_of_structurallyBisimilar formula firstOrder.1 respects head holds.1,
      satAll_of_structurallyBisimilar formulas firstOrder.2 respects tail holds.2⟩
  | _, .nil, _, _, _, _, _, .cons _ _, holds => holds.elim
  | _, .cons _ _, _, _, _, _, _, .nil, holds => holds.elim

theorem satSome_of_structurallyBisimilar : ∀ {n : ℕ} (formulas : Formulas n), Formula.firstOrderList formulas = true →
    ∀ {env : Env Carrier n}, env.Respects S.StructurallyBisimilar → ∀ {parts parts' : List Carrier},
      List.Forall₂ S.StructurallyBisimilar parts parts' → S.satSome env formulas parts → S.satSome env formulas parts'
  | _, .nil, _, _, _, _, _, .nil, holds => holds
  | _, .cons formula formulas, firstOrder, _, respects, _, _, .cons head tail, holds => by
    simp only [Formula.firstOrderList, Bool.and_eq_true] at firstOrder
    exact holds.imp (sat_of_structurallyBisimilar formula firstOrder.1 respects head)
      (satSome_of_structurallyBisimilar formulas firstOrder.2 respects tail)
  | _, .nil, _, _, _, _, _, .cons _ _, _ => trivial
  | _, .cons _ _, _, _, _, _, _, .nil, _ => trivial
end

/-! ## Agreement on first-order formulas is structural bisimilarity, for finitely branching structures -/

variable (S) in
/-- **Finitely many ways to read each relation**: successors and predecessors under each label,
decompositions of each length, splits, members and bodies. -/
structure FullyImageFinite : Prop where
  steps : S.ImageFinite
  decompositions : ∀ element constructor length, ∃ list : List (List Carrier),
    ∀ parts, parts.length = length → (S.built element constructor parts ↔ parts ∈ list)
  splits : ∀ element kind, ∃ list : List (Carrier × Carrier),
    ∀ left right, S.split element kind left right ↔ (left, right) ∈ list
  members : ∀ element kind, ∃ list : List Carrier, ∀ member, S.single element kind member ↔ member ∈ list
  bodies : ∀ element, ∃ list : List Carrier, ∀ inner, S.body element inner ↔ inner ∈ list
  multiBodies : ∀ element arity, ∃ list : List Carrier, ∀ inner, S.multiBody element arity inner ↔ inner ∈ list

variable (S) in
/-- **Agreement on every closed first-order formula.** -/
abbrev FirstOrderEquivalent : Carrier → Carrier → Prop := S.AgreeOn fun formula => formula.firstOrder

theorem forall₂_mapIdx {α β : Type*} {relation : α → β → Prop} :
    ∀ (list : List β) (make : ℕ → β → α), (∀ index element, relation (make index element) element) →
      List.Forall₂ relation (list.mapIdx make) list
  | [], _, _ => by simp
  | element :: list, make, holds => by
    rw [List.mapIdx_cons]
    exact .cons (holds 0 element) (forall₂_mapIdx list (fun index => make (index + 1)) fun index => holds (index + 1))

/-- **A split is matched**: otherwise the separators of its halves from each of the second element's
splits tell the two elements apart. -/
theorem split_match (finite : S.FullyImageFinite) {first second left right : Carrier} {kind : CollType}
    (agree : S.FirstOrderEquivalent first second) (isSplit : S.split first kind left right) :
    ∃ left' right', S.split second kind left' right' ∧ S.FirstOrderEquivalent left left' ∧
      S.FirstOrderEquivalent right right' := by
  by_contra none
  push Not at none
  obtain ⟨pairs, listed⟩ := finite.splits second kind
  let leftFormula := Formula.conj (pairs.map fun pair => S.separator firstOrder_closed left pair.1)
  let rightFormula := Formula.conj (pairs.map fun pair => S.separator firstOrder_closed right pair.2)
  have leftFragment : leftFormula.firstOrder = true := firstOrder_closed.conj _ fun formula member => by
    obtain ⟨pair, -, rfl⟩ := List.mem_map.mp member
    exact separator_fragment firstOrder_closed left pair.1
  have rightFragment : rightFormula.firstOrder = true := firstOrder_closed.conj _ fun formula member => by
    obtain ⟨pair, -, rfl⟩ := List.mem_map.mp member
    exact separator_fragment firstOrder_closed right pair.2
  have inFragment : (Formula.split kind leftFormula rightFormula).firstOrder = true := by
    simp only [Formula.firstOrder, leftFragment, rightFragment, Bool.and_self]
  have atFirst : S.sat Env.closed (.split kind leftFormula rightFormula) first := by
    refine ⟨left, right, isSplit, (S.sat_conj _ _ _).mpr fun formula member => ?_,
      (S.sat_conj _ _ _).mpr fun formula member => ?_⟩
    · obtain ⟨pair, -, rfl⟩ := List.mem_map.mp member
      exact separator_holds firstOrder_closed left pair.1
    · obtain ⟨pair, -, rfl⟩ := List.mem_map.mp member
      exact separator_holds firstOrder_closed right pair.2
  obtain ⟨left', right', isSplit', leftHolds, rightHolds⟩ :=
    (agree (.split kind leftFormula rightFormula) inFragment).mp atFirst
  have member := (listed left' right').mp isSplit'
  by_cases leftAgree : S.FirstOrderEquivalent left left'
  · exact separator_fails firstOrder_closed (none left' right' isSplit' leftAgree)
      ((S.sat_conj _ _ _).mp rightHolds _ (List.mem_map.mpr ⟨(left', right'), member, rfl⟩))
  · exact separator_fails firstOrder_closed leftAgree
      ((S.sat_conj _ _ _).mp leftHolds _ (List.mem_map.mpr ⟨(left', right'), member, rfl⟩))

/-- **A decomposition is matched**: otherwise, at each position, the separators of the part there from
the part at that position of each of the second element's decompositions tell the elements apart. -/
theorem built_match (finite : S.FullyImageFinite) {first second : Carrier} {constructor : String}
    {parts : List Carrier} (agree : S.FirstOrderEquivalent first second) (isBuilt : S.built first constructor parts) :
    ∃ parts', S.built second constructor parts' ∧ List.Forall₂ S.FirstOrderEquivalent parts parts' := by
  by_contra none
  push Not at none
  obtain ⟨decompositions, listed⟩ := finite.decompositions second constructor parts.length
  let positions : List (Formula 0) := parts.mapIdx fun index part =>
    Formula.conj (decompositions.map fun other => S.separator firstOrder_closed part (other.getD index part))
  have positionsFragment : ∀ formula ∈ positions, formula.firstOrder = true := by
    intro formula member
    obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
    rw [List.getElem_mapIdx]
    exact firstOrder_closed.conj _ fun separator member => by
      obtain ⟨other, -, rfl⟩ := List.mem_map.mp member
      exact separator_fragment firstOrder_closed _ _
  have inFragment : (Formula.built constructor (Formulas.ofList positions)).firstOrder = true :=
    Formula.firstOrderList_ofList positions positionsFragment
  have atFirst : S.sat Env.closed (.built constructor (Formulas.ofList positions)) first := by
    refine ⟨parts, isBuilt, (S.satAll_ofList _ positions parts).mpr ?_⟩
    exact forall₂_mapIdx parts _ fun index part => (S.sat_conj _ _ _).mpr fun separator member => by
      obtain ⟨other, -, rfl⟩ := List.mem_map.mp member
      exact separator_holds firstOrder_closed _ _
  obtain ⟨parts', isBuilt', allHold⟩ := (agree _ inFragment).mp atFirst
  have holdsPointwise := (S.satAll_ofList _ positions parts').mp allHold
  have lengths : parts'.length = parts.length := by
    rw [← holdsPointwise.length_eq, List.length_mapIdx]
  have member := (listed parts' lengths).mp isBuilt'
  apply none parts' isBuilt'
  rw [List.forall₂_iff_get]
  refine ⟨lengths.symm, fun index first' second' => ?_⟩
  by_contra differ
  rw [List.forall₂_iff_get] at holdsPointwise
  have atPosition := holdsPointwise.2 index (by simpa [positions, List.length_mapIdx] using first') second'
  simp only [List.get_eq_getElem, positions, List.getElem_mapIdx] at atPosition differ
  have separated := (S.sat_conj _ _ _).mp atPosition _ (List.mem_map.mpr ⟨parts', member, rfl⟩)
  rw [← List.getElem_eq_getD (parts[index]) (h := second')] at separated
  exact separator_fails firstOrder_closed differ separated

/-- On a finitely branching structure, agreement on first-order formulas is a structural
bisimulation. -/
theorem structuralBisimulation_firstOrderEquivalent (finite : S.FullyImageFinite) :
    S.StructuralBisimulation S.FirstOrderEquivalent where
  steps := {
    forth := fun {_ _ label _} agree step =>
      match_of_agree firstOrder_closed (relation := fun element next => S.step element label next)
        (fun element => finite.steps.successors element label) (former := .possibly label)
        (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree step
    back := fun {_ _ label _} agree step => by
      obtain ⟨next, step', related⟩ := match_of_agree firstOrder_closed
        (relation := fun element next => S.step element label next)
        (fun element => finite.steps.successors element label) (former := .possibly label)
        (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm step
      exact ⟨next, step', related.symm⟩
    pastForth := fun {_ _ label _} agree step =>
      match_of_agree firstOrder_closed (relation := fun element previous => S.step previous label element)
        (fun element => finite.steps.predecessors element label) (former := .sometimeBefore label)
        (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree step
    pastBack := fun {_ _ label _} agree step => by
      obtain ⟨previous, step', related⟩ := match_of_agree firstOrder_closed
        (relation := fun element previous => S.step previous label element)
        (fun element => finite.steps.predecessors element label) (former := .sometimeBefore label)
        (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm step
      exact ⟨previous, step', related.symm⟩ }
  builtForth := fun agree isBuilt => built_match finite agree isBuilt
  builtBack := fun agree isBuilt => by
    obtain ⟨parts, isBuilt', related⟩ := built_match finite agree.symm isBuilt
    exact ⟨parts, isBuilt', forall₂_lift (fun related => AgreeOn.symm related) related.flip⟩
  splitForth := fun agree isSplit => split_match finite agree isSplit
  splitBack := fun agree isSplit => by
    obtain ⟨left, right, isSplit', relatedLeft, relatedRight⟩ := split_match finite agree.symm isSplit
    exact ⟨left, right, isSplit', relatedLeft.symm, relatedRight.symm⟩
  singleForth := fun {_ _ kind _} agree isSingle =>
    match_of_agree firstOrder_closed (relation := fun element member => S.single element kind member)
      (fun element => finite.members element kind) (former := .single kind) (fun _ inFragment => inFragment)
      (fun _ _ => Iff.rfl) agree isSingle
  singleBack := fun {_ _ kind _} agree isSingle => by
    obtain ⟨member, isSingle', related⟩ := match_of_agree firstOrder_closed
      (relation := fun element member => S.single element kind member) (fun element => finite.members element kind)
      (former := .single kind) (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm isSingle
    exact ⟨member, isSingle', related.symm⟩
  bodyForth := fun agree isBody =>
    match_of_agree firstOrder_closed (relation := S.body) finite.bodies (former := .body)
      (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree isBody
  bodyBack := fun agree isBody => by
    obtain ⟨inner, isBody', related⟩ := match_of_agree firstOrder_closed (relation := S.body) finite.bodies
      (former := .body) (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm isBody
    exact ⟨inner, isBody', related.symm⟩
  multiBodyForth := fun {_ _ arity _} agree isBody =>
    match_of_agree firstOrder_closed (relation := fun element inner => S.multiBody element arity inner)
      (fun element => finite.multiBodies element arity) (former := .multiBody arity) (fun _ inFragment => inFragment)
      (fun _ _ => Iff.rfl) agree isBody
  multiBodyBack := fun {_ _ arity _} agree isBody => by
    obtain ⟨inner, isBody', related⟩ := match_of_agree firstOrder_closed
      (relation := fun element inner => S.multiBody element arity inner)
      (fun element => finite.multiBodies element arity) (former := .multiBody arity)
      (fun _ inFragment => inFragment) (fun _ _ => Iff.rfl) agree.symm isBody
    exact ⟨inner, isBody', related.symm⟩
  empty := fun {_ _ kind} agree => agree (.empty kind) rfl
  bound := fun {_ _ index} agree => agree (.bound index) rfl
  typed := fun {_ _ type} agree => agree (.typed type) rfl
  named := fun {_ _ term} agree => agree (.is term) rfl
  inRelation := fun {_ _ name} agree => agree (.inRelation name) rfl

/-- **First-order formulas induce structural bisimilarity**, on a structure finitely branching in every
relation. -/
theorem firstOrderEquivalent_iff_structurallyBisimilar (finite : S.FullyImageFinite) {first second : Carrier} :
    S.FirstOrderEquivalent first second ↔ S.StructurallyBisimilar first second :=
  ⟨fun agree => ⟨_, structuralBisimulation_firstOrderEquivalent finite, agree⟩,
    fun related formula firstOrder =>
      ⟨sat_of_structurallyBisimilar formula firstOrder (Env.respects_closed _) related,
        sat_of_structurallyBisimilar formula firstOrder (Env.respects_closed _)
          (S.structurallyBisimilar_equivalence.symm related)⟩⟩

end NativeStructure

/-- **A finite structure is finitely branching in every relation.** -/
theorem FiniteStructure.fullyImageFinite {Carrier : Type u} (F : FiniteStructure Carrier) :
    F.native.FullyImageFinite where
  steps := F.imageFinite
  decompositions element constructor length :=
    ⟨(Listed.lists F.elements length).filter (F.built element constructor ·), fun parts sameLength => by
      simp [FiniteStructure.native, Listed.mem_lists F.elements F.complete, sameLength]⟩
  splits element kind :=
    ⟨(F.elements.flatMap fun left => F.elements.map fun right => (left, right)).filter
      fun pair => F.split element kind pair.1 pair.2, fun left right => by
      simp [FiniteStructure.native, F.complete left, F.complete right]⟩
  members element kind := ⟨F.elements.filter (F.single element kind ·), fun member => by
    simp [FiniteStructure.native, F.complete member]⟩
  bodies element := ⟨F.elements.filter (F.body element ·), fun inner => by
    simp [FiniteStructure.native, F.complete inner]⟩
  multiBodies element arity := ⟨F.elements.filter (F.multiBody element arity ·), fun inner => by
    simp [FiniteStructure.native, F.complete inner]⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
