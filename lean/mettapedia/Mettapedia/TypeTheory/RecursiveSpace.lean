import Mettapedia.TypeTheory.IndexedPolynomialRepresentation

/-!
# Algebraic characterization of recursive spaces

The bottom/constructor presentation has natural-number tags, arbitrary payloads
and natural-number-indexed child functions. Constructor separation, injectivity
and full predicate induction determine its polynomial representation. Recursion
with a supplied bottom value exists uniquely; constructor-only recursion does
not determine that value.
The statements are algebraic laws; interpreting the retained HOL Light proofs
in a selected model remains a separate connection.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.RecursiveSpace
open IndexedPolynomial
universe u v w

/-- The polynomial has an absent shape and countably branching constructors. -/
def polynomial (A : Type u) : IndexedPolynomial.{0, 0, u, 0} PUnit (fun _ => PUnit) where
  Shape := fun _ _ => Option (Nat × A)
  Position := fun shape => match shape with
    | none => PEmpty
    | some _ => Nat
  next := fun _ _ => PUnit.unit

abbrev Tree (A : Type u) := Fix (polynomial A) PUnit.unit PUnit.unit

def bottom {A : Type u} : Tree A := .roll none (fun impossible => PEmpty.elim impossible)

def construct {A : Type u} (tag : Nat) (payload : A) (children : Nat → Tree A) : Tree A :=
  .roll (some (tag, payload)) children

def atUnit {A : Type u} {index : PUnit} (tree : Fix (polynomial A) PUnit.unit index) : Tree A := by
  cases index
  exact tree

@[elab_as_elim] theorem induction {A : Type u} (property : Tree A → Prop)
    (at_bottom : property bottom)
    (at_construct : ∀ tag payload children, (∀ n, property (children n)) → property (construct tag payload children))
    (tree : Tree A) : property tree := by
  have all : ∀ index (tree : Fix (polynomial A) PUnit.unit index), property (atUnit tree) :=
    Fix.eliminate (polynomial A) (fun _ index tree => property (atUnit tree)) (by
      intro base index shape children hypotheses
      cases base
      cases index
      cases shape with
      | none =>
        have empty : children = (fun impossible => PEmpty.elim impossible) := funext fun impossible => PEmpty.elim impossible
        cases empty
        exact at_bottom
      | some point => exact at_construct point.1 point.2 children hypotheses) PUnit.unit
  exact all PUnit.unit tree

/-- Separation, injectivity and full predicate induction characterize the
recursive-space algebra. Restricted Henkin predicates need a separate argument. -/
structure Model (A : Type u) (R : Type v) where
  bottom : R
  construct : Nat → A → (Nat → R) → R
  construct_ne_bottom : ∀ tag payload children, construct tag payload children ≠ bottom
  construct_injective : ∀ tag payload children tag' payload' children',
    construct tag payload children = construct tag' payload' children' ↔
      tag = tag' ∧ payload = payload' ∧ children = children'
  induction : ∀ property : R → Prop,
    property bottom →
    (∀ tag payload children, (∀ n, property (children n)) → property (construct tag payload children)) →
    ∀ value, property value

namespace Model
variable {A : Type u} {B : Type v} {R : Type w}

def changePayload (M : Model B R) (equivalence : A ≃ B) : Model A R where
  bottom := M.bottom
  construct := fun tag payload children => M.construct tag (equivalence payload) children
  construct_ne_bottom := fun tag payload children => M.construct_ne_bottom tag (equivalence payload) children
  construct_injective := by
    intro tag payload children tag' payload' children'
    constructor
    · intro same
      obtain ⟨tags, payloads, recursive⟩ := (M.construct_injective _ _ _ _ _ _).mp same
      exact ⟨tags, equivalence.injective payloads, recursive⟩
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  induction := by
    intro property at_bottom at_construct value
    apply M.induction property at_bottom ?_ value
    intro tag payload children hypotheses
    have complete := at_construct tag (equivalence.symm payload) children hypotheses
    simpa only [Equiv.apply_symm_apply] using complete

end Model

namespace Model
variable {A : Type u} {R : Type v} {S : Type w}

/-- Transport all recursive-space operations and laws along a carrier
equivalence. Children are transported pointwise in both directions. -/
def changeCarrier (M : Model A R) (equivalence : S ≃ R) : Model A S where
  bottom := equivalence.symm M.bottom
  construct := fun tag payload children =>
    equivalence.symm (M.construct tag payload (fun n => equivalence (children n)))
  construct_ne_bottom := by
    intro tag payload children same
    exact M.construct_ne_bottom _ _ _ (equivalence.symm.injective same)
  construct_injective := by
    intro tag payload children tag' payload' children'
    constructor
    · intro same
      obtain ⟨tags,payloads,recursive⟩ := (M.construct_injective _ _ _ _ _ _).mp
        (equivalence.symm.injective same)
      exact ⟨tags,payloads,funext fun n => equivalence.injective (congrFun recursive n)⟩
    · rintro ⟨rfl,rfl,rfl⟩
      rfl
  induction := by
    intro property atBottom atConstructor value
    have all : ∀ point, property (equivalence.symm point) := by
      apply M.induction (fun point => property (equivalence.symm point)) atBottom
      intro tag payload children hypotheses
      have result := atConstructor tag payload (fun n => equivalence.symm (children n)) hypotheses
      simpa only [Equiv.apply_symm_apply] using result
    simpa only [Equiv.symm_apply_apply] using all (equivalence value)

@[simp] theorem changeCarrier_bottom (M : Model A R) (equivalence : S ≃ R) :
    equivalence (M.changeCarrier equivalence).bottom = M.bottom :=
  equivalence.apply_symm_apply _

@[simp] theorem changeCarrier_construct (M : Model A R) (equivalence : S ≃ R)
    (tag : Nat) (payload : A) (children : Nat → S) :
    equivalence ((M.changeCarrier equivalence).construct tag payload children) =
      M.construct tag payload (fun n => equivalence (children n)) :=
  equivalence.apply_symm_apply _

end Model

variable {A : Type u} {R : Type v}

noncomputable def fold (M : Model A R) : Tree A → R :=
  fun tree => Fix.eliminate (polynomial A) (fun _ _ _ => R)
    (fun _ _ shape _ values => match shape with
      | none => M.bottom
      | some point => M.construct point.1 point.2 values) PUnit.unit PUnit.unit tree

@[simp] theorem fold_bottom (M : Model A R) : fold M bottom = M.bottom := rfl

@[simp] theorem fold_construct (M : Model A R) (tag : Nat) (payload : A) (children : Nat → Tree A) :
    fold M (construct tag payload children) = M.construct tag payload (fun n => fold M (children n)) := rfl

theorem fold_surjective (M : Model A R) : Function.Surjective (fold M) := by
  apply M.induction (fun value => ∃ tree, fold M tree = value)
  · exact ⟨bottom, rfl⟩
  · intro tag payload children hypotheses
    let trees := fun n => Classical.choose (hypotheses n)
    have same : ∀ n, fold M (trees n) = children n := fun n => Classical.choose_spec (hypotheses n)
    exact ⟨construct tag payload trees, by rw [fold_construct, funext same]⟩

theorem layer {A : Type u} (tree : Tree A) :
    ∃ (shape : Option (Nat × A)) (children : (polynomial A).Position shape → Tree A),
      tree = Fix.roll shape children :=
  ⟨(Fix.out (polynomial A) tree).1, (Fix.out (polynomial A) tree).2,
    (Fix.rollExtension_out (polynomial A) tree).symm⟩

theorem fold_injective (M : Model A R) : Function.Injective (fold M) := by
  intro first
  apply induction (fun first => ∀ second, fold M first = fold M second → first = second) ?_ ?_ first
  · intro second same
    obtain ⟨shape, children, rfl⟩ := layer second
    cases shape with
    | none =>
      unfold bottom
      apply congrArg (Fix.roll (polynomial := polynomial A) none)
      funext impossible
      exact PEmpty.elim impossible
    | some point => exact False.elim (M.construct_ne_bottom point.1 point.2 _ same.symm)
  · intro tag payload children hypotheses second same
    obtain ⟨shape', children', rfl⟩ := layer second
    cases shape' with
    | none => exact False.elim (M.construct_ne_bottom tag payload _ same)
    | some point' =>
      obtain ⟨tags, payloads, childrenEq⟩ := (M.construct_injective tag payload _ point'.1 point'.2 _).mp same
      rcases point' with ⟨tag', payload'⟩
      dsimp only at tags payloads
      cases tags
      cases payloads
      apply congrArg (construct tag payload)
      funext n
      exact hypotheses n (children' n) (congrFun childrenEq n)

noncomputable def equivalence (M : Model A R) : Tree A ≃ R :=
  Equiv.ofBijective (fold M) ⟨fold_injective M, fold_surjective M⟩

@[simp] theorem inverse_bottom (M : Model A R) :
    (equivalence M).symm M.bottom = bottom := by
  apply (equivalence M).injective
  exact (equivalence M).apply_symm_apply _

@[simp] theorem inverse_construct (M : Model A R) (tag : Nat) (payload : A) (children : Nat → R) :
    (equivalence M).symm (M.construct tag payload children) =
      construct tag payload (fun n => (equivalence M).symm (children n)) := by
  apply (equivalence M).injective
  change fold M ((equivalence M).symm (M.construct tag payload children)) =
    fold M (construct tag payload (fun n => (equivalence M).symm (children n)))
  rw [fold_construct]
  exact (equivalence M).apply_symm_apply _ |>.trans
    (congrArg (M.construct tag payload) (funext fun n => ((equivalence M).apply_symm_apply (children n)).symm))

theorem construct_ne_bottom {A : Type u} (tag : Nat) (payload : A) (children : Nat → Tree A) :
    construct tag payload children ≠ bottom := by
  intro same
  have shape := congrArg (fun tree => (Fix.out (polynomial A) tree).1) same
  cases shape

theorem construct_injective {A : Type u} (tag : Nat) (payload : A) (children : Nat → Tree A)
    (tag' : Nat) (payload' : A) (children' : Nat → Tree A) :
    construct tag payload children = construct tag' payload' children' ↔
      tag = tag' ∧ payload = payload' ∧ children = children' := by
  constructor
  · intro same
    have shape := congrArg (fun tree => (Fix.out (polynomial A) tree).1) same
    have points := Option.some.inj shape
    have tags := congrArg Prod.fst points
    have payloads := congrArg Prod.snd points
    cases tags
    cases payloads
    have layers := congrArg (Fix.out (polynomial A)) same
    exact ⟨rfl, rfl, eq_of_heq (Sigma.mk.inj layers).2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def treeModel (A : Type u) : Model A (Tree A) where
  bottom := bottom
  construct := construct
  construct_ne_bottom := construct_ne_bottom
  construct_injective := construct_injective
  induction := fun property at_bottom at_construct value => induction property at_bottom at_construct value

noncomputable def recurseTree {B : Type w} (M : Model A R) (at_bottom : B)
    (method : Nat → A → (Nat → R) → (Nat → B) → B) : Tree A → B :=
  fun tree => Fix.eliminate (polynomial A) (fun _ _ _ => B)
    (fun _ _ shape children values => match shape with
      | none => at_bottom
      | some point => method point.1 point.2 (fun n => fold M (children n)) values)
    PUnit.unit PUnit.unit tree

noncomputable def recurse {B : Type w} (M : Model A R) (at_bottom : B)
    (method : Nat → A → (Nat → R) → (Nat → B) → B) : R → B :=
  fun value => recurseTree M at_bottom method ((equivalence M).symm value)

@[simp] theorem recurse_bottom {B : Type w} (M : Model A R) (at_bottom : B)
    (method : Nat → A → (Nat → R) → (Nat → B) → B) :
    recurse M at_bottom method M.bottom = at_bottom := by
  unfold recurse
  rw [inverse_bottom]
  rfl

@[simp] theorem recurse_construct {B : Type w} (M : Model A R) (at_bottom : B)
    (method : Nat → A → (Nat → R) → (Nat → B) → B)
    (tag : Nat) (payload : A) (children : Nat → R) :
    recurse M at_bottom method (M.construct tag payload children) =
      method tag payload children (fun n => recurse M at_bottom method (children n)) := by
  unfold recurse
  rw [inverse_construct]
  change method tag payload (fun n => fold M ((equivalence M).symm (children n))) _ = _
  have same : (fun n => fold M ((equivalence M).symm (children n))) = children :=
    funext fun n => (equivalence M).apply_symm_apply (children n)
  rw [same]
  rfl

theorem recurse_unique {B : Type w} (M : Model A R) (at_bottom : B)
    (method : Nat → A → (Nat → R) → (Nat → B) → B) (other : R → B)
    (other_bottom : other M.bottom = at_bottom)
    (other_construct : ∀ tag payload children,
      other (M.construct tag payload children) = method tag payload children (fun n => other (children n))) :
    other = recurse M at_bottom method := by
  funext value
  apply M.induction (fun value => other value = recurse M at_bottom method value) ?_ ?_ value
  · exact other_bottom.trans (recurse_bottom M at_bottom method).symm
  · intro tag payload children hypotheses
    rw [other_construct, recurse_construct, funext hypotheses]

/-- Constructor-only recursion leaves the bottom result genuinely free. -/
theorem constructor_recursion_not_unique (M : Model A R) :
    ∃ (first second : R → Bool), first ≠ second ∧
      (∀ tag payload children, first (M.construct tag payload children) = false) ∧
      (∀ tag payload children, second (M.construct tag payload children) = false) := by
  classical
  let first : R → Bool := fun _ => false
  let second : R → Bool := fun value => if value = M.bottom then true else false
  refine ⟨first, second, ?_, ?_, ?_⟩
  · intro same
    have impossible := congrFun same M.bottom
    change false = (if M.bottom = M.bottom then true else false) at impossible
    simp at impossible
  · intro tag payload children
    rfl
  · intro tag payload children
    exact if_neg (M.construct_ne_bottom tag payload children)

namespace Controls

def branching : Tree Bool :=
  construct 3 true (fun n => if n = 0 then bottom else construct 8 false (fun _ => bottom))

theorem branching_roundtrip :
    (equivalence (treeModel Bool)).symm ((equivalence (treeModel Bool)) branching) = branching :=
  fold_injective (treeModel Bool)
    ((equivalence (treeModel Bool)).apply_symm_apply ((equivalence (treeModel Bool)) branching))

noncomputable def depthAtOne : Tree Bool → Nat :=
  fun tree => Fix.eliminate (polynomial Bool) (fun _ _ _ => Nat)
    (fun _ _ shape _children values => match shape with
      | none => 0
      | some _ => Nat.succ (values (1 : Nat))) PUnit.unit PUnit.unit tree

theorem depth_eq_recursion :
    depthAtOne = recurse (treeModel Bool) 0 (fun _ _ _ values => Nat.succ (values 1)) :=
  recurse_unique (treeModel Bool) 0 (fun _ _ _ values => Nat.succ (values 1)) depthAtOne rfl
    (fun _ _ _ => rfl)

theorem branching_depth : depthAtOne branching = 2 := rfl

theorem branching_not_bottom : branching ≠ bottom := construct_ne_bottom _ _ _

theorem tags_distinguished :
    construct 3 true (fun _ => bottom) ≠ construct 8 true (fun _ => bottom) := by
  intro same
  have impossible := ((construct_injective _ _ _ _ _ _).mp same).1
  cases impossible

theorem hidden_child_distinguished : branching ≠ construct 3 true (fun _ => bottom) := by
  intro same
  have children := ((construct_injective _ _ _ _ _ _).mp same).2.2
  have impossible := congrFun children 1
  change (if (1 : Nat) = 0 then bottom else construct 8 false (fun _ => bottom)) = bottom at impossible
  simp only [Nat.one_ne_zero, if_false] at impossible
  exact construct_ne_bottom _ _ _ impossible

theorem tree_recursion_has_two_bottom_choices :
    ∃ (first second : Tree Bool → Bool), first ≠ second ∧
      (∀ tag payload children, first (construct tag payload children) = false) ∧
      (∀ tag payload children, second (construct tag payload children) = false) :=
  constructor_recursion_not_unique (treeModel Bool)

end Controls
#print axioms fold_injective
#print axioms fold_surjective
#print axioms equivalence
#print axioms treeModel
#print axioms recurse_construct
#print axioms recurse_unique
#print axioms constructor_recursion_not_unique
#print axioms Controls.hidden_child_distinguished
end Mettapedia.TypeTheory.RecursiveSpace
