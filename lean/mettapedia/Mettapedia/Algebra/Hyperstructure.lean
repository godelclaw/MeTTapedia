import Mathlib.Data.Set.Functor
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Tauto

/-!
# Algebraic Hyperstructures via Mathlib's `Set` Monad

Hyperoperations, hypermagmas, and Kleisli composition for `Set`, built on
Mathlib's `LawfulMonad Set` (`Data.Set.Functor`). The powerset monad laws
are Mathlib's — we only add the hyperstructure-specific content.

## Key Results

- `HyperOp` / `Hypermagma` / `Hypersemigroup` — algebraic hyperstructures
- `hyperassoc_iff_bind` — the binary operation's associativity expressed using bind
- `HyperOp.isAssociative_iff_setExtend` — exactly the associativity of set extension
- `HyperOp.Hom` — exact direct-image preservation and transport of associativity
- `HyperOp.lift_assoc` — classical associativity lifts to hyperassociativity
- `kleisliAssoc` — Kleisli composition is associative (from `LawfulMonad Set`)

## What Mathlib provides (not reinvented here)

- `Set.monad` — `bind s f = ⋃ i ∈ s, f i` (Mathlib.Data.Set.Functor:99)
- `LawfulMonad Set` — all monad laws proved (Mathlib.Data.Set.Functor:110)
- `Set.bind_def` — `s >>= f = ⋃ i ∈ s, f i`

## References

- Marty (1934): "Sur une généralisation de la notion de groupe"
- Corsini & Leoreanu (2003): "Applications of Hyperstructure Theory"
- Fujita (2025): "Superhypermagma, Lie Superhypergroup"
- Fujita & Smarandache (2026): "Advancing Uncertain Combinatorics"
-/

namespace Mettapedia.Algebra

-- Use Mathlib's Set monad throughout this file
attribute [local instance] Set.monad

universe u

/-! ## §1: Hyperoperation -/

/-- A **hyperoperation** on `α`: a binary operation returning a set of results.
    Empty results are allowed; nonempty images are additional structure.
    Ref: Marty (1934), Corsini & Leoreanu (2003) §1.1 -/
abbrev HyperOp (α : Type u) := α → α → Set α

/-- Lift a classical operation to a hyperoperation via `pure` (singleton). -/
def HyperOp.lift (f : α → α → α) : HyperOp α :=
  fun a b => pure (f a b)

/-- Set extension: apply hyperoperation to all pairs from two sets.
    `A ⋆ B = ⋃ { op a b | a ∈ A, b ∈ B }` -/
def HyperOp.setExtend (op : HyperOp α) (A B : Set α) : Set α :=
  A >>= fun a => B >>= fun b => op a b

namespace HyperOp

@[simp] theorem mem_setExtend (op : HyperOp α) (A B : Set α) (x : α) :
    x ∈ op.setExtend A B ↔ ∃ a ∈ A, ∃ b ∈ B, x ∈ op a b := by
  simp [setExtend, Set.bind_def]

@[simp] theorem setExtend_empty_left (op : HyperOp α) (B : Set α) :
    op.setExtend ∅ B = ∅ := by
  ext x
  simp

@[simp] theorem setExtend_empty_right (op : HyperOp α) (A : Set α) :
    op.setExtend A ∅ = ∅ := by
  ext x
  simp

@[simp] theorem setExtend_singletons (op : HyperOp α) (a b : α) :
    op.setExtend {a} {b} = op a b := by
  ext x
  simp

theorem setExtend_mono (op : HyperOp α) {A A' B B' : Set α}
    (left : A ⊆ A') (right : B ⊆ B') :
    op.setExtend A B ⊆ op.setExtend A' B' := by
  rintro x hx
  obtain ⟨a, ha, b, hb, hx⟩ := (mem_setExtend ..).mp hx
  exact (mem_setExtend ..).mpr ⟨a, left ha, b, right hb, hx⟩

theorem setExtend_iUnion_left (op : HyperOp α) (A : ι → Set α) (B : Set α) :
    op.setExtend (⋃ i, A i) B = ⋃ i, op.setExtend (A i) B := by
  ext x
  simp only [mem_setExtend, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ⟨i, ha⟩, b, hb, hx⟩
    exact ⟨i, a, ha, b, hb, hx⟩
  · rintro ⟨i, a, ha, b, hb, hx⟩
    exact ⟨a, ⟨i, ha⟩, b, hb, hx⟩

theorem setExtend_iUnion_right (op : HyperOp α) (A : Set α) (B : ι → Set α) :
    op.setExtend A (⋃ i, B i) = ⋃ i, op.setExtend A (B i) := by
  ext x
  simp only [mem_setExtend, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, b, ⟨i, hb⟩, hx⟩
    exact ⟨i, a, ha, b, hb, hx⟩
  · rintro ⟨i, a, ha, b, hb, hx⟩
    exact ⟨a, ha, b, ⟨i, hb⟩, hx⟩

theorem setExtend_union_left (op : HyperOp α) (A B C : Set α) :
    op.setExtend (A ∪ B) C = op.setExtend A C ∪ op.setExtend B C := by
  ext x
  simp only [mem_setExtend, Set.mem_union]
  constructor
  · rintro ⟨a, ha | ha, b, hb, hx⟩
    · exact Or.inl ⟨a, ha, b, hb, hx⟩
    · exact Or.inr ⟨a, ha, b, hb, hx⟩
  · rintro (⟨a, ha, b, hb, hx⟩ | ⟨a, ha, b, hb, hx⟩)
    · exact ⟨a, Or.inl ha, b, hb, hx⟩
    · exact ⟨a, Or.inr ha, b, hb, hx⟩

theorem setExtend_union_right (op : HyperOp α) (A B C : Set α) :
    op.setExtend A (B ∪ C) = op.setExtend A B ∪ op.setExtend A C := by
  ext x
  simp only [mem_setExtend, Set.mem_union]
  constructor
  · rintro ⟨a, ha, b, hb | hb, hx⟩
    · exact Or.inl ⟨a, ha, b, hb, hx⟩
    · exact Or.inr ⟨a, ha, b, hb, hx⟩
  · rintro (⟨a, ha, b, hb, hx⟩ | ⟨a, ha, b, hb, hx⟩)
    · exact ⟨a, ha, b, Or.inl hb, hx⟩
    · exact ⟨a, ha, b, Or.inr hb, hx⟩

end HyperOp

/-! ## §2: Hypermagma -/

/-- A **hypermagma**: set + hyperoperation with nonempty images.
    Ref: Fujita (2025) Definition 7 -/
structure Hypermagma (α : Type u) where
  op : HyperOp α
  nonempty_image : ∀ a b : α, (op a b).Nonempty

/-- **Hyperassociativity**: `(a ⋆ b) ⋆ {c} = {a} ⋆ (b ⋆ c)` -/
def HyperOp.isAssociative (op : HyperOp α) : Prop :=
  ∀ a b c : α, op.setExtend (op a b) (pure c) = op.setExtend (pure a) (op b c)

/-- A **hypersemigroup**: hypermagma with associative operation. -/
structure Hypersemigroup (α : Type u) extends Hypermagma α where
  assoc : op.isAssociative

/-! ## §3: Kleisli composition for `Set`

Derived directly from `LawfulMonad Set`. No hand-rolled monad laws. -/

/-- **Kleisli composition** for set-valued functions. -/
def kleisliComp (g : β → Set γ) (f : α → Set β) : α → Set γ :=
  fun a => f a >>= g

infixr:80 " ∘ₖ " => kleisliComp

/-- Kleisli composition is associative.
    Proof: one-line from `LawfulMonad Set`. -/
theorem kleisliAssoc (f : α → Set β) (g : β → Set γ) (h : γ → Set δ) :
    (h ∘ₖ g) ∘ₖ f = h ∘ₖ (g ∘ₖ f) := by
  funext a; show f a >>= (fun b => g b >>= h) = (f a >>= g) >>= h
  rw [bind_assoc]

/-- Left identity: `f ∘ₖ pure = f` -/
theorem kleisliLeftId (f : α → Set β) : f ∘ₖ (pure · : α → Set α) = f := by
  funext a; simp [kleisliComp]

/-- Right identity: `pure ∘ₖ f = f` -/
theorem kleisliRightId (f : α → Set β) : (pure · : β → Set β) ∘ₖ f = f := by
  funext a; simp [kleisliComp]

/-! ## §4: The binary associativity equation in bind notation -/

/-- Set extension with singleton right = bind. -/
theorem setExtend_pure_right (op : HyperOp α) (a b c : α) :
    op.setExtend (op a b) (pure c) = op a b >>= (op · c) := by
  ext x
  simp [Set.bind_def]

/-- Set extension with singleton left = bind. -/
theorem setExtend_pure_left (op : HyperOp α) (a b c : α) :
    op.setExtend (pure a) (op b c) = op b c >>= (op a ·) := by
  ext x
  simp [Set.bind_def]

/-- The associativity condition on `op`, expressed with Set bind.
This is an additional equation on `op`, not a consequence of the monad laws. -/
theorem hyperassoc_iff_bind (op : HyperOp α) :
    op.isAssociative ↔
    ∀ a b c : α, (op a b >>= (op · c)) = (op b c >>= (op a ·)) := by
  constructor
  · intro h a b c; rw [← setExtend_pure_right, ← setExtend_pure_left]; exact h a b c
  · intro h a b c; rw [setExtend_pure_right, setExtend_pure_left]; exact h a b c

/-! ## §5: Extension and exact representation maps -/

namespace HyperOp

theorem isAssociative_iff_mem (op : HyperOp α) :
    op.isAssociative ↔ ∀ a b c x,
      (∃ y ∈ op a b, x ∈ op y c) ↔ (∃ y ∈ op b c, x ∈ op a y) := by
  rw [hyperassoc_iff_bind]
  simp only [Set.ext_iff, Set.bind_def, Set.mem_iUnion, exists_prop]

/-- The binary law is necessary and sufficient for associativity on all sets.
Neither direction requires nonempty images. -/
theorem isAssociative_iff_setExtend (op : HyperOp α) :
    op.isAssociative ↔ Std.Associative op.setExtend := by
  constructor
  · intro associative
    constructor
    intro A B C
    have point := (isAssociative_iff_mem op).mp associative
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, c, hc, hx⟩ := (mem_setExtend ..).mp hx
      obtain ⟨a, ha, b, hb, hy⟩ := (mem_setExtend ..).mp hy
      obtain ⟨z, hz, hx⟩ := (point a b c x).mp ⟨y, hy, hx⟩
      exact (mem_setExtend ..).mpr
        ⟨a, ha, z, (mem_setExtend ..).mpr ⟨b, hb, c, hc, hz⟩, hx⟩
    · intro hx
      obtain ⟨a, ha, z, hz, hx⟩ := (mem_setExtend ..).mp hx
      obtain ⟨b, hb, c, hc, hz⟩ := (mem_setExtend ..).mp hz
      obtain ⟨y, hy, hx⟩ := (point a b c x).mpr ⟨z, hz, hx⟩
      exact (mem_setExtend ..).mpr
        ⟨y, (mem_setExtend ..).mpr ⟨a, ha, b, hb, hy⟩, c, hc, hx⟩
  · intro associative a b c
    simpa only [Set.pure_def, setExtend_singletons] using associative.assoc {a} {b} {c}

@[simp] theorem lift_isAssociative_iff (f : α → α → α) :
    (lift f).isAssociative ↔ Std.Associative f := by
  rw [isAssociative_iff_mem]
  constructor
  · intro h
    exact ⟨by simpa [lift] using h⟩
  · rintro ⟨h⟩
    simpa [lift] using h

/-- Lifting a classical associative operation gives a hyperassociative one. -/
theorem lift_assoc (f : α → α → α)
    (hassoc : ∀ a b c : α, f (f a b) c = f a (f b c)) :
    (lift f).isAssociative :=
  (lift_isAssociative_iff f).mpr ⟨hassoc⟩

/-- An exact map preserves the entire output set of each binary application.
Forward inclusion alone is deliberately insufficient. -/
structure Hom (source : HyperOp α) (target : HyperOp β) where
  toFun : α → β
  image_op : ∀ a b, toFun '' source a b = target (toFun a) (toFun b)

namespace Hom

instance {source : HyperOp α} {target : HyperOp β} :
    CoeFun (Hom source target) (fun _ => α → β) := ⟨Hom.toFun⟩

@[ext] theorem ext {source : HyperOp α} {target : HyperOp β}
    {first second : Hom source target} (same : ∀ a, first a = second a) : first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have equal : first = second := funext same
      subst second
      rfl

def id (op : HyperOp α) : Hom op op where
  toFun := _root_.id
  image_op _ _ := Set.image_id _

def comp {source : HyperOp α} {middle : HyperOp β} {target : HyperOp γ}
    (after : Hom middle target) (before : Hom source middle) : Hom source target where
  toFun := after ∘ before
  image_op a b := by
    calc
      (after.toFun ∘ before.toFun) '' source a b =
          after '' (before '' source a b) :=
        (Set.image_image after.toFun before.toFun (source a b)).symm
      _ = target (after (before a)) (after (before b)) := by
        rw [before.image_op, after.image_op]

@[simp] theorem id_apply (op : HyperOp α) (a : α) : id op a = a := rfl

@[simp] theorem comp_apply {source : HyperOp α} {middle : HyperOp β} {target : HyperOp γ}
    (after : Hom middle target) (before : Hom source middle) (a : α) :
    after.comp before a = after (before a) := rfl

@[simp] theorem comp_id {source : HyperOp α} {target : HyperOp β} (map : Hom source target) :
    map.comp (id source) = map := ext fun _ => rfl

@[simp] theorem id_comp {source : HyperOp α} {target : HyperOp β} (map : Hom source target) :
    (id target).comp map = map := ext fun _ => rfl

theorem comp_assoc {first : HyperOp α} {second : HyperOp β}
    {third : HyperOp γ} {fourth : HyperOp δ}
    (a : Hom first second) (b : Hom second third) (c : Hom third fourth) :
    (c.comp b).comp a = c.comp (b.comp a) := ext fun _ => rfl

theorem nonempty_iff {source : HyperOp α} {target : HyperOp β}
    (map : Hom source target) (a b : α) :
    (target (map a) (map b)).Nonempty ↔ (source a b).Nonempty := by
  rw [← map.image_op]
  exact Set.image_nonempty

theorem image_setExtend {source : HyperOp α} {target : HyperOp β}
    (map : Hom source target) (A B : Set α) :
    map '' source.setExtend A B = target.setExtend (map '' A) (map '' B) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, hx⟩ := (mem_setExtend ..).mp hx
    apply (mem_setExtend ..).mpr
    refine ⟨map a, ⟨a, ha, rfl⟩, map b, ⟨b, hb, rfl⟩, ?_⟩
    rw [← map.image_op]
    exact ⟨x, hx, rfl⟩
  · intro hz
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hz⟩ := (mem_setExtend ..).mp hz
    rw [← map.image_op] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, (mem_setExtend ..).mpr ⟨a, ha, b, hb, hx⟩, rfl⟩

/-- Associativity descends along an exact surjective representation map. -/
theorem associative_of_surjective {source : HyperOp α} {target : HyperOp β}
    (map : Hom source target) (onto : Function.Surjective map)
    (associative : source.isAssociative) : target.isAssociative := by
  intro a b c
  obtain ⟨a, rfl⟩ := onto a
  obtain ⟨b, rfl⟩ := onto b
  obtain ⟨c, rfl⟩ := onto c
  have preserved := congrArg (Set.image map) (associative a b c)
  simpa only [Set.pure_def, image_setExtend, map.image_op, Set.image_singleton] using preserved

/-- An injective exact map reflects the law; a lossy observation need not. -/
theorem associative_of_injective {source : HyperOp α} {target : HyperOp β}
    (map : Hom source target) (faithful : Function.Injective map)
    (associative : target.isAssociative) : source.isAssociative := by
  intro a b c
  apply Set.image_injective.mpr faithful
  simpa only [Set.pure_def, image_setExtend, map.image_op, Set.image_singleton] using
    associative (map a) (map b) (map c)

end Hom

namespace Controls

/-- Either input may be returned. This is genuinely multivalued on distinct inputs. -/
def choice : HyperOp α := fun a b => {a, b}

theorem choice_associative : (choice : HyperOp α).isAssociative := by
  rw [isAssociative_iff_mem]
  intro a b c x
  simp only [choice, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

theorem choice_two_results : false ∈ choice false true ∧ true ∈ choice false true := by
  simp [choice]

/-- A nonidentity exact change of representation. -/
def flipChoice : Hom (choice : HyperOp Bool) (choice : HyperOp Bool) where
  toFun := Bool.not
  image_op a b := by simp [choice, Set.image_insert_eq]

theorem flipChoice_changes_representation : flipChoice false = true := rfl

/-- Lawful nondeterministic sequencing does not make NAND associative. -/
theorem nand_not_associative :
    ¬ (lift (fun a b : Bool => !(a && b))).isAssociative := by
  rw [lift_isAssociative_iff]
  intro associative
  have bad := associative.assoc false false true
  contradiction

theorem empty_associative : isAssociative (fun _ _ : Bool => (∅ : Set Bool)) := by
  rw [isAssociative_iff_mem]
  simp

theorem empty_not_nonempty :
    ¬ ∀ a b : Bool, ((fun _ _ : Bool => (∅ : Set Bool)) a b).Nonempty := by
  intro nonempty
  exact Set.not_nonempty_empty (nonempty false false)

/-- Exactness alone does not reflect associativity: collapsing all Boolean
values hides NAND's failure. -/
def collapseNand : Hom (lift (fun a b : Bool => !(a && b)))
    (lift (fun _ _ : Unit => ())) where
  toFun _ := ()
  image_op _ _ := by simp [lift]

theorem lossy_exact_map_cannot_reflect :
    (lift (fun _ _ : Unit => ())).isAssociative ∧
      ¬ (lift (fun a b : Bool => !(a && b))).isAssociative :=
  ⟨lift_assoc _ (by intros; rfl), nand_not_associative⟩

/-- Zero is fixed; the two other left inputs are exchanged. -/
def isolatedFlip (a _b : Fin 3) : Fin 3 :=
  if a = 0 then 0 else if a = 1 then 2 else 1

/-- An exact injection can see only a closed associative fragment of a
nonassociative operation. -/
def fixedPointIntoFlip : Hom (lift (fun _ _ : Unit => ())) (lift isolatedFlip) where
  toFun _ := 0
  image_op _ _ := by simp [lift, isolatedFlip]

theorem injection_cannot_transport_to_unseen_inputs :
    Function.Injective fixedPointIntoFlip ∧ ¬ (lift isolatedFlip).isAssociative := by
  constructor
  · intro a b _
    cases a
    cases b
    rfl
  · rw [lift_isAssociative_iff]
    intro associative
    have bad := associative.assoc 1 1 1
    have different : isolatedFlip (isolatedFlip 1 1) 1 ≠
        isolatedFlip 1 (isolatedFlip 1 1) := by decide
    exact different bad

end Controls

/-! ## Finite tables, with occurrence-preserving answers -/

namespace Finite

/-- One row occurrence, separate from the support of the binary operation. -/
structure Row (n : Nat) where
  left : Fin n
  right : Fin n
  result : Fin n
deriving DecidableEq, Repr

abbrev Table (n : Nat) := List (Row n)

/-- Scanning a table preserves its row order and repeated outputs. -/
def outputs (table : Table n) (a b : Fin n) : List (Fin n) :=
  table.filterMap fun row => if row.left = a ∧ row.right = b then some row.result else none

/-- Independent relational meaning of the table; occurrence counts are not
part of this observation. -/
def operation (table : Table n) : HyperOp (Fin n) :=
  fun a b => {c | ∃ row ∈ table, row.left = a ∧ row.right = b ∧ row.result = c}

@[simp] theorem mem_outputs (table : Table n) (a b c : Fin n) :
    c ∈ outputs table a b ↔ c ∈ operation table a b := by
  simp only [outputs, List.mem_filterMap, operation, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨row, member, accepted⟩
    split_ifs at accepted with matched
    · exact ⟨row, member, matched.1, matched.2, Option.some.inj accepted⟩
  · rintro ⟨row, member, left, right, rfl⟩
    exact ⟨row, member, by simp [left, right]⟩

@[simp] theorem outputs_nil (a b : Fin n) : outputs [] a b = [] := rfl

@[simp] theorem outputs_cons (row : Row n) (table : Table n) (a b : Fin n) :
    outputs (row :: table) a b =
      if row.left = a ∧ row.right = b then row.result :: outputs table a b
      else outputs table a b := by
  simp only [outputs, List.filterMap_cons]
  split_ifs <;> rfl

theorem outputs_append (first second : Table n) (a b : Fin n) :
    outputs (first ++ second) a b = outputs first a b ++ outputs second a b :=
  List.filterMap_append

theorem operation_append (first second : Table n) (a b : Fin n) :
    operation (first ++ second) a b = operation first a b ∪ operation second a b := by
  ext c
  simp only [← mem_outputs, outputs_append, List.mem_append, Set.mem_union]

/-- Decide the two finite supports obtained from the two bracketings.
The test is about support equality, not equality of ordered executions. -/
def associative? (table : Table n) : Bool :=
  decide (∀ a b c : Fin n,
    ((outputs table a b).flatMap (fun intermediate => outputs table intermediate c)).toFinset =
      ((outputs table b c).flatMap (fun intermediate => outputs table a intermediate)).toFinset)

/-- Executable checking agrees with the independently defined binary law. -/
theorem associative_iff (table : Table n) :
    associative? table = true ↔ (operation table).isAssociative := by
  rw [associative?, decide_eq_true_eq, isAssociative_iff_mem]
  constructor
  · intro checked a b c x
    have same := (Finset.ext_iff.mp (checked a b c)) x
    simpa only [List.mem_toFinset, List.mem_flatMap, mem_outputs] using same
  · intro associative a b c
    apply Finset.ext
    intro x
    simpa only [List.mem_toFinset, List.mem_flatMap, mem_outputs] using associative a b c x

def total? (table : Table n) : Bool :=
  decide (∀ a b : Fin n, outputs table a b ≠ [])

theorem total_iff (table : Table n) :
    total? table = true ↔ ∀ a b, (operation table a b).Nonempty := by
  simp only [total?, decide_eq_true_eq]
  constructor
  · intro nonempty a b
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil (outputs table a b) (nonempty a b)
    exact ⟨c, (mem_outputs ..).mp hc⟩
  · intro nonempty a b empty
    obtain ⟨c, hc⟩ := nonempty a b
    have member := (mem_outputs ..).mpr hc
    rw [empty] at member
    exact List.not_mem_nil member

/-- Both independent checks are required for the traditional nonempty-image
hypersemigroup structure. -/
def checkedHypersemigroup (table : Table n)
    (associative : associative? table = true) (total : total? table = true) :
    Hypersemigroup (Fin n) where
  op := operation table
  nonempty_image := (total_iff table).mp total
  assoc := (associative_iff table).mp associative

namespace Controls

def choiceTable : Table 2 :=
  [⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 1, 1⟩,
   ⟨1, 0, 1⟩, ⟨1, 0, 0⟩, ⟨1, 1, 1⟩, ⟨1, 1, 1⟩]

def nandTable : Table 2 :=
  [⟨0, 0, 1⟩, ⟨0, 1, 1⟩, ⟨1, 0, 1⟩, ⟨1, 1, 0⟩]

theorem choice_passes : associative? choiceTable = true ∧ total? choiceTable = true := by
  decide

def choiceHypersemigroup : Hypersemigroup (Fin 2) :=
  checkedHypersemigroup choiceTable choice_passes.1 choice_passes.2

theorem choice_instance_assoc : choiceHypersemigroup.op.isAssociative :=
  choiceHypersemigroup.assoc

theorem choice_instance_total (a b : Fin 2) : (choiceHypersemigroup.op a b).Nonempty :=
  choiceHypersemigroup.nonempty_image a b

def encodeBool (value : Bool) : Fin 2 := if value then 1 else 0

/-- A genuine change of carrier relates the Boolean operation to the finite
table, whose repeated equal rows remain visible only to the list observer. -/
def choiceEncoding : Hom (HyperOp.Controls.choice : HyperOp Bool) (operation choiceTable) where
  toFun := encodeBool
  image_op a b := by
    cases a <;> cases b <;> ext c <;>
      simp [HyperOp.Controls.choice, Set.image_insert_eq, encodeBool,
        operation, choiceTable, eq_comm]

theorem encodeBool_injective : Function.Injective encodeBool := by decide

theorem encodeBool_surjective : Function.Surjective encodeBool := by decide

theorem encoded_choice_associative : (operation choiceTable).isAssociative :=
  choiceEncoding.associative_of_surjective encodeBool_surjective HyperOp.Controls.choice_associative

/-- The independently checked finite table also reflects the law back to
the Boolean model through the exact injective representation. -/
theorem decoded_choice_associative : (HyperOp.Controls.choice : HyperOp Bool).isAssociative :=
  choiceEncoding.associative_of_injective encodeBool_injective
    ((associative_iff choiceTable).mp choice_passes.1)

theorem nand_fails_associativity_only :
    associative? nandTable = false ∧ total? nandTable = true := by
  decide

theorem empty_passes_associativity_only :
    associative? ([] : Table 2) = true ∧ total? ([] : Table 2) = false := by
  decide

theorem duplicate_rows_visible :
    outputs ([⟨0, 0, 1⟩] : Table 2) 0 0 = [1] ∧
      outputs ([⟨0, 0, 1⟩, ⟨0, 0, 1⟩] : Table 2) 0 0 = [1, 1] := by
  decide

theorem duplicate_rows_same_operation :
    operation ([⟨0, 0, 1⟩] : Table 2) = operation [⟨0, 0, 1⟩, ⟨0, 0, 1⟩] := by
  funext a b
  ext c
  simp [operation]

end Controls
end Finite
end HyperOp

/-! ## Interpretation boundary

The support of a separately specified binary evaluation relation is a
hyperoperation. A hypermagma additionally requires nonempty outputs everywhere;
a hypersemigroup additionally requires the binary associativity equation.
Neither follows merely from using the Set monad. Support also forgets order,
multiplicity and derivation witnesses, which require their own observations.
-/

end Mettapedia.Algebra
