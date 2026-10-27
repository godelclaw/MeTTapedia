import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image

/-!
# Boundaries of inductive admission: positivity, justified iota, universes, raw instances

An inductive declaration extends formation (a new type former and its constructors) and
conversion (iota rules for its eliminator) at once. This module separates the obligations
such a joint extension carries, each by a model or by the absence of one. The statements are
about Lean's own types and functions, read as candidate interpretations of a declaration: a
declaration whose constructors, eliminator and iota rules admit no interpretation has no
justification in a root theory whose models include these.

* **Positivity is a formation obligation** (`negative_case_inconsistent`). A constructor whose
  field mentions the family to the left of an arrow into the empty type, together with the
  case eliminator's type, already proves `False`; no iota rule is used.
* **The iota rule is load-bearing** (`negativeSignature_inhabited`, `NegativeIota.isEmpty`).
  With a field `D → Bool`, the constructor and the case eliminator have a model, and adding
  the iota rule `case (intro f) = f` leaves none (Cantor). The positive field `Option D` has an
  iota model (`positiveIota_nat`).
* **Typed is not justified** (`WrongSuccessorIota.nat_isEmpty`, `WrongSuccessorIota.unit`).
  The successor rule `rec z s (n+1) ↦ s n (rec z s (n+1))` has the motive's type on both
  sides, so every typing check of a schema accepts it, yet at the motive `ℕ` no recursor
  satisfies it: it asks for a fixed point of the successor. At the motive `Unit` it is
  satisfiable, so a schema is justified only uniformly in its motive. The correct rule is
  satisfied by `Nat.rec` (`correctIota`).
* **Universes are a coordinate of admission** (`SmallTrees.isEmpty_at_same_universe`,
  `SmallTrees.nonempty_one_universe_up`). Trees branching over every type of a universe, with
  their case eliminator and iota rule, have no model whose carrier lies in that universe, and
  have one a universe higher.
* **The motive universe meets existing conversion** (`large_disjunction_elimination_inconsistent`,
  `largeConjunctionElimination`). Under proof irrelevance, an eliminator of a two-constructor
  proposition into types that computes different types on the two constructors identifies
  them; a one-constructor proposition eliminates into types without conflict.
* **Typed schema instances are not raw instances** (`RawCast`). A cast rule whose schema is
  typed at the instance where both indices agree preserves typing there, and its left-linear
  raw form `cast A B e t ↦ t` breaks preservation in a context assuming `e : A = B` for
  distinct `A`, `B`. The raw form that matches the witness `refl` preserves typing at every
  raw instance, by inversion of the witness's type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.InductiveAdmissionBoundaries

universe u v

/-! ## Positivity: a negative field with the case eliminator -/

/-- **A negative occurrence is inconsistent with the case eliminator alone.** The constructor
`intro : (D → False) → D` and the case eliminator `case : D → (D → False)` prove `False` by
diagonalization; no computation rule is involved. -/
theorem negative_case_inconsistent (D : Type u) (intro : (D → False) → D)
    (case : D → D → False) : False :=
  let diagonal : D → False := fun d => case d d
  diagonal (intro diagonal)

/-! ## The iota rule is what a negative field cannot have -/

/-- A family with one constructor whose field is `D → Bool`, and its case eliminator. -/
structure NegativeSignature where
  carrier : Type u
  intro : (carrier → Bool) → carrier
  case : carrier → carrier → Bool

/-- The same signature with its iota rule. -/
structure NegativeIota extends NegativeSignature.{u} where
  iota : ∀ field : carrier → Bool, case (intro field) = field

/-- **The signature alone has a model.** -/
def negativeSignatureUnit : NegativeSignature.{0} where
  carrier := Unit
  intro _ := ()
  case _ _ := true

theorem negativeSignature_inhabited : Nonempty NegativeSignature.{0} :=
  ⟨negativeSignatureUnit⟩

/-- In the model above the iota rule fails. -/
theorem negativeSignatureUnit_not_iota :
    ¬ ∀ field : Unit → Bool,
      negativeSignatureUnit.case (negativeSignatureUnit.intro field) = field := by
  intro iota
  have atFalse := congrFun (iota fun _ => false) ()
  simp [negativeSignatureUnit] at atFalse

/-- **With its iota rule the negative family has no model** (Cantor's diagonal). -/
theorem NegativeIota.isEmpty : IsEmpty NegativeIota.{u} := by
  constructor
  intro family
  let diagonal : family.carrier → Bool := fun d => !(family.case d d)
  have atIntro := congrFun (family.iota diagonal) (family.intro diagonal)
  simp only [diagonal] at atIntro
  revert atIntro
  generalize family.case (family.intro diagonal) (family.intro diagonal) = value
  cases value <;> decide

/-- A family with one positive constructor `intro : Option D → D` and its iota rule. -/
structure PositiveIota where
  carrier : Type u
  intro : Option carrier → carrier
  case : carrier → Option carrier
  iota : ∀ field : Option carrier, case (intro field) = field

/-- **The positive family has an iota model**: the natural numbers. -/
def positiveIota_nat : PositiveIota.{0} where
  carrier := ℕ
  intro
    | none => 0
    | some n => n + 1
  case
    | 0 => none
    | n + 1 => some n
  iota field := by cases field <;> rfl

/-! ## Typed is not justified: a successor rule with the right type and no model -/

/-- A non-dependent recursor for `ℕ` into a motive `M`, with the correct zero rule and the
successor rule `rec z s (n+1) ↦ s n (rec z s (n+1))`. Both sides of each rule have type `M`. -/
structure WrongSuccessorIota (M : Type u) where
  recursor : M → (ℕ → M → M) → ℕ → M
  iotaZero : ∀ zero step, recursor zero step 0 = zero
  iotaSucc : ∀ zero step n, recursor zero step (n + 1) = step n (recursor zero step (n + 1))

/-- **At the motive `ℕ` the typed successor rule has no model**: with the step `m ↦ m + 1` it
asks for a fixed point of the successor. -/
theorem WrongSuccessorIota.nat_isEmpty : IsEmpty (WrongSuccessorIota ℕ) := by
  constructor
  intro recursor
  have fixed := recursor.iotaSucc 0 (fun _ m => m + 1) 0
  omega

/-- At the motive `Unit` the same rule is satisfiable. A schema is justified only when it is
justified at every motive. -/
def WrongSuccessorIota.unit : WrongSuccessorIota Unit where
  recursor zero _ _ := zero
  iotaZero _ _ := rfl
  iotaSucc _ _ _ := rfl

/-- The recursor with the correct successor rule. -/
structure CorrectIota (M : Type u) where
  recursor : M → (ℕ → M → M) → ℕ → M
  iotaZero : ∀ zero step, recursor zero step 0 = zero
  iotaSucc : ∀ zero step n, recursor zero step (n + 1) = step n (recursor zero step n)

/-- **Positive control**: `Nat.rec` satisfies the correct rules at every motive. -/
def correctIota (M : Type u) : CorrectIota M where
  recursor zero step n := Nat.rec (motive := fun _ => M) zero step n
  iotaZero _ _ := rfl
  iotaSucc _ _ _ := rfl

/-! ## Universes: trees over every type of a universe -/

set_option linter.checkUnivs false in
/-- Trees branching over every type of universe `u`, with carrier in universe `v`: the
constructor `sup`, the case eliminator and its iota rule. -/
structure SmallTrees where
  carrier : Type v
  sup : (A : Type u) → (A → carrier) → carrier
  case : carrier → Σ A : Type u, (A → carrier)
  iota : ∀ (A : Type u) (children : A → carrier), case (sup A children) = ⟨A, children⟩

/-- **Same universe: no model.** Sending a set of trees to the tree branching over its
elements is injective, by the iota rule, and Cantor forbids an injection from the sets of a
type into it. -/
theorem SmallTrees.isEmpty_at_same_universe : IsEmpty SmallTrees.{u, u} := by
  constructor
  intro trees
  let collect : Set trees.carrier → trees.carrier := fun s => trees.sup s Subtype.val
  let branches : (Σ A : Type u, (A → trees.carrier)) → Set trees.carrier :=
    fun node => Set.range node.2
  have injective : Function.Injective collect := by
    intro s t same
    have ranges := congrArg (fun tree => branches (trees.case tree)) same
    simp only [collect] at ranges
    rw [trees.iota, trees.iota] at ranges
    simpa only [branches, Subtype.range_coe] using ranges
  exact Function.cantor_injective collect injective

/-- The trees of Lean's own inductive type, one universe up. -/
inductive LargeTree : Type (u + 1) where
  | sup (A : Type u) (children : A → LargeTree) : LargeTree

/-- **One universe up: a model.** -/
def SmallTrees.oneUniverseUp : SmallTrees.{u, u + 1} where
  carrier := LargeTree.{u}
  sup := LargeTree.sup
  case
    | .sup A children => ⟨A, children⟩
  iota _ _ := rfl

theorem SmallTrees.nonempty_one_universe_up : Nonempty SmallTrees.{u, u + 1} :=
  ⟨SmallTrees.oneUniverseUp⟩

/-! ## The motive universe and proof irrelevance -/

/-- **Large elimination of a disjunction is inconsistent with proof irrelevance.** An
eliminator into types that computes `Bool` on one constructor and `Unit` on the other would
identify `Bool` with `Unit`, because the two constructor applications are equal proofs. -/
theorem large_disjunction_elimination_inconsistent {p q : Prop} (left : p) (right : q)
    (eliminate : p ∨ q → Type) (onLeft : eliminate (Or.inl left) = Bool)
    (onRight : eliminate (Or.inr right) = Unit) : False := by
  have irrelevant : (Or.inl left : p ∨ q) = Or.inr right := rfl
  have collapsed : Bool = Unit := onLeft.symm.trans ((congrArg eliminate irrelevant).trans onRight)
  have identified : cast collapsed true = cast collapsed false := Subsingleton.elim _ _
  exact Bool.noConfusion ((cast_inj collapsed).mp identified)

/-- **Positive control**: a one-constructor proposition eliminates into types; Lean's own
kernel admits `And.rec` at a type-valued motive. -/
def largeConjunctionElimination {p q : Prop} (proof : p ∧ q) : Type :=
  And.rec (motive := fun _ => Type) (fun _ _ => Bool) proof

theorem largeConjunctionElimination_eq {p q : Prop} (left : p) (right : q) :
    largeConjunctionElimination (And.intro left right) = Bool := rfl

/-! ## Typed schema instances against raw instances -/

namespace RawCast

/-- Types: two base types and equality types. -/
inductive Ty where
  | nat
  | bool
  | eq (A B : Ty)
  deriving DecidableEq

/-- Terms: variables, two constants, reflexivity and a cast along an equality witness. -/
inductive Tm where
  | var (index : ℕ)
  | zero
  | tt
  | refl (A : Ty)
  | cast (A B : Ty) (witness body : Tm)

/-- Typing in a context of types. -/
inductive HasTy (context : List Ty) : Tm → Ty → Prop where
  | var {index : ℕ} {A : Ty} : context[index]? = some A → HasTy context (.var index) A
  | zero : HasTy context .zero .nat
  | tt : HasTy context .tt .bool
  | refl (A : Ty) : HasTy context (.refl A) (.eq A A)
  | cast {A B : Ty} {witness body : Tm} :
      HasTy context witness (.eq A B) → HasTy context body A →
        HasTy context (.cast A B witness body) B

/-- The left-linear raw rule `cast A B e t ↦ t`, for every raw instance. -/
inductive LinearStep : Tm → Tm → Prop where
  | contract (A B : Ty) (witness body : Tm) : LinearStep (.cast A B witness body) body

/-- The rule at its typed schema instances: both indices agree. -/
inductive SchemaStep : Tm → Tm → Prop where
  | contract (A : Ty) (witness body : Tm) : SchemaStep (.cast A A witness body) body

/-- The raw rule that matches the witness `refl C`, for every raw instance. -/
inductive WitnessStep : Tm → Tm → Prop where
  | contract (A B C : Ty) (body : Tm) : WitnessStep (.cast A B (.refl C) body) body

/-- A step relation preserves typing at every raw instance, in every context. -/
def Preserves (step : Tm → Tm → Prop) : Prop :=
  ∀ {context : List Ty} {left right : Tm} {T : Ty},
    step left right → HasTy context left T → HasTy context right T

/-- **The typed schema instances preserve typing.** -/
theorem schema_preserves : Preserves SchemaStep := by
  intro context left right T step typed
  cases step with
  | contract A witness body =>
      cases typed with
      | cast _ bodyTyped => exact bodyTyped

/-- **The left-linear raw rule breaks preservation**: in the context `e : nat = bool`, the
cast of `zero` has type `bool` and reduces to `zero`, which has only type `nat`. -/
theorem linear_breaks_preservation : ¬ Preserves LinearStep := by
  intro preserves
  have typed : HasTy [.eq .nat .bool] (.cast .nat .bool (.var 0) .zero) .bool :=
    .cast (.var rfl) .zero
  have reduct := preserves (LinearStep.contract .nat .bool (.var 0) .zero) typed
  cases reduct

/-- Every typed schema instance is a raw instance; the raw rule has more instances. -/
theorem schema_le_linear {left right : Tm} (step : SchemaStep left right) :
    LinearStep left right := by
  cases step with
  | contract A witness _ => exact .contract A A witness _

/-- **Matching the witness restores preservation at every raw instance**: the type of
`refl C` forces both indices to be `C`. -/
theorem witness_preserves : Preserves WitnessStep := by
  intro context left right T step typed
  cases step with
  | contract A B C body =>
      cases typed with
      | cast witnessTyped bodyTyped =>
          cases witnessTyped
          exact bodyTyped

end RawCast

/-! ## Axiom audit -/

#print axioms negative_case_inconsistent
#print axioms negativeSignature_inhabited
#print axioms negativeSignatureUnit_not_iota
#print axioms NegativeIota.isEmpty
#print axioms positiveIota_nat
#print axioms WrongSuccessorIota.nat_isEmpty
#print axioms WrongSuccessorIota.unit
#print axioms correctIota
#print axioms SmallTrees.isEmpty_at_same_universe
#print axioms SmallTrees.nonempty_one_universe_up
#print axioms large_disjunction_elimination_inconsistent
#print axioms largeConjunctionElimination_eq
#print axioms RawCast.schema_preserves
#print axioms RawCast.linear_breaks_preservation
#print axioms RawCast.schema_le_linear
#print axioms RawCast.witness_preserves

end Mettapedia.TypeTheory.InductiveAdmissionBoundaries
