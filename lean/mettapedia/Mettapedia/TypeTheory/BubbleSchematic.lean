import Mettapedia.TypeTheory.BubbleWeakness
import Mettapedia.Logic.Relation.NormalFormDecision
import Mettapedia.GSLT.OpenEnded.SufficientBubbles

/-!
# Schematic bubbles: the weakest one, and when normal forms decide it

A bubble declared by rule schemas converts every instance of its rules: its
rule set is closed under substitution and under the exchange of two variables
(`Schematic`).  The obligation bubble of a program is the weakest bubble that
types it (`BubbleWeakness.obligationBubble_weakest`), but it is not schematic
(`BubbleWeakness.obligation_not_substitution_stable`).

* **The weakest schematic bubble** (`SchematicClosure`): close the required
  conversions under substitution and exchange.  It is schematic, and every
  schematic bubble that meets the requirements converts everything it converts,
  so it has at least as many strict models as each of them
  (`schematicClosure_weakest`); for a program, it types the program and is the
  weakest schematic bubble that does (`schematicObligation_weakest`).  The
  closure is a least model of a Horn theory whose clauses have one premise
  (`schematicClosure_eq_hornClosure`): schematic bubbles are a meet-closed
  family, and the weakest one is computed by forward chaining.
* **Presentation does not change weakness**: two bubbles with the same
  conversion have the same strict models (`models_eq_of_convertible_iff`), and
  reversing every declared step changes neither (`convertible_flip_iff`,
  `models_flip`).  Orienting the equations of a bubble into rewrite rules costs
  no strict model.
* **The normal-form fiber on the core.**  A class that the exchange of two
  variables preserves, and in which no member is fixed by it, is decided by
  normal forms on no set (`not_decidedOn_of_swap_class`), for every schematic
  bubble that keeps apart the two instances that would identify the exchanged
  variables.
* **Commutation of a sum** (`CommutationProgram`): the program that uses
  `v : Vec (x + y)` at `Vec (y + x)`.  Its weakest schematic bubble exists, and
  so does a schematic bubble declaring commutativity of every sum.  Each keeps
  `Vec (x + x)` apart from `Vec (x + y)` (a strict model reads every former as
  the sum of its parts), and neither has its conversion decided by normal forms
  on the program's types (`weakest_not_decidedOn`, `commAdd_not_decidedOn`).
  The same holds for every schematic bubble typing the program that keeps
  those two types apart (`schematic_not_decidedOn`).  So for this program the
  weakest schematic bubble lies outside the normal-form fiber, and a checker
  that compares normal forms cannot be its conversion test.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleSchematic

open Mettapedia.Logic.TheoryModel
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleWeakness
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr
open Mettapedia.Logic.Relation (DecidedOn)

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Exchanging two variables -/

/-- Exchange the variables `c` and `c + 1`; under a binder, the next two. -/
def swapAt (c : Nat) : Expr Base Const → Expr Base Const
  | .bvar k => .bvar (if k = c then c + 1 else if k = c + 1 then c else k)
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (swapAt c A) (swapAt (c + 1) B)
  | .lam A b => .lam (swapAt c A) (swapAt (c + 1) b)
  | .app f a => .app (swapAt c f) (swapAt c a)
  | .const τ k => .const τ k
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (swapAt c p) (swapAt c q)
  | .or p q => .or (swapAt c p) (swapAt c q)
  | .imp p q => .imp (swapAt c p) (swapAt c q)
  | .not p => .not (swapAt c p)
  | .eq a b => .eq (swapAt c a) (swapAt c b)
  | .all A b => .all (swapAt c A) (swapAt (c + 1) b)
  | .ex A b => .ex (swapAt c A) (swapAt (c + 1) b)

/-- **The exchange is an involution.** -/
theorem swapAt_swapAt (e : Expr Base Const) (c : Nat) : swapAt c (swapAt c e) = e := by
  induction e generalizing c
  case bvar k =>
    by_cases first : k = c
    · subst first
      simp [swapAt]
    · by_cases second : k = c + 1
      · subst second
        simp [swapAt]
      · simp [swapAt, first, second]
  all_goals simp_all [swapAt]

/-- A rule set closed under the exchange of two variables. -/
def SwapStable (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ (c : Nat) (left right : Expr Base Const), rules left right →
    rules (swapAt c left) (swapAt c right)

/-- **Steps of an exchange-stable rule set are carried to steps.** -/
theorem rewrite_swapAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SwapStable rules) {e e' : Expr Base Const} (step : Rewrite rules e e') :
    ∀ c : Nat, Rewrite rules (swapAt c e) (swapAt c e') := by
  induction step with
  | root rule => exact fun c => .root (stable c _ _ rule)
  | piDomain _ ih => exact fun c => .piDomain (ih c)
  | piBody _ ih => exact fun c => .piBody (ih (c + 1))
  | lamDomain _ ih => exact fun c => .lamDomain (ih c)
  | lamBody _ ih => exact fun c => .lamBody (ih (c + 1))
  | appFunction _ ih => exact fun c => .appFunction (ih c)
  | appArgument _ ih => exact fun c => .appArgument (ih c)
  | andLeft _ ih => exact fun c => .andLeft (ih c)
  | andRight _ ih => exact fun c => .andRight (ih c)
  | orLeft _ ih => exact fun c => .orLeft (ih c)
  | orRight _ ih => exact fun c => .orRight (ih c)
  | impLeft _ ih => exact fun c => .impLeft (ih c)
  | impRight _ ih => exact fun c => .impRight (ih c)
  | notBody _ ih => exact fun c => .notBody (ih c)
  | eqLeft _ ih => exact fun c => .eqLeft (ih c)
  | eqRight _ ih => exact fun c => .eqRight (ih c)
  | allDomain _ ih => exact fun c => .allDomain (ih c)
  | allBody _ ih => exact fun c => .allBody (ih (c + 1))
  | exDomain _ ih => exact fun c => .exDomain (ih c)
  | exBody _ ih => exact fun c => .exBody (ih (c + 1))

theorem convertible_swapAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SwapStable rules) {e e' : Expr Base Const} (converted : Convertible rules e e')
    (c : Nat) : Convertible rules (swapAt c e) (swapAt c e') :=
  Mettapedia.Logic.Relation.EqvGen.map_of_steps (fun _ _ step => rewrite_swapAt stable step c)
    converted

/-- The variable `k` occurs free; under a binder, the variable `k + 1`. -/
def occurs (k : Nat) : Expr Base Const → Bool
  | .bvar i => i == k
  | .pi A B => occurs k A || occurs (k + 1) B
  | .lam A b => occurs k A || occurs (k + 1) b
  | .app f a => occurs k f || occurs k a
  | .and p q => occurs k p || occurs k q
  | .or p q => occurs k p || occurs k q
  | .imp p q => occurs k p || occurs k q
  | .not p => occurs k p
  | .eq a b => occurs k a || occurs k b
  | .all A b => occurs k A || occurs (k + 1) b
  | .ex A b => occurs k A || occurs (k + 1) b
  | _ => false

/-- **An expression fixed by the exchange of `c` and `c + 1` has no free `c`.** -/
theorem occurs_eq_false_of_swapAt_eq (e : Expr Base Const) (c : Nat)
    (fixed : swapAt c e = e) : occurs c e = false := by
  induction e generalizing c
  case bvar k =>
    by_cases first : k = c
    · subst first
      simp [swapAt] at fixed
    · simp [occurs, first]
  all_goals simp_all [swapAt, occurs]

/-- **Substituting for a variable that does not occur gives the same result
whatever is substituted.** -/
theorem substAt_eq_of_occurs_eq_false (e : Expr Base Const) (c : Nat)
    (first second : Expr Base Const) (absent : occurs c e = false) :
    substAt c first e = substAt c second e := by
  induction e generalizing c
  case bvar k =>
    have distinct : k ≠ c := by simpa [occurs] using absent
    simp [substAt, distinct]
  all_goals simp_all [substAt, occurs]

/-! ## Schematic bubbles and the weakest one -/

/-- A bubble is **schematic** when its rule set is closed under substitution
and under the exchange of two variables, as the instances of rule schemas
are. -/
def Schematic (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  SubstitutionStable rules ∧ SwapStable rules

/-- The closure of required conversions under substitution and exchange. -/
inductive SchematicClosure (required : Expr Base Const → Expr Base Const → Prop) :
    Expr Base Const → Expr Base Const → Prop where
  | base {left right : Expr Base Const} : required left right →
      SchematicClosure required left right
  | subst {left right : Expr Base Const} (depth : Nat) (replacement : Expr Base Const) :
      SchematicClosure required left right →
        SchematicClosure required (substAt depth replacement left) (substAt depth replacement right)
  | swap {left right : Expr Base Const} (c : Nat) : SchematicClosure required left right →
      SchematicClosure required (swapAt c left) (swapAt c right)

theorem schematicClosure_schematic (required : Expr Base Const → Expr Base Const → Prop) :
    Schematic (SchematicClosure required) :=
  ⟨fun _ _ member depth replacement => .subst depth replacement member,
    fun c _ _ member => .swap c member⟩

/-- Conversions of one bubble are conversions of another once every declared
step of the first is a conversion of the second. -/
theorem convertible_of_root {small large : Expr Base Const → Expr Base Const → Prop}
    (into : ∀ left right, small left right → Convertible large left right)
    {e e' : Expr Base Const} (converted : Convertible small e e') : Convertible large e e' := by
  induction converted with
  | rel _ _ step => exact convertible_of_rewrite_convertible (rewrite_mono into step)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- Every schematic bubble that meets the requirements converts every pair of
the closure. -/
theorem SchematicClosure.convertible {required rules : Expr Base Const → Expr Base Const → Prop}
    (schematic : Schematic rules)
    (meets : ∀ left right, required left right → Convertible rules left right)
    {left right : Expr Base Const} (member : SchematicClosure required left right) :
    Convertible rules left right := by
  induction member with
  | base requiredPair => exact meets _ _ requiredPair
  | subst depth replacement _ ih => exact convertible_substAt schematic.1 ih depth replacement
  | swap c _ ih => exact convertible_swapAt schematic.2 ih c

/-- **The weakest schematic bubble meeting required conversions**: every
schematic bubble that meets them converts everything the closure converts, so
it has no more strict models. -/
theorem schematicClosure_weakest {required rules : Expr Base Const → Expr Base Const → Prop}
    (schematic : Schematic rules)
    (meets : ∀ left right, required left right → Convertible rules left right) :
    models strictSat (equations rules) ⊆ models strictSat (equations (SchematicClosure required)) :=
  models_equations_subset_iff.mpr fun _ _ converted =>
    convertible_of_root (fun _ _ member => member.convertible schematic meets) converted

/-- The closure types a program whose terms are globally typed. -/
theorem schematicObligation_types {program : Set (Judgment Base Const)}
    (typable : ∀ j ∈ program, ∃ A, HasType j.ctx j.term A) :
    ∀ j ∈ program, HasTypeIn (SchematicClosure (obligations program)) j.ctx j.term j.type :=
  (typesProgram_iff typable).mpr fun _ _ obligation =>
    Relation.EqvGen.rel _ _ (Rewrite.root (.base obligation))

/-- **The weakest schematic bubble typing a program**: every schematic bubble
that types it has no more strict models than the closure of its obligations. -/
theorem schematicObligation_weakest {program : Set (Judgment Base Const)}
    (typable : ∀ j ∈ program, ∃ A, HasType j.ctx j.term A)
    {rules : Expr Base Const → Expr Base Const → Prop} (schematic : Schematic rules)
    (types : ∀ j ∈ program, HasTypeIn rules j.ctx j.term j.type) :
    models strictSat (equations rules) ⊆
      models strictSat (equations (SchematicClosure (obligations program))) :=
  schematicClosure_weakest schematic fun _ _ obligation =>
    (typesProgram_iff typable).mp types _ _ obligation

/-! ### The closure is a least Horn model -/

open Mettapedia.GSLT.OpenEnded.SufficientBubbles in
/-- The one-premise Horn clauses of substitution and exchange, over pairs of
expressions. -/
def schematicHornTheory : Set (HornClause (Expr Base Const × Expr Base Const)) :=
  {clause | ∃ pair : Expr Base Const × Expr Base Const, clause.premises = {pair} ∧
    ((∃ depth replacement, clause.conclusion =
        (substAt depth replacement pair.1, substAt depth replacement pair.2)) ∨
      ∃ c, clause.conclusion = (swapAt c pair.1, swapAt c pair.2))}

open Mettapedia.GSLT.OpenEnded.SufficientBubbles in
/-- **The weakest schematic bubble is the Horn closure of the requirements**
under the clauses of substitution and exchange. -/
theorem schematicClosure_eq_hornClosure (required : Expr Base Const → Expr Base Const → Prop) :
    {pair : Expr Base Const × Expr Base Const | SchematicClosure required pair.1 pair.2} =
      hornClosure schematicHornTheory {pair | required pair.1 pair.2} := by
  ext pair
  constructor
  · intro member
    have general : ∀ {first second : Expr Base Const}, SchematicClosure required first second →
        HornDerivable schematicHornTheory {pair | required pair.1 pair.2} (first, second) := by
      intro first second member
      induction member with
      | base requiredPair => exact HornDerivable.seed requiredPair
      | @subst left right depth replacement _ ih =>
          exact HornDerivable.rule ⟨{(left, right)}, _⟩
            ⟨(left, right), rfl, Or.inl ⟨depth, replacement, rfl⟩⟩
            (fun p member => by rw [Set.mem_singleton_iff.mp member]; exact ih)
      | @swap left right c _ ih =>
          exact HornDerivable.rule ⟨{(left, right)}, _⟩
            ⟨(left, right), rfl, Or.inr ⟨c, rfl⟩⟩
            (fun p member => by rw [Set.mem_singleton_iff.mp member]; exact ih)
    exact general member
  · intro derivable
    induction derivable with
    | seed member => exact .base member
    | rule clause member _ ih =>
        obtain ⟨premise, premises, conclusion⟩ := member
        have premiseIn : SchematicClosure required premise.1 premise.2 :=
          ih premise (by rw [premises]; exact Set.mem_singleton premise)
        rcases conclusion with ⟨depth, replacement, same⟩ | ⟨c, same⟩
        · rw [same]
          exact .subst depth replacement premiseIn
        · rw [same]
          exact .swap c premiseIn

/-! ## Presentation does not change weakness -/

/-- **Strict models depend on conversion only.** -/
theorem models_eq_of_convertible_iff {first second : Expr Base Const → Expr Base Const → Prop}
    (same : ∀ e e', Convertible first e e' ↔ Convertible second e e') :
    models strictSat (equations first) = models strictSat (equations second) :=
  Set.Subset.antisymm (models_equations_subset_iff.mpr fun e e' => (same e e').mpr)
    (models_equations_subset_iff.mpr fun e e' => (same e e').mp)

theorem rewrite_flip {rules : Expr Base Const → Expr Base Const → Prop} {e e' : Expr Base Const}
    (step : Rewrite (flip rules) e e') : Rewrite rules e' e := by
  induction step with
  | root rule => exact .root rule
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- **Reversing every declared step leaves the conversion unchanged.** -/
theorem convertible_flip_iff {rules : Expr Base Const → Expr Base Const → Prop}
    {e e' : Expr Base Const} : Convertible (flip rules) e e' ↔ Convertible rules e e' := by
  constructor
  · exact convertible_of_root fun _ _ rule =>
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Rewrite.root rule))
  · exact convertible_of_root fun _ _ rule =>
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Rewrite.root (show flip rules _ _ from rule)))

/-- **Orienting a bubble's steps costs no strict model.** -/
theorem models_flip (rules : Expr Base Const → Expr Base Const → Prop) :
    models strictSat (equations (flip rules)) = models strictSat (equations rules) :=
  models_eq_of_convertible_iff fun _ _ => convertible_flip_iff

/-! ## The normal-form fiber on the core -/

/-- **The global judgment is in the fiber, trivially**: it declares no step,
so every expression is its own normal form and conversion is syntactic
identity.  An explicit-step kernel checks every conversion this way, with the
steps supplied in the certificate. -/
theorem noSteps_decidedOn :
    DecidedOn (Rewrite (noSteps : Expr Base Const → Expr Base Const → Prop)) Set.univ := by
  have normal : ∀ e : Expr Base Const,
      Mettapedia.Logic.Relation.IsNormal (Rewrite (noSteps : Expr Base Const → Expr Base Const → Prop)) e :=
    fun _ _ step => rewrite_none step
  refine ⟨fun e _ => ⟨e, .refl, normal e⟩, ?_⟩
  intro a _ b _ n m normalA normalB
  rw [(normal a).reflTransGen_eq normalA.1, (normal b).reflTransGen_eq normalB.1]
  exact convertible_none_iff


/-- **A class preserved by an exchange, with no fixed member, is decided by
normal forms on no set**, for a schematic bubble that keeps apart the two
substitution instances that would identify the exchanged variables. -/
theorem not_decidedOn_of_swap_class {rules : Expr Base Const → Expr Base Const → Prop}
    (schematic : Schematic rules) {c : Nat} {left right : Expr Base Const}
    (swapped : swapAt c left = right) (converted : Convertible rules left right)
    {first second : Expr Base Const}
    (apart : ¬ Convertible rules (substAt c first left) (substAt c second left))
    {S : Set (Expr Base Const)} (leftMember : left ∈ S) (rightMember : right ∈ S) :
    ¬ DecidedOn (Rewrite rules) S := by
  refine Mettapedia.Logic.Relation.not_decidedOn_of_symmetric_class (π := swapAt c)
    (σ := swapAt c) (fun e => swapAt_swapAt e c) (fun _ _ step => rewrite_swapAt schematic.2 step c)
    (fun _ _ step => rewrite_swapAt schematic.2 step c) leftMember (by rwa [swapped])
    (by rw [swapped]; exact Relation.EqvGen.symm _ _ converted) ?_
  intro other toOther fixed
  have absent := occurs_eq_false_of_swapAt_eq other c fixed
  have atFirst := convertible_substAt schematic.1 toOther c first
  have atSecond := convertible_substAt schematic.1 toOther c second
  rw [substAt_eq_of_occurs_eq_false other c first second absent] at atFirst
  exact apart (Relation.EqvGen.trans _ _ _ atFirst (Relation.EqvGen.symm _ _ atSecond))

end Core

/-! ## Commutation of a sum -/

namespace CommutationProgram

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The context `x : nat, y : nat, v : Vec (x + y)`, newest first. -/
def context : List AExpr := [vec (addE (bvar 1) (bvar 0)), natType, natType]

/-- `Vec (x + y)`, seen from the end of the context. -/
def sumXY : AExpr := vec (addE (bvar 2) (bvar 1))

/-- `Vec (y + x)`. -/
def sumYX : AExpr := vec (addE (bvar 1) (bvar 2))

theorem v_typed : HasType context (bvar 0) sumXY :=
  HasType.var (Γ := context) (i := 0) rfl

/-- The program that uses `v : Vec (x + y)` at `Vec (y + x)`. -/
def program : Set (Judgment Unit ArithConst) := {⟨context, bvar 0, sumYX⟩}

theorem program_typable : ∀ j ∈ program, ∃ A, HasType j.ctx j.term A := by
  rintro j rfl
  exact ⟨_, v_typed⟩

/-- The single obligation of the program. -/
theorem obligations_program {A B : AExpr} : obligations program A B ↔ A = sumXY ∧ B = sumYX := by
  constructor
  · rintro ⟨j, rfl, typing, rfl⟩
    exact ⟨(v_typed.unique typing).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, v_typed, rfl⟩

theorem swap_sumXY : swapAt 1 sumXY = sumYX := by
  simp [swapAt, sumXY, sumYX, vec, addE]

/-- `Vec (x + x)`. -/
def sumXX : AExpr := vec (addE (bvar 1) (bvar 1))

theorem substAt_sumXY_zero : substAt 1 (bvar 0) sumXY = sumXX := by
  simp [substAt, sumXY, sumXX, vec, addE, shiftN, shiftAt]

theorem substAt_sumXY_one : substAt 1 (bvar 1) sumXY = sumYX := by
  simp [substAt, sumXY, sumYX, vec, addE, shiftN, shiftAt]

/-! ### A schematic bubble: commutativity of every sum -/

/-- `t + u ↦ u + t`, for all `t`, `u`. -/
inductive CommAdd : AExpr → AExpr → Prop where
  | swap (t u : AExpr) : CommAdd (addE t u) (addE u t)

theorem commAdd_schematic : Schematic CommAdd := by
  constructor
  · rintro _ _ ⟨t, u⟩ depth replacement
    simpa [addE, substAt] using CommAdd.swap (substAt depth replacement t) (substAt depth replacement u)
  · rintro c _ _ ⟨t, u⟩
    simpa [addE, swapAt] using CommAdd.swap (swapAt c t) (swapAt c u)

theorem commAdd_converts : Convertible CommAdd sumXY sumYX :=
  Relation.EqvGen.rel _ _ (Rewrite.appArgument (Rewrite.root (CommAdd.swap (bvar 2) (bvar 1))))

theorem commAdd_types : ∀ j ∈ program, HasTypeIn CommAdd j.ctx j.term j.type := by
  rintro j rfl
  exact hasTypeIn_iff.mpr ⟨_, v_typed, commAdd_converts⟩

/-- The valuation under one more binder: the new variable reads `0`. -/
def extend (ρ : Nat → Nat) : Nat → Nat := fun i => if i = 0 then 0 else ρ (i - 1)

/-- Read every former as the sum of its parts, and a variable by a valuation. -/
def sumValue : AExpr → (Nat → Nat) → Nat
  | .bvar i, ρ => ρ i
  | .pi A B, ρ => sumValue A ρ + sumValue B (extend ρ)
  | .lam A b, ρ => sumValue A ρ + sumValue b (extend ρ)
  | .app f a, ρ => sumValue f ρ + sumValue a ρ
  | .and p q, ρ => sumValue p ρ + sumValue q ρ
  | .or p q, ρ => sumValue p ρ + sumValue q ρ
  | .imp p q, ρ => sumValue p ρ + sumValue q ρ
  | .not p, ρ => sumValue p ρ
  | .eq a b, ρ => sumValue a ρ + sumValue b ρ
  | .all A b, ρ => sumValue A ρ + sumValue b (extend ρ)
  | .ex A b, ρ => sumValue A ρ + sumValue b (extend ρ)
  | _, _ => 0

/-- **A strict model in which sums commute**: two expressions are identified
when they have the same value under every valuation. -/
def sumModel : Congruence Unit ArithConst where
  rel e e' := ∀ ρ, sumValue e ρ = sumValue e' ρ
  equivalence := ⟨fun _ _ => rfl, fun same ρ => (same ρ).symm,
    fun first second ρ => (first ρ).trans (second ρ)⟩
  compatible := by
    intro e e' step
    induction step <;> intro ρ <;> simp_all [sumValue]

theorem sumModel_mem : sumModel ∈ models strictSat (equations CommAdd) := by
  rintro ⟨_, _⟩ ⟨t, u⟩ ρ
  simp only [sumValue]
  omega

/-- `Vec (x + x)` and `Vec (x + y)` have different values. -/
theorem sumModel_separates : ¬ sumModel.rel sumXX sumYX := by
  intro same
  have := same id
  simp [sumValue, sumXX, sumYX, vec, addE] at this

/-- **Commutativity of every sum keeps `Vec (x + x)` apart from
`Vec (x + y)`.** -/
theorem commAdd_apart : ¬ Convertible CommAdd sumXX sumYX :=
  fun converted => sumModel_separates (rel_of_convertible sumModel_mem converted)

/-- The weakest schematic bubble typing the program. -/
abbrev weakest : AExpr → AExpr → Prop := SchematicClosure (obligations program)

/-- It converts no more than commutativity of every sum. -/
theorem weakest_convertible {e e' : AExpr} (converted : Convertible weakest e e') :
    Convertible CommAdd e e' :=
  convertible_of_root (fun _ _ member => member.convertible commAdd_schematic fun _ _ obligation => by
    obtain ⟨rfl, rfl⟩ := obligations_program.mp obligation
    exact commAdd_converts) converted

theorem weakest_apart : ¬ Convertible weakest sumXX sumYX :=
  fun converted => commAdd_apart (weakest_convertible converted)

theorem weakest_converts : Convertible weakest sumXY sumYX :=
  Relation.EqvGen.rel _ _ (Rewrite.root (.base (obligations_program.mpr ⟨rfl, rfl⟩)))

/-- **Every schematic bubble that types the program and keeps `Vec (x + x)`
apart from `Vec (x + y)` is decided by normal forms on no set containing the
program's two types.** -/
theorem schematic_not_decidedOn {rules : AExpr → AExpr → Prop} (schematic : Schematic rules)
    (types : ∀ j ∈ program, HasTypeIn rules j.ctx j.term j.type)
    (apart : ¬ Convertible rules sumXX sumYX) {S : Set AExpr} (xyMember : sumXY ∈ S)
    (yxMember : sumYX ∈ S) : ¬ DecidedOn (Rewrite rules) S :=
  not_decidedOn_of_swap_class schematic swap_sumXY
    ((typesProgram_iff program_typable).mp types _ _ (obligations_program.mpr ⟨rfl, rfl⟩))
    (first := bvar 0) (second := bvar 1)
    (by rw [substAt_sumXY_zero, substAt_sumXY_one]; exact apart) xyMember yxMember

/-- **The weakest schematic bubble of the program is outside the normal-form
fiber.** -/
theorem weakest_not_decidedOn : ¬ DecidedOn (Rewrite weakest) {sumXY, sumYX} :=
  schematic_not_decidedOn (schematicClosure_schematic _) (schematicObligation_types program_typable)
    weakest_apart (Or.inl rfl) (Or.inr rfl)

/-- **Commutativity of every sum is outside the normal-form fiber.** -/
theorem commAdd_not_decidedOn : ¬ DecidedOn (Rewrite CommAdd) {sumXY, sumYX} :=
  schematic_not_decidedOn commAdd_schematic commAdd_types commAdd_apart (Or.inl rfl) (Or.inr rfl)

/-- Commutativity of every sum has no more strict models than the weakest
schematic bubble of the program. -/
theorem commAdd_models_subset_weakest :
    models strictSat (equations CommAdd) ⊆ models strictSat (equations weakest) :=
  schematicObligation_weakest program_typable commAdd_schematic commAdd_types

/-- Reversing commutativity of every sum changes no strict model. -/
theorem commAdd_flip_models :
    models strictSat (equations (flip CommAdd)) = models strictSat (equations CommAdd) :=
  models_eq_of_convertible_iff fun _ _ => convertible_flip_iff

end CommutationProgram

#print axioms swapAt_swapAt
#print axioms rewrite_swapAt
#print axioms occurs_eq_false_of_swapAt_eq
#print axioms substAt_eq_of_occurs_eq_false
#print axioms schematicClosure_weakest
#print axioms schematicObligation_weakest
#print axioms schematicClosure_eq_hornClosure
#print axioms models_eq_of_convertible_iff
#print axioms models_flip
#print axioms noSteps_decidedOn
#print axioms not_decidedOn_of_swap_class
#print axioms CommutationProgram.commAdd_apart
#print axioms CommutationProgram.weakest_apart
#print axioms CommutationProgram.schematic_not_decidedOn
#print axioms CommutationProgram.weakest_not_decidedOn
#print axioms CommutationProgram.commAdd_not_decidedOn

end Mettapedia.TypeTheory.BubbleSchematic
