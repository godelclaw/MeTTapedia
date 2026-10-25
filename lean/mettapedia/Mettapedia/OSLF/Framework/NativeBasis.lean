import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions
import Mettapedia.OSLF.Framework.BackwardSearch

/-!
# The complete basis of OSLF: higher-order logic over a language's generators

The native types of a language are the predicates of the higher-order logic of a topos. That logic
has a small basis: equality, abstraction and application, with propositions and function types; every
other connective is definable from equality (`HOLLightBooleanDefinitions`: truth, conjunction,
implication, both quantifiers and falsity, with their denotations proved in full models). The
language contributes the rest of the basis (`Const`): its constructors, and the two legs of its
rewrite span, `source` and `target`, from a type of steps (`Base.event`) to the type of states.

Every OSLF operator is then a closed term built from that basis alone (`BasisOnly`):

- the four one-step operators: `diamond` (some step leads into φ), `pastBox` (every step into the
  state comes from φ), `image` (the state is reached in one step from φ) and `forwardBox` (every
  step leads into φ);
- constructor types (`image₁`, `image₂`: the state is built by a constructor from arguments of the
  given types) and the spatial adjoint (`guarantee`: composing with any argument of one type gives
  the other);
- least and greatest fixed points (`lfp`, `gfp`: the intersection of the pre-fixed predicates, the
  union of the post-fixed ones), and reachability (`reach`).

In the standard model of a presentation (`model`), each term denotes the operator it names:
`denote_diamond`, `denote_pastBox`, `denote_image`, `denote_forwardBox` give the change-of-base
modalities of `DerivedModalities`; `denote_reach` gives backward reachability (`Reaches`), and
`denote_lfp`, `denote_gfp` give Knaster–Tarski's fixed points.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NativeBasis

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HOLLightBooleanDefinitions (conj imp all ex applyClosed denote_conj denote_imp denote_all
  denote_ex denote_applyClosed)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch

/-! ## The generators of a language -/

/-- Base types: the sorts of the language, and its steps. -/
inductive Base (Sorts : Type) where
  | sort (sort : Sorts)
  | event

/-- Constants: the constructors of the language, and the two legs of its rewrite span. -/
inductive Const (Sorts : Type) (state : Sorts) (Op : Ty (Base Sorts) → Type) : Ty (Base Sorts) → Type where
  | op {type : Ty (Base Sorts)} (operation : Op type) : Const Sorts state Op type
  | source : Const Sorts state Op (.base .event ⇒ .base (.sort state))
  | target : Const Sorts state Op (.base .event ⇒ .base (.sort state))

variable {Sorts : Type} {state : Sorts} {Op : Ty (Base Sorts) → Type}

/-- The type of states. -/
abbrev stateTy (state : Sorts) : Ty (Base Sorts) := .base (.sort state)

/-- The type of steps. -/
abbrev eventTy : Ty (Base Sorts) := .base .event

/-- Predicates on states: the native types of the state sort. -/
abbrev predTy (state : Sorts) : Ty (Base Sorts) := stateTy state ⇒ .prop

/-! ## The basis -/

/-- **Built from the basis**: variables, constants, application, abstraction and equality only. -/
def BasisOnly {B : Type} {K : Ty B → Type} {Γ : Ctx B} {type : Ty B} : Term K Γ type → Bool
  | .var _ => true
  | .const _ => true
  | .app function argument => BasisOnly function && BasisOnly argument
  | .lam body => BasisOnly body
  | .eq left right => BasisOnly left && BasisOnly right
  | _ => false

theorem basisOnly_rename {B : Type} {K : Ty B → Type} :
    ∀ {Γ Δ : Ctx B} {type : Ty B} (relabel : Rename B Γ Δ) (term : Term K Γ type),
      BasisOnly (rename relabel term) = BasisOnly term
  | _, _, _, _, .var _ => rfl
  | _, _, _, _, .const _ => rfl
  | _, _, _, relabel, .app function argument => by
    simp only [rename, BasisOnly, basisOnly_rename relabel function, basisOnly_rename relabel argument]
  | _, _, _, relabel, .lam body => by
    simp only [rename, BasisOnly, basisOnly_rename (Rename.lift relabel) body]
  | _, _, _, _, .top => rfl
  | _, _, _, _, .bot => rfl
  | _, _, _, _, .and _ _ => rfl
  | _, _, _, _, .or _ _ => rfl
  | _, _, _, _, .imp _ _ => rfl
  | _, _, _, _, .not _ => rfl
  | _, _, _, relabel, .eq left right => by
    simp only [rename, BasisOnly, basisOnly_rename relabel left, basisOnly_rename relabel right]
  | _, _, _, _, .all _ => rfl
  | _, _, _, _, .ex _ => rfl

@[simp] theorem basisOnly_weaken {B : Type} {K : Ty B → Type} {Γ : Ctx B} {σ type : Ty B} (term : Term K Γ type) :
    BasisOnly (weaken (σ := σ) term) = BasisOnly term :=
  basisOnly_rename _ term

theorem basisOnly_weakenCtx {B : Type} {K : Ty B → Type} {type : Ty B} :
    ∀ (Γ : Ctx B) (term : ClosedTerm K type), BasisOnly (weakenCtx Γ term) = BasisOnly term
  | [], _ => rfl
  | _ :: Γ, term => by
    rw [weakenCtx_cons, basisOnly_weaken, basisOnly_weakenCtx Γ term]

section Connectives

variable {B : Type} {K : Ty B → Type} {Γ : Ctx B}

theorem basisOnly_truth : BasisOnly (HOLLightBooleanDefinitions.truth : ClosedTerm K .prop) = true := rfl

theorem basisOnly_applyClosed {domain codomain : Ty B} (function : ClosedTerm K (domain ⇒ codomain))
    (argument : Term K Γ domain) :
    BasisOnly (applyClosed function argument) = (BasisOnly function && BasisOnly argument) := by
  simp only [applyClosed, BasisOnly, basisOnly_weakenCtx]

theorem basisOnly_conj (left right : Formula K Γ) :
    BasisOnly (conj left right) = (BasisOnly left && BasisOnly right) := by
  simp only [conj, BasisOnly, basisOnly_applyClosed]
  have : BasisOnly (HOLLightBooleanDefinitions.conjunction : ClosedTerm K _) = true := by
    simp [HOLLightBooleanDefinitions.conjunction, BasisOnly, basisOnly_truth]
  simp [this]

theorem basisOnly_imp (left right : Formula K Γ) :
    BasisOnly (imp left right) = (BasisOnly left && BasisOnly right) := by
  simp only [imp, BasisOnly, basisOnly_applyClosed]
  have : BasisOnly (HOLLightBooleanDefinitions.implication : ClosedTerm K _) = true := by
    simp [HOLLightBooleanDefinitions.implication, BasisOnly, basisOnly_conj]
  simp [this]

theorem basisOnly_all {type : Ty B} (body : Formula K (type :: Γ)) : BasisOnly (all body) = BasisOnly body := by
  simp only [all, basisOnly_applyClosed, BasisOnly]
  have : BasisOnly (HOLLightBooleanDefinitions.universal type : ClosedTerm K _) = true := by
    simp [HOLLightBooleanDefinitions.universal, BasisOnly, basisOnly_truth]
  simp [this]

theorem basisOnly_ex {type : Ty B} (body : Formula K (type :: Γ)) : BasisOnly (ex body) = BasisOnly body := by
  simp only [ex, basisOnly_applyClosed, BasisOnly]
  have : BasisOnly (HOLLightBooleanDefinitions.existential type : ClosedTerm K _) = true := by
    simp [HOLLightBooleanDefinitions.existential, BasisOnly, basisOnly_all, basisOnly_imp]
  simp [this]

end Connectives

/-! ## The OSLF operators as terms -/

/-- `◇ = λφ. λx. ∃e. source e = x ∧ φ (target e)`. -/
def diamond : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state) :=
  .lam (.lam (ex (conj (.eq (.app (.const .source) (.var .vz)) (.var (.vs .vz)))
    (.app (.var (.vs (.vs .vz))) (.app (.const .target) (.var .vz))))))

/-- `⧫ = λφ. λx. ∀e. target e = x ⇒ φ (source e)`. -/
def pastBox : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state) :=
  .lam (.lam (all (imp (.eq (.app (.const .target) (.var .vz)) (.var (.vs .vz)))
    (.app (.var (.vs (.vs .vz))) (.app (.const .source) (.var .vz))))))

/-- The image `λφ. λx. ∃e. target e = x ∧ φ (source e)`. -/
def image : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state) :=
  .lam (.lam (ex (conj (.eq (.app (.const .target) (.var .vz)) (.var (.vs .vz)))
    (.app (.var (.vs (.vs .vz))) (.app (.const .source) (.var .vz))))))

/-- The forward box `λφ. λx. ∀e. source e = x ⇒ φ (target e)`. -/
def forwardBox : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state) :=
  .lam (.lam (all (imp (.eq (.app (.const .source) (.var .vz)) (.var (.vs .vz)))
    (.app (.var (.vs (.vs .vz))) (.app (.const .target) (.var .vz))))))

/-- **Reachability**, the least predicate containing φ and closed under `◇`:
`λφ. λx. ∀S. (∀y. φ y ⇒ S y) ⇒ (∀y. ◇ S y ⇒ S y) ⇒ S x`. -/
def reach : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state) :=
  .lam (.lam (all (imp
    (all (imp (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
    (imp (all (imp (.app (applyClosed diamond (.var (.vs .vz))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
      (.app (.var .vz) (.var (.vs .vz)))))))

/-- The least fixed point of an operator on predicates: `λx. ∀S. (∀y. F S y ⇒ S y) ⇒ S x`. -/
def lfp (operator : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state)) :
    ClosedTerm (Const Sorts state Op) (predTy state) :=
  .lam (all (imp
    (all (imp (.app (applyClosed operator (.var (.vs .vz))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
    (.app (.var .vz) (.var (.vs .vz)))))

/-- The greatest fixed point: `λx. ∃S. (∀y. S y ⇒ F S y) ∧ S x`. -/
def gfp (operator : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state)) :
    ClosedTerm (Const Sorts state Op) (predTy state) :=
  .lam (ex (conj
    (all (imp (.app (.var (.vs .vz)) (.var .vz)) (.app (applyClosed operator (.var (.vs .vz))) (.var .vz))))
    (.app (.var .vz) (.var (.vs .vz)))))

/-- The constructor type of a unary operation: `λφ. λx. ∃y. x = f y ∧ φ y`. -/
def image₁ {argument result : Ty (Base Sorts)}
    (function : ClosedTerm (Const Sorts state Op) (argument ⇒ result)) :
    ClosedTerm (Const Sorts state Op) ((argument ⇒ .prop) ⇒ result ⇒ .prop) :=
  .lam (.lam (ex (conj (.eq (.var (.vs .vz)) (applyClosed function (.var .vz)))
    (.app (.var (.vs (.vs .vz))) (.var .vz)))))

/-- The constructor type of a binary operation: `λφ. λψ. λx. ∃y. ∃z. x = f y z ∧ φ y ∧ ψ z`. -/
def image₂ {first second result : Ty (Base Sorts)}
    (function : ClosedTerm (Const Sorts state Op) (first ⇒ second ⇒ result)) :
    ClosedTerm (Const Sorts state Op) ((first ⇒ .prop) ⇒ (second ⇒ .prop) ⇒ result ⇒ .prop) :=
  .lam (.lam (.lam (ex (ex (conj
    (.eq (.var (.vs (.vs .vz))) (.app (applyClosed function (.var (.vs .vz))) (.var .vz)))
    (conj (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs .vz)))
      (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))))))))

/-- The spatial adjoint of a binary operation: `λφ. λψ. λx. ∀y. φ y ⇒ ψ (f x y)`. -/
def guarantee {first second result : Ty (Base Sorts)}
    (function : ClosedTerm (Const Sorts state Op) (first ⇒ second ⇒ result)) :
    ClosedTerm (Const Sorts state Op) ((second ⇒ .prop) ⇒ (result ⇒ .prop) ⇒ first ⇒ .prop) :=
  .lam (.lam (.lam (all (imp (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz))
    (.app (.var (.vs (.vs .vz))) (.app (applyClosed function (.var (.vs .vz))) (.var .vz)))))))

/-! ## Every operator is built from the basis -/

theorem diamond_basisOnly : BasisOnly (diamond : ClosedTerm (Const Sorts state Op) _) = true := by
  simp [diamond, BasisOnly, basisOnly_ex, basisOnly_conj]

theorem pastBox_basisOnly : BasisOnly (pastBox : ClosedTerm (Const Sorts state Op) _) = true := by
  simp [pastBox, BasisOnly, basisOnly_all, basisOnly_imp]

theorem image_basisOnly : BasisOnly (image : ClosedTerm (Const Sorts state Op) _) = true := by
  simp [image, BasisOnly, basisOnly_ex, basisOnly_conj]

theorem forwardBox_basisOnly : BasisOnly (forwardBox : ClosedTerm (Const Sorts state Op) _) = true := by
  simp [forwardBox, BasisOnly, basisOnly_all, basisOnly_imp]

theorem reach_basisOnly : BasisOnly (reach : ClosedTerm (Const Sorts state Op) _) = true := by
  simp [reach, BasisOnly, basisOnly_all, basisOnly_imp, basisOnly_applyClosed, diamond_basisOnly]

/-! ## The standard model of a presentation -/

/-- The carriers of the standard model: the language's carriers, and its steps. -/
def carriers (Carrier : Sorts → Type) (Edge : Type) : Base Sorts → Type 1
  | .sort sort => ULift.{1} (Carrier sort)
  | .event => ULift.{1} Edge

/-- **A presentation of a language**: a carrier for each sort, a rewrite span on states, and a value
for each constructor. -/
structure Presentation (Sorts : Type) (state : Sorts) (Op : Ty (Base Sorts) → Type) where
  Carrier : Sorts → Type
  span : ReductionSpan.{0, 0} (Carrier state)
  operation : {type : Ty (Base Sorts)} → Op type → Ty.denote.{0, 0} (carriers Carrier span.Edge) type

variable (presentation : Presentation Sorts state Op)

/-- **The standard model**: every function is in its domain. -/
def model : HenkinModel.{0, 0, 0} (Base Sorts) (Const Sorts state Op) :=
  HenkinModel.standard.{0, 0, 0} (carriers presentation.Carrier presentation.span.Edge) fun constant =>
    match constant with
    | .op operation => presentation.operation operation
    | .source => fun step => ULift.up (presentation.span.source step.down)
    | .target => fun step => ULift.up (presentation.span.target step.down)

theorem model_full : (model presentation).FullDomains :=
  HenkinModel.fullDomains_standard _ _

/-- The values of the model's types. -/
abbrev Value (type : Ty (Base Sorts)) : Type 1 :=
  Ty.denote.{0, 0} (carriers presentation.Carrier presentation.span.Edge) type

/-- A predicate on states as a value of the model. -/
def lift (predicate : presentation.Carrier state → Prop) : Value presentation (predTy state) :=
  fun point => ULift.up (predicate point.down)

/-- A value of predicate type as a predicate on states. -/
def lower (value : Value presentation (predTy state)) : presentation.Carrier state → Prop :=
  fun point => (value (ULift.up point)).down

theorem lower_lift (predicate : presentation.Carrier state → Prop) : lower presentation (lift presentation predicate) = predicate :=
  rfl

theorem lift_lower (value : Value presentation (predTy state)) : lift presentation (lower presentation value) = value := by
  funext point
  rfl

@[simp] theorem extend_vz {Γ : Ctx (Base Sorts)} {σ : Ty (Base Sorts)} (valuation : (model presentation).Valuation Γ)
    (value : Ty.denote (model presentation).Carrier σ) : (model presentation).extend valuation value Var.vz = value := rfl

@[simp] theorem extend_vs {Γ : Ctx (Base Sorts)} {σ τ : Ty (Base Sorts)} (valuation : (model presentation).Valuation Γ)
    (value : Ty.denote (model presentation).Carrier σ) (index : Var Γ τ) :
    (model presentation).extend valuation value (Var.vs index) = valuation index := rfl

/-- The empty valuation. -/
abbrev nowhere : (model presentation).Valuation [] := fun index => nomatch index

/-- A closed term denotes the same under every empty valuation. -/
theorem denote_nil {type : Ty (Base Sorts)} (term : ClosedTerm (Const Sorts state Op) type)
    (valuation : (model presentation).Valuation []) :
    PreModel.denote (model presentation).toPreModel term valuation =
      PreModel.denote (model presentation).toPreModel term (nowhere presentation) := by
  congr 1
  funext τ index
  cases index

/-- The predicate a closed operator gives from a predicate. -/
def apply (term : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state))
    (predicate : presentation.Carrier state → Prop) : presentation.Carrier state → Prop :=
  lower presentation ((model presentation).denote term (nowhere presentation) (lift presentation predicate))

/-! ## What the operators denote -/

theorem denote_diamond (predicate : presentation.Carrier state → Prop) :
    apply presentation diamond predicate = derivedDiamond presentation.span predicate := by
  have full := model_full presentation
  funext point
  apply propext
  simp only [apply, lower, diamond, HenkinModel.denote, PreModel.denote, denote_ex _ full, denote_conj _ full]
  constructor
  · rintro ⟨step, _, same, holds⟩
    exact ⟨step.down, congrArg ULift.down same, holds⟩
  · rintro ⟨step, same, holds⟩
    exact ⟨ULift.up step, trivial, congrArg ULift.up same, holds⟩

theorem denote_pastBox (predicate : presentation.Carrier state → Prop) :
    apply presentation pastBox predicate = derivedBox presentation.span predicate := by
  have full := model_full presentation
  funext point
  apply propext
  simp only [apply, lower, pastBox, HenkinModel.denote, PreModel.denote, denote_all, denote_imp _ full]
  constructor
  · intro holds step ends
    exact holds (ULift.up step) trivial (congrArg ULift.up ends)
  · intro holds step _ ends
    exact holds step.down (congrArg ULift.down ends)

theorem denote_image (predicate : presentation.Carrier state → Prop) :
    apply presentation image predicate = derivedImage presentation.span predicate := by
  have full := model_full presentation
  funext point
  apply propext
  simp only [apply, lower, image, HenkinModel.denote, PreModel.denote, denote_ex _ full, denote_conj _ full]
  constructor
  · rintro ⟨step, _, same, holds⟩
    exact ⟨step.down, congrArg ULift.down same, holds⟩
  · rintro ⟨step, same, holds⟩
    exact ⟨ULift.up step, trivial, congrArg ULift.up same, holds⟩

theorem denote_forwardBox (predicate : presentation.Carrier state → Prop) :
    apply presentation forwardBox predicate = derivedForwardBox presentation.span predicate := by
  have full := model_full presentation
  funext point
  apply propext
  simp only [apply, lower, forwardBox, HenkinModel.denote, PreModel.denote, denote_all, denote_imp _ full]
  constructor
  · intro holds step starts
    exact holds (ULift.up step) trivial (congrArg ULift.up starts)
  · intro holds step _ starts
    exact holds step.down (congrArg ULift.down starts)

theorem denote_diamond_value (valuation : (model presentation).Valuation []) (value : Value presentation (predTy state))
    (point : Ty.denote (model presentation).Carrier (stateTy state)) :
    (PreModel.denote (model presentation).toPreModel diamond valuation value point).down ↔
      derivedDiamond presentation.span (lower presentation value) point.down := by
  rw [denote_nil]
  have key := congrFun (denote_diamond presentation (lower presentation value)) point.down
  unfold apply at key
  rw [lift_lower] at key
  exact Iff.of_eq key

/-- **Reachability denotes backward reachability**: the least predicate containing the goal and closed
under `◇`. -/
theorem denote_reach (goal : presentation.Carrier state → Prop) :
    apply presentation reach goal = Reaches presentation.span goal := by
  have full := model_full presentation
  funext point
  apply propext
  simp only [apply, lower, reach, HenkinModel.denote, PreModel.denote, denote_all, denote_imp _ full,
    denote_applyClosed, extend_vz, extend_vs]
  constructor
  · intro least
    refine least (lift presentation (Reaches presentation.span goal)) trivial
      (fun target _ atGoal => Reaches.goal atGoal) (fun target _ steps => ?_)
    rw [denote_diamond_value] at steps
    obtain ⟨event, starts, reaches⟩ := steps
    show Reaches presentation.span goal target.down
    rw [← starts]
    exact Reaches.step event reaches
  · intro reaches closed _ containsGoal closedUnder
    induction reaches with
    | goal atGoal => exact containsGoal _ trivial atGoal
    | step event _ ih =>
      exact closedUnder _ trivial ((denote_diamond_value presentation _ closed _).mpr ⟨event, rfl, ih containsGoal⟩)

/-- **The least fixed point is the intersection of the pre-fixed predicates.** -/
theorem denote_lfp (operator : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state))
    (point : presentation.Carrier state) :
    lower presentation ((model presentation).denote (lfp operator) (nowhere presentation)) point ↔
      ∀ prefixed : presentation.Carrier state → Prop,
        apply presentation operator prefixed ≤ prefixed → prefixed point := by
  have full := model_full presentation
  simp only [lower, lfp, HenkinModel.denote, PreModel.denote, denote_all, denote_imp _ full, denote_applyClosed,
    extend_vz, extend_vs]
  constructor
  · intro least prefixed closed
    exact least (lift presentation prefixed) trivial fun target _ holds => by
      rw [denote_nil] at holds
      exact closed target.down holds
  · intro least value _ closed
    rw [← lift_lower presentation value] at closed ⊢
    exact least (lower presentation value) fun target holds => by
      have := closed (ULift.up target) trivial
      rw [denote_nil] at this
      exact this holds

/-- **The greatest fixed point is the union of the post-fixed predicates.** -/
theorem denote_gfp (operator : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state))
    (point : presentation.Carrier state) :
    lower presentation ((model presentation).denote (gfp operator) (nowhere presentation)) point ↔
      ∃ postfixed : presentation.Carrier state → Prop,
        postfixed ≤ apply presentation operator postfixed ∧ postfixed point := by
  have full := model_full presentation
  simp only [lower, gfp, HenkinModel.denote, PreModel.denote, denote_ex _ full, denote_conj _ full, denote_all,
    denote_imp _ full, denote_applyClosed, extend_vz, extend_vs]
  constructor
  · rintro ⟨value, _, closed, holds⟩
    refine ⟨lower presentation value, fun target inside => ?_, holds⟩
    have := closed (ULift.up target) trivial inside
    rw [denote_nil, ← lift_lower presentation value] at this
    exact this
  · rintro ⟨postfixed, closed, holds⟩
    refine ⟨lift presentation postfixed, trivial, fun target _ inside => ?_, holds⟩
    rw [denote_nil]
    exact closed target.down inside

theorem denote_lfp_eq (operator : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state))
    (monotone : Monotone (apply presentation operator)) :
    lower presentation ((model presentation).denote (lfp operator) (nowhere presentation)) =
      OrderHom.lfp ⟨apply presentation operator, monotone⟩ := by
  funext point
  apply propext
  rw [denote_lfp]
  constructor
  · intro least
    exact OrderHom.le_lfp ⟨apply presentation operator, monotone⟩ (a := fun target =>
        ∀ prefixed : presentation.Carrier state → Prop, apply presentation operator prefixed ≤ prefixed → prefixed target)
      (fun prefixed closed _ inside => inside prefixed closed) point least
  · intro inLfp prefixed closed
    exact OrderHom.lfp_le ⟨apply presentation operator, monotone⟩ closed point inLfp

theorem denote_gfp_eq (operator : ClosedTerm (Const Sorts state Op) (predTy state ⇒ predTy state))
    (monotone : Monotone (apply presentation operator)) :
    lower presentation ((model presentation).denote (gfp operator) (nowhere presentation)) =
      OrderHom.gfp ⟨apply presentation operator, monotone⟩ := by
  funext point
  apply propext
  rw [denote_gfp]
  constructor
  · rintro ⟨postfixed, closed, inside⟩
    exact OrderHom.le_gfp ⟨apply presentation operator, monotone⟩ closed point inside
  · intro inGfp
    refine ⟨OrderHom.gfp ⟨apply presentation operator, monotone⟩, ?_, inGfp⟩
    exact (OrderHom.map_gfp (⟨apply presentation operator, monotone⟩ : (presentation.Carrier state → Prop) →o _)).ge

/-- **A constructor type** holds of the values built by the constructor from arguments of the type. -/
theorem denote_image₁ {argument result : Ty (Base Sorts)}
    (function : ClosedTerm (Const Sorts state Op) (argument ⇒ result))
    (predicate : Value presentation (argument ⇒ .prop)) (point : Value presentation result) :
    ((model presentation).denote (image₁ function) (nowhere presentation) predicate point).down ↔
      ∃ origin, (model presentation).Eqv result point
        ((model presentation).denote function (nowhere presentation) origin) ∧ (predicate origin).down := by
  have full := model_full presentation
  have fixed : ∀ (valuation : (model presentation).Valuation []) origin,
      PreModel.denote (model presentation).toPreModel function valuation origin =
        PreModel.denote (model presentation).toPreModel function (nowhere presentation) origin :=
    fun valuation origin => congrFun (denote_nil presentation function valuation) origin
  simp only [image₁, HenkinModel.denote, PreModel.denote, denote_ex _ full, denote_conj _ full, denote_applyClosed,
    extend_vz, extend_vs, fixed]
  exact ⟨fun ⟨origin, _, same, holds⟩ => ⟨origin, same, holds⟩, fun ⟨origin, same, holds⟩ => ⟨origin, trivial, same, holds⟩⟩

/-- **The spatial adjoint** holds of the values that, composed with any argument of the first type,
give a value of the second. -/
theorem denote_guarantee {first second result : Ty (Base Sorts)}
    (function : ClosedTerm (Const Sorts state Op) (first ⇒ second ⇒ result))
    (given : Value presentation (second ⇒ .prop)) (promised : Value presentation (result ⇒ .prop))
    (point : Value presentation first) :
    ((model presentation).denote (guarantee function) (nowhere presentation) given promised point).down ↔
      ∀ partner, (given partner).down →
        (promised ((model presentation).denote function (nowhere presentation) point partner)).down := by
  have full := model_full presentation
  have fixed : ∀ (valuation : (model presentation).Valuation []) origin,
      PreModel.denote (model presentation).toPreModel function valuation origin =
        PreModel.denote (model presentation).toPreModel function (nowhere presentation) origin :=
    fun valuation origin => congrFun (denote_nil presentation function valuation) origin
  simp only [guarantee, HenkinModel.denote, PreModel.denote, denote_all, denote_imp _ full, denote_applyClosed,
    extend_vz, extend_vs, fixed]
  exact ⟨fun holds partner given => holds partner trivial given, fun holds partner _ given => holds partner given⟩

end Mettapedia.OSLF.Framework.NativeBasis
