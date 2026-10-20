import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision
import Mettapedia.Logic.HOL.ConversionTiers

/-!
# The common beta fragment of the sealed tower and HOL

The one-base simply typed calculus has an interpretation in HOL at any chosen
base sort. Its context, variable, term and substitution maps retain the simple
types. HOL beta joinability on this image is exactly intrinsic beta conversion,
and hence exactly the existing sealed cumulative tower's conversion on that
same image. The statement allows the tower conversion path to leave the image.

This compares computation, not all HOL theoremhood or all inhabitants of the
dependent types. In particular, HOL proves eta equality for a pair that the
beta-only tower does not convert. Logical equality and a selected conversion
policy are different interfaces even on these simple terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLComparison

open IntrinsicSTT
open Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The chosen atomic sort remains distinct from the proposition sort. -/
def type (ground : Base) : Ty → HOL.Ty Base
  | .atom => .base ground
  | .arr domain codomain => .arr (type ground domain) (type ground codomain)

abbrev context (ground : Base) (Γ : List Ty) : HOL.Ctx Base := Γ.map (type ground)

def toVar (ground : Base) : {Γ : List Ty} → {A : Ty} →
    Var Γ A → HOL.Var (context ground Γ) (type ground A)
  | _, _, .zero => .vz
  | _, _, .succ index => .vs (toVar ground index)

/-- The logical signature contributes no constants to these lambda terms. -/
def term (ground : Base) : {Γ : List Ty} → {A : Ty} →
    Term Γ A → HOL.Term Const (context ground Γ) (type ground A)
  | _, _, .var index => .var (toVar ground index)
  | _, _, .lam body => .lam (term ground body)
  | _, _, .app function argument => .app (term ground function) (term ground argument)

variable (ground : Base)
variable {Γ Δ : List Ty} {A B : Ty}

/-- Every variable in an image context comes from its original typed context. -/
theorem forall_variables (P : ∀ {τ}, HOL.Var (context ground Γ) τ → Prop)
    (holds : ∀ {A} (index : Var Γ A), P (toVar ground index)) :
    ∀ {τ} (index : HOL.Var (context ground Γ) τ), P index := by
  induction Γ with
  | nil => intro τ index; exact nomatch index
  | cons A Γ ih =>
      intro τ index
      cases index with
      | vz => exact holds .zero
      | vs index =>
          exact ih (fun index => P (.vs index)) (fun index => holds (.succ index)) index

theorem type_injective : Function.Injective (type ground) := by
  intro left
  induction left with
  | atom => intro right same; cases right <;> cases same; rfl
  | arr a b ia ib =>
      intro right same
      cases right with
      | atom => cases same
      | arr c d =>
          obtain ⟨sameA, sameB⟩ := HOL.Ty.arr.inj same
          rw [ia sameA, ib sameB]

/-- Variable positions do not acquire a new meaning at the HOL boundary. -/
theorem variable_injective {left right : Var Γ A}
    (same : toVar ground left = toVar ground right) : left = right := by
  induction left with
  | zero => cases right <;> cases same; rfl
  | succ left ih =>
      cases right with
      | zero => cases same
      | succ right => exact congrArg Var.succ (ih (HOL.Var.vs.inj same))

/-- Typed HOL syntax retains the binder types that raw dependent erasure loses. -/
theorem term_injective {left right : Term Γ A}
    (same : term (Const := Const) ground left = term ground right) : left = right := by
  induction left with
  | var index =>
      cases right with
      | var other => exact congrArg Term.var (variable_injective ground (HOL.Term.var.inj same))
      | _ => cases same
  | @lam B Γ C body ih =>
      cases right with
      | lam other => exact congrArg Term.lam (ih (HOL.Term.lam.inj same))
      | _ => cases same
  | app function argument ihf iha =>
      cases right with
      | app function' argument' =>
          have equal := HOL.Term.app.inj same
          have domains := type_injective ground equal.1
          cases domains
          exact congrArg₂ Term.app (ihf (eq_of_heq equal.2.1))
            (iha (eq_of_heq equal.2.2))
      | _ => cases same

/-- Simultaneous renaming on the selected context image. -/
def toRen (ρ : Renaming Γ Δ) : HOL.Rename Base (context ground Γ) (context ground Δ) :=
  fun index => by
    induction Γ with
    | nil => exact nomatch index
    | cons A Γ ih =>
        cases index with
        | vz => exact toVar ground (ρ .zero)
        | vs index => exact ih (fun i => ρ (.succ i)) index

@[simp] theorem renaming_variable (ρ : Renaming Γ Δ) (index : Var Γ A) :
    toRen ground ρ (toVar ground index) = toVar ground (ρ index) := by
  induction index with
  | zero => rfl
  | succ index ih => exact ih (ρ := fun i => ρ (.succ i))

theorem rename_term (ρ : Renaming Γ Δ) (t : Term Γ A) :
    HOL.rename (toRen ground ρ) (term (Const := Const) ground t) =
      term ground (t.rename ρ) := by
  induction t generalizing Δ with
  | var index => exact congrArg HOL.Term.var (renaming_variable ground ρ index)
  | app f a ihf iha => exact congrArg₂ HOL.Term.app (ihf ρ) (iha ρ)
  | @lam B Γ C body ih =>
      change HOL.Term.lam (HOL.rename _ (term ground body)) = _
      have lifted : (HOL.Rename.lift (toRen ground ρ) :
          HOL.Rename Base (context ground (B :: Γ)) (context ground (B :: Δ))) =
          (fun {_} index => toRen ground (liftRenaming (B := B) ρ) index) := by
        funext τ index
        refine forall_variables ground (Γ := B :: Γ)
          (fun index => HOL.Rename.lift (toRen ground ρ) index =
            toRen ground (liftRenaming (B := B) ρ) index) ?_ index
        intro D index
        cases index with
        | zero => rfl
        | succ index =>
            change HOL.Var.vs (toRen ground ρ (toVar ground index)) =
              toRen ground (liftRenaming ρ) (toVar ground (.succ index))
            rw [renaming_variable, renaming_variable]
            rfl
      rw [lifted, ih]
      rfl

theorem weaken_term (t : Term Γ A) :
    HOL.weaken (σ := type ground B) (term (Const := Const) ground t) =
      term ground (t.rename (IntrinsicSTT.weakening (B := B))) := by
  rw [← rename_term]
  apply HOL.rename_ext
  intro τ index
  refine forall_variables ground (Γ := Γ)
    (fun index => HOL.Rename.weaken index =
      toRen ground (IntrinsicSTT.weakening (B := B)) index) ?_ index
  intro C index
  simp only [renaming_variable, IntrinsicSTT.weakening, toVar, HOL.Rename.weaken]

/-- Simultaneous substitution, with every original type retained. -/
def substitution (σ : Substitution Γ Δ) :
    HOL.Subst Const (context ground Γ) (context ground Δ) :=
  fun index => by
    induction Γ with
    | nil => exact nomatch index
    | cons A Γ ih =>
        cases index with
        | vz => exact term ground (σ .zero)
        | vs index => exact ih (fun i => σ (.succ i)) index

@[simp] theorem substitution_variable (σ : Substitution Γ Δ) (index : Var Γ A) :
    substitution ground σ (toVar ground index) = term (Const := Const) ground (σ index) := by
  induction index with
  | zero => rfl
  | succ index ih => exact ih (σ := fun i => σ (.succ i))

theorem substitute_term (σ : Substitution Γ Δ) (t : Term Γ A) :
    HOL.subst (substitution ground σ) (term (Const := Const) ground t) =
      term ground (t.substitute σ) := by
  induction t generalizing Δ with
  | var index => exact substitution_variable ground σ index
  | app f a ihf iha => exact congrArg₂ HOL.Term.app (ihf σ) (iha σ)
  | @lam B Γ C body ih =>
      change HOL.Term.lam (HOL.subst _ (term ground body)) = _
      have weakening : (HOL.Rename.weaken :
          HOL.Rename Base (context ground Δ) (context ground (B :: Δ))) =
          (fun {_} index => toRen ground (IntrinsicSTT.weakening (B := B)) index) := by
        funext τ index
        refine forall_variables ground (Γ := Δ)
          (fun index => HOL.Rename.weaken index =
            toRen ground (IntrinsicSTT.weakening (B := B)) index) ?_ index
        intro D index
        simp [HOL.Rename.weaken, renaming_variable, IntrinsicSTT.weakening, toVar]
      have lifted : (HOL.Subst.lift (substitution (Const := Const) ground σ) :
          HOL.Subst Const (context ground (B :: Γ)) (context ground (B :: Δ))) =
          (fun {_} index => substitution ground (liftSubstitution (B := B) σ) index) := by
        funext τ index
        refine forall_variables ground (Γ := B :: Γ)
          (fun index => HOL.Subst.lift (substitution (Const := Const) ground σ) index =
            substitution ground (liftSubstitution (B := B) σ) index) ?_ index
        intro D index
        cases index with
        | zero => rfl
        | succ index =>
            change HOL.weaken (substitution ground σ (toVar ground index)) =
              substitution ground (liftSubstitution σ) (toVar ground (.succ index))
            rw [substitution_variable, substitution_variable]
            change HOL.rename _ (term ground (σ index)) =
              term ground ((σ index).rename IntrinsicSTT.weakening)
            rw [weakening, rename_term]
      rw [lifted, ih]
      rfl

theorem instantiate_term (body : Term (A :: Γ) B) (argument : Term Γ A) :
    HOL.instantiate (term (Const := Const) ground argument) (term ground body) =
      term ground (body.instantiateNewest argument) := by
  change HOL.subst _ _ = _
  have single : (HOL.Subst.single (term (Const := Const) ground argument) : HOL.Subst Const (context ground (A :: Γ)) (context ground Γ)) =
      (fun {_} index => substitution (Const := Const) ground (newestSubstitution argument) index) := by
    funext τ index
    refine forall_variables ground (Γ := A :: Γ)
      (fun index => HOL.Subst.single (term (Const := Const) ground argument) index =
        substitution ground (newestSubstitution argument) index) ?_ index
    intro D index
    cases index with
    | zero => rfl
    | succ index =>
        change HOL.Term.var (toVar ground index) =
          substitution ground (newestSubstitution argument) (toVar ground (.succ index))
        rw [substitution_variable]
        rfl
  rw [single, substitute_term]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The substitution square is a genuine functor between the existing context
categories. It does not assert chosen cartesian lifts or a fibration. -/
def contextFunctor : CategoryTheory.Functor syntacticCwfWithTerminal.toCwf.base.Context
    (HOL.ContextualTrinity.SubstContext Base Const) where
  obj Γ := ⟨context ground Γ.val⟩
  map σ := substitution ground σ
  map_id Γ := by
    funext τ index
    refine forall_variables ground (Γ := Γ.val)
      (fun index => substitution ground (Substitution.id Γ.val) index = HOL.Term.var index) ?_ index
    intro B index
    rw [substitution_variable]
    rfl
  map_comp {X Y Z} σ τ := by
    funext A index
    refine forall_variables ground (Γ := Z.val)
      (fun index => substitution ground (Substitution.comp τ σ) index =
        HOL.subst (substitution ground σ) (substitution ground τ index)) ?_ index
    intro B index
    rw [substitution_variable, substitution_variable, substitute_term]
    rfl

theorem betaStep_toHOL {left right : Term Γ A} (step : BetaStep left right) :
    Nonempty (HOL.ContextualTrinity.BetaStep (term (Const := Const) ground left) (term ground right)) := by
  induction step with
  | beta body argument =>
      rw [← instantiate_term]
      exact ⟨.beta _ _⟩
  | lam _ ih => obtain ⟨step⟩ := ih; exact ⟨.lam step⟩
  | appLeft _ ih => obtain ⟨step⟩ := ih; exact ⟨.appFun _ step⟩
  | appRight _ ih => obtain ⟨step⟩ := ih; exact ⟨.appArg _ step⟩

theorem steps_toHOL {left right : Term Γ A}
    (steps : Relation.ReflTransGen BetaStep left right) :
    HOL.BetaNormalization.ReducesStar (term (Const := Const) ground left) (term ground right) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (betaStep_toHOL ground step)

private theorem normal_image_properties (t : Term Γ A) :
    (Neutral t → HOL.BetaNormalization.Neutral (term (Const := Const) ground t) ∧
      HOL.BetaNormalization.Normal (term (Const := Const) ground t)) ∧
    (Normal t → HOL.BetaNormalization.Normal (term (Const := Const) ground t)) := by
  induction t with
  | var index =>
      exact ⟨fun _ => ⟨by trivial, HOL.BetaNormalization.var_irreducible _⟩,
        fun _ => HOL.BetaNormalization.var_irreducible _⟩
  | lam body ih =>
      constructor
      · intro neutral
        cases neutral
      · intro normal target reduces
        cases normal with
        | neutral h => cases h
        | lam h =>
            obtain ⟨body', step, _⟩ := HOL.BetaNormalization.lam_cases reduces
            exact ih.2 h body' step
  | app f a ihf iha =>
      have applied (nf : Neutral f) (na : Normal a) :
          HOL.BetaNormalization.Normal (term (Const := Const) ground (.app f a)) := by
        have f := ihf.1 nf
        have a := iha.2 na
        intro target reduces
        rcases HOL.BetaNormalization.app_cases reduces with
          ⟨body, same, _⟩ | ⟨function', step, _⟩ | ⟨argument', step, _⟩
        · rw [same] at f
          exact f.1
        · exact f.2 function' step
        · exact a argument' step
      constructor
      · intro neutral
        cases neutral with
        | app nf na => exact ⟨by trivial, applied nf na⟩
      · intro normal
        cases normal with
        | neutral h => cases h with | app nf na => exact applied nf na

theorem normal_toHOL {t : Term Γ A} (normal : Normal t) :
    HOL.BetaNormalization.Normal (term (Const := Const) ground t) :=
  (normal_image_properties ground t).2 normal

/-- Exact computational comparison; neither direction uses a theoremhood
assumption or a chosen proof of the desired conversion. -/
theorem holJoinable_iff_betaConv (left right : Term Γ A) :
    HOL.ConversionTiers.Joinable (term (Const := Const) ground left) (term ground right) ↔
      BetaConv left right := by
  constructor
  · rintro ⟨meet, ⟨leftRun⟩, ⟨rightRun⟩⟩
    have equal := HOL.BetaNormalization.normal_eq_of_joinable
      (HOL.ConversionTiers.execution_star leftRun)
      (HOL.ConversionTiers.execution_star rightRun)
      (steps_toHOL ground (Normalization.normalize left).reduces)
      (normal_toHOL ground (ConversionDecision.normalize_normal left))
      (steps_toHOL ground (Normalization.normalize right).reduces)
      (normal_toHOL ground (ConversionDecision.normalize_normal right))
    exact (ConversionDecision.normalize_eq_iff_betaConv left right).1
      (term_injective ground equal)
  · intro converted
    have equal := (ConversionDecision.normalize_eq_iff_betaConv left right).2 converted
    refine ⟨term ground (Normalization.normalize left).normalForm,
      HOL.ConversionTiers.star_execution (steps_toHOL ground (Normalization.normalize left).reduces), ?_⟩
    rw [equal]
    exact HOL.ConversionTiers.star_execution
      (steps_toHOL ground (Normalization.normalize right).reduces)

/-- The lower simple checker decides the larger tower's conversion on the
declared image, and the same observation in HOL's operational calculus. -/
theorem holJoinable_iff_towerConv (left right : Term Γ A) :
    HOL.ConversionTiers.Joinable (term (Const := Const) ground left) (term ground right) ↔
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Conv
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.HeadEq
        (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right) :=
  (holJoinable_iff_betaConv ground left right).trans
    (ConversionDecision.towerConv_iff_betaConv left right).symm

theorem decideConversion_iff_holJoinable (left right : Term Γ A) :
    ConversionDecision.decideConversion left right = true ↔
      HOL.ConversionTiers.Joinable (term (Const := Const) ground left) (term ground right) :=
  (ConversionDecision.decideConversion_correct left right).trans
    (holJoinable_iff_betaConv ground left right).symm

/-- Every accepted simple conversion has a retained HOL equality proof.
It need not retain the particular path used to establish conversion. -/
theorem equality_proof_of_conversion (assumptions : List (HOL.Formula Const (context ground Γ)))
    {left right : Term Γ A} (converted : BetaConv left right) :
    Nonempty (HOL.ProofSyntax Const assumptions (.eq (term ground left) (term ground right))) := by
  obtain ⟨meet, ⟨leftRun⟩, ⟨rightRun⟩⟩ :=
    (holJoinable_iff_betaConv ground left right).2 converted
  exact ⟨.eqTrans (HOL.ContextualTrinity.Execution.proof assumptions leftRun)
    (.eqSymm (HOL.ContextualTrinity.Execution.proof assumptions rightRun))⟩

namespace Controls

open ConversionDecision

/-- A logical eta theorem is available without adding eta to beta conversion. -/
def etaProof : HOL.ProofSyntax Const []
    (.eq (term ground etaExpansion) (term ground etaVariable)) :=
  .eta (term ground etaVariable)

theorem eta_not_holJoinable :
    ¬ HOL.ConversionTiers.Joinable (term (Const := Const) ground etaVariable)
      (term ground etaExpansion) :=
  fun h => eta_not_betaConvertible ((holJoinable_iff_betaConv ground _ _).1 h)

theorem eta_not_towerConv :
    ¬ Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Conv
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.HeadEq
      (TowerDTT.eraseTerm etaVariable) (TowerDTT.eraseTerm etaExpansion) :=
  fun h => eta_not_betaConvertible ((towerConv_iff_betaConv _ _).1 h)

/-- Even on the image, arbitrary HOL equality proofs do not reflect into the
chosen beta-only conversion judgment. -/
theorem hol_equality_does_not_reflect_conversion :
    ¬ (∀ {Γ : List Ty} {A : Ty} (left right : Term Γ A),
      Nonempty (HOL.ProofSyntax Const [] (.eq (term ground left) (term ground right))) →
        BetaConv left right) := by
  intro reflects
  exact eta_not_betaConvertible (.symm _ _ (reflects _ _ ⟨etaProof ground⟩))

abbrev NoConstant : HOL.Ty Unit → Type := fun _ => Empty

def first : Term [.atom, .atom] .atom := .var .zero
def second : Term [.atom, .atom] .atom := .var (.succ .zero)
def redex : Term [.atom, .atom] .atom := .app (.lam (.var .zero)) first

/-- Different intrinsic application types survive the HOL boundary even when
the unannotated tower erasures coincide. -/
theorem hol_retains_erased_types :
    term (Const := NoConstant) () ErasureBoundary.discardAtomicIdentity ≠
      term () ErasureBoundary.discardFunctionIdentity :=
  fun equal => ErasureBoundary.discardIdentities_ne (term_injective () equal)

def verdicts : List (String × Bool) :=
  let hol : {Γ : List Ty} → {A : Ty} → Term Γ A →
      HOL.Term NoConstant (context () Γ) (type () A) := fun t => term () t
  let claim := Mettapedia.GSLT.LanguageDef.KernelAuthority.ConversionClaim.mk
    (HOL.Term.eq (hol redex) (hol first)) (HOL.Term.eq (hol first) (hol first))
  let wrong := Mettapedia.GSLT.LanguageDef.KernelAuthority.ConversionClaim.mk
    (HOL.Term.eq (hol redex) (hol first)) (HOL.Term.eq (hol second) (hol first))
  [ ("simple beta decides", decideConversion redex first),
    ("simple wrong variable refuses", !(decideConversion redex second)),
    ("simple beta symmetry", decideConversion first redex),
    ("simple eta remains outside beta", !(decideConversion etaVariable etaExpansion)),
    ("typed HOL retains erased application types", decide
      (term (Const := NoConstant) () ErasureBoundary.discardAtomicIdentity ≠
        term () ErasureBoundary.discardFunctionIdentity)),
    ("raw tower erasure collision retained", decide
      (TowerDTT.eraseTerm ErasureBoundary.discardAtomicIdentity =
        TowerDTT.eraseTerm ErasureBoundary.discardFunctionIdentity)),
    ("HOL explicit beta in equality", HOL.ConversionTiers.explicitConversion.check claim
      ([[.left]], [])),
    ("HOL wrong redex position refuses", !(HOL.ConversionTiers.explicitConversion.check claim
      ([[.body]], []))),
    ("HOL wrong equality endpoint refuses", !(HOL.ConversionTiers.explicitConversion.check wrong
      ([[.left]], []))),
    ("HOL fuelled beta in equality", HOL.ConversionTiers.fuelledConversion.check claim (1, 0)),
    ("HOL insufficient fuel refuses", !(HOL.ConversionTiers.fuelledConversion.check claim (0, 0))),
    ("HOL eta is not a beta article", !(HOL.ConversionTiers.explicitConversion.check
      ⟨.eq (hol etaVariable) (hol etaVariable), .eq (hol etaExpansion) (hol etaVariable)⟩ ([], []))) ]

end Controls

#print axioms substitute_term
#print axioms holJoinable_iff_betaConv
#print axioms holJoinable_iff_towerConv
#print axioms decideConversion_iff_holJoinable
#print axioms equality_proof_of_conversion
#print axioms Controls.hol_equality_does_not_reflect_conversion

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLComparison
