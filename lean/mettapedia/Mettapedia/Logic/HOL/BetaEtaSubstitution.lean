import Mettapedia.Logic.HOL.EtaNormalization

/-!
# Contextual transport of typed beta/eta conversion

The equivalence closure of typed beta/eta steps is stable under syntax
constructors, renaming, and simultaneous substitution. Pointwise convertible
substitutions remain convertible when inserted into an arbitrary typed term.
No semantic model, normalization strategy, or declaration policy is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BetaEtaSubstitution

open EtaConversion
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma delta : Ctx Base} {type domain result : Ty Base}

theorem beta (body : Term Const (domain :: gamma) result)
    (argument : Term Const gamma domain) :
    BetaEtaConv (.app (.lam body) argument) (instantiate argument body) :=
  .rel _ _ (.inl ⟨.beta body argument⟩)

theorem apply_weakened_abstraction (body : Term Const (domain :: gamma) result) :
    BetaEtaConv (.app (weaken (.lam body)) (.var .vz)) body := by
  change BetaEtaConv
    (.app (.lam (HOL.rename (Rename.lift Rename.weaken) body)) (.var .vz)) body
  have contracted := beta (rename (Rename.lift Rename.weaken) body) (.var .vz)
  simpa only [ContextualTrinity.instantiate_vz_rename_lift_weaken] using contracted

theorem map {other : Ctx Base} {output : Ty Base}
    (make : Term Const gamma type → Term Const other output)
    (move : ∀ {source target}, BetaEtaStep source target → BetaEtaStep (make source) (make target))
    {source target : Term Const gamma type} (converted : BetaEtaConv source target) :
    BetaEtaConv (make source) (make target) := by
  induction converted with
  | rel _ _ step => exact .rel _ _ (move step)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem congr {other : Ctx Base} {output : Ty Base}
    (make : Term Const gamma type → Term Const other output)
    (beta : ∀ {source target}, BetaNormalization.Reduces source target →
      BetaNormalization.Reduces (make source) (make target))
    (eta : ∀ {source target}, EtaStep source target → EtaStep (make source) (make target))
    {source target : Term Const gamma type} (converted : BetaEtaConv source target) :
    BetaEtaConv (make source) (make target) :=
  map make (fun step => step.elim (fun step => Or.inl (beta step))
    (fun step => Or.inr (eta step))) converted

theorem congr₂ {first second output : Ty Base}
    (make : Term Const gamma first → Term Const gamma second → Term Const gamma output)
    (betaFirst : ∀ {source target} right, BetaNormalization.Reduces source target →
      BetaNormalization.Reduces (make source right) (make target right))
    (betaSecond : ∀ left {source target}, BetaNormalization.Reduces source target →
      BetaNormalization.Reduces (make left source) (make left target))
    (etaFirst : ∀ {source target} right, EtaStep source target →
      EtaStep (make source right) (make target right))
    (etaSecond : ∀ left {source target}, EtaStep source target →
      EtaStep (make left source) (make left target))
    {left left' : Term Const gamma first} {right right' : Term Const gamma second}
    (one : BetaEtaConv left left') (two : BetaEtaConv right right') :
    BetaEtaConv (make left right) (make left' right') :=
  .trans _ _ _
    (congr (fun term => make term right) (betaFirst right) (etaFirst right) one)
    (congr (make left') (betaSecond left') (etaSecond left') two)

theorem app_congr {left left' : Term Const gamma (domain ⇒ result)}
    {right right' : Term Const gamma domain}
    (one : BetaEtaConv left left') (two : BetaEtaConv right right') :
    BetaEtaConv (.app left right) (.app left' right') :=
  congr₂ Term.app (fun {_ _} _ ⟨step⟩ => ⟨.appFun _ step⟩)
    (fun _ {_ _} ⟨step⟩ => ⟨.appArg _ step⟩)
    (fun {_ _} _ step => .appFun _ step) (fun _ {_ _} step => .appArg _ step) one two

theorem and_congr {left left' right right' : Formula Const gamma}
    (one : BetaEtaConv left left') (two : BetaEtaConv right right') :
    BetaEtaConv (.and left right) (.and left' right') :=
  congr₂ Term.and (fun {_ _} _ ⟨step⟩ => ⟨.andLeft _ step⟩)
    (fun _ {_ _} ⟨step⟩ => ⟨.andRight _ step⟩)
    (fun {_ _} _ step => .andLeft _ step) (fun _ {_ _} step => .andRight _ step) one two

theorem or_congr {left left' right right' : Formula Const gamma}
    (one : BetaEtaConv left left') (two : BetaEtaConv right right') :
    BetaEtaConv (.or left right) (.or left' right') :=
  congr₂ Term.or (fun {_ _} _ ⟨step⟩ => ⟨.orLeft _ step⟩)
    (fun _ {_ _} ⟨step⟩ => ⟨.orRight _ step⟩)
    (fun {_ _} _ step => .orLeft _ step) (fun _ {_ _} step => .orRight _ step) one two

theorem imp_congr {left left' right right' : Formula Const gamma}
    (one : BetaEtaConv left left') (two : BetaEtaConv right right') :
    BetaEtaConv (.imp left right) (.imp left' right') :=
  congr₂ Term.imp (fun {_ _} _ ⟨step⟩ => ⟨.impLeft _ step⟩)
    (fun _ {_ _} ⟨step⟩ => ⟨.impRight _ step⟩)
    (fun {_ _} _ step => .impLeft _ step) (fun _ {_ _} step => .impRight _ step) one two

theorem eq_congr {left left' right right' : Term Const gamma type}
    (one : BetaEtaConv left left') (two : BetaEtaConv right right') :
    BetaEtaConv (.eq left right) (.eq left' right') :=
  congr₂ Term.eq (fun {_ _} _ ⟨step⟩ => ⟨.eqLeft _ step⟩)
    (fun _ {_ _} ⟨step⟩ => ⟨.eqRight _ step⟩)
    (fun {_ _} _ step => .eqLeft _ step) (fun _ {_ _} step => .eqRight _ step) one two

theorem lam_congr {source target : Term Const (domain :: gamma) result}
    (converted : BetaEtaConv source target) :
    BetaEtaConv (.lam source) (.lam target) :=
  congr Term.lam (fun ⟨step⟩ => ⟨.lam step⟩) (fun step => .lam step) converted

theorem not_congr {source target : Formula Const gamma}
    (converted : BetaEtaConv source target) :
    BetaEtaConv (.not source) (.not target) :=
  congr Term.not (fun ⟨step⟩ => ⟨.not step⟩) (fun step => .not step) converted

theorem all_congr {source target : Formula Const (domain :: gamma)}
    (converted : BetaEtaConv source target) :
    BetaEtaConv (.all source) (.all target) :=
  congr Term.all (fun ⟨step⟩ => ⟨.all step⟩) (fun step => .all step) converted

theorem ex_congr {source target : Formula Const (domain :: gamma)}
    (converted : BetaEtaConv source target) :
    BetaEtaConv (.ex source) (.ex target) :=
  congr Term.ex (fun ⟨step⟩ => ⟨.ex step⟩) (fun step => .ex step) converted

theorem rename (rho : Rename Base gamma delta) {source target : Term Const gamma type}
    (converted : BetaEtaConv source target) :
    BetaEtaConv (HOL.rename rho source) (HOL.rename rho target) :=
  congr (HOL.rename rho) (BetaNormalization.reduces_rename rho)
    (EtaNormalization.rename_step rho) converted

theorem subst (theta : Subst Const gamma delta) {source target : Term Const gamma type}
    (converted : BetaEtaConv source target) :
    BetaEtaConv (HOL.subst theta source) (HOL.subst theta target) :=
  congr (HOL.subst theta) (BetaNormalization.reduces_subst theta)
    (EtaNormalization.subst_step theta) converted

/-- Pointwise conversion of substitution entries is preserved by every
typed term constructor, including the lifted substitutions below binders. -/
theorem subst_pointwise (term : Term Const gamma type)
    {theta other : Subst Const gamma delta}
    (pointwise : ∀ {type} (index : Var gamma type), BetaEtaConv (theta index) (other index)) :
    BetaEtaConv (HOL.subst theta term) (HOL.subst other term) := by
  have lifted {gamma delta : Ctx Base} {bound : Ty Base}
      {theta other : Subst Const gamma delta}
      (pointwise : ∀ {type} (index : Var gamma type), BetaEtaConv (theta index) (other index)) :
      ∀ {type} (index : Var (bound :: gamma) type),
        BetaEtaConv (Subst.lift theta index) (Subst.lift other index) := by
    intro type index
    cases index with
    | vz => exact .refl _
    | vs index => exact rename Rename.weaken (pointwise index)
  induction term generalizing delta with
  | var index => exact pointwise index
  | const | top | bot => exact .refl _
  | app _ _ ihf iha => exact app_congr (ihf pointwise) (iha pointwise)
  | and _ _ ihl ihr => exact and_congr (ihl pointwise) (ihr pointwise)
  | or _ _ ihl ihr => exact or_congr (ihl pointwise) (ihr pointwise)
  | imp _ _ ihl ihr => exact imp_congr (ihl pointwise) (ihr pointwise)
  | eq _ _ ihl ihr => exact eq_congr (ihl pointwise) (ihr pointwise)
  | not _ ih => exact not_congr (ih pointwise)
  | lam _ ih => exact lam_congr (ih (lifted pointwise))
  | all _ ih => exact all_congr (ih (lifted pointwise))
  | ex _ ih => exact ex_congr (ih (lifted pointwise))

theorem instantiate_argument (body : Term Const (domain :: gamma) result)
    {first second : Term Const gamma domain} (converted : BetaEtaConv first second) :
    BetaEtaConv (instantiate first body) (instantiate second body) := by
  apply subst_pointwise body
  intro type index
  cases index with
  | vz => exact converted
  | vs => exact .refl _

theorem instantiate_congr {body otherBody : Term Const (domain :: gamma) result}
    {argument otherArgument : Term Const gamma domain}
    (bodies : BetaEtaConv body otherBody) (arguments : BetaEtaConv argument otherArgument) :
    BetaEtaConv (instantiate argument body) (instantiate otherArgument otherBody) :=
  .trans _ _ _ (subst (Subst.single argument) bodies) (instantiate_argument otherBody arguments)

#print axioms map
#print axioms congr₂
#print axioms rename
#print axioms subst
#print axioms subst_pointwise
#print axioms instantiate_congr

end Mettapedia.Logic.HOL.BetaEtaSubstitution
