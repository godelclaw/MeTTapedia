import Mettapedia.Logic.HOL.ProofSyntaxModuloConservativity
import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.Syntax.DecidableEq

/-!
# Elaborating licensed conversion into retained HOL proofs

An equation used by a conversion engine needs its own justification. Here a
finite equation presentation is licensed by retained HOL equality proofs at
the equations' original telescopes. Every substitution instance, compatible
step, conversion article and logical proof modulo those equations then has
ordinary HOL proof evidence at its original sequent.

The existing modulo calculus stores proposition-valued conversion. Its
translation therefore establishes existence of retained evidence, not a
chosen replay history or an executable serialization. Checked conversion
recipes supply the constructive replay boundary separately.

The result applies to the named implication/universal fragment and arbitrary
HOL base sorts and constants. It does not assert conservativity of a larger
dependent theory, permit arbitrary equations, or equate checking costs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace DefiningEquation

private def code (equation : DefiningEquation Const) :
    Σ Γ : Ctx Base, Σ τ : Ty Base, Term Const Γ τ × Term Const Γ τ :=
  ⟨equation.context, equation.type, equation.left, equation.right⟩

private def decode (coded : Σ Γ : Ctx Base, Σ τ : Ty Base, Term Const Γ τ × Term Const Γ τ) :
    DefiningEquation Const :=
  ⟨coded.1, coded.2.1, coded.2.2.1, coded.2.2.2⟩

private theorem decode_code (equation : DefiningEquation Const) : decode (code equation) = equation :=
  by cases equation; rfl

/-- Equation identity checks the telescope and type as well as both sides.
It is syntactic identity, not equality modulo the equations being admitted. -/
instance [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] :
    DecidableEq (DefiningEquation Const) := fun first second =>
  decidable_of_iff (code first = code second)
    ⟨fun equal => (decode_code first).symm.trans ((congrArg decode equal).trans (decode_code second)),
     congrArg code⟩

end DefiningEquation

/-- Retained, assumption-free equality evidence for each equation at its
original pattern telescope. This is proof data, not a Boolean permission bit
or the assertion that a semantic model happens to satisfy the equation. -/
structure EquationProofs (equations : List (DefiningEquation Const)) where
  proof : (equation : DefiningEquation Const) → equation ∈ equations →
    ProofSyntax Const [] (.eq equation.left equation.right)

namespace EquationProofs

variable {equations : List (DefiningEquation Const)}

/-- Instantiation uses the maintained capture-safe proof substitution. Its
empty assumption list is then weakened into the caller's exact list. -/
def instantiate (licensed : EquationProofs equations)
    (equation : DefiningEquation Const) (listed : equation ∈ equations)
    {Γ : Ctx Base} (substitution : Subst Const equation.context Γ)
    (assumptions : List (Formula Const Γ)) :
    ProofSyntax Const assumptions
      (.eq (subst substitution equation.left) (subst substitution equation.right)) := by
  let instantiated : ProofSyntax Const []
      (.eq (subst substitution equation.left) (subst substitution equation.right)) :=
    ProofSyntax.subst substitution (licensed.proof equation listed)
  exact ProofSyntax.mono (Δ := []) (Δ' := assumptions)
    { index := fun i => Fin.elim0 i
      get_eq := fun i => Fin.elim0 i } instantiated

/-- The union retains the actual evidence supplied by each package. Repeated
equations select the left receipt; no proof identity is asserted. -/
def append {other : List (DefiningEquation Const)}
    [DecidableEq (DefiningEquation Const)]
    (first : EquationProofs equations) (second : EquationProofs other) :
    EquationProofs (equations ++ other) where
  proof equation listed := by
    have occurs := List.mem_append.mp listed
    by_cases left : equation ∈ equations
    · exact first.proof equation left
    · exact second.proof equation (occurs.resolve_left left)

end EquationProofs

/-- Every licensed source step has retained equational evidence. Since the
source step is proposition-valued, this theorem returns `Nonempty` rather
than pretending to recover the submitted step history. -/
theorem SourceStep.hasHOLProof {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations)
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : SourceStep equations source target) :
    ∀ assumptions : List (Formula Const Γ),
      Nonempty (ProofSyntax Const assumptions (.eq source target)) := by
  induction step with
  | beta body argument => intro assumptions; exact ⟨.beta argument body⟩
  | delta equation listed substitution _ =>
      intro assumptions
      exact ⟨licensed.instantiate equation listed substitution assumptions⟩
  | appFun argument _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih assumptions
      exact ⟨.eqApp argument proof⟩
  | appArg function _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih assumptions
      exact ⟨.eqAppArg function proof⟩
  | lam _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih (weakenHyps assumptions)
      exact ⟨.eqLam proof⟩
  | @impLeft Γ left left' right _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih assumptions
      exact ⟨ContextualTrinity.castEq
        (congrArg (Term.imp left) (instantiate_weaken left right))
        (congrArg (Term.imp left') (instantiate_weaken left' right))
        (ContextualTrinity.holeCongr (.imp (.var .vz) (weaken right)) proof)⟩
  | @impRight Γ left right right' _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih assumptions
      exact ⟨ContextualTrinity.castEq
        (congrArg (fun hole => Term.imp hole right) (instantiate_weaken right left))
        (congrArg (fun hole => Term.imp hole right') (instantiate_weaken right' left))
        (ContextualTrinity.holeCongr (.imp (weaken left) (.var .vz)) proof)⟩
  | @eqLeft Γ τ left left' right _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih assumptions
      exact ⟨ContextualTrinity.castEq
        (congrArg (Term.eq left) (instantiate_weaken left right))
        (congrArg (Term.eq left') (instantiate_weaken left' right))
        (ContextualTrinity.holeCongr (.eq (.var .vz) (weaken right)) proof)⟩
  | @eqRight Γ τ left right right' _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih assumptions
      exact ⟨ContextualTrinity.castEq
        (congrArg (fun hole => Term.eq hole right) (instantiate_weaken right left))
        (congrArg (fun hole => Term.eq hole right') (instantiate_weaken right' left))
        (ContextualTrinity.holeCongr (.eq (weaken left) (.var .vz)) proof)⟩
  | all _ ih =>
      intro assumptions
      obtain ⟨proof⟩ := ih (weakenHyps assumptions)
      exact ⟨ContextualTrinity.allCongr proof⟩

/-- Equality evidence composes through the actual source conversion relation. -/
theorem CoreConversion.hasHOLProof {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations)
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (conversion : CoreConversion equations source target)
    (assumptions : List (Formula Const Γ)) :
    Nonempty (ProofSyntax Const assumptions (.eq source target)) := by
  induction conversion with
  | rel _ _ step => exact step.2.2.hasHOLProof licensed assumptions
  | refl term => exact ⟨.eqRefl term⟩
  | symm _ _ _ ih => obtain ⟨proof⟩ := ih; exact ⟨.eqSymm proof⟩
  | trans _ _ _ _ _ first second =>
      obtain ⟨first⟩ := first
      obtain ⟨second⟩ := second
      exact ⟨.eqTrans first second⟩

/-- A licensed conversion never silently casts a logical judgment: it
elaborates to propositional equality elimination in ordinary HOL. -/
theorem ProofSyntaxModulo.hasHOLProof {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations)
    {Γ : Ctx Base} {assumptions : List (Formula Const Γ)} {claim : Formula Const Γ}
    (proof : ProofSyntaxModulo equations assumptions claim) :
    Nonempty (ProofSyntax Const assumptions claim) := by
  induction proof with
  | hyp occurrence => exact ⟨.hyp occurrence⟩
  | impI _ ih => obtain ⟨proof⟩ := ih; exact ⟨.impI proof⟩
  | impE _ _ first second =>
      obtain ⟨first⟩ := first
      obtain ⟨second⟩ := second
      exact ⟨.impE first second⟩
  | allI _ ih => obtain ⟨proof⟩ := ih; exact ⟨.allI proof⟩
  | allE term _ ih => obtain ⟨proof⟩ := ih; exact ⟨.allE term proof⟩
  | convert article _ ih =>
      obtain ⟨equality⟩ := article.hasHOLProof licensed _
      obtain ⟨proof⟩ := ih
      exact ⟨.impE (.eqPropEL equality) proof⟩

namespace ConversionElaborationControls

/-- Eta is a schematic equation over an arbitrary arrow type, rather than a
global equality policy imposed on all profiles. -/
def etaEquation (σ τ : Ty Base) : DefiningEquation Const where
  context := [σ ⇒ τ]
  type := σ ⇒ τ
  left := .lam (.app (.var (.vs .vz)) (.var .vz))
  right := .var .vz

/-- The ordinary eta rule supplies an actual receipt at the schema telescope. -/
def etaProofs (σ τ : Ty Base) : EquationProofs [etaEquation (Const := Const) σ τ] where
  proof equation listed := by
    have same := List.mem_singleton.mp listed
    subst equation
    exact .eta (.var .vz)

/-- A source article can use eta as computation, while the target elaborates
it as an ordinary equality proof. -/
theorem etaArticle (σ τ : Ty Base) :
    CoreConversion [etaEquation (Const := Const) σ τ]
      (etaEquation σ τ).left (etaEquation σ τ).right := by
  have step := SourceStep.delta (equations := [etaEquation (Const := Const) σ τ])
    (etaEquation σ τ) (by simp) Subst.id (fun index => rfl)
  simp only [subst_id] at step
  exact .rel _ _ ⟨rfl, rfl, step⟩

def etaLogicalProof (σ τ : Ty Base) :
    ProofSyntaxModulo [etaEquation (Const := Const) σ τ]
      [.eq (.var .vz) (.var .vz)]
      (.eq (etaEquation σ τ).left (etaEquation σ τ).right) :=
  .convert (CoreConversion.eqLeft rfl (.symm _ _ (etaArticle σ τ))) (.hyp ⟨0, by simp⟩)

/-- The logical conversion is justified by retained ordinary HOL evidence at
the original ordered assumption list. -/
theorem etaLogical_hasHOLProof (σ τ : Ty Base) :
    Nonempty (ProofSyntax Const [.eq (.var .vz) (.var .vz)]
      (.eq (etaEquation σ τ).left (etaEquation σ τ).right)) :=
  (etaLogicalProof σ τ).hasHOLProof (etaProofs σ τ)

/-- A cyclic declaration that produces Curry's paradox cannot acquire the
retained equality receipts required by the elaboration interface. -/
theorem no_curry_equationProofs :
    ¬ Nonempty (EquationProofs [DefinitionControls.curryEquation]) := by
  rintro ⟨licensed⟩
  obtain ⟨proof⟩ := DefinitionControls.curryFalsity.hasHOLProof licensed
  let model := DefinitionControls.modelWith True
  have extensional : model.FunctionsRespectEqv :=
    model.functionsRespectEqv_of_fullDomains (fun _ _ => trivial)
  have holds := Soundness.extDerivation_sound proof.erase
    (M := model) (ρ := fun i => nomatch i) extensional
    (fun i => nomatch i) (fun _ listed => absurd listed List.not_mem_nil)
  exact holds (ULift.up False) trivial

end ConversionElaborationControls

end Mettapedia.Logic.HOL
