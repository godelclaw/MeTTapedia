import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLComparison
import Mettapedia.TypeTheory.BubbleConversion
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Local beta and beta-eta bubbles with HOL proof elaboration

The states are the existing intrinsically typed simple terms, indexed by
context and type. Beta steps retain their HOL operational evidence; an eta
step additionally requires the eta policy. Compatible steps and the existing
free conversion trees retain the path rather than just its endpoints.

Every path elaborates to an ordinary retained HOL equality proof. The
beta-only bubble presents exactly the sealed tower conversion on the simple
image. The eta-enabled bubble is strictly larger, although its extra equation
already has a HOL proof. This is a conversion-policy comparison, not a new
raw-certificate checker, a normalization proof for extensions by arbitrary
equations, or conservativity of all dependent proofs with simple conclusions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLConversionBubble

open IntrinsicSTT HOLComparison
open Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Compatible local computation, with eta as a separate policy. -/
inductive Step (ground : Base) (eta : Bool) :
    {Γ : List Ty} → {A : Ty} → Term Γ A → Term Γ A → Type (max u v) where
  | beta {Γ A} {left right : Term Γ A} :
      HOL.ContextualTrinity.BetaStep (term (Const := Const) ground left) (term ground right) →
        Step ground eta left right
  | eta {Γ A B} (enabled : eta = true) (f : Term Γ (.arr A B)) :
      Step ground eta (.lam (.app (f.rename weakening) (.var .zero))) f
  | lam {Γ A B} {left right : Term (A :: Γ) B} :
      Step ground eta left right → Step ground eta (.lam left) (.lam right)
  | appFun {Γ A B} {left right : Term Γ (.arr A B)} (argument : Term Γ A) :
      Step ground eta left right → Step ground eta (.app left argument) (.app right argument)
  | appArg {Γ A B} (f : Term Γ (.arr A B)) {left right : Term Γ A} :
      Step ground eta left right → Step ground eta (.app f left) (.app f right)

variable (ground : Base)

/-- An instance of the common judgment-indexed bubble interface. -/
def bubbles : BubbleConversion.Bubbles (List Ty × Ty) where
  State index := Term index.1 index.2
  Bubble := Bool
  Step eta := Step (Const := Const) ground eta

/-- A local step elaborates using beta, eta, and equality congruence.
The supplied assumption list is retained unchanged. -/
def Step.proof {eta : Bool} {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (step : Step (Const := Const) ground eta left right)
    (assumptions : List (HOL.Formula Const (context ground Γ))) :
    HOL.ProofSyntax Const assumptions (.eq (term ground left) (term ground right)) :=
  match step with
  | .beta reduction => reduction.proof assumptions
  | .eta _ f => by
      change HOL.ProofSyntax Const assumptions
        (.eq (.lam (.app (term ground (f.rename weakening)) (.var .vz))) (term ground f))
      rw [← weaken_term]
      exact .eta _
  | .lam inner => .eqLam (Step.proof inner (HOL.weakenHyps assumptions))
  | .appFun argument inner => .eqApp (term ground argument) (Step.proof inner assumptions)
  | .appArg f inner => .eqAppArg (term ground f) (Step.proof inner assumptions)

/-- The target equality is the actual HOL proof family, not semantic truth. -/
def holEquality : (bubbles (Const := Const) ground).GlobalEquality where
  Eq left right := HOL.ProofSyntax Const [] (.eq (term ground left) (term ground right))
  refl _ := .eqRefl _
  symm := .eqSymm
  trans := .eqTrans

/-- The common bubble fold produces a retained proof with the same endpoints. -/
def elaborate {eta : Bool} {index : List Ty × Ty}
    {left right : (bubbles (Const := Const) ground).State index}
    (path : (bubbles (Const := Const) ground).Conv eta left right) :
    HOL.ProofSyntax Const [] (.eq (term ground left) (term ground right)) :=
  (bubbles ground).sound (holEquality ground) (fun step => Step.proof ground step []) path

theorem Step.betaOnly {Γ A} {left right : Term Γ A}
    (step : Step (Const := Const) ground false left right) : BetaConv left right := by
  induction step with
  | beta beta =>
      exact (holJoinable_iff_betaConv ground _ _).1
        ⟨_, ⟨.step beta (.done _)⟩, ⟨.done _⟩⟩
  | eta enabled _ => cases enabled
  | lam _ ih => exact ih.lam
  | appFun _ _ ih => exact ih.app (.refl _)
  | appArg _ _ ih => exact BetaConv.app (.refl _) ih

private def betaEquality : (bubbles (Const := Const) ground).GlobalEquality where
  Eq left right := PLift (BetaConv left right)
  refl _ := ⟨.refl _⟩
  symm h := ⟨.symm _ _ h.down⟩
  trans h k := ⟨.trans _ _ _ h.down k.down⟩

/-- The beta policy is exactly the existing simple conversion judgment. -/
theorem beta_path_iff {Γ A} (left right : Term Γ A) :
    Nonempty ((bubbles (Const := Const) ground).Conv false (index := (Γ, A)) left right) ↔
      BetaConv left right := by
  constructor
  · rintro ⟨path⟩
    exact ((bubbles ground).sound (betaEquality ground)
      (fun step => ⟨step.betaOnly⟩) path).down
  · intro conversion
    induction conversion with
    | rel _ _ step =>
        obtain ⟨beta⟩ := betaStep_toHOL (Const := Const) ground step
        exact ⟨.step (.beta beta)⟩
    | refl t => exact ⟨JudgmentalEquality.ConversionEvidence.refl (index := (Γ, A))
        (computation := FreeConversion.computation (bubbles ground).State
          ((bubbles ground).Step false)) t⟩
    | symm _ _ _ ih => obtain ⟨path⟩ := ih; exact ⟨.symm path⟩
    | trans _ _ _ _ _ first second =>
        obtain ⟨first⟩ := first
        obtain ⟨second⟩ := second
        exact ⟨.trans first second⟩

theorem beta_path_iff_tower {Γ A} (left right : Term Γ A) :
    Nonempty ((bubbles (Const := Const) ground).Conv false (index := (Γ, A)) left right) ↔
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Conv
        Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.HeadEq
        (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right) :=
  (beta_path_iff ground left right).trans (ConversionDecision.towerConv_iff_betaConv left right).symm

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

abbrev theory (eta : Bool) (Γ : List Ty) (A : Ty) : GSLT :=
  conversionTheory (fun left right : Term Γ A => Nonempty (Step (Const := Const) ground eta left right))

def nativeType {Γ A} (eta : Bool) (target : Term Γ A) :
    GSLTNativeType (theory (Const := Const) ground eta Γ A) :=
  conversionNativeType (fun left right => Nonempty (Step ground eta left right)) target

/-- The OSLF observation and the retained conversion have the same support;
the predicate does not select or recover a particular proof history. -/
theorem satisfies_iff_path {Γ A} (eta : Bool) (left right : Term Γ A) :
    (gsltOSLF (theory (Const := Const) ground eta Γ A)).satisfies (S := ()) left
      (nativeType ground eta right).pred ↔
    Nonempty ((bubbles (Const := Const) ground).Conv eta (index := (Γ, A)) left right) := by
  exact (satisfies_conversionNativeType_iff
    (fun left right => Nonempty (Step (Const := Const) ground eta left right)) left right).trans
      (JudgmentalEquality.ConversionEvidence.support_iff_nonempty_evidence
        (computation := FreeConversion.computation (bubbles ground).State
          ((bubbles ground).Step eta)) (index := (Γ, A)))

/-- On the admitted beta fragment the native predicate has an exact total
decision procedure, the existing intrinsic normal-form comparison. -/
theorem beta_satisfies_iff_decides {Γ A} (left right : Term Γ A) :
    (gsltOSLF (theory (Const := Const) ground false Γ A)).satisfies (S := ()) left
      (nativeType ground false right).pred ↔
    ConversionDecision.decideConversion left right = true :=
  ((satisfies_iff_path ground false left right).trans (beta_path_iff ground left right)).trans
    (ConversionDecision.decideConversion_correct left right).symm

namespace Controls

open ConversionDecision

def eta_path : (bubbles (Const := Const) ground).Conv true
    (index := ([.arr .atom .atom], .arr .atom .atom)) etaExpansion etaVariable :=
  .step (.eta rfl etaVariable)

theorem no_beta_eta_path :
    ¬ Nonempty ((bubbles (Const := Const) ground).Conv false
      (index := ([.arr .atom .atom], .arr .atom .atom)) etaExpansion etaVariable) :=
  fun path => eta_not_betaConvertible (.symm _ _ ((beta_path_iff ground _ _).1 path))

/-- The two conversion policies are different, with a concrete shared state pair. -/
theorem eta_strictly_adds_conversion :
    Nonempty ((bubbles (Const := Const) ground).Conv true
      (index := ([.arr .atom .atom], .arr .atom .atom)) etaExpansion etaVariable) ∧
    ¬ Nonempty ((bubbles (Const := Const) ground).Conv false
      (index := ([.arr .atom .atom], .arr .atom .atom)) etaExpansion etaVariable) :=
  ⟨⟨eta_path ground⟩, no_beta_eta_path ground⟩

theorem eta_observation_depends_on_policy :
    (gsltOSLF (theory (Const := Const) ground true [.arr .atom .atom] (.arr .atom .atom))).satisfies
      (S := ()) etaExpansion (nativeType ground true etaVariable).pred ∧
    ¬ (gsltOSLF (theory (Const := Const) ground false [.arr .atom .atom] (.arr .atom .atom))).satisfies
      (S := ()) etaExpansion (nativeType ground false etaVariable).pred :=
  ⟨(satisfies_iff_path ground true _ _).2 ⟨eta_path ground⟩,
    fun observed => no_beta_eta_path ground ((satisfies_iff_path ground false _ _).1 observed)⟩

end Controls

#print axioms elaborate
#print axioms beta_path_iff_tower
#print axioms beta_satisfies_iff_decides
#print axioms Controls.eta_strictly_adds_conversion

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLConversionBubble
