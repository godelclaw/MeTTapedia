import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLConversionBubble
import Mettapedia.TypeTheory.BubbleElaboration
import Mettapedia.Languages.HOLLight.RetainedMM0Compilation

/-!
# Beta and beta-eta bubbles of simple types, elaborated to HOL Light and MM0

The simply typed terms over one atomic HOL sort carry two conversion bubbles,
beta and beta-eta (`HOLConversionBubble`). Their conversion trees elaborate to
retained HOL equality proofs, and the all-constructor HOL compiler turns those
proofs into primitive HOL Light proof graphs and, through the first-order
presentation of the HOL Light rules, into MM0 saved-proof certificates. This
module composes these existing edges and states what the composite delivers
for every conversion tree.

* **Accepted at both roots** (`tierZero_accepted`, `mm0_accepted`). The HOL
  Light checker of the eta-axiom policy accepts the compiled graph, and the
  MM0 kernel with saved proofs accepts the compiled certificate of the same
  rendered sequent.
* **The exact equation** (`tierZero_sequent`). The certified sequent has no
  hypotheses and its conclusion is the HOL equation between the two simply
  typed terms; the connective expansion of the compiler leaves these
  connective-free equations unchanged (`term_isCore`).
* **Refusal** (`tierZero_refuses_changed_conclusion`). The same graph does not
  certify any theorem with another conclusion.
* **Natural in the bubble** (`elaborate_widen`, `tierZero_widen`, `mm0_widen`).
  Widening the beta bubble to the beta-eta bubble does not change the retained
  proof, the HOL Light certificate or the MM0 certificate of any beta tree.
* **The wider bubble certifies more**
  (`Controls.eta_certified_only_by_wider_bubble`). The eta pair has a one-step
  beta-eta tree, whose certificate HOL Light accepts with the eta equation as
  conclusion, and no beta tree at all.

The eta axiom is admitted in the HOL Light policy for every tree, as in the
compiler; beta trees do not need it. The compilation is the existing one and
is not a decision procedure for either bubble.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLLightBubbleElaboration

open IntrinsicSTT HOLComparison HOLConversionBubble
open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory (AtomicTy Symbol etaAxiomPolicy Theorem)
open Mettapedia.Languages.OpenTheory.ReverseTranslation (Naming reverseCanonical)
open Mettapedia.Languages.HOLLight
open Mettapedia.TypeTheory.BubbleElaboration

universe u v

/-! ## Beta steps are beta-eta steps -/

section Widening

variable {Base : Type u} {Const : HOL.Ty Base → Type v} (ground : Base)

/-- Every step of the beta bubble is a step of the beta-eta bubble. -/
def betaToBetaEta : {Γ : List Ty} → {A : Ty} → {left right : Term Γ A} →
    Step (Const := Const) ground false left right → Step (Const := Const) ground true left right
  | _, _, _, _, .beta reduction => .beta reduction
  | _, _, _, _, .eta enabled _ => absurd enabled Bool.false_ne_true
  | _, _, _, _, .lam inner => .lam (betaToBetaEta inner)
  | _, _, _, _, .appFun argument inner => .appFun argument (betaToBetaEta inner)
  | _, _, _, _, .appArg function inner => .appArg function (betaToBetaEta inner)

/-- The two bubbles justify a beta step by the same retained proof. -/
theorem proof_betaToBetaEta : ∀ {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (step : Step (Const := Const) ground false left right)
    (assumptions : List (HOL.Formula Const (context ground Γ))),
    Step.proof ground (betaToBetaEta ground step) assumptions = Step.proof ground step assumptions
  | _, _, _, _, .beta _, _ => rfl
  | _, _, _, _, .eta enabled _, _ => absurd enabled Bool.false_ne_true
  | _, _, _, _, .lam inner, assumptions =>
      congrArg HOL.ProofSyntax.eqLam (proof_betaToBetaEta inner (HOL.weakenHyps assumptions))
  | _, _, _, _, .appFun argument inner, assumptions =>
      congrArg (HOL.ProofSyntax.eqApp (term ground argument))
        (proof_betaToBetaEta inner assumptions)
  | _, _, _, _, .appArg function inner, assumptions =>
      congrArg (HOL.ProofSyntax.eqAppArg (term ground function))
        (proof_betaToBetaEta inner assumptions)

/-- **Widening the beta bubble does not change the retained proof.** -/
theorem elaborate_widen {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (path : (bubbles (Const := Const) ground).Conv false (index := (Γ, A)) left right) :
    elaborate ground ((bubbles ground).widen (fun step => betaToBetaEta ground step) path) =
      elaborate ground path :=
  sound_widen (bubbles ground) (holEquality ground) (fun step => betaToBetaEta ground step)
    (fun step => Step.proof ground step []) (fun step => Step.proof ground step [])
    (fun step => proof_betaToBetaEta ground step []) path

/-- Widening keeps the number of recorded steps. -/
theorem stepCount_widen_beta {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (path : (bubbles (Const := Const) ground).Conv false (index := (Γ, A)) left right) :
    stepCount ((bubbles ground).widen (fun step => betaToBetaEta ground step) path) =
      stepCount path :=
  stepCount_widen (bubbles ground) (fun step => betaToBetaEta ground step) path

end Widening

/-! ## Connective-free equations are fixed by the compiler's expansion -/

section Expansion

variable {Base : Type u} {Const : HOL.Ty Base → Type v} (ground : Base)

/-- The HOL image of a simply typed term uses only variables, abstraction and
application. -/
theorem term_isCore : ∀ {Γ : List Ty} {A : Ty} (t : Term Γ A),
    HOL.ImpredicativeConnectives.IsCore (term (Const := Const) ground t)
  | _, _, .var _ => trivial
  | _, _, .lam body => term_isCore body
  | _, _, .app function argument => ⟨term_isCore function, term_isCore argument⟩

/-- The expansion of the equation between two simply typed terms is that
equation. -/
theorem expand_equation {Γ : List Ty} {A : Ty} (left right : Term Γ A) :
    HOL.ImpredicativeConnectives.expand
        (HOL.Term.eq (term (Const := Const) ground left) (term ground right)) =
      HOL.Term.eq (term ground left) (term ground right) :=
  HOL.ImpredicativeConnectives.expand_of_isCore _ ⟨term_isCore ground left, term_isCore ground right⟩

end Expansion

/-! ## The composite into HOL Light and MM0 -/

section TierZero

variable (ground : AtomicTy)

/-- The HOL Light certificate of a conversion tree of either bubble: the
retained proof of `HOLConversionBubble.elaborate`, compiled by the
all-constructor HOL compiler under the eta-axiom policy. -/
def tierZero {eta : Bool} {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv eta (index := (Γ, A)) left right) :
    RetainedCompilation.Compiled etaAxiomPolicy names
      (([] : List (HOL.Formula Symbol (context ground Γ))).map
        HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (.eq (term ground left) (term ground right))) :=
  RetainedCompilation.compile etaAxiomPolicy rfl (elaborate ground path) names origin

/-- **The HOL Light checker accepts the certificate of every conversion tree.** -/
theorem tierZero_accepted {eta : Bool} {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv eta (index := (Γ, A)) left right) :
    (ProofSystem.checker etaAxiomPolicy).check (tierZero ground names origin path).proof.result
      (tierZero ground names origin path).proof.certificate = true :=
  RetainedCompilation.compile_accepted etaAxiomPolicy rfl (elaborate ground path) names origin

/-- **The certified sequent is the bare equation**: no hypotheses, and the HOL
equation between the two simply typed terms as conclusion. -/
theorem tierZero_sequent {eta : Bool} {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv eta (index := (Γ, A)) left right) :
    (tierZero ground names origin path).proof.result.sequent.hyp = ∅ ∧
      (tierZero ground names origin path).proof.result.sequent.concl =
        reverseCanonical names (.eq (term ground left) (term ground right)) := by
  obtain ⟨hypotheses, conclusion⟩ :=
    RetainedCompilation.compile_sequent etaAxiomPolicy rfl (elaborate ground path) names origin
  exact ⟨hypotheses, conclusion.trans
    (congrArg (reverseCanonical names) (expand_equation ground left right))⟩

/-- **The certificate certifies no other conclusion.** -/
theorem tierZero_refuses_changed_conclusion {eta : Bool} {Γ : List Ty} {A : Ty}
    {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv eta (index := (Γ, A)) left right) (claim : Theorem)
    (different :
      claim.sequent.concl ≠ reverseCanonical names (.eq (term ground left) (term ground right))) :
    (ProofSystem.checker etaAxiomPolicy).check claim
      (tierZero ground names origin path).proof.certificate = false :=
  RetainedCompilation.compile_refuses_changed_conclusion etaAxiomPolicy rfl (elaborate ground path)
    names origin claim (fun same => different
      (same.trans (congrArg (reverseCanonical names) (expand_equation ground left right))))

/-- **Widening the beta bubble does not change the HOL Light certificate.** -/
theorem tierZero_widen {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv false (index := (Γ, A)) left right) :
    tierZero ground names origin ((bubbles ground).widen (fun step => betaToBetaEta ground step) path) =
      tierZero ground names origin path :=
  congrArg (fun proof => RetainedCompilation.compile etaAxiomPolicy rfl proof names origin)
    (elaborate_widen ground path)

/-- The MM0 saved-proof certificate of a conversion tree of either bubble. -/
def mm0Certificate {eta : Bool} {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv eta (index := (Γ, A)) left right) :
    Mettapedia.Languages.MM0.Translation.CalculusSimulation.SavedCertificate :=
  RetainedMM0Compilation.compile (elaborate ground path) names origin

/-- **The MM0 kernel with saved proofs accepts the certificate of every
conversion tree**, for the rendered sequent with no hypotheses and the
equation as conclusion. -/
theorem mm0_accepted {eta : Bool} {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv eta (index := (Γ, A)) left right) :
    (Mettapedia.Languages.MM0.Translation.CalculusSimulation.savedChecker
        RetainedMM0Compilation.firstOrder).check
      (FirstOrder.renderSequent
        ⟨∅, reverseCanonical names (.eq (term ground left) (term ground right))⟩)
      (mm0Certificate ground names origin path) = true := by
  have accepted := RetainedMM0Compilation.compile_accepted (elaborate ground path) names origin
  rw [expand_equation] at accepted
  exact accepted

/-- **Widening the beta bubble does not change the MM0 certificate.** -/
theorem mm0_widen {Γ : List Ty} {A : Ty} {left right : Term Γ A}
    (names : Naming (context ground Γ)) (origin : ProofExecution.Origin)
    (path : (bubbles (Const := Symbol) ground).Conv false (index := (Γ, A)) left right) :
    mm0Certificate ground names origin
        ((bubbles ground).widen (fun step => betaToBetaEta ground step) path) =
      mm0Certificate ground names origin path :=
  congrArg (fun proof => RetainedMM0Compilation.compile proof names origin)
    (elaborate_widen ground path)

end TierZero

/-! ## Controls -/

namespace Controls

open ConversionDecision

variable (ground : AtomicTy)

/-- The one-step beta-eta tree of the eta pair. -/
abbrev etaTree : (bubbles (Const := Symbol) ground).Conv true
    (index := ([.arr .atom .atom], .arr .atom .atom)) etaExpansion etaVariable :=
  HOLConversionBubble.Controls.eta_path ground

/-- **The wider bubble certifies the eta equation; the narrower has no tree
for it.** The one-step beta-eta tree of the eta pair records one step, its
HOL Light certificate is accepted with the eta equation as conclusion and no
hypotheses, and the beta bubble has no conversion tree for the pair. -/
theorem eta_certified_only_by_wider_bubble
    (names : Naming (context ground [.arr .atom .atom])) (origin : ProofExecution.Origin) :
    stepCount (etaTree ground) = 1 ∧
      (ProofSystem.checker etaAxiomPolicy).check
          (tierZero ground names origin (etaTree ground)).proof.result
          (tierZero ground names origin (etaTree ground)).proof.certificate = true ∧
      (tierZero ground names origin (etaTree ground)).proof.result.sequent.hyp = ∅ ∧
      (tierZero ground names origin (etaTree ground)).proof.result.sequent.concl =
        reverseCanonical names (.eq (term ground etaExpansion) (term ground etaVariable)) ∧
      ¬ Nonempty ((bubbles (Const := Symbol) ground).Conv false
        (index := ([.arr .atom .atom], .arr .atom .atom)) etaExpansion etaVariable) :=
  ⟨stepCount_step _, tierZero_accepted ground names origin (etaTree ground),
    (tierZero_sequent ground names origin (etaTree ground)).1,
    (tierZero_sequent ground names origin (etaTree ground)).2,
    HOLConversionBubble.Controls.no_beta_eta_path ground⟩

/-- A beta redex: the identity applied to a variable. -/
def identityRedex : Term [.atom] .atom := .app (.lam (.var .zero)) (.var .zero)

/-- The redex and its contractum are beta convertible. -/
theorem identityRedex_betaConv : BetaConv identityRedex (.var .zero) :=
  .rel _ _ (.beta (.var .zero) (.var .zero))

/-- **Positive control for the beta bubble.** The redex has a beta tree; its
HOL Light certificate is accepted with the beta equation as conclusion, and
widening the tree to the beta-eta bubble keeps the certificate. -/
theorem identityRedex_certified (names : Naming (context ground [.atom]))
    (origin : ProofExecution.Origin) :
    ∃ path : (bubbles (Const := Symbol) ground).Conv false
        (index := ([.atom], .atom)) identityRedex (.var .zero),
      (ProofSystem.checker etaAxiomPolicy).check (tierZero ground names origin path).proof.result
          (tierZero ground names origin path).proof.certificate = true ∧
        (tierZero ground names origin path).proof.result.sequent.concl =
          reverseCanonical names (.eq (term ground identityRedex) (term ground (.var .zero))) ∧
        tierZero ground names origin
            ((bubbles ground).widen (fun step => betaToBetaEta ground step) path) =
          tierZero ground names origin path := by
  obtain ⟨path⟩ := (beta_path_iff (Const := Symbol) ground identityRedex (.var .zero)).2
    identityRedex_betaConv
  exact ⟨path, tierZero_accepted ground names origin path,
    (tierZero_sequent ground names origin path).2, tierZero_widen ground names origin path⟩

end Controls

/-! ## Axiom audit -/

#print axioms proof_betaToBetaEta
#print axioms elaborate_widen
#print axioms tierZero_accepted
#print axioms tierZero_sequent
#print axioms tierZero_refuses_changed_conclusion
#print axioms tierZero_widen
#print axioms mm0_accepted
#print axioms mm0_widen
#print axioms Controls.eta_certified_only_by_wider_bubble
#print axioms Controls.identityRedex_certified

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLLightBubbleElaboration
