import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.RetainedSemanticReadback
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution
import Mettapedia.Logic.HOL.TypeSubstitutionSemantics
import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation

/-!
# The common set-operation signature in HOL Light

The six typed set-operation symbols are assigned distinct declared names and
one closed atomic type. Retyping preserves all 29 retained HOL proof rules and
their ordered assumption occurrences. The primitive HOL Light compiler then
produces a checked graph, whose hypotheses are explicitly the finite set of
the translated assumptions.

The semantic extension below assigns actual supplied operations to those six
names. Unrelated symbols receive specified default values. This constructs a
full-domain model of the signature, not an admission of arbitrary set axioms.
The well-founded and hyperset operation interpretations can therefore share
the same checking signature without identifying their membership principles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.SetOperationInterpretation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation

open HOL.Embedding

def setType : AtomicTy :=
  ⟨.op (.mk (Name.global "SetOperationHOL.Set") .undefined) [], by
    constructor
    · rfl
    · apply Bool.eq_false_iff.mpr
      intro equal
      have absurd := (Ty.isBool_eq_true_iff _).mp equal
      simp [Ty.bool, TypeOp.bool, Name.global] at absurd⟩

def base (_ : Unit) : HOL.Ty AtomicTy := .base setType

abbrev type (A : HOL.Ty Unit) : HOL.Ty AtomicTy := HOL.Ty.substitute base A

def symbolName : {A : HOL.Ty Unit} → ZFSetHenkinInterpretation.Symbol A → Name
  | _, .member => Name.global "SetOperationHOL.member"
  | _, .empty => Name.global "SetOperationHOL.empty"
  | _, .union => Name.global "SetOperationHOL.union"
  | _, .power => Name.global "SetOperationHOL.power"
  | _, .separate => Name.global "SetOperationHOL.separate"
  | _, .replace => Name.global "SetOperationHOL.replace"

def symbol {A : HOL.Ty Unit} (constant : ZFSetHenkinInterpretation.Symbol A) : Symbol (type A) :=
  .constant (.mk (symbolName constant) .undefined) (reverseTy (type A)) (toHOL_reverseTy _)

def term {Γ : HOL.Ctx Unit} {A : HOL.Ty Unit} (source : HOL.Term ZFSetHenkinInterpretation.Symbol Γ A) :
    HOL.Term Symbol (Γ.map type) (type A) := HOL.mapTypes base symbol source

/-- Retyping keeps the supplied proof rather than selecting another derivation. -/
def proof {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula ZFSetHenkinInterpretation.Symbol Γ)}
    {φ : HOL.Formula ZFSetHenkinInterpretation.Symbol Γ} (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol Δ φ) :
    HOL.ProofSyntax Symbol (Δ.map term) (term φ) :=
  HOL.ProofSyntax.mapTypes base symbol source

theorem proof_nodeCount {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula ZFSetHenkinInterpretation.Symbol Γ)}
    {φ : HOL.Formula ZFSetHenkinInterpretation.Symbol Γ} (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol Δ φ) :
    (proof source).nodeCount = source.nodeCount := HOL.ProofSyntax.nodeCount_mapTypes base symbol source

theorem term_substitution {Γ Δ : HOL.Ctx Unit} {A : HOL.Ty Unit}
    (substitution : HOL.Subst ZFSetHenkinInterpretation.Symbol Γ Δ)
    (translated : HOL.Subst Symbol (Γ.map type) (Δ.map type))
    (compatible : ∀ {B} (index : HOL.Var Γ B), term (substitution index) =
      translated (index.mapTypes base)) (source : HOL.Term ZFSetHenkinInterpretation.Symbol Γ A) :
    term (HOL.subst substitution source) = HOL.subst translated (term source) :=
  HOL.mapTypes_subst base symbol substitution translated compatible source

def compile (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula ZFSetHenkinInterpretation.Symbol Γ)}
    {φ : HOL.Formula ZFSetHenkinInterpretation.Symbol Γ} (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol Δ φ)
    (names : Naming (Γ.map type)) (origin : ProofExecution.Origin) :=
  RetainedCompilation.compile policy eta (proof source) names origin

theorem compile_accepted (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula ZFSetHenkinInterpretation.Symbol Γ)}
    {φ : HOL.Formula ZFSetHenkinInterpretation.Symbol Γ} (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol Δ φ)
    (names : Naming (Γ.map type)) (origin : ProofExecution.Origin) :
    (ProofSystem.checker policy).check (compile policy eta source names origin).proof.result
      (compile policy eta source names origin).proof.certificate = true :=
  (compile policy eta source names origin).proof.accepted

theorem compile_sequent (policy : AxiomPolicy) [DecidablePred policy] (eta : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx Unit} {Δ : List (HOL.Formula ZFSetHenkinInterpretation.Symbol Γ)}
    {φ : HOL.Formula ZFSetHenkinInterpretation.Symbol Γ} (source : HOL.ProofSyntax ZFSetHenkinInterpretation.Symbol Δ φ)
    (names : Naming (Γ.map type)) (origin : ProofExecution.Origin) :
    (compile policy eta source names origin).proof.result.sequent =
      ⟨reverseHypotheses names ((Δ.map term).map HOL.ImpredicativeConnectives.expand),
       reverseCanonical names (HOL.ImpredicativeConnectives.expand (term φ))⟩ :=
  Sequent.ext (compile policy eta source names origin).hypotheses_exact
    (compile policy eta source names origin).conclusion_exact

universe u

section Interpretation

variable (Carrier : Type (u + 1))

abbrev sourceCarrier (_ : Unit) := Carrier
abbrev targetCarrier (_ : AtomicTy) := Carrier

def defaultValue (point : Carrier) : (A : HOL.Ty AtomicTy) → HOL.Ty.denote.{0, u + 1} (targetCarrier Carrier) A
  | .prop => .up False
  | .base _ => point
  | .arr _ B => fun _ => defaultValue point B

def nameOf : {A : HOL.Ty AtomicTy} → Symbol A → Option Name
  | _, .constant (.mk name .undefined) _ _ => some name
  | _, _ => none

open Classical in
noncomputable def assign (A : HOL.Ty Unit) (constant : ZFSetHenkinInterpretation.Symbol A)
    (value : HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A)
    (fallback : ∀ {B}, Symbol B → HOL.Ty.denote.{0, u + 1} (targetCarrier Carrier) B) :
    ∀ {B}, Symbol B → HOL.Ty.denote.{0, u + 1} (targetCarrier Carrier) B :=
  fun {B} native =>
    if same : B = type A then
      if nameOf native = some (symbolName constant) then
        same.symm ▸ HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A value
      else fallback native
    else fallback native

noncomputable def denotation (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A) :
    ∀ {B}, Symbol B → HOL.Ty.denote.{0, u + 1} (targetCarrier Carrier) B :=
  assign Carrier _ .member (operations .member)
    (assign Carrier _ .empty (operations .empty)
    (assign Carrier _ .union (operations .union)
    (assign Carrier _ .power (operations .power)
    (assign Carrier _ .separate (operations .separate)
    (assign Carrier _ .replace (operations .replace)
      (fun {B} _ => defaultValue Carrier point B))))))

theorem denotation_symbol (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A)
    {A : HOL.Ty Unit} (constant : ZFSetHenkinInterpretation.Symbol A) :
    denotation Carrier point operations (symbol constant) =
      HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A (operations constant) := by
  cases constant <;>
    simp [denotation, assign, nameOf, symbol, symbolName, type, base, HOL.Ty.substitute,
      ZFSetHenkinInterpretation.set, ZFSetHenkinInterpretation.mapping, ZFSetHenkinInterpretation.predicate, Name.global]

noncomputable def model (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A) :
    HOL.HenkinModel.{0, 0, u + 1} AtomicTy Symbol :=
  HOL.HenkinModel.standard (targetCarrier Carrier) (denotation Carrier point operations)

theorem fullDomains (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A) :
    (model Carrier point operations).FullDomains := HOL.HenkinModel.fullDomains_standard _ _

theorem reduct_eq (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A) :
    HOL.HenkinModel.standardTypeReduct base symbol (model Carrier point operations) =
      HOL.HenkinModel.standard (sourceCarrier Carrier) operations := by
  unfold HOL.HenkinModel.standardTypeReduct model
  congr 1
  funext A constant
  exact (congrArg (HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A).symm
    (denotation_symbol Carrier point operations constant)).trans
      ((HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A).symm_apply_apply _)

def sourceValuation {Γ : HOL.Ctx Unit}
    (valuation : ∀ {B}, HOL.Var (Γ.map type) B → HOL.Ty.denote.{0, u + 1} (targetCarrier Carrier) B) :
    ∀ {A}, HOL.Var Γ A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A :=
  fun {A} index => (HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A).symm
    (valuation (index.mapTypes base))

/-- The independently assigned native symbols recover the original operations
under the existing type-derived model reduct. -/
theorem term_meaning (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A)
    {Γ : HOL.Ctx Unit} {A : HOL.Ty Unit} (source : HOL.Term ZFSetHenkinInterpretation.Symbol Γ A)
    (valuation : (model Carrier point operations).Valuation (Γ.map type)) :
    (model Carrier point operations).denote (term source) valuation =
      HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A
        ((HOL.HenkinModel.standard (sourceCarrier Carrier) operations).denote source
          (sourceValuation Carrier valuation)) := by
  have natural := HOL.HenkinModel.denote_mapTypes base symbol (model Carrier point operations)
    (fullDomains Carrier point operations) source valuation
  change HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) A
    ((HOL.HenkinModel.standard (sourceCarrier Carrier)
      (fun {B} c => (HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) B).symm
        (denotation Carrier point operations (symbol c)))).denote source
          (sourceValuation Carrier valuation)) = _ at natural
  have same : (fun {B} (c : ZFSetHenkinInterpretation.Symbol B) =>
      (HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) B).symm
        (denotation Carrier point operations (symbol c))) =
        (operations : ∀ {B}, ZFSetHenkinInterpretation.Symbol B → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) B) := by
    funext B c
    rw [denotation_symbol]
    exact (HOL.Ty.denoteSubstituteEquiv base (targetCarrier Carrier) B).symm_apply_apply _
  rw [same] at natural
  exact natural.symm

/-- Satisfaction of closed formulas agrees with the original operation model. -/
theorem models_term (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A)
    (formula : HOL.ClosedFormula ZFSetHenkinInterpretation.Symbol) :
    (model Carrier point operations).models (term formula) ↔
      (HOL.HenkinModel.standard (sourceCarrier Carrier) operations).models formula := by
  have natural := HOL.HenkinModel.models_mapTypes base symbol (model Carrier point operations)
    (fullDomains Carrier point operations) formula
  rw [reduct_eq] at natural
  exact natural.symm

end Interpretation

theorem term_equalitySymbolFree {Γ : HOL.Ctx Unit} {A : HOL.Ty Unit}
    (source : HOL.Term ZFSetHenkinInterpretation.Symbol Γ A) : EqualitySymbolFree (term source) := by
  intro operand
  induction source with
  | var _ => exact .var
  | const constant =>
      apply Symbol.noConstOccurrence_const
      intro same
      have equalNames := congrArg (fun value : Sigma Symbol => nameOf value.2) same
      cases constant <;>
        simp [nameOf, symbol, symbolName, equalitySymbol, Const.equality, Name.global] at equalNames
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ ih => exact .lam ih
  | top => exact .top
  | bot => exact .bot
  | and _ _ ihp ihq => exact .and ihp ihq
  | or _ _ ihp ihq => exact .or ihp ihq
  | imp _ _ ihp ihq => exact .imp ihp ihq
  | not _ ih => exact .not ih
  | eq _ _ ihp ihq => exact .eq ihp ihq
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

/-- Every expanded material formula is in the actual native signature image. -/
theorem expanded_equalitySymbolFree {Γ : HOL.Ctx Unit}
    (formula : HOL.Formula ZFSetHenkinInterpretation.Symbol Γ) :
    EqualitySymbolFree (HOL.ImpredicativeConnectives.expand (term formula)) :=
  fun operand => HOL.ImpredicativeConnectives.noConstOccurrence_expand (term_equalitySymbolFree formula operand)

/-- Checking an exact common-profile sequent implies truth in any of the
constructed operation models, independently of which producer supplied it. -/
theorem accepted_meaning (Carrier : Type (u + 1)) (point : Carrier)
    (operations : ∀ {A}, ZFSetHenkinInterpretation.Symbol A → HOL.Ty.denote.{0, u + 1} (sourceCarrier Carrier) A)
    (hypotheses : List (HOL.ClosedFormula ZFSetHenkinInterpretation.Symbol))
    (conclusion : HOL.ClosedFormula ZFSetHenkinInterpretation.Symbol)
    {claim : Theorem} {certificate : ProofSystem.Certificate} [DecidablePred etaAxiomPolicy]
    (accepted : (ProofSystem.checker etaAxiomPolicy).check claim certificate = true)
    (exactSequent : claim.sequent = RetainedSemanticReadback.sequent
      (hypotheses.map (fun formula : HOL.ClosedFormula ZFSetHenkinInterpretation.Symbol =>
        HOL.ImpredicativeConnectives.expand (term formula)))
      (HOL.ImpredicativeConnectives.expand (term conclusion)))
    (satisfied : ∀ formula ∈ hypotheses,
      (HOL.HenkinModel.standard (sourceCarrier Carrier) operations).models formula) :
    (HOL.HenkinModel.standard (sourceCarrier Carrier) operations).models conclusion := by
  have derived := RetainedSemanticReadback.accepted_models _ _
    (by
      intro formula member
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
      exact expanded_equalitySymbolFree source)
    (expanded_equalitySymbolFree conclusion) accepted exactSequent
    (model Carrier point operations)
    ((model Carrier point operations).functionsRespectEqv_of_fullDomains (fullDomains Carrier point operations))
    (by
      intro formula member
      obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
      apply (HOL.ImpredicativeConnectives.models_expand _ _).mpr
      exact (models_term Carrier point operations source).mpr (satisfied source sourceMember))
  apply (models_term Carrier point operations conclusion).mp
  exact (HOL.ImpredicativeConnectives.models_expand _ _).mp derived

end Mettapedia.Languages.HOLLight.SetOperationInterpretation
