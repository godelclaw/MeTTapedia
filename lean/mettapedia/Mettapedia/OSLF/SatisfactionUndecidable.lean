import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.MeTTaIL.PatternCode
import Mettapedia.Languages.PartrecMachine.UndecidableEquivalence
import Mettapedia.GSLT.LanguageDef.SemanticDecidabilityFrontier
import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Satisfaction of OSLF formulas on the partial-recursive machine

On the partial-recursive machine, the least fixpoint "a finite reduction reaches
an irreducible term" holds of a probe exactly when that probe halts. Halting of
the probe family is not a computable predicate of the index, and neither is
satisfaction of this formula.

Formulas and terms already have injective numerical codes. Packing those codes
makes satisfaction of an arbitrary formula at an arbitrary term a claim in the
decision-kernel vocabulary, and the probe family is an exact computable
reduction of fixed-input halting into that claim. No computable decision kernel
decides it.

The fragment built from truth, falsity, conjunction, disjunction, and diamond
is decided by the bounded checker once the fuel exceeds the number of
constructors. Conjunction and disjunction spend a unit of fuel, so the bound
counts every constructor, not only diamonds. The fixpoint is what leaves this
fragment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.SatisfactionUndecidable

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.PartrecMachine
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticDecidabilityFrontier
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-! ## The atom-free fixpoint -/

/-- The body of "reaches an irreducible term": the term has no reduct, or some
one-step reduct satisfies the bound predicate. -/
def reachesIrreducibleBody : OSLFFormula :=
  .or (.imp (.dia .top) .bot) (.dia (.var 0))

/-- Least fixpoint of `reachesIrreducibleBody`. A term satisfies it when a
finite chain of reductions reaches a term with no reduct. -/
def reachesIrreducible : OSLFFormula :=
  .mu reachesIrreducibleBody

theorem reachesIrreducibleBody_positiveIn :
    OSLFFormula.positiveIn 0 reachesIrreducibleBody = true := by
  decide

theorem reachesIrreducibleBody_closedAt :
    OSLFFormula.closedAt 1 reachesIrreducibleBody = true := by
  decide

/-- The body is not generator-free: the bound variable occurs in it. -/
theorem reachesIrreducibleBody_not_muFree :
    OSLFFormula.muFree reachesIrreducibleBody = false := by
  decide

theorem reachesIrreducible_closedAt :
    OSLFFormula.closedAt 0 reachesIrreducible = true := by
  decide

theorem reachesIrreducible_not_modalOnly :
    OSLFFormula.modalOnly reachesIrreducible = false := by
  decide

theorem reachesIrreducible_ne_top : reachesIrreducible ≠ .top := by
  decide

/-! ## Reaching an irreducible term -/

/-- The term has no one-step reduct. -/
def Irreducible (R : Pattern → Pattern → Prop) (term : Pattern) : Prop :=
  ¬ ∃ target, R term target

/-- Some finite chain of reductions ends at an irreducible term. -/
def ReachesIrreducible (R : Pattern → Pattern → Prop) (term : Pattern) : Prop :=
  ∃ target, Relation.ReflTransGen R term target ∧ Irreducible R target

theorem halt_is_irreducible (output : List ℕ) :
    Irreducible Reduces (encCfg (.halt output)) := by
  intro ⟨target, step⟩
  exact halt_irreducible output target step

theorem probe_not_irreducible (index : ℕ) :
    ¬ Irreducible Reduces (probe index) := by
  intro irreducible
  exact irreducible ⟨normalReduct universal .halt [index, 0], reduces_normal_iff.mpr rfl⟩

/-- The body, with the bound variable read as `candidate`, is irreducibility or
a one-step reduct in `candidate`. -/
theorem semEnv_reachesIrreducibleBody
    (R : Pattern → Pattern → Prop) (I : AtomSem) (candidate : Pattern → Prop)
    (term : Pattern) :
    semEnv R fullFrame I (ScopeEnv.push candidate ScopeEnv.empty)
        reachesIrreducibleBody term ↔
      Irreducible R term ∨ ∃ target, R term target ∧ candidate target := by
  simp only [reachesIrreducibleBody, semEnv, ScopeEnv.push, and_true, Irreducible]

/-- Satisfaction of the fixpoint is exactly finite reachability of an
irreducible term. The atom interpretation is unused: the formula has no atoms. -/
theorem sem_reachesIrreducible_iff (I : AtomSem) (term : Pattern) :
    sem Reduces I reachesIrreducible term ↔ ReachesIrreducible Reduces term := by
  constructor
  · intro holds
    refine semEnv_mu_le Reduces fullFrame I ScopeEnv.empty reachesIrreducibleBody
        (ReachesIrreducible Reduces) trivial ?_ term holds
    intro source bodyHolds
    rcases (semEnv_reachesIrreducibleBody Reduces I (ReachesIrreducible Reduces) source).mp
        bodyHolds with irreducible | ⟨target, step, ⟨sink, path, sinkIrreducible⟩⟩
    · exact ⟨source, Relation.ReflTransGen.refl, irreducible⟩
    · exact ⟨sink, Relation.ReflTransGen.head step path, sinkIrreducible⟩
  · intro ⟨sink, path, sinkIrreducible⟩ candidate _ pre
    refine Relation.ReflTransGen.head_induction_on path ?base ?step
    · exact pre sink
        ((semEnv_reachesIrreducibleBody Reduces I candidate sink).mpr (Or.inl sinkIrreducible))
    · intro source middle step _ middleHolds
      exact pre source
        ((semEnv_reachesIrreducibleBody Reduces I candidate source).mpr
          (Or.inr ⟨middle, step, middleHolds⟩))

theorem sem_reachesIrreducible_halt (I : AtomSem) (output : List ℕ) :
    sem Reduces I reachesIrreducible (encCfg (.halt output)) :=
  (sem_reachesIrreducible_iff I _).mpr
    ⟨encCfg (.halt output), Relation.ReflTransGen.refl, halt_is_irreducible output⟩

theorem not_body_at_probe (I : AtomSem) (index : ℕ) :
    ¬ semEnv Reduces fullFrame I (ScopeEnv.push (fun _ => False) ScopeEnv.empty)
        reachesIrreducibleBody (probe index) := by
  intro holds
  rcases (semEnv_reachesIrreducibleBody Reduces I (fun _ => False) (probe index)).mp holds with
    irreducible | ⟨_target, _step, impossible⟩
  · exact probe_not_irreducible index irreducible
  · exact impossible

/-! ## The image is closed, and only halt configurations are irreducible in it -/

/-- A reduct of an encoded configuration or pending evaluation is again one. -/
theorem inImage_of_reflTransGen {source target : Pattern} (image : InImage source)
    (path : Relation.ReflTransGen Reduces source target) : InImage target := by
  induction path with
  | refl => exact image
  | tail _ step imageMiddle => exact reduct_inImage imageMiddle step

/-- Every encoded term that is not a halt configuration has a reduct. -/
theorem image_reducible_of_not_halt {term : Pattern} (image : InImage term)
    (notHalt : ∀ output, term ≠ encCfg (.halt output)) :
    ∃ target, Reduces term target := by
  rcases image with ⟨code, continuation, values, rfl⟩ | ⟨configuration, rfl⟩
  · exact ⟨normalReduct code continuation values, reduces_normal_iff.mpr rfl⟩
  · cases configuration with
    | halt output => exact absurd rfl (notHalt output)
    | ret continuation values =>
        exact ⟨retReduct continuation values, reduces_ret_iff.mpr rfl⟩

theorem image_irreducible_iff_halt {term : Pattern} (image : InImage term) :
    Irreducible Reduces term ↔ ∃ output, term = encCfg (.halt output) := by
  constructor
  · intro irreducible
    rcases image with ⟨code, continuation, values, rfl⟩ | ⟨configuration, rfl⟩
    · exact absurd (reduces_normal_iff.mpr rfl)
        (fun step => irreducible ⟨normalReduct code continuation values, step⟩)
    · cases configuration with
      | halt output => exact ⟨output, rfl⟩
      | ret continuation values =>
          exact absurd (reduces_ret_iff.mpr rfl)
            (fun step => irreducible ⟨retReduct continuation values, step⟩)
  · rintro ⟨output, rfl⟩
    exact halt_is_irreducible output

theorem reachesIrreducible_probe_iff_halts (index : ℕ) :
    ReachesIrreducible Reduces (probe index) ↔ Halts (probe index) := by
  constructor
  · rintro ⟨target, path, irreducible⟩
    have imageTarget : InImage target :=
      inImage_of_reflTransGen (probe_inImage index) path
    obtain ⟨output, targetHalt⟩ := (image_irreducible_iff_halt imageTarget).mp irreducible
    subst targetHalt
    exact ⟨output, path⟩
  · rintro ⟨output, path⟩
    exact ⟨encCfg (.halt output), path, halt_is_irreducible output⟩

theorem sem_reachesIrreducible_probe_iff_halts (I : AtomSem) (index : ℕ) :
    sem Reduces I reachesIrreducible (probe index) ↔ Halts (probe index) :=
  (sem_reachesIrreducible_iff I (probe index)).trans (reachesIrreducible_probe_iff_halts index)

/-- Satisfaction of the fixpoint at the probe is not a computable predicate of
the index. -/
theorem sem_reachesIrreducible_probe_not_computable (I : AtomSem) :
    ¬ ComputablePred fun index : ℕ =>
      sem Reduces I reachesIrreducible (probe index) := by
  intro decided
  apply probe_halts_not_computable
  exact decided.of_eq fun index => sem_reachesIrreducible_probe_iff_halts I index

/-! ## The language's satisfaction agrees with `sem` -/

/-- On an equation-free presentation the equation frame contains every
predicate and closes nothing, so formula satisfaction in that frame is the
ambient satisfaction along the same step relation. -/
theorem semEnv_equationFrame_iff_full
    (relEnv : RelationEnv) {lang : LanguageDef}
    (equationFree : lang.isEquationFree = true) (interpretation : AtomSem) :
    ∀ formula env term,
      semEnv (langSemanticReducesUsing relEnv lang) (equationFrameUsing relEnv lang)
          (fun atom =>
            (equationAtomSemUsingOfEquationFree relEnv equationFree interpretation atom).1)
          env formula term ↔
        semEnv (langSemanticReducesUsing relEnv lang) fullFrame interpretation
          env formula term := by
  have equivIffEq : ∀ left right,
      (langGSLTUsing relEnv lang).Equiv left right ↔ left = right := by
    intro left right
    unfold langGSLTUsing
    exact gsltModuloEquations_equiv_iff_eq_of_no_generators equationFree left right
  have closeIff : ∀ predicate point,
      (equationFrameUsing relEnv lang).close predicate point ↔ predicate point := by
    intro predicate point
    unfold equationFrameUsing
    exact saturatePredicate_apply_iff_of_equiv_iff_eq
      (langGSLTUsing relEnv lang) equivIffEq predicate point
  have atomEq : ∀ atom,
      (equationAtomSemUsingOfEquationFree relEnv equationFree interpretation atom).1 =
        interpretation atom := by
    intro atom
    rfl
  intro formula
  induction formula with
  | top =>
      intro _ _
      simp [semEnv]
  | bot =>
      intro _ _
      simp [semEnv]
  | atom _ =>
      intro _ term
      simp only [semEnv, atomEq]
  | var _ =>
      intro env term
      simp [semEnv]
  | and left right ihLeft ihRight =>
      intro env term
      simp only [semEnv]
      exact and_congr (ihLeft env term) (ihRight env term)
  | or left right ihLeft ihRight =>
      intro env term
      simp only [semEnv]
      exact or_congr (ihLeft env term) (ihRight env term)
  | imp left right ihLeft ihRight =>
      intro env term
      simp only [semEnv]
      exact imp_congr (ihLeft env term) (ihRight env term)
  | dia body ih =>
      intro env term
      simp only [semEnv]
      constructor
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (ih env target).mp holds⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (ih env target).mpr holds⟩
  | box body ih =>
      intro env term
      simp only [semEnv]
      constructor
      · intro holds source step
        exact (ih env source).mp (holds source step)
      · intro holds source step
        exact (ih env source).mpr (holds source step)
  | mu body ih =>
      intro env term
      simp only [semEnv]
      constructor
      · intro holds candidate _ preFull
        apply holds candidate
          (equationInvariant_langGSLTUsing_of_equation_free relEnv equationFree candidate)
        intro source bodyFrame
        exact preFull source ((ih (ScopeEnv.push candidate env) source).mp bodyFrame)
      · intro holds candidate _ preFrame
        apply holds candidate trivial
        intro source bodyFull
        exact preFrame source ((ih (ScopeEnv.push candidate env) source).mpr bodyFull)
  | emptyColl _ =>
      intro _ term
      simp only [semEnv, fullFrame]
      exact closeIff _ term
  | cut _ left right ihLeft ihRight =>
      intro env term
      simp only [semEnv, fullFrame]
      rw [closeIff]
      constructor
      · rintro ⟨leftParts, rightParts, shape, holdsLeft, holdsRight⟩
        exact ⟨leftParts, rightParts, shape,
          (ihLeft env _).mp holdsLeft, (ihRight env _).mp holdsRight⟩
      · rintro ⟨leftParts, rightParts, shape, holdsLeft, holdsRight⟩
        exact ⟨leftParts, rightParts, shape,
          (ihLeft env _).mpr holdsLeft, (ihRight env _).mpr holdsRight⟩
  | headed _ body ih =>
      intro env term
      simp only [semEnv, fullFrame]
      rw [closeIff]
      constructor
      · rintro ⟨inner, shape, holds⟩
        exact ⟨inner, shape, (ih env inner).mp holds⟩
      · rintro ⟨inner, shape, holds⟩
        exact ⟨inner, shape, (ih env inner).mpr holds⟩

theorem langSemanticReducesUsing_partrec_eq_reduces :
    langSemanticReducesUsing RelationEnv.empty partrecMachine = Reduces := by
  funext source target
  change (langGSLT partrecMachine).Step source target = Reduces source target
  exact congrFun (congrFun reduces_eq_generatedStep.symm source) target

theorem langFormulaSem_iff_sem_partrec (interpretation : AtomSem)
    (formula : OSLFFormula) (term : Pattern) :
    langFormulaSem partrecMachine
        (equationAtomSemOfEquationFree partrecMachine_equationFree interpretation)
        formula term ↔
      sem Reduces interpretation formula term := by
  rw [langFormulaSem_apply]
  simp only [langSemUsing, sem, equationAtomSemOfEquationFree]
  rw [← langSemanticReducesUsing_partrec_eq_reduces]
  exact semEnv_equationFrame_iff_full RelationEnv.empty
    partrecMachine_equationFree interpretation formula ScopeEnv.empty term

theorem langFormulaSem_reachesIrreducible_probe_iff_halts
    (interpretation : AtomSem) (index : ℕ) :
    langFormulaSem partrecMachine
        (equationAtomSemOfEquationFree partrecMachine_equationFree interpretation)
        reachesIrreducible (probe index) ↔
      Halts (probe index) :=
  (langFormulaSem_iff_sem_partrec interpretation reachesIrreducible (probe index)).trans
    (sem_reachesIrreducible_probe_iff_halts interpretation index)

/-- Satisfaction, in the satisfaction relation of the partial-recursive
machine, of the atom-free fixpoint at the probe is not a computable predicate
of the index. -/
theorem reachesIrreducible_probe_not_computable (interpretation : AtomSem) :
    ¬ ComputablePred fun index : ℕ =>
      langFormulaSem partrecMachine
        (equationAtomSemOfEquationFree partrecMachine_equationFree interpretation)
        reachesIrreducible (probe index) := by
  intro decided
  apply probe_halts_not_computable
  exact decided.of_eq fun index =>
    langFormulaSem_reachesIrreducible_probe_iff_halts interpretation index

/-! ## Codes, and the uniform decision kernel -/

/-- Injective Gödel numbering of formulas. The tag selects the constructor. -/
def formulaCode : OSLFFormula → ℕ
  | .top => Nat.pair 0 0
  | .bot => Nat.pair 1 0
  | .atom name => Nat.pair 2 (stringCode name)
  | .and left right => Nat.pair 3 (Nat.pair (formulaCode left) (formulaCode right))
  | .or left right => Nat.pair 4 (Nat.pair (formulaCode left) (formulaCode right))
  | .imp left right => Nat.pair 5 (Nat.pair (formulaCode left) (formulaCode right))
  | .dia body => Nat.pair 6 (formulaCode body)
  | .box body => Nat.pair 7 (formulaCode body)
  | .var index => Nat.pair 8 index
  | .mu body => Nat.pair 9 (formulaCode body)
  | .emptyColl kind => Nat.pair 10 (collectionCode kind)
  | .cut kind left right =>
      Nat.pair 11 (Nat.pair (collectionCode kind)
        (Nat.pair (formulaCode left) (formulaCode right)))
  | .headed label body =>
      Nat.pair 12 (Nat.pair (stringCode label) (formulaCode body))

theorem formulaCode_top : formulaCode .top = Nat.pair 0 0 := by
  simp [formulaCode]

theorem formulaCode_top_ne_bot : formulaCode .top ≠ formulaCode .bot := by
  simp [formulaCode, Nat.pair_eq_pair]

private theorem formulaCode_tag_absurd {left right : ℕ} {payloadLeft payloadRight : ℕ}
    (equality : Nat.pair left payloadLeft = Nat.pair right payloadRight)
    (distinct : left ≠ right) : False :=
  distinct (Nat.pair_eq_pair.mp equality).1

theorem formulaCode_injective : Function.Injective formulaCode := by
  intro left
  induction left with
  | top =>
      intro right equality
      cases right with
      | top => rfl
      | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | bot =>
      intro right equality
      cases right with
      | bot => rfl
      | top | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | atom name =>
      intro right equality
      cases right with
      | atom other =>
          unfold formulaCode at equality
          exact congrArg OSLFFormula.atom
            (stringCode_injective (Nat.pair_eq_pair.mp equality).2)
      | top | bot | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | and left right ihLeft ihRight =>
      intro other equality
      cases other with
      | and otherLeft otherRight =>
          unfold formulaCode at equality
          have inner := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp equality).2
          exact congrArg₂ OSLFFormula.and (ihLeft inner.1) (ihRight inner.2)
      | top | bot | atom _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | or left right ihLeft ihRight =>
      intro other equality
      cases other with
      | or otherLeft otherRight =>
          unfold formulaCode at equality
          have inner := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp equality).2
          exact congrArg₂ OSLFFormula.or (ihLeft inner.1) (ihRight inner.2)
      | top | bot | atom _ | and _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | imp left right ihLeft ihRight =>
      intro other equality
      cases other with
      | imp otherLeft otherRight =>
          unfold formulaCode at equality
          have inner := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp equality).2
          exact congrArg₂ OSLFFormula.imp (ihLeft inner.1) (ihRight inner.2)
      | top | bot | atom _ | and _ _ | or _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | dia body ih =>
      intro other equality
      cases other with
      | dia otherBody =>
          unfold formulaCode at equality
          exact congrArg OSLFFormula.dia (ih (Nat.pair_eq_pair.mp equality).2)
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | box body ih =>
      intro other equality
      cases other with
      | box otherBody =>
          unfold formulaCode at equality
          exact congrArg OSLFFormula.box (ih (Nat.pair_eq_pair.mp equality).2)
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | var _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | var index =>
      intro other equality
      cases other with
      | var otherIndex =>
          unfold formulaCode at equality
          exact congrArg OSLFFormula.var (Nat.pair_eq_pair.mp equality).2
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | mu _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | mu body ih =>
      intro other equality
      cases other with
      | mu otherBody =>
          unfold formulaCode at equality
          exact congrArg OSLFFormula.mu (ih (Nat.pair_eq_pair.mp equality).2)
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _
        | emptyColl _ | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | emptyColl kind =>
      intro other equality
      cases other with
      | emptyColl otherKind =>
          unfold formulaCode at equality
          exact congrArg OSLFFormula.emptyColl
            (collectionCode_injective (Nat.pair_eq_pair.mp equality).2)
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | cut _ _ _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | cut kind left right ihLeft ihRight =>
      intro other equality
      cases other with
      | cut otherKind otherLeft otherRight =>
          unfold formulaCode at equality
          have middle := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp equality).2
          have inner := Nat.pair_eq_pair.mp middle.2
          have kindEq : kind = otherKind := collectionCode_injective middle.1
          subst kindEq
          exact congrArg₂ (OSLFFormula.cut kind) (ihLeft inner.1) (ihRight inner.2)
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | headed _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))
  | headed label body ih =>
      intro other equality
      cases other with
      | headed otherLabel otherBody =>
          unfold formulaCode at equality
          have inner := Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp equality).2
          have labelEq : label = otherLabel := stringCode_injective inner.1
          subst labelEq
          exact congrArg (OSLFFormula.headed label) (ih inner.2)
      | top | bot | atom _ | and _ _ | or _ _ | imp _ _ | dia _ | box _ | var _ | mu _
        | emptyColl _ | cut _ _ _ =>
          unfold formulaCode at equality
          exact False.elim (formulaCode_tag_absurd equality (by decide))

/-- Atomic observations for the uniform claim: no atom holds of any term.
The fixpoint used to embed halting has no atoms, so this choice does not move
the embedded family. -/
def partrecAtomSem : AtomSem := fun _ _ => False

theorem partrecAtomSem_top_ignored (term : Pattern) :
    partrecAtomSem "unused" term = False := rfl

theorem partrecAtomSem_not_true (name : String) (term : Pattern) :
    ¬ partrecAtomSem name term := by
  simp [partrecAtomSem]

/-- A claim is a code of a formula together with a code of a term. It holds
when the unique formula and term with those codes satisfy the machine's
formula semantics under `partrecAtomSem`. -/
def partrecSatisfaction (claim : ℕ × ℕ) : Prop :=
  ∃ formula : OSLFFormula, ∃ term : Pattern,
    formulaCode formula = claim.1 ∧
    patternCode term = claim.2 ∧
    langFormulaSem partrecMachine
      (equationAtomSemOfEquationFree partrecMachine_equationFree partrecAtomSem)
      formula term

theorem partrecSatisfaction_top (term : Pattern) :
    partrecSatisfaction (formulaCode .top, patternCode term) := by
  refine ⟨.top, term, rfl, rfl, ?_⟩
  exact (langFormulaSem_iff_sem_partrec partrecAtomSem .top term).mpr trivial

theorem not_partrecSatisfaction_bot (term : Pattern) :
    ¬ partrecSatisfaction (formulaCode .bot, patternCode term) := by
  intro ⟨formula, coded, formulaSame, termSame, holds⟩
  have formulaEq : formula = .bot := formulaCode_injective formulaSame
  have termEq : coded = term := patternCode_injective termSame
  subst formulaEq
  subst termEq
  have botHolds : sem Reduces partrecAtomSem .bot coded :=
    (langFormulaSem_iff_sem_partrec partrecAtomSem .bot coded).mp holds
  simp [sem, semEnv] at botHolds

/-- Fixed-input halting reduces to satisfaction of the atom-free fixpoint at
the probe. The term code is the computable probe code, which `patternCode_probe`
identifies with the code of the probe term. -/
noncomputable def haltingToPartrecSatisfaction :
    ComputableExactMeaningReduction Nat.Partrec.Code (ℕ × ℕ)
      Checker.HaltingMeaning partrecSatisfaction where
  encode code :=
    (formulaCode reachesIrreducible,
      probeCode (numeralCode (Encodable.encode code)))
  encode_computable :=
    Computable.pair (Computable.const _)
      ((primrec_probeCode.comp primrec_numeralCode).to_comp.comp Computable.encode)
  meaning_iff code := by
    constructor
    · intro satisfied
      obtain ⟨formula, term, formulaSame, termSame, holds⟩ := satisfied
      have formulaEq : formula = reachesIrreducible :=
        formulaCode_injective formulaSame
      have termCode : patternCode term = patternCode (probe (Encodable.encode code)) := by
        rw [termSame, patternCode_probe]
      have termEq : term = probe (Encodable.encode code) :=
        patternCode_injective termCode
      subst formulaEq
      subst termEq
      have halts : Halts (probe (Encodable.encode code)) :=
        (langFormulaSem_reachesIrreducible_probe_iff_halts partrecAtomSem _).mp holds
      simpa [Checker.HaltingMeaning, probe_halts_iff, Denumerable.ofNat_encode] using halts
    · intro halts
      refine ⟨reachesIrreducible, probe (Encodable.encode code), rfl, ?_, ?_⟩
      · rw [patternCode_probe]
      · exact (langFormulaSem_reachesIrreducible_probe_iff_halts partrecAtomSem _).mpr
          ((probe_halts_iff (Encodable.encode code)).mpr (by
            unfold Checker.HaltingMeaning at halts
            simpa [Denumerable.ofNat_encode] using halts))

theorem haltingToPartrecSatisfaction_encode (code : Nat.Partrec.Code) :
    haltingToPartrecSatisfaction.encode code =
      (formulaCode reachesIrreducible, probeCode (numeralCode (Encodable.encode code))) :=
  rfl

theorem haltingToPartrecSatisfaction_encode_ne_bot (code : Nat.Partrec.Code) :
    (haltingToPartrecSatisfaction.encode code).1 ≠ formulaCode .bot := by
  rw [haltingToPartrecSatisfaction_encode]
  intro same
  have : reachesIrreducible = .bot := formulaCode_injective same
  simp [reachesIrreducible] at this

/-- No computable decision kernel decides satisfaction of an arbitrary formula
at an arbitrary term of the partial-recursive machine. -/
theorem partrecSatisfaction_no_computableDecisionKernel :
    ¬ ∃ kernel : Checker.DecisionKernel (ℕ × ℕ) partrecSatisfaction,
      Computable kernel.decide :=
  no_computableDecisionKernel_of_halting_reduction haltingToPartrecSatisfaction

/-! ## The decidable constructor fragment -/

/-- Formulas built from `⊤`, `⊥`, `∧`, `∨`, and `◇` only. -/
def modalSearch : OSLFFormula → Bool
  | .top | .bot => true
  | .and left right | .or left right => modalSearch left && modalSearch right
  | .dia body => modalSearch body
  | _ => false

/-- Constructor depth. Conjunction, disjunction, and diamond each spend one
unit of checker fuel, so a bound that counted only diamonds would be short.
The successor is written on the right so it matches the checker's `fuel + 1`
recursion. -/
def modalSearchDepth : OSLFFormula → ℕ
  | .top | .bot => 0
  | .and left right | .or left right =>
      max (modalSearchDepth left) (modalSearchDepth right) + 1
  | .dia body => modalSearchDepth body + 1
  | _ => 0

theorem modalSearch_top : modalSearch .top = true := by
  decide

theorem modalSearch_reachesIrreducible : modalSearch reachesIrreducible = false := by
  decide

theorem modalSearchDepth_top : modalSearchDepth .top = 0 := by
  decide

theorem modalSearchDepth_dia_top : modalSearchDepth (.dia .top) = 1 := by
  decide

theorem modalSearch_sem_independent {R : Pattern → Pattern → Prop}
    {I I' : AtomSem} {formula : OSLFFormula} (search : modalSearch formula = true) :
    ∀ term, sem R I formula term ↔ sem R I' formula term := by
  induction formula with
  | top =>
      intro _
      simp [sem, semEnv]
  | bot =>
      intro _
      simp [sem, semEnv]
  | and left right ihLeft ihRight =>
      intro term
      simp only [modalSearch, Bool.and_eq_true] at search
      simp only [sem, semEnv]
      exact and_congr (ihLeft search.1 term) (ihRight search.2 term)
  | or left right ihLeft ihRight =>
      intro term
      simp only [modalSearch, Bool.and_eq_true] at search
      simp only [sem, semEnv]
      exact or_congr (ihLeft search.1 term) (ihRight search.2 term)
  | dia body ih =>
      intro term
      simp only [modalSearch] at search
      simp only [sem, semEnv]
      constructor
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (ih search target).mp holds⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (ih search target).mpr holds⟩
  | atom _ | imp _ _ | box _ | var _ | mu _ | emptyColl _ | cut _ _ _ | headed _ _ =>
      simp [modalSearch] at search

theorem modalSearch_semFuel_independent
    {step : Pattern → List Pattern} {I I' : AtomSem} {formula : OSLFFormula}
    (search : modalSearch formula = true) :
    ∀ fuel term, semFuel step I fuel formula term ↔ semFuel step I' fuel formula term := by
  intro fuel
  induction fuel generalizing formula with
  | zero =>
      intro _
      simp [semFuel]
  | succ fuel ihFuel =>
      induction formula with
      | top =>
          intro _
          simp [semFuel]
      | bot =>
          intro _
          simp [semFuel]
      | and left right =>
          intro term
          simp only [modalSearch, Bool.and_eq_true] at search
          simp only [semFuel]
          exact and_congr (ihFuel search.1 term) (ihFuel search.2 term)
      | or left right =>
          intro term
          simp only [modalSearch, Bool.and_eq_true] at search
          simp only [semFuel]
          exact or_congr (ihFuel search.1 term) (ihFuel search.2 term)
      | dia body =>
          intro term
          simp only [modalSearch] at search
          simp only [semFuel]
          constructor
          · rintro ⟨target, member, holds⟩
            exact ⟨target, member, (ihFuel search target).mp holds⟩
          · rintro ⟨target, member, holds⟩
            exact ⟨target, member, (ihFuel search target).mpr holds⟩
      | atom _ | imp _ _ | box _ | var _ | mu _ | emptyColl _ | cut _ _ _ | headed _ _ =>
          simp [modalSearch] at search

theorem sem_implies_semFuel_modalSearch (I : AtomSem) :
    ∀ formula, modalSearch formula = true → ∀ term,
      sem Reduces I formula term →
        semFuel (rootReducts partrecMachine) I (modalSearchDepth formula + 1)
          formula term := by
  intro formula
  induction formula with
  | top =>
      intro _ term _
      simp [semFuel]
  | bot =>
      intro _ term holds
      simp [sem, semEnv] at holds
  | and left right ihLeft ihRight =>
      intro search term holds
      simp only [modalSearch, Bool.and_eq_true] at search
      simp only [sem, semEnv] at holds
      simp only [modalSearchDepth, semFuel]
      exact ⟨semFuel_mono_fuel
          (Nat.add_le_add_right
            (Nat.le_max_left (modalSearchDepth left) (modalSearchDepth right)) 1)
          (ihLeft search.1 term holds.1),
        semFuel_mono_fuel
          (Nat.add_le_add_right
            (Nat.le_max_right (modalSearchDepth left) (modalSearchDepth right)) 1)
          (ihRight search.2 term holds.2)⟩
  | or left right ihLeft ihRight =>
      intro search term holds
      simp only [modalSearch, Bool.and_eq_true] at search
      simp only [sem, semEnv] at holds
      simp only [modalSearchDepth, semFuel]
      cases holds with
      | inl holdsLeft =>
          exact Or.inl (semFuel_mono_fuel
            (Nat.add_le_add_right
              (Nat.le_max_left (modalSearchDepth left) (modalSearchDepth right)) 1)
            (ihLeft search.1 term holdsLeft))
      | inr holdsRight =>
          exact Or.inr (semFuel_mono_fuel
            (Nat.add_le_add_right
              (Nat.le_max_right (modalSearchDepth left) (modalSearchDepth right)) 1)
            (ihRight search.2 term holdsRight))
  | dia body ih =>
      intro search term holds
      simp only [modalSearch] at search
      simp only [sem, semEnv] at holds
      obtain ⟨target, step, targetHolds⟩ := holds
      simp only [modalSearchDepth, semFuel]
      exact ⟨target, reduces_iff_mem_rootReducts.mp step, ih search target targetHolds⟩
  | atom _ | imp _ _ | box _ | var _ | mu _ | emptyColl _ | cut _ _ _ | headed _ _ =>
      intro search
      simp [modalSearch] at search

theorem modalSearch_sem_iff_semFuel {I : AtomSem} {formula : OSLFFormula}
    (search : modalSearch formula = true) (term : Pattern) :
    sem Reduces I formula term ↔
      semFuel (rootReducts partrecMachine) I (modalSearchDepth formula + 1)
        formula term := by
  constructor
  · exact sem_implies_semFuel_modalSearch I formula search term
  · intro fuelled
    exact semFuel_implies_sem (R := Reduces) (step := rootReducts partrecMachine) (I := I)
      (fun source target (member : target ∈ rootReducts partrecMachine source) =>
        reduces_iff_mem_rootReducts.mpr member)
      fuelled

/-- Bounded search at fuel one past the constructor depth decides the fragment.
The atom checker is constantly negative; the fragment contains no atoms, so
the interpretation does not affect the answer. -/
def decideModalSearch (formula : OSLFFormula) (term : Pattern) : Bool :=
  decide (check (rootReducts partrecMachine) (fun _ _ => false)
    (modalSearchDepth formula + 1) term formula = .sat)

theorem decideModalSearch_top (term : Pattern) : decideModalSearch .top term = true := by
  unfold decideModalSearch modalSearchDepth
  simp only [check]
  rfl

theorem decideModalSearch_bot (term : Pattern) : decideModalSearch .bot term = false := by
  unfold decideModalSearch modalSearchDepth
  simp only [check]
  rfl

theorem modalSearch_check_iff_sem {I : AtomSem} {formula : OSLFFormula}
    (search : modalSearch formula = true) (term : Pattern) :
    check (rootReducts partrecMachine) (fun _ _ => false)
        (modalSearchDepth formula + 1) term formula = .sat ↔
      sem Reduces I formula term := by
  have faithful : ∀ atom pattern,
      (fun (_ : String) (_ : Pattern) => false) atom pattern = true ↔
        partrecAtomSem atom pattern := by
    intro atom pattern
    simp [partrecAtomSem]
  rw [check_sat_iff_semFuel (I_sem := partrecAtomSem) faithful]
  rw [modalSearch_semFuel_independent (I := partrecAtomSem) (I' := I) search
    (modalSearchDepth formula + 1) term]
  exact (modalSearch_sem_iff_semFuel search term).symm

theorem decideModalSearch_iff {I : AtomSem} {formula : OSLFFormula}
    (search : modalSearch formula = true) (term : Pattern) :
    decideModalSearch formula term = true ↔ sem Reduces I formula term := by
  simp only [decideModalSearch, decide_eq_true_iff]
  exact modalSearch_check_iff_sem search term

/-- The same bounded search decides the fragment in the machine's own
satisfaction relation. -/
theorem modalSearch_langFormulaSem_iff_check {formula : OSLFFormula}
    (search : modalSearch formula = true) (term : Pattern) (interpretation : AtomSem) :
    check (rootReducts partrecMachine) (fun _ _ => false)
        (modalSearchDepth formula + 1) term formula = .sat ↔
      langFormulaSem partrecMachine
        (equationAtomSemOfEquationFree partrecMachine_equationFree interpretation)
        formula term := by
  rw [modalSearch_check_iff_sem search term,
    langFormulaSem_iff_sem_partrec interpretation formula term]

end Mettapedia.OSLF.SatisfactionUndecidable
