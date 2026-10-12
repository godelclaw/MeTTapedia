import Mettapedia.OSLF.Syntax.RhoSourceOutputPredicate
import Mettapedia.OSLF.Syntax.BindingConstructorPredicatePresheaf

/-!
# Constructor observations at the actual rho source quotient

Parallel-with-null changes the raw root while preserving the source equation
class. Constructor image predicates remain meaningful on that quotient:
the parallel image covers every process, and overlaps the output image.
Argument receipts keep distinctions lost by that observation. Independently
refined parallel arguments and a bound input continuation use the nonconstant
source output predicate, with failed refinements as negative controls.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoEquationConstructorControls

open RhoSchema BindingConstructorPredicates FreeBindingTerms
open RhoSourceOutputPredicate

abbrev model := BindingEquationQuotientModel.algebra rhoSourceE

def project {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    TermQ rhoSourceE Γ sort := Quotient.mk _ term

/-- The source program with no occurrences. -/
def null {Γ : Ctx sig} : Term sig Γ Srt.pr := .op Op.nil .nil

def parallel {Γ : Ctx sig} (first second : Term sig Γ Srt.pr) : Term sig Γ Srt.pr :=
  .op Op.par (.cons first (.cons second .nil))

def closeProcess {Γ : Ctx sig} (value : Term sig Γ Srt.pr) : Sub sig [Srt.pr] Γ
  | _, .zero => value

/-- The actual quotient constructor agrees with projecting the independently
formed raw binding constructor, including its complete argument vector. -/
theorem constructor_read {Γ : Ctx sig} {sort : Srt} (operator : Op sort)
    (arguments : FamilyArgs sig (Term sig) (sig.arity operator) Γ) :
    model.operation operator (FamilyArgs.map project arguments) =
      project ((BindingCloneAlgebra.terms sig).operation operator arguments) :=
  ((BindingEquationQuotientModel.projection rhoSourceE).raw.map_operation
    operator arguments).symm

/-- The unit equation holds at every open context, with the original
contextual equation presentation and its actual closing substitution. -/
theorem parallel_null_equation {Γ : Ctx sig} (value : Term sig Γ Srt.pr) :
    EqClosure rhoSourceE (parallel value null) value := by
  simpa [rhoSourceE, rightUnitPar, parallel, null, instantiate, instantiateArgs,
    bind, bindArgs, liftSub, closeProcess] using
    (EqClosure.ax_closed (E := rhoSourceE) (Γ := Γ) 2 contDiscard
      (closeProcess value))

inductive Root where
  | variable | null | parallel | output | input | quote | drop
  deriving DecidableEq

/-- The literal parse-root observation before equation admission. -/
def rawRoot : {Γ : Ctx sig} → {sort : Srt} → Term sig Γ sort → Root
  | _, _, .var _ => .variable
  | _, _, .op .nil _ => .null
  | _, _, .op .par _ => .parallel
  | _, _, .op .out _ => .output
  | _, _, .op .inp _ => .input
  | _, _, .op .quo _ => .quote
  | _, _, .op .drp _ => .drop

/-- Even closed process classes cannot retain the exact raw parse root. -/
theorem raw_process_root_does_not_descend :
    ¬ ∃ reading : TermQ rhoSourceE [] Srt.pr → Root,
      ∀ term, reading (project term) = rawRoot term := by
  rintro ⟨reading, readout⟩
  have equalClasses : project (parallel (null : Term sig [] Srt.pr) null) =
      project null := Quotient.sound (parallel_null_equation null)
  have equalRoots := (readout (parallel null null)).symm.trans
    ((congrArg reading equalClasses).trans (readout null))
  change Root.parallel = Root.null at equalRoots
  cases equalRoots

/-- The name reflection equation supplies a second root obstruction at a
different sort, rather than merely a process wrapper example. -/
theorem raw_name_root_does_not_descend :
    ¬ ∃ reading : TermQ rhoSourceE [Srt.nm] Srt.nm → Root,
      ∀ term, reading (project term) = rawRoot term := by
  rintro ⟨reading, readout⟩
  have equalClasses : project RhoSourceEquationModel.quotedDroppedName =
      project RhoSourceEquationModel.nameVariable :=
    Quotient.sound RhoSourceEquationModel.quote_drop_source_equation
  have equalRoots := (readout _).symm.trans
    ((congrArg reading equalClasses).trans (readout _))
  change Root.quote = Root.variable at equalRoots
  cases equalRoots

def parallelInputs : Arguments model (sig.arity Op.par) :=
  .cons (top model Srt.pr) (.cons (top model Srt.pr) .nil)

/-- The exact raw term supplies its own retained parallel decomposition via
the admitted unit equation, without selecting a quotient representative. -/
def parallelReceipt {Γ : Ctx sig} (term : Term sig Γ Srt.pr) :
    Receipt model Op.par parallelInputs (project term) where
  arguments := .cons (project term) (.cons (project null) .nil)
  admitted := ⟨trivial, trivial, trivial⟩
  output := (constructor_read Op.par (.cons term (.cons null .nil))).trans
    (Quotient.sound (parallel_null_equation term))

/-- Consequently the equation-compatible parallel image covers every
process class; it cannot be an exclusive parse-root classifier. -/
theorem parallel_image_all {Γ : Ctx sig} (value : TermQ rhoSourceE Γ Srt.pr) :
    (image model Op.par parallelInputs).holds value := by
  induction value using Quotient.inductionOn with
  | _ term => exact ⟨parallelReceipt term⟩

def outputInputs : Arguments model (sig.arity Op.out) :=
  .cons (top model Srt.nm) (.cons (top model Srt.pr) .nil)

def outputReceipt : Receipt model Op.out outputInputs (project output) where
  arguments := .cons (project chan) (.cons (project nilP) .nil)
  admitted := ⟨trivial, trivial, trivial⟩
  output := constructor_read Op.out (.cons chan (.cons nilP .nil))

/-- The semantic output and parallel images overlap on a real output. -/
theorem constructor_images_overlap :
    (image model Op.out outputInputs).holds (project output) ∧
      (image model Op.par parallelInputs).holds (project output) :=
  ⟨⟨outputReceipt⟩, parallel_image_all (project output)⟩

theorem output_ne_null : project output ≠ project (null : Term sig [] Srt.pr) := by
  intro equal
  have counts := congrArg count equal
  change (1 : Nat) = 0 at counts
  cases counts

/-- Saturation is nontrivial: null's image does not contain an output. -/
theorem output_not_null_image :
    ¬ (image model Op.nil Arguments.nil).holds (project output) := by
  rintro ⟨⟨arguments, _admitted, result⟩⟩
  cases arguments
  have nullRead := constructor_read (Γ := []) Op.nil FamilyArgs.nil
  exact output_ne_null (nullRead.symm.trans result).symm

/-- Reversing the supplied children changes the receipt while the unit and
commutative equations retain the same output class. -/
def reversedOutputReceipt : Receipt model Op.par parallelInputs (project output) where
  arguments := .cons (project null) (.cons (project output) .nil)
  admitted := ⟨trivial, trivial, trivial⟩
  output := (constructor_read Op.par (.cons null (.cons output .nil))).trans
    (Quotient.sound (eqClosure_of_axiom_inclusion RhoSourceEquationModel.acu_in_source
      (par_left_unit output)))

def firstChild {Γ : Ctx sig} :
    FamilyArgs sig (TermQ rhoSourceE) [([], Srt.pr), ([], Srt.pr)] Γ →
      TermQ rhoSourceE Γ Srt.pr
  | .cons first _ => first

/-- Equal observations do not erase independently supplied argument order. -/
theorem same_output_distinct_receipts : parallelReceipt output ≠ reversedOutputReceipt := by
  intro equal
  have firstEqual := congrArg
    (fun receipt : Receipt model Op.par parallelInputs (project output) =>
      firstChild receipt.arguments) equal
  exact output_ne_null firstEqual

def positiveParallelInputs : Arguments model (sig.arity Op.par) :=
  .cons (positive Srt.pr) (.cons (top model Srt.pr) .nil)

private theorem positiveParallelArguments : ∀ {Γ : Ctx sig}
    (arguments : FamilyArgs sig (TermQ rhoSourceE) [([], Srt.pr), ([], Srt.pr)] Γ),
    positiveParallelInputs.Holds arguments → 0 < countArguments arguments
  | _, .cons first (.cons second .nil), admitted => by
      change 0 < count first ∧ True ∧ True at admitted
      change 0 < count first + (count second + 0)
      omega

/-- The refined parallel operation uses the actual first argument's
nonconstant certificate, with the full second argument retained. -/
theorem positive_parallel_iff {Γ : Ctx sig} (value : TermQ rhoSourceE Γ Srt.pr) :
    (image model Op.par positiveParallelInputs).holds value ↔
      (positive Srt.pr).holds value := by
  constructor
  · rintro ⟨receipt⟩
    have argumentPositive := positiveParallelArguments receipt.arguments receipt.admitted
    have reading := (count_operation Op.par receipt.arguments).symm.trans
      (congrArg count receipt.output)
    simp only [outputHeadCount, Nat.zero_add] at reading
    change 0 < count value
    omega
  · intro admitted
    induction value using Quotient.inductionOn with
    | _ term =>
      refine ⟨⟨.cons (project term) (.cons (project null) .nil),
        ⟨admitted, trivial, trivial⟩, ?_⟩⟩
      exact (constructor_read Op.par (.cons term (.cons null .nil))).trans
        (Quotient.sound (parallel_null_equation term))

theorem null_fails_refined_parallel :
    ¬ (image model Op.par positiveParallelInputs).holds (project (null : Term sig [] Srt.pr)) :=
  fun admitted => null_not_positive ((positive_parallel_iff _).mp admitted)

/-- Input's continuation lives under its declared name binder. -/
def boundOutput : Term sig [Srt.nm] Srt.pr := weaken output

def boundNull : Term sig [Srt.nm] Srt.pr := .op Op.nil .nil

def inputWithOutput : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan (.cons boundOutput .nil))

def inertInput : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan (.cons boundNull .nil))

def inputPredicates : Arguments model (sig.arity Op.inp) :=
  .cons (top model Srt.nm) (.cons (positive Srt.pr) .nil)

/-- The constructor receipt contains the actual bound continuation and its
nonconstant native certificate, rather than a first-order stand-in. -/
def inputReceipt : Receipt model Op.inp inputPredicates (project inputWithOutput) where
  arguments := .cons (project chan) (.cons (project boundOutput) .nil)
  admitted := by
    refine ⟨trivial, ?_, trivial⟩
    simpa only [positive, project, count_mk, boundOutput, weaken,
      outputCount_rename, output_count] using Nat.zero_lt_one
  output := constructor_read Op.inp (.cons chan (.cons boundOutput .nil))

private theorem positiveInputArguments : ∀ {Γ : Ctx sig}
    (arguments : FamilyArgs sig (TermQ rhoSourceE) [([], Srt.nm), ([Srt.nm], Srt.pr)] Γ),
    inputPredicates.Holds arguments → 0 < countArguments arguments
  | _, .cons channel (.cons continuation .nil), admitted => by
      change True ∧ 0 < count continuation ∧ True at admitted
      change 0 < count channel + (count continuation + 0)
      omega

/-- An independently formed inert input cannot supply the bound output
certificate required by this constructor predicate. -/
theorem inert_input_fails_refinement :
    ¬ (image model Op.inp inputPredicates).holds (project inertInput) := by
  rintro ⟨receipt⟩
  have argumentPositive := positiveInputArguments receipt.arguments receipt.admitted
  have reading := (count_operation Op.inp receipt.arguments).symm.trans
    (congrArg count receipt.output)
  simp only [outputHeadCount, Nat.zero_add] at reading
  change countArguments receipt.arguments = 0 at reading
  omega

end Mettapedia.OSLF.Binding.RhoEquationConstructorControls
