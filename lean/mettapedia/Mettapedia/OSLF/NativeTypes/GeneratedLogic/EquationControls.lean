import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls

/-!
# Controls: certificates for a language with equations

A ρ-calculus whose parallel composition is a bag with a flattening algebra and unit `Nil`, and with the
authored equation `@(*N) = N`. It is not equation-free: terms are read modulo the bag laws, the algebra
laws and the authored equation.

- **The cleanliness model respects the equations** (`laws_hold`): its joins are left-commutative and
  associative, `Nil` is the empty bag and a left identity, each process is its own singleton, and
  quoting undoes dropping. So the certificate proves that the safe process never reaches `Err`, modulo
  every equation (`safe_modulo_equations`).
- **A model that does not undo quoting fails** (`careless_refused`), and one whose empty bag is dirty
  fails (`dirty_unit_refused`). Neither proves anything.
- **The leaky process reaches `Err`**, and the certificate is silent there (`leaky_silent`).
- **A conditional equation**: `@(*N) = N` when `x` is fresh in `N`. The model's sides agree under every
  valuation, so the premise needs no check, and the certificate proves the same safety
  (`conditional_laws_hold`, `safe_modulo_conditional`). The careless model is refused for it as well
  (`careless_refused_conditional`): a premise does not excuse sides that disagree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.FiniteModels (Certificate)
open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
  (rhoTerms rhoComm rhoCertificate rhoModel rhoSafe rhoLeaky quote drop errRho Cleanness)

/-- The parallel bag declares a flattening algebra with unit `Nil`. -/
def termsWithLaws : List GrammarRule :=
  rhoTerms.map fun rule =>
    if rule.label = "Par" then { rule with algebra? := some { flatten := true, unit := some "Nil" } } else rule

/-- `@(*N) = N`. -/
def quoteDrop : Equation :=
  { name := "QuoteDrop", typeContext := [], premises := [], left := quote (drop (.fvar "N")), right := .fvar "N" }

def rhoWithLaws : LanguageDef :=
  { name := "RhoWithLaws", types := ["Name", "Proc"], terms := termsWithLaws, equations := [quoteDrop],
    rewrites := [rhoComm] }

theorem not_equation_free : rhoWithLaws.isEquationFree = false := by decide

abbrev RhoWithLaws : NativeStructure Pattern := referenceStructure RelationEnv.empty rhoWithLaws

/-- No run reaches `Err`. -/
def neverErrs : Formula 0 := .nu (.and (.isNot errRho) (.necessarily .any (.var 0)))

/-- **The cleanliness model respects the equations.** -/
theorem laws_hold : Certificate.equationsValid rhoCertificate rhoWithLaws = true := by decide +kernel

/-- **The safe process never reaches `Err`, modulo every equation.** -/
theorem safe_modulo_equations : RhoWithLaws.sat Env.closed neverErrs rhoSafe :=
  proves_sound (certificate := rhoCertificate) (by decide +kernel)

/-- A model in which dropping a name gives a dirty process. -/
def careless : Certificate Cleanness :=
  { rhoCertificate with model := { rhoModel with
      operation := fun label arguments => if label = "Drop" then .dirty else rhoModel.operation label arguments } }

/-- **It does not undo quoting**, so it fails the equation check and proves nothing. -/
theorem careless_refused :
    Certificate.equationsValid careless rhoWithLaws = false ∧ proves careless rhoWithLaws neverErrs rhoSafe = false := by
  constructor <;> decide +kernel

/-- A model whose empty bag is dirty. -/
def dirtyUnit : Certificate Cleanness :=
  { rhoCertificate with model := { rhoModel with collectionUnit := fun _ => .dirty } }

/-- **Its empty bag is not `Nil`**, so it fails the algebra laws. -/
theorem dirty_unit_refused : Certificate.equationsValid dirtyUnit rhoWithLaws = false := by decide +kernel

/-- **The certificate is silent at the leaky process.** -/
theorem leaky_silent : proves rhoCertificate rhoWithLaws neverErrs rhoLeaky = false := by decide +kernel

/-! ## A conditional equation -/

/-- `@(*N) = N` when `x` is fresh in `N`. -/
def quoteDropFresh : Equation :=
  { quoteDrop with name := "QuoteDropFresh", premises := [.freshness { varName := "x", term := .fvar "N" }] }

def rhoConditional : LanguageDef := { rhoWithLaws with name := "RhoConditional", equations := [quoteDropFresh] }

abbrev RhoConditional : NativeStructure Pattern := referenceStructure RelationEnv.empty rhoConditional

/-- **The cleanliness model respects the conditional equation.** -/
theorem conditional_laws_hold : Certificate.equationsValid rhoCertificate rhoConditional = true := by decide +kernel

/-- **So the safe process never reaches `Err` modulo it.** -/
theorem safe_modulo_conditional : RhoConditional.sat Env.closed neverErrs rhoSafe :=
  proves_sound (certificate := rhoCertificate) (by decide +kernel)

/-- **The careless model is refused for it too.** -/
theorem careless_refused_conditional : Certificate.equationsValid careless rhoConditional = false := by decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquationControls
