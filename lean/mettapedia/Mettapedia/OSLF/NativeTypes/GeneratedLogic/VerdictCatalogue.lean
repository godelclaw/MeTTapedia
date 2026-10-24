import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SyntacticEmbeddings
import Mettapedia.OSLF.NativeTypes.Semantics.Checking
import Mettapedia.OSLF.NativeTypes.Decision.Admission
import Mettapedia.OSLF.Framework.BackwardNarrowing
import Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusSession
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Query
import Mettapedia.OSLF.NativeTypes.Generation.BindingNativeSearch

/-!
# The verdict catalogue

The remaining verdict types of the tree, each read as a verdict about the proposition it decides.

- **Verdicts that carry proofs** map exactly: checking verdicts (`ofChecking`) and admission verdicts
  (`ofAdmission`). Refusals, unresolved cubes and unknowns make no claim.
- **Verdicts with soundness theorems for both answers** map through them: backward past boxes
  (`ofPastBox`) and MM2 batches (`ofMM2`).
- **Verdicts with a soundness theorem for the positive answer only**: a negative answer is a rejected
  certificate or a missing request, not a refutation, so it makes no claim. These are finite focus
  sessions (`ofFocusSession`), discovery sessions (`ofDiscovery`), native queries (`ofNativeQuery`) and
  the OSLF formula checker (`ofOSLFCheck`).
- **The OSLF checker speaks about generated formulas** (`ofOSLFCheckGenerated`): its verdict carries
  over to the generated formula its formula embeds as, along the embedding's exactness
  (`Verdict.transport`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **A verdict carries over along an equivalence.** -/
def Verdict.transport {first second : Prop} (same : first ↔ second) : Verdict first → Verdict second
  | .suspended => .suspended
  | .established evidence => .established ⟨same.mp evidence.down⟩
  | .refuted obstruction => .refuted ⟨obstruction.reason, fun evidence => obstruction.refutes ⟨same.mpr evidence.down⟩⟩

theorem Verdict.transport_answer {first second : Prop} (same : first ↔ second) (verdict : Verdict first) :
    (Verdict.transport same verdict).answer = verdict.answer := by
  cases verdict <;> rfl

/-! ## Verdicts that carry proofs -/

/-- **A checking verdict**: proofs and refutations map exactly. -/
def ofChecking {statement : Prop} : Mettapedia.OSLF.NativeTypes.Semantics.Checking.Verdict statement → Verdict statement
  | .proof certificate => .established ⟨certificate⟩
  | .refutation certificate => .refuted ⟨"refuted", fun evidence => certificate evidence.down⟩
  | .unknown | .refused _ | .illFormed _ | .refusedPossibility | .rejectedCube => .suspended

/-- **An admission verdict**: its semantic outcome maps exactly. -/
def ofAdmission {statement : Prop} : Mettapedia.OSLF.NativeTypes.Decision.Admission.Verdict statement → Verdict statement
  | .semantic result => ofOutcome result
  | .refused _ | .rejectedCube | .unresolvedCube => .suspended

/-! ## Verdicts with soundness theorems for both answers -/

section PastBox

open Mettapedia.Logic.LP (Term)
open Mettapedia.Logic.LP.FirstOrderRewriting (Equation)
open Mettapedia.OSLF.Framework.BackwardNarrowing (Signature span pastBox pastBox_proved pastBox_refuted Ground Instance)
open Mettapedia.OSLF.Framework.DerivedModalities (derivedBox)

variable {C F : Type} {arity : F → ℕ} [DecidableEq C] [DecidableEq F]

/-- **A backward past box** at a ground term: proved when every predecessor is an instance of a pattern,
refuted by a ground predecessor that is an instance of none. -/
def ofPastBox (rules : List (Equation (Signature C F arity))) {term : Term (Signature C F arity)} (ground : Ground term)
    (types : List (Term (Signature C F arity))) :
    Verdict (derivedBox (span rules) (fun state => ∃ type ∈ types, Instance type state) term) :=
  Verdict.ofChecks (decide (pastBox rules term types = .proved)) (decide (pastBox rules term types = .refuted))
    (fun read => pastBox_proved ground (of_decide_eq_true read))
    (fun read => pastBox_refuted ground (of_decide_eq_true read))
    "a ground predecessor is an instance of no pattern"

end PastBox

section MM2

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.NativeTypes.Consumers.MM2Batch (Profile Inhabits check check_proved check_refuted CheckResult)

/-- Whether a batch check proved its target. -/
def mm2Proved : CheckResult → Bool
  | .proved _ _ => true
  | _ => false

/-- Whether a batch check refuted its target. -/
def mm2Refuted : CheckResult → Bool
  | .refuted => true
  | _ => false

/-- **An MM2 batch check**, through its soundness theorems. -/
def ofMM2 (profile : Profile) (scope : ProgrammableSpaceMM2.Scope) (current target : List Atom)
    (checkpoint : ProgrammableSpaceMM2Resumable.Checkpoint) (grant : ℕ) :
    Verdict (Inhabits profile scope target (current, .matching checkpoint)) :=
  Verdict.ofChecks (mm2Proved (check profile scope current target checkpoint grant))
    (mm2Refuted (check profile scope current target checkpoint grant))
    (fun read => by
      cases checked : check profile scope current target checkpoint grant with
      | proved receipt spent => exact (check_proved profile scope current target checkpoint grant spent receipt checked).1
      | refuted => simp [checked, mm2Proved] at read
      | unknown _ => simp [checked, mm2Proved] at read)
    (fun read => check_refuted profile scope current target checkpoint grant (by
      cases checked : check profile scope current target checkpoint grant <;> simp_all [mm2Refuted]))
    "the completed batch reaches another store"

end MM2

/-! ## Verdicts with a positive soundness theorem only -/

section Focus

open Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking (Parameters Session Witness)
open Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusMeaning (Inhabits)

/-- **A finite focus session**: proved through its soundness theorem; a rejected certificate makes no
claim. -/
def ofFocusSession {installed : Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined.Installed} {index : installed.Index} {ambient : List String}
    {parameters : Parameters installed index ambient} {focus : Pattern} {certificate : List Witness}
    (session : Session parameters focus certificate) : Verdict (Inhabits parameters.meaning focus) :=
  Verdict.ofChecks (decide (session.verdict = .proved)) false (fun read => session.proved (of_decide_eq_true read))
    (fun never => absurd never Bool.false_ne_true) "unreachable"

end Focus

section Discovery

/-- **A discovery session**: proved through its soundness theorem; a missing request makes no claim. -/
def ofDiscovery {installed : Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined.Installed} {ambient : List String}
    {question : Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusQuery.Question installed ambient}
    (session : Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.Session question) :
    Verdict question.Meaning :=
  Verdict.ofChecks (decide (session.verdict = .proved)) false (fun read => session.proved (of_decide_eq_true read))
    (fun never => absurd never Bool.false_ne_true) "unreachable"

end Discovery

section Native

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

/-- **A native query**: proved through its soundness theorem; a refused vocabulary or an unfinished
search makes no claim. -/
def ofNativeQuery (installed : Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed)
    (judgment : Judgment installed.symbols) (budget : ℕ) :
    Verdict (installed.logic.permits judgment ∧
      ∃ certificate, Mettapedia.OSLF.NativeTypes.Generation.NativeLogic.CertificatePermitted installed.logic certificate ∧
        ∃ derivation : Derivation installed.signature judgment,
          Mettapedia.OSLF.NativeTypes.Certificates.Refinement.erase derivation = certificate) :=
  Verdict.ofChecks (decide (installed.queryNative judgment budget = .proved)) false
    (fun read => installed.queryNative_proved judgment budget (of_decide_eq_true read))
    (fun never => absurd never Bool.false_ne_true) "unreachable"

end Native

section OSLF

open Mettapedia.OSLF.Formula (OSLFFormula AtomCheck AtomSem check check_sat_sound sem)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings (syntactic ofOSLF consistent Agrees sat_ofOSLF)

/-- **The OSLF formula checker**: `sat` through its soundness theorem; `unsat` and `unknown` make no claim. -/
def ofOSLFCheck {relation : Pattern → Pattern → Prop} {step : Pattern → List Pattern} {atomCheck : AtomCheck}
    {atoms : AtomSem} (atomsSound : ∀ atom pattern, atomCheck atom pattern = true → atoms atom pattern)
    (stepsSound : ∀ pattern next, next ∈ step pattern → relation pattern next) (fuel : ℕ) (pattern : Pattern)
    (formula : OSLFFormula) : Verdict (sem relation atoms formula pattern) :=
  Verdict.ofChecks (decide (check step atomCheck fuel pattern formula = .sat)) false
    (fun read => check_sat_sound atomsSound stepsSound (of_decide_eq_true read))
    (fun never => absurd never Bool.false_ne_true) "unreachable"

/-- **The OSLF checker's verdict about the generated formula** its formula embeds as, for a closed
formula whose scope variables occur at the polarity of their binders. -/
def ofOSLFCheckGenerated {m : ℕ} {positive negative : String → Fin m} {relation : Pattern → Pattern → Prop}
    {step : Pattern → List Pattern} {atomCheck : AtomCheck} {atoms : AtomSem}
    (atomsSound : ∀ atom pattern, atomCheck atom pattern = true → atoms atom pattern)
    (stepsSound : ∀ pattern next, next ∈ step pattern → relation pattern next) (fuel : ℕ) (pattern : Pattern)
    (formula : OSLFFormula) (closed : OSLFFormula.closedAt 0 formula = true)
    (positiveFormula : consistent (fun _ => true) true formula = true) {env : Env Pattern (m + 0)}
    (agrees : Agrees positive negative atoms Mettapedia.OSLF.Formula.ScopeEnv.empty (fun _ => true) 0 env) :
    Verdict ((syntactic relation).sat env (ofOSLF positive negative 0 true formula) pattern) :=
  Verdict.transport (sat_ofOSLF relation atoms formula closed positiveFormula agrees pattern).symm
    (ofOSLFCheck atomsSound stepsSound fuel pattern formula)

end OSLF

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
