import Mettapedia.TypeTheory.DisplayedEvidence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
import Mettapedia.OSLF.NativeTypes.Executable.ExploredCompiled
import Mettapedia.OSLF.NativeTypes.Executable.FiniteModelKripke
import Mettapedia.OSLF.Framework.BackwardSearchPlans

/-!
# One verdict type

Every strategy's answer becomes a displayed status about a proposition (`Verdict`): suspended,
established with a proof, or refuted with a reason and a proof of the negation. Soundness is part of the
type, and the precision order of `DisplayedEvidence` is the order of refinement by more budget.

- **Proof-carrying outcomes** (`Reference.Core.Outcome`, shared by the finite checkers, the explored
  graphs and the finite μ-calculus) map in exactly (`ofOutcome`, `ofOutcome_answer`).
- **`ask`** maps in with its evidence as the reason for a refutation (`ofAsk`).
- **Verdicts that carry no proof** map in through their soundness theorems (`ofChecks`). Instances:
  - the explored-graph verdict (`ofExplored`);
  - backward-search answers (`ofBackward`);
  - finite-model certificates for reachability (`ofCannotReach`);
  - the finite Kripke reading of certificates (`ofKripke`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts

open Mettapedia.TypeTheory.DisplayedEvidence
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Outcome)

/-- **Propositions as a displayed family**: exact evidence for a proposition is a proof of it. -/
def propositions : Family where
  Raw := Prop
  Exact statement := PLift statement

/-- **A verdict about a proposition**: suspended, established with a proof, or refuted with a reason and a
proof of the negation. -/
abbrev Verdict (statement : Prop) := Status propositions String statement

namespace Verdict

variable {statement : Prop}

/-- The Boolean reading of a verdict. -/
def answer : Verdict statement → Option Bool
  | .suspended => none
  | .established _ => some true
  | .refuted _ => some false

theorem holds_of_answer {verdict : Verdict statement} (read : verdict.answer = some true) : statement := by
  cases verdict with
  | suspended => cases read
  | established evidence => exact evidence.down
  | refuted _ => cases read

theorem fails_of_answer {verdict : Verdict statement} (read : verdict.answer = some false) : ¬ statement := by
  cases verdict with
  | suspended => cases read
  | established _ => cases read
  | refuted obstruction => exact fun holds => obstruction.refutes ⟨holds⟩

/-- **A verdict with its soundness theorems**: established when the positive check passes, refuted when
the negative one does, suspended otherwise. -/
def ofChecks (positive negative : Bool) (positiveSound : positive = true → statement)
    (negativeSound : negative = true → ¬ statement) (reason : String) : Verdict statement :=
  if proved : positive = true then .established ⟨positiveSound proved⟩
  else if refuted : negative = true then .refuted ⟨reason, fun evidence => negativeSound refuted evidence.down⟩
  else .suspended

theorem ofChecks_answer (positive negative : Bool) (positiveSound : positive = true → statement)
    (negativeSound : negative = true → ¬ statement) (reason : String) :
    (ofChecks positive negative positiveSound negativeSound reason).answer =
      if positive then some true else if negative then some false else none := by
  unfold ofChecks
  cases positive <;> cases negative <;> rfl

end Verdict

/-! ## Proof-carrying outcomes -/

/-- **An outcome maps in exactly.** -/
def ofOutcome {statement : Prop} : Outcome statement → Verdict statement
  | .proved proof => .established ⟨proof⟩
  | .refuted refutation => .refuted ⟨"refuted", fun evidence => refutation evidence.down⟩
  | .unknown => .suspended

theorem ofOutcome_answer {statement : Prop} (outcome : Outcome statement) :
    (ofOutcome outcome).answer = outcome.answer := by
  cases outcome <;> rfl

/-! ## Asking -/

/-- The reason a refutation gives: its evidence. -/
def describe : Evidence → String
  | .certificate _ => "a finite-model certificate"
  | .exploration rounds => s!"an exploration of {rounds} rounds"
  | .closedRegion rounds => s!"a closed region grown in {rounds} rounds"
  | .canonicalRegion rounds => s!"a closed canonical region grown in {rounds} rounds"
  | .decided => "a certified decider"

/-- **An answer of `ask` as a verdict.** -/
def ofAsk (relEnv : RelationEnv) (signature : Mettapedia.OSLF.Framework.FiniteModels.Signature)
    (language : LanguageDef) (fuel : ℕ) (formula : Formula 0) (term : Pattern)
    (hint : Option CertificateCandidate) (rounds : ℕ) (forms : Option (CanonicalForms relEnv language fuel) := none) :
    Verdict ((referenceStructure relEnv language).sat Env.closed formula term) :=
  match answered : ask relEnv signature language fuel formula term hint rounds forms with
  | .proved _ => .established ⟨ask_proved answered⟩
  | .refuted evidence => .refuted ⟨describe evidence, fun holds => ask_refuted answered holds.down⟩
  | .unknown _ => .suspended

/-! ## Verdicts that carry no proof -/

section Explored

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Complete
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Executable.Explored
open Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled

/-- **The explored-graph verdict**, through its soundness theorems. -/
def ofExplored (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (checked : Predecessors.equationsChecked plan = true) {normal : Pattern → Pattern} {same : Setoid Pattern}
    {good : Pattern → Prop} (abstraction : Abstraction plan bound expected normal same good) {start : Pattern}
    (startGood : good start) (work : ℕ) {n : ℕ} (formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal n)
    (atoms : Atoms same n)
    (budget : ℕ) :
    Verdict (satisfies (transitionSystem (gsltSpan (theory plan bound expected))) atoms.meaning formula start) :=
  Verdict.ofChecks (verdict plan bound expected normal start work formula atoms budget == .proved)
    (verdict plan bound expected normal start work formula atoms budget == .refuted)
    (fun read => verdict_proved checked abstraction startGood (by simpa using read))
    (fun read => verdict_refuted checked abstraction startGood (by simpa using read))
    "the explored graph refutes it"

end Explored

section Backward

open Mettapedia.OSLF.Framework.BackwardSearch

/-- **A backward-search answer**, through its soundness theorems. -/
def ofBackward {X Node : Type} {span : Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan X} {goal : X → Prop}
    (presentation : Presentation span goal Node) {member : Node → X → Bool}
    (sound : ∀ node state, member node state = true → presentation.denote node state)
    (scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler Node) (covering : Presentation.Covering presentation) (fuel : ℕ)
    (state : X)
    (complete : ∀ node, presentation.denote node state → member node state = true) :
    Verdict (Reaches span goal state) :=
  Verdict.ofChecks (presentation.answer scheduler covering member fuel state == .reaches)
    (presentation.answer scheduler covering member fuel state == .cannotReach)
    (fun read => presentation.answer_reaches sound (by simpa using read))
    (fun read => presentation.answer_cannotReach complete (by simpa using read))
    "the search saturated without reaching the goal"

end Backward

section Certificates

open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.Framework.BackwardSearch (Reaches between)
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal)

variable {A : Type} [DecidableEq A] [Fintype A]

/-- **A finite-model certificate for reachability**: it can only refute. -/
def ofCannotReach (certificate : Certificate A) (language : LanguageDef) (goals : List Pattern) (accept : A → Bool)
    (state : Pattern) : Verdict (Reaches (between (languageSpan language) ObjectState) (Goal goals) state) :=
  Verdict.ofChecks false (certificate.cannotReach language goals accept state) (fun never => absurd never (by decide))
    (fun checked => Certificate.cannotReach_of_check checked) "a finite-model certificate"

/-- **The finite Kripke reading of a certificate**: it proves formulas without diamonds and refutes
formulas without boxes. -/
def ofKripke (certificate : Certificate A) (language : LanguageDef) {n : ℕ}
    (formula : Mettapedia.Logic.ModalMuCalculus.Formula Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula.Traversal n)
    (environment : Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus.Environment A n) (state : Pattern) :
    Verdict (Mettapedia.Logic.ModalMuCalculus.satisfies
      (Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula.transitionSystem (between (languageSpan language) ObjectState))
      (Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula.pullEnvironment (value certificate.model) environment.meaning) formula state) :=
  Verdict.ofChecks (certificate.proves language formula environment state)
    (certificate.refutes language formula environment state)
    (fun checked => Certificate.proves_of_check checked) (fun checked => Certificate.refutes_of_check checked)
    "a finite Kripke model"

end Certificates

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
