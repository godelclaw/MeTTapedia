import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EntailmentHigherOrder
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls

/-!
# Controls: judgments at the front door

The language `coins` has sides `H` and `T`, a coin `Toss` that steps to either side, `Show(s) ⇒ s`, and numbers `Z` and
`S(n)`. Its sort of sides has constants only, so it has a fibre. Evaluated by the kernel:

- **open judgments**: `x : Side ⊢ x : H ∨ T` and `x : Side ⊢ Show(x) : ◇(H ∨ T)` over the fibre; `x : Side ⊢ x : H`
  refuted at `T` and `x : Side ⊢ Show(x) : ◇H` at `Show(T)`; `n : Nat ⊢ S(n) : S(Z)` refuted at the valuation
  `n := S(Z)`; the closed `Toss` judged at itself in the context `n : Nat`; substitution of `H` for `x`;
- **entailment**: `H ⊑ H ∨ T` at sides, `H ∨ T ⊑ H` refuted at `T`; `H ⊑ H` by a derivation in higher-order logic, and
  `H ∨ T ⊑ H` has none; under full β, a finite-model certificate proves that the term `(λx. (λy. y) x) ok` is safe,
  and `Err ⊑ safety` is refuted at `Err`;
- **inhabitation**: a coin that steps to `H` (witness `Toss`), and no side has a step (emptiness over the fibre); under
  full β, no term that is `(λx. (λy. y) x) ok` reaches `Err` (emptiness by the certificate);
- **Σ and Π**: `Toss` steps to some side and to each side; `H` is not each side and steps to none; `S(Z)` is built from
  some number (witness `Z`), and is not different from each number (counter-value `S(Z)`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-! ## The language -/

def constantRule (label category : String) : GrammarRule :=
  { label := label, category := category, params := [], syntaxPattern := [] }

def unaryRule (label category parameter parameterType : String) : GrammarRule :=
  { label := label, category := category, params := [.simple parameter (.base parameterType)], syntaxPattern := [] }

def heads : Pattern := .apply "H" []
def tails : Pattern := .apply "T" []
def toss : Pattern := .apply "Toss" []
def zero : Pattern := .apply "Z" []
def succ (n : Pattern) : Pattern := .apply "S" [n]
def showing (side : Pattern) : Pattern := .apply "Show" [side]

/-- `Toss ⇒ target`. -/
def tossRule (name : String) (target : Pattern) : RewriteRule :=
  { name := name, typeContext := [], premises := [], left := toss, right := target, bindings := none }

/-- `Show(s) ⇒ s`. -/
def showRule : RewriteRule :=
  { name := "Reveal", typeContext := [("s", .base "Side")], premises := [], left := showing (.fvar "s"),
    right := .fvar "s", bindings := none }

def coins : LanguageDef :=
  { name := "Coins", types := ["Side", "Coin", "Nat"],
    terms := [constantRule "H" "Side", constantRule "T" "Side", constantRule "Toss" "Coin",
      unaryRule "Show" "Coin" "s" "Side", constantRule "Z" "Nat", unaryRule "S" "Nat" "n" "Nat"],
    equations := [], rewrites := [tossRule "TossH" heads, tossRule "TossT" tails, showRule] }

abbrev Coins : NativeStructure Pattern := FrontStructure RelationEnv.empty coins 2 none

/-- The fibres of the constant sorts. -/
abbrev fibres : (type : TypeExpr) → Option (Fibre Coins type) :=
  constantFibres RelationEnv.empty coins (formsReading none)

def side : TypeExpr := .base "Side"
def coin : TypeExpr := .base "Coin"
def nat : TypeExpr := .base "Nat"
def x : Pattern := .fvar "x"
def n : Pattern := .fvar "n"

/-- `H ∨ T`. -/
def isSide : Formula 0 := .or (.is heads) (.is tails)

/-- The open judgment at the front door, four rounds. -/
def judge (context : Context) (formula : Formula 0) (term : Pattern) (counter : Option (List (String × Pattern)) := none) :
    JudgmentAnswer :=
  askOpen RelationEnv.empty [] coins 2 none fibres context formula term none 4 counter

/-! ## Open judgments -/

theorem side_answer : judge [("x", side)] isSide x = .proved (.instances 2) := by decide +kernel

/-- **`x : Side ⊢ x : H ∨ T`**, over the fibre of sides. -/
theorem side_judged : OpenHolds Coins [("x", side)] isSide x := askOpen_proved side_answer

theorem heads_answer : judge [("x", side)] (.is heads) x = .refuted (.atInstance tails (.closedRegion 4)) := by
  decide +kernel

/-- **`x : Side ⊢ x : H` fails**, at `T`. -/
theorem heads_not_judged : ¬ OpenHolds Coins [("x", side)] (.is heads) x := askOpen_refuted heads_answer

theorem show_answer : judge [("x", side)] (.possibly .any isSide) (showing x) = .proved (.instances 2) := by
  decide +kernel

/-- **`x : Side ⊢ Show(x) : ◇(H ∨ T)`.** -/
theorem show_judged : OpenHolds Coins [("x", side)] (.possibly .any isSide) (showing x) := askOpen_proved show_answer

theorem show_heads_answer :
    judge [("x", side)] (.possibly .any (.is heads)) (showing x) = .refuted (.atInstance (showing tails) (.closedRegion 4)) := by
  decide +kernel

/-- **`x : Side ⊢ Show(x) : ◇H` fails**, at `Show(T)`. -/
theorem show_heads_not_judged : ¬ OpenHolds Coins [("x", side)] (.possibly .any (.is heads)) (showing x) :=
  askOpen_refuted show_heads_answer

theorem successor_answer :
    judge [("n", nat)] (.is (succ zero)) (succ n) (some [("n", succ zero)]) =
      .refuted (.atInstance (succ (succ zero)) (.closedRegion 4)) := by
  decide +kernel

/-- **`n : Nat ⊢ S(n) : S(Z)` fails**, at the valuation `n := S(Z)`; numbers have no fibre. -/
theorem successor_not_judged : ¬ OpenHolds Coins [("n", nat)] (.is (succ zero)) (succ n) :=
  askOpen_refuted successor_answer

theorem successor_open : judge [("n", nat)] (.is (succ (succ zero))) (succ n) (some [("n", succ zero)]) = .unknown := by
  decide +kernel

theorem closed_answer : judge [("n", nat)] (.possibly .any (.is heads)) toss = .proved (.closed (.exploration 4)) := by
  decide +kernel

/-- **A closed term is judged at itself**: `n : Nat ⊢ Toss : ◇H`. -/
theorem closed_judged : OpenHolds Coins [("n", nat)] (.possibly .any (.is heads)) toss := askOpen_proved closed_answer

/-- The assignment of a value to `x`. -/
def pick (value : Pattern) : String → Pattern := fun name => if name = "x" then value else .fvar name

theorem heads_value : ClosedValue heads ∧ Coins.typed heads side :=
  (constantFibre RelationEnv.empty coins (formsReading none) "Side" (by decide) (by decide)).sound heads (by decide)

/-- **Substitution**: `H` for `x` takes `x : Side ⊢ Show(x) : ◇(H ∨ T)` to `⊢ Show(H) : ◇(H ∨ T)`. -/
theorem show_heads_judged : OpenHolds Coins [] (.possibly .any isSide) (showing heads) := by
  have substitution : Substitution Coins [] [("x", side)] (pick heads) := by
    refine ⟨fun entry member => ?_, fun assignment valuation => ⟨fun entry member => ?_, fun name outside => ?_⟩⟩
    · rcases List.mem_singleton.mp member with rfl
      exact heads_value.1.2
    · rcases List.mem_singleton.mp member with rfl
      simp only [restrictTo, Context.names, List.map_cons, List.map_nil, List.mem_singleton, if_true, pick]
      rw [freeSubst_of_closed heads_value.1.2]
      exact heads_value
    · simp only [restrictTo, outside, if_false]
  exact openHolds_subst show_judged (by decide) substitution

/-! ## Entailment -/

/-- Entailment at a type at the front door, four rounds. -/
def entails (type : TypeExpr) (premise conclusion : Formula 0) (separating : Option Pattern := none) : JudgmentAnswer :=
  askEntails RelationEnv.empty [] coins 2 none fibres type premise conclusion none 4 none separating

theorem heads_side_answer : entails side (.is heads) isSide = .proved (.reduced (.instances 2)) := by decide +kernel

/-- **`H ⊑ H ∨ T` at sides.** -/
theorem heads_side : Entails Coins side (.is heads) isSide := askEntails_proved heads_side_answer

theorem side_heads_answer :
    entails side isSide (.is heads) = .refuted (.reduced (.atInstance tails (.closedRegion 4))) := by decide +kernel

/-- **`H ∨ T ⊑ H` fails at sides**, separated by `T`. -/
theorem side_not_heads : ¬ Entails Coins side isSide (.is heads) := askEntails_refuted side_heads_answer

/-- **`H ⊑ H`, by a derivation in higher-order logic.** -/
theorem heads_heads : Entails Coins side (.is heads) (.is heads) :=
  entails_of_entailmentTheorem (entailmentFormula_refl _) Coins side

/-- **`H ∨ T ⊑ H` has no derivation in higher-order logic**: it is refuted at `T`. -/
theorem side_heads_underivable :
    ¬ Mettapedia.Logic.HOL.Derivation.Theorem HigherOrder.Constant (entailmentFormula isSide (.is heads)) :=
  fun derived => side_not_heads (entails_of_entailmentTheorem derived Coins side)

section Certificate

open Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls (fullLambda lambdaSignature underBinder app ok err)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateControls (safety reachesErr)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls (found)

abbrev FullLambda : NativeStructure Pattern := FrontStructure RelationEnv.empty fullLambda 2 none

def term : TypeExpr := .base "Term"

/-- Entailment under full β at the front door, with the finder's certificate. -/
def lambdaEntails (premise conclusion : Formula 0) (separating : Option Pattern := none) : JudgmentAnswer :=
  askEntails RelationEnv.empty lambdaSignature fullLambda 2 none (fun _ => none) term premise conclusion none 4 (some found)
    separating

theorem safe_answer : lambdaEntails (.is (app underBinder ok)) safety = .proved (.certificate found) := by decide +kernel

/-- **A finite-model certificate proves an entailment**: the term `(λx. (λy. y) x) ok` is safe. -/
theorem safe_entailed : Entails FullLambda term (.is (app underBinder ok)) safety := askEntails_proved safe_answer

theorem err_answer : lambdaEntails (.is err) safety (some err) = .refuted (.reduced (.atInstance err (.exploration 4))) := by
  decide +kernel

/-- **`Err ⊑ safety` fails**, separated by `Err`; the certificate does not prove it. -/
theorem err_not_entailed : ¬ Entails FullLambda term (.is err) safety := askEntails_refuted err_answer

theorem unsafe_answer :
    askInhabited RelationEnv.empty lambdaSignature fullLambda 2 none (fun _ => none) term
      (.and (.is (app underBinder ok)) reachesErr) none 4 [] (some found) = .refuted (.reduced (.certificate found)) := by
  decide +kernel

/-- **Emptiness by certificate**: no term that is `(λx. (λy. y) x) ok` reaches `Err`. -/
theorem unsafe_empty : ¬ Inhabited FullLambda term (.and (.is (app underBinder ok)) reachesErr) :=
  askInhabited_refuted unsafe_answer

end Certificate

/-! ## Inhabitation -/

def inhabited (type : TypeExpr) (formula : Formula 0) (candidates : List Pattern) : JudgmentAnswer :=
  askInhabited RelationEnv.empty [] coins 2 none fibres type formula none 4 candidates

theorem coin_answer : inhabited coin (.possibly .any (.is heads)) [toss] = .proved (.atInstance toss (.exploration 4)) := by
  decide +kernel

/-- **Some coin steps to `H`**: `Toss`. -/
theorem coin_inhabited : Inhabited Coins coin (.possibly .any (.is heads)) := askInhabited_proved coin_answer

theorem side_step_answer : inhabited side (.possibly .any .top) [] = .refuted (.reduced (.reduced (.instances 2))) := by
  decide +kernel

/-- **No side has a step**, by emptiness over the fibre. -/
theorem side_step_empty : ¬ Inhabited Coins side (.possibly .any .top) := askInhabited_refuted side_step_answer

/-! ## Σ and Π -/

/-- Steps to the value. -/
def stepsTo (value : Pattern) : Formula 0 := .possibly .any (.is value)

theorem toss_some_answer :
    askSigma RelationEnv.empty [] coins 2 none fibres side stepsTo toss none 4 = .proved (.compiled (.exploration 4)) := by
  decide +kernel

/-- **`Toss` steps to some side.** -/
theorem toss_some : SigmaHolds Coins side stepsTo toss := askSigma_proved toss_some_answer

theorem toss_each_answer :
    askPi RelationEnv.empty [] coins 2 none fibres side stepsTo toss none 4 = .proved (.compiled (.exploration 4)) := by
  decide +kernel

/-- **`Toss` steps to each side.** -/
theorem toss_each : PiHolds Coins side stepsTo toss := askPi_proved toss_each_answer

theorem heads_each_answer :
    askPi RelationEnv.empty [] coins 2 none fibres side (fun value => .is value) heads none 4 =
      .refuted (.compiled (.closedRegion 4)) := by
  decide +kernel

/-- **`H` is not each side.** -/
theorem heads_not_each : ¬ PiHolds Coins side (fun value => .is value) heads := askPi_refuted heads_each_answer

theorem heads_some_answer :
    askSigma RelationEnv.empty [] coins 2 none fibres side stepsTo heads none 4 = .refuted (.compiled (.closedRegion 4)) := by
  decide +kernel

/-- **`H` steps to no side.** -/
theorem heads_steps_nowhere : ¬ SigmaHolds Coins side stepsTo heads := askSigma_refuted heads_some_answer

/-- Built by `S` from the value. -/
def successorOf (value : Pattern) : Formula 0 := .built "S" (.cons (.is value) .nil)

theorem one_answer :
    askSigma RelationEnv.empty [] coins 2 none fibres nat successorOf (succ zero) none 4 [zero] =
      .proved (.atInstance zero (.closedRegion 4)) := by
  decide +kernel

/-- **`S(Z)` is built from some number**, the witness `Z`; numbers have no fibre. -/
theorem one_successor : SigmaHolds Coins nat successorOf (succ zero) := askSigma_proved one_answer

theorem different_answer :
    askPi RelationEnv.empty [] coins 2 none fibres nat (fun value => .isNot value) (succ zero) none 4 [zero, succ zero] =
      .refuted (.atInstance (succ zero) (.exploration 4)) := by
  decide +kernel

/-- **`S(Z)` is not different from each number**: the counter-value `S(Z)`. -/
theorem not_different : ¬ PiHolds Coins nat (fun value => .isNot value) (succ zero) := askPi_refuted different_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls
