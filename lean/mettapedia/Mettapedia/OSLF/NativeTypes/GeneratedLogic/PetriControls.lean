import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Resumption
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# Controls: Petri nets modulo their bag laws

Three authored presentations whose markings are bags of places. Their bag laws make the order of a marking
immaterial. Each module file is loaded and elaborated to its core, which is the literal language below
(`petri_core`, `guarded_core`, `inspected_core`).

**The Petri net** (`petriCore`): places `A`, `B`, `C` and `D`, and two rules on whole markings,
`{A, B, ...rest} ⇒ {C, D, ...rest}` and `{C, ...rest} ⇒ {A, ...rest}`.
- Canonical forms sort every bag (`petriForms`): the language has no authored equation, no collection
  algebra and no premise (`BagForms.forms`).
- Verdicts from closed canonical regions:
  - `{A, B}` steps (`ab_steps`), and `{B, A}` is `{A, B}` (`ba_is_ab`);
  - `{A, D}` is stuck (`ad_stuck`);
  - `{A, B}` takes two steps in a row (`ab_two_steps`) and never three (`ab_no_three_steps`);
  - some run from `{A, B}` reaches a stuck marking (`ab_reaches_deadlock`);
  - every marking reachable from `{A, B}` is `{A, B}`, `{C, D}` or `{A, D}` (`ab_reachable_markings`).
- Counting is modulo the bag laws: `{A, C, A, B}` has three steps, to three different presentations
  (`acab_three_steps`), and two results (`acab_two_results`, `acab_not_three_results`). Both ways of
  selecting an `A` lead to the same marking.
- The front door, given the canonical forms, proves that `{A, B}` steps and refutes that `{A, D}` does
  (`ask_ab_steps`, `ask_ad_stuck`). Without them it leaves `{A, D}` open (`ask_ad_open_without_forms`): the
  bag laws are equations, so a closed region read as written gives no verdict.

**The guarded workflow** (`guardedCore`): a workflow holds a marking of `A`s and `B`s, and
`workflow {A, ...rest} ⇒ workflow {B, ...rest}` fires when the relation `permit()` holds. A guard reads no
binding, so the same canonical forms are coherent in every relation environment (`guardedForms`).
- With `permit()` (`permitted`): `workflow {A, B, A}` has two steps, by the two ways of selecting an `A`, to
  different presentations of one marking (`aba_two_steps`), so it has exactly one result
  (`aba_one_result`); every run reaches `workflow {B, B, B}` (`aba_reaches_bbb`) in two steps and stops
  there (`aba_no_three_steps`).
- Without it, `workflow {A}` is stuck (`unpermitted_stuck`).
- The reference relation steps where the language authors a rule, and this language authors no congruence,
  so a workflow inside a box does not step (`boxed_stuck`).

**The inspected workflow** (`inspectedCore`): the same rule, fired when `inspect(rest)` holds, a relation
query over the captured rest. Here the relation holds when the rest holds a `B`, read off its canonical
form, so the relation environment respects canonical forms (`inspecting_respects`) and the canonical forms
are coherent (`BagForms.coherentQueries`).
- `workflow {A, B}` steps (`ab_inspected_steps`); `workflow {A, A}` does not (`aa_inspected_stuck`).
- Every run from `workflow {A, B, A}` reaches `workflow {B, B, B}` (`aba_inspected_reaches_bbb`).

**The relabelled workflow** (`relabelledCore`): `workflow {x, ...rest} ⇒ workflow {y, ...rest}` when `next(x, y)`
holds, a query whose second argument is an output: the answer binds `y`, and the right side uses it. The relation
relabels `A` to `B` and `B` to `C`, read off canonical forms, so it respects them (`nexting_respects`).
- Some run from `workflow {A, B}` reaches `workflow {C, C}` (`ab_relabelled_reaches_cc`), and every run from
  `workflow {A, A}` does (`aa_relabelled_reaches_cc`).
- `workflow {C}` does not step: `next` answers nothing for `C` (`c_relabelled_stuck`); no run from `workflow {B}`
  reaches `workflow {A}` (`b_relabelled_not_a`).

**Sets are left out of the domain** (`set_not_admitted`): the set laws identify `{A, A}` with `{A}`
(`set_presentations_same`), yet a pattern `{x, ...rest}` leaves `{A}` in the rest at the first and the empty
set at the second (`set_rests_differ`).
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.Match (matchPattern)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon)

/-- A loaded module's language, elaborated to its core. -/
def core (loaded : Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef) : LanguageDef :=
  ((loaded.toOption.getD (LanguageDef.empty "")).toCore.toOption.map (·.language)).getD (LanguageDef.empty "")

def token (label : String) : Pattern := .apply label []
def marking (items : List Pattern) : Pattern := .collection .hashBag items none
def graph (items : List Pattern) : Pattern := .collection .hashSet items none

def placeRule (label : String) : GrammarRule :=
  { label := label, category := "Place", params := [], syntaxPattern := [.terminal label] }

/-- A bag carrier of places. -/
def bagRule (label category parameter : String) : GrammarRule :=
  { label := label, category := category, params := [.simple parameter (.collection .hashBag (.base "Place"))],
    syntaxPattern := [.terminal "{", .op (.sep parameter "," none), .terminal "}"] }

def restOccurrences (path : List ℕ) : RuleBindingSpec :=
  { dependencies := [("rest", [])],
    occurrences := [{ name := "rest", site := .left, path := path, arguments := [] },
      { name := "rest", site := .right, path := path, arguments := [] }] }

/-! ## Deciding with sorted bags -/

section Deciding

variable {relEnv : RelationEnv} {language : LanguageDef} (noEquations : language.equations = [])
  (noAlgebra : language.hasAlgebraDeclarations = false)
  (guarded : language.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true)
include noEquations noAlgebra guarded

theorem decided_true {formula : Formula 0} {term : Pattern} (rounds : ℕ) (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical relEnv language 2 BagForms.sortBags
      (BagForms.domain language) List.singleton formula term rounds =
      some true) :
    (referenceStructure relEnv language).sat Env.closed formula term :=
  (decideCanonical_sound (BagForms.canonical noEquations noAlgebra) (BagForms.coherent noEquations noAlgebra guarded 2)
    behavioural decided).mp rfl

theorem decided_false {formula : Formula 0} {term : Pattern} (rounds : ℕ) (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical relEnv language 2 BagForms.sortBags
      (BagForms.domain language) List.singleton formula term rounds =
      some false) :
    ¬ (referenceStructure relEnv language).sat Env.closed formula term := fun holds =>
  Bool.false_ne_true ((decideCanonical_sound (BagForms.canonical noEquations noAlgebra)
    (BagForms.coherent noEquations noAlgebra guarded 2) behavioural decided).mpr holds)

end Deciding

section DecidingQueries

variable {relEnv : RelationEnv} {language : LanguageDef} (noEquations : language.equations = [])
  (noAlgebra : language.hasAlgebraDeclarations = false)
  (queried : language.rewrites.all (fun rule => rule.premises.all BagForms.query) = true)
  (respects : BagForms.RespectsCanon relEnv)
include noEquations noAlgebra queried respects

theorem decided_true_queries {formula : Formula 0} {term : Pattern} (rounds : ℕ)
    (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical relEnv language 2 BagForms.sortBags
      (BagForms.domain language) List.singleton formula term rounds =
      some true) :
    (referenceStructure relEnv language).sat Env.closed formula term :=
  (decideCanonical_sound (BagForms.canonical noEquations noAlgebra)
    (BagForms.coherentQueries noEquations noAlgebra queried respects 2) behavioural decided).mp rfl

theorem decided_false_queries {formula : Formula 0} {term : Pattern} (rounds : ℕ)
    (behavioural : formula.behaviouralForward = true)
    (decided : decideCanonical relEnv language 2 BagForms.sortBags
      (BagForms.domain language) List.singleton formula term rounds =
      some false) :
    ¬ (referenceStructure relEnv language).sat Env.closed formula term := fun holds =>
  Bool.false_ne_true ((decideCanonical_sound (BagForms.canonical noEquations noAlgebra)
    (BagForms.coherentQueries noEquations noAlgebra queried respects 2) behavioural decided).mpr holds)

end DecidingQueries

def steps : Formula 0 := .possibly .any .top
def twoSteps : Formula 0 := .possibly .any steps
def threeSteps : Formula 0 := .possibly .any twoSteps

/-! ## The Petri net -/

/-- `{A, B, ...rest} ⇒ {C, D, ...rest}`. -/
def consumeAB : RewriteRule :=
  { name := "ConsumeAB", typeContext := [("rest", .collection .hashBag (.base "Place"))], premises := [],
    left := .collection .hashBag [token "A", token "B"] (some "rest"),
    right := .collection .hashBag [token "C", token "D"] (some "rest"), bindings := some (restOccurrences [2]) }

/-- `{C, ...rest} ⇒ {A, ...rest}`. -/
def recycleC : RewriteRule :=
  { name := "RecycleC", typeContext := [("rest", .collection .hashBag (.base "Place"))], premises := [],
    left := .collection .hashBag [token "C"] (some "rest"),
    right := .collection .hashBag [token "A"] (some "rest"), bindings := some (restOccurrences [1]) }

def petriCore : LanguageDef :=
  { name := "CollectionPetri.Markings", types := [⟨"Place", .ast⟩, ⟨"Marking", .ast⟩],
    terms := [placeRule "A", placeRule "B", placeRule "C", placeRule "D", bagRule "MarkingBag" "Marking" "tokens"],
    equations := [], rewrites := [consumeAB, recycleC] }

theorem petri_no_equations : petriCore.equations = [] := rfl

theorem petri_no_algebra : petriCore.hasAlgebraDeclarations = false := by decide

theorem petri_guarded : petriCore.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true := by decide

/-- Every bag sorted, with its contract, as the front door takes it. -/
def petriForms : CanonicalForms RelationEnv.empty petriCore 2 :=
  BagForms.forms petri_no_equations petri_no_algebra petri_guarded 2

abbrev Petri := referenceStructure RelationEnv.empty petriCore

def ab : Pattern := marking [token "A", token "B"]
def ba : Pattern := marking [token "B", token "A"]
def cd : Pattern := marking [token "C", token "D"]
def ad : Pattern := marking [token "A", token "D"]

/-- Some run reaches a marking with no step. -/
def reachesDeadlock : Formula 0 := .mu (.or (.necessarily .any .bot) (.possibly .any (.var 0)))

/-- Every reachable marking is `{A, B}`, `{C, D}` or `{A, D}`. -/
def onlyThreeMarkings : Formula 0 := .nu (.and (.or (.is ab) (.or (.is cd) (.is ad))) (.necessarily .any (.var 0)))

/-- **`{A, B}` steps.** -/
theorem ab_steps : Petri.sat Env.closed steps ab :=
  decided_true petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **`{B, A}` is `{A, B}`.** -/
theorem ba_is_ab : Petri.sat Env.closed (.is ab) ba :=
  decided_true petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **`{A, D}` is stuck.** -/
theorem ad_stuck : ¬ Petri.sat Env.closed steps ad :=
  decided_false petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **`{A, B}` takes two steps in a row.** -/
theorem ab_two_steps : Petri.sat Env.closed twoSteps ab :=
  decided_true petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **And never three.** -/
theorem ab_no_three_steps : ¬ Petri.sat Env.closed threeSteps ab :=
  decided_false petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **Some run from `{A, B}` reaches a stuck marking.** -/
theorem ab_reaches_deadlock : Petri.sat Env.closed reachesDeadlock ab :=
  decided_true petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **Every marking reachable from `{A, B}` is `{A, B}`, `{C, D}` or `{A, D}`.** -/
theorem ab_reachable_markings : Petri.sat Env.closed onlyThreeMarkings ab :=
  decided_true petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-! ### Counting modulo the bag laws -/

def acab : Pattern := marking [token "A", token "C", token "A", token "B"]

/-- **`{A, C, A, B}` has three steps, to three different presentations**: `{C, D, C, A}` and `{C, D, A, C}`,
by the two ways of selecting an `A`, and `{A, A, A, B}`. -/
theorem acab_three_steps : (stepsAt RelationEnv.empty petriCore 2 acab).map Prod.snd =
    [marking [token "C", token "D", token "C", token "A"], marking [token "C", token "D", token "A", token "C"],
      marking [token "A", token "A", token "A", token "B"]] := by
  decide +kernel

/-- **Modulo the bag laws it has two results.** -/
theorem acab_two_results : Petri.sat Env.closed (.atLeast 2 .forward .any .top) acab :=
  decided_true petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-- **And not three.** -/
theorem acab_not_three_results : ¬ Petri.sat Env.closed (.atLeast 3 .forward .any .top) acab :=
  decided_false petri_no_equations petri_no_algebra petri_guarded 4 rfl (by decide +kernel)

/-! ### The front door -/

def petriSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature :=
  [.operation "A" 0, .operation "B" 0, .operation "C" 0, .operation "D" 0]

theorem ask_ab_steps_answer :
    ask RelationEnv.empty petriSignature petriCore 2 steps ab none 2 (some petriForms) = .proved (.exploration 2) := by
  decide +kernel

/-- **The front door proves that `{A, B}` steps.** -/
theorem ask_ab_steps : Petri.sat Env.closed steps ab := ask_proved ask_ab_steps_answer

theorem ask_ad_stuck_answer :
    ask RelationEnv.empty petriSignature petriCore 2 steps ad none 2 (some petriForms) = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **Given the canonical forms, it refutes that `{A, D}` steps.** -/
theorem ask_ad_stuck : ¬ Petri.sat Env.closed steps ad := ask_refuted ask_ad_stuck_answer

/-- **Without them it leaves the question open.** -/
theorem ask_ad_open_without_forms :
    ask RelationEnv.empty petriSignature petriCore 2 steps ad none 2 = .unknown 2 := by
  decide +kernel

/-! ## The guarded workflow -/

/-- `workflow {A, ...rest} ⇒ workflow {B, ...rest}`, when `permit()` holds. -/
def consumeA : RewriteRule :=
  { name := "ConsumeA", typeContext := [("rest", .collection .hashBag (.base "Place"))],
    premises := [.relationQuery "permit" []],
    left := .apply "Flow" [.collection .hashBag [token "A"] (some "rest")],
    right := .apply "Flow" [.collection .hashBag [token "B"] (some "rest")], bindings := some (restOccurrences [0, 1]) }

def flowRule : GrammarRule :=
  { label := "Flow", category := "Workflow", params := [.simple "marking" (.base "Marking")],
    syntaxPattern := [.terminal "workflow", .nonTerminal "marking"] }

def boxRule : GrammarRule :=
  { label := "Box", category := "Workspace", params := [.simple "workflow" (.base "Workflow")],
    syntaxPattern := [.terminal "box", .nonTerminal "workflow"] }

def guardedCore : LanguageDef :=
  { name := "CollectionNestedGuardedPetri.Workflow",
    types := [⟨"Place", .ast⟩, ⟨"Marking", .ast⟩, ⟨"Workflow", .ast⟩, ⟨"Workspace", .ast⟩],
    terms := [placeRule "A", placeRule "B", bagRule "Tokens" "Marking" "items", flowRule, boxRule], equations := [],
    rewrites := [consumeA] }

theorem guarded_no_equations : guardedCore.equations = [] := rfl

theorem guarded_no_algebra : guardedCore.hasAlgebraDeclarations = false := by decide

theorem guarded_guarded : guardedCore.rewrites.all (fun rule => rule.premises.all BagForms.guard) = true := by decide

/-- `permit()` holds. -/
def permitted : RelationEnv := ⟨fun relation _ => if relation == "permit" then [[]] else []⟩

/-- Every bag sorted, coherent in any relation environment, here the one where `permit()` holds. -/
def guardedForms : CanonicalForms permitted guardedCore 2 :=
  BagForms.forms guarded_no_equations guarded_no_algebra guarded_guarded 2

abbrev Guarded := referenceStructure permitted guardedCore

def workflow (items : List Pattern) : Pattern := .apply "Flow" [marking items]
def box (items : List Pattern) : Pattern := .apply "Box" [workflow items]

def aba : Pattern := workflow [token "A", token "B", token "A"]

/-- **`workflow {A, B, A}` has two steps, by the two ways of selecting an `A`, to different presentations
of one marking.** -/
theorem aba_two_steps : (stepsAt permitted guardedCore 2 aba).map Prod.snd =
    [workflow [token "B", token "B", token "A"], workflow [token "B", token "A", token "B"]] := by
  decide +kernel

/-- **So it has exactly one result.** -/
theorem aba_one_result : Guarded.sat Env.closed (Formula.exactlyOne .forward .any) aba :=
  decided_true guarded_no_equations guarded_no_algebra guarded_guarded 4 rfl (by decide +kernel)

/-- Every run reaches `workflow {B, B, B}`. -/
def reachesBBB : Formula 0 :=
  .mu (.or (.is (workflow [token "B", token "B", token "B"])) (.and (.possibly .any .top) (.necessarily .any (.var 0))))

/-- **Every run from `workflow {A, B, A}` reaches `workflow {B, B, B}`.** -/
theorem aba_reaches_bbb : Guarded.sat Env.closed reachesBBB aba :=
  decided_true guarded_no_equations guarded_no_algebra guarded_guarded 4 rfl (by decide +kernel)

/-- **In two steps, and it stops there.** -/
theorem aba_no_three_steps : Guarded.sat Env.closed twoSteps aba ∧ ¬ Guarded.sat Env.closed threeSteps aba :=
  ⟨decided_true guarded_no_equations guarded_no_algebra guarded_guarded 4 rfl (by decide +kernel),
    decided_false guarded_no_equations guarded_no_algebra guarded_guarded 4 rfl (by decide +kernel)⟩

/-- **Without `permit()`, `workflow {A}` is stuck.** -/
theorem unpermitted_stuck :
    ¬ (referenceStructure RelationEnv.empty guardedCore).sat Env.closed steps (workflow [token "A"]) :=
  decided_false guarded_no_equations guarded_no_algebra guarded_guarded 4 rfl (by decide +kernel)

/-- **A workflow inside a box does not step**: the language authors no congruence. -/
theorem boxed_stuck : ¬ Guarded.sat Env.closed steps (box [token "A"]) :=
  decided_false guarded_no_equations guarded_no_algebra guarded_guarded 4 rfl (by decide +kernel)

/-! ## The inspected workflow -/

/-- The rest's occurrences: in the left side, in the query, and in the right side. -/
def inspectedOccurrences : RuleBindingSpec :=
  { dependencies := [("rest", [])],
    occurrences := [{ name := "rest", site := .left, path := [0, 1], arguments := [] },
      { name := "rest", site := .premise 0 0 0, path := [], arguments := [] },
      { name := "rest", site := .right, path := [0, 1], arguments := [] }] }

/-- `workflow {A, ...rest} ⇒ workflow {B, ...rest}`, when `inspect(rest)` holds. -/
def consumeInspected : RewriteRule :=
  { name := "ConsumeA", typeContext := [("rest", .collection .hashBag (.base "Place"))],
    premises := [.relationQuery "inspect" [.fvar "rest"]],
    left := .apply "Flow" [.collection .hashBag [token "A"] (some "rest")],
    right := .apply "Flow" [.collection .hashBag [token "B"] (some "rest")],
    bindings := some inspectedOccurrences }

def inspectedCore : LanguageDef :=
  { guardedCore with name := "CollectionNestedInputPetri.Workflow", rewrites := [consumeInspected] }

theorem inspected_no_equations : inspectedCore.equations = [] := rfl

theorem inspected_no_algebra : inspectedCore.hasAlgebraDeclarations = false := by decide

theorem inspected_queried : inspectedCore.rewrites.all (fun rule => rule.premises.all BagForms.query) = true := by
  decide

/-- Whether a bag holds a `B`. -/
def holdsB : Pattern → Bool
  | .collection _ elements _ => elements.contains (token "B")
  | _ => false

/-- `inspect(rest)` holds when `rest` holds a `B`, read off its canonical form. -/
def inspecting : RelationEnv := ⟨fun relation arguments =>
  match relation, arguments with
  | "inspect", [bag] => if holdsB (BagForms.sortBags bag) then [[bag]] else []
  | _, _ => []⟩

/-- **The inspection respects canonical forms.** -/
theorem inspecting_respects : BagForms.RespectsCanon inspecting := by
  intro relation arguments tuple member
  simp only [inspecting] at member ⊢
  split at member
  · rename_i bag
    by_cases holds : holdsB (BagForms.sortBags bag) = true
    · simp only [holds, ↓reduceIte, List.mem_singleton] at member
      subst member
      have same : BagForms.sortBags (canon bag) = BagForms.sortBags bag := by
        rw [BagForms.sortBags_eq, BagForms.sortBags_eq, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent]
      simp [same, holds]
    · simp [holds] at member
  · simp at member

abbrev Inspected := referenceStructure inspecting inspectedCore

/-- **`workflow {A, B}` steps**: the rest `{B}` holds a `B`. -/
theorem ab_inspected_steps : Inspected.sat Env.closed steps (workflow [token "A", token "B"]) :=
  decided_true_queries inspected_no_equations inspected_no_algebra inspected_queried inspecting_respects 4 rfl
    (by decide +kernel)

/-- **`workflow {A, A}` does not**: the rest `{A}` holds no `B`. -/
theorem aa_inspected_stuck : ¬ Inspected.sat Env.closed steps (workflow [token "A", token "A"]) :=
  decided_false_queries inspected_no_equations inspected_no_algebra inspected_queried inspecting_respects 4 rfl
    (by decide +kernel)

/-- **Every run from `workflow {A, B, A}` reaches `workflow {B, B, B}`.** -/
theorem aba_inspected_reaches_bbb : Inspected.sat Env.closed reachesBBB aba :=
  decided_true_queries inspected_no_equations inspected_no_algebra inspected_queried inspecting_respects 4 rfl
    (by decide +kernel)

/-! ## The relabelled workflow -/

/-- `workflow {x, ...rest} ⇒ workflow {y, ...rest}`, when `next(x, y)` holds: the query's second argument is an
output, bound by the answer and used on the right side. -/
def relabel : RewriteRule :=
  { name := "Relabel",
    typeContext := [("x", .base "Place"), ("y", .base "Place"), ("rest", .collection .hashBag (.base "Place"))],
    premises := [.relationQuery "next" [.fvar "x", .fvar "y"]],
    left := .apply "Flow" [.collection .hashBag [.fvar "x"] (some "rest")],
    right := .apply "Flow" [.collection .hashBag [.fvar "y"] (some "rest")], bindings := none }

def relabelledCore : LanguageDef :=
  { name := "Relabelled.Workflow",
    types := [⟨"Place", .ast⟩, ⟨"Marking", .ast⟩, ⟨"Workflow", .ast⟩, ⟨"Workspace", .ast⟩],
    terms := [placeRule "A", placeRule "B", placeRule "C", bagRule "Tokens" "Marking" "items", flowRule, boxRule],
    equations := [], rewrites := [relabel] }

theorem relabelled_no_equations : relabelledCore.equations = [] := rfl

theorem relabelled_no_algebra : relabelledCore.hasAlgebraDeclarations = false := by decide

theorem relabelled_queried : relabelledCore.rewrites.all (fun rule => rule.premises.all BagForms.query) = true := by
  decide

/-- The place a place is relabelled to. -/
def nextPlace : Pattern → Option Pattern
  | .apply "A" [] => some (token "B")
  | .apply "B" [] => some (token "C")
  | _ => none

theorem nextPlace_canon {place next : Pattern} (found : nextPlace place = some next) : canon next = next := by
  unfold nextPlace at found
  split at found <;> cases found <;> simp [token, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_apply]

/-- `next(x, y)` answers the place `x` is relabelled to, read off the canonical form of `x`. -/
def nexting : RelationEnv := ⟨fun relation arguments =>
  match relation, arguments with
  | "next", [place, _] =>
    match nextPlace (BagForms.sortBags place) with
    | some next => [[BagForms.sortBags place, next]]
    | none => []
  | _, _ => []⟩

/-- **The relabelling respects canonical forms.** -/
theorem nexting_respects : BagForms.RespectsCanon nexting := by
  intro relation arguments tuple member
  simp only [nexting] at member ⊢
  split at member
  · rename_i place output
    have same : BagForms.sortBags (canon place) = BagForms.sortBags place := by
      rw [BagForms.sortBags_eq, BagForms.sortBags_eq, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent]
    have canonical : canon (BagForms.sortBags place) = BagForms.sortBags place := by
      rw [BagForms.sortBags_eq, Mettapedia.OSLF.MeTTaIL.CanonicalBags.canon_idempotent]
    simp only [List.map_cons, List.map_nil, same]
    split at member
    · rename_i next found
      rw [List.mem_singleton] at member
      subst member
      simp [nextPlace_canon found, canonical]
    · simp at member
  · simp at member

abbrev Relabelled := referenceStructure nexting relabelledCore

/-- Some run reaches the term. -/
def someRunReaches (target : Pattern) : Formula 0 := .mu (.or (.is target) (.possibly .any (.var 0)))

/-- Every run reaches the term. -/
def everyRunReaches (target : Pattern) : Formula 0 :=
  .mu (.or (.is target) (.and (.possibly .any .top) (.necessarily .any (.var 0))))

/-- **Some run from `workflow {A, B}` reaches `workflow {C, C}`**: each answer binds the output `y`. -/
theorem ab_relabelled_reaches_cc :
    Relabelled.sat Env.closed (someRunReaches (workflow [token "C", token "C"])) (workflow [token "A", token "B"]) :=
  decided_true_queries relabelled_no_equations relabelled_no_algebra relabelled_queried nexting_respects 4 rfl
    (by decide +kernel)

/-- **Every run from `workflow {A, A}` reaches `workflow {C, C}`.** -/
theorem aa_relabelled_reaches_cc :
    Relabelled.sat Env.closed (everyRunReaches (workflow [token "C", token "C"])) (workflow [token "A", token "A"]) :=
  decided_true_queries relabelled_no_equations relabelled_no_algebra relabelled_queried nexting_respects 5 rfl
    (by decide +kernel)

/-- **`workflow {C}` does not step**: `next` answers nothing for `C`. -/
theorem c_relabelled_stuck : ¬ Relabelled.sat Env.closed steps (workflow [token "C"]) :=
  decided_false_queries relabelled_no_equations relabelled_no_algebra relabelled_queried nexting_respects 4 rfl
    (by decide +kernel)

/-- **No run from `workflow {B}` reaches `workflow {A}`.** -/
theorem b_relabelled_not_a :
    ¬ Relabelled.sat Env.closed (someRunReaches (workflow [token "A"])) (workflow [token "B"]) :=
  decided_false_queries relabelled_no_equations relabelled_no_algebra relabelled_queried nexting_respects 4 rfl
    (by decide +kernel)

/-! ## Sets -/

def setPattern : Pattern := .collection .hashSet [.fvar "x"] (some "rest")

/-- **Sets are not admitted.** -/
theorem set_not_admitted : BagForms.domain petriCore (graph [token "A"]) = false := by decide +kernel

/-- **The set laws identify `{A, A}` with `{A}`.** -/
theorem set_presentations_same : canon (graph [token "A", token "A"]) = canon (graph [token "A"]) := by
  rw [← BagForms.sortBags_eq, ← BagForms.sortBags_eq]
  decide +kernel

/-- **Yet `{x, ...rest}` leaves `{A}` in the rest at the first, and the empty set at the second.** -/
theorem set_rests_differ :
    matchPattern setPattern (graph [token "A", token "A"]) =
        [[("rest", graph [token "A"]), ("x", token "A")], [("rest", graph [token "A"]), ("x", token "A")]] ∧
      matchPattern setPattern (graph [token "A"]) = [[("rest", graph []), ("x", token "A")]] := by
  constructor <;> decide +kernel

/-! ## The authored modules

Loading a module makes its syntax available in the rest of the file, so the modules are loaded last. -/

#module_file "../../../../../../metta/gslt/module/CollectionPetri.module"
#module_file "../../../../../../metta/gslt/module/CollectionNestedGuardedPetri.module"
#module_file "../../../../../../metta/gslt/module/CollectionNestedInputPetri.module"

/-- **The authored Petri module, loaded and elaborated to its core, is `petriCore`.** -/
theorem petri_core : core CollectionPetri.language = petriCore := by cbv

/-- **The authored guarded module, loaded and elaborated to its core, is `guardedCore`.** -/
theorem guarded_core : core CollectionNestedGuardedPetri.language = guardedCore := by cbv

/-- **The authored inspected module, loaded and elaborated to its core, is `inspectedCore`.** -/
theorem inspected_core : core CollectionNestedInputPetri.language = inspectedCore := by cbv

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
