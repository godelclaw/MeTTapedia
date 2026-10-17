import Mettapedia.Logic.HostingStyles.LocatedAtoms.Language
import Mettapedia.Logic.HostingStyles.AmbientSpace.Tokens

/-!
# A normal form for located atoms

The static equivalence of the candidate in which atoms reduce is that of
quotation and dropping, and contraction is a normal form for it: two terms
are equal exactly when they have one contraction.  With the four equations of
a run the classes are larger.  This module gives the normal form that reads
the four equations from the run outside to the runs inside.

* `push space pattern` places a run in `space` at every leaf of `pattern`
  that is not yet beneath a run: it descends through application, abstraction
  and product, it stops at a run, and it wraps every other node.  A pattern
  that is pushed stays as it is when it is pushed again, in any space
  (`push_push`): the inner run wins, which is the equation of a run of a run.
* `settle pattern` normalizes a pattern, innermost first: a quotation of a
  dropping is contracted, a run is pushed, and the display name of a binder is
  dropped.
* **Patterns that the static equivalence identifies have one normal form**
  (`settle_eq_of_equiv`), and so do terms (`settle_eq_of_related`).  The proof
  is one line per law (`Law.settle_eq`) and compositionality
  (`settle_fill`).
* On a pattern without a run the normal form is the contraction
  (`settle_eq_contract`); so the atom of a λΠ term and the space of a list of
  rules are their own normal forms (`settle_atomAt`, `settle_ruleSpace`).

What changes against the candidate in which atoms reduce, with witnesses:

* **the run of a term is no longer alone in its class** (`run_not_alone`):
  the run of an application and the application of the runs are two terms of
  one class;
* **the normal form of a term need not be a term** (`settle_not_term`): the
  run of an abstraction in a space that is a bound variable of sort `Space`
  normalizes to a pattern in which that variable stands beneath the binder of
  the abstraction, where the variable of that index is an atom;
* **the two equations with a binder capture** (`binder_captures`): the run of
  an abstraction, in a space that stores the variable of an enclosing binder,
  is equal to the abstraction whose body runs in the space that stores the
  variable of the abstraction itself, and not to the one that stores the
  enclosing variable.  Equations are instantiated without a shift.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (tokens_apply_eq_zero_iff atomAt_wellSorted_of ruleSpace_wellSorted_of numeral_wellSorted_of)

/-! ## Pushing a space to the leaves -/

/-- Whether a pattern is an abstraction node, the argument of a binder. -/
def isAbstraction : Pattern → Bool
  | .lambda _ _ => true
  | _ => false

/-- **Whether a run distributes over a node**: an application of two
arguments, or an abstraction or a product of an atom and an abstraction
node. -/
def distributes (label : String) (arguments : List Pattern) : Bool :=
  match arguments with
  | [_, second] => label == "App" || ((label == "Lam" || label == "Pi") && isAbstraction second)
  | _ => false

/-- Place a node whose arguments are pushed: a node that a run distributes
over keeps its label, a run stays as it is, and every other node is wrapped
in a run. -/
def pushRoot (space : Pattern) (label : String) (arguments pushed : List Pattern) : Pattern :=
  if distributes label arguments then .apply label pushed
  else if label = "prime-run" ∧ arguments.length = 2 then .apply label arguments
  else runPattern space (.apply label arguments)

mutual
  /-- **Push a space to the leaves of a pattern.**  Every leaf that is not
  beneath a run is placed in a run in `space`. -/
  def push (space : Pattern) : Pattern → Pattern
    | .bvar index => runPattern space (.bvar index)
    | .fvar name => runPattern space (.fvar name)
    | .apply label arguments => pushRoot space label arguments (pushList space arguments)
    | .lambda binder body => .lambda binder (push space body)
    | .multiLambda arity binders body => runPattern space (.multiLambda arity binders body)
    | .subst body replacement => runPattern space (.subst body replacement)
    | .collection kind elements rest => runPattern space (.collection kind elements rest)

  /-- Pushing, along a list. -/
  def pushList (space : Pattern) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => push space pattern :: pushList space patterns
end

@[simp] theorem pushList_eq_map (space : Pattern) :
    ∀ patterns : List Pattern, pushList space patterns = patterns.map (push space)
  | [] => rfl
  | pattern :: patterns => by
      simp only [pushList, List.map_cons, pushList_eq_map space patterns]

theorem push_apply (space : Pattern) (label : String) (arguments : List Pattern) :
    push space (.apply label arguments) =
      pushRoot space label arguments (arguments.map (push space)) := by
  rw [push, pushList_eq_map]

/-- **Positive**: a run distributes over an application. -/
theorem push_app (space function argument : Pattern) :
    push space (.apply "App" [function, argument]) =
      .apply "App" [push space function, push space argument] := by
  simp [push_apply, pushRoot, distributes]

/-- A run distributes over an abstraction and over a product, beneath the
binder. -/
theorem push_binder {label : String} (binding : label = "Lam" ∨ label = "Pi")
    (space domain body : Pattern) (binder : Option String) :
    push space (.apply label [domain, .lambda binder body]) =
      .apply label [push space domain, .lambda binder (push space body)] := by
  rcases binding with rfl | rfl <;> simp [push, pushRoot, distributes, isAbstraction]

/-- **Negative**: a run is not pushed into: the inner run wins. -/
theorem push_runPattern (space inner subject : Pattern) :
    push space (runPattern inner subject) = runPattern inner subject := by
  simp [runPattern, push, pushRoot, distributes]

/-- A node that a run does not distribute over, and that is no run, is
wrapped. -/
theorem push_wraps {label : String} {arguments : List Pattern}
    (stays : distributes label arguments = false)
    (noRun : ¬ (label = "prime-run" ∧ arguments.length = 2)) (space : Pattern) :
    push space (.apply label arguments) = runPattern space (.apply label arguments) := by
  rw [push_apply, pushRoot, if_neg (by simp [stays]), if_neg noRun]

/-- Pushing keeps whether a pattern is an abstraction node. -/
theorem isAbstraction_push (space pattern : Pattern) :
    isAbstraction (push space pattern) = isAbstraction pattern := by
  cases pattern with
  | apply label arguments =>
      rw [push_apply, pushRoot]
      split_ifs <;> rfl
  | lambda binder body => simp [push, isAbstraction]
  | bvar index => simp [push, isAbstraction, runPattern]
  | fvar name => simp [push, isAbstraction, runPattern]
  | multiLambda arity binders body => simp [push, isAbstraction, runPattern]
  | subst body replacement => simp [push, isAbstraction, runPattern]
  | collection kind elements rest => simp [push, isAbstraction, runPattern]

/-- Whether a run distributes over a node does not change when its arguments
are pushed. -/
theorem distributes_map_push (space : Pattern) (label : String) (arguments : List Pattern) :
    distributes label (arguments.map (push space)) = distributes label arguments := by
  match arguments with
  | [] => rfl
  | [_] => rfl
  | [_, second] => simp [distributes, isAbstraction_push]
  | _ :: _ :: _ :: _ => rfl

/-- **A pushed pattern stays as it is when it is pushed again**, in any
space. -/
theorem push_push (outer space : Pattern) (pattern : Pattern) :
    push outer (push space pattern) = push space pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [push, push_runPattern]
  | hfvar name => simp [push, push_runPattern]
  | happly label arguments ih =>
      rw [push_apply]
      unfold pushRoot
      split_ifs with spread isRun
      · rw [push_apply, pushRoot,
          if_pos (by rw [distributes_map_push]; exact spread), List.map_map]
        congr 1
        exact List.map_congr_left fun argument member => ih argument member
      · rw [push_apply, pushRoot, if_neg spread, if_pos isRun]
      · exact push_runPattern outer space _
  | hlambda binder body ih => simp only [push, ih]
  | hmultiLambda arity binders body _ => simp [push, push_runPattern]
  | hsubst body replacement _ _ => simp [push, push_runPattern]
  | hcollection kind elements rest _ => simp [push, push_runPattern]

/-! ## The normal form -/

/-- Normalize a node whose arguments are normal: a run is pushed, a quotation
of a dropping is contracted. -/
def settleRoot (label : String) (arguments : List Pattern) : Pattern :=
  if label = "prime-run" then
    match arguments with
    | [space, subject] => push space subject
    | _ => .apply label arguments
  else contractRoot label arguments

mutual
  /-- **The normal form of a pattern for the five laws**, innermost first. -/
  def settle : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => settleRoot label (settleList arguments)
    | .lambda _ body => .lambda none (settle body)
    | .multiLambda arity binders body => .multiLambda arity binders (settle body)
    | .subst body replacement => .subst (settle body) (settle replacement)
    | .collection kind elements rest => .collection kind (settleList elements) rest

  /-- The normal form, along a list. -/
  def settleList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => settle pattern :: settleList patterns
end

@[simp] theorem settleList_eq_map :
    ∀ patterns : List Pattern, settleList patterns = patterns.map settle
  | [] => rfl
  | pattern :: patterns => by
      simp only [settleList, List.map_cons, settleList_eq_map patterns]

theorem settle_apply (label : String) (arguments : List Pattern) :
    settle (.apply label arguments) = settleRoot label (arguments.map settle) := by
  rw [settle, settleList_eq_map]

/-- **The normal form of a run**: the normal form of its subject, pushed in
the normal form of its space. -/
theorem settle_runPattern (space subject : Pattern) :
    settle (runPattern space subject) = push (settle space) (settle subject) := by
  simp [runPattern, settle_apply, settleRoot]

/-- The normal form of a node that is no run and no quotation keeps the
node. -/
theorem settle_apply_of_ne {label : String} (noRun : label ≠ "prime-run")
    (noQuote : label ≠ "prime-quote") (arguments : List Pattern) :
    settle (.apply label arguments) = .apply label (arguments.map settle) := by
  rw [settle_apply]
  unfold settleRoot
  rw [if_neg noRun, contractRoot_of_ne noQuote]

theorem settle_lambda (binder : Option String) (body : Pattern) :
    settle (.lambda binder body) = .lambda none (settle body) := by
  rw [settle]

theorem settle_app (function argument : Pattern) :
    settle (.apply "App" [function, argument]) = .apply "App" [settle function, settle argument] := by
  rw [settle_apply_of_ne (by decide) (by decide)]
  rfl

theorem settle_binder {label : String} (binding : label = "Lam" ∨ label = "Pi")
    (domain body : Pattern) (binder : Option String) :
    settle (.apply label [domain, .lambda binder body]) =
      .apply label [settle domain, .lambda none (settle body)] := by
  rcases binding with rfl | rfl <;>
    rw [settle_apply_of_ne (by decide) (by decide)] <;> simp [settle_lambda]

/-- A quotation of a dropping has the normal form of what was dropped. -/
theorem settle_quoted_dropped (name : Pattern) : settle (quoted (dropped name)) = settle name := by
  simp [quoted, dropped, settle_apply, settleRoot, contractRoot]

/-- The normal form is compositional: it is determined by the normal forms of
the parts. -/
theorem settle_fill (context : OneHoleContext) {first second : Pattern}
    (same : settle first = settle second) :
    settle (context.fill first) = settle (context.fill second) := by
  induction context with
  | hole => exact same
  | apply label before inner after ih =>
      simp only [OneHoleContext.fill, settle, settleList_eq_map, List.map_append, List.map_cons, ih]
  | lambda binder inner ih => simp only [OneHoleContext.fill, settle, ih]
  | multiLambda arity binders inner ih => simp only [OneHoleContext.fill, settle, ih]
  | substBody inner replacement ih => simp only [OneHoleContext.fill, settle, ih]
  | substReplacement body inner ih => simp only [OneHoleContext.fill, settle, ih]
  | collection kind before inner after rest ih =>
      simp only [OneHoleContext.fill, settle, settleList_eq_map, List.map_append, List.map_cons, ih]

/-- **The two sides of a law have one normal form.** -/
theorem Law.settle_eq {left right : Pattern} (law : Law left right) :
    settle left = settle right := by
  cases law with
  | quoteDrop name => exact settle_quoted_dropped _
  | application space function argument =>
      simp only [settle_runPattern, settle_app, push_app]
  | abstraction space domain body first second =>
      simp only [settle_runPattern, settle_binder (label := "Lam") (.inl rfl),
        push_binder (label := "Lam") (.inl rfl)]
  | product space domain body first second =>
      simp only [settle_runPattern, settle_binder (label := "Pi") (.inr rfl),
        push_binder (label := "Pi") (.inr rfl)]
  | inner outer space subject => simp only [settle_runPattern, push_push]

variable {base : BasePremiseEvaluator}

/-- **Patterns that the static equivalence identifies have one normal
form.** -/
theorem settle_eq_of_equiv {left right : Pattern}
    (equivalent : EquationEquiv base located left right) : settle left = settle right := by
  induction equivalent with
  | rel left right step =>
      cases step with
      | inContext context generator =>
          rcases located_generator generator with law | law
          · exact settle_fill context law.settle_eq
          · exact settle_fill context law.settle_eq.symm
  | refl pattern => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Terms of one class have one normal form.** -/
theorem settle_eq_of_related {interface : Contexts.Interface}
    {first second : Contexts.Term located interface}
    (related : (termSetoid base located interface).r first second) :
    settle first.1 = settle second.1 :=
  settle_eq_of_equiv (equationEquiv_of_termSetoid related)

/-! ## Without a run, the normal form is the contraction -/

/-- **On a pattern without a run and with unnamed binders the normal form is
the contraction.** -/
theorem settle_eq_contract (pattern : Pattern) :
    tokens runLabel pattern = 0 → pattern.hasCanonicalBinderMetadata = true →
      settle pattern = contract pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _; rw [settle, contract]
  | hfvar name => intro _ _; rw [settle, contract]
  | happly label arguments ih =>
      intro clean canonical
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp clean
      have noRun : label ≠ "prime-run" := by simpa [runLabel] using uncounted
      have unnamed := (Pattern.hasCanonicalBinderMetadataList_eq_true_iff arguments).mp
        (by simpa [Pattern.hasCanonicalBinderMetadata] using canonical)
      have same : arguments.map settle = arguments.map contract :=
        List.map_congr_left fun argument member =>
          ih argument member (each argument member) (unnamed argument member)
      rw [settle_apply]
      unfold settleRoot
      rw [if_neg noRun, same, contract, contractList_eq_map]
  | hlambda binder body ih =>
      intro clean canonical
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true, Option.isNone_iff_eq_none]
        at canonical
      obtain ⟨rfl, bodyCanonical⟩ := canonical
      rw [settle, contract, ih (by rwa [tokens] at clean) bodyCanonical]
  | hmultiLambda arity binders body ih =>
      intro clean canonical
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      rw [settle, contract, ih (by rwa [tokens] at clean) canonical.2]
  | hsubst body replacement ihBody ihReplacement =>
      intro clean canonical
      simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
      rw [tokens] at clean
      rw [settle, contract, ihBody (by omega) canonical.1, ihReplacement (by omega) canonical.2]
  | hcollection kind elements rest ih =>
      intro clean canonical
      have unnamed := (Pattern.hasCanonicalBinderMetadataList_eq_true_iff elements).mp
        (by simpa [Pattern.hasCanonicalBinderMetadata] using canonical)
      have each := AmbientSpace.tokens_eq_zero_of_mem (counted := runLabel)
        (by rwa [tokens] at clean)
      have same : elements.map settle = elements.map contract :=
        List.map_congr_left fun element member =>
          ih element member (each element member) (unnamed element member)
      rw [settle, settleList_eq_map, same, contract, contractList_eq_map]

/-- **The atom of a λΠ term is its own normal form.** -/
theorem settle_atomAt (term : LF.Term) (depth : Nat) :
    settle (atomAt depth term) = atomAt depth term := by
  rw [settle_eq_contract _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) term depth)
    (atomAt_wellSorted_of located_carriesAtoms term depth).2.1]
  exact contract_atomAt term depth

/-- **The space of a list of rules is its own normal form.** -/
theorem settle_ruleSpace (rules : List Dedukti.RewriteRule) :
    settle (ruleSpace rules) = ruleSpace rules := by
  rw [settle_eq_contract _ (tokens_ruleSpace (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) rules)
    (ruleSpace_wellSorted_of located_carriesAtoms rules).2.1]
  exact contract_ruleSpace rules

/-- The normal form of the run of the atom of a term in the space of a list
of rules: the atom, pushed in the space. -/
theorem settle_run_atomAt (rules : List Dedukti.RewriteRule) (term : LF.Term) (depth : Nat) :
    settle (runPattern (ruleSpace rules) (atomAt depth term)) =
      push (ruleSpace rules) (atomAt depth term) := by
  rw [settle_runPattern, settle_ruleSpace, settle_atomAt]

/-! ## The run of a term is not alone in its class -/

/-- One instance of an equation relates the terms of its two sides. -/
theorem related_of_instance {interface : Contexts.Interface}
    {first second : Contexts.Term located interface}
    (found : EquationInstance base located first.1 second.1) :
    (termSetoid base located interface).r first second :=
  Relation.EqvGen.rel _ _ (EquationContextStep.inContext .hole (Or.inl found))

/-- The run of an application, in the empty space. -/
def runOfApplication : Contexts.Term located AtomsReduce.closedAtom :=
  ⟨runPattern emptySpace (.apply "App" [unitAtom, unitAtom]),
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The application of two runs, in the empty space. -/
def applicationOfRuns : Contexts.Term located AtomsReduce.closedAtom :=
  ⟨.apply "App" [runPattern emptySpace unitAtom, runPattern emptySpace unitAtom],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The run of a term is no longer alone in its class**: the run of an
application and the application of the runs are two terms, and they are
equal. -/
theorem run_not_alone (base : BasePremiseEvaluator) :
    (termSetoid base located AtomsReduce.closedAtom).r runOfApplication applicationOfRuns ∧
      runOfApplication ≠ applicationOfRuns :=
  ⟨related_of_instance (runApplication_instance emptySpace unitAtom unitAtom),
    fun same => absurd (congrArg Subtype.val same) (by decide)⟩

/-- **Negative**: an application of an atom to a run is not the run of the
application.  The atom is in no space. -/
theorem plain_function_apart (base : BasePremiseEvaluator) :
    ¬ EquationEquiv base located
      (runPattern emptySpace (.apply "App" [unitAtom, unitAtom]))
      (.apply "App" [unitAtom, runPattern emptySpace unitAtom]) :=
  fun equivalent => absurd (settle_eq_of_equiv equivalent) (by decide)

/-! ## The normal form of a term need not be a term -/

/-- The run of an abstraction in a space that is a bound variable of sort
`Space`. -/
def spaceVariableRun :
    Contexts.Term located ⟨.base "Atom", [.base "Space"]⟩ :=
  ⟨runPattern (.bvar 0) (.apply "Lam" [unitAtom, .lambda none unitAtom]),
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The normal form of a term need not be a term.**  Pushed beneath the
binder of the abstraction, the variable of the space is the variable of an
atom. -/
theorem settle_not_term :
    ¬ OpenPatternWellSorted located FreeTypeContext.empty [.base "Space"] (.base "Atom")
      (settle spaceVariableRun.1) :=
  fun sorted => absurd (checkOpenPatternWellSorted_complete sorted) (by decide +kernel)

/-! ## The equations with a binder capture -/

/-- The space that stores one bound variable. -/
def storesVariable (index : Nat) : Pattern := addAtom (.bvar index) emptySpace

/-- An abstraction whose body is the run of an abstraction in the space that
stores the variable of the outer binder. -/
def runBeneathBinder : Contexts.Term located AtomsReduce.closedAtom :=
  ⟨.apply "Lam" [unitAtom, .lambda none
      (runPattern (storesVariable 0) (.apply "Lam" [unitAtom, .lambda none unitAtom]))],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The same with the run distributed as the equation of abstraction does:
beneath the inner binder the space stores the variable of index zero, which
there is the variable of the inner binder. -/
def runCaptured : Contexts.Term located AtomsReduce.closedAtom :=
  ⟨.apply "Lam" [unitAtom, .lambda none
      (.apply "Lam" [runPattern (storesVariable 0) unitAtom,
        .lambda none (runPattern (storesVariable 0) unitAtom)])],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The same with the space shifted beneath the inner binder: it stores the
variable of the outer binder. -/
def runShifted : Contexts.Term located AtomsReduce.closedAtom :=
  ⟨.apply "Lam" [unitAtom, .lambda none
      (.apply "Lam" [runPattern (storesVariable 0) unitAtom,
        .lambda none (runPattern (storesVariable 1) unitAtom)])],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The equation of abstraction captures**: the run of an abstraction in a
space that stores the variable of an enclosing binder is equal to the
abstraction whose body runs in the space that stores the variable of the
abstraction itself, and is not equal to the one whose body runs in the space
that stores the enclosing variable. -/
theorem binder_captures (base : BasePremiseEvaluator) :
    (termSetoid base located AtomsReduce.closedAtom).r runBeneathBinder runCaptured ∧
      ¬ (termSetoid base located AtomsReduce.closedAtom).r runBeneathBinder runShifted :=
  ⟨Relation.EqvGen.rel _ _
      (EquationContextStep.inContext (.apply "Lam" [unitAtom] (.lambda none .hole) [])
        (Or.inl (runAbstraction_instance (storesVariable 0) unitAtom unitAtom none))),
    fun related => absurd (settle_eq_of_related related) (by decide)⟩

#print axioms push_push
#print axioms Law.settle_eq
#print axioms settle_eq_of_equiv
#print axioms settle_eq_of_related
#print axioms settle_eq_contract
#print axioms settle_atomAt
#print axioms settle_ruleSpace
#print axioms run_not_alone
#print axioms plain_function_apart
#print axioms settle_not_term
#print axioms binder_captures

end Mettapedia.Logic.HostingStyles.LocatedAtoms
