import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedPart

/-!
# Two readings of a written program, and three programs that tell them apart

A program is written with names, abstractions of a name, applications, and
the dropping of the quotation of a program, `*@program` (`Written`).  It is
read as an atom of the candidate in two ways.

* **The plain reading** (`readPlain`) writes every name bound by an
  abstraction around it as the bound variable of that abstraction, beneath a
  quotation as elsewhere.
* **The sealing reading** (`readSealing`) writes a name bound by an
  abstraction around a quotation, where it occurs beneath that quotation, as
  the variable atom of the name.  The dropped quotation of the name of a
  binder in scope, `*@x`, is read as that name: the drop of the name of a
  binder is the bound value.

Both readings produce atoms of the candidate (`readPlain_wellSorted`,
`readSealing_wellSorted`).  **The sealing reading produces sealed terms**
(`readSealing_sealed`, `sealingTerm_sealed`); the plain reading does not
(`plainTerm_quotedUseProgram_not_sealed`).

Three programs, under every guard and at every ambient space:

| program | sealing reading reaches | plain reading reaches |
|---|---|---|
| `((lam x *@(f x)) payload)` | `(f x)`, `x` the variable atom (`quotedUseProgram_sealing_reaches`) | `(f payload)` (`quotedUseProgram_plain_reaches`) |
| `((lam x *@x) payload)` | `payload` (`droppedNameProgram_sealing_reaches`) | `payload` (`droppedNameProgram_plain_reaches`) |
| `((lam x ((pair x) *@(f x))) payload)` | `((pair payload) (f x))` (`mixedUseProgram_sealing_reaches`) | `((pair payload) (f payload))` (`mixedUseProgram_plain_reaches`) |

The two results of the first program are different terms of the theory
(`quotedUseProgram_results_apart`).  **Under the plain reading no program reaches
a term with a variable atom**, at any ambient space
(`plainTerm_reaches_no_variableAtom`); in particular the first program does
not reach `(f x)` (`quotedUseProgram_plain_not_sealingResult`).  **Under the
sealing reading the first program does not reach `(f payload)`**, at the
empty ambient space.  Here that is shown on patterns as they are written: its
reducts there are four (`quotedUseProgram_sealing_reducts`,
`quotedUseProgram_sealing_not_plainResult`), found with the forms of a step
(`spacesAndRegions_step_cases`).  On the terms of the theory, where a
transition is a step up to the static equivalence, it is
`quotedUseProgram_sealing_not_plainResult_on_terms`, in the module of the
reducts of a sealed program.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (termSetoid TermStep)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
  (instantiateBVar instantiateBVarAt liftBVars instantiateBVarAt_eq_self_of_isWellScopedAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (symbolAtom releaseRule step_release step_beta step_appArgument wellSorted_apply_binder
    wellSorted_extendOuter tokens_numeral instantiateBVarAt_numeral liftBVars_numeral
    contract_dropped contract_quoted abstractionConstructor applicationConstructor
    beta_inv appFunction_inv appArgument_inv piDomain_inv piBody_inv lamDomain_inv lamBody_inv
    release_inv spatialCongruences exists_rule_of_stepAt)
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

variable {admits : Pattern → Bool}

/-! ## A program as it is written -/

/-- **A program as it is written**: a name, an abstraction of a name, an
application, and the dropping of the quotation of a program, `*@program`. -/
inductive Written where
  | name (spelling : String)
  | lam (binder : String) (body : Written)
  | app (function argument : Written)
  | dropQuote (code : Written)
deriving DecidableEq, Repr

/-- Whether a written program is the name of a binder in scope. -/
def Written.boundIn (scope : List String) : Written → Bool
  | .name spelling => decide (spelling ∈ scope)
  | _ => false

/-- **Positive**: the name of a binder in scope. -/
theorem boundIn_name : (Written.name "x").boundIn ["x"] = true := by decide

/-- **Negative**: an application of that name. -/
theorem not_boundIn_app : (Written.app (.name "f") (.name "x")).boundIn ["x"] = false := by decide

/-- `((lam x *@(f x)) payload)`: the body drops a quotation that mentions the
bound name. -/
def quotedUseProgram : Written :=
  .app (.lam "x" (.dropQuote (.app (.name "f") (.name "x")))) (.name "payload")

/-- `((lam x *@x) payload)`: the body drops the quotation of the bound
name. -/
def droppedNameProgram : Written := .app (.lam "x" (.dropQuote (.name "x"))) (.name "payload")

/-- `((lam x ((pair x) *@(f x))) payload)`: the bound name outside a
quotation and beneath one. -/
def mixedUseProgram : Written :=
  .app (.lam "x" (.app (.app (.name "pair") (.name "x"))
    (.dropQuote (.app (.name "f") (.name "x"))))) (.name "payload")

/-! ## The two readings -/

/-- **The plain reading**, beneath the binders of `scope`, the innermost
first: a name in scope is the bound variable of its binder, beneath a
quotation as elsewhere; another name is a symbol.  An abstraction is read
with the unit atom as its domain, which a program does not write. -/
def readPlain (scope : List String) : Written → Pattern
  | .name spelling =>
      if spelling ∈ scope then .bvar (scope.idxOf spelling) else symbolAtom (nameCode spelling)
  | .lam binder body => .apply "Lam" [unitAtom, .lambda none (readPlain (binder :: scope) body)]
  | .app function argument => .apply "App" [readPlain scope function, readPlain scope argument]
  | .dropQuote code => dropped (quoted (readPlain scope code))

/-- **The sealing reading**, beneath the binders of `scope` inside the
innermost quotation, the innermost first, and the binders of `outer` around
that quotation.  A name in scope is the bound variable of its binder; a name
bound around the quotation is the variable atom of the name; another name is
a symbol.  The dropped quotation of the name of a binder in scope is that
name; every other dropped quotation seals its program: what is in scope goes
to the binders around the quotation. -/
def readSealing (outer scope : List String) : Written → Pattern
  | .name spelling =>
      if spelling ∈ scope then .bvar (scope.idxOf spelling)
      else if spelling ∈ outer then variableAtom (numeral (nameCode spelling))
      else symbolAtom (nameCode spelling)
  | .lam binder body =>
      .apply "Lam" [unitAtom, .lambda none (readSealing outer (binder :: scope) body)]
  | .app function argument =>
      .apply "App" [readSealing outer scope function, readSealing outer scope argument]
  | .dropQuote code =>
      if code.boundIn scope then readSealing outer scope code
      else dropped (quoted (readSealing (scope ++ outer) [] code))

/-- **Positive**: the plain reading of the first program has the bound
variable beneath the quotation. -/
theorem readPlain_quotedUseProgram :
    readPlain [] quotedUseProgram =
      .apply "App" [.apply "Lam" [unitAtom,
        .lambda none (dropped (quoted (.apply "App" [symbolAtom (nameCode "f"), .bvar 0])))],
        symbolAtom (nameCode "payload")] :=
  rfl

/-- **Positive**: the sealing reading of the first program has the variable
atom of the bound name beneath the quotation. -/
theorem readSealing_quotedUseProgram :
    readSealing [] [] quotedUseProgram =
      .apply "App" [.apply "Lam" [unitAtom,
        .lambda none (dropped (quoted (.apply "App" [symbolAtom (nameCode "f"),
          variableAtom (numeral (nameCode "x"))])))],
        symbolAtom (nameCode "payload")] :=
  rfl

/-- **The dropped quotation of the name of a binder is read as the bound
variable**, by the sealing reading. -/
theorem readSealing_droppedNameProgram :
    readSealing [] [] droppedNameProgram =
      .apply "App" [.apply "Lam" [unitAtom, .lambda none (.bvar 0)],
        symbolAtom (nameCode "payload")] :=
  rfl

/-- **Negative**: the two readings of the first program differ. -/
theorem readPlain_ne_readSealing :
    readPlain [] quotedUseProgram ≠ readSealing [] [] quotedUseProgram := by
  rw [readPlain_quotedUseProgram, readSealing_quotedUseProgram]
  simp [variableAtom, dropped, quoted]

/-! ## The sealing reading produces sealed terms -/

/-- A numeral is sealed with plain runs, beneath any binders. -/
theorem sealedWithPlainRuns_numeral (depth count : Nat) :
    SealedWithPlainRuns depth (numeral count) := by
  have quiet : tokens quoteOrRun (numeral count) = 0 := tokens_numeral (by decide) (by decide) count
  exact ⟨sealedAt_of_wellScoped (counted := quoteOrRun) (by decide) _ depth
      (isWellScopedAt_mono (numeral_wellSorted_of spacesAndRegions_carriesAtoms [] count).2.2.2
        (Nat.zero_le depth)) quiet,
    runsPlain_of_tokens_eq_zero (counted := quoteOrRun) (by decide) _ quiet⟩

/-- A symbol is sealed with plain runs, beneath any binders. -/
theorem sealedWithPlainRuns_symbolAtom (depth code : Nat) :
    SealedWithPlainRuns depth (symbolAtom code) :=
  (sealedWithPlainRuns_apply_iff (label := "prime-symbol") (by decide) depth _).mpr
    fun argument member => by
      rw [List.mem_singleton.mp member]
      exact sealedWithPlainRuns_numeral depth code

/-- A variable atom is sealed with plain runs, beneath any binders. -/
theorem sealedWithPlainRuns_variableAtom (depth index : Nat) :
    SealedWithPlainRuns depth (variableAtom (numeral index)) :=
  (sealedWithPlainRuns_apply_iff (label := "prime-variable") (by decide) depth _).mpr
    fun argument member => by
      rw [List.mem_singleton.mp member]
      exact sealedWithPlainRuns_numeral depth index

/-- **The dropped quotation of a closed sealed atom is sealed**, beneath any
binders. -/
theorem sealedWithPlainRuns_dropQuote {atom : Pattern} (kept : SealedWithPlainRuns 0 atom)
    (depth : Nat) : SealedWithPlainRuns depth (dropped (quoted atom)) :=
  (sealedWithPlainRuns_apply_iff (label := "prime-drop") (by decide) depth _).mpr
    fun argument member => by
      rw [List.mem_singleton.mp member]
      exact ⟨by rw [sealedAt_quoted]; exact kept.1,
        (runsPlain_apply_of_ne (by decide) _).mpr fun inner inside => by
          rw [List.mem_singleton.mp inside]
          exact kept.2⟩

/-- **The sealing reading produces sealed patterns**: beneath the binders in
scope, what it reads is sealed, and it has no run. -/
theorem readSealing_sealed (written : Written) :
    ∀ outer scope : List String,
      SealedWithPlainRuns scope.length (readSealing outer scope written) := by
  induction written with
  | name spelling =>
      intro outer scope
      rw [readSealing]
      split
      · next bound =>
          exact ⟨by simpa [sealedAt, binderSafeAt] using List.idxOf_lt_length_iff.mpr bound,
            by rw [runsPlain]⟩
      · split
        · exact sealedWithPlainRuns_variableAtom _ _
        · exact sealedWithPlainRuns_symbolAtom _ _
  | lam binder body ih =>
      intro outer scope
      rw [readSealing]
      refine (sealedWithPlainRuns_apply_iff (label := "Lam") (by decide) _ _).mpr ?_
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact sealedWithPlainRuns_numeral _ 0
      · exact (sealedWithPlainRuns_lambda _ _ _).mpr (ih outer (binder :: scope))
  | app function argument ihFunction ihArgument =>
      intro outer scope
      rw [readSealing]
      refine (sealedWithPlainRuns_apply_iff (label := "App") (by decide) _ _).mpr ?_
      intro part member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ihFunction outer scope
      · exact ihArgument outer scope
  | dropQuote code ih =>
      intro outer scope
      rw [readSealing]
      split
      · exact ih outer scope
      · exact sealedWithPlainRuns_dropQuote (ih (scope ++ outer) []) scope.length

/-! ## Both readings produce atoms of the candidate -/

/-- A bound variable in scope is an atom, at the stage of the binders in
scope. -/
theorem boundVariable_wellSorted {depth index : Nat} (below : index < depth) :
    OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty
      (List.replicate depth (.base "Atom")) (.base "Atom") (.bvar index) := by
  refine ⟨.bvar (by simp [below]), by simp [Pattern.hasCanonicalBinderMetadata],
    by simp [isObjectPattern], ?_⟩
  show (Pattern.bvar index).isWellScopedAt (List.replicate depth (TypeExpr.base "Atom")).length =
    true
  simp [Pattern.isWellScopedAt, below]

/-- An abstraction of an atom, with the unit atom as its domain, is an
atom. -/
theorem abstraction_wellSorted {depth : Nat} {body : Pattern}
    (sorted : OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty
      (List.replicate (depth + 1) (.base "Atom")) (.base "Atom") body) :
    OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty
      (List.replicate depth (.base "Atom")) (.base "Atom")
      (.apply "Lam" [unitAtom, .lambda none body]) := by
  rw [List.replicate_succ] at sorted
  exact wellSorted_apply_binder (lang := spacesAndRegions) (label := "Lam") (name := "a")
    (binder := "x") (bodyName := "body")
    (spacesAndRegions_carriesAtoms abstractionConstructor (by decide))
    (numeral_wellSorted_of spacesAndRegions_carriesAtoms _ 0) sorted

/-- An application of two atoms is an atom. -/
theorem application_wellSorted {bound : List TypeExpr} {function argument : Pattern}
    (functionSorted : OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound
      (.base "Atom") function)
    (argumentSorted : OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound
      (.base "Atom") argument) :
    OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound (.base "Atom")
      (.apply "App" [function, argument]) :=
  wellSorted_apply_two (lang := spacesAndRegions) (label := "App") (firstName := "f")
    (secondName := "a") (spacesAndRegions_carriesAtoms applicationConstructor (by decide))
    functionSorted argumentSorted

/-- The dropped quotation of an atom is an atom. -/
theorem dropQuote_wellSorted {bound : List TypeExpr} {atom : Pattern}
    (sorted : OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound (.base "Atom")
      atom) :
    OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound (.base "Atom")
      (dropped (quoted atom)) :=
  wellSorted_apply_one (lang := spacesAndRegions) (label := "prime-drop") (category := "Atom")
    (name := "name") (sort := "CandidateName") (by decide)
    (wellSorted_apply_one (lang := spacesAndRegions) (label := "prime-quote")
      (category := "CandidateName") (name := "term") (sort := "Atom") (by decide) sorted)

/-- **The plain reading produces atoms of the candidate**, at the stage of
the binders in scope. -/
theorem readPlain_wellSorted (written : Written) :
    ∀ scope : List String, OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty
      (List.replicate scope.length (.base "Atom")) (.base "Atom") (readPlain scope written) := by
  induction written with
  | name spelling =>
      intro scope
      rw [readPlain]
      split
      · next bound => exact boundVariable_wellSorted (List.idxOf_lt_length_iff.mpr bound)
      · exact symbolAtom_wellSorted_of spacesAndRegions_carriesAtoms _ _
  | lam binder body ih =>
      intro scope
      rw [readPlain]
      exact abstraction_wellSorted (ih (binder :: scope))
  | app function argument ihFunction ihArgument =>
      intro scope
      rw [readPlain]
      exact application_wellSorted (ihFunction scope) (ihArgument scope)
  | dropQuote code ih =>
      intro scope
      rw [readPlain]
      exact dropQuote_wellSorted (ih scope)

/-- **The sealing reading produces atoms of the candidate**, at the stage of
the binders in scope. -/
theorem readSealing_wellSorted (written : Written) :
    ∀ outer scope : List String, OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty
      (List.replicate scope.length (.base "Atom")) (.base "Atom")
      (readSealing outer scope written) := by
  induction written with
  | name spelling =>
      intro outer scope
      rw [readSealing]
      split
      · next bound => exact boundVariable_wellSorted (List.idxOf_lt_length_iff.mpr bound)
      · split
        · exact wellSorted_apply_one (lang := spacesAndRegions) (label := "prime-variable")
            (category := "Atom") (name := "index") (sort := "Atom")
            (spacesAndRegions_carriesAtoms variableConstructor (by decide))
            (numeral_wellSorted_of spacesAndRegions_carriesAtoms _ _)
        · exact symbolAtom_wellSorted_of spacesAndRegions_carriesAtoms _ _
  | lam binder body ih =>
      intro outer scope
      rw [readSealing]
      exact abstraction_wellSorted (ih outer (binder :: scope))
  | app function argument ihFunction ihArgument =>
      intro outer scope
      rw [readSealing]
      exact application_wellSorted (ihFunction outer scope) (ihArgument outer scope)
  | dropQuote code ih =>
      intro outer scope
      rw [readSealing]
      split
      · exact ih outer scope
      · exact dropQuote_wellSorted
          (wellSorted_extendOuter (ih (scope ++ outer) []) (List.replicate scope.length _))

/-- The plain reading of a program, as a closed atom of the candidate. -/
def plainTerm (written : Written) : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩ :=
  ⟨readPlain [] written, readPlain_wellSorted written []⟩

/-- The sealing reading of a program beneath a quotation whose binders are
`outer`, as a closed atom of the candidate. -/
def sealingTerm (outer : List String) (written : Written) :
    Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩ :=
  ⟨readSealing outer [] written, readSealing_wellSorted written outer []⟩

/-- **The sealing reading of a program is a sealed term.** -/
theorem sealingTerm_sealed (outer : List String) (written : Written) :
    SealedTerm (sealingTerm outer written) :=
  sealedTerm_of_sealed (readSealing_sealed written outer [])

/-- **Negative**: the plain reading of the first program is not a sealed
term. -/
theorem plainTerm_quotedUseProgram_not_sealed : ¬ SealedTerm (plainTerm quotedUseProgram) := by
  intro kept
  have fixed : contract (readPlain [] quotedUseProgram) = readPlain [] quotedUseProgram := by
    rw [readPlain_quotedUseProgram]
    simp [contract, contractList, contractRoot, dropped, quoted, symbolAtom, unitAtom,
      contract_numeral]
  have safe : sealedAt 0 (readPlain [] quotedUseProgram) = true := by
    have literal := kept.1
    rwa [show (plainTerm quotedUseProgram).1 = readPlain [] quotedUseProgram from rfl, fixed]
      at literal
  rw [readPlain_quotedUseProgram] at safe
  simp [sealedAt, binderSafeAt, binderSafeListAt, dropped, quoted] at safe

/-! ## Steps of the readings -/

/-- A step between the patterns of two terms is a transition between the
terms. -/
theorem termStep_of_step {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {source target : Contexts.Term spacesAndRegions interface}
    (step : Step base spacesAndRegions source.1 target.1) :
    TermStep base spacesAndRegions source target :=
  ⟨source, target, Relation.EqvGen.refl _, step, Relation.EqvGen.refl _⟩

/-- The rewrites of the candidate that ask nothing of a space are rewrites of
it. -/
theorem spacesAndRegions_mem_plain {rule : RewriteRule}
    (member : rule ∈ [betaRule, appFunctionRule, appArgumentRule,
      Mettapedia.GSLT.Dedukti.Language.piDomainRule, Mettapedia.GSLT.Dedukti.Language.piBodyRule,
      Mettapedia.GSLT.Dedukti.Language.lamDomainRule, Mettapedia.GSLT.Dedukti.Language.lamBodyRule,
      releaseRule]) : rule ∈ spacesAndRegions.rewrites := by
  rw [spacesAndRegions_rewrites]
  exact allHeaded_mem_plain member

/-- **Beta on an abstraction whose body is closed gives the body**: the bound
variable does not occur in it. -/
theorem step_beta_closedBody {base : BasePremiseEvaluator} {domain body : Pattern}
    (closed : body.isWellScopedAt 0 = true) (argument : Pattern) (binder : Option String) :
    Step base spacesAndRegions (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument])
      body := by
  have step := step_beta (base := base) (lang := spacesAndRegions)
    (spacesAndRegions_mem_plain (by simp)) domain body argument binder
  rw [show instantiateBVar argument body = body from
    instantiateBVarAt_eq_self_of_isWellScopedAt closed] at step
  exact ⟨1, step⟩

/-- The release of a dropped quotation, in the candidate. -/
theorem step_release_candidate {base : BasePremiseEvaluator} (atom : Pattern) :
    Step base spacesAndRegions (dropped (quoted atom)) atom :=
  ⟨1, step_release (spacesAndRegions_mem_plain (by simp)) atom⟩

/-- The instance of a symbol is the symbol. -/
theorem instantiateBVarAt_symbolAtom (depth : Nat) (replacement : Pattern) (code : Nat) :
    instantiateBVarAt depth replacement (symbolAtom code) = symbolAtom code := by
  simp [symbolAtom, instantiateBVarAt, instantiateBVarAt_numeral]

/-- The instance of a variable atom is the variable atom. -/
theorem instantiateBVarAt_variableAtom (depth : Nat) (replacement : Pattern) (index : Nat) :
    instantiateBVarAt depth replacement (variableAtom (numeral index)) =
      variableAtom (numeral index) := by
  simp [variableAtom, instantiateBVarAt, instantiateBVarAt_numeral]

/-- Lifting a symbol by nothing is the symbol. -/
theorem liftBVars_symbolAtom (cutoff amount code : Nat) :
    liftBVars cutoff amount (symbolAtom code) = symbolAtom code := by
  simp [symbolAtom, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList,
    liftBVars_numeral]

/-! ## `((lam x *@(f x)) payload)` -/

/-- **Under the sealing reading the first program reaches `(f x)`**, with
`x` the variable atom of the bound name, under every guard and at every
ambient space: beta leaves the quotation as it is, and the release yields the
quoted atom. -/
theorem quotedUseProgram_sealing_reaches (admits : Pattern → Bool) (ambientSpace : Pattern) :
    Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (sealingTerm [] quotedUseProgram) (sealingTerm ["x"] (.app (.name "f") (.name "x"))) := by
  have first : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (sealingTerm [] quotedUseProgram)
      (sealingTerm ["x"] (.dropQuote (.app (.name "f") (.name "x")))) :=
    termStep_of_step (step_beta_closedBody
      (sealingTerm ["x"] (.dropQuote (.app (.name "f") (.name "x")))).2.2.2.2 _ none)
  have second : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (sealingTerm ["x"] (.dropQuote (.app (.name "f") (.name "x"))))
      (sealingTerm ["x"] (.app (.name "f") (.name "x"))) :=
    termStep_of_step (step_release_candidate _)
  exact .tail (.single first) second

/-- What it reaches: the application of the symbol `f` to the variable atom
of `x`. -/
theorem sealingTerm_fx :
    (sealingTerm ["x"] (.app (.name "f") (.name "x"))).1 =
      .apply "App" [symbolAtom (nameCode "f"), variableAtom (numeral (nameCode "x"))] :=
  rfl

/-- **Under the plain reading the first program reaches `(f payload)`**,
under every guard and at every ambient space: beta puts the argument beneath
the quotation, and the release yields the quoted atom with the argument in
it. -/
theorem quotedUseProgram_plain_reaches (admits : Pattern → Bool) (ambientSpace : Pattern) :
    Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (plainTerm quotedUseProgram) (plainTerm (.app (.name "f") (.name "payload"))) := by
  have instantiated : instantiateBVar (symbolAtom (nameCode "payload"))
      (dropped (quoted (.apply "App" [symbolAtom (nameCode "f"), .bvar 0]))) =
      dropped (quoted
        (.apply "App" [symbolAtom (nameCode "f"), symbolAtom (nameCode "payload")])) := by
    simp [instantiateBVar, instantiateBVarAt, dropped, quoted, instantiateBVarAt_symbolAtom,
      liftBVars_symbolAtom]
  have first : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (plainTerm quotedUseProgram)
      (plainTerm (.dropQuote (.app (.name "f") (.name "payload")))) := by
    refine termStep_of_step ⟨1, ?_⟩
    have step := step_beta (base := regionEvaluator admits ambientSpace) (lang := spacesAndRegions)
      (spacesAndRegions_mem_plain (by simp)) unitAtom
      (dropped (quoted (.apply "App" [symbolAtom (nameCode "f"), .bvar 0])))
      (symbolAtom (nameCode "payload")) none
    rw [instantiated] at step
    exact step
  have second : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (plainTerm (.dropQuote (.app (.name "f") (.name "payload"))))
      (plainTerm (.app (.name "f") (.name "payload"))) :=
    termStep_of_step (step_release_candidate _)
  exact .tail (.single first) second

/-- What it reaches: the application of the symbol `f` to the symbol
`payload`. -/
theorem plainTerm_fpayload :
    (plainTerm (.app (.name "f") (.name "payload"))).1 =
      .apply "App" [symbolAtom (nameCode "f"), symbolAtom (nameCode "payload")] :=
  rfl

/-- **The two results are different terms of the theory**: no equation
identifies `(f x)`, with `x` the variable atom, and `(f payload)`. -/
theorem quotedUseProgram_results_apart (base : BasePremiseEvaluator) :
    ¬ (termSetoid base spacesAndRegions ⟨.base "Atom", []⟩).r
      (sealingTerm ["x"] (.app (.name "f") (.name "x")))
      (plainTerm (.app (.name "f") (.name "payload"))) := by
  intro related
  have same := spacesAndRegions_quoteDropOnly.contract_eq related
  rw [sealingTerm_fx, plainTerm_fpayload] at same
  simp [contract, contractList, contractRoot, symbolAtom, variableAtom] at same

/-! ## `((lam x *@x) payload)` -/

/-- **Under the sealing reading the second program reaches `payload`**: the
dropped quotation of the name of the binder is the bound value. -/
theorem droppedNameProgram_sealing_reaches (admits : Pattern → Bool) (ambientSpace : Pattern) :
    Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (sealingTerm [] droppedNameProgram) (sealingTerm [] (.name "payload")) := by
  refine .single (termStep_of_step ⟨1, ?_⟩)
  have step := step_beta (base := regionEvaluator admits ambientSpace) (lang := spacesAndRegions)
    (spacesAndRegions_mem_plain (by simp)) unitAtom (.bvar 0) (symbolAtom (nameCode "payload")) none
  rw [show instantiateBVar (symbolAtom (nameCode "payload")) (.bvar 0) =
      symbolAtom (nameCode "payload") by
    simp [instantiateBVar, instantiateBVarAt, liftBVars_symbolAtom]] at step
  exact step

/-- **Under the plain reading the second program reaches `payload`** too:
beta puts the argument beneath the quotation, and the release yields it. -/
theorem droppedNameProgram_plain_reaches (admits : Pattern → Bool) (ambientSpace : Pattern) :
    Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (plainTerm droppedNameProgram) (plainTerm (.name "payload")) := by
  have first : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (plainTerm droppedNameProgram) (plainTerm (.dropQuote (.name "payload"))) := by
    refine termStep_of_step ⟨1, ?_⟩
    have step := step_beta (base := regionEvaluator admits ambientSpace) (lang := spacesAndRegions)
      (spacesAndRegions_mem_plain (by simp)) unitAtom (dropped (quoted (.bvar 0)))
      (symbolAtom (nameCode "payload")) none
    rw [show instantiateBVar (symbolAtom (nameCode "payload")) (dropped (quoted (.bvar 0))) =
        dropped (quoted (symbolAtom (nameCode "payload"))) by
      simp [instantiateBVar, instantiateBVarAt, dropped, quoted, liftBVars_symbolAtom]] at step
    exact step
  have second : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (plainTerm (.dropQuote (.name "payload"))) (plainTerm (.name "payload")) :=
    termStep_of_step (step_release_candidate _)
  exact .tail (.single first) second

/-- The two readings of the name `payload` are one term. -/
theorem sealingTerm_payload : sealingTerm [] (.name "payload") = plainTerm (.name "payload") :=
  rfl

/-! ## `((lam x ((pair x) *@(f x))) payload)` -/

/-- **Under the sealing reading the third program reaches
`((pair payload) (f x))`**: the bound name outside the quotation is replaced,
and the one beneath it is not. -/
theorem mixedUseProgram_sealing_reaches (admits : Pattern → Bool) (ambientSpace : Pattern) :
    Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (sealingTerm [] mixedUseProgram)
      (sealingTerm ["x"] (.app (.app (.name "pair") (.name "payload"))
        (.app (.name "f") (.name "x")))) := by
  have instantiated : instantiateBVar (symbolAtom (nameCode "payload"))
      (.apply "App" [.apply "App" [symbolAtom (nameCode "pair"), .bvar 0],
        dropped (quoted (.apply "App" [symbolAtom (nameCode "f"),
          variableAtom (numeral (nameCode "x"))]))]) =
      .apply "App" [.apply "App" [symbolAtom (nameCode "pair"), symbolAtom (nameCode "payload")],
        dropped (quoted (.apply "App" [symbolAtom (nameCode "f"),
          variableAtom (numeral (nameCode "x"))]))] := by
    simp [instantiateBVar, instantiateBVarAt, dropped, quoted, instantiateBVarAt_symbolAtom,
      instantiateBVarAt_variableAtom, liftBVars_symbolAtom]
  have first : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (sealingTerm [] mixedUseProgram)
      (sealingTerm ["x"] (.app (.app (.name "pair") (.name "payload"))
        (.dropQuote (.app (.name "f") (.name "x"))))) := by
    refine termStep_of_step ⟨1, ?_⟩
    have step := step_beta (base := regionEvaluator admits ambientSpace) (lang := spacesAndRegions)
      (spacesAndRegions_mem_plain (by simp)) unitAtom
      (.apply "App" [.apply "App" [symbolAtom (nameCode "pair"), .bvar 0],
        dropped (quoted (.apply "App" [symbolAtom (nameCode "f"),
          variableAtom (numeral (nameCode "x"))]))])
      (symbolAtom (nameCode "payload")) none
    rw [instantiated] at step
    exact step
  have second : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (sealingTerm ["x"] (.app (.app (.name "pair") (.name "payload"))
        (.dropQuote (.app (.name "f") (.name "x")))))
      (sealingTerm ["x"] (.app (.app (.name "pair") (.name "payload"))
        (.app (.name "f") (.name "x")))) :=
    termStep_of_step ⟨2, step_appArgument (spacesAndRegions_mem_plain (by simp)) _
      (step_release (spacesAndRegions_mem_plain (by simp)) _)⟩
  exact .tail (.single first) second

/-- **Under the plain reading the third program reaches
`((pair payload) (f payload))`.** -/
theorem mixedUseProgram_plain_reaches (admits : Pattern → Bool) (ambientSpace : Pattern) :
    Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (plainTerm mixedUseProgram)
      (plainTerm (.app (.app (.name "pair") (.name "payload"))
        (.app (.name "f") (.name "payload")))) := by
  have instantiated : instantiateBVar (symbolAtom (nameCode "payload"))
      (.apply "App" [.apply "App" [symbolAtom (nameCode "pair"), .bvar 0],
        dropped (quoted (.apply "App" [symbolAtom (nameCode "f"), .bvar 0]))]) =
      .apply "App" [.apply "App" [symbolAtom (nameCode "pair"), symbolAtom (nameCode "payload")],
        dropped (quoted (.apply "App" [symbolAtom (nameCode "f"),
          symbolAtom (nameCode "payload")]))] := by
    simp [instantiateBVar, instantiateBVarAt, dropped, quoted, instantiateBVarAt_symbolAtom,
      liftBVars_symbolAtom]
  have first : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (plainTerm mixedUseProgram)
      (plainTerm (.app (.app (.name "pair") (.name "payload"))
        (.dropQuote (.app (.name "f") (.name "payload"))))) := by
    refine termStep_of_step ⟨1, ?_⟩
    have step := step_beta (base := regionEvaluator admits ambientSpace) (lang := spacesAndRegions)
      (spacesAndRegions_mem_plain (by simp)) unitAtom
      (.apply "App" [.apply "App" [symbolAtom (nameCode "pair"), .bvar 0],
        dropped (quoted (.apply "App" [symbolAtom (nameCode "f"), .bvar 0]))])
      (symbolAtom (nameCode "payload")) none
    rw [instantiated] at step
    exact step
  have second : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions
      (plainTerm (.app (.app (.name "pair") (.name "payload"))
        (.dropQuote (.app (.name "f") (.name "payload")))))
      (plainTerm (.app (.app (.name "pair") (.name "payload"))
        (.app (.name "f") (.name "payload")))) :=
    termStep_of_step ⟨2, step_appArgument (spacesAndRegions_mem_plain (by simp)) _
      (step_release (spacesAndRegions_mem_plain (by simp)) _)⟩
  exact .tail (.single first) second

/-! ## The plain reading reaches no variable atom -/

/-- A numeral has no variable atom. -/
theorem tokens_variable_numeral (count : Nat) : tokens isVariableAtom (numeral count) = 0 :=
  tokens_numeral (by decide) (by decide) count

/-- **The plain reading writes no variable atom.** -/
theorem tokens_variable_readPlain (written : Written) :
    ∀ scope : List String, tokens isVariableAtom (readPlain scope written) = 0 := by
  induction written with
  | name spelling =>
      intro scope
      rw [readPlain]
      split
      · rfl
      · simp [symbolAtom, tokens, tokensList, tokens_variable_numeral, isVariableAtom]
  | lam binder body ih =>
      intro scope
      rw [readPlain]
      simp [tokens, tokensList, ih, isVariableAtom, unitAtom]
  | app function argument ihFunction ihArgument =>
      intro scope
      rw [readPlain]
      simp [tokens, tokensList, ihFunction, ihArgument, isVariableAtom]
  | dropQuote code ih =>
      intro scope
      rw [readPlain]
      simp [dropped, quoted, tokens, tokensList, ih, isVariableAtom]

/-- **A transition of the candidate makes no variable atom**, under every
guard and at every ambient space. -/
theorem spacesAndRegions_termStep_no_variableAtom {ambientSpace : Pattern}
    {interface : Contexts.Interface} {source target : Contexts.Term spacesAndRegions interface}
    (step : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions source target)
    (clean : tokens isVariableAtom source.1 = 0) : tokens isVariableAtom target.1 = 0 := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  have sameCount : ∀ {first second : Contexts.Term spacesAndRegions interface},
      (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions interface).r first second →
        tokens isVariableAtom first.1 = tokens isVariableAtom second.1 := by
    intro first second related
    rw [← tokens_contract (counted := isVariableAtom) (by decide) (by decide) first.1,
      ← tokens_contract (counted := isVariableAtom) (by decide) (by decide) second.1,
      spacesAndRegions_quoteDropOnly.contract_eq related]
  rw [← sameCount after]
  exact spacesAndRegions_step_no_variableAtom fired (by rw [← sameCount before]; exact clean)

/-- **Under the plain reading no program reaches a term with a variable
atom**, under every guard and at every ambient space. -/
theorem plainTerm_reaches_no_variableAtom {ambientSpace : Pattern} {written : Written}
    {target : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩}
    (reached : Relation.ReflTransGen
      (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions) (plainTerm written)
      target) :
    tokens isVariableAtom target.1 = 0 := by
  induction reached with
  | refl => exact tokens_variable_readPlain written []
  | tail _ step ih => exact spacesAndRegions_termStep_no_variableAtom step ih

/-- **Under the plain reading the first program does not reach `(f x)`**,
what the sealing reading reaches, under any guard and at any ambient
space. -/
theorem quotedUseProgram_plain_not_sealingResult (admits : Pattern → Bool)
    (ambientSpace : Pattern) :
    ¬ Relation.ReflTransGen (TermStep (regionEvaluator admits ambientSpace) spacesAndRegions)
      (plainTerm quotedUseProgram) (sealingTerm ["x"] (.app (.name "f") (.name "x"))) := by
  intro reached
  have none := plainTerm_reaches_no_variableAtom reached
  rw [sealingTerm_fx] at none
  simp [tokens, tokensList, variableAtom, isVariableAtom] at none

/-! ## The forms of a step, and the reducts of the first program under the sealing reading -/

/-- **The forms of a step of the candidate**, under every guard and at every
ambient space: beta; a step of the function or of the argument of an
application; a step of the domain or of the body of a product or of an
abstraction; the release of a dropped quotation; an answer of the ambient
space; or a step of a run. -/
theorem spacesAndRegions_step_cases {ambientSpace source target : Pattern}
    (step : Step (regionEvaluator admits ambientSpace) spacesAndRegions source target) :
    (∃ domain binder body argument,
      source = .apply "App" [.apply "Lam" [domain, .lambda binder body], argument] ∧
        target = instantiateBVar argument body) ∨
    (∃ function argument next, source = .apply "App" [function, argument] ∧
      Step (regionEvaluator admits ambientSpace) spacesAndRegions function next ∧
        target = .apply "App" [next, argument]) ∨
    (∃ function argument next, source = .apply "App" [function, argument] ∧
      Step (regionEvaluator admits ambientSpace) spacesAndRegions argument next ∧
        target = .apply "App" [function, next]) ∨
    (∃ domain binder body next, source = .apply "Pi" [domain, .lambda binder body] ∧
      Step (regionEvaluator admits ambientSpace) spacesAndRegions domain next ∧
        target = .apply "Pi" [next, .lambda none body]) ∨
    (∃ domain binder body next, source = .apply "Pi" [domain, .lambda binder body] ∧
      Step (regionEvaluator admits ambientSpace) spacesAndRegions body next ∧
        target = .apply "Pi" [domain, .lambda none next]) ∨
    (∃ domain binder body next, source = .apply "Lam" [domain, .lambda binder body] ∧
      Step (regionEvaluator admits ambientSpace) spacesAndRegions domain next ∧
        target = .apply "Lam" [next, .lambda none body]) ∨
    (∃ domain binder body next, source = .apply "Lam" [domain, .lambda binder body] ∧
      Step (regionEvaluator admits ambientSpace) spacesAndRegions body next ∧
        target = .apply "Lam" [domain, .lambda none next]) ∨
    (∃ atom, source = dropped (quoted atom) ∧ target = atom) ∨
    target ∈ admittedAnswers admits ambientSpace source ∨
    ∃ space subject, source = runPattern space subject := by
  obtain ⟨fuel, bounded⟩ := step
  cases fuel with
  | zero => cases bounded
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt bounded
      rw [spacesAndRegions_rewrites] at member
      rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
          exact .inl ⟨domain, binder, body, argument, rfl, applied⟩
        · obtain ⟨function, argument, next, rfl, inner, applied⟩ :=
            appFunction_inv matched premises
          exact .inr (.inl ⟨function, argument, next, rfl, ⟨fuel, inner⟩, applied⟩)
        · obtain ⟨function, argument, next, rfl, inner, applied⟩ :=
            appArgument_inv matched premises
          exact .inr (.inr (.inl ⟨function, argument, next, rfl, ⟨fuel, inner⟩, applied⟩))
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piDomain_inv matched premises
          exact .inr (.inr (.inr (.inl ⟨domain, binder, body, next, rfl, ⟨fuel, inner⟩, applied⟩)))
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piBody_inv matched premises
          exact .inr (.inr (.inr (.inr (.inl
            ⟨domain, binder, body, next, rfl, ⟨fuel, inner⟩, applied⟩))))
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ :=
            lamDomain_inv matched premises
          exact .inr (.inr (.inr (.inr (.inr (.inl
            ⟨domain, binder, body, next, rfl, ⟨fuel, inner⟩, applied⟩)))))
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := lamBody_inv matched premises
          exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
            ⟨domain, binder, body, next, rfl, ⟨fuel, inner⟩, applied⟩))))))
        · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
          exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨atom, rfl, applied⟩)))))))
      · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
        obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (applied ▸ found)))))))))
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inl spatial)
        rw [shape] at matched
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (eq_run_of_matched matched)))))))))
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inl runRoot))
        rw [shape] at matched
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (eq_run_of_matched matched)))))))))
      · obtain ⟨left, right, shape⟩ := allHeaded_runRule_left (.inr (.inr beneath))
        rw [shape] at matched
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (eq_run_of_matched matched)))))))))

/-- **At the empty ambient space an application of a constructor that no
congruence enters, and that is no dropping and no run, has no step.** -/
theorem leaf_normal_at_emptySpace {label : String} {arguments : List Pattern}
    (notApp : label ≠ "App") (notPi : label ≠ "Pi") (notLam : label ≠ "Lam")
    (notDrop : label ≠ "prime-drop") (notRun : label ≠ "prime-run") (target : Pattern) :
    ¬ Step (regionEvaluator admits emptySpace) spacesAndRegions (.apply label arguments)
      target := by
  intro step
  rcases spacesAndRegions_step_cases step with ⟨_, _, _, _, shape, -⟩ | ⟨_, _, _, shape, -, -⟩ |
    ⟨_, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ |
    ⟨_, _, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ | ⟨_, shape, -⟩ | found | ⟨_, _, shape⟩
  · exact notApp (Pattern.apply.inj shape).1
  · exact notApp (Pattern.apply.inj shape).1
  · exact notApp (Pattern.apply.inj shape).1
  · exact notPi (Pattern.apply.inj shape).1
  · exact notPi (Pattern.apply.inj shape).1
  · exact notLam (Pattern.apply.inj shape).1
  · exact notLam (Pattern.apply.inj shape).1
  · exact notDrop (Pattern.apply.inj shape).1
  · rw [admittedAnswers_emptySpace] at found
    cases found
  · exact notRun (Pattern.apply.inj shape).1

/-- **At the empty ambient space a dropped quotation steps to its atom
alone.** -/
theorem dropQuote_step_at_emptySpace {atom target : Pattern}
    (step : Step (regionEvaluator admits emptySpace) spacesAndRegions (dropped (quoted atom))
      target) : target = atom := by
  rcases spacesAndRegions_step_cases step with ⟨_, _, _, _, shape, -⟩ | ⟨_, _, _, shape, -, -⟩ |
    ⟨_, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ |
    ⟨_, _, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ | ⟨other, shape, rfl⟩ | found |
    ⟨_, _, shape⟩
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · simp only [dropped, quoted, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
    exact shape.symm
  · rw [admittedAnswers_emptySpace] at found
    cases found
  · exact absurd (Pattern.apply.inj shape).1 (by decide)

/-- **At the empty ambient space an abstraction steps in its domain or in its
body.** -/
theorem lam_step_at_emptySpace {domain body target : Pattern} {binder : Option String}
    (step : Step (regionEvaluator admits emptySpace) spacesAndRegions
      (.apply "Lam" [domain, .lambda binder body]) target) :
    (∃ next, Step (regionEvaluator admits emptySpace) spacesAndRegions domain next ∧
      target = .apply "Lam" [next, .lambda none body]) ∨
    ∃ next, Step (regionEvaluator admits emptySpace) spacesAndRegions body next ∧
      target = .apply "Lam" [domain, .lambda none next] := by
  rcases spacesAndRegions_step_cases step with ⟨_, _, _, _, shape, -⟩ | ⟨_, _, _, shape, -, -⟩ |
    ⟨_, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ | ⟨_, _, _, _, shape, -, -⟩ |
    ⟨otherDomain, otherBinder, otherBody, next, shape, moved, rfl⟩ |
    ⟨otherDomain, otherBinder, otherBody, next, shape, moved, rfl⟩ | ⟨_, shape, -⟩ | found |
    ⟨_, _, shape⟩
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
      true_and] at shape
    obtain ⟨rfl, -, rfl⟩ := shape
    exact .inl ⟨next, moved, rfl⟩
  · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
      true_and] at shape
    obtain ⟨rfl, -, rfl⟩ := shape
    exact .inr ⟨next, moved, rfl⟩
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · rw [admittedAnswers_emptySpace] at found
    cases found
  · exact absurd (Pattern.apply.inj shape).1 (by decide)

/-- At the empty ambient space the application of a symbol to a variable atom
has no step. -/
theorem symbol_of_variable_normal (function index : Nat) (target : Pattern) :
    ¬ Step (regionEvaluator admits emptySpace) spacesAndRegions
      (.apply "App" [symbolAtom function, variableAtom (numeral index)]) target := by
  intro step
  rcases spacesAndRegions_app_step_iff.mp step with ⟨domain, binder, body, shape, -⟩ |
    ⟨next, moved, -⟩ | ⟨next, moved, -⟩ | found
  · exact absurd (Pattern.apply.inj shape).1 (by decide)
  · exact leaf_normal_at_emptySpace (label := "prime-symbol") (by decide) (by decide) (by decide)
      (by decide) (by decide) next moved
  · exact leaf_normal_at_emptySpace (label := "prime-variable") (by decide) (by decide)
      (by decide) (by decide) (by decide) next moved
  · rw [admittedAnswers_emptySpace] at found
    cases found

/-- **The reducts of the first program under the sealing reading, at the
empty ambient space**: the program; the program with the quotation in its
body released; the dropped quotation `*@(f x)`; and `(f x)`.  In each of them
the symbol `f` is applied to the variable atom of `x`. -/
theorem quotedUseProgram_sealing_reducts (admits : Pattern → Bool) {target : Pattern}
    (reached : Relation.ReflTransGen (Step (regionEvaluator admits emptySpace) spacesAndRegions)
      (readSealing [] [] quotedUseProgram) target) :
    target = readSealing [] [] quotedUseProgram ∨
    target = .apply "App" [.apply "Lam" [unitAtom, .lambda none
        (.apply "App" [symbolAtom (nameCode "f"), variableAtom (numeral (nameCode "x"))])],
      symbolAtom (nameCode "payload")] ∨
    target = dropped (quoted
      (.apply "App" [symbolAtom (nameCode "f"), variableAtom (numeral (nameCode "x"))])) ∨
    target = .apply "App" [symbolAtom (nameCode "f"), variableAtom (numeral (nameCode "x"))] := by
  induction reached with
  | refl => exact .inl rfl
  | @tail middle target _ step ih =>
      have unitNormal : ∀ next, ¬ Step (regionEvaluator admits emptySpace) spacesAndRegions
          unitAtom next := fun next =>
        leaf_normal_at_emptySpace (label := "prime-unit") (arguments := []) (by decide)
          (by decide) (by decide) (by decide) (by decide) next
      have payloadNormal : ∀ next, ¬ Step (regionEvaluator admits emptySpace) spacesAndRegions
          (symbolAtom (nameCode "payload")) next := fun next =>
        leaf_normal_at_emptySpace (label := "prime-symbol") (by decide) (by decide) (by decide)
          (by decide) (by decide) next
      rcases ih with rfl | rfl | rfl | rfl
      · rw [readSealing_quotedUseProgram] at step
        rcases spacesAndRegions_app_step_iff.mp step with ⟨domain, binder, body, shape, rfl⟩ |
          ⟨next, moved, rfl⟩ | ⟨next, moved, -⟩ | found
        · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
            true_and] at shape
          obtain ⟨-, -, rfl⟩ := shape
          refine .inr (.inr (.inl ?_))
          simp [instantiateBVar, instantiateBVarAt, dropped, quoted, instantiateBVarAt_symbolAtom,
            instantiateBVarAt_variableAtom]
        · rcases lam_step_at_emptySpace moved with ⟨reached, inner, -⟩ | ⟨reached, inner, rfl⟩
          · exact absurd inner (unitNormal reached)
          · rw [dropQuote_step_at_emptySpace inner]
            exact .inr (.inl rfl)
        · exact absurd moved (payloadNormal next)
        · rw [admittedAnswers_emptySpace] at found
          cases found
      · rcases spacesAndRegions_app_step_iff.mp step with ⟨domain, binder, body, shape, rfl⟩ |
          ⟨next, moved, -⟩ | ⟨next, moved, -⟩ | found
        · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
            true_and] at shape
          obtain ⟨-, -, rfl⟩ := shape
          refine .inr (.inr (.inr ?_))
          simp [instantiateBVar, instantiateBVarAt, instantiateBVarAt_symbolAtom,
            instantiateBVarAt_variableAtom]
        · rcases lam_step_at_emptySpace moved with ⟨reached, inner, -⟩ | ⟨reached, inner, -⟩
          · exact absurd inner (unitNormal reached)
          · exact absurd inner (symbol_of_variable_normal _ _ reached)
        · exact absurd moved (payloadNormal next)
        · rw [admittedAnswers_emptySpace] at found
          cases found
      · exact .inr (.inr (.inr (dropQuote_step_at_emptySpace step)))
      · exact absurd step (symbol_of_variable_normal _ _ target)

/-- **Under the sealing reading the first program does not reach
`(f payload)`**, at the empty ambient space and under every guard: the
argument is never put where the quotation has the variable atom. -/
theorem quotedUseProgram_sealing_not_plainResult (admits : Pattern → Bool) :
    ¬ Relation.ReflTransGen (Step (regionEvaluator admits emptySpace) spacesAndRegions)
      (readSealing [] [] quotedUseProgram) (readPlain [] (.app (.name "f") (.name "payload"))) := by
  intro reached
  have target : readPlain [] (.app (.name "f") (.name "payload")) =
      .apply "App" [symbolAtom (nameCode "f"), symbolAtom (nameCode "payload")] := rfl
  rw [target] at reached
  rcases quotedUseProgram_sealing_reducts admits reached with same | same | same | same
  · rw [readSealing_quotedUseProgram] at same
    simp [symbolAtom] at same
  · simp [symbolAtom] at same
  · simp [dropped] at same
  · simp [symbolAtom, variableAtom] at same

#print axioms readPlain_quotedUseProgram
#print axioms readSealing_quotedUseProgram
#print axioms readSealing_droppedNameProgram
#print axioms readPlain_ne_readSealing
#print axioms readSealing_sealed
#print axioms readPlain_wellSorted
#print axioms readSealing_wellSorted
#print axioms sealingTerm_sealed
#print axioms plainTerm_quotedUseProgram_not_sealed
#print axioms quotedUseProgram_sealing_reaches
#print axioms quotedUseProgram_plain_reaches
#print axioms quotedUseProgram_results_apart
#print axioms droppedNameProgram_sealing_reaches
#print axioms droppedNameProgram_plain_reaches
#print axioms mixedUseProgram_sealing_reaches
#print axioms mixedUseProgram_plain_reaches
#print axioms tokens_variable_readPlain
#print axioms spacesAndRegions_termStep_no_variableAtom
#print axioms plainTerm_reaches_no_variableAtom
#print axioms quotedUseProgram_plain_not_sealingResult
#print axioms spacesAndRegions_step_cases
#print axioms leaf_normal_at_emptySpace
#print axioms dropQuote_step_at_emptySpace
#print axioms lam_step_at_emptySpace
#print axioms quotedUseProgram_sealing_reducts
#print axioms quotedUseProgram_sealing_not_plainResult

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
