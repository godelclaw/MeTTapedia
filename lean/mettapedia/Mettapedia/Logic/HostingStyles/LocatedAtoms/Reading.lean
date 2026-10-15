import Mettapedia.Logic.HostingStyles.LocatedAtoms.Spellings

/-!
# The class of the run of an atom, and its transitions

The run of the atom of a term has many spellings (`Spells`).  This module
shows that they are its whole class, and reads the transitions of the class.

* **What an atom of the candidate is** (`atom_cases`): a bound variable, a
  node of one of the five constructors that a run does not distribute over,
  an application of two atoms, an abstraction or a product of an atom and an
  atom beneath a binder, or a run of an atom in a space.  The parts are terms
  again.
* **A term of the sorts of atoms and spaces whose normal form has no run and
  no dropping is its normal form** (`settle_fixed`): a run leaves a run in the
  normal form (`tokens_settle_clean`), and without a run the normal form is
  the contraction.
* **Every term whose normal form is the atom of a term pushed in a plain
  space is a spelling of that atom** (`spells_of_settle`).  With the
  soundness of the normal form: every term of the class of the run of an atom
  is a spelling of the atom.
* **A spelling all of whose leaves are located is equal to the run of the
  atom** (`spelled_related`): the equations are read back, one node at a
  time.  So the class of the run of an atom is the set of its spellings.
* **The transitions of the run of the atom of a term, in the space of a list
  of first-order rules with bound right sides, are the runs of the atoms of
  the steps of the term** (`runAtom_termStep_iff`), in a theory whose rules
  are those of the list and which has no definition; at every depth, one
  transition for one step.  The run of an atom determines the term
  (`runAtom_related_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory inst patternVars usesOnly)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList tokensList_eq_zero)
open Mettapedia.Logic.HostingStyles.AmbientSpace (tokens_apply_eq_zero_iff tokens_eq_zero_of_mem)

variable {base : BasePremiseEvaluator}

/-! ## What an atom is -/

theorem located_no_bareCollection : ∀ rule ∈ located.terms, usesBareCollection? rule = false := by
  decide

/-- **What an atom of the candidate is**, with its parts as terms. -/
theorem atom_cases {bound : List TypeExpr} {pattern : Pattern}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") pattern) :
    (∃ index, pattern = .bvar index) ∨
    (∃ label arguments, pattern = .apply label arguments ∧
      label ∈ ["=", "prime-unit", "prime-drop", "prime-variable", "prime-symbol"]) ∨
    (∃ function argument, pattern = .apply "App" [function, argument] ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") function ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") argument) ∨
    (∃ label domain body, (label = "Lam" ∨ label = "Pi") ∧
      pattern = .apply label [domain, .lambda none body] ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") domain ∧
      OpenPatternWellSorted located FreeTypeContext.empty (.base "Atom" :: bound) (.base "Atom")
        body) ∨
    (∃ space subject, pattern = runPattern space subject ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Space") space ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") subject) := by
  obtain ⟨typed, canonical, object, scope⟩ := sorted
  generalize sameType : TypeExpr.base "Atom" = type at typed
  cases typed with
  | bvar _ => exact .inl ⟨_, rfl⟩
  | fvar known => simp [FreeTypeContext.empty] at known
  | @constructor _ rule arguments member notBare argumentsTyped =>
      have category : rule.category = "Atom" := by simpa using sameType.symm
      have listed : rule ∈
          [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
            emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
            runAtomConstructor, applicationConstructor, abstractionConstructor,
            productConstructor] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact .inr (.inl ⟨_, _, rfl, by decide⟩)
      · exact .inr (.inl ⟨_, _, rfl, by decide⟩)
      · exact absurd category (by decide)
      · exact .inr (.inl ⟨_, _, rfl, by decide⟩)
      · exact absurd category (by decide)
      · exact absurd category (by decide)
      · exact .inr (.inl ⟨_, _, rfl, by decide⟩)
      · exact .inr (.inl ⟨_, _, rfl, by decide⟩)
      · have typedArguments : ArgumentsHaveTypes located FreeTypeContext.empty bound arguments
            [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")] := argumentsTyped
        cases typedArguments with
        | cons _ spaceType spaceTyped rest =>
            cases rest with
            | cons _ subjectType subjectTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at spaceType subjectType
                subst spaceType
                subst subjectType
                simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
                  at canonical
                simp [isObjectPattern, isObjectPatternList] at object
                simp [ScopeSafeAt, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] at scope
                exact .inr (.inr (.inr (.inr ⟨_, _, rfl,
                  ⟨spaceTyped, canonical.1, object.1, scope.1⟩,
                  ⟨subjectTyped, canonical.2, object.2, scope.2⟩⟩)))
      · have typedArguments : ArgumentsHaveTypes located FreeTypeContext.empty bound arguments
            [.simple "f" (.base "Atom"), .simple "a" (.base "Atom")] := argumentsTyped
        cases typedArguments with
        | cons _ functionType functionTyped rest =>
            cases rest with
            | cons _ argumentType argumentTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at functionType argumentType
                subst functionType
                subst argumentType
                simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
                  at canonical
                simp [isObjectPattern, isObjectPatternList] at object
                simp [ScopeSafeAt, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] at scope
                exact .inr (.inr (.inl ⟨_, _, rfl,
                  ⟨functionTyped, canonical.1, object.1, scope.1⟩,
                  ⟨argumentTyped, canonical.2, object.2, scope.2⟩⟩))
      · have typedArguments : ArgumentsHaveTypes located FreeTypeContext.empty bound arguments
            [.simple "a" (.base "Atom"), .abstractionNamed (some "x") "body" (.base "Atom")] :=
          argumentsTyped
        cases typedArguments with
        | cons _ domainType domainTyped rest =>
            cases rest with
            | cons representation bodyType abstractionTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at domainType bodyType
                subst domainType
                subst bodyType
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                cases abstractionTyped with
                | lambda bodyTyped =>
                    simp [Pattern.hasCanonicalBinderMetadata,
                      Pattern.hasCanonicalBinderMetadataList] at canonical
                    simp [isObjectPattern, isObjectPatternList] at object
                    simp [ScopeSafeAt, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
                      at scope
                    exact .inr (.inr (.inr (.inl ⟨"Lam", _, body, .inl rfl, rfl,
                      ⟨domainTyped, canonical.1, object.1, scope.1⟩,
                      ⟨bodyTyped, canonical.2, object.2, scope.2⟩⟩)))
      · have typedArguments : ArgumentsHaveTypes located FreeTypeContext.empty bound arguments
            [.simple "a" (.base "Atom"), .abstractionNamed (some "x") "body" (.base "Atom")] :=
          argumentsTyped
        cases typedArguments with
        | cons _ domainType domainTyped rest =>
            cases rest with
            | cons representation bodyType abstractionTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at domainType bodyType
                subst domainType
                subst bodyType
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                cases abstractionTyped with
                | lambda bodyTyped =>
                    simp [Pattern.hasCanonicalBinderMetadata,
                      Pattern.hasCanonicalBinderMetadataList] at canonical
                    simp [isObjectPattern, isObjectPatternList] at object
                    simp [ScopeSafeAt, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]
                      at scope
                    exact .inr (.inr (.inr (.inl ⟨"Pi", _, body, .inr rfl, rfl,
                      ⟨domainTyped, canonical.1, object.1, scope.1⟩,
                      ⟨bodyTyped, canonical.2, object.2, scope.2⟩⟩)))
  | lambda _ => cases sameType
  | multiLambda _ => cases sameType
  | subst _ _ => simp [isObjectPattern] at object
  | collection _ => cases sameType
  | collectionConstructor member shape _ =>
      have bare := (usesBareCollection?_eq_true_iff _).mpr ⟨_, _, _, shape⟩
      rw [located_no_bareCollection _ member] at bare
      cases bare

/-- The two parts of an application that is an atom are atoms. -/
theorem wellSorted_app_inv {bound : List TypeExpr} {function argument : Pattern}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom")
      (.apply "App" [function, argument])) :
    OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") function ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") argument := by
  rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, listed⟩ | ⟨_, _, shape, first, second⟩ |
    ⟨_, _, _, binding, shape, _, _⟩ | ⟨_, _, shape, _, _⟩
  · cases shape
  · simp only [Pattern.apply.injEq] at shape
    obtain ⟨rfl, -⟩ := shape
    exact absurd listed (by decide)
  · simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact ⟨first, second⟩
  · simp only [Pattern.apply.injEq] at shape
    rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  · simp only [runPattern, Pattern.apply.injEq] at shape
    exact absurd shape.1 (by decide)

/-- The domain and the body of an abstraction or of a product that is an atom
are atoms. -/
theorem wellSorted_binder_inv {label : String} (binding : label = "Lam" ∨ label = "Pi")
    {bound : List TypeExpr} {domain body : Pattern}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom")
      (.apply label [domain, .lambda none body])) :
    OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") domain ∧
      OpenPatternWellSorted located FreeTypeContext.empty (.base "Atom" :: bound) (.base "Atom")
        body := by
  rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, listed⟩ | ⟨_, _, shape, _, _⟩ |
    ⟨_, _, _, _, shape, first, second⟩ | ⟨_, _, shape, _, _⟩
  · cases shape
  · simp only [Pattern.apply.injEq] at shape
    obtain ⟨rfl, -⟩ := shape
    rcases binding with rfl | rfl <;> exact absurd listed (by decide)
  · simp only [Pattern.apply.injEq] at shape
    rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  · simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true, true_and]
      at shape
    obtain ⟨-, rfl, rfl⟩ := shape
    exact ⟨first, second⟩
  · simp only [runPattern, Pattern.apply.injEq] at shape
    rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)

/-- The space and the subject of a run that is an atom are a space and an
atom. -/
theorem wellSorted_run_inv {bound : List TypeExpr} {space subject : Pattern}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom")
      (runPattern space subject)) :
    OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Space") space ∧
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") subject := by
  rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, listed⟩ | ⟨_, _, shape, _, _⟩ |
    ⟨_, _, _, binding, shape, _, _⟩ | ⟨_, _, shape, first, second⟩
  · simp [runPattern] at shape
  · simp only [runPattern, Pattern.apply.injEq] at shape
    obtain ⟨rfl, -⟩ := shape
    exact absurd listed (by decide)
  · simp only [runPattern, Pattern.apply.injEq] at shape
    exact absurd shape.1 (by decide)
  · simp only [runPattern, Pattern.apply.injEq] at shape
    rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  · obtain ⟨rfl, rfl⟩ := runPattern_injective shape
    exact ⟨first, second⟩

/-! ## A normal form without a run and without a dropping -/

/-- A pushed pattern has a run. -/
theorem tokens_push_pos (space pattern : Pattern) : 0 < tokens runLabel (push space pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [push, runPattern, tokens, runLabel]
  | hfvar name => simp [push, runPattern, tokens, runLabel]
  | happly label arguments ih =>
      rw [push_apply]
      unfold pushRoot
      split_ifs with spread isRun
      · match arguments, spread, ih with
        | [first, second], _, ih =>
            have positive := ih first (by simp)
            simp only [List.map_cons, List.map_nil, tokens, tokensList]
            omega
        | [], spread, _ => simp [distributes] at spread
        | [_], spread, _ => simp [distributes] at spread
        | _ :: _ :: _ :: _, spread, _ => simp [distributes] at spread
      · rw [tokens]
        simp [isRun.1, runLabel]
      · simp [runPattern, tokens, runLabel]
  | hlambda binder body ih =>
      rw [push, tokens]
      exact ih
  | hmultiLambda arity binders body _ => simp [push, runPattern, tokens, runLabel]
  | hsubst body replacement _ _ => simp [push, runPattern, tokens, runLabel]
  | hcollection kind elements rest _ => simp [push, runPattern, tokens, runLabel]

/-- The arguments of a contracted node without a run have no run. -/
theorem tokens_contractRoot_clean {label : String} {arguments : List Pattern}
    (clean : tokens runLabel (contractRoot label arguments) = 0) :
    ∀ argument ∈ arguments, tokens runLabel argument = 0 := by
  unfold contractRoot at clean
  split_ifs at clean with isQuote
  · split at clean
    · split_ifs at clean with isDrop
      · intro argument member
        rw [List.mem_singleton.mp member]
        simp [tokens, tokensList, clean, isDrop, runLabel]
      · exact (tokens_apply_eq_zero_iff.mp clean).2
    · exact (tokens_apply_eq_zero_iff.mp clean).2
  · exact (tokens_apply_eq_zero_iff.mp clean).2

/-- **A pattern whose normal form has no run has no run**: a run leaves a run
in the normal form. -/
theorem tokens_settle_clean (pattern : Pattern) :
    tokens runLabel (settle pattern) = 0 → tokens runLabel pattern = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly label arguments ih =>
      intro clean
      rw [settle_apply] at clean
      unfold settleRoot at clean
      by_cases isRun : label = "prime-run"
      · rw [if_pos isRun] at clean
        split at clean
        · exact absurd clean (Nat.pos_iff_ne_zero.mp (tokens_push_pos _ _))
        · rw [tokens] at clean
          simp [isRun, runLabel] at clean
      · rw [if_neg isRun] at clean
        have each := tokens_contractRoot_clean clean
        exact tokens_apply_eq_zero_iff.mpr ⟨by simpa [runLabel] using isRun,
          fun argument member => ih argument member (each _ (List.mem_map_of_mem member))⟩
  | hlambda binder body ih =>
      intro clean
      rw [settle, tokens] at clean
      rw [tokens]
      exact ih clean
  | hmultiLambda arity binders body ih =>
      intro clean
      rw [settle, tokens] at clean
      rw [tokens]
      exact ih clean
  | hsubst body replacement ihBody ihReplacement =>
      intro clean
      rw [settle, tokens] at clean
      rw [tokens, ihBody (by omega), ihReplacement (by omega)]
  | hcollection kind elements rest ih =>
      intro clean
      rw [settle, settleList_eq_map, tokens] at clean
      rw [tokens]
      exact tokensList_eq_zero fun element member =>
        ih element member (tokens_eq_zero_of_mem clean _ (List.mem_map_of_mem member))

/-- **A term of the sorts of atoms and spaces whose normal form has no run
and no dropping is its normal form.** -/
theorem settle_fixed {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty bound type pattern)
    (inSorts : resultIn unquotedSorts type = true)
    (noRun : tokens runLabel (settle pattern) = 0)
    (noDrop : tokens dropLabel (settle pattern) = 0) : settle pattern = pattern := by
  have same := settle_eq_contract pattern (tokens_settle_clean pattern noRun) sorted.2.1
  rw [same] at noDrop ⊢
  exact contract_of_dropFree located_namesOnlyDropped located_quoteDropSorted sorted.1 inSorts
    sorted.2.2.1 noDrop

/-! ## Every term with the normal form of the run of an atom is a spelling -/

/-- The atom of a term pushed in a space, by the shape of the term. -/
theorem push_atomAt_cases (space : Pattern) (depth : Nat) (term : LF.Term) :
    (IsLeaf (atomAt depth term) ∧
      push space (atomAt depth term) = runPattern space (atomAt depth term)) ∨
    (∃ function argument, term = .app function argument ∧
      push space (atomAt depth term) = .apply "App"
        [push space (atomAt depth function), push space (atomAt depth argument)]) ∨
    (∃ domain body, term = .lam domain body ∧
      push space (atomAt depth term) = .apply "Lam"
        [push space (atomAt depth domain), .lambda none (push space (atomAt (depth + 1) body))]) ∨
    (∃ domain body, term = .pi domain body ∧
      push space (atomAt depth term) = .apply "Pi"
        [push space (atomAt depth domain), .lambda none (push space (atomAt (depth + 1) body))]) := by
  cases term with
  | var index => exact .inl ⟨isLeaf_atomAt_var depth index, (isLeaf_atomAt_var depth index).push_eq _⟩
  | srt sort => exact .inl ⟨isLeaf_atomAt_srt depth sort, (isLeaf_atomAt_srt depth sort).push_eq _⟩
  | con name => exact .inl ⟨isLeaf_atomAt_con depth name, (isLeaf_atomAt_con depth name).push_eq _⟩
  | app function argument => exact .inr (.inl ⟨_, _, rfl, push_app _ _ _⟩)
  | lam domain body => exact .inr (.inr (.inl ⟨_, _, rfl, push_binder (.inl rfl) _ _ _ _⟩))
  | pi domain body => exact .inr (.inr (.inr ⟨_, _, rfl, push_binder (.inr rfl) _ _ _ _⟩))

/-- A run does not distribute over a node of another label than application,
abstraction and product. -/
theorem distributes_eq_false {label : String} (noApp : label ≠ "App") (noLam : label ≠ "Lam")
    (noPi : label ≠ "Pi") (arguments : List Pattern) : distributes label arguments = false := by
  unfold distributes
  split <;> simp [noApp, noLam, noPi]

/-- **A term whose normal form, pushed in a space, is the atom of a term
pushed in a plain space: its run in the first space is a spelling of the
atom.**  The second clause carries the statement beneath a binder. -/
theorem spelled_run_of_settle {space : Pattern} (plain : PlainSpace space) (pattern : Pattern) :
    (∀ {bound : List TypeExpr} {outer : Pattern} {depth : Nat} {term : LF.Term},
      OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") pattern →
      push outer (settle pattern) = push space (atomAt depth term) →
        Spells space true (runPattern outer pattern) (atomAt depth term)) ∧
    (∀ {binder : Option String} {body : Pattern}, pattern = .lambda binder body →
      ∀ {bound : List TypeExpr} {outer : Pattern} {depth : Nat} {term : LF.Term},
        OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") body →
        push outer (settle body) = push space (atomAt depth term) →
          Spells space true (runPattern outer body) (atomAt depth term)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      refine ⟨?_, fun wrong => by cases wrong⟩
      intro bound outer depth term _ pushed
      rw [settle, push] at pushed
      rcases push_atomAt_cases space depth term with ⟨isLeaf, located⟩ | ⟨_, _, _, located⟩ |
        ⟨_, _, _, located⟩ | ⟨_, _, _, located⟩
      · rw [located] at pushed
        obtain ⟨rfl, same⟩ := runPattern_injective pushed
        rw [same]
        exact .live (.leaf isLeaf)
      · rw [located] at pushed
        simp [runPattern] at pushed
      · rw [located] at pushed
        simp [runPattern] at pushed
      · rw [located] at pushed
        simp [runPattern] at pushed
  | hfvar name =>
      refine ⟨?_, fun wrong => by cases wrong⟩
      intro bound outer depth term sorted _
      rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, _, _, shape, _, _⟩ | ⟨_, _, shape, _, _⟩
      · cases shape
      · cases shape
      · cases shape
      · cases shape
      · simp [runPattern] at shape
  | happly label arguments ih =>
      refine ⟨?_, fun wrong => by cases wrong⟩
      intro bound outer depth term sorted pushed
      rcases atom_cases sorted with ⟨_, shape⟩ | ⟨other, others, shape, listed⟩ |
        ⟨function, argument, shape, sortedFunction, sortedArgument⟩ |
        ⟨binderLabel, domain, body, binding, shape, sortedDomain, sortedBody⟩ |
        ⟨inner, subject, shape, sortedInner, sortedSubject⟩
      · cases shape
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        have noRun : label ≠ "prime-run" := by rintro rfl; exact absurd listed (by decide)
        have noQuote : label ≠ "prime-quote" := by rintro rfl; exact absurd listed (by decide)
        have noApp : label ≠ "App" := by rintro rfl; exact absurd listed (by decide)
        have noLam : label ≠ "Lam" := by rintro rfl; exact absurd listed (by decide)
        have noPi : label ≠ "Pi" := by rintro rfl; exact absurd listed (by decide)
        have normal : settle (.apply label arguments) = .apply label (arguments.map settle) :=
          settle_apply_of_ne noRun noQuote arguments
        rw [normal, push_wraps (distributes_eq_false noApp noLam noPi _)
          (fun both => noRun both.1)] at pushed
        rcases push_atomAt_cases space depth term with ⟨isLeaf, located⟩ | ⟨_, _, _, located⟩ |
          ⟨_, _, _, located⟩ | ⟨_, _, _, located⟩
        · rw [located] at pushed
          obtain ⟨rfl, same⟩ := runPattern_injective pushed
          have noRun' : tokens runLabel (settle (.apply label arguments)) = 0 := by
            rw [normal, same]
            exact tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) term depth
          have noDrop' : tokens dropLabel (settle (.apply label arguments)) = 0 := by
            rw [normal, same]
            exact tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) term depth
          have fixed : settle (.apply label arguments) = .apply label arguments :=
            settle_fixed sorted (by decide) noRun' noDrop'
          have whole : Pattern.apply label arguments = atomAt depth term := by
            rw [← fixed, normal, same]
          rw [whole]
          exact .live (.leaf isLeaf)
        · rw [located] at pushed
          simp [runPattern] at pushed
        · rw [located] at pushed
          simp [runPattern] at pushed
        · rw [located] at pushed
          simp [runPattern] at pushed
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [settle_app, push_app] at pushed
        rcases push_atomAt_cases space depth term with ⟨_, located⟩ |
          ⟨functionTerm, argumentTerm, rfl, located⟩ | ⟨_, _, _, located⟩ | ⟨_, _, _, located⟩
        · rw [located] at pushed
          simp [runPattern] at pushed
        · rw [located] at pushed
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at pushed
          exact Spells.run_app ((ih function (by simp)).1 sortedFunction pushed.1)
            ((ih argument (by simp)).1 sortedArgument pushed.2)
        · rw [located] at pushed
          simp at pushed
        · rw [located] at pushed
          simp at pushed
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [settle_binder binding, push_binder binding] at pushed
        rcases push_atomAt_cases space depth term with ⟨_, located⟩ | ⟨_, _, _, located⟩ |
          ⟨domainTerm, bodyTerm, rfl, located⟩ | ⟨domainTerm, bodyTerm, rfl, located⟩
        · rw [located] at pushed
          simp only [runPattern, Pattern.apply.injEq] at pushed
          rcases binding with rfl | rfl <;> exact absurd pushed.1 (by decide)
        · rw [located] at pushed
          simp only [Pattern.apply.injEq] at pushed
          rcases binding with rfl | rfl <;> exact absurd pushed.1 (by decide)
        · rw [located] at pushed
          simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
            true_and] at pushed
          obtain ⟨rfl, sameDomain, sameBody⟩ := pushed
          exact Spells.run_binder (.inl rfl) ((ih domain (by simp)).1 sortedDomain sameDomain)
            ((ih (.lambda none body) (by simp)).2 rfl sortedBody sameBody)
        · rw [located] at pushed
          simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
            true_and] at pushed
          obtain ⟨rfl, sameDomain, sameBody⟩ := pushed
          exact Spells.run_binder (.inr rfl) ((ih domain (by simp)).1 sortedDomain sameDomain)
            ((ih (.lambda none body) (by simp)).2 rfl sortedBody sameBody)
      · simp only [runPattern, Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        have normal : settle (Pattern.apply "prime-run" [inner, subject]) =
            push (settle inner) (settle subject) := settle_runPattern inner subject
        rw [normal, push_push] at pushed
        have beneath := (ih subject (by simp)).1 sortedSubject pushed
        rcases beneath.run_inv with ⟨same, _, live⟩ | dead
        · have fixed : settle inner = inner :=
            settle_fixed sortedInner (by decide) (by rw [← same]; exact plain.noRun)
              (by rw [← same]; exact plain.noDrop)
          have whole : inner = space := by rw [← fixed, ← same]
          subst whole
          exact .dead outer (.live live)
        · exact .dead outer (.dead inner dead)
  | hlambda binder body ih =>
      refine ⟨?_, ?_⟩
      · intro bound outer depth term sorted _
        rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
          ⟨_, _, _, _, shape, _, _⟩ | ⟨_, _, shape, _, _⟩
        · cases shape
        · cases shape
        · cases shape
        · cases shape
        · simp [runPattern] at shape
      · intro otherBinder otherBody same
        simp only [Pattern.lambda.injEq] at same
        obtain ⟨-, rfl⟩ := same
        exact ih.1
  | hmultiLambda arity binders body _ =>
      refine ⟨?_, fun wrong => by cases wrong⟩
      intro bound outer depth term sorted _
      rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, _, _, shape, _, _⟩ | ⟨_, _, shape, _, _⟩
      · cases shape
      · cases shape
      · cases shape
      · cases shape
      · simp [runPattern] at shape
  | hsubst body replacement _ _ =>
      refine ⟨?_, fun wrong => by cases wrong⟩
      intro bound outer depth term sorted _
      rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, _, _, shape, _, _⟩ | ⟨_, _, shape, _, _⟩
      · cases shape
      · cases shape
      · cases shape
      · cases shape
      · simp [runPattern] at shape
  | hcollection kind elements rest _ =>
      refine ⟨?_, fun wrong => by cases wrong⟩
      intro bound outer depth term sorted _
      rcases atom_cases sorted with ⟨_, shape⟩ | ⟨_, _, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, _, _, shape, _, _⟩ | ⟨_, _, shape, _, _⟩
      · cases shape
      · cases shape
      · cases shape
      · cases shape
      · simp [runPattern] at shape

/-- **Every term whose normal form is the atom of a term pushed in a plain
space is a spelling of that atom, all of whose leaves are located.** -/
theorem spells_of_settle {space : Pattern} (plain : PlainSpace space) {bound : List TypeExpr}
    {pattern : Pattern} {depth : Nat} {term : LF.Term}
    (sorted : OpenPatternWellSorted located FreeTypeContext.empty bound (.base "Atom") pattern)
    (normal : settle pattern = push space (atomAt depth term)) :
    Spells space true pattern (atomAt depth term) := by
  have wrapped := (spelled_run_of_settle plain pattern).1 (outer := .fvar "outside") sorted
    (by rw [normal, push_push])
  rcases wrapped.run_inv with ⟨same, -, -⟩ | whole
  · exact absurd same (plain.node _)
  · exact whole

/-! ## A spelling is equal to the run of the atom -/

/-- The static equivalence passes to the two parts of an application. -/
theorem appTerm_related {stage : List TypeExpr}
    {function next argument other : Contexts.Term located (atomsAt stage)}
    (first : (termSetoid base located (atomsAt stage)).r function next)
    (second : (termSetoid base located (atomsAt stage)).r argument other) :
    (termSetoid base located (atomsAt stage)).r (appTerm function argument)
      (appTerm next other) :=
  .trans _ _ _
    (related_fill (outer := atomsAt stage) (.apply "App" [] .hole [argument.1])
      (fun term => (appTerm term argument).2) first)
    (related_fill (outer := atomsAt stage) (.apply "App" [next.1] .hole [])
      (fun term => (appTerm next term).2) second)

/-- The static equivalence passes to the domain and the body of an
abstraction. -/
theorem lamTerm_related {stage : List TypeExpr}
    {domain next : Contexts.Term located (atomsAt stage)}
    {body other : Contexts.Term located (atomsAt (.base "Atom" :: stage))}
    (first : (termSetoid base located (atomsAt stage)).r domain next)
    (second : (termSetoid base located (atomsAt (.base "Atom" :: stage))).r body other) :
    (termSetoid base located (atomsAt stage)).r (lamTerm domain body) (lamTerm next other) :=
  .trans _ _ _
    (related_fill (outer := atomsAt stage) (.apply "Lam" [] .hole [.lambda none body.1])
      (fun term => (lamTerm term body).2) first)
    (related_fill (outer := atomsAt stage) (.apply "Lam" [next.1] (.lambda none .hole) [])
      (fun term => (lamTerm next term).2) second)

/-- The static equivalence passes to the domain and the body of a product. -/
theorem piTerm_related {stage : List TypeExpr}
    {domain next : Contexts.Term located (atomsAt stage)}
    {body other : Contexts.Term located (atomsAt (.base "Atom" :: stage))}
    (first : (termSetoid base located (atomsAt stage)).r domain next)
    (second : (termSetoid base located (atomsAt (.base "Atom" :: stage))).r body other) :
    (termSetoid base located (atomsAt stage)).r (piTerm domain body) (piTerm next other) :=
  .trans _ _ _
    (related_fill (outer := atomsAt stage) (.apply "Pi" [] .hole [.lambda none body.1])
      (fun term => (piTerm term body).2) first)
    (related_fill (outer := atomsAt stage) (.apply "Pi" [next.1] (.lambda none .hole) [])
      (fun term => (piTerm next term).2) second)

/-- The static equivalence passes to the subject of a run. -/
theorem runTerm_related {stage : List TypeExpr} (space : Contexts.Term located (spacesAt stage))
    {subject next : Contexts.Term located (atomsAt stage)}
    (related : (termSetoid base located (atomsAt stage)).r subject next) :
    (termSetoid base located (atomsAt stage)).r (runTerm space subject) (runTerm space next) :=
  related_fill (outer := atomsAt stage) (.apply "prime-run" [space.1] .hole [])
    (fun term => (runTerm space term).2) related

/-- **A spelling of an atom in a closed space is equal to the run of the
atom**: its run in the space is, and the spelling itself is when all its
leaves are located. -/
theorem spelled_related (space : Contexts.Term located closedSpace) {whole : Bool}
    {pattern atom : Pattern} (spelled : Spells space.1 whole pattern atom) :
    ∀ {stage : List TypeExpr}
      (sorted : OpenPatternWellSorted located FreeTypeContext.empty stage (.base "Atom") pattern)
      (plain : OpenPatternWellSorted located FreeTypeContext.empty stage (.base "Atom") atom),
      (whole = true → (termSetoid base located (atomsAt stage)).r
        (⟨pattern, sorted⟩ : Contexts.Term located (atomsAt stage))
        (runTerm (spaceAt space stage) ⟨atom, plain⟩)) ∧
      (termSetoid base located (atomsAt stage)).r
        (runTerm (spaceAt space stage) (⟨pattern, sorted⟩ : Contexts.Term located (atomsAt stage)))
        (runTerm (spaceAt space stage) ⟨atom, plain⟩) := by
  induction spelled with
  | leaf _ =>
      intro stage sorted plain
      exact ⟨fun wrong => (by cases wrong), .refl _⟩
  | @app _ function argument first second _ _ ihFunction ihArgument =>
      intro stage sorted plain
      obtain ⟨sortedFunction, sortedArgument⟩ := wellSorted_app_inv sorted
      obtain ⟨plainFunction, plainArgument⟩ := wellSorted_app_inv plain
      obtain ⟨wholeFunction, runFunction⟩ := ihFunction sortedFunction plainFunction
      obtain ⟨wholeArgument, runArgument⟩ := ihArgument sortedArgument plainArgument
      have back : (termSetoid base located (atomsAt stage)).r
          (appTerm (runTerm (spaceAt space stage) ⟨first, plainFunction⟩)
            (runTerm (spaceAt space stage) ⟨second, plainArgument⟩))
          (runTerm (spaceAt space stage) ⟨.apply "App" [first, second], plain⟩) :=
        .symm _ _ (runTerm_app (spaceAt space stage) ⟨first, plainFunction⟩
          ⟨second, plainArgument⟩)
      exact ⟨fun all => .trans _ _ _
          (appTerm_related (wholeFunction all) (wholeArgument all)) back,
        .trans _ _ _ (runTerm_app (spaceAt space stage) ⟨function, sortedFunction⟩
          ⟨argument, sortedArgument⟩) (.trans _ _ _ (appTerm_related runFunction runArgument) back)⟩
  | @binder _ label domain body first second binding _ _ ihDomain ihBody =>
      intro stage sorted plain
      obtain ⟨sortedDomain, sortedBody⟩ := wellSorted_binder_inv binding sorted
      obtain ⟨plainDomain, plainBody⟩ := wellSorted_binder_inv binding plain
      obtain ⟨wholeDomain, runDomain⟩ := ihDomain sortedDomain plainDomain
      obtain ⟨wholeBody, runBody⟩ := ihBody sortedBody plainBody
      rcases binding with rfl | rfl
      · have back : (termSetoid base located (atomsAt stage)).r
            (lamTerm (runTerm (spaceAt space stage) ⟨first, plainDomain⟩)
              (runTerm (spaceAt space (.base "Atom" :: stage)) ⟨second, plainBody⟩))
            (runTerm (spaceAt space stage) ⟨.apply "Lam" [first, .lambda none second], plain⟩) :=
          .symm _ _ (runTerm_lam space ⟨first, plainDomain⟩ ⟨second, plainBody⟩)
        exact ⟨fun all => .trans _ _ _ (lamTerm_related (wholeDomain all) (wholeBody all)) back,
          .trans _ _ _ (runTerm_lam space ⟨domain, sortedDomain⟩ ⟨body, sortedBody⟩)
            (.trans _ _ _ (lamTerm_related runDomain runBody) back)⟩
      · have back : (termSetoid base located (atomsAt stage)).r
            (piTerm (runTerm (spaceAt space stage) ⟨first, plainDomain⟩)
              (runTerm (spaceAt space (.base "Atom" :: stage)) ⟨second, plainBody⟩))
            (runTerm (spaceAt space stage) ⟨.apply "Pi" [first, .lambda none second], plain⟩) :=
          .symm _ _ (runTerm_pi space ⟨first, plainDomain⟩ ⟨second, plainBody⟩)
        exact ⟨fun all => .trans _ _ _ (piTerm_related (wholeDomain all) (wholeBody all)) back,
          .trans _ _ _ (runTerm_pi space ⟨domain, sortedDomain⟩ ⟨body, sortedBody⟩)
            (.trans _ _ _ (piTerm_related runDomain runBody) back)⟩
  | @live _ subject atom _ ih =>
      intro stage sorted plain
      obtain ⟨_, sortedSubject⟩ := wellSorted_run_inv sorted
      obtain ⟨_, runSubject⟩ := ih sortedSubject plain
      exact ⟨fun _ => runSubject,
        .trans _ _ _ (runTerm_run (spaceAt space stage) (spaceAt space stage)
          ⟨subject, sortedSubject⟩) runSubject⟩
  | @dead outer subject atom _ ih =>
      intro stage sorted plain
      obtain ⟨sortedOuter, sortedSubject⟩ := wellSorted_run_inv sorted
      obtain ⟨wholeSubject, _⟩ := ih sortedSubject plain
      have whole : (termSetoid base located (atomsAt stage)).r
          (runTerm ⟨outer, sortedOuter⟩ ⟨subject, sortedSubject⟩)
          (runTerm (spaceAt space stage) ⟨atom, plain⟩) :=
        .trans _ _ _ (runTerm_related ⟨outer, sortedOuter⟩ (wholeSubject rfl))
          (runTerm_run ⟨outer, sortedOuter⟩ (spaceAt space stage) ⟨atom, plain⟩)
      exact ⟨fun _ => whole,
        .trans _ _ _ (runTerm_run (spaceAt space stage) ⟨outer, sortedOuter⟩
          ⟨subject, sortedSubject⟩) whole⟩
  | forget _ ih =>
      intro stage sorted plain
      obtain ⟨whole, _⟩ := ih sorted plain
      exact ⟨fun wrong => (by cases wrong),
        .trans _ _ _ (runTerm_related (spaceAt space stage) (whole rfl))
          (runTerm_run (spaceAt space stage) (spaceAt space stage) ⟨_, plain⟩)⟩

/-! ## The transitions of the run of an atom -/

/-- **The run of the atom of a term determines the term.** -/
theorem runAtom_related_iff {rules : List Dedukti.RewriteRule} {depth : Nat}
    {first second : LF.Term} :
    (termSetoid base located (atomInterface depth)).r (runAtom rules depth first)
      (runAtom rules depth second) ↔ first = second := by
  constructor
  · intro related
    have same := settle_eq_of_related related
    rw [runAtom_val, runAtom_val, settle_run_atomAt, settle_run_atomAt] at same
    have plain := congrArg unlocate same
    rw [unlocate_push _ _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) first depth),
      unlocate_push _ _ (tokens_atomAt (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) second depth)] at plain
    exact atomAt_injective depth plain
  · rintro rfl
    exact .refl _

/-- **Every transition of the run of the atom of a term, in the space of a
list of first-order rules with bound right sides, is to the run of the atom
of a step of the term**, in every theory that declares those rules. -/
theorem runAtom_termStep_inv {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (declared : ∀ rule ∈ rules, theory.rule rule) {depth : Nat}
    {term : LF.Term} {target : Contexts.Term located (atomInterface depth)}
    (step : TermStep locatedEvaluator located (runAtom rules depth term) target) :
    ∃ next, Dedukti.Step theory term next ∧
      (termSetoid locatedEvaluator located (atomInterface depth)).r target
        (runAtom rules depth next) := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  have normal : settle redex.1 = push (ruleSpace rules) (atomAt depth term) := by
    rw [← settle_eq_of_related before]
    exact settle_run_atomAt rules term depth
  have spelled := spells_of_settle (ruleSpace_plain rules) redex.2 normal
  obtain ⟨next, sNext, sourceStep⟩ :=
    spelled_stepAt (ruleSpace_plain rules) (theory := theory) (fun found => by
      obtain ⟨rule, inRules, assignment, rfl, rfl⟩ :=
        AtomsReduce.exists_instance_of_mem_matchResults firstOrder bound found
      exact ⟨_, rfl, Dedukti.Step.root (.rule assignment (declared rule inRules))⟩) fuel spelled
      fired
  have back := (spelled_related (base := locatedEvaluator) (ruleSpaceTerm rules) sNext
    contractum.2 (locatedAtom depth next).2).1 rfl
  exact ⟨next, sourceStep, .trans _ _ _ (.symm _ _ after) back⟩

/-- **The transitions of the run of the atom of a term are the runs of the
atoms of the steps of the term**, in the space of a list of first-order rules
with bound right sides and in a theory whose rules are those of the list and
which has no definition.  At every depth, one transition for one step. -/
theorem runAtom_termStep_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {theory : Theory} (rulesIff : ∀ rule, theory.rule rule ↔ rule ∈ rules)
    (undefined : ∀ name, theory.body name = none) {depth : Nat} {term : LF.Term}
    {target : Contexts.Term located (atomInterface depth)} :
    TermStep locatedEvaluator located (runAtom rules depth term) target ↔
      ∃ next, Dedukti.Step theory term next ∧
        (termSetoid locatedEvaluator located (atomInterface depth)).r target
          (runAtom rules depth next) := by
  constructor
  · exact runAtom_termStep_inv firstOrder bound fun rule member => (rulesIff rule).mpr member
  · rintro ⟨next, sourceStep, related⟩
    exact termStep_between (.refl _)
      (runAtom_termStep firstOrder bound (fun rule member => (rulesIff rule).mp member) undefined
        sourceStep depth) (.symm _ _ related)

#print axioms atom_cases
#print axioms tokens_settle_clean
#print axioms settle_fixed
#print axioms spelled_run_of_settle
#print axioms spells_of_settle
#print axioms spelled_related
#print axioms runAtom_related_iff
#print axioms runAtom_termStep_inv
#print axioms runAtom_termStep_iff

end Mettapedia.Logic.HostingStyles.LocatedAtoms
