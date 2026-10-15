import Mettapedia.Logic.HostingStyles.AmbientRegions.AllHeaded
import Mettapedia.OSLF.MeTTaIL.LinearMatch
import Mettapedia.OSLF.MeTTaIL.DecimalNames

/-!
# Root steps generated from the constructors of atoms

The presentation with every root step headed (`allHeaded`) writes its root
steps by hand: one root step and one root step of a run for each of the eight
constructors of atoms other than the run.  A constructor of atoms that is
added to such a list of constructors without its two root steps takes no
answer of a space, and nothing says so.

This module makes the root steps a function of the constructors.

* `generatedRoots` and `generatedRunRoots` send a list of constructors to the
  root steps and to the root steps of a run of its constructors of atoms other
  than the run (`takesRootSteps`).  How a root step is written, the name of
  the rewrite and the variables of the parts of its subject, is a parameter
  (`RootSpelling`); the spelling `spellingOf` writes the eight constructors as
  they were written by hand and every other constructor by the positions of
  its parts.
* On the constructors of the candidate in which atoms reduce the generated
  root steps are the eight written by hand (`generatedRoots_written`,
  `generatedRunRoots_written`).
* **The generated root steps cover every constructor of atoms**, for every
  list of constructors.  As lists: every constructor that takes root steps has
  its two, and only those have (`mem_generatedRoots`, `generatedRoots_only`,
  `mem_generatedRunRoots`, `generatedRunRoots_only`).  As steps: in every
  language that has the generated root steps, an atom headed by such a
  constructor steps to every answer of the ambient space for it
  (`generatedRoot_step`), and its run in a space steps to the run of every
  answer of that space (`generatedRunRoot_step`), for every spelling that fits
  the constructor (`RootSpelling.Fits`).  `spellingOf` fits every constructor
  (`spellingOf_fits`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.LinearMatch (matchArgs_fvars mergeBindings_of_fresh)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions

/-! ## How a root step is written -/

/-- **How the two root steps of a constructor are written**: the name of its
root step, the name of its root step of a run, and the variables that stand
for the parts of its subject, in order. -/
structure RootSpelling where
  /-- The name of the root step. -/
  root : String
  /-- The name of the root step of a run. -/
  runRoot : String
  /-- The variables of the parts of the subject. -/
  parts : List String
deriving DecidableEq, Repr

/-- **A spelling fits a constructor**: one variable for each parameter, no
variable twice, and none of them the variable of the space of a run. -/
def RootSpelling.Fits (spelling : RootSpelling) (constructor : GrammarRule) : Prop :=
  spelling.parts.length = constructor.params.length ∧ spelling.parts.Nodup ∧
    "space" ∉ spelling.parts

/-- **Positive**: the application, written with `F` and `X`. -/
theorem fits_application :
    (RootSpelling.mk "RootApp" "RunRootApp" ["F", "X"]).Fits applicationConstructor := by
  unfold RootSpelling.Fits
  decide

/-- **Negative**: one variable for two parts, one variable twice, and the
variable of the space of a run. -/
theorem not_fits_application :
    ¬ (RootSpelling.mk "RootApp" "RunRootApp" ["F"]).Fits applicationConstructor ∧
      ¬ (RootSpelling.mk "RootApp" "RunRootApp" ["F", "F"]).Fits applicationConstructor ∧
        ¬ (RootSpelling.mk "RootApp" "RunRootApp" ["space", "X"]).Fits applicationConstructor := by
  unfold RootSpelling.Fits
  decide

/-- The variable of the part at a position, where none was written. -/
def partName (index : Nat) : String := "part" ++ toString index

/-- **The spelling by positions**: the rewrites are named after the label of
the constructor, the variables after the positions of the parts. -/
def positionalSpelling (constructor : GrammarRule) : RootSpelling :=
  { root := "Root:" ++ constructor.label
    runRoot := "RunRoot:" ++ constructor.label
    parts := (List.range constructor.params.length).map partName }

theorem part_ne_space (tail : List Char) : "part".toList ++ tail ≠ "space".toList := by
  have left : "part".toList = ['p', 'a', 'r', 't'] := by decide
  have right : "space".toList = ['s', 'p', 'a', 'c', 'e'] := by decide
  rw [left, right]
  simp

/-- **The spelling by positions fits every constructor.** -/
theorem positionalSpelling_fits (constructor : GrammarRule) :
    (positionalSpelling constructor).Fits constructor := by
  refine ⟨by simp [positionalSpelling],
    Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_range_nodup "part" _, ?_⟩
  intro member
  obtain ⟨index, -, same⟩ := List.mem_map.mp member
  exact Mettapedia.OSLF.MeTTaIL.DecimalNames.prefixed_ne_literal "part" "space" (toString index)
    part_ne_space same

/-- **The spellings that were written by hand**: those of the eight
constructors of atoms other than the run of the candidate in which atoms
reduce, by the label of the constructor. -/
def writtenSpellings : List (String × RootSpelling) :=
  [("=", ⟨"RootEquation", "RunRootEquation", ["L", "R"]⟩),
    ("prime-unit", ⟨"RootUnit", "RunRootUnit", []⟩),
    ("prime-drop", ⟨"RootDrop", "RunRootDrop", ["N"]⟩),
    ("prime-variable", ⟨"RootVariable", "RunRootVariable", ["I"]⟩),
    ("prime-symbol", ⟨"RootSymbol", "RunRootSymbol", ["I"]⟩),
    ("App", ⟨"RootApp", "RunRootApp", ["F", "X"]⟩),
    ("Lam", ⟨"RootLam", "RunRootLam", ["A", "M"]⟩),
    ("Pi", ⟨"RootPi", "RunRootPi", ["A", "M"]⟩)]

/-- No written spelling has a variable twice or the variable of the space of
a run. -/
theorem writtenSpellings_wellWritten :
    ∀ written ∈ writtenSpellings, written.2.parts.Nodup ∧ "space" ∉ written.2.parts := by
  decide

/-- **The spelling of the root steps of a constructor**: the one written by
hand for its label, where that has a variable for each of its parameters, and
the spelling by positions otherwise. -/
def spellingOf (constructor : GrammarRule) : RootSpelling :=
  match writtenSpellings.find? (fun written => written.1 == constructor.label) with
  | some written =>
      if written.2.parts.length = constructor.params.length then written.2
      else positionalSpelling constructor
  | none => positionalSpelling constructor

/-- **Positive**: the application is written as it was by hand. -/
theorem spellingOf_application :
    spellingOf applicationConstructor = ⟨"RootApp", "RunRootApp", ["F", "X"]⟩ := by
  decide

/-- **Negative**: a constructor that no hand wrote is written by positions,
and so is a constructor with the label of the application and three parts. -/
theorem spellingOf_unwritten :
    spellingOf (plainConstructor "prime-pair" "Atom"
        [.simple "first" (.base "Atom"), .simple "second" (.base "Atom")]) =
      ⟨"Root:prime-pair", "RunRoot:prime-pair", ["part0", "part1"]⟩ ∧
    spellingOf (plainConstructor "App" "Atom"
        [.simple "f" (.base "Atom"), .simple "a" (.base "Atom"), .simple "b" (.base "Atom")]) =
      ⟨"Root:App", "RunRoot:App", ["part0", "part1", "part2"]⟩ := by
  decide

/-- **`spellingOf` fits every constructor.** -/
theorem spellingOf_fits (constructor : GrammarRule) :
    (spellingOf constructor).Fits constructor := by
  unfold spellingOf
  cases found : writtenSpellings.find? (fun written => written.1 == constructor.label) with
  | none => exact positionalSpelling_fits constructor
  | some written =>
      by_cases arity : written.2.parts.length = constructor.params.length
      · have listed := writtenSpellings_wellWritten written (List.mem_of_find?_eq_some found)
        simp only [arity, if_true]
        exact ⟨arity, listed.1, listed.2⟩
      · simp only [arity, if_false]
        exact positionalSpelling_fits constructor

/-! ## The generated root steps -/

/-- **A constructor takes root steps**: it is a constructor of atoms other
than the run. -/
def takesRootSteps (constructor : GrammarRule) : Bool :=
  constructor.category == "Atom" && constructor.label != "prime-run"

/-- **Positive**: the application, the abstraction and the dropping. -/
theorem takesRootSteps_application :
    takesRootSteps applicationConstructor = true ∧ takesRootSteps abstractionConstructor = true ∧
      takesRootSteps dropConstructor = true := by
  decide

/-- **Negative**: the run, a constructor of spaces and quotation. -/
theorem not_takesRootSteps_run :
    takesRootSteps runAtomConstructor = false ∧ takesRootSteps addAtomConstructor = false ∧
      takesRootSteps quoteConstructor = false := by
  decide

/-- **The subject of the root steps of a constructor**: the constructor
applied to the variables of its parts. -/
def rootSubject (spelling : RootSpelling) (constructor : GrammarRule) : Pattern :=
  .apply constructor.label (spelling.parts.map .fvar)

/-- **The root steps of a list of constructors**: one for each constructor
that takes root steps,
`AmbientStep(c(parts), answer) ⊢ c(parts) ~> answer`. -/
def generatedRoots (spell : GrammarRule → RootSpelling) (constructors : List GrammarRule) :
    List RewriteRule :=
  (constructors.filter takesRootSteps).map fun constructor =>
    headedRootRule (spell constructor).root (rootSubject (spell constructor) constructor)

/-- **The root steps of a run of a list of constructors**: one for each
constructor that takes root steps,
`PrimeStep(space, c(parts), answer) ⊢ run(space, c(parts)) ~> run(space, answer)`. -/
def generatedRunRoots (spell : GrammarRule → RootSpelling) (constructors : List GrammarRule) :
    List RewriteRule :=
  (constructors.filter takesRootSteps).map fun constructor =>
    headedRunRootRule (spell constructor).runRoot (rootSubject (spell constructor) constructor)

/-- **On the constructors of the candidate in which atoms reduce the generated
root steps are the eight written by hand.** -/
theorem generatedRoots_written : generatedRoots spellingOf atomsReduce.terms = headedRoots := by
  rfl

/-- **And the generated root steps of a run are the eight written by hand.** -/
theorem generatedRunRoots_written :
    generatedRunRoots spellingOf atomsReduce.terms = headedRunRoots := by
  rfl

/-- **Negative**: with the spelling by positions they are other rewrites, of
the same number. -/
theorem generatedRoots_positional :
    generatedRoots positionalSpelling atomsReduce.terms ≠ headedRoots ∧
      (generatedRoots positionalSpelling atomsReduce.terms).length = headedRoots.length := by
  refine ⟨fun same => ?_, by decide⟩
  have names := congrArg (fun rules => rules.map (·.name)) same
  revert names
  decide

variable {spell : GrammarRule → RootSpelling} {constructors : List GrammarRule}

/-! ## They cover the constructors of atoms: as lists -/

/-- **Every constructor that takes root steps has its root step.** -/
theorem mem_generatedRoots {constructor : GrammarRule} (declared : constructor ∈ constructors)
    (takes : takesRootSteps constructor = true) :
    headedRootRule (spell constructor).root (rootSubject (spell constructor) constructor) ∈
      generatedRoots spell constructors :=
  List.mem_map.mpr ⟨constructor, List.mem_filter.mpr ⟨declared, takes⟩, rfl⟩

/-- **And only those have one**: a generated root step is the root step of a
declared constructor of atoms other than the run. -/
theorem generatedRoots_only {rule : RewriteRule}
    (member : rule ∈ generatedRoots spell constructors) :
    ∃ constructor ∈ constructors, takesRootSteps constructor = true ∧
      rule = headedRootRule (spell constructor).root
        (rootSubject (spell constructor) constructor) := by
  obtain ⟨constructor, listed, rfl⟩ := List.mem_map.mp member
  exact ⟨constructor, (List.mem_filter.mp listed).1, (List.mem_filter.mp listed).2, rfl⟩

/-- **Every constructor that takes root steps has its root step of a run.** -/
theorem mem_generatedRunRoots {constructor : GrammarRule} (declared : constructor ∈ constructors)
    (takes : takesRootSteps constructor = true) :
    headedRunRootRule (spell constructor).runRoot (rootSubject (spell constructor) constructor) ∈
      generatedRunRoots spell constructors :=
  List.mem_map.mpr ⟨constructor, List.mem_filter.mpr ⟨declared, takes⟩, rfl⟩

/-- **And only those have one.** -/
theorem generatedRunRoots_only {rule : RewriteRule}
    (member : rule ∈ generatedRunRoots spell constructors) :
    ∃ constructor ∈ constructors, takesRootSteps constructor = true ∧
      rule = headedRunRootRule (spell constructor).runRoot
        (rootSubject (spell constructor) constructor) := by
  obtain ⟨constructor, listed, rfl⟩ := List.mem_map.mp member
  exact ⟨constructor, (List.mem_filter.mp listed).1, (List.mem_filter.mp listed).2, rfl⟩

/-- The root steps of more constructors include those of fewer. -/
theorem generatedRoots_mono {fewer more : List GrammarRule}
    (included : ∀ constructor ∈ fewer, constructor ∈ more) :
    ∀ rule ∈ generatedRoots spell fewer, rule ∈ generatedRoots spell more := by
  intro rule member
  obtain ⟨constructor, declared, takes, rfl⟩ := generatedRoots_only member
  exact mem_generatedRoots (included constructor declared) takes

/-- The root steps of a run of more constructors include those of fewer. -/
theorem generatedRunRoots_mono {fewer more : List GrammarRule}
    (included : ∀ constructor ∈ fewer, constructor ∈ more) :
    ∀ rule ∈ generatedRunRoots spell fewer, rule ∈ generatedRunRoots spell more := by
  intro rule member
  obtain ⟨constructor, declared, takes, rfl⟩ := generatedRunRoots_only member
  exact mem_generatedRunRoots (included constructor declared) takes

/-! ## They cover the constructors of atoms: as steps -/

/-- The variables of the parts are a first-order list of patterns. -/
theorem isMatchCorrectListAux_fvars :
    ∀ names : List String, isMatchCorrectListAux (names.map Pattern.fvar) = true
  | [] => rfl
  | _ :: names => by
      simp [isMatchCorrectListAux, isMatchCorrectAux, isMatchCorrectListAux_fvars names]

/-- The subject of a root step is a first-order pattern. -/
theorem rootSubject_firstOrder (spelling : RootSpelling) (constructor : GrammarRule) :
    isMatchCorrectAux (rootSubject spelling constructor) = true := by
  simp [rootSubject, isMatchCorrectAux, isMatchCorrectListAux_fvars]

/-- **The subject of the root step of a constructor matches every application
of the constructor to as many parts as it has parameters**, when the spelling
fits. -/
theorem rootSubject_matched {spelling : RootSpelling} {constructor : GrammarRule}
    (fits : spelling.Fits constructor) {arguments : List Pattern}
    (arity : arguments.length = constructor.params.length) :
    ∃ bindings : Bindings,
      bindings ∈ matchPattern (rootSubject spelling constructor)
        (.apply constructor.label arguments) ∧
      (bindings.map Prod.fst).Nodup ∧
        ∀ name, name ∈ bindings.map Prod.fst ↔ name ∈ spelling.parts := by
  obtain ⟨bindings, member, nodup, names, -⟩ :=
    matchArgs_fvars spelling.parts arguments fits.2.1 (fits.1.trans arity.symm)
  refine ⟨bindings, ?_, nodup, names⟩
  have lengths : (spelling.parts.map Pattern.fvar).length = arguments.length := by
    rw [List.length_map]
    exact fits.1.trans arity.symm
  simp only [rootSubject, matchPattern, beq_self_eq_true, lengths, Bool.and_self, if_true]
  exact member

/-- **And its run matches the run of every such application.** -/
theorem runRootSubject_matched {spelling : RootSpelling} {constructor : GrammarRule}
    (fits : spelling.Fits constructor) {arguments : List Pattern}
    (arity : arguments.length = constructor.params.length) (space : Pattern) :
    ∃ bindings : Bindings,
      bindings ∈ matchPattern (runPattern (.fvar "space") (rootSubject spelling constructor))
        (runPattern space (.apply constructor.label arguments)) := by
  obtain ⟨inner, member, nodup, names⟩ := rootSubject_matched fits arity
  have fresh : ∀ name ∈ inner.map Prod.fst,
      name ∉ ([("space", space)] : Bindings).map Prod.fst := by
    intro name listed
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    intro same
    exact fits.2.2 (same ▸ (names name).mp listed)
  have merged := mergeBindings_of_fresh inner [("space", space)] fresh nodup
  refine ⟨inner.reverse ++ [("space", space)], ?_⟩
  simp only [runPattern, matchPattern, beq_self_eq_true, List.length_cons, List.length_nil,
    Bool.and_self, if_true, matchArgs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filterMap_cons, List.filterMap_nil, List.mem_filterMap, List.mem_flatMap]
  exact ⟨inner, ⟨inner, member, by simp [mergeBindings]⟩, merged⟩

variable {lang : LanguageDef} {admits : Pattern → Bool}

/-- **In a language that has the generated root steps, an atom headed by a
constructor that takes root steps steps to every answer of the ambient space
for it.** -/
theorem generatedRoot_step
    (included : ∀ rule ∈ generatedRoots spell constructors, rule ∈ lang.rewrites)
    {constructor : GrammarRule} (declared : constructor ∈ constructors)
    (takes : takesRootSteps constructor = true) (fits : (spell constructor).Fits constructor)
    {arguments : List Pattern} (arity : arguments.length = constructor.params.length)
    {ambientSpace answer : Pattern}
    (found : answer ∈ admittedAnswers admits ambientSpace (.apply constructor.label arguments)) :
    Step (regionEvaluator admits ambientSpace) lang (.apply constructor.label arguments)
      answer := by
  obtain ⟨bindings, matched, -, -⟩ := rootSubject_matched fits arity
  exact ⟨1, step_headedRoot (included _ (mem_generatedRoots declared takes)) matched
    (matchPattern_correct matched (rootSubject_firstOrder _ _)) found⟩

/-- **And its run in a space steps to the run of every answer of that space
for it**, at every ambient space. -/
theorem generatedRunRoot_step
    (included : ∀ rule ∈ generatedRunRoots spell constructors, rule ∈ lang.rewrites)
    {constructor : GrammarRule} (declared : constructor ∈ constructors)
    (takes : takesRootSteps constructor = true) (fits : (spell constructor).Fits constructor)
    {arguments : List Pattern} (arity : arguments.length = constructor.params.length)
    (ambientSpace : Pattern) {space answer : Pattern}
    (found : answer ∈ admittedAnswers admits space (.apply constructor.label arguments)) :
    Step (regionEvaluator admits ambientSpace) lang
      (runPattern space (.apply constructor.label arguments)) (runPattern space answer) := by
  obtain ⟨bindings, matched⟩ := runRootSubject_matched fits arity space
  have exactRun : isMatchCorrectAux
      (.apply "prime-run" [.fvar "space", rootSubject (spell constructor) constructor]) = true := by
    simp [isMatchCorrectAux, isMatchCorrectListAux, rootSubject_firstOrder]
  have rebuiltRun := matchPattern_correct
    (show bindings ∈ matchPattern
      (.apply "prime-run" [.fvar "space", rootSubject (spell constructor) constructor])
      (.apply "prime-run" [space, .apply constructor.label arguments]) from matched) exactRun
  have parts : applyBindings bindings (.fvar "space") = space ∧
      applyBindings bindings (rootSubject (spell constructor) constructor) =
        .apply constructor.label arguments := by
    have unfolded : Pattern.apply "prime-run"
        [applyBindings bindings (.fvar "space"),
          applyBindings bindings (rootSubject (spell constructor) constructor)] =
          .apply "prime-run" [space, .apply constructor.label arguments] := by
      rw [← rebuiltRun]
      conv_rhs => rw [applyBindings]
      rfl
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
    exact unfolded
  exact ⟨1, step_headedRunRoot (included _ (mem_generatedRunRoots declared takes)) matched parts.1
    parts.2 found⟩

#print axioms fits_application
#print axioms not_fits_application
#print axioms positionalSpelling_fits
#print axioms writtenSpellings_wellWritten
#print axioms spellingOf_application
#print axioms spellingOf_unwritten
#print axioms spellingOf_fits
#print axioms takesRootSteps_application
#print axioms not_takesRootSteps_run
#print axioms generatedRoots_written
#print axioms generatedRunRoots_written
#print axioms generatedRoots_positional
#print axioms mem_generatedRoots
#print axioms generatedRoots_only
#print axioms mem_generatedRunRoots
#print axioms generatedRunRoots_only
#print axioms generatedRoots_mono
#print axioms generatedRunRoots_mono
#print axioms rootSubject_matched
#print axioms runRootSubject_matched
#print axioms generatedRoot_step
#print axioms generatedRunRoot_step
#print axioms part_ne_space
#print axioms isMatchCorrectListAux_fvars
#print axioms rootSubject_firstOrder

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
