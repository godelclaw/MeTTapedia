import Mettapedia.Logic.HostingStyles.LocatedAtoms.Steps

/-!
# The spellings of an atom located in one space, and what their steps are

With the equations of a run, the run of the atom of a term has many
spellings: the run may stand at the root, at the leaves, or anywhere between,
and a run that is no longer read may stand around a run.  A transition of the
candidate with located atoms may start at any of them.  This module describes
the spellings by a relation and shows that a step from a spelling is a step
of the term.

* A space is **plain** (`PlainSpace`) when it is its own normal form, has no
  loose bound variable, no run and no dropping, and is no pattern variable.
  The space of a list of rules is plain (`ruleSpace_plain`); a space that
  stores a bound variable is not (`storesVariable_not_plain`).
* `Spells space whole pattern atom` says that `pattern` is a spelling of the
  plain atom `atom` in which every leaf is in no run or in a run in `space`:
  a leaf of the atom, an application, an abstraction or a product of
  spellings, the run of a spelling in `space` (`live`), or any run around a
  spelling all of whose leaves are located (`dead`: the outer space is not
  read).  `whole` says that every leaf is located.
* A spelling has the normal form of the atom pushed in the space
  (`Spells.settle_whole`, `Spells.settle_partial`), and spellings are closed
  under lifting and under the instantiation of a bound variable by a spelling
  (`Spells.lift`, `Spells.instantiate`): the space is plain.
* The run of an application is spelled exactly when the runs of its two parts
  are (`Spells.run_app`, `Spells.run_app_inv`), and the same for the two
  binders (`Spells.run_binder`, `Spells.run_binder_inv`).  This is the
  equation of distribution, read on spellings.
* **A step of the candidate from a spelling of the atom of a term reaches a
  spelling of the atom of a step of the term** (`spelled_stepAt`), in every
  theory whose root steps include what the space answers.  The sixteen
  rewrites are read one by one; the root step of a run reads the space in
  which its subject is located, which is `space` for a spelling.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory inst patternVars usesOnly)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.GSLT.LanguageDef.LFTyping (subst0)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
  (liftBVars liftBVarsList instantiateBVarAt instantiateBVar liftBVars_eq_self_of_isWellScopedAt
    instantiateBVarAt_eq_self_of_isWellScopedAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (isWellScopedAt_mono)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (ruleSpace_wellSorted_of numeral_wellSorted_of)

/-! ## Plain spaces -/

/-- **A plain space**: its own normal form, with no loose bound variable, no
run and no dropping, and no pattern variable. -/
structure PlainSpace (space : Pattern) : Prop where
  normal : settle space = space
  lifted : ∀ cutoff shift : Nat, liftBVars cutoff shift space = space
  instantiated : ∀ (depth : Nat) (replacement : Pattern),
    instantiateBVarAt depth replacement space = space
  noRun : tokens runLabel space = 0
  noDrop : tokens dropLabel space = 0
  node : ∀ name : String, space ≠ .fvar name

/-- **Positive**: the space of a list of rules. -/
theorem ruleSpace_plain (rules : List Dedukti.RewriteRule) : PlainSpace (ruleSpace rules) where
  normal := settle_ruleSpace rules
  lifted := fun _ _ => liftBVars_eq_self_of_isWellScopedAt
    (isWellScopedAt_mono (ruleSpace_wellSorted_of located_carriesAtoms rules).2.2.2
      (Nat.zero_le _))
  instantiated := fun _ _ => instantiateBVarAt_eq_self_of_isWellScopedAt
    (isWellScopedAt_mono (ruleSpace_wellSorted_of located_carriesAtoms rules).2.2.2
      (Nat.zero_le _))
  noRun := tokens_ruleSpace (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rules
  noDrop := tokens_ruleSpace (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rules
  node := fun name same => by
    cases rules with
    | nil => simp [ruleSpace, spaceOfAtoms, emptySpace] at same
    | cons rule rules => simp [ruleSpace, spaceOfAtoms, addAtom] at same

/-- **Negative**: a space that stores a bound variable is not plain. -/
theorem storesVariable_not_plain : ¬ PlainSpace (storesVariable 0) :=
  fun plain => absurd (plain.lifted 0 1) (by decide)

/-! ## The leaves of the atom of a term -/

/-- **A leaf of the atom of a term**: a bound variable, a symbol or a variable
atom. -/
def IsLeaf (atom : Pattern) : Prop :=
  (∃ index, atom = .bvar index) ∨ (∃ code, atom = symbolAtom code) ∨
    ∃ index, atom = variableAtom (numeral index)

theorem isLeaf_atomAt_var (depth index : Nat) : IsLeaf (atomAt depth (.var index)) := by
  by_cases below : index < depth
  · rw [atomAt_var_of_lt below]
    exact .inl ⟨_, rfl⟩
  · rw [atomAt_var_of_le (Nat.le_of_not_lt below)]
    exact .inr (.inr ⟨_, rfl⟩)

theorem isLeaf_atomAt_srt (depth : Nat) (sort : LF.Srt) : IsLeaf (atomAt depth (.srt sort)) := by
  rw [atomAt_srt]
  exact .inr (.inl ⟨_, rfl⟩)

/-- **Positive**: the atom of a constant. -/
theorem isLeaf_atomAt_con (depth : Nat) (name : String) : IsLeaf (atomAt depth (.con name)) :=
  .inr (.inl ⟨_, rfl⟩)

/-- The head of a leaf that is a node. -/
theorem IsLeaf.head {atom : Pattern} (leaf : IsLeaf atom) {label : String}
    {arguments : List Pattern} (shape : atom = .apply label arguments) :
    label = "prime-symbol" ∨ label = "prime-variable" := by
  rcases leaf with ⟨index, rfl⟩ | ⟨code, rfl⟩ | ⟨index, rfl⟩
  · cases shape
  · simp only [symbolAtom, Pattern.apply.injEq] at shape
    exact .inl shape.1.symm
  · simp only [variableAtom, Pattern.apply.injEq] at shape
    exact .inr shape.1.symm

/-- **Negative**: an application is no leaf. -/
theorem not_isLeaf_app (function argument : Pattern) :
    ¬ IsLeaf (.apply "App" [function, argument]) := fun leaf => by
  rcases leaf.head rfl with wrong | wrong <;> exact absurd wrong (by decide)

theorem settle_numeral (count : Nat) : settle (numeral count) = numeral count := by
  rw [settle_eq_contract _ (tokens_numeral (by decide) (by decide) count)
    (numeral_wellSorted_of located_carriesAtoms [] count).2.1]
  exact contract_numeral count

/-- A leaf is its own normal form. -/
theorem IsLeaf.settle_eq {atom : Pattern} (leaf : IsLeaf atom) : settle atom = atom := by
  rcases leaf with ⟨index, rfl⟩ | ⟨code, rfl⟩ | ⟨index, rfl⟩
  · rw [settle]
  · rw [symbolAtom, settle_apply_of_ne (by decide) (by decide)]
    simp [settle_numeral]
  · rw [variableAtom, settle_apply_of_ne (by decide) (by decide)]
    simp [settle_numeral]

/-- A leaf, pushed in a space, is in a run in that space. -/
theorem IsLeaf.push_eq {atom : Pattern} (leaf : IsLeaf atom) (space : Pattern) :
    push space atom = runPattern space atom := by
  rcases leaf with ⟨index, rfl⟩ | ⟨code, rfl⟩ | ⟨index, rfl⟩
  · rw [push]
  · exact push_wraps (by rfl) (fun both => absurd both.1 (by decide)) space
  · exact push_wraps (by rfl) (fun both => absurd both.1 (by decide)) space

/-- A leaf, lifted, is a leaf. -/
theorem IsLeaf.lift {atom : Pattern} (leaf : IsLeaf atom) (cutoff shift : Nat) :
    IsLeaf (liftBVars cutoff shift atom) := by
  rcases leaf with ⟨index, rfl⟩ | ⟨code, rfl⟩ | ⟨index, rfl⟩
  · rw [liftBVars]
    split <;> exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨code, by simp [symbolAtom, liftBVars, liftBVarsList, liftBVars_numeral]⟩)
  · exact .inr (.inr ⟨index, by
      simp [variableAtom, liftBVars, liftBVarsList, liftBVars_numeral]⟩)

/-! ## Spellings -/

/-- **A spelling of a plain atom with its leaves in one space.**  `whole`
says that every leaf is located. -/
inductive Spells (space : Pattern) : Bool → Pattern → Pattern → Prop where
  | leaf {atom : Pattern} : IsLeaf atom → Spells space false atom atom
  | app {whole : Bool} {function argument first second : Pattern} :
      Spells space whole function first → Spells space whole argument second →
        Spells space whole (.apply "App" [function, argument]) (.apply "App" [first, second])
  | binder {whole : Bool} {label : String} {domain body first second : Pattern} :
      (label = "Lam" ∨ label = "Pi") →
      Spells space whole domain first → Spells space whole body second →
        Spells space whole (.apply label [domain, .lambda none body])
          (.apply label [first, .lambda none second])
  | live {whole : Bool} {subject atom : Pattern} :
      Spells space whole subject atom → Spells space true (runPattern space subject) atom
  | dead (outer : Pattern) {subject atom : Pattern} :
      Spells space true subject atom → Spells space true (runPattern outer subject) atom
  | forget {pattern atom : Pattern} :
      Spells space true pattern atom → Spells space false pattern atom

namespace Spells

variable {space : Pattern}

/-- A spelling, without the knowledge that every leaf is located. -/
theorem weaken {whole : Bool} {pattern atom : Pattern} (spelled : Spells space whole pattern atom) :
    Spells space false pattern atom := by
  cases whole with
  | false => exact spelled
  | true => exact .forget spelled

/-- A spelling all of whose leaves are located, at any flag. -/
theorem ofWhole {whole : Bool} {pattern atom : Pattern} (spelled : Spells space true pattern atom) :
    Spells space whole pattern atom := by
  cases whole with
  | false => exact .forget spelled
  | true => exact spelled

/-- **Positive**: the atom of a term spells itself. -/
theorem atom (space : Pattern) (term : LF.Term) :
    ∀ depth : Nat, Spells space false (atomAt depth term) (atomAt depth term) := by
  induction term with
  | var index => intro depth; exact .leaf (isLeaf_atomAt_var depth index)
  | srt sort => intro depth; exact .leaf (isLeaf_atomAt_srt depth sort)
  | con name => intro depth; exact .leaf (isLeaf_atomAt_con depth name)
  | app function argument ihFunction ihArgument =>
      intro depth
      exact .app (ihFunction depth) (ihArgument depth)
  | lam domain body ihDomain ihBody =>
      intro depth
      exact .binder (.inl rfl) (ihDomain depth) (ihBody (depth + 1))
  | pi domain body ihDomain ihBody =>
      intro depth
      exact .binder (.inr rfl) (ihDomain depth) (ihBody (depth + 1))

/-- The head of a spelling that is a node. -/
theorem head {whole : Bool} {label : String} {arguments : List Pattern} {atom : Pattern}
    (spelled : Spells space whole (.apply label arguments) atom) :
    label ∈ ["App", "Lam", "Pi", "prime-run", "prime-symbol", "prime-variable"] := by
  generalize shape : Pattern.apply label arguments = pattern at spelled
  induction spelled with
  | leaf isLeaf => rcases isLeaf.head shape.symm with rfl | rfl <;> decide
  | app _ _ _ _ =>
      simp only [Pattern.apply.injEq] at shape
      rw [shape.1]
      decide
  | binder binding _ _ _ _ =>
      simp only [Pattern.apply.injEq] at shape
      rw [shape.1]
      rcases binding with rfl | rfl <;> decide
  | live _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      rw [shape.1]
      decide
  | dead _ _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      rw [shape.1]
      decide
  | forget _ ih => exact ih shape

/-- **Negative**: a dropping spells no atom. -/
theorem not_dropped {whole : Bool} {name atom : Pattern} :
    ¬ Spells space whole (dropped name) atom := fun spelled =>
  absurd (spelled.head) (by decide)

/-- What a spelling that is an application is. -/
theorem app_inv {whole : Bool} {function argument atom : Pattern}
    (spelled : Spells space whole (.apply "App" [function, argument]) atom) :
    ∃ first second, atom = .apply "App" [first, second] ∧ Spells space whole function first ∧
      Spells space whole argument second := by
  generalize shape : Pattern.apply "App" [function, argument] = pattern at spelled
  induction spelled with
  | leaf isLeaf =>
      rcases isLeaf.head shape.symm with wrong | wrong <;> exact absurd wrong (by decide)
  | app sFunction sArgument _ _ =>
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
      obtain ⟨rfl, rfl⟩ := shape
      exact ⟨_, _, rfl, sFunction, sArgument⟩
  | binder binding _ _ _ _ =>
      simp only [Pattern.apply.injEq] at shape
      rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  | live _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      exact absurd shape.1 (by decide)
  | dead _ _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      exact absurd shape.1 (by decide)
  | forget _ ih =>
      obtain ⟨first, second, rfl, sFunction, sArgument⟩ := ih shape
      exact ⟨first, second, rfl, .forget sFunction, .forget sArgument⟩

/-- What a spelling that is an abstraction or a product is. -/
theorem binder_inv {whole : Bool} {label : String} (binding : label = "Lam" ∨ label = "Pi")
    {domain abstraction atom : Pattern}
    (spelled : Spells space whole (.apply label [domain, abstraction]) atom) :
    ∃ body first second, abstraction = .lambda none body ∧
      atom = .apply label [first, .lambda none second] ∧ Spells space whole domain first ∧
        Spells space whole body second := by
  generalize shape : Pattern.apply label [domain, abstraction] = pattern at spelled
  induction spelled with
  | leaf isLeaf =>
      rcases isLeaf.head shape.symm with wrong | wrong <;>
        rcases binding with rfl | rfl <;> exact absurd wrong (by decide)
  | app _ _ _ _ =>
      simp only [Pattern.apply.injEq] at shape
      rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  | binder _ sDomain sBody _ _ =>
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at shape
      obtain ⟨rfl, rfl, rfl⟩ := shape
      exact ⟨_, _, _, rfl, rfl, sDomain, sBody⟩
  | live _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  | dead _ _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  | forget _ ih =>
      obtain ⟨body, first, second, rfl, rfl, sDomain, sBody⟩ := ih shape
      exact ⟨body, first, second, rfl, rfl, .forget sDomain, .forget sBody⟩

/-- **What a spelling that is a run is**: the run of a spelling in the space,
or a run around a spelling all of whose leaves are located. -/
theorem run_inv {whole : Bool} {outer subject atom : Pattern}
    (spelled : Spells space whole (runPattern outer subject) atom) :
    (space = outer ∧ ∃ other, Spells space other subject atom) ∨ Spells space true subject atom := by
  generalize shape : runPattern outer subject = pattern at spelled
  induction spelled with
  | leaf isLeaf =>
      rcases isLeaf.head (label := "prime-run") (arguments := [outer, subject]) shape.symm with
        wrong | wrong <;> exact absurd wrong (by decide)
  | app _ _ _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      exact absurd shape.1 (by decide)
  | binder binding _ _ _ _ =>
      simp only [runPattern, Pattern.apply.injEq] at shape
      rcases binding with rfl | rfl <;> exact absurd shape.1 (by decide)
  | live sSubject _ =>
      obtain ⟨rfl, rfl⟩ := runPattern_injective shape
      exact .inl ⟨rfl, _, sSubject⟩
  | dead _ sSubject _ =>
      obtain ⟨rfl, rfl⟩ := runPattern_injective shape
      exact .inr sSubject
  | forget _ ih => exact ih shape

/-- A spelling that is a run has every leaf located. -/
theorem run_whole {whole : Bool} {outer subject atom : Pattern}
    (spelled : Spells space whole (runPattern outer subject) atom) :
    Spells space true (runPattern outer subject) atom := by
  rcases spelled.run_inv with ⟨rfl, other, live⟩ | dead
  · exact .live live
  · exact .dead outer dead

/-! ## The equations of distribution, on spellings -/

/-- **The run of an application is spelled when the runs of its two parts
are.** -/
theorem run_app {outer function argument first second : Pattern}
    (sFunction : Spells space true (runPattern outer function) first)
    (sArgument : Spells space true (runPattern outer argument) second) :
    Spells space true (runPattern outer (.apply "App" [function, argument]))
      (.apply "App" [first, second]) := by
  rcases sFunction.run_inv with ⟨rfl, _, liveFunction⟩ | deadFunction
  · rcases sArgument.run_inv with ⟨_, _, liveArgument⟩ | deadArgument
    · exact .live (.app liveFunction.weaken liveArgument.weaken)
    · exact .live (.app liveFunction.weaken deadArgument.weaken)
  · rcases sArgument.run_inv with ⟨rfl, _, liveArgument⟩ | deadArgument
    · exact .live (.app deadFunction.weaken liveArgument.weaken)
    · exact .dead outer (.app deadFunction deadArgument)

/-- **The runs of the two parts of an application are spelled when the run of
the application is.** -/
theorem run_app_inv {whole : Bool} {outer function argument atom : Pattern}
    (spelled : Spells space whole (runPattern outer (.apply "App" [function, argument])) atom) :
    ∃ first second, atom = .apply "App" [first, second] ∧
      Spells space true (runPattern outer function) first ∧
        Spells space true (runPattern outer argument) second := by
  rcases spelled.run_inv with ⟨rfl, _, live⟩ | dead
  · obtain ⟨first, second, rfl, sFunction, sArgument⟩ := live.app_inv
    exact ⟨first, second, rfl, .live sFunction, .live sArgument⟩
  · obtain ⟨first, second, rfl, sFunction, sArgument⟩ := dead.app_inv
    exact ⟨first, second, rfl, .dead outer sFunction, .dead outer sArgument⟩

/-- The run of an abstraction or of a product is spelled when the runs of its
domain and of its body are. -/
theorem run_binder {label : String} (binding : label = "Lam" ∨ label = "Pi")
    {outer domain body first second : Pattern}
    (sDomain : Spells space true (runPattern outer domain) first)
    (sBody : Spells space true (runPattern outer body) second) :
    Spells space true (runPattern outer (.apply label [domain, .lambda none body]))
      (.apply label [first, .lambda none second]) := by
  rcases sDomain.run_inv with ⟨rfl, _, liveDomain⟩ | deadDomain
  · rcases sBody.run_inv with ⟨_, _, liveBody⟩ | deadBody
    · exact .live (.binder binding liveDomain.weaken liveBody.weaken)
    · exact .live (.binder binding liveDomain.weaken deadBody.weaken)
  · rcases sBody.run_inv with ⟨rfl, _, liveBody⟩ | deadBody
    · exact .live (.binder binding deadDomain.weaken liveBody.weaken)
    · exact .dead outer (.binder binding deadDomain deadBody)

/-- The runs of the domain and of the body of an abstraction or of a product
are spelled when the run of the whole is. -/
theorem run_binder_inv {whole : Bool} {label : String} (binding : label = "Lam" ∨ label = "Pi")
    {outer domain abstraction atom : Pattern}
    (spelled : Spells space whole (runPattern outer (.apply label [domain, abstraction])) atom) :
    ∃ body first second, abstraction = .lambda none body ∧
      atom = .apply label [first, .lambda none second] ∧
        Spells space true (runPattern outer domain) first ∧
          Spells space true (runPattern outer body) second := by
  rcases spelled.run_inv with ⟨rfl, _, live⟩ | dead
  · obtain ⟨body, first, second, rfl, rfl, sDomain, sBody⟩ := live.binder_inv binding
    exact ⟨body, first, second, rfl, rfl, .live sDomain, .live sBody⟩
  · obtain ⟨body, first, second, rfl, rfl, sDomain, sBody⟩ := dead.binder_inv binding
    exact ⟨body, first, second, rfl, rfl, .dead outer sDomain, .dead outer sBody⟩

/-! ## The normal form of a spelling -/

/-- The normal form of a spelling, pushed in the space, is the atom pushed in
the space; and it is that already when every leaf is located. -/
theorem settle_both (plain : PlainSpace space) {whole : Bool} {pattern atom : Pattern}
    (spelled : Spells space whole pattern atom) :
    push space (settle pattern) = push space atom ∧
      (whole = true → settle pattern = push space atom) := by
  induction spelled with
  | leaf isLeaf => exact ⟨by rw [isLeaf.settle_eq], fun wrong => by cases wrong⟩
  | app _ _ ihFunction ihArgument =>
      exact ⟨by rw [settle_app, push_app, push_app, ihFunction.1, ihArgument.1], fun all => by
        rw [settle_app, push_app, ihFunction.2 all, ihArgument.2 all]⟩
  | binder binding _ _ ihDomain ihBody =>
      exact ⟨by rw [settle_binder binding, push_binder binding, push_binder binding, ihDomain.1,
        ihBody.1], fun all => by
        rw [settle_binder binding, push_binder binding, ihDomain.2 all, ihBody.2 all]⟩
  | @live _ subject atom _ ih =>
      have located : settle (runPattern space subject) = push space atom := by
        rw [settle_runPattern, plain.normal, ih.1]
      exact ⟨by rw [located, push_push], fun _ => located⟩
  | @dead outer subject atom _ ih =>
      have located : settle (runPattern outer subject) = push space atom := by
        rw [settle_runPattern, ih.2 rfl, push_push]
      exact ⟨by rw [located, push_push], fun _ => located⟩
  | forget _ ih => exact ⟨by rw [ih.2 rfl, push_push], fun wrong => by cases wrong⟩

/-- **The normal form of a spelling all of whose leaves are located is the
atom pushed in the space.** -/
theorem settle_whole (plain : PlainSpace space) {pattern atom : Pattern}
    (spelled : Spells space true pattern atom) : settle pattern = push space atom :=
  (spelled.settle_both plain).2 rfl

/-- The normal form of a spelling, pushed in the space. -/
theorem settle_partial (plain : PlainSpace space) {whole : Bool} {pattern atom : Pattern}
    (spelled : Spells space whole pattern atom) :
    push space (settle pattern) = push space atom :=
  (spelled.settle_both plain).1

/-! ## Lifting and instantiation -/

/-- **A spelling, lifted, spells the lifted atom**: the space has no loose
bound variable. -/
theorem lift (plain : PlainSpace space) {whole : Bool} {pattern atom : Pattern}
    (spelled : Spells space whole pattern atom) :
    ∀ cutoff shift : Nat,
      Spells space whole (liftBVars cutoff shift pattern) (liftBVars cutoff shift atom) := by
  induction spelled with
  | leaf isLeaf => intro cutoff shift; exact .leaf (isLeaf.lift cutoff shift)
  | app _ _ ihFunction ihArgument =>
      intro cutoff shift
      simpa [liftBVars, liftBVarsList] using
        Spells.app (ihFunction cutoff shift) (ihArgument cutoff shift)
  | binder binding _ _ ihDomain ihBody =>
      intro cutoff shift
      simpa [liftBVars, liftBVarsList] using
        Spells.binder binding (ihDomain cutoff shift) (ihBody (cutoff + 1) shift)
  | live _ ih =>
      intro cutoff shift
      simpa [runPattern, liftBVars, liftBVarsList, plain.lifted] using
        Spells.live (space := space) (ih cutoff shift)
  | dead outer _ ih =>
      intro cutoff shift
      simpa [runPattern, liftBVars, liftBVarsList] using
        Spells.dead (liftBVars cutoff shift outer) (ih cutoff shift)
  | forget _ ih => intro cutoff shift; exact .forget (ih cutoff shift)

/-- **A bound variable of a spelling, instantiated by a spelling, gives a
spelling of the instantiated atom.**  This is beta on spellings. -/
theorem instantiate (plain : PlainSpace space) {whole other : Bool}
    {body atom argument value : Pattern} (spelled : Spells space whole body atom)
    (filling : Spells space other argument value) :
    ∀ depth : Nat, Spells space whole (instantiateBVarAt depth argument body)
      (instantiateBVarAt depth value atom) := by
  induction spelled with
  | leaf isLeaf =>
      intro depth
      rcases isLeaf with ⟨index, rfl⟩ | ⟨code, rfl⟩ | ⟨index, rfl⟩
      · simp only [instantiateBVarAt]
        split_ifs with below same
        · exact .leaf (.inl ⟨_, rfl⟩)
        · exact (filling.lift plain 0 depth).weaken
        · exact .leaf (.inl ⟨_, rfl⟩)
      · have fixed : ∀ replacement : Pattern,
            instantiateBVarAt depth replacement (symbolAtom code) = symbolAtom code :=
          fun replacement => by simp [symbolAtom, instantiateBVarAt, instantiateBVarAt_numeral]
        rw [fixed, fixed]
        exact .leaf (.inr (.inl ⟨code, rfl⟩))
      · have fixed : ∀ replacement : Pattern,
            instantiateBVarAt depth replacement (variableAtom (numeral index)) =
              variableAtom (numeral index) :=
          fun replacement => by simp [variableAtom, instantiateBVarAt, instantiateBVarAt_numeral]
        rw [fixed, fixed]
        exact .leaf (.inr (.inr ⟨index, rfl⟩))
  | app _ _ ihFunction ihArgument =>
      intro depth
      simpa [instantiateBVarAt] using Spells.app (ihFunction depth) (ihArgument depth)
  | binder binding _ _ ihDomain ihBody =>
      intro depth
      simpa [instantiateBVarAt] using Spells.binder binding (ihDomain depth) (ihBody (depth + 1))
  | live _ ih =>
      intro depth
      simpa [runPattern, instantiateBVarAt, plain.instantiated] using
        Spells.live (space := space) (ih depth)
  | dead outer _ ih =>
      intro depth
      simpa [runPattern, instantiateBVarAt] using
        Spells.dead (instantiateBVarAt depth argument outer) (ih depth)
  | forget _ ih => intro depth; exact .forget (ih depth)

end Spells

/-! ## A step from a spelling -/

/-- **A step of the candidate from a spelling of the atom of a term reaches a
spelling of the atom of a step of the term**, in every theory whose steps at
the root include what the space answers for the atoms of terms.  At every
depth, and whether or not every leaf is located. -/
theorem spelled_stepAt {space : Pattern} (plain : PlainSpace space) {theory : Theory}
    (answers : ∀ {depth : Nat} {term : LF.Term} {answer : Pattern},
      answer ∈ matchResults space (atomAt depth term) →
        ∃ next, answer = atomAt depth next ∧ Dedukti.Step theory term next) :
    ∀ (fuel : Nat) {whole : Bool} {pattern target : Pattern} {depth : Nat} {term : LF.Term},
      Spells space whole pattern (atomAt depth term) →
      StepAt locatedEvaluator located fuel pattern target →
        ∃ next, Spells space whole target (atomAt depth next) ∧ Dedukti.Step theory term next := by
  intro fuel
  induction fuel with
  | zero => intro whole pattern target depth term _ step; cases step
  | succ fuel ih =>
      intro whole pattern target depth term spelled step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [located_rewrites, atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        obtain ⟨first, second, shape, sFunction, sArgument⟩ := spelled.app_inv
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨inner, domainAtom, bodyAtom, sameAbstraction, shapeLam, _, sBody⟩ :=
          sFunction.binder_inv (.inl rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shapeLam
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        refine ⟨subst0 argumentTerm bodyTerm, ?_,
          Dedukti.Step.root (.beta domainTerm bodyTerm argumentTerm)⟩
        rw [applied, ← instantiateBVar_atomAt]
        exact sBody.instantiate plain sArgument 0
      · obtain ⟨function, argument, next, rfl, inner, applied⟩ := appFunction_inv matched premises
        obtain ⟨first, second, shape, sFunction, sArgument⟩ := spelled.app_inv
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sFunction inner
        exact ⟨.app nextTerm argumentTerm, by rw [applied]; exact .app sNext sArgument,
          innerStep.plug (.appFunction .hole argumentTerm)⟩
      · obtain ⟨function, argument, next, rfl, inner, applied⟩ := appArgument_inv matched premises
        obtain ⟨first, second, shape, sFunction, sArgument⟩ := spelled.app_inv
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sArgument inner
        exact ⟨.app functionTerm nextTerm, by rw [applied]; exact .app sFunction sNext,
          innerStep.plug (.appArgument functionTerm .hole)⟩
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piDomain_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.binder_inv (.inr rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sDomain inner
        exact ⟨.pi nextTerm bodyTerm, by rw [applied]; exact .binder (.inr rfl) sNext sBody,
          innerStep.plug (.piDomain .hole bodyTerm)⟩
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piBody_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.binder_inv (.inr rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sBody inner
        exact ⟨.pi domainTerm nextTerm, by rw [applied]; exact .binder (.inr rfl) sDomain sNext,
          innerStep.plug (.piBody domainTerm .hole)⟩
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := lamDomain_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.binder_inv (.inl rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sDomain inner
        exact ⟨.lam nextTerm bodyTerm, by rw [applied]; exact .binder (.inl rfl) sNext sBody,
          innerStep.plug (.lamDomain .hole bodyTerm)⟩
      · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := lamBody_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.binder_inv (.inl rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sBody inner
        exact ⟨.lam domainTerm nextTerm, by rw [applied]; exact .binder (.inl rfl) sDomain sNext,
          innerStep.plug (.lamBody domainTerm .hole)⟩
      · obtain ⟨atom, rfl, -⟩ := release_inv matched premises
        exact absurd spelled Spells.not_dropped
      · obtain ⟨outer, subject, next, rfl, inner, applied⟩ := runSubject_inv matched premises
        rcases spelled.run_inv with ⟨rfl, other, live⟩ | dead
        · obtain ⟨nextTerm, sNext, innerStep⟩ := ih live inner
          exact ⟨nextTerm, by rw [applied]; exact (Spells.live sNext).ofWhole, innerStep⟩
        · obtain ⟨nextTerm, sNext, innerStep⟩ := ih dead inner
          exact ⟨nextTerm, by rw [applied]; exact (Spells.dead outer sNext).ofWhole, innerStep⟩
      · obtain ⟨outer, subject, answer, rfl, found, applied⟩ := locatedRoot_inv matched premises
        rw [locatedAnswers_of_settle (spelled.run_whole.settle_whole plain)
          (tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) term depth)] at found
        obtain ⟨plainAnswer, inResults, rfl⟩ := List.mem_map.mp found
        obtain ⟨nextTerm, rfl, rootStep⟩ := answers inResults
        exact ⟨nextTerm, by
          rw [applied]
          exact (Spells.dead outer (.live (Spells.atom space nextTerm depth))).ofWhole, rootStep⟩
      · obtain ⟨outer, function, argument, next, rfl, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨first, second, shape, sFunction, sArgument⟩ := spelled.run_app_inv
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sFunction inner
        exact ⟨.app nextTerm argumentTerm, by
          rw [applied]
          exact (Spells.run_app sNext sArgument).ofWhole,
          innerStep.plug (.appFunction .hole argumentTerm)⟩
      · obtain ⟨outer, function, argument, next, rfl, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨first, second, shape, sFunction, sArgument⟩ := spelled.run_app_inv
        obtain ⟨functionTerm, argumentTerm, rfl, rfl, rfl⟩ := atomAt_eq_app shape
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sArgument inner
        exact ⟨.app functionTerm nextTerm, by
          rw [applied]
          exact (Spells.run_app sFunction sNext).ofWhole,
          innerStep.plug (.appArgument functionTerm .hole)⟩
      · obtain ⟨outer, domain, binder, body, next, rfl, inner, applied⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.run_binder_inv (.inr rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sDomain inner
        exact ⟨.pi nextTerm bodyTerm, by
          rw [applied]
          exact (Spells.run_binder (.inr rfl) sNext sBody).ofWhole,
          innerStep.plug (.piDomain .hole bodyTerm)⟩
      · obtain ⟨outer, domain, binder, body, next, rfl, inner, applied⟩ :=
          runPiBody_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.run_binder_inv (.inr rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_pi shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sBody inner
        exact ⟨.pi domainTerm nextTerm, by
          rw [applied]
          exact (Spells.run_binder (.inr rfl) sDomain sNext).ofWhole,
          innerStep.plug (.piBody domainTerm .hole)⟩
      · obtain ⟨outer, domain, binder, body, next, rfl, inner, applied⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.run_binder_inv (.inl rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sDomain inner
        exact ⟨.lam nextTerm bodyTerm, by
          rw [applied]
          exact (Spells.run_binder (.inl rfl) sNext sBody).ofWhole,
          innerStep.plug (.lamDomain .hole bodyTerm)⟩
      · obtain ⟨outer, domain, binder, body, next, rfl, inner, applied⟩ :=
          runLamBody_inv matched premises
        obtain ⟨bodyInner, first, second, sameAbstraction, shape, sDomain, sBody⟩ :=
          spelled.run_binder_inv (.inl rfl)
        simp only [Pattern.lambda.injEq] at sameAbstraction
        obtain ⟨rfl, rfl⟩ := sameAbstraction
        obtain ⟨domainTerm, bodyTerm, rfl, rfl, bodyEq⟩ := atomAt_eq_lam shape
        simp only [Pattern.lambda.injEq, true_and] at bodyEq
        subst bodyEq
        obtain ⟨nextTerm, sNext, innerStep⟩ := ih sBody inner
        exact ⟨.lam domainTerm nextTerm, by
          rw [applied]
          exact (Spells.run_binder (.inl rfl) sDomain sNext).ofWhole,
          innerStep.plug (.lamBody domainTerm .hole)⟩

#print axioms ruleSpace_plain
#print axioms storesVariable_not_plain
#print axioms Spells.atom
#print axioms Spells.run_inv
#print axioms Spells.run_app
#print axioms Spells.run_app_inv
#print axioms Spells.settle_whole
#print axioms Spells.lift
#print axioms Spells.instantiate
#print axioms spelled_stepAt

end Mettapedia.Logic.HostingStyles.LocatedAtoms
