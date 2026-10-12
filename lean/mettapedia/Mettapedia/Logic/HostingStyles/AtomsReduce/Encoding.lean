import Mettapedia.Logic.HostingStyles.AtomsReduce.Language
import Mettapedia.Logic.HostingStyles.ContextReadings.Conservation

/-!
# λΠ terms as atoms of the candidate in which atoms reduce

A λΠ term is read as an atom (`atomAt`).  Application, abstraction and
product are the three constructors of expressions; a sort and a constant are
symbols.  A variable that a binder of the term binds is a bound variable of
the pattern; a free variable is a variable atom.  So **every term, open or
closed, is a closed atom** (`atomAt_wellSorted`, at depth zero), and beneath
`depth` binders of an enclosing term it is an atom at the stage of those
binders.

* The reading is injective at every depth (`atomAt_injective`).
* It carries lifting to the shift of loose bound variables
  (`liftBVars_atomAt`) and substitution to the binder-eliminating
  instantiation of patterns (`instantiateBVarAt_atomAt`): beta of the term is
  the instantiation of the outermost binder (`instantiateBVar_atomAt`).  A
  variable atom is closed, so nothing is shifted in it.
* An atom of a term has no quotation, no dropping and no run
  (`contract_atomAt`, `tokens_atomAt`).

**Negative**: the encoding of the language of the pure λΠ-calculus sends a
free variable to a loose bound variable, which is no closed term
(`encode_var_not_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.GSLT.Dedukti (lift_zero lift_lift_same)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList liftBVars_zero instantiateBVarAt
  instantiateBVar)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## The reading -/

/-- The symbol of a number. -/
def symbolAtom (code : Nat) : Pattern := .apply "prime-symbol" [numeral code]

/-- **A λΠ term as an atom, beneath `depth` binders.**  A variable below
`depth` is bound by one of them; the others are free, and are variable
atoms. -/
def atomAt (depth : Nat) : LF.Term → Pattern
  | .var index => if index < depth then .bvar index else variableAtom (numeral (index - depth))
  | .srt .type => symbolAtom 0
  | .srt .kind => symbolAtom 1
  | .con name => symbolAtom (nameCode name + 2)
  | .app function argument => .apply "App" [atomAt depth function, atomAt depth argument]
  | .lam domain body => .apply "Lam" [atomAt depth domain, .lambda none (atomAt (depth + 1) body)]
  | .pi domain body => .apply "Pi" [atomAt depth domain, .lambda none (atomAt (depth + 1) body)]

theorem atomAt_var_of_lt {depth index : Nat} (below : index < depth) :
    atomAt depth (.var index) = .bvar index := by
  simp [atomAt, below]

theorem atomAt_var_of_le {depth index : Nat} (above : depth ≤ index) :
    atomAt depth (.var index) = variableAtom (numeral (index - depth)) := by
  have notBelow : ¬ index < depth := by omega
  simp [atomAt, notBelow]

/-- The atom of a sort, as a symbol. -/
def sortCode : LF.Srt → Nat
  | .type => 0
  | .kind => 1

theorem atomAt_srt (depth : Nat) (sort : LF.Srt) :
    atomAt depth (.srt sort) = symbolAtom (sortCode sort) := by
  cases sort <;> rfl

/-- **Positive**: a free variable is a variable atom, a closed pattern. -/
theorem atomAt_freeVariable (index : Nat) :
    atomAt 0 (.var index) = variableAtom (numeral index) :=
  atomAt_var_of_le (Nat.zero_le index)

/-- **Negative**: the encoding of the language of the pure λΠ-calculus sends
a free variable to a loose bound variable, which is not scoped at depth
zero. -/
theorem encode_var_not_closed (index : Nat) :
    (Mettapedia.GSLT.Dedukti.Language.encode (.var index)).isWellScopedAt 0 = false := by
  simp [Mettapedia.GSLT.Dedukti.Language.encode, Pattern.isWellScopedAt]

/-! ## The shape of an atom of a term -/

/-- An atom of a term is a bound variable or an application of one of five
constructors. -/
theorem atomAt_shape (depth : Nat) (term : LF.Term) :
    (∃ index, atomAt depth term = .bvar index) ∨
      ∃ label arguments, atomAt depth term = .apply label arguments ∧
        label ∈ ["prime-variable", "prime-symbol", "App", "Lam", "Pi"] := by
  cases term with
  | var index =>
      by_cases below : index < depth
      · exact .inl ⟨index, atomAt_var_of_lt below⟩
      · exact .inr ⟨_, _, atomAt_var_of_le (Nat.le_of_not_lt below), by decide⟩
  | srt sort => exact .inr ⟨_, _, atomAt_srt depth sort, by decide⟩
  | con name => exact .inr ⟨_, _, rfl, by decide⟩
  | app function argument => exact .inr ⟨_, _, rfl, by decide⟩
  | lam domain body => exact .inr ⟨_, _, rfl, by decide⟩
  | pi domain body => exact .inr ⟨_, _, rfl, by decide⟩

/-- An application of another constructor is the atom of no term. -/
theorem atomAt_ne_apply {label : String}
    (outside : label ∉ ["prime-variable", "prime-symbol", "App", "Lam", "Pi"]) (depth : Nat)
    (term : LF.Term) (arguments : List Pattern) : atomAt depth term ≠ .apply label arguments := by
  intro same
  rcases atomAt_shape depth term with ⟨index, isVariable⟩ | ⟨found, others, isApply, listed⟩
  · rw [isVariable] at same
    cases same
  · rw [isApply] at same
    injection same with sameLabel
    exact outside (sameLabel ▸ listed)

/-- What the atom of a term is when it is an application. -/
theorem atomAt_eq_app {depth : Nat} {term : LF.Term} {function argument : Pattern}
    (same : atomAt depth term = .apply "App" [function, argument]) :
    ∃ first second, term = .app first second ∧ function = atomAt depth first ∧
      argument = atomAt depth second := by
  cases term with
  | var index =>
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below] at same
        cases same
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)] at same
        simp [variableAtom] at same
  | srt sort => rw [atomAt_srt] at same; simp [symbolAtom] at same
  | con name => simp [atomAt, symbolAtom] at same
  | app first second =>
      simp only [atomAt, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      exact ⟨first, second, rfl, same.1.symm, same.2.symm⟩
  | lam domain body => simp [atomAt] at same
  | pi domain body => simp [atomAt] at same

/-- What the atom of a term is when it is an abstraction. -/
theorem atomAt_eq_lam {depth : Nat} {term : LF.Term} {domain abstraction : Pattern}
    (same : atomAt depth term = .apply "Lam" [domain, abstraction]) :
    ∃ first second, term = .lam first second ∧ domain = atomAt depth first ∧
      abstraction = .lambda none (atomAt (depth + 1) second) := by
  cases term with
  | var index =>
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below] at same
        cases same
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)] at same
        simp [variableAtom] at same
  | srt sort => rw [atomAt_srt] at same; simp [symbolAtom] at same
  | con name => simp [atomAt, symbolAtom] at same
  | app first second => simp [atomAt] at same
  | lam first second =>
      simp only [atomAt, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      exact ⟨first, second, rfl, same.1.symm, same.2.symm⟩
  | pi first second => simp [atomAt] at same

/-- What the atom of a term is when it is a product. -/
theorem atomAt_eq_pi {depth : Nat} {term : LF.Term} {domain abstraction : Pattern}
    (same : atomAt depth term = .apply "Pi" [domain, abstraction]) :
    ∃ first second, term = .pi first second ∧ domain = atomAt depth first ∧
      abstraction = .lambda none (atomAt (depth + 1) second) := by
  cases term with
  | var index =>
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below] at same
        cases same
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)] at same
        simp [variableAtom] at same
  | srt sort => rw [atomAt_srt] at same; simp [symbolAtom] at same
  | con name => simp [atomAt, symbolAtom] at same
  | app first second => simp [atomAt] at same
  | lam first second => simp [atomAt] at same
  | pi first second =>
      simp only [atomAt, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      exact ⟨first, second, rfl, same.1.symm, same.2.symm⟩

/-! ## Injectivity -/

/-- **The reading is injective at every depth.** -/
theorem atomAt_injective : ∀ depth : Nat, Function.Injective (atomAt depth) := by
  intro depth first
  induction first generalizing depth with
  | var index =>
      intro second same
      cases second with
      | var other =>
          by_cases below : index < depth
          · by_cases otherBelow : other < depth
            · rw [atomAt_var_of_lt below, atomAt_var_of_lt otherBelow] at same
              cases same
              rfl
            · rw [atomAt_var_of_lt below, atomAt_var_of_le (Nat.le_of_not_lt otherBelow)] at same
              cases same
          · by_cases otherBelow : other < depth
            · rw [atomAt_var_of_le (Nat.le_of_not_lt below), atomAt_var_of_lt otherBelow] at same
              cases same
            · rw [atomAt_var_of_le (Nat.le_of_not_lt below),
                atomAt_var_of_le (Nat.le_of_not_lt otherBelow)] at same
              simp only [variableAtom, Pattern.apply.injEq, List.cons.injEq, and_true,
                true_and] at same
              have equal := numeral_injective same
              have : index = other := by omega
              rw [this]
      | srt sort =>
          by_cases below : index < depth
          · rw [atomAt_var_of_lt below, atomAt_srt] at same
            cases same
          · rw [atomAt_var_of_le (Nat.le_of_not_lt below), atomAt_srt] at same
            simp [variableAtom, symbolAtom] at same
      | con name =>
          by_cases below : index < depth
          · rw [atomAt_var_of_lt below] at same
            cases same
          · rw [atomAt_var_of_le (Nat.le_of_not_lt below)] at same
            simp [variableAtom, atomAt, symbolAtom] at same
      | app function argument =>
          exact absurd (atomAt_eq_app same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
      | lam domain body =>
          exact absurd (atomAt_eq_lam same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
      | pi domain body =>
          exact absurd (atomAt_eq_pi same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
  | srt sort =>
      intro second same
      cases second with
      | srt other =>
          rw [atomAt_srt, atomAt_srt] at same
          simp only [symbolAtom, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          have codes := numeral_injective same
          cases sort <;> cases other <;> first | rfl | exact absurd codes (by decide)
      | var index =>
          by_cases below : index < depth
          · rw [atomAt_var_of_lt below, atomAt_srt] at same
            cases same
          · rw [atomAt_var_of_le (Nat.le_of_not_lt below), atomAt_srt] at same
            simp [variableAtom, symbolAtom] at same
      | con name =>
          rw [atomAt_srt] at same
          simp only [atomAt, symbolAtom, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          have codes := numeral_injective same
          cases sort <;> simp [sortCode] at codes
      | app function argument =>
          exact absurd (atomAt_eq_app same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
      | lam domain body =>
          exact absurd (atomAt_eq_lam same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
      | pi domain body =>
          exact absurd (atomAt_eq_pi same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
  | con name =>
      intro second same
      cases second with
      | con other =>
          simp only [atomAt, symbolAtom, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          have codes := numeral_injective same
          rw [nameCode_injective (Nat.add_right_cancel codes)]
      | var index =>
          by_cases below : index < depth
          · rw [atomAt_var_of_lt below] at same
            cases same
          · rw [atomAt_var_of_le (Nat.le_of_not_lt below)] at same
            simp [variableAtom, atomAt, symbolAtom] at same
      | srt sort =>
          rw [atomAt_srt] at same
          simp only [atomAt, symbolAtom, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          have codes := numeral_injective same
          cases sort <;> simp [sortCode] at codes
      | app function argument =>
          exact absurd (atomAt_eq_app same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
      | lam domain body =>
          exact absurd (atomAt_eq_lam same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
      | pi domain body =>
          exact absurd (atomAt_eq_pi same) (by rintro ⟨_, _, impossible, _⟩; cases impossible)
  | app function argument ihFunction ihArgument =>
      intro second same
      obtain ⟨first, other, rfl, functionEq, argumentEq⟩ := atomAt_eq_app same.symm
      rw [ihFunction depth functionEq, ihArgument depth argumentEq]
  | lam domain body ihDomain ihBody =>
      intro second same
      obtain ⟨first, other, rfl, domainEq, bodyEq⟩ := atomAt_eq_lam same.symm
      simp only [Pattern.lambda.injEq, true_and] at bodyEq
      rw [ihDomain depth domainEq, ihBody (depth + 1) bodyEq]
  | pi domain body ihDomain ihBody =>
      intro second same
      obtain ⟨first, other, rfl, domainEq, bodyEq⟩ := atomAt_eq_pi same.symm
      simp only [Pattern.lambda.injEq, true_and] at bodyEq
      rw [ihDomain depth domainEq, ihBody (depth + 1) bodyEq]

/-! ## Every term is an atom of the candidate -/

/-- The interface of the atoms beneath `depth` binders of atoms. -/
def atomInterface (depth : Nat) : Contexts.Interface :=
  ⟨.base "Atom", List.replicate depth (.base "Atom")⟩

/-- The interface of the closed atoms. -/
def closedAtom : Contexts.Interface := ⟨.base "Atom", []⟩

theorem atomInterface_zero : atomInterface 0 = closedAtom := rfl

/-- A declared constructor of an atom and an atom beneath a binder, applied
to a term and an abstraction of a term, is a term. -/
theorem wellSorted_apply_binder {lang : LanguageDef} {bound : List TypeExpr}
    {label category name binder bodyName sort bodySort : String} {first body : Pattern}
    (declared : plainConstructor label category
      [.simple name (.base sort), .abstractionNamed (some binder) bodyName (.base bodySort)] ∈
        lang.terms)
    (firstSorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base sort) first)
    (bodySorted : OpenPatternWellSorted lang FreeTypeContext.empty (.base bodySort :: bound)
      (.base bodySort) body) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base category)
      (.apply label [first, .lambda none body]) := by
  obtain ⟨firstTyped, firstCanonical, firstObject, firstScope⟩ := firstSorted
  obtain ⟨bodyTyped, bodyCanonical, bodyObject, bodyScope⟩ := bodySorted
  refine ⟨.constructor (rule := plainConstructor label category
      [.simple name (.base sort), .abstractionNamed (some binder) bodyName (.base bodySort)])
    declared (fun bare => ?_)
    (.cons trivial rfl firstTyped (.cons trivial rfl (.lambda bodyTyped) .nil)), ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, shape⟩ := bare
    simp [plainConstructor] at shape
  · simpa [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using ⟨firstCanonical, bodyCanonical⟩
  · simpa [isObjectPattern, isObjectPatternList] using ⟨firstObject, bodyObject⟩
  · have here : first.isWellScopedAt bound.length = true := firstScope
    have there : body.isWellScopedAt (bound.length + 1) = true := bodyScope
    show (Pattern.apply label [first, .lambda none body]).isWellScopedAt bound.length = true
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here, there]

/-- A numeral is an atom of the candidate, beneath any binders. -/
theorem numeral_wellSorted_atoms (bound : List TypeExpr) (count : Nat) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Atom") (numeral count) :=
  numeral_wellSorted_in (lang := atomsReduce) (by decide) (by decide) bound count

/-- A symbol is an atom of the candidate, beneath any binders. -/
theorem symbolAtom_wellSorted (bound : List TypeExpr) (code : Nat) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Atom") (symbolAtom code) :=
  wellSorted_apply_one (lang := atomsReduce) (label := "prime-symbol") (name := "index")
    (by decide) (numeral_wellSorted_atoms bound code)

/-- **Every λΠ term is an atom of the candidate**, at the stage of the
binders it is beneath. -/
theorem atomAt_wellSorted (term : LF.Term) :
    ∀ depth : Nat, OpenPatternWellSorted atomsReduce FreeTypeContext.empty
      (List.replicate depth (.base "Atom")) (.base "Atom") (atomAt depth term) := by
  induction term with
  | var index =>
      intro depth
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below]
        refine ⟨.bvar (by simp [below]), by simp [Pattern.hasCanonicalBinderMetadata],
          by simp [isObjectPattern], ?_⟩
        show (Pattern.bvar index).isWellScopedAt (List.replicate depth (TypeExpr.base "Atom")).length =
          true
        simp [Pattern.isWellScopedAt, below]
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)]
        exact wellSorted_apply_one (lang := atomsReduce) (label := "prime-variable")
          (name := "index") (by decide) (numeral_wellSorted_atoms _ _)
  | srt sort =>
      intro depth
      rw [atomAt_srt]
      exact symbolAtom_wellSorted _ _
  | con name => intro depth; exact symbolAtom_wellSorted _ _
  | app function argument ihFunction ihArgument =>
      intro depth
      exact wellSorted_apply_two (lang := atomsReduce) (label := "App") (firstName := "f")
        (secondName := "a") (by decide) (ihFunction depth) (ihArgument depth)
  | lam domain body ihDomain ihBody =>
      intro depth
      have bodySorted := ihBody (depth + 1)
      rw [List.replicate_succ] at bodySorted
      exact wellSorted_apply_binder (lang := atomsReduce) (label := "Lam") (name := "a")
        (binder := "x") (bodyName := "body") (by decide) (ihDomain depth) bodySorted
  | pi domain body ihDomain ihBody =>
      intro depth
      have bodySorted := ihBody (depth + 1)
      rw [List.replicate_succ] at bodySorted
      exact wellSorted_apply_binder (lang := atomsReduce) (label := "Pi") (name := "a")
        (binder := "x") (bodyName := "body") (by decide) (ihDomain depth) bodySorted

/-- The atom of a term, as a term of the candidate at the stage of `depth`
binders. -/
def atomTermAt (depth : Nat) (term : LF.Term) : Contexts.Term atomsReduce (atomInterface depth) :=
  ⟨atomAt depth term, atomAt_wellSorted term depth⟩

/-! ## No quotation, no dropping, no run -/

theorem tokens_numeral {counted : String → Bool} (equation : counted "=" = false)
    (unit : counted "prime-unit" = false) (count : Nat) : tokens counted (numeral count) = 0 := by
  induction count with
  | zero => simp [numeral, unitAtom, tokens, tokensList, unit]
  | succ count ih => simp [numeral, unitAtom, tokens, tokensList, equation, unit, ih]

/-- **An atom of a term has no constructor outside the seven it is built
from.** -/
theorem tokens_atomAt {counted : String → Bool} (equation : counted "=" = false)
    (unit : counted "prime-unit" = false) (variable_ : counted "prime-variable" = false)
    (symbol : counted "prime-symbol" = false) (application : counted "App" = false)
    (abstraction : counted "Lam" = false) (product : counted "Pi" = false) (term : LF.Term) :
    ∀ depth : Nat, tokens counted (atomAt depth term) = 0 := by
  induction term with
  | var index =>
      intro depth
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below]
        simp [tokens]
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)]
        simp [variableAtom, tokens, tokensList, variable_, tokens_numeral equation unit]
  | srt sort =>
      intro depth
      rw [atomAt_srt]
      simp [symbolAtom, tokens, tokensList, symbol, tokens_numeral equation unit]
  | con name =>
      intro depth
      simp [atomAt, symbolAtom, tokens, tokensList, symbol, tokens_numeral equation unit]
  | app function argument ihFunction ihArgument =>
      intro depth
      simp [atomAt, tokens, tokensList, application, ihFunction depth, ihArgument depth]
  | lam domain body ihDomain ihBody =>
      intro depth
      simp [atomAt, tokens, tokensList, abstraction, ihDomain depth, ihBody (depth + 1)]
  | pi domain body ihDomain ihBody =>
      intro depth
      simp [atomAt, tokens, tokensList, product, ihDomain depth, ihBody (depth + 1)]

/-- **An atom of a term has no quotation to contract.** -/
theorem contract_atomAt (term : LF.Term) : ∀ depth : Nat, contract (atomAt depth term) =
    atomAt depth term := by
  induction term with
  | var index =>
      intro depth
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below, contract]
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below), variableAtom,
          contract_apply_of_ne (by decide)]
        simp [contract_numeral]
  | srt sort =>
      intro depth
      rw [atomAt_srt, symbolAtom, contract_apply_of_ne (by decide)]
      simp [contract_numeral]
  | con name =>
      intro depth
      rw [atomAt, symbolAtom, contract_apply_of_ne (by decide)]
      simp [contract_numeral]
  | app function argument ihFunction ihArgument =>
      intro depth
      rw [atomAt, contract_apply_of_ne (by decide)]
      simp [ihFunction depth, ihArgument depth]
  | lam domain body ihDomain ihBody =>
      intro depth
      rw [atomAt, contract_apply_of_ne (by decide)]
      simp [contract, ihDomain depth, ihBody (depth + 1)]
  | pi domain body ihDomain ihBody =>
      intro depth
      rw [atomAt, contract_apply_of_ne (by decide)]
      simp [contract, ihDomain depth, ihBody (depth + 1)]

/-! ## Lifting and substitution -/

theorem liftBVars_numeral (cutoff amount count : Nat) :
    liftBVars cutoff amount (numeral count) = numeral count := by
  induction count with
  | zero => simp [numeral, unitAtom, liftBVars, liftBVarsList]
  | succ count ih => simp [numeral, unitAtom, liftBVars, liftBVarsList, ih]

theorem instantiateBVarAt_numeral (depth : Nat) (replacement : Pattern) (count : Nat) :
    instantiateBVarAt depth replacement (numeral count) = numeral count := by
  induction count with
  | zero => simp [numeral, unitAtom, instantiateBVarAt]
  | succ count ih => simp [numeral, unitAtom, instantiateBVarAt, ih]

/-- **Lifting is the shift of loose bound variables**, above a cutoff within
the binders: the variable atoms are closed and stay. -/
theorem liftBVars_atomAt (term : LF.Term) :
    ∀ (cutoff depth amount : Nat), cutoff ≤ depth →
      liftBVars cutoff amount (atomAt depth term) =
        atomAt (depth + amount) (lift amount cutoff term) := by
  induction term with
  | var index =>
      intro cutoff depth amount within
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below]
        by_cases low : index < cutoff
        · have notAbove : ¬ index ≥ cutoff := by omega
          have lifted : lift amount cutoff (.var index) = .var index := by simp [lift, low]
          rw [lifted, atomAt_var_of_lt (by omega)]
          simp [liftBVars, notAbove]
        · have above : index ≥ cutoff := by omega
          have lifted : lift amount cutoff (.var index) = .var (index + amount) := by
            simp [lift, low]
          rw [lifted, atomAt_var_of_lt (by omega)]
          simp [liftBVars, above]
      · have low : ¬ index < cutoff := by omega
        have lifted : lift amount cutoff (.var index) = .var (index + amount) := by
          simp [lift, low]
        rw [atomAt_var_of_le (Nat.le_of_not_lt below), lifted, atomAt_var_of_le (by omega)]
        have same : index + amount - (depth + amount) = index - depth := by omega
        simp [variableAtom, liftBVars, liftBVarsList, liftBVars_numeral, same]
  | srt sort =>
      intro cutoff depth amount _
      have lifted : lift amount cutoff (.srt sort) = .srt sort := rfl
      rw [lifted, atomAt_srt, atomAt_srt]
      simp [symbolAtom, liftBVars, liftBVarsList, liftBVars_numeral]
  | con name =>
      intro cutoff depth amount _
      simp [atomAt, lift, symbolAtom, liftBVars, liftBVarsList, liftBVars_numeral]
  | app function argument ihFunction ihArgument =>
      intro cutoff depth amount within
      simp [atomAt, lift, liftBVars, liftBVarsList, ihFunction cutoff depth amount within,
        ihArgument cutoff depth amount within]
  | lam domain body ihDomain ihBody =>
      intro cutoff depth amount within
      have inner := ihBody (cutoff + 1) (depth + 1) amount (by omega)
      rw [Nat.add_right_comm] at inner
      simp [atomAt, lift, liftBVars, liftBVarsList, ihDomain cutoff depth amount within, inner]
  | pi domain body ihDomain ihBody =>
      intro cutoff depth amount within
      have inner := ihBody (cutoff + 1) (depth + 1) amount (by omega)
      rw [Nat.add_right_comm] at inner
      simp [atomAt, lift, liftBVars, liftBVarsList, ihDomain cutoff depth amount within, inner]

/-- **Substitution is the binder-eliminating instantiation of patterns**,
beneath `inner` binders of the body and `depth` binders around the redex. -/
theorem instantiateBVarAt_atomAt (body : LF.Term) :
    ∀ (inner depth : Nat) (replacement : LF.Term),
      instantiateBVarAt inner (atomAt depth replacement) (atomAt (depth + inner + 1) body) =
        atomAt (depth + inner) (subst inner (lift inner 0 replacement) body) := by
  induction body with
  | var index =>
      intro inner depth replacement
      by_cases low : index < inner
      · have notSame : index ≠ inner := by omega
        have notAbove : ¬ inner < index := by omega
        have substituted : subst inner (lift inner 0 replacement) (.var index) = .var index := by
          simp [subst, notSame, notAbove]
        rw [substituted, atomAt_var_of_lt (by omega), atomAt_var_of_lt (by omega)]
        simp [instantiateBVarAt, low]
      · by_cases same : index = inner
        · subst same
          have substituted : subst index (lift index 0 replacement) (.var index) =
              lift index 0 replacement := by simp [subst]
          rw [substituted, atomAt_var_of_lt (by omega)]
          simp [instantiateBVarAt, liftBVars_atomAt replacement 0 depth index (Nat.zero_le _)]
        · have above : inner < index := by omega
          have substituted : subst inner (lift inner 0 replacement) (.var index) =
              .var (index - 1) := by simp [subst, same, above]
          rw [substituted]
          by_cases below : index < depth + inner + 1
          · rw [atomAt_var_of_lt below, atomAt_var_of_lt (by omega)]
            simp [instantiateBVarAt, low, same]
          · rw [atomAt_var_of_le (Nat.le_of_not_lt below), atomAt_var_of_le (by omega)]
            have indices : index - 1 - (depth + inner) = index - (depth + inner + 1) := by omega
            simp [variableAtom, instantiateBVarAt, instantiateBVarAt_numeral, indices]
  | srt sort =>
      intro inner depth replacement
      have substituted : subst inner (lift inner 0 replacement) (.srt sort) = .srt sort := rfl
      rw [substituted, atomAt_srt, atomAt_srt]
      simp [symbolAtom, instantiateBVarAt, instantiateBVarAt_numeral]
  | con name =>
      intro inner depth replacement
      simp [atomAt, subst, symbolAtom, instantiateBVarAt, instantiateBVarAt_numeral]
  | app function argument ihFunction ihArgument =>
      intro inner depth replacement
      simp [atomAt, subst, instantiateBVarAt, ihFunction inner depth replacement,
        ihArgument inner depth replacement]
  | lam domain body ihDomain ihBody =>
      intro inner depth replacement
      have lifted : lift 1 0 (lift inner 0 replacement) = lift (inner + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      have beneath := ihBody (inner + 1) depth replacement
      simp only [← Nat.add_assoc] at beneath
      simp [atomAt, subst, instantiateBVarAt, ihDomain inner depth replacement, lifted, beneath]
  | pi domain body ihDomain ihBody =>
      intro inner depth replacement
      have lifted : lift 1 0 (lift inner 0 replacement) = lift (inner + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      have beneath := ihBody (inner + 1) depth replacement
      simp only [← Nat.add_assoc] at beneath
      simp [atomAt, subst, instantiateBVarAt, ihDomain inner depth replacement, lifted, beneath]

/-- **Beta is the instantiation of the outermost binder**, beneath any number
of binders around the redex. -/
theorem instantiateBVar_atomAt (depth : Nat) (argument body : LF.Term) :
    instantiateBVar (atomAt depth argument) (atomAt (depth + 1) body) =
      atomAt depth (subst0 argument body) := by
  have general := instantiateBVarAt_atomAt body 0 depth argument
  rw [lift_zero] at general
  exact general

#print axioms atomAt_injective
#print axioms atomAt_wellSorted
#print axioms tokens_atomAt
#print axioms contract_atomAt
#print axioms liftBVars_atomAt
#print axioms instantiateBVarAt_atomAt
#print axioms instantiateBVar_atomAt
#print axioms encode_var_not_closed

end Mettapedia.Logic.HostingStyles.AtomsReduce
