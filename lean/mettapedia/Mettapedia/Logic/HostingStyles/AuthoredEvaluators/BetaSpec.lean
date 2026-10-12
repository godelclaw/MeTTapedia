import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.WeakEvaluators

/-!
# One step of beta at every position, as a function on atoms

The pure λΠ-calculus is the theory of the empty table of rules: its step is a
beta contraction at any position of a term.  This module writes that step as
a computable function on the atoms of the probe, so that an equation program
can be proved to compute it.

* `betaReducts` lists the reducts of a λΠ term by one step
  (`mem_betaReducts_iff`).
* `termAtom` reads a λΠ term as a closed atom built from the unit atom and
  equations of two atoms: a numeral that tags the constructor, and the parts.
  Different terms are read as different atoms (`termAtom_injective`), every
  atom of a term is well sorted (`termAtom_closedAtom`) and has no quotation
  to contract (`contract_termAtom`).
* `AtomTerm` is what an atom is read back as: a λΠ term whose sorts and
  constants are kept as the atoms that stand for them.  `readAtom` reads any
  pattern back, and `AtomTerm.write` writes one.  Lifting, substitution and
  the reducts are computed on what was read back, and agree with those of the
  calculus (`AtomTerm.lift_ofTerm`, `AtomTerm.subst_ofTerm`,
  `AtomTerm.reducts_ofTerm`).
* `betaAnswers` reads an atom back and writes its reducts.  At the atom of a
  term these are the atoms of the reducts of the term
  (`mem_betaAnswers_termAtom`).

Reading back is total: a pattern that is the atom of no term is kept as an
atom, with no reduct.  Only the behaviour at the atoms of terms is used for
hosting; the behaviour elsewhere is what makes the function total.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF (Srt)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Dedukti (Theory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HostingStyles.PrimeCandidate

/-! ## The reducts of a λΠ term -/

/-- The contractions of an application at its root: one when the function is
an abstraction, none otherwise. -/
def betaContractions : LF.Term → LF.Term → List LF.Term
  | .lam _ body, argument => [LFTyping.subst0 argument body]
  | _, _ => []

/-- **Positive**: an abstraction applied contracts. -/
theorem betaContractions_lam (domain body argument : LF.Term) :
    betaContractions (.lam domain body) argument = [LFTyping.subst0 argument body] := rfl

/-- **Negative**: a variable applied does not. -/
theorem betaContractions_var (index : Nat) (argument : LF.Term) :
    betaContractions (.var index) argument = [] := rfl

/-- **The reducts of a λΠ term by one step of beta at any position.** -/
def betaReducts : LF.Term → List LF.Term
  | .srt _ => []
  | .con _ => []
  | .var _ => []
  | .pi domain body =>
      (betaReducts domain).map (fun reduct => LF.Term.pi reduct body) ++
        (betaReducts body).map (fun reduct => LF.Term.pi domain reduct)
  | .lam domain body =>
      (betaReducts domain).map (fun reduct => LF.Term.lam reduct body) ++
        (betaReducts body).map (fun reduct => LF.Term.lam domain reduct)
  | .app function argument =>
      betaContractions function argument ++
        ((betaReducts function).map (fun reduct => LF.Term.app reduct argument) ++
          (betaReducts argument).map (fun reduct => LF.Term.app function reduct))

/-- **Positive**: the identity applied to a constant has the constant as its
one reduct. -/
theorem betaReducts_identity :
    betaReducts (.app (.lam (.con "A") (.var 0)) (.con "c")) = [.con "c"] := by decide

/-- **Negative**: a variable has no reduct. -/
theorem betaReducts_var (index : Nat) : betaReducts (.var index) = [] := rfl

private theorem step_of_mem_betaReducts :
    ∀ {term next : LF.Term}, next ∈ betaReducts term →
      Dedukti.Step (Theory.ofTable ∅) term next := by
  intro term
  induction term with
  | srt sort =>
      intro next member
      simp [betaReducts] at member
  | con name =>
      intro next member
      simp [betaReducts] at member
  | var index =>
      intro next member
      simp [betaReducts] at member
  | pi domain body ihDomain ihBody =>
      intro next member
      simp only [betaReducts, List.mem_append, List.mem_map] at member
      rcases member with ⟨reduct, inner, rfl⟩ | ⟨reduct, inner, rfl⟩
      · exact (ihDomain inner).plug (.piDomain .hole body)
      · exact (ihBody inner).plug (.piBody domain .hole)
  | lam domain body ihDomain ihBody =>
      intro next member
      simp only [betaReducts, List.mem_append, List.mem_map] at member
      rcases member with ⟨reduct, inner, rfl⟩ | ⟨reduct, inner, rfl⟩
      · exact (ihDomain inner).plug (.lamDomain .hole body)
      · exact (ihBody inner).plug (.lamBody domain .hole)
  | app function argument ihFunction ihArgument =>
      intro next member
      simp only [betaReducts, List.mem_append, List.mem_map] at member
      rcases member with root | ⟨reduct, inner, rfl⟩ | ⟨reduct, inner, rfl⟩
      · cases function with
        | lam domain body =>
            obtain rfl : next = LFTyping.subst0 argument body := by
              simpa [betaContractions] using root
            exact .root (.beta domain body argument)
        | _ => simp [betaContractions] at root
      · exact (ihFunction inner).plug (.appFunction .hole argument)
      · exact (ihArgument inner).plug (.appArgument function .hole)

private theorem mem_betaReducts_of_step {term next : LF.Term}
    (step : Dedukti.Step (Theory.ofTable ∅) term next) : next ∈ betaReducts term := by
  cases step with
  | inContext context root =>
      induction context with
      | hole =>
          cases root with
          | beta domain body argument =>
              simp [LFContextualBetaEta.Context.plug, betaReducts, betaContractions]
          | delta defined => cases defined
          | rule assignment member => exact absurd member (Finset.notMem_empty _)
      | piDomain rest body ih =>
          simp only [LFContextualBetaEta.Context.plug, betaReducts, List.mem_append, List.mem_map]
          exact .inl ⟨_, ih, rfl⟩
      | piBody domain rest ih =>
          simp only [LFContextualBetaEta.Context.plug, betaReducts, List.mem_append, List.mem_map]
          exact .inr ⟨_, ih, rfl⟩
      | lamDomain rest body ih =>
          simp only [LFContextualBetaEta.Context.plug, betaReducts, List.mem_append, List.mem_map]
          exact .inl ⟨_, ih, rfl⟩
      | lamBody domain rest ih =>
          simp only [LFContextualBetaEta.Context.plug, betaReducts, List.mem_append, List.mem_map]
          exact .inr ⟨_, ih, rfl⟩
      | appFunction rest argument ih =>
          simp only [LFContextualBetaEta.Context.plug, betaReducts, List.mem_append, List.mem_map]
          exact .inr (.inl ⟨_, ih, rfl⟩)
      | appArgument function rest ih =>
          simp only [LFContextualBetaEta.Context.plug, betaReducts, List.mem_append, List.mem_map]
          exact .inr (.inr ⟨_, ih, rfl⟩)

/-- **The reducts listed are the steps of the pure λΠ-calculus.** -/
theorem mem_betaReducts_iff {term next : LF.Term} :
    next ∈ betaReducts term ↔ Dedukti.Step (Theory.ofTable ∅) term next :=
  ⟨step_of_mem_betaReducts, mem_betaReducts_of_step⟩

/-! ## λΠ terms as atoms -/

/-- The equation of two atoms. -/
def equationAtom (left right : Pattern) : Pattern := .apply "=" [left, right]

/-- **Positive**: a numeral above zero is the equation of the unit atom and
the numeral before it. -/
theorem numeral_succ (count : Nat) :
    numeral (count + 1) = equationAtom unitAtom (numeral count) := rfl

/-- **Negative**: the unit atom is no equation. -/
theorem unitAtom_ne_equationAtom (left right : Pattern) : unitAtom ≠ equationAtom left right := by
  simp [unitAtom, equationAtom]

theorem equationAtom_inj {left right otherLeft otherRight : Pattern} :
    equationAtom left right = equationAtom otherLeft otherRight ↔
      left = otherLeft ∧ right = otherRight := by
  simp [equationAtom]

theorem equationAtom_closedAtom {left right : Pattern}
    (leftSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom") left)
    (rightSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom")
      right) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom")
      (equationAtom left right) :=
  wellSorted_apply_two (lang := probeWithSpace) (label := "=") (firstName := "left")
    (secondName := "right") (by decide) leftSorted rightSorted

theorem contract_equationAtom (left right : Pattern) :
    contract (equationAtom left right) = equationAtom (contract left) (contract right) := by
  rw [equationAtom, contract_apply_of_ne (by decide)]
  rfl

/-- The atom of a sort. -/
def sortAtom : Srt → Pattern
  | .type => numeral 0
  | .kind => numeral 1

/-- The atom of a list of characters: the numerals of their codes, chained by
equations. -/
def charactersAtom : List Char → Pattern
  | [] => unitAtom
  | character :: rest => equationAtom (numeral character.toNat) (charactersAtom rest)

/-- **Positive**: one character. -/
theorem charactersAtom_singleton (character : Char) :
    charactersAtom [character] = equationAtom (numeral character.toNat) unitAtom := rfl

/-- **Negative**: no character, the unit atom. -/
theorem charactersAtom_nil : charactersAtom [] = unitAtom := rfl

/-- **Positive**: the atom of the sort of types is the unit atom. -/
theorem sortAtom_type : sortAtom .type = unitAtom := rfl

/-- **Negative**: the two sorts have two atoms. -/
theorem sortAtom_type_ne_kind : sortAtom .type ≠ sortAtom .kind := by decide

/-- **The atom of a λΠ term**: the numeral that tags its constructor, and its
parts. -/
def termAtom : LF.Term → Pattern
  | .srt sort => equationAtom (numeral 0) (sortAtom sort)
  | .con name => equationAtom (numeral 1) (charactersAtom name.toList)
  | .var index => equationAtom (numeral 2) (numeral index)
  | .pi domain body => equationAtom (numeral 3) (equationAtom (termAtom domain) (termAtom body))
  | .lam domain body => equationAtom (numeral 4) (equationAtom (termAtom domain) (termAtom body))
  | .app function argument =>
      equationAtom (numeral 5) (equationAtom (termAtom function) (termAtom argument))

/-- **Positive**: the atom of the variable of index zero. -/
theorem termAtom_var_zero : termAtom (.var 0) = equationAtom (numeral 2) unitAtom := rfl

/-- **Negative**: the unit atom is the atom of no term. -/
theorem termAtom_ne_unitAtom (term : LF.Term) : termAtom term ≠ unitAtom := by
  cases term <;> exact fun same => unitAtom_ne_equationAtom _ _ same.symm

theorem sortAtom_closedAtom (sort : Srt) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom") (sortAtom sort) := by
  cases sort <;> exact numeral_closedAtom _

theorem charactersAtom_closedAtom : ∀ characters : List Char,
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom")
      (charactersAtom characters)
  | [] => numeral_closedAtom 0
  | _ :: rest => equationAtom_closedAtom (numeral_closedAtom _) (charactersAtom_closedAtom rest)

/-- **The atom of a term is a closed atom of the probe with a space.** -/
theorem termAtom_closedAtom : ∀ term : LF.Term,
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom") (termAtom term)
  | .srt sort => equationAtom_closedAtom (numeral_closedAtom 0) (sortAtom_closedAtom sort)
  | .con _ => equationAtom_closedAtom (numeral_closedAtom 1) (charactersAtom_closedAtom _)
  | .var index => equationAtom_closedAtom (numeral_closedAtom 2) (numeral_closedAtom index)
  | .pi domain body =>
      equationAtom_closedAtom (numeral_closedAtom 3)
        (equationAtom_closedAtom (termAtom_closedAtom domain) (termAtom_closedAtom body))
  | .lam domain body =>
      equationAtom_closedAtom (numeral_closedAtom 4)
        (equationAtom_closedAtom (termAtom_closedAtom domain) (termAtom_closedAtom body))
  | .app function argument =>
      equationAtom_closedAtom (numeral_closedAtom 5)
        (equationAtom_closedAtom (termAtom_closedAtom function) (termAtom_closedAtom argument))

theorem contract_sortAtom (sort : Srt) : contract (sortAtom sort) = sortAtom sort := by
  cases sort <;> exact contract_numeral _

theorem contract_charactersAtom : ∀ characters : List Char,
    contract (charactersAtom characters) = charactersAtom characters
  | [] => contract_numeral 0
  | character :: rest => by
      rw [charactersAtom, contract_equationAtom, contract_numeral, contract_charactersAtom rest]

/-- **The atom of a term has no quotation to contract.** -/
theorem contract_termAtom : ∀ term : LF.Term, contract (termAtom term) = termAtom term
  | .srt sort => by rw [termAtom, contract_equationAtom, contract_numeral, contract_sortAtom]
  | .con name => by rw [termAtom, contract_equationAtom, contract_numeral, contract_charactersAtom]
  | .var index => by
      rw [termAtom, contract_equationAtom, contract_numeral, contract_numeral]
  | .pi domain body => by
      rw [termAtom, contract_equationAtom, contract_equationAtom, contract_numeral,
        contract_termAtom domain, contract_termAtom body]
  | .lam domain body => by
      rw [termAtom, contract_equationAtom, contract_equationAtom, contract_numeral,
        contract_termAtom domain, contract_termAtom body]
  | .app function argument => by
      rw [termAtom, contract_equationAtom, contract_equationAtom, contract_numeral,
        contract_termAtom function, contract_termAtom argument]

theorem sortAtom_injective : Function.Injective sortAtom := by
  intro first second same
  cases first <;> cases second <;>
    first
      | rfl
      | exact absurd (numeral_injective same) (by decide)

theorem charactersAtom_injective : Function.Injective charactersAtom := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second with
      | nil => rfl
      | cons character rest => exact absurd same (unitAtom_ne_equationAtom _ _)
  | cons character rest ih =>
      intro second same
      cases second with
      | nil => exact absurd same.symm (unitAtom_ne_equationAtom _ _)
      | cons other more =>
          obtain ⟨codes, tails⟩ := equationAtom_inj.mp same
          rw [Char.toNat_inj.mp (numeral_injective codes), ih tails]

/-- **Different terms are read as different atoms.** -/
theorem termAtom_injective : Function.Injective termAtom := by
  intro first
  induction first with
  | srt sort =>
      intro second same
      cases second with
      | srt other => rw [sortAtom_injective (equationAtom_inj.mp same).2]
      | _ => exact absurd (numeral_injective (equationAtom_inj.mp same).1) (by decide)
  | con name =>
      intro second same
      cases second with
      | con other =>
          rw [String.toList_injective (charactersAtom_injective (equationAtom_inj.mp same).2)]
      | _ => exact absurd (numeral_injective (equationAtom_inj.mp same).1) (by decide)
  | var index =>
      intro second same
      cases second with
      | var other => rw [numeral_injective (equationAtom_inj.mp same).2]
      | _ => exact absurd (numeral_injective (equationAtom_inj.mp same).1) (by decide)
  | pi domain body ihDomain ihBody =>
      intro second same
      cases second with
      | pi otherDomain otherBody =>
          obtain ⟨domains, bodies⟩ := equationAtom_inj.mp (equationAtom_inj.mp same).2
          rw [ihDomain domains, ihBody bodies]
      | _ => exact absurd (numeral_injective (equationAtom_inj.mp same).1) (by decide)
  | lam domain body ihDomain ihBody =>
      intro second same
      cases second with
      | lam otherDomain otherBody =>
          obtain ⟨domains, bodies⟩ := equationAtom_inj.mp (equationAtom_inj.mp same).2
          rw [ihDomain domains, ihBody bodies]
      | _ => exact absurd (numeral_injective (equationAtom_inj.mp same).1) (by decide)
  | app function argument ihFunction ihArgument =>
      intro second same
      cases second with
      | app otherFunction otherArgument =>
          obtain ⟨functions, arguments⟩ := equationAtom_inj.mp (equationAtom_inj.mp same).2
          rw [ihFunction functions, ihArgument arguments]
      | _ => exact absurd (numeral_injective (equationAtom_inj.mp same).1) (by decide)

/-! ## Reading atoms back -/

/-- **What an atom is read back as**: a λΠ term in which sorts and constants
are kept as the atoms that stand for them. -/
inductive AtomTerm where
  | atom (raw : Pattern)
  | var (index : Nat)
  | pi (domain body : AtomTerm)
  | lam (domain body : AtomTerm)
  | app (function argument : AtomTerm)
  deriving DecidableEq

/-- The two arguments of an application to two arguments, whatever its
label. -/
def twoArguments : Pattern → Option (Pattern × Pattern)
  | .apply _ [left, right] => some (left, right)
  | _ => none

/-- **Positive**: the two sides of an equation. -/
theorem twoArguments_equationAtom (left right : Pattern) :
    twoArguments (equationAtom left right) = some (left, right) := rfl

/-- **Negative**: the unit atom has none. -/
theorem twoArguments_unitAtom : twoArguments unitAtom = none := rfl

theorem twoArguments_eq_some {pattern left right : Pattern}
    (found : twoArguments pattern = some (left, right)) :
    ∃ label, pattern = .apply label [left, right] := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
      · cases found
      · cases found
      · cases found
        exact ⟨label, rfl⟩
      · cases found
  | _ => cases found

theorem twoArguments_sizeOf {pattern left right : Pattern}
    (found : twoArguments pattern = some (left, right)) :
    sizeOf left < sizeOf pattern ∧ sizeOf right < sizeOf pattern := by
  obtain ⟨label, rfl⟩ := twoArguments_eq_some found
  simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
  omega

/-- **What a tag and two parts stand for.**  The tag two is a variable of the
given index; three, four and five are a product, an abstraction and an
application of the two parts; every other tag, and a tag above two without
parts, keeps the whole pattern as an atom. -/
def assemble (tag : Nat) (parts : Option (AtomTerm × AtomTerm)) (index : Nat) (whole : Pattern) :
    AtomTerm :=
  match tag with
  | 2 => .var index
  | 3 =>
      match parts with
      | some (domain, body) => .pi domain body
      | none => .atom whole
  | 4 =>
      match parts with
      | some (domain, body) => .lam domain body
      | none => .atom whole
  | 5 =>
      match parts with
      | some (function, argument) => .app function argument
      | none => .atom whole
  | _ => .atom whole

/-- **Positive**: the tag two is a variable. -/
theorem assemble_var (index : Nat) : assemble 2 none index unitAtom = .var index := rfl

/-- **Negative**: the tag zero keeps the whole pattern. -/
theorem assemble_zero (index : Nat) : assemble 0 none index unitAtom = .atom unitAtom := rfl

mutual
  /-- **An atom, read back.**  An application to a tag and a payload is read
  by its tag; every other pattern is kept as an atom. -/
  def readAtom : Pattern → AtomTerm
    | .apply label arguments => readArguments (.apply label arguments) arguments
    | .bvar index => .atom (.bvar index)
    | .fvar name => .atom (.fvar name)
    | .lambda binder body => .atom (.lambda binder body)
    | .multiLambda arity binders body => .atom (.multiLambda arity binders body)
    | .subst body replacement => .atom (.subst body replacement)
    | .collection kind elements rest => .atom (.collection kind elements rest)

  /-- The reading of a tag and a payload. -/
  def readArguments (whole : Pattern) : List Pattern → AtomTerm
    | [tag, payload] =>
        assemble (numeralValue tag) (readParts payload) (numeralValue payload) whole
    | _ => .atom whole

  /-- The two parts of a payload, read back. -/
  def readParts : Pattern → Option (AtomTerm × AtomTerm)
    | .apply _ arguments => readPair arguments
    | .bvar _ => none
    | .fvar _ => none
    | .lambda _ _ => none
    | .multiLambda _ _ _ => none
    | .subst _ _ => none
    | .collection _ _ _ => none

  /-- Two patterns, read back. -/
  def readPair : List Pattern → Option (AtomTerm × AtomTerm)
    | [first, second] => some (readAtom first, readAtom second)
    | _ => none
end

theorem readParts_eq (payload : Pattern) :
    readParts payload =
      (twoArguments payload).map fun parts => (readAtom parts.1, readAtom parts.2) := by
  cases payload with
  | apply label arguments =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
        simp [readParts, readPair, twoArguments]
  | _ => simp [readParts, twoArguments]

theorem readAtom_of_none {pattern : Pattern} (found : twoArguments pattern = none) :
    readAtom pattern = .atom pattern := by
  cases pattern with
  | apply label arguments =>
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
      · simp [readAtom, readArguments]
      · simp [readAtom, readArguments]
      · cases found
      · simp [readAtom, readArguments]
  | _ => simp [readAtom]

theorem readAtom_of_some {pattern tag payload : Pattern}
    (found : twoArguments pattern = some (tag, payload)) :
    readAtom pattern =
      assemble (numeralValue tag) (readParts payload) (numeralValue payload) pattern := by
  obtain ⟨label, rfl⟩ := twoArguments_eq_some found
  simp [readAtom, readArguments]

/-- **Negative**: the unit atom is the atom of no term; it is kept. -/
theorem readAtom_unitAtom : readAtom unitAtom = .atom unitAtom := readAtom_of_none rfl

namespace AtomTerm

/-- Lifting by one above a cutoff. -/
def lift (cutoff : Nat) : AtomTerm → AtomTerm
  | .atom raw => .atom raw
  | .var index => .var (if index < cutoff then index else index + 1)
  | .pi domain body => .pi (lift cutoff domain) (lift (cutoff + 1) body)
  | .lam domain body => .lam (lift cutoff domain) (lift (cutoff + 1) body)
  | .app function argument => .app (lift cutoff function) (lift cutoff argument)

/-- **Positive**: a variable at the cutoff is lifted. -/
theorem lift_at : lift 0 (.var 0) = .var 1 := rfl

/-- **Negative**: a variable below the cutoff is not. -/
theorem lift_below : lift 1 (.var 0) = .var 0 := rfl

/-- Substitution of a replacement for one index. -/
def subst (target : Nat) (replacement : AtomTerm) : AtomTerm → AtomTerm
  | .atom raw => .atom raw
  | .var index =>
      if index = target then replacement
      else if target < index then .var (index - 1) else .var index
  | .pi domain body =>
      .pi (subst target replacement domain) (subst (target + 1) (lift 0 replacement) body)
  | .lam domain body =>
      .lam (subst target replacement domain) (subst (target + 1) (lift 0 replacement) body)
  | .app function argument =>
      .app (subst target replacement function) (subst target replacement argument)

/-- **Positive**: the variable of the index is replaced. -/
theorem subst_hit (replacement : AtomTerm) : subst 0 replacement (.var 0) = replacement := rfl

/-- **Negative**: an atom is not. -/
theorem subst_atom (target : Nat) (replacement : AtomTerm) (raw : Pattern) :
    subst target replacement (.atom raw) = .atom raw := rfl

/-- The contractions of an application at its root. -/
def contractions : AtomTerm → AtomTerm → List AtomTerm
  | .lam _ body, argument => [subst 0 argument body]
  | _, _ => []

/-- **Positive**: an abstraction applied contracts. -/
theorem contractions_lam (domain body argument : AtomTerm) :
    contractions (.lam domain body) argument = [subst 0 argument body] := rfl

/-- **Negative**: an atom applied does not. -/
theorem contractions_atom (raw : Pattern) (argument : AtomTerm) :
    contractions (.atom raw) argument = [] := rfl

/-- **The reducts by one step of beta at any position.** -/
def reducts : AtomTerm → List AtomTerm
  | .atom _ => []
  | .var _ => []
  | .pi domain body =>
      (reducts domain).map (fun reduct => AtomTerm.pi reduct body) ++
        (reducts body).map (fun reduct => AtomTerm.pi domain reduct)
  | .lam domain body =>
      (reducts domain).map (fun reduct => AtomTerm.lam reduct body) ++
        (reducts body).map (fun reduct => AtomTerm.lam domain reduct)
  | .app function argument =>
      contractions function argument ++
        ((reducts function).map (fun reduct => AtomTerm.app reduct argument) ++
          (reducts argument).map (fun reduct => AtomTerm.app function reduct))

/-- **Negative**: an atom has no reduct. -/
theorem reducts_atom (raw : Pattern) : reducts (.atom raw) = [] := rfl

/-- **What was read back, written as an atom.** -/
def write : AtomTerm → Pattern
  | .atom raw => raw
  | .var index => equationAtom (numeral 2) (numeral index)
  | .pi domain body => equationAtom (numeral 3) (equationAtom (write domain) (write body))
  | .lam domain body => equationAtom (numeral 4) (equationAtom (write domain) (write body))
  | .app function argument =>
      equationAtom (numeral 5) (equationAtom (write function) (write argument))

/-- **Negative**: an atom that was kept is written as it was. -/
theorem write_atom (raw : Pattern) : write (.atom raw) = raw := rfl

/-- **A λΠ term, as what its atom is read back as.** -/
def ofTerm : LF.Term → AtomTerm
  | .srt sort => .atom (termAtom (.srt sort))
  | .con name => .atom (termAtom (.con name))
  | .var index => .var index
  | .pi domain body => .pi (ofTerm domain) (ofTerm body)
  | .lam domain body => .lam (ofTerm domain) (ofTerm body)
  | .app function argument => .app (ofTerm function) (ofTerm argument)

/-- **Negative**: the unit atom, kept as an atom, is what no term is read back
as. -/
theorem ofTerm_ne_unit (term : LF.Term) : ofTerm term ≠ .atom unitAtom := by
  cases term with
  | srt sort => exact fun same => termAtom_ne_unitAtom _ (AtomTerm.atom.inj same)
  | con name => exact fun same => termAtom_ne_unitAtom _ (AtomTerm.atom.inj same)
  | _ => exact fun same => AtomTerm.noConfusion same

/-- **Positive**: writing what a term is read back as gives its atom. -/
theorem write_ofTerm : ∀ term : LF.Term, write (ofTerm term) = termAtom term
  | .srt _ => rfl
  | .con _ => rfl
  | .var _ => rfl
  | .pi domain body => by rw [ofTerm, write, write_ofTerm domain, write_ofTerm body, termAtom]
  | .lam domain body => by rw [ofTerm, write, write_ofTerm domain, write_ofTerm body, termAtom]
  | .app function argument => by
      rw [ofTerm, write, write_ofTerm function, write_ofTerm argument, termAtom]

theorem lift_ofTerm : ∀ (term : LF.Term) (cutoff : Nat),
    lift cutoff (ofTerm term) = ofTerm (LFTyping.lift 1 cutoff term)
  | .srt _, _ => rfl
  | .con _, _ => rfl
  | .var _, _ => rfl
  | .pi domain body, cutoff => by
      simp only [ofTerm, lift, LFTyping.lift, lift_ofTerm domain cutoff,
        lift_ofTerm body (cutoff + 1)]
  | .lam domain body, cutoff => by
      simp only [ofTerm, lift, LFTyping.lift, lift_ofTerm domain cutoff,
        lift_ofTerm body (cutoff + 1)]
  | .app function argument, cutoff => by
      simp only [ofTerm, lift, LFTyping.lift, lift_ofTerm function cutoff,
        lift_ofTerm argument cutoff]

theorem subst_ofTerm : ∀ (term : LF.Term) (target : Nat) (replacement : LF.Term),
    subst target (ofTerm replacement) (ofTerm term) =
      ofTerm (LFTyping.subst target replacement term)
  | .srt _, _, _ => rfl
  | .con _, _, _ => rfl
  | .var index, target, replacement => by
      simp only [ofTerm, subst, LFTyping.subst]
      split_ifs <;> rfl
  | .pi domain body, target, replacement => by
      simp only [ofTerm, subst, LFTyping.subst, lift_ofTerm,
        subst_ofTerm domain target replacement,
        subst_ofTerm body (target + 1) (LFTyping.lift 1 0 replacement)]
  | .lam domain body, target, replacement => by
      simp only [ofTerm, subst, LFTyping.subst, lift_ofTerm,
        subst_ofTerm domain target replacement,
        subst_ofTerm body (target + 1) (LFTyping.lift 1 0 replacement)]
  | .app function argument, target, replacement => by
      simp only [ofTerm, subst, LFTyping.subst, subst_ofTerm function target replacement,
        subst_ofTerm argument target replacement]

theorem contractions_ofTerm (function argument : LF.Term) :
    contractions (ofTerm function) (ofTerm argument) =
      (betaContractions function argument).map ofTerm := by
  cases function with
  | lam domain body =>
      simp only [ofTerm, contractions, betaContractions, LFTyping.subst0, List.map_cons,
        List.map_nil, subst_ofTerm]
  | _ => rfl

/-- **The reducts computed on what was read back are the reducts of the
term.** -/
theorem reducts_ofTerm : ∀ term : LF.Term, reducts (ofTerm term) = (betaReducts term).map ofTerm
  | .srt _ => rfl
  | .con _ => rfl
  | .var _ => rfl
  | .pi domain body => by
      simp only [ofTerm, reducts, betaReducts, reducts_ofTerm domain, reducts_ofTerm body,
        List.map_append, List.map_map, Function.comp_def]
  | .lam domain body => by
      simp only [ofTerm, reducts, betaReducts, reducts_ofTerm domain, reducts_ofTerm body,
        List.map_append, List.map_map, Function.comp_def]
  | .app function argument => by
      simp only [ofTerm, reducts, betaReducts, contractions_ofTerm, reducts_ofTerm function,
        reducts_ofTerm argument, List.map_append, List.map_map, Function.comp_def]

end AtomTerm

/-- **Positive**: the atom of a term is read back as the term. -/
theorem readAtom_termAtom : ∀ term : LF.Term, readAtom (termAtom term) = AtomTerm.ofTerm term
  | .srt sort => by
      rw [termAtom, readAtom_of_some (twoArguments_equationAtom _ _), numeralValue_numeral]
      rfl
  | .con name => by
      rw [termAtom, readAtom_of_some (twoArguments_equationAtom _ _), numeralValue_numeral]
      rfl
  | .var index => by
      rw [termAtom, readAtom_of_some (twoArguments_equationAtom _ _), numeralValue_numeral,
        numeralValue_numeral]
      rfl
  | .pi domain body => by
      rw [termAtom, readAtom_of_some (twoArguments_equationAtom _ _), numeralValue_numeral]
      simp only [readParts_eq, twoArguments_equationAtom, Option.map_some,
        readAtom_termAtom domain, readAtom_termAtom body]
      rfl
  | .lam domain body => by
      rw [termAtom, readAtom_of_some (twoArguments_equationAtom _ _), numeralValue_numeral]
      simp only [readParts_eq, twoArguments_equationAtom, Option.map_some,
        readAtom_termAtom domain, readAtom_termAtom body]
      rfl
  | .app function argument => by
      rw [termAtom, readAtom_of_some (twoArguments_equationAtom _ _), numeralValue_numeral]
      simp only [readParts_eq, twoArguments_equationAtom, Option.map_some,
        readAtom_termAtom function, readAtom_termAtom argument]
      rfl

/-! ## The answers of one step of beta -/

/-- **The answers of one step of beta at a subject**: the subject is read
back, and its reducts are written. -/
def betaAnswers (subject : Pattern) : List Pattern :=
  (AtomTerm.reducts (readAtom subject)).map AtomTerm.write

theorem betaAnswers_termAtom (term : LF.Term) :
    betaAnswers (termAtom term) = (betaReducts term).map termAtom := by
  rw [betaAnswers, readAtom_termAtom, AtomTerm.reducts_ofTerm, List.map_map]
  exact List.map_congr_left fun reduct _ => AtomTerm.write_ofTerm reduct

/-- **At the atom of a term, the answers are the atoms of the reducts of the
term** in the pure λΠ-calculus. -/
theorem mem_betaAnswers_termAtom {term : LF.Term} {result : Pattern} :
    result ∈ betaAnswers (termAtom term) ↔
      ∃ next, Dedukti.Step (Theory.ofTable ∅) term next ∧ result = termAtom next := by
  rw [betaAnswers_termAtom, List.mem_map]
  constructor
  · rintro ⟨next, member, rfl⟩
    exact ⟨next, mem_betaReducts_iff.mp member, rfl⟩
  · rintro ⟨next, step, rfl⟩
    exact ⟨next, mem_betaReducts_iff.mpr step, rfl⟩

/-- **Positive**: at the atom of the identity applied to a constant, the atom
of the constant. -/
theorem betaAnswers_identity :
    betaAnswers (termAtom (.app (.lam (.con "A") (.var 0)) (.con "c"))) = [termAtom (.con "c")] := by
  rw [betaAnswers_termAtom, betaReducts_identity]
  rfl

/-- **Negative**: at the unit atom, which is the atom of no term, nothing. -/
theorem betaAnswers_unitAtom : betaAnswers unitAtom = [] := by
  rw [betaAnswers, readAtom_unitAtom]
  rfl

#print axioms mem_betaReducts_iff
#print axioms termAtom_closedAtom
#print axioms contract_termAtom
#print axioms termAtom_injective
#print axioms readAtom_termAtom
#print axioms AtomTerm.lift_ofTerm
#print axioms AtomTerm.subst_ofTerm
#print axioms AtomTerm.reducts_ofTerm
#print axioms mem_betaAnswers_termAtom

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
