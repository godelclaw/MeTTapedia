import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.GSLT.LanguageDef.DefinitionalEquations
import Foundation.Propositional.Hilbert.Standard.Basic

/-!
# Propositional logic as a rule presentation

Intuitionistic and classical propositional logic are authored here as
sorted first-order rule presentations: one sort of formulas, the four
connectives as constructors, and one rule for modus ponens and for each
axiom scheme. The classical presentation is the intuitionistic one with one
more rule, excluded middle.

The rules are those of the standard Hilbert system of the `Foundation`
library, one for one. `derives_iff_hilbert` proves that the two agree: a
formula over the first `count` atoms is derivable in the presentation, in
the context of `count` formula variables, exactly when it is provable in
that Hilbert system. Atoms are the variables of the context, and a rule
instance is a substitution instance of its scheme.

The presentation is independent of that library's proofs: only its formula
type, its substitution and the definition of its derivability are used. The
soundness and completeness theorems it proves for Kripke models and for
truth tables then say what derivability in the presentation means.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PropositionalHilbert

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open LO LO.Propositional

/-! ## The language -/

abbrev wff : TypeExpr := .base "wff"

def nullary (label : String) : GrammarRule :=
  { label := label, category := "wff", params := [], syntaxPattern := [] }

def binary (label : String) : GrammarRule :=
  { label := label, category := "wff"
    params := [.simple "left" wff, .simple "right" wff], syntaxPattern := [] }

/-- One sort of formulas; falsity, conjunction, disjunction, implication. -/
def language : LanguageDef :=
  { name := "PropositionalHilbert"
    types := [TypeDecl.plain "wff"]
    terms := [nullary "falsum", binary "and", binary "or", binary "imp"]
    equations := []
    rewrites := [] }

def falsum : Pattern := .apply "falsum" []
def conj (left right : Pattern) : Pattern := .apply "and" [left, right]
def disj (left right : Pattern) : Pattern := .apply "or" [left, right]
def impl (left right : Pattern) : Pattern := .apply "imp" [left, right]

/-- The context of `count` formula variables. -/
def context (count : ℕ) : List TypeExpr := List.replicate count wff

/-! ## The rules -/

def schemaRule (id : String) (vars : List String) (premises : List Pattern)
    (conclusion : Pattern) : SortedFirstOrderRules.Rule :=
  { row := { id := id, vars := vars, premises := premises, conclusion := conclusion }
    variableTypes := vars.map fun _ => wff }

def ph : Pattern := .fvar "ph"
def ps : Pattern := .fvar "ps"
def ch : Pattern := .fvar "ch"

def mdp := schemaRule "mdp" ["ph", "ps"] [impl ph ps, ph] ps
def implyK := schemaRule "implyK" ["ph", "ps"] [] (impl ph (impl ps ph))
def implyS := schemaRule "implyS" ["ph", "ps", "ch"] []
  (impl (impl ph (impl ps ch)) (impl (impl ph ps) (impl ph ch)))
def andElimL := schemaRule "andElimL" ["ph", "ps"] [] (impl (conj ph ps) ph)
def andElimR := schemaRule "andElimR" ["ph", "ps"] [] (impl (conj ph ps) ps)
def andIntro := schemaRule "andIntro" ["ph", "ps"] [] (impl ph (impl ps (conj ph ps)))
def orIntroL := schemaRule "orIntroL" ["ph", "ps"] [] (impl ph (disj ph ps))
def orIntroR := schemaRule "orIntroR" ["ph", "ps"] [] (impl ps (disj ph ps))
def orElim := schemaRule "orElim" ["ph", "ps", "ch"] []
  (impl (impl ph ch) (impl (impl ps ch) (impl (disj ph ps) ch)))
def efq := schemaRule "efq" ["ph"] [] (impl falsum ph)
def lem := schemaRule "lem" ["ph"] [] (disj ph (impl ph falsum))

/-- Modus ponens and the axiom schemes of minimal logic. -/
def minimalRules : List SortedFirstOrderRules.Rule :=
  [mdp, implyK, implyS, andElimL, andElimR, andIntro, orIntroL, orIntroR, orElim]

/-- The rules of intuitionistic logic, and with excluded middle those of
classical logic. -/
def rules (classical : Bool) : List SortedFirstOrderRules.Rule :=
  minimalRules ++ efq :: (if classical then [lem] else [])

/-- The axioms of the corresponding Hilbert system. -/
def axioms (classical : Bool) : Axiom ℕ :=
  if classical then Propositional.Cl.axioms else Propositional.Int.axioms

/-! ## Formulas as patterns -/

/-- An atom is a variable of the context. -/
def encode : Formula ℕ → Pattern
  | .atom a => .bvar a
  | .falsum => falsum
  | .and φ ψ => conj (encode φ) (encode ψ)
  | .or φ ψ => disj (encode φ) (encode ψ)
  | .imp φ ψ => impl (encode φ) (encode ψ)

@[simp] theorem encode_atom (a : ℕ) : encode (.atom a) = .bvar a := rfl
@[simp] theorem encode_bot : encode (⊥ : Formula ℕ) = falsum := rfl
@[simp] theorem encode_and (φ ψ : Formula ℕ) : encode (φ ⋏ ψ) = conj (encode φ) (encode ψ) := rfl
@[simp] theorem encode_or (φ ψ : Formula ℕ) : encode (φ ⋎ ψ) = disj (encode φ) (encode ψ) := rfl
@[simp] theorem encode_imp (φ ψ : Formula ℕ) : encode (φ ➝ ψ) = impl (encode φ) (encode ψ) := rfl

/-- Every atom of the formula is below the bound. -/
def AtomsBelow (bound : ℕ) : Formula ℕ → Prop
  | .atom a => a < bound
  | .falsum => True
  | .and φ ψ => AtomsBelow bound φ ∧ AtomsBelow bound ψ
  | .or φ ψ => AtomsBelow bound φ ∧ AtomsBelow bound ψ
  | .imp φ ψ => AtomsBelow bound φ ∧ AtomsBelow bound ψ

theorem encode_injective {φ ψ : Formula ℕ} (same : encode φ = encode ψ) : φ = ψ := by
  induction φ using Formula.rec generalizing ψ with
  | atom a => cases ψ <;> simp_all [encode, falsum, conj, disj, impl]
  | falsum => cases ψ <;> simp_all [encode, falsum, conj, disj, impl]
  | and left right leftHypothesis rightHypothesis =>
      cases ψ with
      | and otherLeft otherRight =>
          simp only [encode, conj, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [leftHypothesis same.1, rightHypothesis same.2]
      | _ => simp [encode, falsum, conj, disj, impl] at same
  | or left right leftHypothesis rightHypothesis =>
      cases ψ with
      | or otherLeft otherRight =>
          simp only [encode, disj, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [leftHypothesis same.1, rightHypothesis same.2]
      | _ => simp [encode, falsum, conj, disj, impl] at same
  | imp left right leftHypothesis rightHypothesis =>
      cases ψ with
      | imp otherLeft otherRight =>
          simp only [encode, impl, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [leftHypothesis same.1, rightHypothesis same.2]
      | _ => simp [encode, falsum, conj, disj, impl] at same

theorem matchCorrect_encode : ∀ φ : Formula ℕ, isMatchCorrectAux (encode φ) = true
  | .atom _ => by simp [encode, isMatchCorrectAux]
  | .falsum => by simp [encode, falsum, isMatchCorrectAux, isMatchCorrectListAux]
  | .and φ ψ => by
      simp [encode, conj, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_encode φ,
        matchCorrect_encode ψ]
  | .or φ ψ => by
      simp [encode, disj, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_encode φ,
        matchCorrect_encode ψ]
  | .imp φ ψ => by
      simp [encode, impl, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_encode φ,
        matchCorrect_encode ψ]

/-! ## Typing -/

theorem nullary_notBare (label : String) : ¬ UsesBareCollection (nullary label) := by
  rintro ⟨_, _, _, impossible⟩
  simp [nullary] at impossible

theorem binary_notBare (label : String) : ¬ UsesBareCollection (binary label) := by
  rintro ⟨_, _, _, impossible⟩
  simp [binary] at impossible

theorem hasType_binary {count : ℕ} {label : String} (member : binary label ∈ language.terms)
    {left right : Pattern}
    (leftTyped : HasType language FreeTypeContext.empty (context count) left wff)
    (rightTyped : HasType language FreeTypeContext.empty (context count) right wff) :
    HasType language FreeTypeContext.empty (context count) (.apply label [left, right]) wff :=
  HasType.constructor (rule := binary label) member (binary_notBare label)
    (.cons trivial rfl leftTyped (.cons trivial rfl rightTyped .nil))

/-- A formula over the atoms of the context is a typed term. -/
theorem hasType_encode {count : ℕ} : ∀ {φ : Formula ℕ}, AtomsBelow count φ →
    HasType language FreeTypeContext.empty (context count) (encode φ) wff
  | .atom a, below =>
      HasType.bvar (by simp [context, show a < count from below])
  | .falsum, _ =>
      HasType.constructor (rule := nullary "falsum") (by simp [language])
        (nullary_notBare _) .nil
  | .and _ _, below =>
      hasType_binary (label := "and") (by simp [language]) (hasType_encode below.1)
        (hasType_encode below.2)
  | .or _ _, below =>
      hasType_binary (label := "or") (by simp [language]) (hasType_encode below.1)
        (hasType_encode below.2)
  | .imp _ _, below =>
      hasType_binary (label := "imp") (by simp [language]) (hasType_encode below.1)
        (hasType_encode below.2)

/-- Every typed first-order term is a formula over the atoms of the
context: the language has no other terms. -/
theorem typed_decodes {count : ℕ} (pattern : Pattern) {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty (context count) pattern type)
    (fragment : isMatchCorrectAux pattern = true) :
    ∃ φ, AtomsBelow count φ ∧ pattern = encode φ := by
  cases typed with
  | @bvar _ index _ lookup =>
      have below : index < count := by
        by_contra beyond
        simp [context, beyond] at lookup
      exact ⟨.atom index, below, rfl⟩
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | @constructor _ rule arguments member notBare argumentsTyped =>
      have options : rule = nullary "falsum" ∨ rule = binary "and" ∨ rule = binary "or" ∨
          rule = binary "imp" := by simpa [language] using member
      rcases options with rfl | rfl | rfl | rfl
      · cases argumentsTyped
        exact ⟨⊥, trivial, rfl⟩
      all_goals
        cases argumentsTyped with
        | cons _ _ leftTyped rest =>
          cases rest with
          | cons _ _ rightTyped rest =>
            cases rest
            have parts := fragment
            simp only [isMatchCorrectAux, isMatchCorrectListAux, Bool.and_true,
              Bool.and_eq_true] at parts
            obtain ⟨left, leftBelow, rfl⟩ := typed_decodes _ leftTyped parts.1
            obtain ⟨right, rightBelow, rfl⟩ := typed_decodes _ rightTyped parts.2
            first
              | exact ⟨left ⋏ right, ⟨leftBelow, rightBelow⟩, rfl⟩
              | exact ⟨left ⋎ right, ⟨leftBelow, rightBelow⟩, rfl⟩
              | exact ⟨left ➝ right, ⟨leftBelow, rightBelow⟩, rfl⟩
  | lambda _ => simp [isMatchCorrectAux] at fragment
  | multiLambda _ => simp [isMatchCorrectAux] at fragment
  | subst _ _ => simp [isMatchCorrectAux] at fragment
  | collection _ => simp [isMatchCorrectAux] at fragment
  | collectionConstructor _ _ _ => simp [isMatchCorrectAux] at fragment
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- The typed arguments of a rule instance are formulas. -/
theorem arguments_decode {count : ℕ} : ∀ {arguments : List Pattern} {types : List TypeExpr},
    List.Forall₂ (fun argument type =>
      HasType language FreeTypeContext.empty (context count) argument type) arguments types →
    (∀ argument ∈ arguments, isMatchCorrectAux argument = true) →
    ∃ formulas : List (Formula ℕ), arguments = formulas.map encode
  | [], _, _, _ => ⟨[], rfl⟩
  | argument :: rest, _, typed, fragments => by
      cases typed with
      | cons first others =>
        obtain ⟨φ, -, rfl⟩ := typed_decodes argument first (fragments _ (by simp))
        obtain ⟨formulas, rfl⟩ := arguments_decode others
          (fun other member => fragments other (by simp [member]))
        exact ⟨φ :: formulas, rfl⟩

theorem arguments_typed {count : ℕ} : ∀ (formulas : List (Formula ℕ)) (vars : List String),
    formulas.length = vars.length → (∀ φ ∈ formulas, AtomsBelow count φ) →
    List.Forall₂ (fun argument type =>
      HasType language FreeTypeContext.empty (context count) argument type)
      (formulas.map encode) (vars.map fun _ => wff)
  | [], [], _, _ => .nil
  | φ :: formulas, _ :: vars, arity, below =>
      .cons (hasType_encode (below φ (by simp)))
        (arguments_typed formulas vars (by simpa using arity)
          (fun ψ member => below ψ (by simp [member])))
  | [], _ :: _, arity, _ => by simp at arity
  | _ :: _, [], arity, _ => by simp at arity

/-! ## Rule instances -/

theorem bind_first (value : Pattern) (rest : Bindings) :
    applyBindings (("ph", value) :: rest) ph = value := by
  simp [applyBindings, ph]

theorem bind_second (first value : Pattern) (rest : Bindings) :
    applyBindings (("ph", first) :: ("ps", value) :: rest) ps = value := by
  simp [applyBindings, ps]

theorem bind_third (first second value : Pattern) :
    applyBindings [("ph", first), ("ps", second), ("ch", value)] ch = value := by
  simp [applyBindings, ch]

section Instances

variable (a b c : Pattern)

theorem mdp_premises : mdp.row.instPremises [a, b] = [impl a b, a] := by
  simp [mdp, schemaRule, FORule.instPremises, FORule.bindings, impl, applyBindings_apply,
    bind_first, bind_second]

theorem mdp_conclusion : mdp.row.instConclusion [a, b] = b := by
  simp [mdp, schemaRule, FORule.instConclusion, FORule.bindings, bind_second]

theorem implyK_conclusion : implyK.row.instConclusion [a, b] = impl a (impl b a) := by
  simp [implyK, schemaRule, FORule.instConclusion, FORule.bindings, impl, applyBindings_apply,
    bind_first, bind_second]

theorem implyS_conclusion : implyS.row.instConclusion [a, b, c] =
    impl (impl a (impl b c)) (impl (impl a b) (impl a c)) := by
  simp [implyS, schemaRule, FORule.instConclusion, FORule.bindings, impl, applyBindings_apply,
    bind_first, bind_second, bind_third]

theorem andElimL_conclusion : andElimL.row.instConclusion [a, b] = impl (conj a b) a := by
  simp [andElimL, schemaRule, FORule.instConclusion, FORule.bindings, impl, conj,
    applyBindings_apply, bind_first, bind_second]

theorem andElimR_conclusion : andElimR.row.instConclusion [a, b] = impl (conj a b) b := by
  simp [andElimR, schemaRule, FORule.instConclusion, FORule.bindings, impl, conj,
    applyBindings_apply, bind_first, bind_second]

theorem andIntro_conclusion :
    andIntro.row.instConclusion [a, b] = impl a (impl b (conj a b)) := by
  simp [andIntro, schemaRule, FORule.instConclusion, FORule.bindings, impl, conj,
    applyBindings_apply, bind_first, bind_second]

theorem orIntroL_conclusion : orIntroL.row.instConclusion [a, b] = impl a (disj a b) := by
  simp [orIntroL, schemaRule, FORule.instConclusion, FORule.bindings, impl, disj,
    applyBindings_apply, bind_first, bind_second]

theorem orIntroR_conclusion : orIntroR.row.instConclusion [a, b] = impl b (disj a b) := by
  simp [orIntroR, schemaRule, FORule.instConclusion, FORule.bindings, impl, disj,
    applyBindings_apply, bind_first, bind_second]

theorem orElim_conclusion : orElim.row.instConclusion [a, b, c] =
    impl (impl a c) (impl (impl b c) (impl (disj a b) c)) := by
  simp [orElim, schemaRule, FORule.instConclusion, FORule.bindings, impl, disj,
    applyBindings_apply, bind_first, bind_second, bind_third]

theorem efq_conclusion : efq.row.instConclusion [a] = impl falsum a := by
  simp [efq, schemaRule, FORule.instConclusion, FORule.bindings, impl, falsum,
    applyBindings_apply, bind_first]

theorem lem_conclusion : lem.row.instConclusion [a] = disj a (impl a falsum) := by
  simp [lem, schemaRule, FORule.instConclusion, FORule.bindings, impl, disj, falsum,
    applyBindings_apply, bind_first]

end Instances

/-! ## Substitution and bounds -/

@[simp] theorem encode_top : encode (⊤ : Formula ℕ) = impl falsum falsum := rfl

@[simp] theorem encode_neg (φ : Formula ℕ) : encode (∼φ) = impl (encode φ) falsum := rfl

theorem atomsBelow_subst {count : ℕ} {σ : Substitution ℕ}
    (bounded : ∀ a, AtomsBelow count (σ a)) : ∀ φ : Formula ℕ, AtomsBelow count (φ⟦σ⟧)
  | .atom a => bounded a
  | .falsum => trivial
  | .and φ ψ => ⟨atomsBelow_subst bounded φ, atomsBelow_subst bounded ψ⟩
  | .or φ ψ => ⟨atomsBelow_subst bounded φ, atomsBelow_subst bounded ψ⟩
  | .imp φ ψ => ⟨atomsBelow_subst bounded φ, atomsBelow_subst bounded ψ⟩

/-- Keep the atoms of the context and replace every other atom by falsity. -/
def truncate (count : ℕ) : Substitution ℕ := fun a => if a < count then .atom a else ⊥

theorem truncate_below (count : ℕ) : ∀ a, AtomsBelow count (truncate count a) := by
  intro a
  by_cases below : a < count
  · rw [truncate, if_pos below]
    exact below
  · simp [truncate, below, AtomsBelow]

theorem subst_truncate {count : ℕ} : ∀ {φ : Formula ℕ}, AtomsBelow count φ →
    φ⟦truncate count⟧ = φ
  | .atom a, below => by
      have inside : a < count := below
      simp [Formula.subst, truncate, inside]
  | .falsum, _ => rfl
  | .and φ ψ, below => by
      show Formula.and (φ⟦truncate count⟧) (ψ⟦truncate count⟧) = Formula.and φ ψ
      rw [subst_truncate below.1, subst_truncate below.2]
  | .or φ ψ, below => by
      show Formula.or (φ⟦truncate count⟧) (ψ⟦truncate count⟧) = Formula.or φ ψ
      rw [subst_truncate below.1, subst_truncate below.2]
  | .imp φ ψ, below => by
      show Formula.imp (φ⟦truncate count⟧) (ψ⟦truncate count⟧) = Formula.imp φ ψ
      rw [subst_truncate below.1, subst_truncate below.2]

/-! ## The two derivability relations agree -/

theorem list_one {α : Type} : ∀ {items : List α}, items.length = 1 → ∃ a, items = [a]
  | [a], _ => ⟨a, rfl⟩

theorem list_two {α : Type} : ∀ {items : List α}, items.length = 2 → ∃ a b, items = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

theorem list_three {α : Type} :
    ∀ {items : List α}, items.length = 3 → ∃ a b c, items = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩

theorem minimal_mem {classical : Bool} {rule : SortedFirstOrderRules.Rule}
    (member : rule ∈ minimalRules) : rule ∈ rules classical :=
  List.mem_append_left _ member

theorem efq_mem (classical : Bool) : efq ∈ rules classical :=
  List.mem_append_right _ (by simp)

theorem lem_mem : lem ∈ rules true :=
  List.mem_append_right _ (by simp)

/-- One instance of a rule at formulas of the context. -/
theorem derives_instance {classical : Bool} {count : ℕ} {rule : SortedFirstOrderRules.Rule}
    (member : rule ∈ rules classical)
    (shape : rule.variableTypes = rule.row.vars.map fun _ => wff)
    (formulas : List (Formula ℕ)) (arity : formulas.length = rule.row.vars.length)
    (below : ∀ φ ∈ formulas, AtomsBelow count φ)
    (premises : ∀ premise ∈ rule.row.instPremises (formulas.map encode),
      Derives language (rules classical) (context count) [] premise) :
    Derives language (rules classical) (context count) []
      (rule.row.instConclusion (formulas.map encode)) :=
  Derives.rule member (formulas.map encode) (by simpa using arity)
    (shape ▸ arguments_typed formulas rule.row.vars arity below)
    (by
      intro argument inArguments
      obtain ⟨φ, -, rfl⟩ := List.mem_map.mp inArguments
      exact matchCorrect_encode φ)
    premises

theorem substituted_below {count : ℕ} {σ : Substitution ℕ}
    (bounded : ∀ a, AtomsBelow count (σ a)) (formulas : List (Formula ℕ)) :
    ∀ φ ∈ formulas.map (fun χ => χ⟦σ⟧), AtomsBelow count φ := by
  intro φ member
  obtain ⟨χ, -, rfl⟩ := List.mem_map.mp member
  exact atomsBelow_subst bounded χ

/-- Every proof of the Hilbert system is a derivation of the presentation,
at every instance over the atoms of the context. -/
theorem derives_of_hilbert {classical : Bool} {count : ℕ} {φ : Formula ℕ}
    (provable : Hilbert.Standard (axioms classical) φ) :
    ∀ σ : Substitution ℕ, (∀ a, AtomsBelow count (σ a)) →
      Derives language (rules classical) (context count) [] (encode (φ⟦σ⟧)) := by
  have none : ∀ {rule : SortedFirstOrderRules.Rule} (arguments : List Pattern),
      rule.row.premises = [] → ∀ premise ∈ rule.row.instPremises arguments,
        Derives language (rules classical) (context count) [] premise := by
    intro rule arguments empty premise inPremises
    simp [FORule.instPremises, empty] at inPremises
  induction provable with
  | @axm χ s member =>
      intro σ bounded
      have options : χ = Axioms.EFQ (.atom 0) ∨
          (classical = true ∧ χ = Axioms.LEM (.atom 0)) := by
        cases classical <;> simpa [axioms] using member
      rcases options with rfl | ⟨rfl, rfl⟩
      · have step := derives_instance (classical := classical) (count := count) (efq_mem classical)
          rfl ([s 0].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
        simpa [efq_conclusion] using step
      · have step := derives_instance (count := count) lem_mem rfl
          ([s 0].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
        simpa [lem_conclusion] using step
  | @mdp φ ψ _ _ implication argument =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := mdp) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _)
        (by
          intro premise inPremises
          simp only [List.map_cons, List.map_nil, mdp_premises, List.mem_cons,
            List.not_mem_nil, or_false] at inPremises
          rcases inPremises with rfl | rfl
          · simpa using implication σ bounded
          · exact argument σ bounded)
      simpa [mdp_conclusion] using step
  | verum =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count) (efq_mem classical)
        rfl [⊥] rfl (by intro φ member; simp at member; subst member; trivial) (none _ rfl)
      simpa [efq_conclusion] using step
  | implyS φ ψ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := implyK) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [implyK_conclusion] using step
  | implyK φ ψ χ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := implyS) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ, χ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [implyS_conclusion] using step
  | andElimL φ ψ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := andElimL) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [andElimL_conclusion] using step
  | andElimR φ ψ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := andElimR) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [andElimR_conclusion] using step
  | andIntro φ ψ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := andIntro) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [andIntro_conclusion] using step
  | orIntroL φ ψ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := orIntroL) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [orIntroL_conclusion] using step
  | orIntroR φ ψ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := orIntroR) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [orIntroR_conclusion] using step
  | orElim φ ψ χ =>
      intro σ bounded
      have step := derives_instance (classical := classical) (count := count)
        (rule := orElim) (minimal_mem (by simp [minimalRules])) rfl
        ([φ, ψ, χ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [orElim_conclusion] using step

/-- Every derivation of the presentation is a proof of the Hilbert system. -/
theorem hilbert_of_derives {classical : Bool} {count : ℕ} {pattern : Pattern}
    (derived : Derives language (rules classical) (context count) [] pattern) :
    ∀ φ : Formula ℕ, pattern = encode φ → Hilbert.Standard (axioms classical) φ := by
  induction derived with
  | hypothesis member => cases member
  | @rule rule member arguments arity typed fragments _ premises =>
      intro φ same
      obtain ⟨formulas, rfl⟩ := arguments_decode typed fragments
      rw [List.length_map] at arity
      have options : rule ∈ minimalRules ∨ rule = efq ∨ (classical = true ∧ rule = lem) := by
        cases classical <;> simpa [rules] using member
      rcases options with minimal | rfl | ⟨rfl, rfl⟩
      · simp only [minimalRules, List.mem_cons, List.not_mem_nil, or_false] at minimal
        rcases minimal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode b = encode φ := by simpa [mdp_conclusion] using same
          have implication := premises (encode (a ➝ b)) (by simp [mdp_premises]) (a ➝ b) rfl
          have argument := premises (encode a) (by simp [mdp_premises]) a rfl
          rw [← encode_injective equal]
          exact Hilbert.Standard.mdp implication argument
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (a ➝ b ➝ a) = encode φ := by simpa [implyK_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.implyS a b
        · obtain ⟨a, b, c, rfl⟩ := list_three arity
          have equal : encode ((a ➝ b ➝ c) ➝ (a ➝ b) ➝ a ➝ c) = encode φ := by
            simpa [implyS_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.implyK a b c
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (a ⋏ b ➝ a) = encode φ := by simpa [andElimL_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.andElimL a b
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (a ⋏ b ➝ b) = encode φ := by simpa [andElimR_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.andElimR a b
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (a ➝ b ➝ a ⋏ b) = encode φ := by
            simpa [andIntro_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.andIntro a b
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (a ➝ a ⋎ b) = encode φ := by simpa [orIntroL_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.orIntroL a b
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (b ➝ a ⋎ b) = encode φ := by simpa [orIntroR_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.orIntroR a b
        · obtain ⟨a, b, c, rfl⟩ := list_three arity
          have equal : encode ((a ➝ c) ➝ (b ➝ c) ➝ (a ⋎ b ➝ c)) = encode φ := by
            simpa [orElim_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.Standard.orElim a b c
      · obtain ⟨a, rfl⟩ := list_one arity
        have equal : encode (⊥ ➝ a) = encode φ := by simpa [efq_conclusion] using same
        rw [← encode_injective equal]
        have instance_ := Hilbert.Standard.axm (Ax := axioms classical) (fun _ => a)
          (φ := Axioms.EFQ (.atom 0)) (by cases classical <;> simp [axioms])
        simpa using instance_
      · obtain ⟨a, rfl⟩ := list_one arity
        have equal : encode (a ⋎ ∼a) = encode φ := by simpa [lem_conclusion] using same
        rw [← encode_injective equal]
        have instance_ := Hilbert.Standard.axm (Ax := axioms true) (fun _ => a)
          (φ := Axioms.LEM (.atom 0)) (by simp [axioms])
        simpa using instance_

/-- **The presentation derives exactly what the Hilbert system proves.** A
formula over the atoms of the context is derivable from the rules exactly
when it is provable from the corresponding axioms. -/
theorem derives_iff_hilbert {classical : Bool} {count : ℕ} {φ : Formula ℕ}
    (below : AtomsBelow count φ) :
    Derives language (rules classical) (context count) [] (encode φ) ↔
      Hilbert.Standard (axioms classical) φ := by
  constructor
  · intro derived
    exact hilbert_of_derives derived φ rfl
  · intro provable
    have step := derives_of_hilbert (count := count) provable (truncate count)
      (truncate_below count)
    rwa [subst_truncate below] at step

/-- The intuitionistic rules derive the theorems of intuitionistic logic. -/
theorem derives_iff_int {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ) :
    Derives language (rules false) (context count) [] (encode φ) ↔ Propositional.Int ⊢ φ :=
  (derives_iff_hilbert below).trans Logic.iff_provable.symm

/-- With excluded middle they derive the theorems of classical logic. -/
theorem derives_iff_cl {count : ℕ} {φ : Formula ℕ} (below : AtomsBelow count φ) :
    Derives language (rules true) (context count) [] (encode φ) ↔ Propositional.Cl ⊢ φ :=
  (derives_iff_hilbert below).trans Logic.iff_provable.symm

end Mettapedia.GSLT.LanguageDef.PropositionalHilbert
