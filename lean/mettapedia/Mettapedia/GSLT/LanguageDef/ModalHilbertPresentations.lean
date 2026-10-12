import Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
import Mettapedia.GSLT.LanguageDef.DefinitionalEquations
import Foundation.Modal.Hilbert.WithRE.Basic
import Std.Data.String.ToNat

/-!
# Classical modal logics as rule presentations

A classical modal logic is given by the rule of replacement of equivalents
under the box (RE), modus ponens, three propositional schemes, and a finite
list of further axioms. The `Foundation` library writes such a logic as the
Hilbert system `Hilbert.WithRE`; the minimal one is `E`, and adding the
axioms `M`, `N`, `C`, `T`, `D`, ... gives the logics complete for classes of
neighborhood frames.

This module authors every such logic as a sorted first-order rule
presentation: one sort of formulas; falsity, implication and the box as
constructors; one rule for modus ponens, one for each scheme, one for RE,
and one for each extra axiom, whose atoms become the rule's metavariables.
`derives_iff_hilbert` proves that the presentation derives a formula over
the first `count` atoms, in the context of `count` formula variables,
exactly when the Hilbert system proves it.

The RE rule has a premise and no binder: from `φ ⭤ ψ`, infer `□φ ⭤ □ψ`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModalHilbert

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open LO LO.Modal

/-- Modal formulas over numbered atoms. -/
abbrev ModalFormula : Type := LO.Modal.Formula ℕ

/-! ## The language -/

abbrev wff : TypeExpr := .base "wff"

def nullary (label : String) : GrammarRule :=
  { label := label, category := "wff", params := [], syntaxPattern := [] }

def unary (label : String) : GrammarRule :=
  { label := label, category := "wff", params := [.simple "body" wff], syntaxPattern := [] }

def binary (label : String) : GrammarRule :=
  { label := label, category := "wff"
    params := [.simple "left" wff, .simple "right" wff], syntaxPattern := [] }

/-- One sort of formulas; falsity, implication and the box. -/
def language : LanguageDef :=
  { name := "ModalHilbert"
    types := [TypeDecl.plain "wff"]
    terms := [nullary "falsum", binary "imp", unary "box"]
    equations := []
    rewrites := [] }

def falsumP : Pattern := .apply "falsum" []
def impP (left right : Pattern) : Pattern := .apply "imp" [left, right]
def boxP (body : Pattern) : Pattern := .apply "box" [body]
def negP (body : Pattern) : Pattern := impP body falsumP
def conjP (left right : Pattern) : Pattern := negP (impP left (negP right))
def iffP (left right : Pattern) : Pattern := conjP (impP left right) (impP right left)

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

def mdp := schemaRule "mdp" ["ph", "ps"] [impP ph ps, ph] ps
def implyK := schemaRule "implyK" ["ph", "ps"] [] (impP ph (impP ps ph))
def implyS := schemaRule "implyS" ["ph", "ps", "ch"] []
  (impP (impP ph (impP ps ch)) (impP (impP ph ps) (impP ph ch)))
def elimContra := schemaRule "ec" ["ph", "ps"] [] (impP (impP (negP ps) (negP ph)) (impP ph ps))
def re := schemaRule "re" ["ph", "ps"] [iffP ph ps] (iffP (boxP ph) (boxP ps))

/-- The name of the metavariable for an atom. -/
def atomName (a : ℕ) : String := "p" ++ Nat.repr a

theorem atomName_injective : Function.Injective atomName := by
  intro first second same
  exact Nat.repr_injective ((String.append_right_inj "p").mp same)

/-- An axiom as a schema: each atom becomes a metavariable. -/
def schema : ModalFormula → Pattern
  | .atom a => .fvar (atomName a)
  | .falsum => falsumP
  | .imp φ ψ => impP (schema φ) (schema ψ)
  | .box φ => boxP (schema φ)

/-- One more than the largest atom. -/
def atomBound : ModalFormula → ℕ
  | .atom a => a + 1
  | .falsum => 0
  | .imp φ ψ => max (atomBound φ) (atomBound ψ)
  | .box φ => atomBound φ

/-- The metavariables of an axiom: one per atom below its bound. -/
def axiomVars (χ : ModalFormula) : List String := (List.range (atomBound χ)).map atomName

/-- The rule of an axiom. -/
def axiomRule (index : ℕ) (χ : ModalFormula) : SortedFirstOrderRules.Rule :=
  schemaRule ("axiom" ++ Nat.repr index) (axiomVars χ) [] (schema χ)

/-- The rules of a list of axioms, numbered from `index`. -/
def axiomRules : ℕ → List ModalFormula → List SortedFirstOrderRules.Rule
  | _, [] => []
  | index, χ :: rest => axiomRule index χ :: axiomRules (index + 1) rest

theorem mem_axiomRules {rule : SortedFirstOrderRules.Rule} :
    ∀ {index : ℕ} {extra : List ModalFormula}, rule ∈ axiomRules index extra →
      ∃ position χ, χ ∈ extra ∧ rule = axiomRule position χ
  | _, [], member => by cases member
  | index, χ :: rest, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨index, χ, by simp, rfl⟩
      · obtain ⟨position, ξ, inList, rfl⟩ := mem_axiomRules inRest
        exact ⟨position, ξ, List.mem_cons_of_mem _ inList, rfl⟩

theorem axiomRule_mem {χ : ModalFormula} :
    ∀ {start : ℕ} {extra : List ModalFormula}, χ ∈ extra →
      ∃ position, axiomRule position χ ∈ axiomRules start extra
  | start, ξ :: rest, member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨start, by simp [axiomRules]⟩
      · obtain ⟨position, inRules⟩ := axiomRule_mem (start := start + 1) inRest
        exact ⟨position, List.mem_cons_of_mem _ inRules⟩

/-- Modus ponens, the three schemes and RE. -/
def baseRules : List SortedFirstOrderRules.Rule := [mdp, implyK, implyS, elimContra, re]

/-- The rules of the logic with the given extra axioms. -/
def rules (extra : List ModalFormula) : List SortedFirstOrderRules.Rule :=
  baseRules ++ axiomRules 0 extra

/-- The axioms of the corresponding Hilbert system. -/
def axioms (extra : List ModalFormula) : Axiom ℕ := {χ | χ ∈ extra}

/-! ## Formulas as patterns -/

/-- An atom is a variable of the context. -/
def encode : ModalFormula → Pattern
  | .atom a => .bvar a
  | .falsum => falsumP
  | .imp φ ψ => impP (encode φ) (encode ψ)
  | .box φ => boxP (encode φ)

@[simp] theorem encode_atom (a : ℕ) : encode (.atom a) = .bvar a := rfl
@[simp] theorem encode_bot : encode (⊥ : ModalFormula) = falsumP := rfl
@[simp] theorem encode_imp (φ ψ : ModalFormula) : encode (φ ➝ ψ) = impP (encode φ) (encode ψ) :=
  rfl
@[simp] theorem encode_box (φ : ModalFormula) : encode (□φ) = boxP (encode φ) := rfl
@[simp] theorem encode_neg (φ : ModalFormula) : encode (∼φ) = negP (encode φ) := rfl
@[simp] theorem encode_iff (φ ψ : ModalFormula) :
    encode (φ ⭤ ψ) = iffP (encode φ) (encode ψ) := rfl

/-- Every atom of the formula is below the bound. -/
def AtomsBelow (bound : ℕ) : ModalFormula → Prop
  | .atom a => a < bound
  | .falsum => True
  | .imp φ ψ => AtomsBelow bound φ ∧ AtomsBelow bound ψ
  | .box φ => AtomsBelow bound φ

theorem AtomsBelow.mono {small large : ℕ} (inside : small ≤ large) :
    ∀ {φ : ModalFormula}, AtomsBelow small φ → AtomsBelow large φ
  | .atom _, below => Nat.lt_of_lt_of_le below inside
  | .falsum, _ => trivial
  | .imp _ _, below => ⟨AtomsBelow.mono inside below.1, AtomsBelow.mono inside below.2⟩
  | .box φ, below => AtomsBelow.mono (φ := φ) inside below

/-- Every formula mentions finitely many atoms. -/
theorem exists_atomsBelow : ∀ φ : ModalFormula, ∃ count, AtomsBelow count φ
  | .atom a => ⟨a + 1, Nat.lt_succ_self a⟩
  | .falsum => ⟨0, trivial⟩
  | .imp φ ψ => by
      obtain ⟨left, leftBelow⟩ := exists_atomsBelow φ
      obtain ⟨right, rightBelow⟩ := exists_atomsBelow ψ
      exact ⟨max left right, leftBelow.mono (le_max_left _ _), rightBelow.mono (le_max_right _ _)⟩
  | .box φ => exists_atomsBelow φ

theorem encode_injective {φ ψ : ModalFormula} (same : encode φ = encode ψ) : φ = ψ := by
  induction φ generalizing ψ with
  | atom a => cases ψ <;> simp_all [encode, falsumP, impP, boxP]
  | falsum => cases ψ <;> simp_all [encode, falsumP, impP, boxP]
  | imp left right leftHypothesis rightHypothesis =>
      cases ψ with
      | imp otherLeft otherRight =>
          simp only [encode, impP, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [leftHypothesis same.1, rightHypothesis same.2]
      | _ => simp [encode, falsumP, impP, boxP] at same
  | box body bodyHypothesis =>
      cases ψ with
      | box other =>
          simp only [encode, boxP, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [bodyHypothesis same]
      | _ => simp [encode, falsumP, impP, boxP] at same

theorem matchCorrect_encode : ∀ φ : ModalFormula, isMatchCorrectAux (encode φ) = true
  | .atom _ => by simp [encode, isMatchCorrectAux]
  | .falsum => by simp [encode, falsumP, isMatchCorrectAux, isMatchCorrectListAux]
  | .imp φ ψ => by
      simp [encode, impP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_encode φ,
        matchCorrect_encode ψ]
  | .box φ => by
      simp [encode, boxP, isMatchCorrectAux, isMatchCorrectListAux, matchCorrect_encode φ]

/-! ## Typing -/

theorem nullary_notBare (label : String) : ¬ UsesBareCollection (nullary label) := by
  rintro ⟨_, _, _, impossible⟩
  simp [nullary] at impossible

theorem unary_notBare (label : String) : ¬ UsesBareCollection (unary label) := by
  rintro ⟨_, _, _, impossible⟩
  simp [unary] at impossible

theorem binary_notBare (label : String) : ¬ UsesBareCollection (binary label) := by
  rintro ⟨_, _, _, impossible⟩
  simp [binary] at impossible

/-- A formula over the atoms of the context is a typed term. -/
theorem hasType_encode {count : ℕ} : ∀ {φ : ModalFormula}, AtomsBelow count φ →
    HasType language FreeTypeContext.empty (context count) (encode φ) wff
  | .atom a, below =>
      HasType.bvar (by simp [context, show a < count from below])
  | .falsum, _ =>
      HasType.constructor (rule := nullary "falsum") (by simp [language])
        (nullary_notBare _) .nil
  | .imp _ _, below =>
      HasType.constructor (rule := binary "imp") (by simp [language]) (binary_notBare _)
        (.cons trivial rfl (hasType_encode below.1) (.cons trivial rfl (hasType_encode below.2) .nil))
  | .box _, below =>
      HasType.constructor (rule := unary "box") (by simp [language]) (unary_notBare _)
        (.cons trivial rfl (hasType_encode below) .nil)

/-- Every typed first-order term is a formula over the atoms of the context. -/
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
      have options : rule = nullary "falsum" ∨ rule = binary "imp" ∨ rule = unary "box" := by
        simpa [language] using member
      rcases options with rfl | rfl | rfl
      · cases argumentsTyped
        exact ⟨⊥, trivial, rfl⟩
      · cases argumentsTyped with
        | cons _ _ leftTyped rest =>
          cases rest with
          | cons _ _ rightTyped rest =>
            cases rest
            have parts := fragment
            simp only [isMatchCorrectAux, isMatchCorrectListAux, Bool.and_true,
              Bool.and_eq_true] at parts
            obtain ⟨left, leftBelow, rfl⟩ := typed_decodes _ leftTyped parts.1
            obtain ⟨right, rightBelow, rfl⟩ := typed_decodes _ rightTyped parts.2
            exact ⟨left ➝ right, ⟨leftBelow, rightBelow⟩, rfl⟩
      · cases argumentsTyped with
        | cons _ _ bodyTyped rest =>
          cases rest
          have parts := fragment
          simp only [isMatchCorrectAux, isMatchCorrectListAux, Bool.and_true] at parts
          obtain ⟨body, bodyBelow, rfl⟩ := typed_decodes _ bodyTyped parts
          exact ⟨□body, bodyBelow, rfl⟩
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
    ∃ formulas : List ModalFormula, arguments = formulas.map encode
  | [], _, _, _ => ⟨[], rfl⟩
  | argument :: rest, _, typed, fragments => by
      cases typed with
      | cons first others =>
        obtain ⟨φ, -, rfl⟩ := typed_decodes argument first (fragments _ (by simp))
        obtain ⟨formulas, rfl⟩ := arguments_decode others
          (fun other member => fragments other (by simp [member]))
        exact ⟨φ :: formulas, rfl⟩

theorem arguments_typed {count : ℕ} : ∀ (formulas : List ModalFormula) (vars : List String),
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

theorem mdp_premises : mdp.row.instPremises [a, b] = [impP a b, a] := by
  simp [mdp, schemaRule, FORule.instPremises, FORule.bindings, impP, applyBindings_apply,
    bind_first, bind_second]

theorem mdp_conclusion : mdp.row.instConclusion [a, b] = b := by
  simp [mdp, schemaRule, FORule.instConclusion, FORule.bindings, bind_second]

theorem implyK_conclusion : implyK.row.instConclusion [a, b] = impP a (impP b a) := by
  simp [implyK, schemaRule, FORule.instConclusion, FORule.bindings, impP, applyBindings_apply,
    bind_first, bind_second]

theorem implyS_conclusion : implyS.row.instConclusion [a, b, c] =
    impP (impP a (impP b c)) (impP (impP a b) (impP a c)) := by
  simp [implyS, schemaRule, FORule.instConclusion, FORule.bindings, impP, applyBindings_apply,
    bind_first, bind_second, bind_third]

theorem elimContra_conclusion : elimContra.row.instConclusion [a, b] =
    impP (impP (negP b) (negP a)) (impP a b) := by
  simp [elimContra, schemaRule, FORule.instConclusion, FORule.bindings, impP, negP, falsumP,
    applyBindings_apply, bind_first, bind_second]

theorem re_premises : re.row.instPremises [a, b] = [iffP a b] := by
  simp [re, schemaRule, FORule.instPremises, FORule.bindings, iffP, conjP, negP, impP, falsumP,
    applyBindings_apply, bind_first, bind_second]

theorem re_conclusion : re.row.instConclusion [a, b] = iffP (boxP a) (boxP b) := by
  simp [re, schemaRule, FORule.instConclusion, FORule.bindings, iffP, conjP, negP, impP, boxP,
    falsumP, applyBindings_apply, bind_first, bind_second]

end Instances

theorem axiomVars_nodup (χ : ModalFormula) : (axiomVars χ).Nodup :=
  List.Nodup.map atomName_injective List.nodup_range

/-- An axiom rule at the encodings of a substitution's values is the
encoding of the substitution instance of the axiom. -/
theorem schema_instance (s : ℕ → ModalFormula) {bound : ℕ} :
    ∀ χ : ModalFormula, atomBound χ ≤ bound →
      applyBindings (((List.range bound).map atomName).zip
        ((List.range bound).map fun a => encode (s a))) (schema χ) = encode (χ⟦s⟧)
  | .atom a, inside => by
      have below : a < bound := by simp only [atomBound] at inside; omega
      have nameLookup : ((List.range bound).map atomName)[a]? = some (atomName a) := by
        simp [List.getElem?_range below]
      have valueLookup : ((List.range bound).map fun a => encode (s a))[a]? =
          some (encode (s a)) := by
        simp [List.getElem?_range below]
      rw [schema, applyBindings_fvar_of_find (find?_zip
        (List.Nodup.map atomName_injective List.nodup_range) nameLookup valueLookup)]
      rfl
  | .falsum, _ => by simp [schema, falsumP, applyBindings]; rfl
  | .imp φ ψ, inside => by
      have left : atomBound φ ≤ bound := le_trans (le_max_left _ _) inside
      have right : atomBound ψ ≤ bound := le_trans (le_max_right _ _) inside
      simp only [schema, impP, applyBindings_apply, List.map_cons, List.map_nil]
      rw [schema_instance s φ left, schema_instance s ψ right]
      rfl
  | .box φ, inside => by
      simp only [schema, boxP, applyBindings_apply, List.map_cons, List.map_nil]
      rw [schema_instance s φ inside]
      rfl

theorem axiomRule_conclusion (index : ℕ) (χ : ModalFormula) (s : ℕ → ModalFormula) :
    (axiomRule index χ).row.instConclusion ((List.range (atomBound χ)).map fun a => encode (s a)) =
      encode (χ⟦s⟧) :=
  schema_instance s χ le_rfl

/-! ## Substitution and bounds -/

theorem atomsBelow_subst {count : ℕ} {σ : Substitution ℕ}
    (bounded : ∀ a, AtomsBelow count (σ a)) : ∀ φ : ModalFormula, AtomsBelow count (φ⟦σ⟧)
  | .atom a => bounded a
  | .falsum => trivial
  | .imp φ ψ => ⟨atomsBelow_subst bounded φ, atomsBelow_subst bounded ψ⟩
  | .box φ => atomsBelow_subst bounded φ

/-- Keep the atoms of the context and replace every other atom by falsity. -/
def truncate (count : ℕ) : Substitution ℕ := fun a => if a < count then .atom a else ⊥

theorem truncate_below (count : ℕ) : ∀ a, AtomsBelow count (truncate count a) := by
  intro a
  by_cases below : a < count
  · rw [truncate, if_pos below]
    exact below
  · simp [truncate, below, AtomsBelow]

theorem subst_truncate {count : ℕ} : ∀ {φ : ModalFormula}, AtomsBelow count φ →
    φ⟦truncate count⟧ = φ
  | .atom a, below => by
      have inside : a < count := below
      simp [Formula.subst, truncate, inside]
  | .falsum, _ => rfl
  | .imp φ ψ, below => by
      show Formula.imp (φ⟦truncate count⟧) (ψ⟦truncate count⟧) = Formula.imp φ ψ
      rw [subst_truncate below.1, subst_truncate below.2]
  | .box φ, below => by
      show Formula.box (φ⟦truncate count⟧) = Formula.box φ
      rw [subst_truncate (φ := φ) below]

/-! ## The two derivability relations agree -/

theorem list_two {α : Type} : ∀ {items : List α}, items.length = 2 → ∃ a b, items = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

theorem list_three {α : Type} :
    ∀ {items : List α}, items.length = 3 → ∃ a b c, items = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩

theorem base_mem {extra : List ModalFormula} {rule : SortedFirstOrderRules.Rule}
    (member : rule ∈ baseRules) : rule ∈ rules extra :=
  List.mem_append_left _ member

/-- One instance of a rule at formulas of the context. -/
theorem derives_instance {extra : List ModalFormula} {count : ℕ}
    {rule : SortedFirstOrderRules.Rule} (member : rule ∈ rules extra)
    (shape : rule.variableTypes = rule.row.vars.map fun _ => wff)
    (formulas : List ModalFormula) (arity : formulas.length = rule.row.vars.length)
    (below : ∀ φ ∈ formulas, AtomsBelow count φ)
    (premises : ∀ premise ∈ rule.row.instPremises (formulas.map encode),
      Derives language (rules extra) (context count) [] premise) :
    Derives language (rules extra) (context count) []
      (rule.row.instConclusion (formulas.map encode)) :=
  Derives.rule member (formulas.map encode) (by simpa using arity)
    (shape ▸ arguments_typed formulas rule.row.vars arity below)
    (by
      intro argument inArguments
      obtain ⟨φ, -, rfl⟩ := List.mem_map.mp inArguments
      exact matchCorrect_encode φ)
    premises

theorem substituted_below {count : ℕ} {σ : Substitution ℕ}
    (bounded : ∀ a, AtomsBelow count (σ a)) (formulas : List ModalFormula) :
    ∀ φ ∈ formulas.map (fun χ => χ⟦σ⟧), AtomsBelow count φ := by
  intro φ member
  obtain ⟨χ, -, rfl⟩ := List.mem_map.mp member
  exact atomsBelow_subst bounded χ

/-- Every proof of the Hilbert system is a derivation of the presentation,
at every instance over the atoms of the context. -/
theorem derives_of_hilbert {extra : List ModalFormula} {count : ℕ} {φ : ModalFormula}
    (provable : Hilbert.WithRE (axioms extra) φ) :
    ∀ σ : Substitution ℕ, (∀ a, AtomsBelow count (σ a)) →
      Derives language (rules extra) (context count) [] (encode (φ⟦σ⟧)) := by
  have none : ∀ {rule : SortedFirstOrderRules.Rule} (arguments : List Pattern),
      rule.row.premises = [] → ∀ premise ∈ rule.row.instPremises arguments,
        Derives language (rules extra) (context count) [] premise := by
    intro rule arguments empty premise inPremises
    simp [FORule.instPremises, empty] at inPremises
  induction provable with
  | @axm χ s member =>
      intro σ bounded
      obtain ⟨position, inRules⟩ := axiomRule_mem (start := 0) member
      let values : ℕ → ModalFormula := fun a => (s a)⟦σ⟧
      have step := derives_instance (count := count)
        (List.mem_append_right baseRules inRules) rfl
        ((List.range (atomBound χ)).map values) (by simp [axiomRule, schemaRule, axiomVars])
        (by
          intro ψ inList
          obtain ⟨a, -, rfl⟩ := List.mem_map.mp inList
          exact atomsBelow_subst bounded (s a))
        (none _ rfl)
      rw [List.map_map] at step
      have conclusion := axiomRule_conclusion position χ values
      simp only [Function.comp_def] at step
      rw [conclusion] at step
      have composed : χ⟦s⟧⟦σ⟧ = χ⟦values⟧ := by
        rw [← Formula.subst.def_comp]
        rfl
      rw [composed]
      exact step
  | @mdp φ ψ _ _ implication argument =>
      intro σ bounded
      have step := derives_instance (extra := extra) (count := count)
        (rule := mdp) (base_mem (by simp [baseRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _)
        (by
          intro premise inPremises
          simp only [List.map_cons, List.map_nil, mdp_premises, List.mem_cons,
            List.not_mem_nil, or_false] at inPremises
          rcases inPremises with rfl | rfl
          · simpa using implication σ bounded
          · exact argument σ bounded)
      simpa [mdp_conclusion] using step
  | @re φ ψ _ equivalence =>
      intro σ bounded
      have step := derives_instance (extra := extra) (count := count)
        (rule := re) (base_mem (by simp [baseRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _)
        (by
          intro premise inPremises
          simp only [List.map_cons, List.map_nil, re_premises, List.mem_cons,
            List.not_mem_nil, or_false] at inPremises
          subst inPremises
          simpa using equivalence σ bounded)
      simpa [re_conclusion] using step
  | implyK φ ψ =>
      intro σ bounded
      have step := derives_instance (extra := extra) (count := count)
        (rule := implyK) (base_mem (by simp [baseRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [implyK_conclusion] using step
  | implyS φ ψ χ =>
      intro σ bounded
      have step := derives_instance (extra := extra) (count := count)
        (rule := implyS) (base_mem (by simp [baseRules])) rfl
        ([φ, ψ, χ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [implyS_conclusion] using step
  | ec φ ψ =>
      intro σ bounded
      have step := derives_instance (extra := extra) (count := count)
        (rule := elimContra) (base_mem (by simp [baseRules])) rfl
        ([φ, ψ].map fun χ => χ⟦σ⟧) rfl (substituted_below bounded _) (none _ rfl)
      simpa [elimContra_conclusion] using step

/-- Every derivation of the presentation is a proof of the Hilbert system. -/
theorem hilbert_of_derives {extra : List ModalFormula} {count : ℕ} {pattern : Pattern}
    (derived : Derives language (rules extra) (context count) [] pattern) :
    ∀ φ : ModalFormula, pattern = encode φ → Hilbert.WithRE (axioms extra) φ := by
  induction derived with
  | hypothesis member => cases member
  | @rule rule member arguments arity typed fragments _ premises =>
      intro φ same
      obtain ⟨formulas, rfl⟩ := arguments_decode typed fragments
      rw [List.length_map] at arity
      rcases List.mem_append.mp member with base | extraRule
      · simp only [baseRules, List.mem_cons, List.not_mem_nil, or_false] at base
        rcases base with rfl | rfl | rfl | rfl | rfl
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode b = encode φ := by simpa [mdp_conclusion] using same
          have implication := premises (encode (a ➝ b)) (by simp [mdp_premises]) (a ➝ b) rfl
          have argument := premises (encode a) (by simp [mdp_premises]) a rfl
          rw [← encode_injective equal]
          exact Hilbert.WithRE.mdp implication argument
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (Axioms.ImplyK a b) = encode φ := by
            simpa [implyK_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.WithRE.implyK a b
        · obtain ⟨a, b, c, rfl⟩ := list_three arity
          have equal : encode (Axioms.ImplyS a b c) = encode φ := by
            simpa [implyS_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.WithRE.implyS a b c
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (Axioms.ElimContra a b) = encode φ := by
            simpa [elimContra_conclusion] using same
          rw [← encode_injective equal]
          exact Hilbert.WithRE.ec a b
        · obtain ⟨a, b, rfl⟩ := list_two arity
          have equal : encode (□a ⭤ □b) = encode φ := by simpa [re_conclusion] using same
          have equivalence := premises (encode (a ⭤ b)) (by simp [re_premises]) (a ⭤ b) rfl
          rw [← encode_injective equal]
          exact Hilbert.WithRE.re equivalence
      · obtain ⟨position, χ, inList, rfl⟩ := mem_axiomRules extraRule
        have count : formulas.length = atomBound χ := by
          simpa [axiomRule, schemaRule, axiomVars] using arity
        let values : ℕ → ModalFormula := fun a => formulas[a]?.getD ⊥
        have arguments : formulas.map encode =
            (List.range (atomBound χ)).map fun a => encode (values a) := by
          refine List.ext_getElem (by simp [count]) fun index left right => ?_
          have inside : index < formulas.length := by simpa using left
          simp [values, List.getElem?_eq_getElem inside]
        rw [arguments, axiomRule_conclusion] at same
        rw [← encode_injective same]
        exact Hilbert.WithRE.axm values inList

/-- **The presentation derives exactly what the Hilbert system proves.** -/
theorem derives_iff_hilbert {extra : List ModalFormula} {count : ℕ} {φ : ModalFormula}
    (below : AtomsBelow count φ) :
    Derives language (rules extra) (context count) [] (encode φ) ↔
      Hilbert.WithRE (axioms extra) φ := by
  constructor
  · intro derived
    exact hilbert_of_derives derived φ rfl
  · intro provable
    have step := derives_of_hilbert (count := count) provable (truncate count)
      (truncate_below count)
    rwa [subst_truncate below] at step

end Mettapedia.GSLT.LanguageDef.ModalHilbert
