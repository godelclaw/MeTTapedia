import Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversionCertificates
import Mettapedia.GSLT.LanguageDef.DefinitionalAdmission
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SortedFirstOrderAuthoring

/-!
# Controls: propositional calculus with defined connectives

The language has implication and negation as primitives. Conjunction, the
biconditional and disjunction are defined as in the propositional part of
`set.mm0`; exclusive disjunction is defined from two of them, so one
unfolding passes through two definitions. The rules are the three axiom
schemes and modus ponens. Everything is authored in the module quotation:
definitions are ordinary rows of its `Equations` block.

Positive controls: the language is admitted; full unfolding computes the
expected normal form; a hypothesis in primitive form yields the defined
form by one conversion; a closed theorem is checked from the identity proof
and one conversion under implication; the base language has the two
primitive connectives only, and the unfolded theorem is derivable in the
base presentation.

Negative controls: a wrong unfolding is unequal and its certificate is
refused; a conjunction is not a statement of the base language; a cyclic
definition, a constructor with two definitions, a definition with a
repeated formal and a definition with fewer formals than its constructor
has parameters are not admitted; commutativity is not a definition,
although it is an equation of its language and generates the expected
equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SortedFirstOrderAuthoring

def propositional : QuotedInferenceTheory := inferenceTheory! Theory Propositional() {
  Types { wff; }
  Exports { wff; }
  Terms {
    wi . ph:wff, ps:wff |- "(" ph "->" ps ")" : wff;
    wn . ph:wff |- "~" ph : wff;
    wa . ph:wff, ps:wff |- "(" ph "/\\" ps ")" : wff;
    wb . ph:wff, ps:wff |- "(" ph "<->" ps ")" : wff;
    wo . ph:wff, ps:wff |- "(" ph "\\/" ps ")" : wff;
    wx . ph:wff, ps:wff |- "(" ph "(+)" ps ")" : wff;
  }
  Equations {
    (wa ph ps) == (wn (wi ph (wn ps)));
    (wb ph ps) == (wn (wi (wi ph ps) (wn (wi ps ph))));
    (wo ph ps) == (wi (wn ph) ps);
    (wx ph ps) == (wa (wo ph ps) (wn (wa ph ps)));
  }
  Judgments { wff; }
  Inferences {
    ax_1 (ph:wff, ps:wff) : [] => (wi ph (wi ps ph));
    ax_2 (ph:wff, ps:wff, ch:wff) : [] =>
      (wi (wi ph (wi ps ch)) (wi (wi ph ps) (wi ph ch)));
    ax_3 (ph:wff, ps:wff) : [] => (wi (wi (wn ph) (wn ps)) (wi ps ph));
    ax_mp (ph:wff, ps:wff) : [ph, (wi ph ps)] => ps;
  }
}

abbrev language : LanguageDef := propositional.toLanguageDef

abbrev inferenceRules : List Rule := rules propositional

abbrev judgments : List String := judgmentSorts propositional

abbrev rows : List Row := definitions language

def wi (left right : Pattern) : Pattern := .apply "wi" [left, right]
def wn (inner : Pattern) : Pattern := .apply "wn" [inner]
def wa (left right : Pattern) : Pattern := .apply "wa" [left, right]
def wx (left right : Pattern) : Pattern := .apply "wx" [left, right]

/-- Two formula variables of the ambient context. -/
def p : Pattern := .bvar 0
def q : Pattern := .bvar 1

def context : List TypeExpr := [.base "wff", .base "wff"]

/-! ## Admission -/

theorem admitted : checkDefinitional language = true := by decide +kernel

theorem definitional : DefinitionalLanguage language rows := checkDefinitional_sound admitted

/-- The rows are determined by the language. -/
theorem rows_unique {other : List Row} (also : DefinitionalLanguage language other) :
    other = rows :=
  also.rows_eq

theorem heads_read : rows.map (·.head) = ["wa", "wb", "wo", "wx"] := by decide +kernel

theorem rules_formed : ∀ rule ∈ inferenceRules, rule.WellFormed language judgments := by
  have checked : inferenceRules.all (fun rule => rule.check language judgments) = true := by
    decide +kernel
  intro rule member
  exact (Rule.check_iff language judgments rule).mp (List.all_eq_true.mp checked rule member)

theorem rules_distinct : (inferenceRules.map (fun rule => rule.row.id)).Nodup := by
  decide +kernel

/-! ## Unfolding -/

/-- Exclusive disjunction unfolds through disjunction and conjunction. -/
theorem exclusive_unfolds :
    expand rows (wx p q) =
      wn (wi (wi (wn p) q) (wn (wn (wn (wi p (wn q)))))) := by decide +kernel

theorem conjunction_equals_its_body {base : BasePremiseEvaluator} :
    EquationEquiv base language (wa p q) (wn (wi p (wn q))) :=
  (definitional.equationEquiv_iff _ _).mpr (by decide +kernel)

/-- Swapping the two formulas in the body is not the definition. -/
theorem wrong_unfolding_unequal {base : BasePremiseEvaluator} :
    ¬ EquationEquiv base language (wa p q) (wn (wi q (wn p))) := by
  intro equivalent
  have same := (definitional.equationEquiv_iff _ _).mp equivalent
  revert same
  decide +kernel

/-! ## Certificates -/

/-- From the primitive form to the defined form, by one conversion. -/
def foldConjunction : ModuloProof := .convert (wa p q) (.premise 0)

theorem fold_accepted :
    proofModulo? rows language inferenceRules context [wn (wi p (wn q))]
      foldConjunction = some (wa p q) := by decide +kernel

theorem fold_derivable {base : BasePremiseEvaluator} :
    DerivesModulo base language inferenceRules context [wn (wi p (wn q))]
      (wa p q) :=
  (derivesModulo_iff_accepted definitional rules_distinct _).mpr ⟨_, fold_accepted⟩

theorem wrong_fold_refused :
    proofModulo? rows language inferenceRules context [wn (wi p (wn q))]
      (.convert (wa q p) (.premise 0)) = none := by decide +kernel

/-- The primitive form of the conjunction of the two variables. -/
def body : Pattern := wn (wi p (wn q))

/-- The usual five-step proof of `body -> body`. -/
def identityProof : ModuloProof :=
  .node ⟨⟨"ax_mp"⟩, [wi body (wi body body), wi body body]⟩
    [.node ⟨⟨"ax_1"⟩, [body, body]⟩ [],
      .node ⟨⟨"ax_mp"⟩,
          [wi body (wi (wi body body) body), wi (wi body (wi body body)) (wi body body)]⟩
        [.node ⟨⟨"ax_1"⟩, [body, wi body body]⟩ [],
          .node ⟨⟨"ax_2"⟩, [body, wi body body, body]⟩ []]]

/-- `(p /\ q) -> ~(p -> ~q)`: the identity proof, then one conversion under
the implication. -/
def conjunctionElimination : ModuloProof := .convert (wi (wa p q) body) identityProof

theorem identity_accepted :
    proofModulo? rows language inferenceRules context [] identityProof =
      some (wi body body) := by decide +kernel

theorem elimination_accepted :
    proofModulo? rows language inferenceRules context [] conjunctionElimination =
      some (wi (wa p q) body) := by decide +kernel

theorem elimination_derivable {base : BasePremiseEvaluator} :
    DerivesModulo base language inferenceRules context [] (wi (wa p q) body) :=
  (derivesModulo_iff_accepted definitional rules_distinct _).mpr ⟨_, elimination_accepted⟩

/-! ## The base presentation -/

/-- The base language declares the primitive connectives only. -/
theorem base_constructors :
    (baseLanguage language rows).terms.map (·.label) = ["wi", "wn"] := by decide +kernel

theorem base_rules_formed : ∀ rule ∈ inferenceRules.map (expandRule rows),
    rule.WellFormed (baseLanguage language rows) judgments := by
  intro unfolded member
  obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
  exact expandRule_wellFormed definitional (rules_formed rule ruleMember)

/-- A conjunction is not a statement of the base language. -/
theorem conjunction_not_base_statement :
    ¬ Statement (baseLanguage language rows) judgments context (wa p q) := by
  intro statement
  have checked := (checkStatement_iff (baseLanguage language rows) judgments context (wa p q)
    (by decide +kernel)).mpr statement
  revert checked
  decide +kernel

/-- The same theorem, unfolded, in the base presentation: it is the
identity. -/
theorem elimination_unfolds_to_identity :
    Derives (baseLanguage language rows) (inferenceRules.map (expandRule rows)) context []
      (wi body body) := by
  have unfolded := derives_expand_of_derivesModulo (base := fun _ _ _ => []) definitional
    rules_formed (elimination_derivable (base := fun _ _ _ => []))
  have target : expand rows (wi (wa p q) body) = wi body body := by decide +kernel
  rw [target] at unfolded
  exact unfolded

/-! ## What is not admitted -/

def cyclic : QuotedTheory := moduleTheory! Theory Cyclic() {
  Types { wff; }
  Terms {
    wn . ph:wff |- "~" ph : wff;
    wc . ph:wff |- "!" ph : wff;
  }
  Equations { (wc ph) == (wn (wc ph)); }
}

/-- A body that mentions its own head: no list of rows makes the language
definitional. -/
theorem cyclic_not_definitional :
    ¬ ∃ rows, DefinitionalLanguage cyclic.toLanguageDef rows := by
  rw [← checkDefinitional_iff]
  decide +kernel

def definedTwice : QuotedTheory := moduleTheory! Theory DefinedTwice() {
  Types { wff; }
  Terms {
    wn . ph:wff |- "~" ph : wff;
    wc . ph:wff |- "!" ph : wff;
  }
  Equations {
    (wc ph) == (wn ph);
    (wc ph) == (wn (wn ph));
  }
}

theorem definedTwice_not_definitional :
    ¬ ∃ rows, DefinitionalLanguage definedTwice.toLanguageDef rows := by
  rw [← checkDefinitional_iff]
  decide +kernel

def repeatedFormal : QuotedTheory := moduleTheory! Theory RepeatedFormal() {
  Types { wff; }
  Terms {
    wn . ph:wff |- "~" ph : wff;
    wd . ph:wff, ps:wff |- "(" ph "&" ps ")" : wff;
  }
  Equations { (wd ph ph) == (wn ph); }
}

theorem repeatedFormal_not_definitional :
    ¬ ∃ rows, DefinitionalLanguage repeatedFormal.toLanguageDef rows := by
  rw [← checkDefinitional_iff]
  decide +kernel

def commutative : QuotedTheory := moduleTheory! Theory Commutative() {
  Types { wff; }
  Terms {
    wn . ph:wff |- "~" ph : wff;
    wa . ph:wff, ps:wff |- "(" ph "/\\" ps ")" : wff;
  }
  Equations { (wa ph ps) == (wa ps ph); }
}

def missingFormal : QuotedTheory := moduleTheory! Theory MissingFormal() {
  Types { wff; }
  Terms {
    wn . ph:wff |- "~" ph : wff;
    wt . ph:wff, ps:wff |- "(" ph "!" ps ")" : wff;
  }
  Equations { (wt ph) == (wn ph); }
}

/-- The constructor has two parameters and the definition one formal. -/
theorem missingFormal_not_definitional :
    ¬ ∃ rows, DefinitionalLanguage missingFormal.toLanguageDef rows := by
  rw [← checkDefinitional_iff]
  decide +kernel

/-- Commutativity is not a definition. -/
theorem commutative_not_definitional :
    ¬ ∃ rows, DefinitionalLanguage commutative.toLanguageDef rows := by
  rw [← checkDefinitional_iff]
  decide +kernel

/-- It is still an equation of its language, and it relates the two orders. -/
theorem commutative_equation_holds {base : BasePremiseEvaluator} :
    EquationEquiv base commutative.toLanguageDef (wa p q) (wa q p) := by
  let row : Row := ⟨"wa", ["ph", "ps"], .apply "wa" [.fvar "ps", .fvar "ph"]⟩
  have formed : row.WellFormed := (Row.check_iff row).mp (by decide +kernel)
  obtain ⟨equation, authored, found⟩ :
      ∃ equation ∈ commutative.toLanguageDef.equations, rowOf? equation = some row := by
    decide +kernel
  have related := instance_equivalent (base := base) authored (rowOf?_sound found) formed
    [("ph", p), ("ps", q)]
  have left : applyBindings [("ph", p), ("ps", q)] row.left = wa p q := by decide +kernel
  have right : applyBindings [("ph", p), ("ps", q)] row.body = wa q p := by decide +kernel
  rw [left, right] at related
  exact related

end Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion.Controls
