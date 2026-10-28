import Mettapedia.GSLT.Parsing.CanonicalGrammar
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Constructor-tree projection through the authoritative LanguageDef

The existing canonical tree carrier is projected into the existing Pattern
carrier using the actual core declarations. Constructor and result sort must
select exactly one declaration occurrence. Argument types come from that row,
not from constructor spelling or host equations.

The independent formation relation and the executable projection agree in
both directions. Every projected constructor tree has the core typing judgment.
This boundary covers first-order constructor trees. Token interpretation,
binders, source spans, native iteration and the preceding byte parser are
separate implementation and correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ConstructorTermProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open Mettapedia.GSLT.LanguageDef.WellSorted

def matching (language : LanguageDef) (sort label : String) : List GrammarRule :=
  language.terms.filter fun rule => rule.label == label && rule.category == sort

def selectRule? (language : LanguageDef) (sort label : String) : Option GrammarRule :=
  match matching language sort label with
  | [rule] => some rule
  | _ => none

theorem selectRule_some_iff (language : LanguageDef) (sort label : String) (rule : GrammarRule) :
    selectRule? language sort label = some rule ↔ matching language sort label = [rule] := by
  unfold selectRule?
  cases matching language sort label with
  | nil => simp
  | cons first rest => cases rest <;> simp

theorem matching_singleton (language : LanguageDef) (sort label : String) (rule : GrammarRule)
    (unique : matching language sort label = [rule]) :
    rule ∈ language.terms ∧ rule.label = label ∧ rule.category = sort := by
  have member : rule ∈ matching language sort label := by rw [unique]; simp
  simpa [matching] using member

mutual
  def project? (language : LanguageDef) (sort : String) : CanonicalTerm → Option Pattern
    | .node label children => do
        let rule ← selectRule? language sort label
        let arguments ← projectArguments? language rule.params children
        pure (.apply label arguments)
    | _ => none
  termination_by source => sizeOf source

  def projectArguments? (language : LanguageDef) :
      List TermParam → List CanonicalTerm → Option (List Pattern)
    | [], [] => some []
    | .simple _ (.base sort) :: parameters, child :: children => do
        pure ((← project? language sort child) ::
          (← projectArguments? language parameters children))
    | _, _ => none
  termination_by _ source => sizeOf source
end

mutual
  inductive Projects (language : LanguageDef) : String → CanonicalTerm → Pattern → Prop
    | node {sort label : String} {rule : GrammarRule}
        {children : List CanonicalTerm} {arguments : List Pattern}
        (unique : matching language sort label = [rule])
        (slots : ProjectsArguments language rule.params children arguments) :
        Projects language sort (.node label children) (.apply label arguments)

  inductive ProjectsArguments (language : LanguageDef) :
      List TermParam → List CanonicalTerm → List Pattern → Prop
    | nil : ProjectsArguments language [] [] []
    | cons {name sort : String} {parameters : List TermParam}
        {child : CanonicalTerm} {children : List CanonicalTerm}
        {argument : Pattern} {arguments : List Pattern}
        (head : Projects language sort child argument)
        (tail : ProjectsArguments language parameters children arguments) :
        ProjectsArguments language (.simple name (.base sort) :: parameters)
          (child :: children) (argument :: arguments)
end

variable {language : LanguageDef}

theorem ProjectsArguments.notBare {rule : GrammarRule}
    {children : List CanonicalTerm} {arguments : List Pattern}
    (slots : ProjectsArguments language rule.params children arguments) : ¬ UsesBareCollection rule := by
  rintro ⟨name, kind, element, shape⟩
  cases mode : rule.collectionRepresentation with
  | bare =>
      rw [GrammarRule.bareParams_of_bare rule mode] at shape
      rw [shape] at slots
      cases slots
  | wrapped => simp [GrammarRule.bareParams, mode] at shape

mutual
  theorem Projects.typed {sort : String} {source : CanonicalTerm} {term : Pattern}
      (projected : Projects language sort source term)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      HasSort language free bound term sort := by
    cases projected with
    | node unique slots =>
        obtain ⟨member, label, category⟩ := matching_singleton _ _ _ _ unique
        rw [← label, ← category]
        exact .constructor member slots.notBare (slots.typed free bound)
  termination_by sizeOf source

  theorem ProjectsArguments.typed {parameters : List TermParam}
      {source : List CanonicalTerm} {terms : List Pattern}
      (projected : ProjectsArguments language parameters source terms)
      (free : FreeTypeContext) (bound : List TypeExpr) :
      ArgumentsHaveTypes language free bound terms parameters := by
    cases projected with
    | nil => exact .nil
    | cons head tail => exact .cons trivial rfl (head.typed free bound) (tail.typed free bound)
  termination_by sizeOf source
end

mutual
  theorem Projects.executed {sort : String} {source : CanonicalTerm} {term : Pattern}
      (projected : Projects language sort source term) : project? language sort source = some term := by
    cases projected with
    | node unique slots =>
        have selected := (selectRule_some_iff _ _ _ _).mpr unique
        simp [project?.eq_def, selected, slots.executed]
  termination_by sizeOf source

  theorem ProjectsArguments.executed {parameters : List TermParam}
      {source : List CanonicalTerm} {terms : List Pattern}
      (projected : ProjectsArguments language parameters source terms) :
      projectArguments? language parameters source = some terms := by
    cases projected with
    | nil => simp [projectArguments?]
    | cons head tail => simp [projectArguments?, head.executed, tail.executed]
  termination_by sizeOf source
end

mutual
  theorem project_sound (sort : String) (source : CanonicalTerm) (term : Pattern)
      (success : project? language sort source = some term) : Projects language sort source term := by
    cases source with
    | text spelling => simp [project?] at success
    | seq children => simp [project?] at success
    | node label children =>
        cases selected : selectRule? language sort label with
        | none => simp [project?.eq_def, selected] at success
        | some rule =>
            cases slots : projectArguments? language rule.params children with
            | none => simp [project?.eq_def, selected, slots] at success
            | some arguments =>
                have same : Pattern.apply label arguments = term := by
                  simpa [project?.eq_def, selected, slots] using success
                subst term
                exact .node ((selectRule_some_iff _ _ _ _).mp selected)
                  (projectArguments_sound _ _ _ slots)
  termination_by sizeOf source

  theorem projectArguments_sound (parameters : List TermParam) (source : List CanonicalTerm)
      (terms : List Pattern) (success : projectArguments? language parameters source = some terms) :
      ProjectsArguments language parameters source terms := by
    cases parameters with
    | nil =>
        cases source with
        | nil => simp [projectArguments?] at success; subst terms; exact .nil
        | cons child children => simp [projectArguments?] at success
    | cons parameter parameters =>
        cases source with
        | nil => simp [projectArguments?] at success
        | cons child children =>
            cases parameter with
            | abstractionNamed binder name type => simp [projectArguments?] at success
            | multiAbstractionNamed binders name type => simp [projectArguments?] at success
            | simple name type =>
                cases type with
                | arrow left right => simp [projectArguments?] at success
                | multiBinder type => simp [projectArguments?] at success
                | collection kind type => simp [projectArguments?] at success
                | base sort =>
                    cases head : project? language sort child with
                    | none => simp [projectArguments?, head] at success
                    | some argument =>
                        cases tail : projectArguments? language parameters children with
                        | none => simp [projectArguments?, head, tail] at success
                        | some arguments =>
                            have same : argument :: arguments = terms := by
                              simpa [projectArguments?, head, tail] using success
                            subst terms
                            exact .cons (project_sound _ _ _ head) (projectArguments_sound _ _ _ tail)
  termination_by sizeOf source
end

theorem project_iff (sort : String) (source : CanonicalTerm) (term : Pattern) :
    project? language sort source = some term ↔ Projects language sort source term :=
  ⟨project_sound sort source term, Projects.executed⟩

theorem project_is_core_typed (sort : String) (source : CanonicalTerm) (term : Pattern)
    (success : project? language sort source = some term) :
    HasSort language FreeTypeContext.empty [] term sort :=
  (project_sound sort source term success).typed _ _

/-- Multiplicity is retained even when two source occurrences project to one value. -/
theorem repeated_alternatives (sort : String) (source : CanonicalTerm) (term : Pattern)
    (success : project? language sort source = some term) :
    [source, source].mapM (project? language sort) = some [term, term] := by
  simp [success]

def zeroRow : GrammarRule := { label := "Z", category := "Nat", params := [], syntaxPattern := [] }
def successorRow : GrammarRule where
  label := "S"
  category := "Nat"
  params := [.simple "child" (.base "Nat")]
  syntaxPattern := [.nonTerminal "child"]
def naturals : LanguageDef where
  name := "ProjectionNaturals"
  types := [TypeDecl.plain "Nat"]
  terms := [zeroRow, successorRow]
  equations := []
  rewrites := []

theorem nested_constructor_control :
    project? naturals "Nat" (.node "S" [.node "Z" []]) = some (.apply "S" [.apply "Z" []]) := by
  simp [project?, projectArguments?, selectRule?, matching, naturals, zeroRow, successorRow]

theorem unknown_constructor_control : project? naturals "Nat" (.node "Invented" []) = none := by
  simp [project?, selectRule?, matching, naturals, zeroRow, successorRow]
theorem wrong_sort_control : project? naturals "Other" (.node "Z" []) = none := by
  simp [project?, selectRule?, matching, naturals, zeroRow, successorRow]
theorem wrong_arity_control : project? naturals "Nat" (.node "S" []) = none := by
  simp [project?, projectArguments?, selectRule?, matching, naturals, zeroRow, successorRow]
theorem duplicate_authority_control :
    project? { naturals with terms := [zeroRow, zeroRow] } "Nat" (.node "Z" []) = none := by
  simp [project?, selectRule?, matching, zeroRow]

#print axioms project_iff
#print axioms project_is_core_typed
#print axioms repeated_alternatives

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ConstructorTermProjection
