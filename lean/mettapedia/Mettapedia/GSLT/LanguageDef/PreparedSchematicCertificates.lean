import Mettapedia.GSLT.LanguageDef.PreparedSchematicInference

/-!
# Complete certificates over prepared schematic rules

The existing open-proof wire format is checked against an installed table of
numbered templates. Compilation happens once per rule table, not once per
invocation. The resulting checker agrees on every certificate, including
refusals, with the authored many-sorted first-order certificate checker.

The completeness theorem concerns derivations in the installed calculus.
It does not claim that a search strategy enumerates all answers, that the
installed rules are logically conservative extensions of another calculus,
or that an untrusted serialized prepared table authenticates itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PreparedSchematicCertificates

open Mettapedia.OSLF.MeTTaIL.Syntax
open CertificateGSLT SortedFirstOrderRules PreparedSchematicInference

abbrev Table := List (String × PreparedRule)

def install (rules : List Rule) : Table :=
  rules.map fun rule => (rule.row.id, prepare rule)

def lookup? (table : Table) (name : String) : Option PreparedRule :=
  (table.find? fun entry => entry.1 == name).map Prod.snd

theorem lookup_install (rules : List Rule) (name : String) :
    lookup? (install rules) name = (lookupRule? rules name).map prepare := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      simp only [install, List.map_cons, lookup?, lookupRule?, List.find?_cons]
      split <;> simp_all [lookup?, install, lookupRule?]

private theorem apply_compiled {language : LanguageDef} {judgments : List String}
    {rule : Rule} (formed : rule.WellFormed language judgments)
    (context : List TypeExpr) (arguments premises : List Pattern) :
    apply? language context (prepare rule) arguments premises =
      if arguments.length = rule.row.vars.length ∧
          checkArgumentTypes language context arguments rule.variableTypes = true then
        if premises = rule.row.instPremises arguments then
          some (rule.row.instConclusion arguments) else none
      else none := by
  by_cases arity : arguments.length = rule.row.vars.length
  · unfold apply?
    rw [prepared_premises formed arguments arity, prepared_conclusion formed arguments arity]
    simp only [prepare, arity, true_and]
    split <;> simp_all
  · simp [apply?, prepare, arity]

mutual
  def proof? (language : LanguageDef) (table : Table)
      (context : List TypeExpr) (hypotheses : List Pattern) : RawOpenProof → Option Pattern
    | .premise index => hypotheses[index]?
    | .node invocation children => do
        let rule ← lookup? table invocation.ruleId.value
        let premises ← children? language table context hypotheses children
        apply? language context rule invocation.arguments premises
  termination_by proof => sizeOf proof

  def children? (language : LanguageDef) (table : Table)
      (context : List TypeExpr) (hypotheses : List Pattern) :
      List RawOpenProof → Option (List Pattern)
    | [] => some []
    | first :: rest => do
        let firstResult ← proof? language table context hypotheses first
        let remaining ← children? language table context hypotheses rest
        pure (firstResult :: remaining)
  termination_by children => sizeOf children
end

mutual
  /-- Installation changes the substitution algorithm, not acceptance. -/
  theorem proof?_agrees {language : LanguageDef} {judgments : List String} {rules : List Rule}
      (formed : ∀ rule ∈ rules, rule.WellFormed language judgments)
      (context : List TypeExpr) (hypotheses : List Pattern) (proof : RawOpenProof) :
      proof? language (install rules) context hypotheses proof =
        SortedFirstOrderRules.proof? language rules context hypotheses proof := by
    cases proof with
    | premise index => simp only [proof?, SortedFirstOrderRules.proof?]
    | node invocation children =>
        simp only [proof?, SortedFirstOrderRules.proof?, lookup_install]
        cases found : lookupRule? rules invocation.ruleId.value with
        | none => simp
        | some rule =>
            have wellFormed := formed rule (lookupRule?_member found).1
            simp only [Option.map_some, bind, Option.bind,
              children?_agrees formed context hypotheses children]
            by_cases valid : invocation.arguments.length = rule.row.vars.length ∧
                checkArgumentTypes language context invocation.arguments rule.variableTypes = true
            · rw [if_pos valid]
              cases result : SortedFirstOrderRules.children? language rules context hypotheses children with
              | none => rfl
              | some premises =>
                  simp [apply_compiled wellFormed, valid]
            · rw [if_neg valid]
              cases result : SortedFirstOrderRules.children? language rules context hypotheses children with
              | none => rfl
              | some premises =>
                  simp [apply_compiled wellFormed, valid]
  termination_by sizeOf proof

  theorem children?_agrees {language : LanguageDef} {judgments : List String} {rules : List Rule}
      (formed : ∀ rule ∈ rules, rule.WellFormed language judgments)
      (context : List TypeExpr) (hypotheses : List Pattern) (children : List RawOpenProof) :
      children? language (install rules) context hypotheses children =
        SortedFirstOrderRules.children? language rules context hypotheses children := by
    cases children with
    | nil => simp only [children?, SortedFirstOrderRules.children?]
    | cons first rest =>
        simp only [children?, SortedFirstOrderRules.children?,
          proof?_agrees formed context hypotheses first,
          children?_agrees formed context hypotheses rest]
  termination_by sizeOf children
end

theorem check_exact {language : LanguageDef} {judgments : List String} {rules : List Rule}
    (formed : ∀ rule ∈ rules, rule.WellFormed language judgments)
    (context : List TypeExpr) (hypotheses : List Pattern) (proof : RawOpenProof) (claim : Pattern) :
    proof? language (install rules) context hypotheses proof = some claim ↔
      Checks language rules context hypotheses proof claim := by
  rw [proof?_agrees formed, proof?_eq_some_iff]

/-- Every derivation in a well-formed, uniquely named calculus has a prepared
certificate; every accepted certificate proves that same source derivation. -/
theorem exists_certificate_iff {language : LanguageDef} {judgments : List String} {rules : List Rule}
    (formed : ∀ rule ∈ rules, rule.WellFormed language judgments)
    (distinct : (rules.map fun rule => rule.row.id).Nodup)
    (context : List TypeExpr) (hypotheses : List Pattern) (claim : Pattern) :
    (∃ proof, proof? language (install rules) context hypotheses proof = some claim) ↔
      Derives language rules context hypotheses claim := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact ((check_exact formed context hypotheses proof claim).mp accepted).derives
  · intro derived
    obtain ⟨proof, checked⟩ := derived.certificate_exists distinct
    exact ⟨proof, (check_exact formed context hypotheses proof claim).mpr checked⟩

namespace Controls

open PreparedSchematicInference.Controls

def scopedApplication : RawOpenProof :=
  .node ⟨⟨"application"⟩, [.bvar 0, a, A, B]⟩ [.premise 0, .premise 1]

theorem scoped_application_accepted :
    proof? language (install [application]) [.base "term"]
      [hasType (.bvar 0) (arrow A B), hasType a A] scopedApplication =
        some (hasType (.apply "app" [.bvar 0, a]) B) := by
  simpa [proof?, children?, lookup?, install, scopedApplication, application] using scoped_application

theorem changed_premise_refused :
    proof? language (install [application]) [.base "term"]
      [hasType (.bvar 0) (arrow A B), hasType a B] scopedApplication = none := by
  simpa [proof?, children?, lookup?, install, scopedApplication, application] using inconsistent_domain_refused

theorem missing_premise_refused :
    proof? language (install [application]) [.base "term"]
      [hasType (.bvar 0) (arrow A B)] scopedApplication = none := by
  simp [proof?, children?, lookup?, install, scopedApplication, application]

end Controls

#print axioms proof?_agrees
#print axioms check_exact
#print axioms exists_certificate_iff
#print axioms Controls.scoped_application_accepted
#print axioms Controls.changed_premise_refused

end Mettapedia.GSLT.LanguageDef.PreparedSchematicCertificates
