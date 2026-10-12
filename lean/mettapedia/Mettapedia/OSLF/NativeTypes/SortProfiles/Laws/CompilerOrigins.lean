import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerSemantics

open Mettapedia.OSLF.Framework

/-!
# Complete original origins of compiled display laws

The compiler's equation and directed-rule streams retain their different
source kinds and original declaration positions. An empty diagnostics list
earns coverage of every declaration, rather than only the successfully
encoded endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

def equationLaw (equation : Mettapedia.OSLF.MeTTaIL.Syntax.Equation) (index : Nat) : Law :=
  ⟨.equation, index, equation.name, equation.typeContext, equation.premises,
    equation.bindings, equation.left, equation.right⟩

def rewriteLaw (rule : RewriteRule) (index : Nat) : Law :=
  ⟨.rewrite, index, rule.name, rule.typeContext, rule.premises,
    rule.bindings, rule.left, rule.right⟩

theorem equation_law_origin (language : LanguageDef) (law : Law) :
    law ∈ equationLaws language ↔
      ∃ equation index, (equation, index) ∈ language.equations.zipIdx ∧
        equationLaw equation index = law := by
  simp only [equationLaws, List.mem_map]
  constructor
  · rintro ⟨⟨equation, index⟩, declared, same⟩
    exact ⟨equation, index, declared, same⟩
  · rintro ⟨equation, index, declared, same⟩
    exact ⟨(equation, index), declared, same⟩

theorem rewrite_law_origin (language : LanguageDef) (law : Law) :
    law ∈ rewriteLaws language ↔
      ∃ rule index, (rule, index) ∈ language.rewrites.zipIdx ∧
        rewriteLaw rule index = law := by
  simp only [rewriteLaws, List.mem_map]
  constructor
  · rintro ⟨⟨rule, index⟩, declared, same⟩
    exact ⟨rule, index, declared, same⟩
  · rintro ⟨rule, index, declared, same⟩
    exact ⟨(rule, index), declared, same⟩

theorem compiled_original_equation_coverage (language : LanguageDef)
    (complete : (equations language).diagnostics = [])
    (equation : Mettapedia.OSLF.MeTTaIL.Syntax.Equation) (index : Nat)
    (declared : (equation, index) ∈ language.equations.zipIdx) :
    ∃ encoded, encodeLaw language (equationLaw equation index) = some encoded ∧
      encoded ∈ (equations language).system.equations := by
  have lawMember := (equation_law_origin _ _).mpr ⟨equation, index, declared, rfl⟩
  obtain ⟨encoded, encodedLaw⟩ := encodeLaw_exists_of_no_diagnostics _ _
    (complete_laws _ _ complete _ lawMember)
  exact ⟨encoded, encodedLaw,
    (compiled_equation_member _ _ _).mpr ⟨_, lawMember, encodedLaw⟩⟩

theorem compiled_original_rewrite_coverage (language : LanguageDef)
    (complete : (rewrites language).diagnostics = [])
    (rule : RewriteRule) (index : Nat)
    (declared : (rule, index) ∈ language.rewrites.zipIdx) :
    ∃ encoded, encodeLaw language (rewriteLaw rule index) = some encoded ∧
      encoded ∈ (rewrites language).system.equations := by
  have lawMember := (rewrite_law_origin _ _).mpr ⟨rule, index, declared, rfl⟩
  obtain ⟨encoded, encodedLaw⟩ := encodeLaw_exists_of_no_diagnostics _ _
    (complete_laws _ _ complete _ lawMember)
  exact ⟨encoded, encodedLaw,
    (compiled_equation_member _ _ _).mpr ⟨_, lawMember, encodedLaw⟩⟩

theorem equation_source_check_exact (language : LanguageDef)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    (equations language).check? vertex = some true ↔
      (equations language).diagnostics = [] ∧
        ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
          SourceLawHolds language (equationLaw equation index) vertex := by
  change (compileLaws language (equationLaws language)).check? vertex = some true ↔ _
  rw [compiled_check_exact_source]
  constructor
  · rintro ⟨complete, holds⟩
    exact ⟨complete, fun equation index declared =>
      holds _ ((equation_law_origin _ _).mpr ⟨equation, index, declared, rfl⟩)⟩
  · rintro ⟨complete, holds⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨equation, index, declared, rfl⟩ := (equation_law_origin _ _).mp member
    exact holds equation index declared

theorem rewrite_source_check_exact (language : LanguageDef)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    (rewrites language).check? vertex = some true ↔
      (rewrites language).diagnostics = [] ∧
        ∀ rule index, (rule, index) ∈ language.rewrites.zipIdx →
          SourceLawHolds language (rewriteLaw rule index) vertex := by
  change (compileLaws language (rewriteLaws language)).check? vertex = some true ↔ _
  rw [compiled_check_exact_source]
  constructor
  · rintro ⟨complete, holds⟩
    exact ⟨complete, fun rule index declared =>
      holds _ ((rewrite_law_origin _ _).mpr ⟨rule, index, declared, rfl⟩)⟩
  · rintro ⟨complete, holds⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨rule, index, declared, rfl⟩ := (rewrite_law_origin _ _).mp member
    exact holds rule index declared

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
