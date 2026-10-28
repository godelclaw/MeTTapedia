import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProgram
import Mettapedia.Languages.Datalog.ProgramGrounding
import Mathlib.Data.List.Forall2

/-! Native declaration positions read back through the source clause table.
The two lookup helpers have no source-clause identity. Declarations and I/O
directives retain their original statement positions in every compiled row. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Program

open Mettapedia.Languages.Datalog

def sourceOrdinal? (program : Mettapedia.Languages.Datalog.Program) (declarationIndex : Nat) : Option Nat :=
  if declarationIndex < baseLanguage.rewrites.length then none
  else ((LPBridge.numberedClauses program)[declarationIndex - baseLanguage.rewrites.length]?).map Prod.fst

theorem helper_has_no_source_ordinal (program : Mettapedia.Languages.Datalog.Program) (index : Nat)
    (helper : index < baseLanguage.rewrites.length) : sourceOrdinal? program index = none := by
  simp [sourceOrdinal?,helper]

/-- The native rule index identifies an actual source clause, its successful
compilation, and its unchanged location in the emitted language definition. -/
theorem compiled_origin_at (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (prepared : Prepared) (success : prepare? program known = some prepared)
    (index : Nat) (inside : index < prepared.rules.length) :
    ∃ statementIndex clause,
      ProgramGrounding.ClauseAt program statementIndex clause ∧
      compileClause? prepared.vocabulary statementIndex clause = some prepared.rules[index] ∧
      (language prepared.rules).rewrites[baseLanguage.rewrites.length + index]? = some prepared.rules[index] ∧
      sourceOrdinal? program (baseLanguage.rewrites.length + index) = some statementIndex := by
  have rows := (prepare?_sound program known prepared success).2.2.2
  have bound : index < (LPBridge.numberedClauses program).length := by
    rw [rows.length_eq]
    exact inside
  let source := (LPBridge.numberedClauses program)[index]
  have member : source ∈ LPBridge.numberedClauses program := List.getElem_mem bound
  refine ⟨source.1,source.2,(ProgramGrounding.clauseAt_iff_numbered _ _ _).mpr member,?_,?_,?_⟩
  · exact rows.get bound inside
  · change (baseLanguage.rewrites ++ prepared.rules)[baseLanguage.rewrites.length + index]? = _
    rw [List.getElem?_append_right (by omega)]
    simp [inside]
  · have later : ¬baseLanguage.rewrites.length + index < baseLanguage.rewrites.length := by omega
    simp [sourceOrdinal?,later,bound,source]

#print axioms helper_has_no_source_ordinal
#print axioms compiled_origin_at

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Program
