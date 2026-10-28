import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProgramOrigins

/-! Source positions for the snapshot compiler. Its rule table contains only
compiled source clauses, so declaration indices have no lookup-helper offset. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem preparation (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) :
    ∃ core : Join.Program.Prepared, ∃ encoded : List Pattern,
      Join.Program.prepare? program seeds = some core ∧
      seeds.mapM (fact? core.vocabulary) = some encoded ∧
      prepared = ⟨program,core.vocabulary,
        Query.language (core.rules.map (Query.lowerRule core.vocabulary)),
        encoded.eraseDups,comparisonRows program core.vocabulary⟩ := by
  cases base : Join.Program.prepare? program seeds with
  | none => simp [prepare,base] at accepted
  | some core =>
    cases diagnostic : scalarDiagnostic? program core.vocabulary with
    | some reason => simp [prepare,base,diagnostic] at accepted
    | none =>
      cases encoded : seeds.mapM (fact? core.vocabulary) with
      | none => simp [prepare,base,diagnostic,encoded] at accepted
      | some values =>
        refine ⟨core,values,rfl,encoded,?_⟩
        simp only [prepare,base,diagnostic,encoded] at accepted
        change Except.ok (ε := String)
            (Prepared.mk program core.vocabulary
              (Query.language (core.rules.map (Query.lowerRule core.vocabulary)))
              values.eraseDups (comparisonRows program core.vocabulary)) = .ok prepared at accepted
        exact (Except.ok.inj accepted).symm

theorem prepare_typed (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) :
    prepared.source = program ∧ ProgramStatic.ProgramTyped program ∧
      seeds.all (StaticTyping.checkFact (ProgramStatic.signature program)) = true := by
  obtain ⟨core,encoded,base,_,same⟩ := preparation program seeds prepared accepted
  subst prepared
  have sound := Join.Program.prepare?_sound program seeds core base
  exact ⟨rfl,sound.1,sound.2.1⟩

theorem prepare_vocabulary (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) :
    prepared.vocabulary = Join.Program.pools program seeds := by
  obtain ⟨core,encoded,base,_,same⟩ := preparation program seeds prepared accepted
  subst prepared
  exact (Join.Program.prepare?_sound program seeds core base).2.2.1

theorem prepare_staticRows (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) :
    prepared.staticRows = comparisonRows program prepared.vocabulary := by
  obtain ⟨core,encoded,_,_,same⟩ := preparation program seeds prepared accepted
  subst prepared
  rfl

theorem compiled_origin_at (program : Program) (seeds : List GroundFact) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared)
    (index : Nat) (inside : index < prepared.compiled.rewrites.length) :
    ∃ statementIndex clause,
      ProgramGrounding.ClauseAt program statementIndex clause ∧
      Query.compileClause? prepared.vocabulary statementIndex clause =
        some prepared.compiled.rewrites[index] ∧
      (LPBridge.numberedClauses program)[index]? = some (statementIndex,clause) := by
  obtain ⟨core,encoded,base,_,same⟩ := preparation program seeds prepared accepted
  subst prepared
  have rows := (Join.Program.prepare?_sound program seeds core base).2.2.2
  have inRules : index < core.rules.length := by simpa [Query.language] using inside
  have inSource : index < (LPBridge.numberedClauses program).length := by
    rw [rows.length_eq]
    exact inRules
  let entry := (LPBridge.numberedClauses program)[index]
  have source := (ProgramGrounding.clauseAt_iff_numbered program entry.1 entry.2).mpr
    (List.getElem_mem inSource)
  refine ⟨entry.1,entry.2,source,?_,?_⟩
  · have compiled := rows.get inSource inRules
    simpa [Query.compileClause?,Query.language,compiled,entry] using
      congrArg (Option.map (Query.lowerRule core.vocabulary)) compiled
  · simp [inSource,entry]

#print axioms prepare_typed
#print axioms prepare_vocabulary
#print axioms prepare_staticRows
#print axioms compiled_origin_at

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable
