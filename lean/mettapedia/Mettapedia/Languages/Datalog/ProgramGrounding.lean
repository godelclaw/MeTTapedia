import Mettapedia.Languages.Datalog.LPBridge
import Mettapedia.Languages.Datalog.GroundInstancesComplete

/-! Whole-program grounding uses the existing ordered LP clause extraction.
Its source judgment instead names original statement positions directly.
Declarations and I/O directives neither become rules nor renumber later rules. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.ProgramGrounding

open GroundInstances

def ClauseAt (program : Program) (statementIndex : Nat) (clause : Clause) : Prop :=
  program.statements[statementIndex]? = some (.rule clause) ∨
    ∃ fact, program.statements[statementIndex]? = some (.fact fact) ∧
      clause = LPBridge.groundClause fact

theorem clauseAt_iff_numbered (program : Program) (statementIndex : Nat) (clause : Clause) :
    ClauseAt program statementIndex clause ↔
      (statementIndex, clause) ∈ LPBridge.numberedClauses program := by
  constructor
  · intro source
    rcases source with rule | ⟨fact, factAt, rfl⟩
    · exact List.mem_filterMap.mpr ⟨(.rule clause, statementIndex),
        List.mk_mem_zipIdx_iff_getElem?.mpr rule, rfl⟩
    · exact List.mem_filterMap.mpr ⟨(.fact fact, statementIndex),
        List.mk_mem_zipIdx_iff_getElem?.mpr factAt, rfl⟩
  · intro member
    obtain ⟨⟨statement, position⟩, indexed, selected⟩ := List.mem_filterMap.mp member
    have source := List.mk_mem_zipIdx_iff_getElem?.mp indexed
    cases statement with
    | declaration _ => cases selected
    | input _ => cases selected
    | output _ => cases selected
    | rule actual =>
      have same : (position, actual) = (statementIndex, clause) := Option.some.inj selected
      cases same
      exact Or.inl source
    | fact fact =>
      have same : (position, LPBridge.groundClause fact) = (statementIndex, clause) :=
        Option.some.inj selected
      cases same
      exact Or.inr ⟨fact, source, rfl⟩

def produce (policy : Comparisons.Policy) (program : Program) (known : List GroundFact) : List Instance :=
  (LPBridge.numberedClauses program).flatMap fun (statementIndex, clause) =>
    GroundInstances.produce policy statementIndex clause known

def SourceAuthorized (policy : Comparisons.Policy) (program : Program)
    (known : List GroundFact) (instanceData : Instance) : Prop :=
  ∃ clause, ClauseAt program instanceData.key.statementIndex clause ∧
    Authorized policy instanceData.key.statementIndex clause known instanceData

theorem produce_sound (policy : Comparisons.Policy) (program : Program) (known : List GroundFact)
    {instanceData : Instance} (member : instanceData ∈ produce policy program known) :
    SourceAuthorized policy program known instanceData := by
  obtain ⟨⟨statementIndex, clause⟩, selected, emitted⟩ := List.mem_flatMap.mp member
  have authorized := (GroundInstances.produce_sound policy statementIndex clause known emitted).1
  have ordinal : instanceData.key.statementIndex = statementIndex := authorized.2.1
  refine ⟨clause, ?_, ?_⟩
  · rw [ordinal]
    exact (clauseAt_iff_numbered program statementIndex clause).mpr selected
  · simpa only [ordinal] using authorized

/-- Coverage retains the source rule position and complete logical key; the
actual join supplies its own snapshot-relative validation positions. -/
theorem produce_complete (policy : Comparisons.Policy) (program : Program) (known : List GroundFact)
    (wanted : Instance) (authorized : SourceAuthorized policy program known wanted) :
    ∃ emitted ∈ produce policy program known,
      emitted.key = wanted.key ∧ emitted.conclusion = wanted.conclusion := by
  obtain ⟨clause, source, valid⟩ := authorized
  obtain ⟨emitted, produced, keySame, conclusionSame⟩ :=
    GroundInstances.produce_complete policy wanted.key.statementIndex clause known wanted valid
  exact ⟨emitted, List.mem_flatMap.mpr ⟨(wanted.key.statementIndex, clause),
    (clauseAt_iff_numbered program wanted.key.statementIndex clause).mp source, produced⟩,
    keySame, conclusionSame⟩

#print axioms clauseAt_iff_numbered
#print axioms produce_sound
#print axioms produce_complete

end Mettapedia.Languages.Datalog.ProgramGrounding
