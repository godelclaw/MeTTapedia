import Mettapedia.Logic.Prolog.ReaderSource
import Mettapedia.Logic.LP.RuntimeMaterializeSoundness

/-!
# Dynamic clause decoding on the canonical Prolog representation

`asserta/1` and `assertz/1` receive an already-materialized heap term.  This
module performs the certified-local part of that boundary: finite readback,
capture-free rebasing of live runtime variables into one source-clause
namespace, and classification by the same `ReaderSource.classify` function
used for textual Prolog clauses.

It does not select or execute a clause and it has no database authority.  A
later runtime-session transition may consume the resulting canonical
`SourceSignature.Clause`; there is no second parser, goal decoder, or resolver.
-/

namespace Mettapedia.Logic.Prolog.RuntimeClauseDecode

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open SourceSignature

abbrev Sigma := SourceSignature.signature

/-- Failures before a dynamic clause can enter the persistent database.
These are kept precise here; the source runtime later maps them to the
corresponding ISO exception packets rather than collapsing them to failure. -/
inductive Error where
  | readback (error : LP.RuntimeReadback.ReadbackError)
  | source (error : ReaderSource.Error)
  | notClause
deriving DecidableEq, Repr

/-- Runtime identities in structural argument order. -/
def termVariables : (term : LP.Term Sigma.scoped) →
    List (LP.ScopedVar SourceSignature.Variable)
  | .var identity => [identity]
  | .const _ => []
  | .app _ arguments =>
      (List.ofFn fun index => termVariables (arguments index)).flatten
termination_by term => term.size
decreasing_by
  exact LP.Term.size_subterm _

/-- The distinct live identities of one asserted term.  This complete finite
support is the sole domain used by the rebasing map. -/
def variableSupport (term : LP.Term Sigma.scoped) :
    List (LP.ScopedVar SourceSignature.Variable) :=
  (termVariables term).eraseDups

/-- Copy one runtime identity into the asserted clause's private source
namespace.  `idxOf` preserves sharing and, over `variableSupport`, separates
distinct live identities even when their source spellings coincide. -/
def copiedVariable
    (support : List (LP.ScopedVar SourceSignature.Variable))
    (identity : LP.ScopedVar SourceSignature.Variable) :
    SourceSignature.Variable := {
  spelling := identity.name.spelling
  occurrence := support.idxOf identity
}

/-- Support members receive in-range private occurrence identities. -/
theorem copiedVariable_occurrence_lt
    (support : List (LP.ScopedVar SourceSignature.Variable))
    {identity : LP.ScopedVar SourceSignature.Variable}
    (hIdentity : identity ∈ support) :
    (copiedVariable support identity).occurrence < support.length := by
  exact List.idxOf_lt_length_of_mem hIdentity

/-- Rebasing is injective on the complete term support: two distinct runtime
identities cannot collapse merely because their spellings or activation-local
names coincide. -/
theorem copiedVariable_eq_iff
    (support : List (LP.ScopedVar SourceSignature.Variable))
    {identity other : LP.ScopedVar SourceSignature.Variable}
    (hIdentity : identity ∈ support) :
    copiedVariable support identity = copiedVariable support other ↔
      identity = other := by
  constructor
  · intro hEqual
    apply (List.idxOf_inj hIdentity).mp
    exact congrArg SourceSignature.Variable.occurrence hEqual
  · intro hEqual
    exact congrArg (copiedVariable support) hEqual

/-- Remove runtime activation scopes from a finite asserted term by one
capture-free, support-indexed renaming.  The result is again the canonical
`Logic.LP.Term` used by the source reader and clause runtime. -/
def rebaseTerm (term : LP.Term Sigma.scoped) : SourceSignature.Term :=
  term.renameVars (copiedVariable (variableSupport term))

/-- Classify one already-read finite term as a canonical dynamic clause.
Directives, queries, and DCG forms are not database clauses. -/
def classifyClause (term : LP.Term Sigma.scoped) :
    Except Error SourceSignature.Clause :=
  match ReaderSource.classify (rebaseTerm term) with
  | .error error => .error (.source error)
  | .ok (.clause clause) => .ok clause
  | .ok _ => .error .notClause

/-- Read and decode one heap root.  Rational terms are rejected explicitly by
the shared finite-readback boundary; no truncation or cyclic unfolding occurs.
-/
def decodeClause (heap : Heap Sigma.scoped) (root : Addr) :
    Except Error SourceSignature.Clause :=
  match LP.RuntimeReadback.Heap.readTerm heap root with
  | .error error => .error (.readback error)
  | .ok term => classifyClause term

/-- Materialization followed by dynamic decoding uses the exact term returned
by the canonical heap round-trip.  This pins the decoder to the shared
materializer rather than a compatible hand-built heap model. -/
theorem decodeClause_of_materialize
    {memory : Memory Sigma.scoped} {term : LP.Term Sigma.scoped}
    {result : MaterializedTerm Sigma.scoped}
    {clause : SourceSignature.Clause}
    (hMaterialize : materializeTerm memory term = .ok result)
    (hClassify : classifyClause term = .ok clause) :
    decodeClause result.memory.heap result.root = .ok clause := by
  have hRead :=
    (LP.RuntimeUnificationSoundness.materializeTerm_roundtrip
      hMaterialize).2.1
  simp [decodeClause, hRead, hClassify]

end Mettapedia.Logic.Prolog.RuntimeClauseDecode
