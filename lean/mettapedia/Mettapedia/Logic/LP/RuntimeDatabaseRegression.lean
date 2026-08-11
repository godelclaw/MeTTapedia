import Mettapedia.Logic.LP.RuntimeDatabase

/-!
# Executable logical-update database canaries

These examples discriminate source order, snapshot isolation, stable clause
references, and persistent generation advance.  They exercise the canonical
runtime's database component directly; query-state integration is a separate
next step and is not claimed here.
-/

namespace Mettapedia.Logic.LP.RuntimeDatabaseRegression

open RuntimeDatabase

def initial : RuntimeDatabase.Database String :=
  RuntimeDatabase.Database.ofProgram ["a", "b"]
def afterAsserta : RuntimeDatabase.Database String :=
  (RuntimeDatabase.Database.asserta initial "front").2
def afterAssertz : RuntimeDatabase.Database String :=
  (RuntimeDatabase.Database.assertz afterAsserta "back").2

def oldSnapshotSurvivesAssertions : Bool :=
  afterAssertz.visibleClausesAt initial.generation ==
    initial.visibleClausesAt initial.generation

def newSnapshotHasExactOrder : Bool :=
  afterAssertz.visibleClauses ==
    [(2, "front"), (0, "a"), (1, "b"), (3, "back")]

def erasedDatabase? : Option (RuntimeDatabase.Database String) := do
  let (_, database) ← RuntimeDatabase.Database.eraseRef afterAssertz 0
  pure database

def retractionPreservesOldSnapshot : Bool :=
  match erasedDatabase? with
  | none => false
  | some database =>
      database.visibleClausesAt afterAssertz.generation ==
        afterAssertz.visibleClausesAt afterAssertz.generation

def retractionHidesOnlyTargetAtNewSnapshot : Bool :=
  match erasedDatabase? with
  | none => false
  | some database =>
      database.visibleClauses ==
        [(2, "front"), (1, "b"), (3, "back")]

def failedRetractionIsPure : Bool :=
  match RuntimeDatabase.Database.eraseRef afterAssertz 999 with
  | none => true
  | some _ => false

#guard initial.snapshot.generation == 0
#guard initial.snapshot.clauses == [(0, "a"), (1, "b")]
#guard oldSnapshotSurvivesAssertions
#guard newSnapshotHasExactOrder
#guard retractionPreservesOldSnapshot
#guard retractionHidesOnlyTargetAtNewSnapshot
#guard failedRetractionIsPure

end Mettapedia.Logic.LP.RuntimeDatabaseRegression
