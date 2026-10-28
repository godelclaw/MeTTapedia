import Mettapedia.Languages.MeTTa.PLeaTTa.Builtins
import Mettapedia.Languages.MeTTa.PLeaTTa.Machine

namespace Mettapedia.Languages.MeTTa.PLeaTTa

private def sreadSemicolonExpected : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  chainify (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr
    [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "shell", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "a;b"]])

-- Runtime `sread` follows PeTTa's token grammar rather than the source-file
-- reader: semicolons are token content, and exactly one complete form must be
-- consumed.
#guard sreadC [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.str "((shell a;b))")] ==
  .ok [sreadSemicolonExpected]
#guard sreadC [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.str "((send ok)) ((rest))")] ==
  .runtimeError "((send ok)) ((rest))"
#guard sreadC [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.str "\"unterminated")] ==
  .runtimeError "\"unterminated"

-- PeTTa's Prolog clause constructs `[Head|Tail]` for every tail, including
-- improper lists.  Proper and improper tails therefore share the same
-- constant-time constructor path; only arity is rejected.
#guard consAtomC [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "head", nilA] ==
  .ok [consC (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "head") nilA]
#guard consAtomC [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "head", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "tail"] ==
  .ok [consC (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "head") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "tail")]
#guard consAtomC [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "head"] ==
  .incorrectArgument "cons-atom"

private def aliasSeed : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst :=
  [("outer", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "inner")]

-- A later binding for a fresh clause variable must reach the outer variable
-- that was previously aliased to it. This is the substitution shape created
-- by relational calls nested in rule-head patterns.
#guard
  match unifyB aliasSeed (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "inner") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "value") with
  | some b => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup b "outer" == some (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "value")
  | none => false

#guard unifyB aliasSeed (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "same") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "same") ==
  some aliasSeed

#guard (unifyB aliasSeed (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "left") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "right")).isNone

-- Pinned PeTTa delegates clause-head unification to SWI-Prolog: integer and
-- float terms remain distinct even when they have the same numeric value.
-- The broader Hyperon matcher may still use numeric equivalence elsewhere.
#guard (unifyB [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.int 1))
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.float 1.0))).isNone
#guard unifyB [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.int 1)) (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.int 1)) == some []
#guard unifyB [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.float 1.0))
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.float 1.0)) == some []
#guard (unifyB []
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [.sym "pair", .var "x", .var "x"])
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [.sym "pair", .gnd (.int 1), .gnd (.float 1.0)])).isNone

private def canonicalNaN₁ : Float :=
  Float.ofBits 0x7ff8000000000000

private def canonicalNaN₂ : Float :=
  Float.ofBits 0x7ff8000000000001

private def canonicalNegativeNaN : Float :=
  Float.ofBits 0xfff8000000000000

private def positiveZero : Float :=
  Float.ofBits 0x0000000000000000

private def negativeZero : Float :=
  Float.ofBits 0x8000000000000000

-- SWI has one NaN term regardless of IEEE payload/sign, but distinguishes
-- the two signed zero terms.  These executable guards pin the new canonical
-- identity used by the live local-clause resolver.
#guard PrologFloatIdentity.ofFloat canonicalNaN₁ == .nan
#guard PrologFloatIdentity.ofFloat canonicalNaN₂ == .nan
#guard PrologFloatIdentity.ofFloat canonicalNegativeNaN == .nan
#guard prologGroundIdentical (.float canonicalNaN₁) (.float canonicalNaN₂)
#guard prologGroundIdentical (.float canonicalNaN₁) (.float canonicalNegativeNaN)
#guard !prologGroundIdentical (.float positiveZero) (.float negativeZero)
#guard !prologGroundIdentical (.int 1) (.float 1.0)
#guard !(Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.float canonicalNaN₁) ==
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.float canonicalNaN₂))
#guard unifyB [] (.gnd (.float canonicalNaN₁))
  (.gnd (.float canonicalNaN₂)) == some []
#guard (unifyB [] (.gnd (.float positiveZero))
  (.gnd (.float negativeZero))).isNone

-- The exact comparator is consulted after every elimination round, not only
-- as a prefilter.  Binding the repeated variable exposes two distinct IEEE
-- NaN payloads; Prolog identity makes the remaining ground equation succeed.
#guard
  match unifyB []
      (.expr [.sym "pair", .var "x", .var "x"])
      (.expr [.sym "pair", .gnd (.float canonicalNaN₁),
        .gnd (.float canonicalNaN₂)]) with
  | some [("x", .gnd (.float value))] =>
      PrologFloatIdentity.ofFloat value == .nan
  | _ => false

-- PeTTa's `!=/3` now consumes that same term identity: distinct NaN payloads
-- are one Prolog term, while signed zeroes remain different terms.
#guard notEqualOp [.gnd (.float canonicalNaN₁), .gnd (.float canonicalNaN₂)] ==
  .ok [.sym "False"]
#guard notEqualOp
  [.gnd (.float canonicalNaN₁), .gnd (.float canonicalNegativeNaN)] ==
    .ok [.sym "False"]
#guard notEqualOp [.gnd (.float positiveZero), .gnd (.float negativeZero)] ==
  .ok [.sym "True"]

private def trimSeed : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst :=
  [("live", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "needed"),
   ("live", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "shadowed"),
   ("needed", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr
     [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "pair", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "leaf"]),
   ("leaf", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "live"),
   ("shadowed", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "wrong"),
   ("dead", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "unused")]

-- Trimming follows the first binding through a branching, cyclic transitive
-- dependency while removing a shadowed duplicate and unreachable bindings.
#guard trimFor [Goal.eq (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "live") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "result")]
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "query") trimSeed ==
  [("live", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "needed"),
   ("needed", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr
     [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "pair", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "leaf"]),
   ("leaf", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "live")]

-- Conservative clause indexing accepts a compatible variable-bearing head
-- and rejects only a structural clash that unification could not solve.
#guard matchCompat
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "pair", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x"])
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "pair", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "value"])

#guard !matchCompat
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "left", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "value"])
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "right", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "value"])

#guard matchCompat
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.int 1))
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.float 1.0))

#guard !matchCompat
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.int 1))
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.int 2))

private def indexedClause (tag : String) (params : List Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom) : Clause :=
  { params
    result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym tag
    body := [] }

private def clauseIndexZero : Clause := indexedClause "zero" []
private def clauseIndexUnary : Clause :=
  indexedClause "unary" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x"]
private def clauseIndexUnaryDuplicate : Clause :=
  indexedClause "unary-duplicate" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x"]
private def clauseIndexOther : Clause := indexedClause "other" []
private def clauseIndexAppended : Clause :=
  indexedClause "appended" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "y"]

private def clauseIndexFixture : List (String × Clause) :=
  [("f", clauseIndexZero), ("g", clauseIndexOther),
   ("f", clauseIndexUnary), ("f", clauseIndexUnaryDuplicate)]

private def clauseIndexBuilt : ClauseIndex :=
  ClauseIndex.build clauseIndexFixture

-- Buckets preserve canonical insertion order and discriminate arity without
-- losing repeated clauses from the same head.
#guard ClauseIndex.candidates clauseIndexBuilt "f" 0 == [clauseIndexZero]
#guard ClauseIndex.candidates clauseIndexBuilt "f" 1 ==
  [clauseIndexUnary, clauseIndexUnaryDuplicate]
#guard ClauseIndex.candidates clauseIndexBuilt "g" 0 == [clauseIndexOther]

-- Missing heads and wrong arities produce no candidates.
#guard (ClauseIndex.candidates clauseIndexBuilt "missing" 0).isEmpty
#guard (ClauseIndex.candidates clauseIndexBuilt "f" 2).isEmpty

-- Dynamic assertion appends within the selected bucket and leaves other
-- arities unchanged.
private def clauseIndexPushed : ClauseIndex :=
  ClauseIndex.push clauseIndexBuilt ("f", clauseIndexAppended)

#guard ClauseIndex.candidates clauseIndexPushed "f" 1 ==
  [clauseIndexUnary, clauseIndexUnaryDuplicate, clauseIndexAppended]
#guard ClauseIndex.candidates clauseIndexPushed "f" 0 == [clauseIndexZero]

private def indexedWorld : PWorld :=
  ({ progClauses := clauseIndexFixture } : PWorld).reindexClauses

#guard indexedWorld.clauseIndexReady
#guard indexedWorld.clauseHeadCandidates "f" ==
  [clauseIndexZero, clauseIndexUnary, clauseIndexUnaryDuplicate]
#guard indexedWorld.resolutionCandidates "f" 1 ==
  [clauseIndexUnary, clauseIndexUnaryDuplicate]
#guard (indexedWorld.resolutionCandidates "missing" 1).isEmpty

private def indexedWorldAppended : PWorld :=
  indexedWorld.appendProgClause ("f", clauseIndexAppended)

#guard indexedWorldAppended.clauseHeadCandidates "f" ==
  [clauseIndexZero, clauseIndexUnary, clauseIndexUnaryDuplicate,
   clauseIndexAppended]
#guard indexedWorldAppended.resolutionCandidates "f" 1 ==
  [clauseIndexUnary, clauseIndexUnaryDuplicate, clauseIndexAppended]

private def indexedWorldRemoved : PWorld :=
  indexedWorldAppended.replaceProgClauses
    [("g", clauseIndexOther), ("f", clauseIndexZero)]

#guard indexedWorldRemoved.clauseHeadCandidates "f" == [clauseIndexZero]
#guard (indexedWorldRemoved.resolutionCandidates "f" 1).isEmpty

private def getTypeExtensionClause : Clause :=
  { params := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "value"]
    result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "CustomType"
    body := [] }

private def getTypeExtensionWorld : PWorld :=
  PWorld.reindexClauses
    ({ progClauses := [("get-type", getTypeExtensionClause)] } : PWorld)

private def getTypeExtensionResult : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "type"

-- Pinned `get-type/2` has one built-in clause followed by source-asserted
-- extensions. An empty world contributes no extension choice; a locally
-- compiled unary clause contributes exactly one continuation after built-in
-- answers, retaining the current substitution.
#guard (localGetTypeExtensionAlts ({} : PWorld) (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.int 2))
  getTypeExtensionResult [] ([] : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst)).isEmpty

#guard match localGetTypeExtensionAlts getTypeExtensionWorld
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.int 2)) getTypeExtensionResult []
    ([] : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst) with
  | [Alt.br goals binding] =>
      goals == [Goal.call "get-type" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.int 2)]
        getTypeExtensionResult] && binding.isEmpty
  | _ => false

private def spaceOld : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "kind",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "old"]

private def spaceNew : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "kind",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "new"]

private def spaceOther : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "other", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "kind",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "old"]

private def exactSpaceAtomsNewest : List Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  [spaceNew, spaceOther, spaceOld, spaceOld]

private def exactSpaceIndex : SpaceIndex.State :=
  SpaceIndex.build exactSpaceAtomsNewest

-- Exact lookup preserves insertion order and duplicate multiplicity.
#guard SpaceIndex.candidates exactSpaceIndex exactSpaceAtomsNewest spaceOld ==
  [spaceOld, spaceOld]

-- Exact misses and outer-head misses produce no candidates.
#guard (SpaceIndex.candidates exactSpaceIndex exactSpaceAtomsNewest
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "kind",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "missing"])).isEmpty
#guard (SpaceIndex.candidates exactSpaceIndex exactSpaceAtomsNewest
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "missing", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "kind",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x"])).isEmpty

private def collisionOne : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "number",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.int 1)]

private def collisionTwo : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "number",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.int 2)]

private def collisionFloatOne : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "number",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.float 1.0)]

private def collisionAtomsNewest : List Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  [collisionTwo, collisionOne]

private def collisionIndex : SpaceIndex.State :=
  SpaceIndex.build collisionAtomsNewest

-- A coarse discriminator collision may add a candidate, but the unchanged
-- compatibility check removes it without reordering the true hit.
#guard SpaceIndex.candidates collisionIndex collisionAtomsNewest collisionFloatOne ==
  [collisionOne, collisionTwo]
#guard (SpaceIndex.candidates collisionIndex collisionAtomsNewest
  collisionFloatOne).filter (matchCompat collisionFloatOne) == [collisionOne]

private def wildcardStored : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "record", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "kind",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "wild"]

private def wildcardAtomsNewest : List Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  [collisionTwo, wildcardStored, collisionOne]

-- A stored wildcard disables unsafe pruning; query wildcards likewise retain
-- every canonical candidate.
#guard SpaceIndex.candidates (SpaceIndex.build wildcardAtomsNewest)
  wildcardAtomsNewest collisionOne == [collisionOne, wildcardStored]
#guard SpaceIndex.candidates collisionIndex collisionAtomsNewest
  (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "query") == collisionAtomsNewest.reverse

private def namedIndexSpace : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "&indexed"

private def spaceIndexedWorld : PWorld :=
  ({ selfAtoms := exactSpaceAtomsNewest
     spaceAtoms := [(namedIndexSpace, collisionAtomsNewest)] } : PWorld).reindexSpaces

#guard spaceIndexedWorld.spaceIndexReady
#guard spaceIndexedWorld.atomCandidates selfSpace spaceOld == [spaceOld, spaceOld]
#guard spaceIndexedWorld.atomCandidates namedIndexSpace collisionOne ==
  [collisionOne]

private def namedIndexAdded : PWorld :=
  spaceIndexedWorld.addAtom namedIndexSpace spaceOld

#guard namedIndexAdded.atomCandidates namedIndexSpace (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "all") ==
  [collisionOne, collisionTwo, spaceOld]

private def namedIndexRemoved : PWorld :=
  namedIndexAdded.removeAtom namedIndexSpace collisionOne

#guard namedIndexRemoved.atomCandidates namedIndexSpace (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "all") ==
  [collisionTwo, spaceOld]

private def smatchSnapshotWorld : PWorld :=
  ({ selfAtoms := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "second", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first",
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first"] } : PWorld).reindexSpaces

private def smatchSnapshot : List Alt × Nat :=
  smatchAlts smatchSnapshotWorld 7 [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x") []
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x")

private def smatchMatchedAtom : Alt → Option Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom
  | .br (Goal.eq _ atom :: _) _ => some atom
  | _ => none

-- Alternatives are a logical-update snapshot in canonical order.  Later
-- mutation changes the next match, not the already materialized branches.
#guard smatchSnapshot.1.filterMap smatchMatchedAtom ==
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "second"]
#guard smatchSnapshot.2 == 10

private def smatchAfterRemoval : List Alt × Nat :=
  smatchAlts
    (smatchSnapshotWorld.removeAtom selfSpace (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first"))
    7 [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x") [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x")

#guard smatchAfterRemoval.1.filterMap smatchMatchedAtom ==
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "second"]
#guard smatchSnapshot.1.filterMap smatchMatchedAtom ==
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "first", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "second"]

private def repeated (x y : String) : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "p", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var x, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var y]

#guard alphaEqOp [repeated "x" "x", repeated "y" "y"] ==
  .ok [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "True"]

#guard alphaEqOp [repeated "x" "x", repeated "y" "z"] ==
  .ok [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "False"]

-- PeTTa assertion succeeds only for a successful evaluated goal; failure is
-- an evaluation error rather than an inert `(assert False)` value.
#guard assertOp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "True"] == .ok [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "True"]
#guard assertOp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "False"] == .runtimeError "assertion failed"

#guard nonstrictOps.contains "=="

#guard testResultsOp [chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "answer"], Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "answer"] ==
  .ok [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "True"]

#guard testResultsOp
  [chainOf [chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "True"]], chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "true"]] ==
  .ok [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "True"]

#guard
  match testResultsOp [chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "actual"], Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "expected"] with
  | .runtimeError _ => true
  | _ => false

private def intAtom (n : Int) : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.int n)

private def floatAtom (n : Float) : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground.float n)

#guard floatUnC Float.sqrt [floatAtom (-1.0)] ==
  .runtimeError "undefined"
#guard floatUnC Float.sqrt [floatAtom 9.0] ==
  .ok [floatAtom 3.0]

-- PeTTa raises an arithmetic evaluation error at every numeric zero divisor;
-- it never creates IEEE infinity or NaN values from `/`.
#guard divOp [intAtom 1, intAtom 0] == .runtimeError "division by zero"
#guard divOp [floatAtom 1.0, floatAtom 0.0] ==
  .runtimeError "division by zero"
#guard divOp [floatAtom 0.0, floatAtom 0.0] ==
  .runtimeError "division by zero"
#guard divOp [floatAtom 6.0, floatAtom 2.0] == .ok [floatAtom 3.0]

private def zeroDivisorValue : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "Error",
    chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "evaluation_error", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "zero_divisor"],
    chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "context",
      chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "/", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "/", intAtom 2],
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "_errorContext"]]

private def errorRegressionProg : Prog :=
  { clauses := [], facts := [], typeDecls := [] }

private def uncaughtDivisionConf : Conf :=
  { cur := some
      ([Goal.bin "/" [floatAtom 1.0, floatAtom 0.0] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "bad"),
        Goal.bin "+" [intAtom 2, intAtom 3] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "later")], [])
    alts := []
    world := {}
    counter := 0
    qterm := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "later" }

private def caughtDivisionConf : Conf :=
  { cur := some
      ([Goal.catchg (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "caught")
        [Goal.bin "/" [floatAtom 1.0, floatAtom 0.0]
          (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "inner")]
        (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "caught")], [])
    alts := []
    world := {}
    counter := 0
    qterm := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "caught" }

-- An uncaught arithmetic error aborts before its sibling goal; the nearest
-- one-argument catch instead reifies the exact PeTTa error payload as a value.
#guard
  match runClean errorRegressionProg pleattaTable 20 uncaughtDivisionConf none with
  | .errored d err => d.answers.isEmpty && err == zeroDivisorValue
  | _ => false

#guard
  match runClean errorRegressionProg pleattaTable 20 caughtDivisionConf none with
  | .done d => d.answers == [zeroDivisorValue]
  | _ => false

private def foo (arg : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom) : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "foo", arg]

private def fooPair : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  foo (chainOf [intAtom 42, intAtom 42])

#guard msortC
  [chainOf [fooPair, foo (intAtom 42), foo (intAtom 2), foo (intAtom 1)]] ==
  .ok [chainOf [foo (intAtom 1), foo (intAtom 2), foo (intAtom 42), fooPair]]

private def capturedClause : Clause :=
  { params := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
    result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out"
    body := [Goal.callDyn (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g")
      [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")] }

private def capturedSource : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "=",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"],
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]]

private def capturedWorld : PWorld :=
  ({} : PWorld).captureMeta capturedSource capturedClause

-- Positive capture: a source rule and its generic IR are retained together.
#guard capturedWorld.metaClauses ==
  [{ parent := "f"
     sourceParams := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
     sourceBody := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr
       [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]
     compiled := capturedClause }]

-- Negative capture: ordinary atoms cannot enter the rule metadata registry.
#guard (({} : PWorld).captureMeta (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "ordinary")
  capturedClause).metaClauses.isEmpty

-- Retraction removes the corresponding captured clause as well as the live IR.
#guard (capturedWorld.removeCapturedMeta "f"
  (clauseAlphaKey capturedClause)).metaClauses.isEmpty

private def guardedCapturedClause : Clause :=
  { capturedClause with
      body := Goal.eq (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "fixed") ::
        capturedClause.body }

private def dualIdentityCapturedWorld : PWorld :=
  ({} : PWorld).captureMetaWithSourceKey capturedSource guardedCapturedClause
    (clauseAlphaKey capturedClause)

-- Generated metadata carries executable semantics and a distinct visible
-- source-removal key.  The source key removes it; the executable key does not.
#guard dualIdentityCapturedWorld.metaClauses.head?.map (·.compiled) ==
  some guardedCapturedClause
#guard (dualIdentityCapturedWorld.removeCapturedMeta "f"
  (clauseAlphaKey capturedClause)).metaClauses.isEmpty
#guard (dualIdentityCapturedWorld.removeCapturedMeta "f"
  (clauseAlphaKey guardedCapturedClause)).metaClauses.length == 1

#guard specializationName
  { parent := "f", bindings := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] } == "f_Spec_[g]"

#guard specializationName
  { parent := "map-flat"
    bindings := [partialC "+" (chainOf [intAtom 1])] } ==
      "map-flat_Spec_[partial(+,[1])]"

#guard specializationName
  { parent := "higher-order-fun"
    bindings :=
      [partialC "+" (chainOf [intAtom 1]),
       partialC "*" (chainOf [intAtom 1])] } ==
    "higher-order-fun_Spec_[partial(+,[1]),partial(*,[1])]"

private def directDiscovery : Option SpecCandidate :=
  discoverSpecialization (fun f => f == "g") (fun _ => false) "f"
    [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] capturedWorld.metaClauses

-- Positive discovery: a defined value bound to a dynamic-head variable
-- yields the structural key and clause-local substitution.
#guard directDiscovery.map (fun candidate =>
  (candidate.key, candidate.clauses.map (·.binding))) ==
    some ({ parent := "f", bindings := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] },
      [[("g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g")]])

private def repeatedResidualPartial (name : String) : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  partialC "cons"
    (chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var name, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var name])

private def freshRepeatedBinding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst :=
  freshenSpecializationBinding capturedClause
    [("g", repeatedResidualPartial "x")]

-- Positive residual-copy regression: both source occurrences share one fresh
-- clause-local variable, distinct from the source and every callee variable.
#guard match Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup freshRepeatedBinding "g" with
  | some value =>
      match value.vars with
      | [left, right] =>
          left == right && left != "x" &&
            !(specializationClauseVars capturedClause).contains left
      | _ => false
  | none => false

-- The copied pattern still matches the originating open call site as one
-- tuple, while a structurally different closure is rejected.
#guard specializationBindingSupported freshRepeatedBinding
  capturedClause.params [repeatedResidualPartial "x"]
#guard !specializationBindingSupported freshRepeatedBinding
  capturedClause.params [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "different"]

-- Negative discovery: an unknown symbol is data, so the generic path remains.
#guard (discoverSpecialization (fun _ => false) (fun _ => false) "f"
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "unknown"] capturedWorld.metaClauses).isNone

-- Positive and negative call-site support: a generated guard is justified
-- only by the same concrete value at an occurrence of its formal variable.
#guard specializationBindingSupported [("g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g")]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"] [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"]
#guard !specializationBindingSupported [("g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g")]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"] [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "h"]
#guard !specializationBindingSupported [("g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g")]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "other"] [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"]

-- The executable retargeting boundary accepts exact open alpha-copies but
-- rejects numeric-coercion-only support; those calls retain generic dispatch.
#guard specializationBindingExactlySupported freshRepeatedBinding
  capturedClause.params [repeatedResidualPartial "x"]
#guard specializationBindingExactlySupported [("n", intAtom 1)]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "n"] [intAtom 1]
#guard !specializationBindingExactlySupported [("n", intAtom 1)]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "n"] [floatAtom 1.0]

#guard specializationSourceBindingExact [("n", intAtom 1)]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "n"] [intAtom 1]
#guard !specializationSourceBindingExact [("n", intAtom 1)]
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "n"] [floatAtom 1.0]

-- A sibling clause with no generated guards is supported vacuously; its
-- ordinary resolution head remains responsible for arity/shape rejection.
#guard specializationBindingSupported []
  [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "unrelated"] []

private def identityClause : Clause :=
  { params := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x"]
    result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "x"
    body := [] }

private def specializerSeedWorld : PWorld :=
  { progClauses := [("g", identityClause), ("f", capturedClause)]
    knownHeads := ["g", "f"]
    knownArities := [("g", 1), ("f", 1)]
    metaClauses := capturedWorld.metaClauses
    typeDecls :=
      [(Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "Type1"]),
       (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "Type2"])] }

private def specializedOnce : PWorld × List Goal :=
  specializeGoals (fun _ => false) 100 specializerSeedWorld
    [Goal.call "f" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

#guard specializedOnce.1.specializationProvenanceValid

-- The real lifecycle installs one reusable direct-call clause, copies every
-- parent type in order, and rewrites the initiating call to its stable name.
#guard specializedOnce.2 ==
  [Goal.call "f_Spec_[g]" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

#guard specializedOnce.1.clausesOf "f_Spec_[g]" ==
  [{ params := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
     result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out"
     body := [Goal.eq (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"),
       Goal.call "g" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]
       (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")] }]

-- The proof-facing ledger is one-for-one with the installed clause and keeps
-- both the guarded base and the exact executable produced by recursive
-- rewriting.  It is never consulted by execution.
#guard specializedOnce.1.specClauseProvenance.length == 1
#guard specializedOnce.1.specClauseProvenance.head?.map
  (fun provenance => provenance.parent) == some "f"
#guard specializedOnce.1.specClauseProvenance.head?.map
  (fun provenance => provenance.executableClause) ==
    (specializedOnce.1.clausesOf "f_Spec_[g]").head?

#guard specializedOnce.1.typeDecls.drop 2 ==
  [(Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f_Spec_[g]", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "Type1"]),
   (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f_Spec_[g]", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "Type2"])]

private def secondCapturedClause : Clause :=
  { capturedClause with
      body := [Goal.callDyn (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g")
        [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input2"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")] }

private def secondCapturedSource : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "=",
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"],
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input2"]]

private def multiCapturedMeta : List MetaClause :=
  ((({} : PWorld).captureMeta capturedSource capturedClause).captureMeta
    secondCapturedSource secondCapturedClause).metaClauses

private def multiClauseWorld : PWorld :=
  { progClauses :=
      [("g", identityClause), ("f", capturedClause),
       ("f", secondCapturedClause)]
    knownHeads := ["g", "f"]
    knownArities := [("g", 1), ("f", 1)]
    metaClauses := multiCapturedMeta }

private def multiClauseSpecialized : PWorld × List Goal :=
  specializeGoals (fun _ => false) 100 multiClauseWorld
    [Goal.call "f" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

-- Executable clauses remain in source order, while generated discovery
-- metadata remains newest-first.  Both lists are complete.
#guard (multiClauseSpecialized.1.clausesOf "f_Spec_[g,g]").map (fun clause =>
  clause.body.drop 1) ==
    [[Goal.call "g" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")],
     [Goal.call "g" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input2"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]]
#guard (multiClauseSpecialized.1.metaClauses.filter (fun captured =>
  captured.parent == "f_Spec_[g,g]")).map (·.sourceBody) ==
    [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input2"],
     Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]]
#guard multiClauseSpecialized.1.specializationProvenanceValid

private def specializedTwice : PWorld × List Goal :=
  specializeGoals (fun _ => false) 100 specializedOnce.1
    [Goal.call "f" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "again")]

-- Stable reuse cannot duplicate clauses, copied types, or registry entries.
#guard specializedTwice.1.progClauses.length == specializedOnce.1.progClauses.length
#guard specializedTwice.1.typeDecls.length == specializedOnce.1.typeDecls.length
#guard specializedTwice.1.specializations.length == 1
#guard specializedTwice.1.specClauseProvenance.length == 1
#guard specializedTwice.2 ==
  [Goal.call "f_Spec_[g]" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "again")]

private def collisionWorld : PWorld :=
  { specializerSeedWorld with
      progClauses := specializerSeedWorld.progClauses ++
        [("f_Spec_[g]", identityClause)] }

private def collisionFallback : PWorld × List Goal :=
  specializeGoals (fun _ => false) 100 collisionWorld
    [Goal.call "f" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

-- A user/live clause already owning the public generated name forces the
-- generic fallback; specialization never merges unrelated clause families.
#guard collisionFallback.2 ==
  [Goal.call "f" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]
#guard collisionFallback.1.specClauseProvenance.isEmpty
#guard collisionFallback.1.specializationProvenanceValid

private def emptyRegisteredSpecialization : PWorld :=
  { specializations :=
      [{ key := { parent := "f", bindings := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] }
         name := "f_Spec_[g]" }] }

-- A registry row without an installed clause/provenance witness cannot make
-- recursive call-site validation hold vacuously.
#guard !emptyRegisteredSpecialization.specializationProvenanceValid
#guard !emptyRegisteredSpecialization.childCallSiteValid [] "f"
  "f_Spec_[g]" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"]

private def partialValueOne : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  partialC "+" (chainOf [intAtom 1])

private def partialSpecialized : PWorld × List Goal :=
  specializeGoals (fun name => name == "+") 100 specializerSeedWorld
    [Goal.call "f" [partialValueOne] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

-- Partial bindings use the native-compatible name and lower to the existing
-- builtin IR with bound arguments before newly supplied arguments.
#guard partialSpecialized.2 ==
  [Goal.call "f_Spec_[partial(+,[1])]" [partialValueOne]
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

#guard (partialSpecialized.1.clausesOf
  "f_Spec_[partial(+,[1])]").map (·.body) ==
    [[Goal.eq partialValueOne (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"),
      Goal.bin "+" [intAtom 1, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]
      (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]]

-- Open copied residuals flow toward the caller: the fresh clause variable is
-- bound to the caller variable, while the caller variable remains unbound.
private def openGuardBase : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst :=
  [("hof", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr
    [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "partial", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "caller"])]

#guard match unifyB openGuardBase
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "partial", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "fresh"])
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "hof") with
  | some result =>
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup result "fresh" == some (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "caller") &&
        (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup result "caller").isNone
  | none => false

-- Changing a bound callable does not invalidate a specialization whose
-- parent is `f`: native invalidation follows parent-to-generated-child edges,
-- not reverse call or binding-use edges.  The generated direct call observes
-- the callable's current definition when it eventually executes.
#guard partialSpecialized.1.specializationDescendants "+" == []
#guard (partialSpecialized.1.invalidateSpecializations "+").specializations ==
  partialSpecialized.1.specializations
#guard (partialSpecialized.1.invalidateSpecializations "+"
  ).specClauseProvenance == partialSpecialized.1.specClauseProvenance
#guard (partialSpecialized.1.invalidateSpecializations "+").progClauses ==
  partialSpecialized.1.progClauses
#guard (partialSpecialized.1.invalidateSpecializations "+").selfAtoms ==
  partialSpecialized.1.selfAtoms

private def nanPartialValue : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom :=
  partialC "+"
    (chainOf [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.gnd (.float (Float.ofBits 0x7ff8000000000000))])

#guard !specializationBindingRuntimeSafe [("g", nanPartialValue)]

private def nanPartialFallback : PWorld × List Goal :=
  specializeGoals (fun name => name == "+") 100 specializerSeedWorld
    [Goal.call "f" [nanPartialValue] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

-- Specialization still applies a deliberately conservative Hyperon-reflexive
-- admission gate even though the local resolver now handles NaN exactly.
-- Falling back keeps answers correct; removing this optimization-only
-- restriction is separate specialization work.
#guard proofGoalsEq nanPartialFallback.2
  [Goal.call "f" [nanPartialValue] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]
#guard nanPartialFallback.1.specializations.isEmpty

private def propagatedClause (callee : String) : Clause :=
  { params := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
    result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "r"
    body := [Goal.call callee [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "r")] }

private def propagatedMeta (parent callee : String) : MetaClause :=
  { parent
    sourceParams := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
    sourceBody := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym callee, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
    compiled := propagatedClause callee }

private def rollbackWorld : PWorld :=
  { progClauses :=
      [("g", identityClause),
       ("cycle1", propagatedClause "cycle2"),
       ("cycle2", propagatedClause "cycle1")]
    knownHeads := ["g", "cycle1", "cycle2"]
    metaClauses :=
      [propagatedMeta "cycle2" "cycle1",
       propagatedMeta "cycle1" "cycle2"] }

private def rolledBack : PWorld × List Goal :=
  specializeGoals (fun _ => false) 100 rollbackWorld
    [Goal.call "cycle1" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

-- Negative recursive case: a finite provisional cycle with no direct dynamic
-- gain rolls back atomically and leaves the generic call/world untouched.
#guard rolledBack.2 ==
  [Goal.call "cycle1" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]
#guard rolledBack.1.progClauses.length == rollbackWorld.progClauses.length
#guard rolledBack.1.specializations.isEmpty
#guard rolledBack.1.specClauseProvenance.isEmpty
#guard rolledBack.1.specializationProvenanceValid

private def capturedTwice : PWorld :=
  capturedWorld.captureMeta capturedSource capturedClause

-- Duplicate assertion/retract-one retains exactly one live-equivalent meta.
#guard (capturedTwice.removeCapturedMeta "f"
  (clauseAlphaKey capturedClause)).metaClauses.length == 1

private def invalidatedDirect : PWorld :=
  specializedOnce.1.invalidateSpecializations "f"

-- Direct invalidation removes every generated artifact but preserves both
-- ordinary functions and the parent's original declarations/metadata.
#guard specializedOnce.1.specializationDescendants "f" == ["f_Spec_[g]"]
#guard invalidatedDirect.specializations.isEmpty
#guard invalidatedDirect.specClauseProvenance.isEmpty
#guard invalidatedDirect.specializationProvenanceValid
#guard invalidatedDirect.progClauses.map (·.1) == ["g", "f"]
#guard invalidatedDirect.metaClauses.map (·.parent) == ["f"]
#guard invalidatedDirect.typeDecls == specializerSeedWorld.typeDecls
#guard (invalidatedDirect.atomsOf selfSpace).isEmpty

private def recursiveGainMeta : MetaClause :=
  { parent := "recursive2"
    sourceParams := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
    sourceBody := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr
      [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]
    compiled := capturedClause }

private def recursiveGainWorld : PWorld :=
  { progClauses :=
      [("g", identityClause),
       ("recursive1", propagatedClause "recursive2"),
       ("recursive2", capturedClause)]
    knownHeads := ["g", "recursive1", "recursive2"]
    metaClauses :=
      [recursiveGainMeta, propagatedMeta "recursive1" "recursive2"] }

private def recursiveCommitted : PWorld × List Goal :=
  specializeGoals (fun _ => false) 100 recursiveGainWorld
    [Goal.call "recursive1" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")]

#guard recursiveCommitted.1.specializations.map (·.name) ==
  ["recursive1_Spec_[g]", "recursive2_Spec_[g]"]

#guard recursiveCommitted.1.specClauseProvenance.map
  (fun provenance => (provenance.name, provenance.parent)) ==
    [("recursive2_Spec_[g]", "recursive2"),
     ("recursive1_Spec_[g]", "recursive1")]

#guard recursiveCommitted.1.specClauseProvenance.any (fun provenance =>
  provenance.name == "recursive1_Spec_[g]" &&
    provenance.guardedClause != provenance.executableClause)
#guard recursiveCommitted.1.specializationProvenanceValid

#guard (recursiveCommitted.1.clausesOf "recursive1_Spec_[g]").map (·.body) ==
  [[Goal.eq (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"),
    Goal.call "recursive2_Spec_[g]" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g"]
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "r")]]

private def incompatibleChildClause : Clause :=
  { capturedClause with
      body := [Goal.eq (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g") (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "h"),
        Goal.call "g" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"]
          (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")] }

private def incompatibleChildWorld : PWorld :=
  { recursiveCommitted.1 with
      progClauses := recursiveCommitted.1.progClauses.map (fun entry =>
        if entry.1 == "recursive2_Spec_[g]"
        then (entry.1, incompatibleChildClause)
        else entry)
      specClauseProvenance :=
        recursiveCommitted.1.specClauseProvenance.map (fun provenance =>
          if provenance.name == "recursive2_Spec_[g]" then
            { provenance with
                binding := [("g", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "h")]
                guardedClause := incompatibleChildClause
                executableClause := incompatibleChildClause }
          else provenance) }

-- Negative recursive provenance: registration and exact installed-clause
-- linkage alone are insufficient when the parent call supplies `g` but the
-- child guard requires `h`.
#guard !incompatibleChildWorld.specializationProvenanceValid

-- Invalidation follows the generated graph forward.  Changing the outer
-- parent removes its recursively generated child; changing the child removes
-- the child specialization without walking backward into its caller.
#guard (recursiveCommitted.1.invalidateSpecializations
  "recursive1").specializations.isEmpty
#guard (recursiveCommitted.1.invalidateSpecializations
  "recursive2").specializations.map (·.name) ==
    ["recursive1_Spec_[g]"]
#guard (recursiveCommitted.1.invalidateSpecializations
  "recursive1").progClauses.length == recursiveGainWorld.progClauses.length

-- A subsequent call rebuilds from the still-live ordinary metadata.
#guard (specializeGoals (fun _ => false) 100
  (recursiveCommitted.1.invalidateSpecializations "recursive1")
  [Goal.call "recursive1" [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "g"]
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "again")]).1.specializations.length == 2

private def alternateBodyClause : Clause :=
  { capturedClause with body :=
      [Goal.callDyn (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "g") [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "other-input"]
        (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "out")] }

-- Whole-clause α-keys distinguish same-head clauses by body, while remaining
-- insensitive to a consistent renaming of all clause-local variables.
#guard clauseAlphaKey capturedClause != clauseAlphaKey alternateBodyClause

private def alphaRenamedCapturedClause : Clause :=
  { params := [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "function"]
    result := Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "answer"
    body := [Goal.callDyn (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "function")
      [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "input"] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var "answer")] }

#guard clauseAlphaKey capturedClause == clauseAlphaKey alphaRenamedCapturedClause

-- Ordinary/type atom mutation does not invalidate function specializations.
#guard
  match wactRun specializedOnce.1 "add-atom"
      [chainify (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.expr [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym ":",
        Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "f", Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "NewType"])] with
  | some (_, next) => next.specializations.length == 1
  | none => false

private def compactCollisionName : String :=
  "this_variable_name_is_deliberately_long_enough_to_force_compact_resolution_suffix#r1000000"

private def compactCollisionSuffix : String :=
  resolutionFreshSuffix [] (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.sym "result") [] []
    (Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var compactCollisionName) 1000000

-- Positive collision regression: a source variable may deliberately end in
-- the allocator's current token.  `resolutionFreshSuffix` now emits the compact
-- seed suffix directly (no per-resolution occupied scan); collision-safety is
-- provided by the global counter, which the source seed and
-- `advanceCounterPastAtoms` keep strictly above every occupied token (checked
-- below), so the allocated suffix is exactly `#r<seed>`.
#guard compactCollisionName.length > 64
#guard terminalResolutionSeed? compactCollisionName == some 1000000
#guard compactCollisionSuffix == "#r1000000"
#guard "local" ++ compactCollisionSuffix != compactCollisionName
#guard advanceCounterPastAtoms 4 [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.var compactCollisionName] ==
  1000001
#guard resolutionSeedHighWaterNames [compactCollisionName] == 1000001

-- Negative scanner cases: only a terminal, decimal `#r<n>` token reserves
-- allocator space; a later token supersedes an earlier embedded token.
#guard terminalResolutionSeed? "x#r5tail" == none
#guard terminalResolutionSeed? "plain" == none
#guard terminalResolutionSeed? "x#r5#r7" == some 7

end Mettapedia.Languages.MeTTa.PLeaTTa
