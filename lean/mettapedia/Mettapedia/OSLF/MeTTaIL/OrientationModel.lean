import Mettapedia.OSLF.MeTTaIL.OrientationSettle
import Mettapedia.OSLF.MeTTaIL.DistributiveLaws

/-!
# The combined normal form of oriented processes

The canonical form of an oriented process settles its action nodes, writes its data and decorations in
the normal form of `G ∗ F(V)`, and then takes the distributive normal form (`combinedNormal`). The order
matters: data must be in normal form before the distributive form sorts and removes repetitions, since
the lexicographic order reads data syntax.

The oriented model relates processes by the distributive moves, by equality of data in `G ∗ F(V)`
(terms with one frame normal form), and by evaluating action nodes. The combined normal form is
invariant under the last two on well-formed terms:
- `combinedNormal_frameNormal`: terms of one frame normal form have one combined normal form, since settling
  sees through the frame normal form;
- `combinedNormal_settle`: a term and its settled form have one combined normal form, since settling is
  idempotent.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax

section Combined

variable (language : LanguageDef) (decl : OrientationDecl) (distributive : Distributive.Decl)
variable {G : Type} [Group G] [DecidableEq G]

/-- **The combined normal form**: settled, data and decorations in normal form, then the distributive
normal form. -/
def combinedNormal (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  Distributive.normal distributive (frameNormal language decl reading type (settle language decl type pattern))

variable {language decl distributive} {reading : DataReading decl G}

/-- What the combined normal form asks of a term: its action nodes sit at the body sort, every action
coefficient is a closed word, and its data and decorations are words. -/
structure WellFormed (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Prop where
  placed : actionsAtBody language decl type pattern = true
  closed : closedActions language decl reading type pattern = true
  words : WordsAt (language := language) reading 0 type pattern

/-- **Terms of one frame normal form have one combined normal form.** -/
theorem combinedNormal_frameNormal (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType]) {type : TypeExpr}
    {first second : Pattern} (firstWell : WellFormed (language := language) reading type first)
    (secondWell : WellFormed (language := language) reading type second)
    (same : frameNormal language decl reading type first = frameNormal language decl reading type second) :
    combinedNormal language decl distributive reading type first =
      combinedNormal language decl distributive reading type second := by
  have bodySort := bodySort_of_dataSorted dataSorted
  have firstSees := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort 0 type first
    firstWell.placed firstWell.closed firstWell.words
  have secondSees := normalWalk_settle_normal multiplyNe bodyNotData dataSorted bodySort 0 type second
    secondWell.placed secondWell.closed secondWell.words
  unfold normalWalkAt at firstSees secondSees
  unfold combinedNormal frameNormal
  rw [← firstSees, ← secondSees]
  unfold frameNormal at same
  rw [same]

/-- **A term and its settled form have one combined normal form.** -/
theorem combinedNormal_settle (multiplyNe : decl.multiply ≠ decl.action)
    (bodyNotData : actionType language decl ≠ some (.base decl.dataSort)) {bodyType : TypeExpr}
    (dataSorted : paramTypes language decl.action = some [.base decl.dataSort, bodyType]) {type : TypeExpr}
    {pattern : Pattern} (well : WellFormed (language := language) reading type pattern) :
    combinedNormal language decl distributive reading type (settle language decl type pattern) =
      combinedNormal language decl distributive reading type pattern := by
  unfold combinedNormal
  rw [settle_settle multiplyNe bodyNotData dataSorted 0 type pattern well.placed well.words]

end Combined

end Mettapedia.OSLF.MeTTaIL.Orientation
