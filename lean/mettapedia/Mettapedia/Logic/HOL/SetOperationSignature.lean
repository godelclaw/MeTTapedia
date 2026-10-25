import Mettapedia.Logic.HOL.Syntax.Term

/-!
# A common higher-order signature for material set operations

One object sort carries membership, empty set, union, powerset, separation
and replacement. The predicate and mapping types are simple HOL arrows.
The vocabulary fixes no membership axioms or foundation principle; concrete
set and hyperset interpretations supply their own laws.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
abbrev set : Ty Unit := .base ()
abbrev predicate : Ty Unit := set ⇒ .prop
abbrev mapping : Ty Unit := set ⇒ set

/-- Typed mathematical constants; logical connectives remain HOL syntax. -/
inductive Symbol : Ty Unit → Type where
  | member : Symbol (set ⇒ set ⇒ .prop)
  | empty : Symbol set
  | union : Symbol mapping
  | power : Symbol mapping
  | separate : Symbol (set ⇒ predicate ⇒ set)
  | replace : Symbol (set ⇒ mapping ⇒ set)

instance {type : Ty Unit} : DecidableEq (Symbol type) := fun first second => by
  cases first <;> cases second <;>
    first | exact isTrue rfl | exact isFalse (by intro same; cases same)

end Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
