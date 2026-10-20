import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# `.module` controls

Upstream MeTTaIL's two frozen example files, `UnivAlg.module` and `Rholang.module`, are read
unchanged and elaborated:

- the free ring has one carrier and two monoid structures on it, the additive one shared by the
  abelian group and the commutative monoid: 14 equations, none duplicated;
- an abelian group's laws use the replaced names: `x + (-x) = 0`;
- the rho calculus takes parallel composition from the commutative monoid with its carrier
  renamed to `Proc`: the monoid's associativity and unit become the declared algebra of the bag
  constructor `PPar` (flattening, with unit `PZero`, a name written `(Zero)` before the
  replacement), and leave the equations together with commutativity, which the bag quotients out;
- a monoid replaced by a list constructor declares flattening with its unit, since both unit laws
  hold;
- both languages pass the core predicate;
- both modules print as `.module` text that reads back to the same data.

Negative controls: passing one monoid as both arguments of `Rig` (the mistake upstream's file
warns about) is a join collision; an argument that is not an instance of its parameter's theory,
a replacement of a missing constructor and an unknown theory are refused; replacing a monoid's
operation by a bag would add commutativity, and a commutative monoid's by a set would add
idempotence, so both are refused.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleSource (Error)

#module_file "../../../../artifacts/upstream-authoring-20261008/UnivAlg.module"
#module_file "../../../../artifacts/upstream-authoring-20261008/Rholang.module"

#module_roundtrip UnivAlg
#module_roundtrip Rholang

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.Controls

def labels (result : Except Error LanguageDef) : List String :=
  match result with
  | .ok language => language.terms.map fun rule => rule.label
  | .error _ => []

def sorts (result : Except Error LanguageDef) : List String :=
  match result with
  | .ok language => language.types.map fun sort => sort.name
  | .error _ => []

def counts (result : Except Error LanguageDef) : Nat × Nat :=
  match result with
  | .ok language => (language.equations.length, language.rewrites.length)
  | .error _ => (0, 0)

def equationNamed (result : Except Error LanguageDef) (wanted : String) : Option (Pattern × Pattern) :=
  match result with
  | .ok language => (language.equations.find? fun row => row.name == wanted).map fun row => (row.left, row.right)
  | .error _ => none

def algebraOf (result : Except Error LanguageDef) (label : String) : Option CollectionAlgebra :=
  match result with
  | .ok language => (language.terms.find? fun rule => rule.label == label).bind (·.algebra?)
  | .error _ => none

def isCore (result : Except Error LanguageDef) : Bool :=
  match result with
  | .ok language => match language.toCore with
    | .ok _ => true
    | .error _ => false
  | .error _ => false

#guard sorts UnivAlg.language == ["Elem"]
#guard labels UnivAlg.language == ["Zero", "Plus", "One", "Mult", "Neg"]
#guard counts UnivAlg.language == (14, 0)
#guard equationNamed UnivAlg.language "Group:equation:0@5" ==
  some (Pattern.apply "Plus" [Pattern.fvar "x", Pattern.apply "Neg" [Pattern.fvar "x"]], Pattern.apply "Zero" [])
#guard isCore UnivAlg.language

#guard sorts Rholang.language == ["Proc", "Name"]
#guard labels Rholang.language == ["PZero", "PPar", "PDrop", "NQuote", "PRepl", "PNew", "POutput", "PInput"]
#guard counts Rholang.language == (3, 4)
#guard algebraOf Rholang.language "PPar" == some { flatten := true, unit := some "PZero" }
#guard (match Rholang.language with
  | .ok language => language.equations.map (·.name)
  | .error _ => []) == ["QuoteDropCalc:equation:0@5", "NewReplCalc:equation:0@6", "NewReplCalc:equation:1@6"]
#guard isCore Rholang.language

#module
  import "UnivAlg.module" as u
  Module ListOfMonoid {
    Theory Words(m: u.Monoid) {
      m Replacements { Mult => Word . xs:Vec(Elem) |- "[" xs.*sep(",") "]" : Elem; }
    }
    theory Words(u.Monoid(u.EmptySet()))
  }

#guard algebraOf ListOfMonoid.language "Word" == some { flatten := true, unit := some "One" }
#guard counts ListOfMonoid.language == (0, 0)

#module
  import "UnivAlg.module" as u
  Module BagOfMonoid {
    Theory Wrong(m: u.Monoid) {
      m Replacements { Mult => Bag . xs:HashBag(Elem) |- "{" xs.*sep(",") "}" : Elem; }
    }
    theory Wrong(u.Monoid(u.EmptySet()))
  }

#guard match BagOfMonoid.language with
  | .error (.replaceAddsLaws "Mult" "Bag" "commutativity") => true
  | _ => false

#module
  import "UnivAlg.module" as u
  Module SetOfCommutativeMonoid {
    Theory Wrong(c: u.CommutativeMonoid) {
      c Replacements { Plus => Set . xs:HashSet(Elem) |- "{" xs.*sep(",") "}" : Elem; }
    }
    theory Wrong(u.CommutativeMonoid(u.Monoid(u.EmptySet())))
  }

#guard match SetOfCommutativeMonoid.language with
  | .error (.replaceAddsLaws "Plus" "Set" "idempotence") => true
  | _ => false

#module
  import "UnivAlg.module" as u
  Module SharedMistake {
    Theory OneMonoidTwice() {
      let s = u.EmptySet() in (
      let m = u.Monoid(s) in (
      let cm = u.CommutativeMonoid(m) in (
      u.Rig(cm, m)
      )))
    }
    theory OneMonoidTwice()
  }

#guard match SharedMistake.language with
  | .error (.collision _) => true
  | _ => false

#module
  import "UnivAlg.module" as u
  Module NotAnInstance {
    Theory Wrong() { u.CommutativeMonoid(u.EmptySet()) }
    theory Wrong()
  }

#guard match NotAnInstance.language with
  | .error (.notInstance _ _ _) => true
  | _ => false

#module
  import "UnivAlg.module" as u
  Module MissingConstructor {
    Theory Wrong(m: u.Monoid) {
      m Replacements { Times => Star . x:Elem, y:Elem |- x "*" y : Elem; }
    }
    theory Wrong(u.Monoid(u.EmptySet()))
  }

#guard match MissingConstructor.language with
  | .error (.replaceMissing "Times") => true
  | _ => false

Module UnknownTheory {
  Theory Wrong() { Nowhere() }
  theory Wrong()
}

#guard match UnknownTheory.language with
  | .error (.unknownTheory ["Nowhere"]) => true
  | _ => false

end Mettapedia.GSLT.LanguageDef.ModuleSource.Controls
