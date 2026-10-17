import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# Upstream MeTTaIL's ambient calculus, as authored

`language` is upstream's `languages/src/ambient.rs` declaration, rule for rule, in the
`languageDef!` notation, with one correction: moving a name `N` under a restriction
`new x` needs `x # N`, while upstream writes `x # P` on the restricted body, which confines
`InNew`, `OutNew`, `OpenNew` and `AmbNew` to vacuous restrictions. In the core, binding is by
index, so the corrected side condition reduces to no premise at all. `upstreamLiteral` keeps
upstream's text for conformance runs against upstream's own outputs.

Controls:

- every rule and equation reduces and passes the core predicate;
- `NewComm` swaps the occurrence arguments of its body, following the binder names;
- `ScopeExtrusion`'s `x # ...rest` is absorbed: the rest does not depend on `x`;
- `InNew`'s `x # N` is absorbed: `N` sits outside the binder, so it cannot use `x`;
- in `upstreamLiteral`, `InNew`'s `x # P` excludes `x` from `P`'s dependencies;
- `NewCong`'s premise is a step under one `Name` binder;
- negative: a body that names a binder outside its scope is refused.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Upstream.Ambient

open Mettapedia.OSLF.MeTTaIL Syntax

open LanguageDefDSL in
/-- Upstream's declaration. -/
def language : LanguageDef :=
  languageDef! {
    name : "Ambient"
    types {
      Proc
      Name
    }
    terms {
      PZero . |- "0" : Proc;
      PIn . n:Name, p:Proc |- "in(" n "," p ")" : Proc;
      POut . n:Name, p:Proc |- "out(" n "," p ")" : Proc;
      POpen . n:Name, p:Proc |- "open(" n "," p ")" : Proc;
      PAmb . n:Name, p:Proc |- n "[" p "]" : Proc;
      PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
      PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
    }
    equations {
      NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
      ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
      InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
      OutNew . | x # N |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P));
      OpenNew . | x # N |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
      AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
    }
    rewrites {
      InRule . |- (PPar {(PAmb N (PPar {(PIn M P), ...rest1})), (PAmb M R), ...rest2})
        ~> (PPar {(PAmb M (PPar {(PAmb N (PPar {P, ...rest1})), R})), ...rest2});
      OutRule . |- (PAmb M (PPar {(PAmb N (PPar {(POut M P), ...rest1})), R, ...rest2}))
        ~> (PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M R), ...rest2});
      OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest});
      ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
      NewCong . | S ~> T |- (PNew ^x.S) ~> (PNew ^x.T);
      AmbCong . | S ~> T |- (PAmb N S) ~> (PAmb N T);
    }
  }

/-- The reduced rules and equations, or the declaration itself if it had no core. -/
def reduced : LanguageDef :=
  match language.toCore with
  | .ok core => core.language
  | .error _ => language

#guard language.toCore.toOption.isSome
#guard CoreReduction.isCore reduced

-- `NewComm`: the body's arguments follow the binder names across the swap.
#guard (reduced.equations[0]?.bind (·.bindings)).map (·.occurrences.map (·.arguments)) ==
  some [[.bvar 0, .bvar 1], [.bvar 1, .bvar 0]]

-- `ScopeExtrusion`: the bound-name freshness is absorbed, and the rest has no dependency.
#guard (reduced.equations[1]?).map (·.premises.length) == some 0
#guard (reduced.equations[1]?.bind (·.bindings)).bind
    (fun spec => spec.dependencies.find? (·.1 == "rest")) ==
  some ("rest", [])

-- `InNew`: `x # N` is absorbed, and `P` keeps its dependency on `x`.
#guard (reduced.equations[2]?).map (·.premises.length) == some 0
#guard (reduced.equations[2]?.bind (·.bindings)).bind
    (fun spec => spec.dependencies.find? (·.1 == "P")) ==
  some ("P", [.base "Name"])

/-- Upstream's literal declaration, with `x # P` in the four restriction equations. -/
def upstreamLiteral : LanguageDef :=
  { language with «equations» := language.equations.map fun equation =>
      if ["InNew", "OutNew", "OpenNew", "AmbNew"].contains equation.name then
        { equation with «premises» := [.freshness ⟨"x", .fvar "P"⟩] }
      else equation }

-- In the literal text, `InNew`'s `x # P` excludes `x` from `P`.
#guard ((upstreamLiteral.toCore.toOption.map (·.language)).bind (·.equations[2]?) |>.bind (·.bindings)).bind
    (fun spec => spec.dependencies.find? (·.1 == "P")) ==
  some ("P", [])

-- `NewCong`: a step under one `Name` binder.
#guard (reduced.rewrites[4]?).map (·.premises) ==
  some [.scopedStep ⟨[.base "Name"], .base "Proc", .fvar "S", .fvar "T"⟩]

open LanguageDefDSL in
/-- Negative control: `x` is used outside the binder that names it. -/
def escaping : LanguageDef :=
  languageDef! {
    name : "Escaping"
    types {
      Proc
      Name
    }
    terms {
      PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
      PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
    }
    equations {
    }
    rewrites {
      Escape . |- (PPar {(PNew ^x.P), ...rest}) ~> (PPar {P, ...rest});
    }
  }

#guard match escaping.toCore with
  | .error (.outOfScope "Escape" "P" "x") => true
  | _ => false

end Mettapedia.OSLF.MeTTaIL.Upstream.Ambient
