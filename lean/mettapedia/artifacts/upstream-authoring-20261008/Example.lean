import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

def carrier := moduleTheory! Theory Carrier() {
  Types { Elem; }
  Exports { Elem; }
}

def operations := moduleTheory! Theory Operations() {
  Terms {
    One  . |- "1" : Elem;
    Mult . x:Elem, y:Elem |- "(" x "*" y ")" : Elem;
  }
  Equations {
    (Mult (Mult x y) z) == (Mult x (Mult y z));
    (Mult x (One)) == x;
    (Mult (One) x) == x;
  }
}

def monoid := assemble "Monoid" [carrier, operations]

example : (admit? monoid).isSome = true := by cbv
