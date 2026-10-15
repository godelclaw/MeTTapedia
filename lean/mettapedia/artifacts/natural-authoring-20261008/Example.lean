import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation.EnglishAuthoring

def carrier := englishTheory! Theory Carrier {
  Declare the sort Elem.
  Export the sort Elem.
}

def operations := englishTheory! Theory Operations {
  Declare One returning Elem with notation "1".
  Declare Mult taking x:Elem, y:Elem returning Elem
    with notation "(" x "*" y ")".
  Assert that (Mult (Mult x y) z) equals (Mult x (Mult y z)).
  Assert that (Mult x (One)) equals x.
  Assert that (Mult (One) x) equals x.
}

def monoid := assemble "Monoid" [carrier, operations]

example : (admit? monoid).isSome = true := by cbv

def binding := englishTheory! Theory Scope {
  Declare the sort Proc.
  Declare the sort Name.
  Declare Input taking n:Name, ^x.p:[Name -> Proc] returning Proc
    with notation n "?" x "." "{" p "}".
  Rewrite Unseal : (Input n ^x.p) to (subst ^x.p n).
}

example : binding.rewrites.length = 1 := rfl
