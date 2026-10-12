import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.OSLF.Framework.GrammarDerives
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.Languages.MM0Lite.LanguageDef
import Mettapedia.Languages.MM0.Presentation.Calculus

/-!
# Upstream quotation and full-language assembly controls

The carrier quotation is the current upstream `EmptySet` body. The monoid and
rho operator fragments use current upstream rows while leaving their inherited
base to explicit assembly. HE and MM0 syntax checks compare independently
authored quotations with existing source declarations. Whole-language split
and reconstruction controls do not create parallel specifications.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open UpstreamTheoryQuotation

def carrier : QuotedTheory := moduleTheory! Theory EmptySet() {
  Types { Elem; }
  Exports { Elem; }
}

def monoidOperations : QuotedTheory := moduleTheory! Theory MonoidOperations() {
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

def monoid : QuotedTheory := assemble "Monoid" [carrier, monoidOperations]


#eval monoid.validate
#eval (admit? monoid).isSome
#reduce monoid.validate
end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls
