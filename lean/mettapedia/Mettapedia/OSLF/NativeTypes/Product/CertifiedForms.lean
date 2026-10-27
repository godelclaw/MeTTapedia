import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegionControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls

/-!
# Certified canonical forms, by language

Canonical forms whose coherence is proved for one language (the π-calculus and the ambient calculus with their
flattening algebras, the ρ-calculus, the grids modulo `A = B` and `Wrap x = x`) are kept with that language. A
language read from a file gets them when it is that language: languages have decidable equality, and the forms are
carried along the equality (`certifiedFormsOf`). So the executable reads these languages modulo their equations, with
the forms their own theorems certify, and any other language as before.
-/

namespace Mettapedia.OSLF.MeTTaIL.Syntax

deriving instance DecidableEq for Equation
deriving instance DecidableEq for RewriteRule
deriving instance DecidableEq for LanguageDef

end Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic

/-- **A language with certified canonical forms**, at the premise fuels they are certified for. -/
structure Certified where
  name : String
  language : LanguageDef
  forms : (fuel : ℕ) → Option (CanonicalForms RelationEnv.empty language fuel)

/-- Forms certified at one premise fuel. -/
def atFuel {language : LanguageDef} (certifiedFuel : ℕ) (forms : CanonicalForms RelationEnv.empty language certifiedFuel)
    (fuel : ℕ) : Option (CanonicalForms RelationEnv.empty language fuel) :=
  if same : certifiedFuel = fuel then some (same ▸ forms) else none

/-- **The languages with certified canonical forms.** -/
def certified : List Certified :=
  [⟨"pi", Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piCalc, fun fuel => some (PiForms.forms fuel)⟩,
   ⟨"ambient", Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.ambientCalc,
     fun fuel => some (AmbientForms.forms fuel)⟩,
   ⟨"rho", rhoCalc, atFuel 1 Rho.Controls.canonicalForms⟩,
   ⟨"aliased", CanonicalRegionControls.aliased, atFuel 2 CanonicalRegionControls.aliasForms⟩,
   ⟨"wrapped", CanonicalUnwrapControls.wrapped, atFuel 2 CanonicalUnwrapControls.wrapForms⟩]

/-- **The certified canonical forms of a language**, when it is one of the certified languages. -/
def certifiedFormsOf (language : LanguageDef) (fuel : ℕ) : Option (CanonicalForms RelationEnv.empty language fuel) :=
  go certified
where
  go : List Certified → Option (CanonicalForms RelationEnv.empty language fuel)
    | [] => none
    | entry :: rest => if same : entry.language = language then same ▸ entry.forms fuel else go rest

end Mettapedia.OSLF.NativeTypes.Product
