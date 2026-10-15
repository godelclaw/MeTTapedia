import Mettapedia.OSLF.NativeTypes.Generation.NativeHeaderFormation
import Mettapedia.OSLF.NativeTypes.Generation.NativeEquality
import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking

/-!
# Executable authored native declaration installation

One decoder installs every constructor declaration in its original order.
Installation retains the exact source snapshot and its decoding equation.
The dependent grammar and certificate checker consume the resulting finite
signature directly. Formation trees are generated, not supplied by a language
adapter. Operational modalities and their admission are joined separately.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent

structure Installation (language : LanguageDef) where
  headers : List (Header language)
  decoded : decodeHeaders? language = some headers

def install? (language : LanguageDef) : Option (Installation language) :=
  match decoded : decodeHeaders? language with
  | none => none
  | some headers => some ⟨headers, decoded⟩

theorem install?_complete {language : LanguageDef}
    (formed : ∀ origin, AdmittedHeader language origin) :
    ∃ installed, install? language = some installed := by
  obtain ⟨headers, decoded⟩ := decodeHeaders?_complete formed
  unfold install?
  split
  · rename_i rejected
    rw [decoded] at rejected
    cases rejected
  · exact ⟨_, rfl⟩

namespace Installation

variable {language : LanguageDef}

abbrev symbols (installed : Installation language) := NativeSignature.symbols language installed.headers

abbrev signature (installed : Installation language) :=
  NativeSignature.signature language installed.headers

def formation (installed : Installation language) : Refinement.HeaderFormation installed.signature :=
  headerFormation language installed.headers

theorem constructor_count (installed : Installation language) :
    installed.headers.length = language.terms.length := decodeHeaders?_length installed.decoded

theorem constructor_correspondence (installed : Installation language) :
    List.Forall₂ (fun origin header => header.origin = origin ∧ HeaderCorrect header)
      (List.finRange language.terms.length) installed.headers :=
  decodeHeaders?_correct installed.decoded

abbrev Constructor (installed : Installation language) := Fin installed.headers.length

def origin (installed : Installation language) (constructor : installed.Constructor) :
    Fin language.terms.length := installed.headers[constructor].origin

def parameters (installed : Installation language) (constructor : installed.Constructor) :
    List (Carrier language) := installed.headers[constructor].parameters

def result (installed : Installation language) (constructor : installed.Constructor) :
    Carrier language := .sort installed.headers[constructor].result

def parameterTypes (installed : Installation language) (constructor : installed.Constructor)
    (n : Nat) : List (Refinement.TypeExpr installed.symbols n) :=
  (installed.parameters constructor).map Carrier.native

def inputPredicateType (installed : Installation language) (carrier : Carrier language)
    (n : Nat) : Refinement.TypeExpr installed.symbols n :=
  .pi carrier.native .propositions

/-- A constructor graph is native logical equality with the declared
constructor operation. Its argument vector keeps the authored order. -/
def graph (installed : Installation language) (constructor : installed.Constructor) {n : Nat}
    (arguments : Fin (installed.parameters constructor).length → Refinement.TermExpr installed.symbols n)
    (target : Refinement.TermExpr installed.symbols n) : Refinement.PropExpr installed.symbols n :=
  NativeEquality.equal (installed.result constructor).native target
    (.primitive constructor arguments)

theorem graph_rename (installed : Installation language) (constructor : installed.Constructor)
    {n m : Nat} (mapping : Refinement.Renaming n m)
    (arguments : Fin (installed.parameters constructor).length → Refinement.TermExpr installed.symbols n)
    (target : Refinement.TermExpr installed.symbols n) :
    (installed.graph constructor arguments target).rename mapping =
      installed.graph constructor (fun position => (arguments position).rename mapping)
        (target.rename mapping) := by
  simp only [graph, NativeEquality.equal_rename, Carrier.native_rename,
    Refinement.TermExpr.rename]
  rfl

theorem graph_substitute (installed : Installation language) (constructor : installed.Constructor)
    {n m : Nat} (substitution : Refinement.Substitution installed.symbols n m)
    (arguments : Fin (installed.parameters constructor).length → Refinement.TermExpr installed.symbols n)
    (target : Refinement.TermExpr installed.symbols n) :
    (installed.graph constructor arguments target).substitute substitution =
      installed.graph constructor (fun position => (arguments position).substitute substitution)
        (target.substitute substitution) := by
  simp only [graph, NativeEquality.equal_substitute, Carrier.native_substitute,
    Refinement.TermExpr.substitute]
  rfl

def check (installed : Installation language)
    (certificate : Mettapedia.OSLF.NativeTypes.Certificates.Refinement.Certificate installed.signature)
    (judgment : Refinement.Judgment installed.symbols) : Bool :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check certificate judgment

theorem check_exact (installed : Installation language)
    (certificate : Mettapedia.OSLF.NativeTypes.Certificates.Refinement.Certificate installed.signature)
    (judgment : Refinement.Judgment installed.symbols) :
    installed.check certificate judgment = true ↔
      ∃ derivation : Refinement.Derivation installed.signature judgment,
        Mettapedia.OSLF.NativeTypes.Certificates.Refinement.erase derivation = certificate :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check_exact certificate judgment

def parameterCertificate (installed : Installation language) (constructor : installed.Constructor) :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.erase (installed.formation.termHeader constructor)

theorem parameterCertificate_checked (installed : Installation language)
    (constructor : installed.Constructor) :
    installed.check (installed.parameterCertificate constructor)
      (.context (installed.signature.termParameters constructor)) = true :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check_erase _

def resultCertificate (installed : Installation language) (constructor : installed.Constructor) :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.erase (installed.formation.termResult constructor)

theorem resultCertificate_checked (installed : Installation language)
    (constructor : installed.Constructor) :
    installed.check (installed.resultCertificate constructor)
      (.type (installed.signature.termParameters constructor)
        (installed.signature.termResult constructor)) = true :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check_erase _

end Installation

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature
