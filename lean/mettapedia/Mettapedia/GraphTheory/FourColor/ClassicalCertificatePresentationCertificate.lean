import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationPattern

/-!
# Certificate syntax for finite unavoidability presentations

This file fixes the concrete leaf and command types shared by the seven
finite presentation certificates.  Reducibility and hubcap leaves remain
syntactic until a semantic backend verifies their local computation.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationCertificate

open ClassicalCertificatePresentationLogic
open ClassicalCertificatePresentationPattern

/-- One discharging bound in a hubcap.  Sector indices are zero based. -/
structure HubcapTerm where
  first : Nat
  second : Option Nat
  bound : Int
deriving DecidableEq, Repr

/-- The two computational terminal forms of a presentation. -/
inductive LeafCode where
  | reducible
  | hubcap (terms : List HubcapTerm)
deriving DecidableEq, Repr

/-- Concrete syntax tree checked by the generic reflection kernel. -/
abbrev Code := PresentationCode Pattern LeafCode Pattern.SplitCode
  Pattern.SimilarityCode

private def emptyObserve : Empty → HubProfile := by
  intro hub
  exact hub.elim

private def emptySymmetry :
    Pattern.ObservedSymmetry (fun _ : Empty => False) emptyObserve where
  mirrorHub hub := hub
  rotateHub _ hub := hub
  valid_mirror := by intro hub hvalid; exact hvalid
  valid_rotate := by intro _ hub hvalid; exact hvalid
  fits_mirror := by intro hub; exact hub.elim
  fits_rotate := by intro _ hub; exact hub.elim

/-- Backend used solely to validate split and similarity structure.  Empty
semantic hubs make terminal soundness vacuous, while every nonterminal still
runs the same reflected checks as the eventual geometric backend. -/
def structuralBackend :
    Backend Empty Pattern LeafCode Pattern.SplitCode Pattern.SimilarityCode :=
  Pattern.backend (fun _ => False) emptyObserve emptySymmetry
    (fun _leaf _pattern => true) (by
      intro leaf pattern _hcheck hub hvalid
      exact False.elim hvalid)

/-- Validate all scoped splits and similarities in a concrete presentation. -/
def structureCheck (arity : Nat) (code : Code) : Bool :=
  check structuralBackend [] (Pattern.free arity) (Pattern.free arity) code

end ClassicalCertificatePresentationCertificate

end Mettapedia.GraphTheory.FourColor
