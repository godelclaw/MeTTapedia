import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

/-!
# Kempe derivations at any arity, and their physical soundness

A *derivation* of a boundary word into a target set: either the word is in the
target, or for some colour pair every active noncrossing matching admits a
component-union switch whose result is again derivable.  This is the closure a
reducibility certificate certifies, at any ring length.

Physical soundness: on a cubic port tangle whose physical bichromatic mate is
noncrossing in the chosen boundary coordinates (planarity supplies this), a
derivable word in the exact support can be replaced, by literal Kempe
switches of the tangle's colourings, by a target word in the exact support
(`exists_mem_target_of_derivable`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation

open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTanglePhysicalKempeClosure GoertzelV24HexagonPairingTargetAwareBoundary

/-- Tait boundary words of arity `n` -/
abbrev Word (n : Nat) := Fin n → {color : Color // color ≠ 0}

/-- a port carries one of the pair's colours -/
def activeAt {n : Nat} (w : Word n) (pair : TaitColorPair) (i : Fin n) : Prop :=
  pairActiveColor pair (w i).1

/-- an involutive pairing of exactly the active ports -/
def IsActiveMatching {n : Nat} (w : Word n) (pair : TaitColorPair) (mate : Fin n → Fin n) : Prop :=
  ∀ i, (activeAt w pair i ↔ activeAt w pair (mate i)) ∧ mate (mate i) = i ∧
    (activeAt w pair i → mate i ≠ i) ∧ (¬ activeAt w pair i → mate i = i)

/-- a selected set is a union of matched pairs -/
def IsComponentUnion {n : Nat} (mate : Fin n → Fin n) (selected : Finset (Fin n)) : Prop :=
  ∀ i, i ∈ selected ↔ mate i ∈ selected

/-- **derivations**: a word is derivable into `target` if it is in `target`, or if for some
colour pair every active noncrossing matching has a component-union switch whose result is
derivable -/
inductive Derivable {n : Nat} (target : Set (Word n)) : Word n → Prop
  | base {w : Word n} : w ∈ target → Derivable target w
  | step {w : Word n} (pair : TaitColorPair)
      (sel : ∀ mate : Fin n → Fin n, IsActiveMatching w pair mate → IsNoncrossingMatching mate →
        Finset (Fin n))
      (hunion : ∀ mate ha hn, IsComponentUnion mate (sel mate ha hn))
      (hder : ∀ mate ha hn, Derivable target (switchBoundaryWord w pair (sel mate ha hn))) :
      Derivable target w

/-! ## Physical soundness -/

universe u

variable {V I P : Type u} [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]
variable {n : Nat} (order : Fin n ≃ P) (T : PortTangle V I P) (hcubic : IsCubic T)

theorem activeAt_iff (coloring : Coloring T) (hproper : IsProper coloring) (pair : TaitColorPair)
    (i : Fin n) :
    activeAt (properBoundaryWordInCoordinates order coloring hproper) pair i ↔
      pairActiveDart coloring pair (Sum.inr (order i)) := Iff.rfl

/-- the physical mate in coordinates is an active matching of the colouring's word -/
theorem physicalMateInCoordinates_isActiveMatching (coloring : Coloring T)
    (hproper : IsProper coloring) (pair : TaitColorPair) :
    IsActiveMatching (properBoundaryWordInCoordinates order coloring hproper) pair
      (physicalMateInCoordinates order T hcubic coloring hproper pair) := by
  intro i
  have hmate : order (physicalMateInCoordinates order T hcubic coloring hproper pair i) =
      physicalMate T hcubic coloring hproper pair (order i) := by
    simp [physicalMateInCoordinates]
  refine ⟨?_, physicalMateInCoordinates_involutive order T hcubic coloring hproper pair i, ?_, ?_⟩
  · rw [activeAt_iff, activeAt_iff, hmate]
    exact (physicalMate_active_iff T hcubic coloring hproper pair (order i)).symm
  · intro ha heq
    apply physicalMate_ne_of_active T hcubic coloring hproper pair (order i)
      ((activeAt_iff order T coloring hproper pair i).mp ha)
    rw [← hmate, heq]
  · intro hna
    apply order.injective
    rw [hmate]
    exact physicalMate_eq_self_of_inactive T hcubic coloring hproper pair (order i)
      (fun h => hna ((activeAt_iff order T coloring hproper pair i).mpr h))

/-- **physical soundness of derivations**: if the physical mate is noncrossing in the chosen
coordinates for every proper colouring, then a derivable word of the exact support yields a
target word of the exact support -/
theorem exists_mem_target_of_derivable
    (hnc : ∀ (coloring : Coloring T) (hproper : IsProper coloring) (pair : TaitColorPair),
      IsNoncrossingMatching (physicalMateInCoordinates order T hcubic coloring hproper pair))
    {target : Set (Word n)} {w : Word n} (hd : Derivable target w)
    (hw : w ∈ supportInCoordinates order T) :
    ∃ w' ∈ target, w' ∈ supportInCoordinates order T := by
  induction hd with
  | base h => exact ⟨_, h, hw⟩
  | @step w pair sel hunion hder ih =>
    obtain ⟨⟨coloring, hproper, hword⟩⟩ := hw
    have hw' : properBoundaryWordInCoordinates order coloring hproper = w := by
      funext i
      apply Subtype.ext
      have := congrFun hword (order i)
      show word coloring (order i) = (w i).1
      simpa using this
    have ha : IsActiveMatching w pair (physicalMateInCoordinates order T hcubic coloring hproper pair) := by
      rw [← hw']
      exact physicalMateInCoordinates_isActiveMatching order T hcubic coloring hproper pair
    have hn := hnc coloring hproper pair
    refine ih _ ha hn ?_
    have := switchBoundaryWord_mem_supportInCoordinates order T hcubic coloring hproper pair
      (sel _ ha hn) (hunion _ ha hn)
    rwa [hw'] at this

end KempeDerivation
end Mettapedia.GraphTheory.FourColor
