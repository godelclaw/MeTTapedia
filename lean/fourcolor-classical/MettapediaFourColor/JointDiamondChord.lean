import MettapediaFourColor.JointDiamondRecognition

/-! # The boundary obstruction to one extra joint-diamond chord

The completed dart permutation is exact. A Boolean orbit label separates
surviving ports on opposite sides of every chord not already excluded by
girth. Its invariance is checked on all forty-two darts, not assumed from a
picture or from a count of faces.
-/

namespace FourColor.JointDiamondPatch.Tangle.Chord

open Mettapedia.GraphTheory.FourColor
open PartialCubicDartSeparation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def port (b : Fin 8) : Realization.Unpaired (P := JointDiamond.diagram) :=
  ⟨coordinate (.inr b), coordinate_boundary b⟩

theorem port_injective : Function.Injective port := by
  intro a b h
  exact Sum.inr.inj (coordinate.injective (congrArg Subtype.val h))

theorem port_surjective : Function.Surjective port := by
  intro r
  have hs : ∀ d : JointDiamond.Slot, JointDiamond.flip d = none →
      ∃ b : Fin 8, coordinate (.inr b) = d := by decide +kernel
  obtain ⟨b, hb⟩ := hs r.1 r.2
  exact ⟨b, Subtype.ext hb⟩

noncomputable def portEquiv : Fin 8 ≃ Realization.Unpaired (P := JointDiamond.diagram) :=
  Equiv.ofBijective port ⟨port_injective, port_surjective⟩

def remaining (p q : Fin 8) (r : Realization.Unpaired (P := JointDiamond.diagram)) : Prop :=
  r ≠ port p ∧ r ≠ port q

instance (p q : Fin 8) (r : Realization.Unpaired (P := JointDiamond.diagram)) :
    Decidable (remaining p q r) := inferInstanceAs (Decidable (r ≠ port p ∧ r ≠ port q))

theorem remaining_card (p q : Fin 8) (hne : p ≠ q) :
    Fintype.card {r // remaining p q r} = 6 := by
  let e := portEquiv.subtypeEquiv (p := fun r => r ≠ p ∧ r ≠ q)
    (q := remaining p q) (fun r => by
      change (r ≠ p ∧ r ≠ q) ↔ (port r ≠ port p ∧ port r ≠ port q)
      simp only [port_injective.ne_iff])
  rw [← Fintype.card_congr e, Fintype.card_subtype]
  have hs : Finset.univ.filter (fun r : Fin 8 => r ≠ p ∧ r ≠ q) =
      (Finset.univ.erase p).erase q := by ext r; simp [and_comm]
  rw [hs, Finset.card_erase_of_mem (by simp [hne.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]


def short (p q : Fin 8) : Bool :=
  JointDiamond.diagram.pathCheck 1 (port p).1.1 (port q).1.1 ||
  JointDiamond.diagram.pathCheck 2 (port p).1.1 (port q).1.1 ||
  JointDiamond.diagram.pathCheck 3 (port p).1.1 (port q).1.1

def alpha (p q : Fin 8) : Equiv.Perm Dart :=
  (Equiv.sumCongr piece.interiorAlpha (Equiv.refl _)).trans (Equiv.swap (.inr p) (.inr q))

def phi (p q : Fin 8) : Equiv.Perm Dart := (alpha p q).trans piece.rho

/-- Next original port on each open face arc; eight marks internal faces. -/
def nextPortCodes : String := "IBIHIAIAIDICICIFIEIEIGIGIIIIIIIIIIABCDEFGH"

def nextPort (d : Dart) : Fin 9 := ConfigurationTable.lookup nextPortCodes (index d)

/-- The directed cyclic interval cut out by the chord. -/
def label (p q : Fin 8) (d : Dart) : Bool :=
  decide ((nextPort d).val < 8) && decide (0 < ((nextPort d).val + 8 - p.val) % 8 ∧
    ((nextPort d).val + 8 - p.val) % 8 ≤ (q.val + 8 - p.val) % 8)

theorem label_invariant : ∀ p q d, label p q (phi p q d) = label p q d := by decide +kernel

theorem separated_ports : ∀ p q : Fin 8, p ≠ q → short p q = false →
    p + 1 ≠ p ∧ p + 1 ≠ q ∧ q + 1 ≠ p ∧ q + 1 ≠ q ∧
      label p q (.inr (p + 1)) ≠ label p q (.inr (q + 1)) := by decide +kernel

/-- The separating label rules out a common boundary orbit. -/
theorem not_sameCycle (p q : Fin 8) (hne : p ≠ q) (hs : short p q = false) :
    ¬ (phi p q).SameCycle (.inr (p + 1)) (.inr (q + 1)) := by
  intro hc
  obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
  have hp (n : ℕ) : label p q ((phi p q ^ n) (.inr (p + 1))) =
      label p q (.inr (p + 1)) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, label_invariant, ih]
  have hh := hp n
  rw [hn] at hh
  exact (separated_ports p q hne hs).2.2.2.2 hh.symm

end FourColor.JointDiamondPatch.Tangle.Chord
