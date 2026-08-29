import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeCertificateRedBlue
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeCertificateRedPurple
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeCertificateBluePurple

/-!
# Same-family persistence still does not determine the hexagon language

The physical mate of one bichromatic web persists under switches of that
same web.  This file assembles three independently checked finite
certificates.  They exhibit a nonempty, colour-blind sixty-word
language which avoids the literal hexagon support but carries a deterministic
noncrossing mate for every state and colour pair.  Every component-union
switch stays in the language and preserves the selected mate for that pair.

Thus even stateful same-family persistence does not recover the shared-edge
incidence between the three bichromatic webs.  The remaining source datum is
the genuinely joint idemposition action on one common trivalent web.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24HexagonPersistentKempeAdversary

open GoertzelV24RawNooseCountPumping
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24HexCycleBoundarySupport

private theorem allPersistentRows_eq_true (pair : TaitColorPair) :
    allPersistentRows pair = true := by
  cases pair
  · exact allPersistentRows_redBlue
  · exact allPersistentRows_redPurple
  · exact allPersistentRows_bluePurple

/-- Consumer-facing form of the checked sixty-state census. -/
theorem persistentAdversary_card_eq_sixty :
    persistentAdversaryFinset.card = 60 :=
  card_persistentAdversaryFinset

/-- Every supported word carries a deterministic noncrossing mate whose
component-union transitions remain supported and preserve that same mate. -/
theorem persistentAdversary_hasPersistentCandidate :
    ∀ word ∈ persistentAdversary, ∀ pair : TaitColorPair,
      PersistentCandidateKempeWitness word pair := by
  intro word hword pair
  rw [← explicitWord_of_word word] at hword ⊢
  have hrow := persistentRow_eq_true pair
    (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)
    (allPersistentRows_eq_true pair)
  have hwordBool :
      persistentAdversaryBool
        (explicitWord (word 0) (word 1) (word 2)
          (word 3) (word 4) (word 5)) = true := hword
  have hwitness :
      persistentCandidateKempeWitnessBool
        (explicitWord (word 0) (word 1) (word 2)
          (word 3) (word 4) (word 5)) pair = true := by
    have hpair :
        persistentCandidateKempeWitnessBool
            (explicitWord (word 0) (word 1) (word 2)
              (word 3) (word 4) (word 5)) pair = true ∧
          hexBoundaryRealizableBool
            (explicitWord (word 0) (word 1) (word 2)
              (word 3) (word 4) (word 5)) = false := by
      simpa [persistentRow, hwordBool] using hrow
    exact hpair.1
  exact (persistentCandidateKempeWitnessBool_eq_true_iff _ _).1 hwitness

/-- The sixty-state language contains no literal hexagon boundary word.  Its
cardinality is checked separately by `card_persistentAdversaryFinset`. -/
theorem persistentAdversary_disjoint_hexagonSupport :
    Disjoint persistentAdversary hexagonSupport := by
  rw [Set.disjoint_left]
  intro word hword hhex
  have hword' :
      explicitWord (word 0) (word 1) (word 2)
        (word 3) (word 4) (word 5) ∈ persistentAdversary := by
    simpa only [explicitWord_of_word] using hword
  have hhex' :
      explicitWord (word 0) (word 1) (word 2)
        (word 3) (word 4) (word 5) ∈ hexagonSupport := by
    simpa only [explicitWord_of_word] using hhex
  have hrow := persistentRow_eq_true TaitColorPair.redBlue
    (word 0) (word 1) (word 2) (word 3) (word 4) (word 5)
    allPersistentRows_redBlue
  have hwordBool :
      persistentAdversaryBool
        (explicitWord (word 0) (word 1) (word 2)
          (word 3) (word 4) (word 5)) = true := hword'
  have hnotRealizable :
      hexBoundaryRealizableBool
        (explicitWord (word 0) (word 1) (word 2)
          (word 3) (word 4) (word 5)) = false := by
    have hpair :
        persistentCandidateKempeWitnessBool
            (explicitWord (word 0) (word 1) (word 2)
              (word 3) (word 4) (word 5)) TaitColorPair.redBlue = true ∧
          hexBoundaryRealizableBool
            (explicitWord (word 0) (word 1) (word 2)
              (word 3) (word 4) (word 5)) = false := by
      simpa [persistentRow, hwordBool] using hrow
    exact hpair.2
  have hrealizable : HexBoundaryRealizable
      (explicitWord (word 0) (word 1) (word 2)
        (word 3) (word 4) (word 5)) :=
    (exists_hexagonExtension_iff_hexBoundaryRealizable _).1 hhex'
  have htrue := (hexBoundaryRealizableBool_eq_true_iff _).2 hrealizable
  rw [hnotRealizable] at htrue
  contradiction

/-- The adversary is not vacuous. -/
theorem persistentAdversary_nonempty : persistentAdversary.Nonempty := by
  refine ⟨explicitWord ⟨red, red_ne_zero⟩ ⟨red, red_ne_zero⟩
    ⟨blue, blue_ne_zero⟩ ⟨red, red_ne_zero⟩
    ⟨red, red_ne_zero⟩ ⟨blue, blue_ne_zero⟩, ?_⟩
  decide

end GoertzelV24HexagonPersistentKempeAdversary
end Mettapedia.GraphTheory.FourColor
