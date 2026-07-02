import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTauReverseAudit

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shared helpers for generated `mirror,normal` length-two direct bridges
-/

namespace GoertzelLemma818LengthTwoMTBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818MirrorTauReverseAudit

theorem mtRowReverseValid_step_of_ne (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) (hne : row.source ≠ row.parent)
    (h : mtRowReverseValid key expected row = true) :
    chainSpecifiedKempeStep mtWord
      (directStates row.parentLeft row.parentRight)
      (directStates row.sourceLeft row.sourceRight) row.move = true := by
  simp [mtRowReverseValid] at h
  rcases h with ⟨_, hrest⟩
  rcases hrest.2 with heq | hstep
  · exact False.elim (hne heq)
  · exact hstep

end GoertzelLemma818LengthTwoMTBridge

end Mettapedia.GraphTheory.FourColor
