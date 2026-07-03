import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorMirrorReverseAudit

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shared helpers for generated `mirror,mirror` length-two direct bridges
-/

namespace GoertzelLemma818LengthTwoMMBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818MirrorMirrorReverseAudit

theorem mmRowReverseValid_step_of_ne (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) (hne : row.source ≠ row.parent)
    (h : mmRowReverseValid key expected row = true) :
    chainSpecifiedKempeStep mmWord
      (directStates row.parentLeft row.parentRight)
      (directStates row.sourceLeft row.sourceRight) row.move = true := by
  simp [mmRowReverseValid] at h
  rcases h with ⟨_, hrest⟩
  rcases hrest.2 with heq | hstep
  · exact False.elim (hne heq)
  · exact hstep

end GoertzelLemma818LengthTwoMMBridge

end Mettapedia.GraphTheory.FourColor
