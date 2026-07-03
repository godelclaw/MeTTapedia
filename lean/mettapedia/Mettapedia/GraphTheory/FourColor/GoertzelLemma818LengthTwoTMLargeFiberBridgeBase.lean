import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoDirectClosurePrototype
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TauMirrorReverseAudit

namespace Mettapedia.GraphTheory.FourColor

/-!
# Shared helpers for generated size-64 `normal,mirror` length-two bridges
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

theorem tmRowReverseValid_step_of_ne (key : List LColor) (expected : List Nat)
    (row : DirectChainParentRow) (hne : row.source ≠ row.parent)
    (h : tmRowReverseValid key expected row = true) :
    chainSpecifiedKempeStep tmWord
      (directStates row.parentLeft row.parentRight)
      (directStates row.sourceLeft row.sourceRight) row.move = true := by
  simp [tmRowReverseValid] at h
  rcases h with ⟨_, hrest⟩
  rcases hrest.2 with heq | hstep
  · exact False.elim (hne heq)
  · exact hstep

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
