import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCollapse
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditThree

/-!
# The collapse at width three

With the kernel-checked audit at width three: a root reachable at width three
has an empty colour field exactly when it has a small cut, and two codes
reachable at width three with the same cut field have the same
colourability against every reachable completion glued by a legal planar
fork.  This module imports the width-three audit and is built with it,
outside the lane gate.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCollapse

open PhysicalForkCode

theorem colour_eq_empty_iff_hasSmallCut_three {c : Code 0} (hc : Reach 3 0 c) :
    c.colour = ∅ ↔ HasSmallCut c :=
  colour_eq_empty_iff_hasSmallCut PhysicalForkCodeFlat.audit_three hc

theorem colour_behaviour_eq_of_cut_eq_three {n nR : ℕ} {L L' : Code n} {R : Code nR}
    (hL : Reach 3 n L) (hL' : Reach 3 n L') (hR : Reach 3 nR R) (hcut : L.cut = L'.cut)
    {g : Glue n nR 0} (hg : Legal L R g) (he : PhysicalForkCode.Euler L R g)
    (hg' : Legal L' R g) (he' : PhysicalForkCode.Euler L' R g) :
    (fork L R g).colour = ∅ ↔ (fork L' R g).colour = ∅ :=
  colour_behaviour_eq_of_cut_eq PhysicalForkCodeFlat.audit_three hL hL' hR hcut hg he hg' he'

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCollapse
