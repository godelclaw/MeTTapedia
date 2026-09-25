import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeSound
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeAuditTwo
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCut

/-!
# At the root, the colour field is the cut field

A reachable root code is the code of a connected cubic map.  A small cut of
such a map is left by exactly one edge, and cut parity (the colours of the
edges leaving a vertex set sum to zero in the Klein four-group) forces that
edge to have colour zero.  So at every width, a reachable root with a small
cut has an empty colour field.

The converse is the audit: at a width where no reachable root is rejecting, a
reachable root with an empty colour field has a small cut.  At such widths
the root decision reads the cut field alone.  The cut field of a fork is
computed from the cut fields of its children, so two reachable codes with the
same cut field have the same colourability against every planar completion
from the closure: the colour field carries no information for the decision.
The minimal machine deciding colourability at such a width is a machine
deciding bridges, and it is correct exactly because the audit holds.

The audit is kernel-checked at width two, used here, and at width three, used
in `PhysicalForkCodeCollapseThree`.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCollapse

open PhysicalForkCode PhysicalForkCodeCut PhysicalForkCodeEuler PhysicalForkCodePiece
open GoertzelV24TwoEdgeCutMinimality

section Parity

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **A bridge blocks every Tait colouring.**  A cubic map with a vertex set
left by exactly one dart has no Tait colouring. -/
theorem not_taitColorable_of_cross_eq_one (RS : RotationSystem V E) (hcub : RS.IsCubic)
    (U : Finset V) (hcross : cross RS Finset.univ U = 1) :
    ¬ RotationSystemTaitColorable RS := by
  rintro ⟨C, hC⟩
  unfold cross at hcross
  obtain ⟨d0, hd0⟩ := Finset.card_eq_one.mp hcross
  have hleave : ∀ d, RS.vertOf d ∈ U → RS.vertOf (RS.alpha d) ∉ U → d = d0 := by
    intro d hd hd'
    have h := Finset.ext_iff.mp hd0 d
    rw [Finset.mem_filter, Finset.mem_singleton] at h
    exact h.mp ⟨Finset.mem_univ _, Finset.mem_univ _, hd, hd'⟩
  have hd0mem : RS.vertOf d0 ∈ U ∧ RS.vertOf (RS.alpha d0) ∉ U := by
    have h := Finset.ext_iff.mp hd0 d0
    rw [Finset.mem_filter, Finset.mem_singleton] at h
    exact (h.mpr rfl).2.2
  have hbd : RS.vertexSideEdgeBoundary U = {RS.edgeOf d0} := by
    ext e
    rw [RS.mem_vertexSideEdgeBoundary_iff, Finset.mem_singleton]
    constructor
    · intro hcard
      obtain ⟨d, hd⟩ := RS.dartsOn_nonempty e
      have hde : RS.edgeOf d = e := RS.mem_dartsOn.mp hd
      rw [RS.endpoints_eq_pair_of_mem hd] at hcard
      by_cases hu : RS.vertOf d ∈ U
      · by_cases hv : RS.vertOf (RS.alpha d) ∈ U
        · exfalso
          have hsub : ({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V) ∩ U =
              {RS.vertOf d, RS.vertOf (RS.alpha d)} := by
            apply Finset.inter_eq_left.mpr
            intro x hx
            rw [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hu
            · exact hv
          rw [hsub, Finset.card_pair (RS.no_self_loops d)] at hcard
          omega
        · rw [← hde, hleave d hu hv]
      · by_cases hv : RS.vertOf (RS.alpha d) ∈ U
        · have hback : RS.alpha d = d0 :=
            hleave (RS.alpha d) hv (by rw [RS.alpha_involutive]; exact hu)
          rw [← hde, ← RS.edge_alpha d, hback]
        · exfalso
          have hemp : ({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V) ∩ U = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro x hx
            rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with ⟨rfl | rfl, hxU⟩
            · exact hu hxU
            · exact hv hxU
          rw [hemp, Finset.card_empty] at hcard
          omega
    · rintro rfl
      rw [RS.endpoints_eq_pair_of_mem (RS.mem_dartsOn.mpr rfl : d0 ∈ RS.dartsOn (RS.edgeOf d0))]
      have hone : ({RS.vertOf d0, RS.vertOf (RS.alpha d0)} : Finset V) ∩ U =
          {RS.vertOf d0} := by
        ext x
        rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hx⟩
          · rfl
          · exact absurd hx hd0mem.2
        · rintro rfl
          exact ⟨Or.inl rfl, hd0mem.1⟩
      rw [hone, Finset.card_singleton]
  have hsum := RS.vertexSideEdgeBoundary_colorSum_eq_zero_of_isTaitEdgeColoring hcub C hC U
  rw [hbd, Finset.sum_singleton] at hsum
  exact hC _ hsum

/-- In a connected map, a nonempty vertex set with a nonempty complement is
left by at least one dart. -/
theorem one_le_cross_of_shoreConnected (RS : RotationSystem V E)
    (hconn : ShoreConnected RS Finset.univ) {U : Finset V}
    (hU : U ⊆ touched RS Finset.univ) (hin : U.Nonempty)
    (hout : (touched RS Finset.univ \ U).Nonempty) :
    1 ≤ cross RS Finset.univ U := by
  obtain ⟨u, hu⟩ := hin
  obtain ⟨w, hw⟩ := hout
  obtain ⟨hwT, hwU⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨p⟩ := hconn u w (hU hu) hwT
  obtain ⟨dd, _, hx, hy⟩ := p.exists_boundary_dart {v | v ∈ U} hu hwU
  obtain ⟨d, _, hdx, hdy⟩ := dd.adj
  unfold cross
  show 0 < _
  exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
    by rw [hdx]; exact hx, by rw [hdy]; exact hy⟩⟩

end Parity

/-! ## The root decision -/

/-- **Parity at every width.**  A reachable root code with a small cut has an
empty colour field. -/
theorem colour_eq_empty_of_hasSmallCut {bound : ℕ} {c : Code 0} (hc : Reach bound 0 c)
    (hcut : HasSmallCut c) : c.colour = ∅ := by
  obtain ⟨V, E, i1, i2, i3, i4, RS, hC, hcub, hconn, _, hcode⟩ := reach_root_realized hc
  subst hcode
  rw [PhysicalForkCodeBase.root_colour_eq_empty_iff hC]
  have hsmall : ¬ ∀ U : Finset V, U ⊆ touched RS Finset.univ → U.Nonempty →
      (touched RS Finset.univ \ U).Nonempty → 1 < cross RS Finset.univ U :=
    fun h => (not_hasSmallCut_iff hC PhysicalForkCodeBase.rootLabel).mpr h hcut
  push Not at hsmall
  obtain ⟨U, hU, hin, hout, hle⟩ := hsmall
  exact not_taitColorable_of_cross_eq_one RS hcub U
    (le_antisymm hle (one_le_cross_of_shoreConnected RS hconn hU hin hout))

/-- **The collapse at the root.**  At a width where the audit holds, a
reachable root code has an empty colour field exactly when it has a small
cut. -/
theorem colour_eq_empty_iff_hasSmallCut {bound : ℕ} (haudit : Audit bound) {c : Code 0}
    (hc : Reach bound 0 c) : c.colour = ∅ ↔ HasSmallCut c := by
  constructor
  · intro hcol
    by_contra hno
    exact haudit c hc ⟨hcol, hno⟩
  · exact colour_eq_empty_of_hasSmallCut hc

/-- The same for a root glued from two reachable codes by a legal planar fork. -/
theorem fork_colour_eq_empty_iff {bound nL nR : ℕ} (haudit : Audit bound) {L : Code nL}
    {R : Code nR} (hL : Reach bound nL L) (hR : Reach bound nR R) {g : Glue nL nR 0}
    (hg : Legal L R g) (he : PhysicalForkCode.Euler L R g) :
    (fork L R g).colour = ∅ ↔ HasSmallCut (fork L R g) :=
  colour_eq_empty_iff_hasSmallCut haudit (Reach.fork g hL hR hg he (Nat.zero_le _))

/-- The cut field of a fork reads only the cut fields of its children. -/
theorem fork_cut_congr {nL nR nP : ℕ} {L L' : Code nL} (R : Code nR) (g : Glue nL nR nP)
    (h : L.cut = L'.cut) : (fork L R g).cut = (fork L' R g).cut := by
  simp only [fork, h]

/-- **The colour field is redundant.**  At a width where the audit holds, two
reachable codes with the same cut field have the same colourability against
every reachable completion glued to them by a legal planar fork. -/
theorem colour_behaviour_eq_of_cut_eq {bound n nR : ℕ} (haudit : Audit bound) {L L' : Code n}
    {R : Code nR} (hL : Reach bound n L) (hL' : Reach bound n L') (hR : Reach bound nR R)
    (hcut : L.cut = L'.cut) {g : Glue n nR 0} (hg : Legal L R g)
    (he : PhysicalForkCode.Euler L R g) (hg' : Legal L' R g)
    (he' : PhysicalForkCode.Euler L' R g) :
    (fork L R g).colour = ∅ ↔ (fork L' R g).colour = ∅ := by
  rw [fork_colour_eq_empty_iff haudit hL hR hg he, fork_colour_eq_empty_iff haudit hL' hR hg' he']
  unfold HasSmallCut
  rw [fork_cut_congr R g hcut]

/-! ## Width two -/

theorem colour_eq_empty_iff_hasSmallCut_two {c : Code 0} (hc : Reach 2 0 c) :
    c.colour = ∅ ↔ HasSmallCut c :=
  colour_eq_empty_iff_hasSmallCut PhysicalForkCodeFlat.audit_two hc

theorem colour_behaviour_eq_of_cut_eq_two {n nR : ℕ} {L L' : Code n} {R : Code nR}
    (hL : Reach 2 n L) (hL' : Reach 2 n L') (hR : Reach 2 nR R) (hcut : L.cut = L'.cut)
    {g : Glue n nR 0} (hg : Legal L R g) (he : PhysicalForkCode.Euler L R g)
    (hg' : Legal L' R g) (he' : PhysicalForkCode.Euler L' R g) :
    (fork L R g).colour = ∅ ↔ (fork L' R g).colour = ∅ :=
  colour_behaviour_eq_of_cut_eq PhysicalForkCodeFlat.audit_two hL hL' hR hcut hg he hg' he'

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCollapse
