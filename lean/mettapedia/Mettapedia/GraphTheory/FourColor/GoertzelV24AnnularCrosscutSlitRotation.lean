import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscut
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSpliceConstructor

/-!
# Opening a rotation system along an annular crosscut

An annular transversal is an open interface, not a cyclic vertex cut.  This
file gives it a literal combinatorial-map realization: every crossed edge is
opened into two degree-one boundary stubs while every uncut dart retains its
old vertex rotation.  Thus the source-level open tangle is a checked rotation
system before it is used by any profile or splice theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscutSlitRotation

open GoertzelV24RotationSpliceConstructor

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- The actual oriented ends of edges opened by a crosscut. -/
abbrev CutDart (RS : RotationSystem V E) (cut : Finset E) :=
  { dart : RS.D // RS.edgeOf dart ∈ cut }

/-- Old vertices together with one fresh endpoint for every opened dart. -/
abbrev SlitVertex (RS : RotationSystem V E) (cut : Finset E) :=
  V ⊕ CutDart RS cut

/-- Old darts together with one fresh dart at every exposed boundary stub. -/
abbrev SlitDart (RS : RotationSystem V E) (cut : Finset E) :=
  RS.D ⊕ CutDart RS cut

/-- Vertex map for the cut-open combinatorial map. -/
def slitVertOf (RS : RotationSystem V E) (cut : Finset E) :
    SlitDart RS cut → SlitVertex RS cut
  | Sum.inl dart => Sum.inl (RS.vertOf dart)
  | Sum.inr port => Sum.inr port

/-- The old rotation is kept at every old vertex; a new boundary stub has the
single-dart rotation appropriate for degree one. -/
def slitRho (RS : RotationSystem V E) (cut : Finset E) :
    Equiv.Perm (SlitDart RS cut) :=
  Equiv.sumCongr RS.rho (Equiv.refl _)

/-- The edge involution after cutting.  An uncut edge keeps its old partner;
each oriented end of a cut edge is paired with its own fresh boundary dart. -/
def slitAlphaFun (RS : RotationSystem V E) (cut : Finset E) :
    SlitDart RS cut → SlitDart RS cut
  | Sum.inl dart =>
      if hcut : RS.edgeOf dart ∈ cut then Sum.inr ⟨dart, hcut⟩
      else Sum.inl (RS.alpha dart)
  | Sum.inr port => Sum.inl port.1

/-- Opening twice restores every dart. -/
theorem slitAlphaFun_involutive (RS : RotationSystem V E) (cut : Finset E)
    (dart : SlitDart RS cut) :
    slitAlphaFun RS cut (slitAlphaFun RS cut dart) = dart := by
  rcases dart with dart | port
  · by_cases hcut : RS.edgeOf dart ∈ cut
    · simp [slitAlphaFun, hcut]
    · have hcutAlpha : RS.edgeOf (RS.alpha dart) ∉ cut := by
        simpa only [RS.edge_alpha dart] using hcut
      simp [slitAlphaFun, hcut, hcutAlpha, RS.alpha_involutive]
  · simp [slitAlphaFun, port.2]

/-- The cut-open edge involution, derived from the involutive function above. -/
def slitAlpha (RS : RotationSystem V E) (cut : Finset E) :
    Equiv.Perm (SlitDart RS cut) where
  toFun := slitAlphaFun RS cut
  invFun := slitAlphaFun RS cut
  left_inv := slitAlphaFun_involutive RS cut
  right_inv := slitAlphaFun_involutive RS cut

@[simp]
theorem slitAlpha_apply (RS : RotationSystem V E) (cut : Finset E)
    (dart : SlitDart RS cut) :
    slitAlpha RS cut dart = slitAlphaFun RS cut dart :=
  rfl

@[simp]
theorem slitAlpha_old_of_mem (RS : RotationSystem V E) (cut : Finset E)
    {dart : RS.D} (hcut : RS.edgeOf dart ∈ cut) :
    slitAlpha RS cut (Sum.inl dart) = Sum.inr ⟨dart, hcut⟩ := by
  simp [slitAlpha, slitAlphaFun, hcut]

@[simp]
theorem slitAlpha_old_of_not_mem (RS : RotationSystem V E) (cut : Finset E)
    {dart : RS.D} (hcut : RS.edgeOf dart ∉ cut) :
    slitAlpha RS cut (Sum.inl dart) = Sum.inl (RS.alpha dart) := by
  simp [slitAlpha, slitAlphaFun, hcut]

@[simp]
theorem slitAlpha_stub (RS : RotationSystem V E) (cut : Finset E)
    (port : CutDart RS cut) :
    slitAlpha RS cut (Sum.inr port) = Sum.inl port.1 :=
  rfl

/-- The full rewired dart system of the cut-open map.  Its finite edge type
and its two-dart edge fibers are derived by `RewiredDartSystem`, rather than
postulated for the new boundary stubs. -/
def slitRewiredDartSystem (RS : RotationSystem V E) (cut : Finset E) :
    RewiredDartSystem (SlitVertex RS cut) (SlitDart RS cut) where
  vertOf := slitVertOf RS cut
  alpha := slitAlpha RS cut
  rho := slitRho RS cut
  alpha_involutive := slitAlphaFun_involutive RS cut
  alpha_fixfree := by
    intro dart
    rcases dart with dart | port
    · by_cases hcut : RS.edgeOf dart ∈ cut
      · simp [slitAlpha, slitAlphaFun, hcut]
      · intro hfixed
        have hold : RS.alpha dart = dart := by
          have hfixed' :
              (Sum.inl (RS.alpha dart) : SlitDart RS cut) = Sum.inl dart := by
            simpa [slitAlpha, slitAlphaFun, hcut] using hfixed
          exact Sum.inl.inj hfixed'
        exact RS.alpha_fixfree dart hold
    · simp [slitAlpha, slitAlphaFun]
  vert_rho := by
    intro dart
    rcases dart with dart | port
    · have hrotation := congrArg
        (fun vertex => (Sum.inl vertex : SlitVertex RS cut))
        (RS.vert_rho dart)
      simpa [slitVertOf, slitRho] using hrotation
    · rfl
  outer := Sum.inl RS.outer
  no_self_loops := by
    intro dart
    rcases dart with dart | port
    · by_cases hcut : RS.edgeOf dart ∈ cut
      · simp [slitVertOf, slitAlpha, slitAlphaFun, hcut]
      · intro hloop
        have hold : RS.vertOf dart = RS.vertOf (RS.alpha dart) := by
          have hloop' :
              (Sum.inl (RS.vertOf dart) : SlitVertex RS cut) =
                Sum.inl (RS.vertOf (RS.alpha dart)) := by
            simpa [slitVertOf, slitAlpha, slitAlphaFun, hcut] using hloop
          exact Sum.inl.inj hloop'
        exact RS.no_self_loops dart hold
    · simp [slitVertOf, slitAlpha, slitAlphaFun]

/-- The actual cut-open rotation system. -/
noncomputable def slitRotationSystem (RS : RotationSystem V E) (cut : Finset E) :
    RotationSystem (SlitVertex RS cut) (slitRewiredDartSystem RS cut).Edge :=
  (slitRewiredDartSystem RS cut).toRotationSystem

@[simp]
theorem slitRotationSystem_vertOf_old (RS : RotationSystem V E) (cut : Finset E)
    (dart : RS.D) :
    (slitRotationSystem RS cut).vertOf (Sum.inl dart) =
      Sum.inl (RS.vertOf dart) :=
  rfl

@[simp]
theorem slitRotationSystem_vertOf_stub (RS : RotationSystem V E) (cut : Finset E)
    (port : CutDart RS cut) :
    (slitRotationSystem RS cut).vertOf (Sum.inr port) = Sum.inr port :=
  rfl

@[simp]
theorem slitRotationSystem_rho_old (RS : RotationSystem V E) (cut : Finset E)
    (dart : RS.D) :
    (slitRotationSystem RS cut).rho (Sum.inl dart) = Sum.inl (RS.rho dart) :=
  rfl

@[simp]
theorem slitRotationSystem_rho_stub (RS : RotationSystem V E) (cut : Finset E)
    (port : CutDart RS cut) :
    (slitRotationSystem RS cut).rho (Sum.inr port) = Sum.inr port :=
  rfl

@[simp]
theorem slitRotationSystem_alpha_old_of_mem
    (RS : RotationSystem V E) (cut : Finset E) {dart : RS.D}
    (hcut : RS.edgeOf dart ∈ cut) :
    (slitRotationSystem RS cut).alpha (Sum.inl dart) = Sum.inr ⟨dart, hcut⟩ :=
  slitAlpha_old_of_mem RS cut hcut

@[simp]
theorem slitRotationSystem_alpha_old_of_not_mem
    (RS : RotationSystem V E) (cut : Finset E) {dart : RS.D}
    (hcut : RS.edgeOf dart ∉ cut) :
    (slitRotationSystem RS cut).alpha (Sum.inl dart) =
      Sum.inl (RS.alpha dart) :=
  slitAlpha_old_of_not_mem RS cut hcut

@[simp]
theorem slitRotationSystem_alpha_stub (RS : RotationSystem V E) (cut : Finset E)
    (port : CutDart RS cut) :
    (slitRotationSystem RS cut).alpha (Sum.inr port) = Sum.inl port.1 :=
  slitAlpha_stub RS cut port

end

end GoertzelV24AnnularCrosscutSlitRotation

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24AnnularCrosscutSlitRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace SimpleDualCrosscut

/-- The source-level annular crosscut, realized as an actual open rotation
system.  Its crossed facial-dual edges become boundary stubs in the new map;
the construction is derived from the crosscut's finite support. -/
noncomputable def slitRotationSystem
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    RotationSystem
      (SlitVertex RS (crosscut.crossingEdges hunique))
      (slitRewiredDartSystem RS (crosscut.crossingEdges hunique)).Edge :=
  GoertzelV24AnnularCrosscutSlitRotation.slitRotationSystem RS
    (crosscut.crossingEdges hunique)

/-- A primal dart whose edge is crossed by the transversal is literally
opened to its own fresh boundary stub in the source-level slit map. -/
theorem slitRotationSystem_crossing_opens
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (step : Fin crosscut.walk.length) (dart : RS.D)
    (hcrossing : RS.edgeOf dart = crosscut.crossingEdge hunique step) :
    (crosscut.slitRotationSystem hunique).alpha (Sum.inl dart) =
      Sum.inr ⟨dart, (crosscut.mem_crossingEdges_iff hunique _).2
        ⟨step, hcrossing.symm⟩⟩ := by
  exact slitRotationSystem_alpha_old_of_mem RS
    (crosscut.crossingEdges hunique)
    ((crosscut.mem_crossingEdges_iff hunique _).2 ⟨step, hcrossing.symm⟩)

end SimpleDualCrosscut

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
