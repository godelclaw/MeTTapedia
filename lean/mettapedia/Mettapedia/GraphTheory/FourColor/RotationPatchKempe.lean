import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleCommonKempeWeb

/-!
# Physical Kempe switches on an actual vertex side

The retained darts of a rotation system are the original incidences, with
crossing edges exposed as ports. An edge mask automatically respects the two
halves of every intact edge. Local saturation at retained vertices supplies
the existing common-web switch theorem. Consequently a switch preserves the
actual exterior colouring, including its cut-edge observations, without
requiring any colouring of the omitted vertices.
-/

namespace Mettapedia.GraphTheory.FourColor.RotationPatchKempe

open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E) (outside : V → Prop)

abbrev SideDart := InternalDart RS outside ⊕ BoundaryDart RS outside

/-- The original dart underlying an intact incidence or an exposed port. -/
def underlying : SideDart RS outside → RS.D :=
  fun dart => dart.elim (fun d => d.1.1) (fun d => d.1.1)

theorem underlying_outside (dart : SideDart RS outside) :
    outside (RS.vertOf (underlying RS outside dart)) := by
  cases dart with
  | inl d => exact d.1.2
  | inr d => exact d.1.2

theorem underlying_injective : Function.Injective (underlying RS outside) := by
  intro a b h
  have hret : (retainedDartEquivInternalSumBoundary RS outside).symm a =
      (retainedDartEquivInternalSumBoundary RS outside).symm b := by
    apply Subtype.ext
    cases a <;> cases b <;> exact h
  exact (retainedDartEquivInternalSumBoundary RS outside).symm.injective hret

/-- The exact port reduct of the retained rotation side; no new incidence is
introduced and the original intact involution is retained. -/
def tangle : PortTangle {v : V // outside v}
    (InternalDart RS outside) (BoundaryDart RS outside) where
  vert dart := ⟨RS.vertOf (underlying RS outside dart), underlying_outside RS outside dart⟩
  alpha := internalAlpha RS outside
  alpha_involutive := internalAlpha_involutive RS outside
  alpha_fixfree := internalAlpha_fixfree RS outside
  no_self_loops := by
    intro dart h
    exact RS.no_self_loops dart.1.1 (congrArg Subtype.val h)

/-- Restriction uses actual edge identities, so invariance needs no global
proper-colouring assumption. -/
def colouring (base : E → Color) : Coloring (tangle RS outside) where
  color dart := base (RS.edgeOf (underlying RS outside dart))
  invariant dart := congrArg base (RS.edge_alpha dart.1.1)

/-- Properness stated only at retained vertices. -/
def LocalProper (base : E → Color) : Prop :=
  (∀ d, outside (RS.vertOf d) → base (RS.edgeOf d) ≠ 0) ∧
    ∀ d e, outside (RS.vertOf d) → RS.vertOf d = RS.vertOf e →
      d ≠ e → base (RS.edgeOf d) ≠ base (RS.edgeOf e)

theorem colouring_proper (base : E → Color) (h : LocalProper RS outside base) :
    IsProper (colouring RS outside base) := by
  constructor
  · intro dart
    exact h.1 _ (underlying_outside RS outside dart)
  · intro first second hv hn
    exact h.2 _ _ (underlying_outside RS outside first)
      (congrArg Subtype.val hv) (fun he => hn (underlying_injective RS outside he))

/-- A physical edge mask contains only active incidences and retains both
active incidences together at each exterior vertex. Edge closure is automatic
because the mask is a predicate on actual edges. -/
structure Region (base : E → Color) (pair : TaitColorPair) (mask : E → Prop) : Prop where
  active : ∀ d, outside (RS.vertOf d) → mask (RS.edgeOf d) →
    pairActiveColor pair (base (RS.edgeOf d))
  vertex_closed : ∀ d e, outside (RS.vertOf d) → RS.vertOf d = RS.vertOf e →
    pairActiveColor pair (base (RS.edgeOf d)) →
    pairActiveColor pair (base (RS.edgeOf e)) →
    (mask (RS.edgeOf d) ↔ mask (RS.edgeOf e))

theorem region_common_web (base : E → Color) (pair : TaitColorPair) (mask : E → Prop)
    (h : Region RS outside base pair mask) :
    KempeRegion (tangle RS outside) (colouring RS outside base) pair
      (fun dart => mask (RS.edgeOf (underlying RS outside dart))) := by
  constructor
  · intro dart hd
    exact h.active _ (underlying_outside RS outside dart) hd
  · intro dart
    change mask (RS.edgeOf (RS.alpha dart.1.1)) ↔ mask (RS.edgeOf dart.1.1)
    rw [RS.edge_alpha]
  · intro first second hf hs hv
    exact h.vertex_closed _ _ (underlying_outside RS outside first)
      (congrArg Subtype.val hv) hf hs

/-- The actual edge-field update, including every exposed boundary edge. -/
def switched (base : E → Color) (pair : TaitColorPair) (mask : E → Prop)
    [DecidablePred mask] (e : E) : Color :=
  if mask e then Color.swap pair.colors.1 pair.colors.2 (base e) else base e

theorem colouring_switched (base : E → Color) (pair : TaitColorPair) (mask : E → Prop)
    [DecidablePred mask] (h : Region RS outside base pair mask) :
    colouring RS outside (switched base pair mask) =
      switchRegion (tangle RS outside) (colouring RS outside base) pair
        (fun dart => mask (RS.edgeOf (underlying RS outside dart)))
        (region_common_web RS outside base pair mask h) := by
  apply Coloring.ext'
  rfl

/-- A reusable physical preservation law for any retained vertex side.
The omitted vertices need not admit any colouring. -/
theorem switched_proper (base : E → Color) (hproper : LocalProper RS outside base)
    (pair : TaitColorPair) (mask : E → Prop) [DecidablePred mask]
    (h : Region RS outside base pair mask) :
    IsProper (colouring RS outside (switched base pair mask)) := by
  rw [colouring_switched RS outside base pair mask h]
  exact switchRegion_isProper _ _ (colouring_proper RS outside base hproper)
    pair _ (region_common_web RS outside base pair mask h)

end
end Mettapedia.GraphTheory.FourColor.RotationPatchKempe
