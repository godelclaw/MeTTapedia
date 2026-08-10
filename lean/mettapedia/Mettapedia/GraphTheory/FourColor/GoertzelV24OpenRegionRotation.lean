import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

/-!
# Literal open regions of a rotation system

The compositional route uses open planar pieces, not merely a closed map with
some boundary data named externally.  Given a retained vertex-side, this file
constructs its literal combinatorial-map realization: old darts based at
retained vertices stay in the piece, and every edge leaving that side receives
a new degree-one boundary stub.

The construction is generic rotation-system theory.  Later source-specific
crosscut constructions supply the retained side and identify its stubs with
the ordered boundary word used by the finite profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionRotation

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The old vertices retained by an open region. -/
abbrev RetainedVertex (keep : V → Prop) := { vertex : V // keep vertex }

noncomputable instance retainedVertexFintype (keep : V → Prop) :
    Fintype (RetainedVertex keep) :=
  Fintype.ofInjective (fun vertex : RetainedVertex keep => vertex.1)
    Subtype.val_injective

instance retainedVertexDecidableEq (keep : V → Prop) :
    DecidableEq (RetainedVertex keep) :=
  Classical.decEq _

/-- A literal open region has old retained vertices and one fresh vertex for
each exposed half-edge. -/
abbrev Vertex (RS : RotationSystem V E) (keep : V → Prop) :=
  RetainedVertex keep ⊕ BoundaryDart RS keep

/-- A literal open region has each dart based at a retained vertex, together
with one fresh dart for each exposed half-edge. -/
abbrev Dart (RS : RotationSystem V E) (keep : V → Prop) :=
  RetainedDart RS keep ⊕ BoundaryDart RS keep

/-- Vertex map for the open region.  Fresh darts live at their own fresh
degree-one boundary vertices. -/
def vertOf (RS : RotationSystem V E) (keep : V → Prop) :
    Dart RS keep → Vertex RS keep
  | Sum.inl dart => Sum.inl ⟨RS.vertOf dart.1, dart.2⟩
  | Sum.inr boundary => Sum.inr boundary

/-- The old cyclic order restricts to every retained vertex; each new boundary
vertex has the unique degree-one rotation. -/
def rho (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (Dart RS keep) :=
  Equiv.sumCongr (retainedRho RS keep) (Equiv.refl _)

/-- Edge flip after opening the retained region.  An internal old dart keeps
its old mate.  An exposed old dart is paired with its own fresh stub. -/
noncomputable def alphaFun (RS : RotationSystem V E) (keep : V → Prop) :
    Dart RS keep → Dart RS keep := by
  classical
  intro dart
  rcases dart with dart | boundary
  · by_cases hinternal : keep (RS.vertOf (RS.alpha dart.1))
    · exact Sum.inl ⟨RS.alpha dart.1, hinternal⟩
    · exact Sum.inr ⟨dart, hinternal⟩
  · exact Sum.inl boundary.1

/-- Opening a region twice returns each dart. -/
theorem alphaFun_involutive (RS : RotationSystem V E) (keep : V → Prop)
    (dart : Dart RS keep) :
    alphaFun RS keep (alphaFun RS keep dart) = dart := by
  classical
  rcases dart with dart | boundary
  · by_cases hinternal : keep (RS.vertOf (RS.alpha dart.1))
    · simp [alphaFun, hinternal, dart.2, RS.alpha_involutive]
    · simp [alphaFun, hinternal]
  · simp [alphaFun, boundary.2]

/-- The involutive open-region edge flip. -/
def alpha (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (Dart RS keep) where
  toFun := alphaFun RS keep
  invFun := alphaFun RS keep
  left_inv := alphaFun_involutive RS keep
  right_inv := alphaFun_involutive RS keep

@[simp]
theorem alpha_apply (RS : RotationSystem V E) (keep : V → Prop)
    (dart : Dart RS keep) :
    alpha RS keep dart = alphaFun RS keep dart :=
  rfl

@[simp]
theorem alpha_old_of_internal (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep)
    (hinternal : keep (RS.vertOf (RS.alpha dart.1))) :
    alpha RS keep (Sum.inl dart) = Sum.inl ⟨RS.alpha dart.1, hinternal⟩ := by
  classical
  simp [alpha, alphaFun, hinternal]

@[simp]
theorem alpha_old_of_boundary (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep)
    (hboundary : ¬ keep (RS.vertOf (RS.alpha dart.1))) :
    alpha RS keep (Sum.inl dart) = Sum.inr ⟨dart, hboundary⟩ := by
  classical
  simp [alpha, alphaFun, hboundary]

@[simp]
theorem alpha_stub (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) :
    alpha RS keep (Sum.inr boundary) = Sum.inl boundary.1 :=
  rfl

/-- The literal dart system of the retained open region.  The open piece may
lie away from the ambient map's distinguished outer dart, so it takes its own
chosen dart as the rotation-system root. -/
def rewiredDartSystem (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    RewiredDartSystem (Vertex RS keep) (Dart RS keep) where
  vertOf := vertOf RS keep
  alpha := alpha RS keep
  rho := rho RS keep
  alpha_involutive := alphaFun_involutive RS keep
  alpha_fixfree := by
    classical
    intro dart
    rcases dart with dart | boundary
    · by_cases hinternal : keep (RS.vertOf (RS.alpha dart.1))
      · intro hfixed
        have hold : RS.alpha dart.1 = dart.1 := by
          have hfixed' :
              (Sum.inl ⟨RS.alpha dart.1, hinternal⟩ : Dart RS keep) =
                Sum.inl dart := by
            simpa [alpha, alphaFun, hinternal] using hfixed
          have hfixedDart :
              (⟨RS.alpha dart.1, hinternal⟩ : RetainedDart RS keep) = dart :=
            Sum.inl.inj hfixed'
          exact congrArg Subtype.val hfixedDart
        exact RS.alpha_fixfree dart.1 hold
      · simp [alpha, alphaFun, hinternal]
    · simp [alpha, alphaFun]
  vert_rho := by
    intro dart
    rcases dart with dart | boundary
    · simpa [rho, vertOf, retainedRho_val] using RS.vert_rho dart.1
    · rfl
  outer := outer
  no_self_loops := by
    classical
    intro dart hloop
    rcases dart with dart | boundary
    · by_cases hinternal : keep (RS.vertOf (RS.alpha dart.1))
      · have hold : RS.vertOf dart.1 = RS.vertOf (RS.alpha dart.1) := by
          have hloop' :
              (Sum.inl ⟨RS.vertOf dart.1, dart.2⟩ : Vertex RS keep) =
                Sum.inl ⟨RS.vertOf (RS.alpha dart.1), hinternal⟩ := by
            simpa [vertOf, alpha, alphaFun, hinternal] using hloop
          exact congrArg Subtype.val (Sum.inl.inj hloop')
        exact RS.no_self_loops dart.1 hold
      · simp [vertOf, alpha, alphaFun, hinternal] at hloop
    · simp [vertOf, alpha, alphaFun] at hloop

/-- The actual rotation system of the literal open region. -/
noncomputable def rotationSystem (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    RotationSystem (Vertex RS keep) (rewiredDartSystem RS keep outer).Edge :=
  (rewiredDartSystem RS keep outer).toRotationSystem

@[simp]
theorem rotationSystem_vertOf_old (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : RetainedDart RS keep) :
    (rotationSystem RS keep outer).vertOf (Sum.inl dart) =
      Sum.inl ⟨RS.vertOf dart.1, dart.2⟩ :=
  rfl

@[simp]
theorem rotationSystem_vertOf_stub (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    (rotationSystem RS keep outer).vertOf (Sum.inr boundary) =
      Sum.inr boundary :=
  rfl

@[simp]
theorem rotationSystem_rho_old (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : RetainedDart RS keep) :
    (rotationSystem RS keep outer).rho (Sum.inl dart) =
      Sum.inl (retainedRho RS keep dart) :=
  rfl

@[simp]
theorem rotationSystem_rho_stub (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    (rotationSystem RS keep outer).rho (Sum.inr boundary) = Sum.inr boundary :=
  rfl

@[simp]
theorem rotationSystem_alpha_old_of_internal
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : RetainedDart RS keep)
    (hinternal : keep (RS.vertOf (RS.alpha dart.1))) :
    (rotationSystem RS keep outer).alpha (Sum.inl dart) =
      Sum.inl ⟨RS.alpha dart.1, hinternal⟩ :=
  alpha_old_of_internal RS keep dart hinternal

@[simp]
theorem rotationSystem_alpha_old_of_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : RetainedDart RS keep)
    (hboundary : ¬ keep (RS.vertOf (RS.alpha dart.1))) :
    (rotationSystem RS keep outer).alpha (Sum.inl dart) =
      Sum.inr ⟨dart, hboundary⟩ :=
  alpha_old_of_boundary RS keep dart hboundary

@[simp]
theorem rotationSystem_alpha_stub
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (boundary : BoundaryDart RS keep) :
    (rotationSystem RS keep outer).alpha (Sum.inr boundary) = Sum.inl boundary.1 :=
  alpha_stub RS keep boundary

end

end GoertzelV24OpenRegionRotation

end Mettapedia.GraphTheory.FourColor
