import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSpliceConstructor

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Darts based at vertices retained after deleting a region. A crossing dart
is retained as a half-edge so that it can subsequently be rewired. -/
def RetainedDart (RS : RotationSystem V E) (keep : V → Prop) :=
  {dart : RS.D // keep (RS.vertOf dart)}

/-- Retained darts whose old opposite dart is also retained. -/
def InternalDart (RS : RotationSystem V E) (keep : V → Prop) :=
  {dart : RetainedDart RS keep //
    keep (RS.vertOf (RS.alpha dart.1))}

/-- Retained darts whose old opposite dart lies in the deleted region. These
are exactly the half-edges exposed for seam rewiring. -/
def BoundaryDart (RS : RotationSystem V E) (keep : V → Prop) :=
  {dart : RetainedDart RS keep //
    ¬ keep (RS.vertOf (RS.alpha dart.1))}

noncomputable instance retainedDartFintype
    (RS : RotationSystem V E) (keep : V → Prop) :
    Fintype (RetainedDart RS keep) :=
  Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

instance retainedDartDecidableEq
    (RS : RotationSystem V E) (keep : V → Prop) :
    DecidableEq (RetainedDart RS keep) :=
  Classical.decEq _

noncomputable instance internalDartFintype
    (RS : RotationSystem V E) (keep : V → Prop) :
    Fintype (InternalDart RS keep) :=
  Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

instance internalDartDecidableEq
    (RS : RotationSystem V E) (keep : V → Prop) :
    DecidableEq (InternalDart RS keep) :=
  Classical.decEq _

noncomputable instance boundaryDartFintype
    (RS : RotationSystem V E) (keep : V → Prop) :
    Fintype (BoundaryDart RS keep) :=
  Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

instance boundaryDartDecidableEq
    (RS : RotationSystem V E) (keep : V → Prop) :
    DecidableEq (BoundaryDart RS keep) :=
  Classical.decEq _

/-- Every retained dart is uniquely classified as intact or exposed. -/
def retainedDartEquivInternalSumBoundary
    (RS : RotationSystem V E) (keep : V → Prop) :
    RetainedDart RS keep ≃ InternalDart RS keep ⊕ BoundaryDart RS keep := by
  classical
  refine
    { toFun := fun dart =>
        if hopposite : keep (RS.vertOf (RS.alpha dart.1)) then
          Sum.inl ⟨dart, hopposite⟩
        else
          Sum.inr ⟨dart, hopposite⟩
      invFun := fun dart => dart.elim
        (fun internal => internal.1)
        (fun boundary => boundary.1)
      left_inv := ?_
      right_inv := ?_ }
  · intro dart
    by_cases hopposite : keep (RS.vertOf (RS.alpha dart.1))
    · simp only [dif_pos hopposite, Sum.elim_inl]
    · simp only [dif_neg hopposite, Sum.elim_inr]
  · intro dart
    rcases dart with internal | boundary
    · simp only [Sum.elim_inl, dif_pos internal.2]
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
    · simp only [Sum.elim_inr, dif_neg boundary.2]
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl

/-- The old edge flip restricts to a permutation of intact retained darts. -/
def internalAlpha (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (InternalDart RS keep) where
  toFun dart :=
    ⟨⟨RS.alpha dart.1.1, dart.2⟩, by
      simpa [RS.alpha_involutive] using dart.1.2⟩
  invFun dart :=
    ⟨⟨RS.alpha dart.1.1, dart.2⟩, by
      simpa [RS.alpha_involutive] using dart.1.2⟩
  left_inv dart := by
    apply Subtype.ext
    apply Subtype.ext
    exact RS.alpha_involutive dart.1.1
  right_inv dart := by
    apply Subtype.ext
    apply Subtype.ext
    exact RS.alpha_involutive dart.1.1

@[simp]
theorem internalAlpha_val (RS : RotationSystem V E) (keep : V → Prop)
    (dart : InternalDart RS keep) :
    (internalAlpha RS keep dart).1.1 = RS.alpha dart.1.1 :=
  rfl

/-- The restricted intact flip remains involutive. -/
theorem internalAlpha_involutive
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : InternalDart RS keep) :
    internalAlpha RS keep (internalAlpha RS keep dart) = dart := by
  apply Subtype.ext
  apply Subtype.ext
  exact RS.alpha_involutive dart.1.1

/-- The restricted intact flip remains fixed-point free. -/
theorem internalAlpha_fixfree
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : InternalDart RS keep) :
    internalAlpha RS keep dart ≠ dart := by
  intro heq
  exact RS.alpha_fixfree dart.1.1
    (congrArg (fun retained : InternalDart RS keep => retained.1.1) heq)

/-- The vertex rotation restricts automatically to retained darts because it
never changes the base vertex. -/
def retainedRho (RS : RotationSystem V E) (keep : V → Prop) :
    Equiv.Perm (RetainedDart RS keep) :=
  RS.rho.subtypePerm fun dart => by
    rw [RS.vert_rho]

@[simp]
theorem retainedRho_val (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep) :
    (retainedRho RS keep dart).1 = RS.rho dart.1 :=
  rfl

/-- Restrict exposed darts to those supported on a specified cut edge set. -/
def BoundaryDartOn (RS : RotationSystem V E) (keep : V → Prop)
    (cut : Finset E) :=
  {dart : BoundaryDart RS keep // RS.edgeOf dart.1.1 ∈ cut}

noncomputable instance boundaryDartOnFintype
    (RS : RotationSystem V E) (keep : V → Prop) (cut : Finset E) :
    Fintype (BoundaryDartOn RS keep cut) :=
  Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

instance boundaryDartOnDecidableEq
    (RS : RotationSystem V E) (keep : V → Prop) (cut : Finset E) :
    DecidableEq (BoundaryDartOn RS keep cut) :=
  Classical.decEq _

/-- Two outward-oriented boundary darts on the same old edge are equal. The
alpha-opposite alternative is excluded because that dart is not retained. -/
theorem boundaryDart_eq_of_edgeOf_eq
    (RS : RotationSystem V E) (keep : V → Prop)
    (left right : BoundaryDart RS keep)
    (hedge : RS.edgeOf left.1.1 = RS.edgeOf right.1.1) :
    left = right := by
  have hleftMem : left.1.1 ∈ RS.dartsOn (RS.edgeOf left.1.1) := by
    simp
  have hrightMem : right.1.1 ∈ RS.dartsOn (RS.edgeOf left.1.1) := by
    simp [RotationSystem.mem_dartsOn, hedge]
  have hpairs := RS.dartsOn_eq_pair_of_mem hleftMem
  have hcases : right.1.1 = left.1.1 ∨ right.1.1 = RS.alpha left.1.1 := by
    have : right.1.1 ∈ ({left.1.1, RS.alpha left.1.1} : Finset RS.D) := by
      rw [← hpairs]
      exact hrightMem
    simpa using this
  rcases hcases with heq | hopposite
  · exact Subtype.ext (Subtype.ext heq.symm)
  · exact False.elim (left.2 (hopposite ▸ right.1.2))

/-- The cut set enumerated by an ordered crossing map. -/
def orderedCut (crossingEdge : Fin n → E) : Finset E :=
  Finset.univ.image crossingEdge

/-- Choose the unique retained orientation of one crossed edge from an
existence proof that the edge really leaves the retained side. -/
def orientedBoundaryDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (step : Fin n) : BoundaryDart RS keep :=
  ⟨⟨Classical.choose (hcrosses step),
      (Classical.choose_spec (hcrosses step)).2.1⟩,
    (Classical.choose_spec (hcrosses step)).2.2⟩

@[simp]
theorem orientedBoundaryDart_edgeOf
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (step : Fin n) :
    RS.edgeOf (orientedBoundaryDart RS keep crossingEdge hcrosses step).1.1 =
      crossingEdge step :=
  (Classical.choose_spec (hcrosses step)).1

/-- The ordered crossing map lands in all exposed darts supported on its cut. -/
def orderedBoundaryDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (step : Fin n) :
    BoundaryDartOn RS keep (orderedCut crossingEdge) :=
  ⟨orientedBoundaryDart RS keep crossingEdge hcrosses step, by
    exact Finset.mem_image.2 ⟨step, Finset.mem_univ _,
      (orientedBoundaryDart_edgeOf RS keep crossingEdge hcrosses step).symm⟩⟩

@[simp]
theorem orderedBoundaryDart_edgeOf
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (step : Fin n) :
    RS.edgeOf (orderedBoundaryDart RS keep crossingEdge hcrosses step).1.1.1 =
      crossingEdge step :=
  orientedBoundaryDart_edgeOf RS keep crossingEdge hcrosses step

/-- An injective ordered edge cut gives an injective enumeration of its
outward boundary darts. -/
theorem orderedBoundaryDart_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hinjective : Function.Injective crossingEdge) :
    Function.Injective
      (orderedBoundaryDart RS keep crossingEdge hcrosses) := by
  intro left right hdarts
  apply hinjective
  rw [← orientedBoundaryDart_edgeOf RS keep crossingEdge hcrosses left,
    ← orientedBoundaryDart_edgeOf RS keep crossingEdge hcrosses right]
  exact congrArg
    (fun dart : BoundaryDartOn RS keep (orderedCut crossingEdge) =>
      RS.edgeOf dart.1.1.1) hdarts

/-- Every outward boundary dart on the enumerated cut is the selected
orientation of exactly one cut position. -/
theorem orderedBoundaryDart_surjective
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart))) :
    Function.Surjective
      (orderedBoundaryDart RS keep crossingEdge hcrosses) := by
  rintro ⟨dart, hdartCut⟩
  rcases Finset.mem_image.1 hdartCut with ⟨step, _, hstep⟩
  have hedges :
      RS.edgeOf
          (orientedBoundaryDart RS keep crossingEdge hcrosses step).1.1 =
        RS.edgeOf dart.1.1 := by
    rw [orientedBoundaryDart_edgeOf]
    exact hstep
  have hdarts :
      orientedBoundaryDart RS keep crossingEdge hcrosses step = dart :=
    boundaryDart_eq_of_edgeOf_eq RS keep _ _ hedges
  exact ⟨step, Subtype.ext hdarts⟩

/-- Thus an ordered injective transversal, once oriented across a retained
side, is exactly its full boundary-dart interface. -/
def orderedBoundaryDartEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hinjective : Function.Injective crossingEdge) :
    Fin n ≃ BoundaryDartOn RS keep (orderedCut crossingEdge) :=
  Equiv.ofBijective (orderedBoundaryDart RS keep crossingEdge hcrosses)
    ⟨orderedBoundaryDart_injective RS keep crossingEdge hcrosses hinjective,
      orderedBoundaryDart_surjective RS keep crossingEdge hcrosses⟩

@[simp]
theorem orderedBoundaryDartEquiv_apply
    (RS : RotationSystem V E) (keep : V → Prop)
    (crossingEdge : Fin n → E)
    (hcrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = crossingEdge step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hinjective : Function.Injective crossingEdge) (step : Fin n) :
    orderedBoundaryDartEquiv RS keep crossingEdge hcrosses hinjective step =
      orderedBoundaryDart RS keep crossingEdge hcrosses step :=
  rfl

end

end GoertzelV24RotationCutDartDecomposition

end Mettapedia.GraphTheory.FourColor
