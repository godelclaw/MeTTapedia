import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePersistentKempe

/-!
# Recompose the other Kempe channels after a physical switch

Switching a region of one colour pair preserves that pair's web. For either
other pair, the new web is assembled from two parts of the old common graph:
keep the old channel's local wires with both ends outside the selected
region, and insert the conjugate channel's wires touching that region.

Connectedness is exactly the equivalence closure of those two pieces. Each
piece may itself be replaced by its connectedness relation before gluing.
The resulting theorem determines actual physical boundary mates. It retains
the internal attachment darts; the five external boundary mates alone do not
determine this composition, and no uniform bound on the attachments is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.KempeChannelSplice

open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTanglePhysicalKempeClosure

universe u

variable {V I P : Type u}

/-- Conjugate an observed colour pair by the globally applied switch. -/
def conjugatePair : TaitColorPair → TaitColorPair → TaitColorPair
  | .redBlue, .redPurple => .bluePurple
  | .redBlue, .bluePurple => .redPurple
  | .redPurple, .redBlue => .bluePurple
  | .redPurple, .bluePurple => .redBlue
  | .bluePurple, .redBlue => .redPurple
  | .bluePurple, .redPurple => .redBlue
  | _, q => q

private instance (p : TaitColorPair) (c : Color) : Decidable (pairActiveColor p c) := by
  unfold pairActiveColor Color.twoColor; infer_instance

theorem active_swap_iff : ∀ p q c,
    pairActiveColor q (Color.swap p.colors.1 p.colors.2 c) ↔
      pairActiveColor (conjugatePair p q) c := by decide +kernel

theorem active_conjugate_iff_of_inactive : ∀ p q c,
    ¬ pairActiveColor p c →
      (pairActiveColor (conjugatePair p q) c ↔ pairActiveColor q c) := by decide +kernel

variable (T : PortTangle V I P) (coloring : Coloring T)
  (switched observed : TaitColorPair) (selected : I ⊕ P → Prop)
  [DecidablePred selected] (region : KempeRegion T coloring switched selected)

/-- The complete local physical wire relation, before colour restrictions. -/
def Wire (first second : I ⊕ P) : Prop :=
  T.vert first = T.vert second ∨
    ∃ dart : I, first = Sum.inl dart ∧ second = Sum.inl (T.alpha dart)

omit [DecidablePred selected] in
/-- Saturation forbids a wire between a selected dart and an unselected dart
of the switched pair. This is the common-graph constraint used in the splice. -/
theorem selected_iff_of_wire (saturation : KempeRegion T coloring switched selected)
    {first second : I ⊕ P}
    (hf : pairActiveDart coloring switched first)
    (hs : pairActiveDart coloring switched second)
    (hwire : Wire T first second) : selected first ↔ selected second := by
  rcases hwire with hv | ⟨dart, rfl, rfl⟩
  · exact saturation.vertex_closed first second hf hs hv
  · exact (saturation.alpha_closed dart).symm

theorem active_after_iff (dart : I ⊕ P) :
    pairActiveDart (switchRegion T coloring switched selected region) observed dart ↔
      if selected dart then pairActiveDart coloring (conjugatePair switched observed) dart
      else pairActiveDart coloring observed dart := by
  by_cases hd : selected dart
  · simp only [pairActiveDart, switchRegion_color_of_mem T coloring switched selected region hd,
      ite_eq_left hd, active_swap_iff]
  · simp only [pairActiveDart,
      switchRegion_color_of_not_mem T coloring switched selected region hd, ite_eq_right hd]

/-- Wires of the observed channel left intact by the switch. -/
def outsideStep (first second : I ⊕ P) : Prop :=
  KempeStep T coloring observed first second ∧ ¬selected first ∧ ¬selected second

/-- Wires imported from the conjugate channel at the selected region. -/
def insertedStep (first second : I ⊕ P) : Prop :=
  KempeStep T coloring (conjugatePair switched observed) first second ∧
    (selected first ∨ selected second)

/-- The colour excluded from the switched pair. -/
def thirdColour : TaitColorPair → Color
  | .redBlue => purple
  | .redPurple => blue
  | .bluePurple => red

private theorem thirdColour_of_active_inactive : ∀ p q c,
    pairActiveColor (conjugatePair p q) c → ¬pairActiveColor p c →
      c = thirdColour p := by decide +kernel

omit [DecidablePred selected] in
/-- The two pieces meet through darts of the third colour. Their number and
position are information about the internal web, not just the outer ports. -/
theorem inserted_attachment_colour (saturation : KempeRegion T coloring switched selected)
    {first second : I ⊕ P}
    (hstep : insertedStep T coloring switched observed selected first second)
    (hf : selected first) (hs : ¬selected second) :
    coloring.color second = thirdColour switched := by
  apply thirdColour_of_active_inactive switched observed _ hstep.1.2.1
  intro ha
  exact hs ((selected_iff_of_wire T coloring switched selected saturation
    (saturation.active first hf) ha hstep.1.2.2).mp hf)

/-- An exact local update law on the original dart carrier. -/
theorem step_after_iff (first second : I ⊕ P) :
    KempeStep T (switchRegion T coloring switched selected region) observed first second ↔
      outsideStep T coloring observed selected first second ∨
        insertedStep T coloring switched observed selected first second := by
  classical
  by_cases hw : Wire T first second
  · have offSecond (hf : selected first) (hs : ¬selected second) :
        ¬ pairActiveDart coloring switched second := by
      intro ha
      exact hs ((selected_iff_of_wire T coloring switched selected region
        (region.active first hf) ha hw).mp hf)
    have offFirst (hf : ¬selected first) (hs : selected second) :
        ¬ pairActiveDart coloring switched first := by
      intro ha
      exact hf ((selected_iff_of_wire T coloring switched selected region
        ha (region.active second hs) hw).mpr hs)
    have hwire : T.vert first = T.vert second ∨
        ∃ dart : I, first = Sum.inl dart ∧ second = Sum.inl (T.alpha dart) := hw
    by_cases hf : selected first <;> by_cases hs : selected second
    · simp [KempeStep, outsideStep, insertedStep, active_after_iff,
        hf, hs, hwire]
    · have heq := active_conjugate_iff_of_inactive switched observed
        (coloring.color second) (offSecond hf hs)
      change pairActiveDart coloring (conjugatePair switched observed) second ↔
        pairActiveDart coloring observed second at heq
      simp [KempeStep, outsideStep, insertedStep, active_after_iff,
        hf, hs, hwire, heq]
    · have heq := active_conjugate_iff_of_inactive switched observed
        (coloring.color first) (offFirst hf hs)
      change pairActiveDart coloring (conjugatePair switched observed) first ↔
        pairActiveDart coloring observed first at heq
      simp [KempeStep, outsideStep, insertedStep, active_after_iff,
        hf, hs, hwire, heq]
    · simp [KempeStep, outsideStep, insertedStep, active_after_iff,
        hf, hs, hwire]
  · have hwire : ¬ (T.vert first = T.vert second ∨
        ∃ dart : I, first = Sum.inl dart ∧ second = Sum.inl (T.alpha dart)) := hw
    simp [KempeStep, outsideStep, insertedStep, hwire]

/-- The connectivity computation uses both cut pieces of the common web. -/
def recomposed (first second : I ⊕ P) : Prop :=
  Relation.EqvGen (fun a b => outsideStep T coloring observed selected a b ∨
    insertedStep T coloring switched observed selected a b) first second

theorem connected_after_iff (first second : I ⊕ P) :
    KempeConnected T (switchRegion T coloring switched selected region) observed first second ↔
      recomposed T coloring switched observed selected first second := by
  constructor
  · exact Relation.EqvGen.mono
      (fun a b h => (step_after_iff T coloring switched observed selected region a b).mp h)
      first second
  · exact Relation.EqvGen.mono
      (fun a b h => (step_after_iff T coloring switched observed selected region a b).mpr h)
      first second

/-- Either piece may be summarized by its internal connectedness before the
two are composed. All attachment points remain in the carrier. -/
theorem eqvGen_union_components_iff {A : Type*} (R S : A → A → Prop) (a b : A) :
    Relation.EqvGen (fun x y => Relation.EqvGen R x y ∨ Relation.EqvGen S x y) a b ↔
      Relation.EqvGen (fun x y => R x y ∨ S x y) a b := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      rcases h with h | h
      · exact Relation.EqvGen.mono (fun _ _ h => Or.inl h) x y h
      · exact Relation.EqvGen.mono (fun _ _ h => Or.inr h) x y h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · exact Relation.EqvGen.mono (fun x y h => h.elim
      (fun h => Or.inl (Relation.EqvGen.rel x y h))
      (fun h => Or.inr (Relation.EqvGen.rel x y h))) a b

/-- Compositional form of the other-channel update. -/
theorem connected_after_iff_components (first second : I ⊕ P) :
    KempeConnected T (switchRegion T coloring switched selected region) observed first second ↔
      Relation.EqvGen (fun a b =>
        Relation.EqvGen (outsideStep T coloring observed selected) a b ∨
        Relation.EqvGen (insertedStep T coloring switched observed selected) a b) first second :=
  (connected_after_iff T coloring switched observed selected region first second).trans
    (eqvGen_union_components_iff _ _ first second).symm

section Finite

variable [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

/-- Recover the actual boundary mate from the recomposed common-web pieces. -/
theorem physicalMate_after_eq_iff (hcubic : IsCubic T) (hproper : IsProper coloring)
    (root other : P)
    (hroot : pairActiveDart (switchRegion T coloring switched selected region)
      observed (Sum.inr root)) :
    physicalMate T hcubic (switchRegion T coloring switched selected region)
        (switchRegion_isProper T coloring hproper switched selected region) observed root = other ↔
      other ≠ root ∧
        pairActiveDart (switchRegion T coloring switched selected region) observed (Sum.inr other) ∧
        recomposed T coloring switched observed selected (Sum.inr root) (Sum.inr other) := by
  rw [physicalMate_eq_iff_of_active T hcubic
    (switchRegion T coloring switched selected region)
    (switchRegion_isProper T coloring hproper switched selected region) observed root other hroot]
  rw [connected_after_iff T coloring switched observed selected region]

end Finite

end Mettapedia.GraphTheory.FourColor.Compositional.KempeChannelSplice
