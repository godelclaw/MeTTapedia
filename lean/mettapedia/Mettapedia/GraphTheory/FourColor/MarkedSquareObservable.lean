import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareProfile
import Mathlib.Data.Fin.VecNotation

/-!
# Erased-edge observables in a square reduction

The unmarked square count identity does not transport a colour name on an
erased internal edge by choosing one of the surviving seam edges. The
all-red boundary is a counterexample, even for equality with the colour of
an external port not incident with the internal marked edge.

An exact replacement observable retains one internal colour as a virtual
seed. All four internal colours are reconstructed from it and the full
boundary. Arbitrary targets can then be transported, but this does not
construct a smaller physical tangle carrying that virtual observation.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedSquareObservable

def reconstruct (w : SquareBoundaryWord) (t : Color) : SquareInternalColoring :=
  ![t, w 1 + t, w 2 + (w 1 + t), w 3 + (w 2 + (w 1 + t))]

/-- The seed transforms with the colours; it is not an arbitrary ordering
of the two extensions at an all-equal boundary. -/
theorem reconstruct_map (e : Color ≃+ Color) (w : SquareBoundaryWord) (t : Color) :
    reconstruct (e ∘ w) (e t) = e ∘ reconstruct w t := by
  funext i
  fin_cases i <;> simp [reconstruct]

private theorem third (a b c : Color) :
    ProperColorTriple a b c → c = a + b := by decide +revert

/-- The first internal colour and the complete boundary determine the fibre. -/
theorem extension_reconstruct {w : SquareBoundaryWord} {x : SquareInternalColoring}
    (h : IsSquareExtension w x) : reconstruct w (x 0) = x := by
  have h1 := third _ _ _ h.2.1
  have h2 := third _ _ _ h.2.2.1
  have h3 := third _ _ _ h.2.2.2
  funext i
  fin_cases i <;> simp [reconstruct, h1, h2, h3]

/-- The affine reconstruction must close around the square and stay nonzero. -/
def SeedOK (w : SquareBoundaryWord) (t : Color) : Prop :=
  w 0 + w 1 + w 2 + w 3 = 0 ∧ ∀ i, reconstruct w t i ≠ 0
  deriving Decidable

set_option maxRecDepth 4096 in
theorem seedOK_iff : ∀ (w : SquareBoundaryWord) (t : Color),
    w.Nonzero → (SeedOK w t ↔ IsSquareExtension w (reconstruct w t)) := by
  decide +kernel

/-- An arbitrary predicate may inspect all internal colours, not just edge 0. -/
def targetEquiv (w : SquareBoundaryWord) (P : SquareInternalColoring → Prop) :
    {x // IsSquareExtension w x ∧ P x} ≃
      {t // IsSquareExtension w (reconstruct w t) ∧ P (reconstruct w t)} where
  toFun x := ⟨x.1 0, by simpa [extension_reconstruct x.2.1] using x.2⟩
  invFun t := ⟨reconstruct w t.1, t.2⟩
  left_inv x := Subtype.ext (extension_reconstruct x.2.1)
  right_inv t := by apply Subtype.ext; rfl

/-- Exact count transport for any internal observation, via the seed fibre. -/
theorem target_count (w : SquareBoundaryWord) (P : SquareInternalColoring → Prop)
    [DecidablePred P] :
    Fintype.card {x // IsSquareExtension w x ∧ P x} =
      Fintype.card {t // IsSquareExtension w (reconstruct w t) ∧ P (reconstruct w t)} :=
  Fintype.card_congr (targetEquiv w P)

/-- The zero-target version does not lose the erased observation. -/
theorem target_empty_iff (w : SquareBoundaryWord) (P : SquareInternalColoring → Prop) :
    (¬ ∃ x, IsSquareExtension w x ∧ P x) ↔
      ¬ ∃ t, IsSquareExtension w (reconstruct w t) ∧ P (reconstruct w t) := by
  constructor
  · intro h ⟨t, ht⟩; exact h ⟨reconstruct w t, ht⟩
  · intro h ⟨x, hx⟩
    apply h
    exact ⟨x 0, by simpa [extension_reconstruct hx.1] using hx⟩

def redBoundary : SquareBoundaryWord := fun _ => red
def blueFirst : SquareInternalColoring := ![blue, purple, blue, purple]
def purpleFirst : SquareInternalColoring := ![purple, blue, purple, blue]

theorem explicit_extensions :
    IsSquareExtension redBoundary blueFirst ∧
      IsSquareExtension redBoundary purpleFirst := by decide

/-- Both seam edges of either unmarked smoothing carry red; no literal
seam-edge image can preserve the erased mark's equality with boundary port 2. -/
theorem no_red_internal_mark (x : SquareInternalColoring)
    (h : IsSquareExtension redBoundary x) : x 0 ≠ redBoundary 2 :=
  h.1.2.2.2.2.1.symm

/-- Colours on the two surviving seam edges, in either planar smoothing. -/
def seamColor (w : SquareBoundaryWord) (side : SquareReductionSide) (seam : Fin 2) : Color :=
  if side = .join01_23 then (if seam = 0 then w 0 else w 2)
  else (if seam = 0 then w 1 else w 3)

/-- Refined zero upstairs need not mean refined zero under literal tracking. -/
theorem literal_image_zero_failure :
    (¬ ∃ x, IsSquareExtension redBoundary x ∧ x 0 = redBoundary 2) ∧
      (∀ side : SquareReductionSide, ∀ seam : Fin 2,
        side.Compatible redBoundary ∧ seamColor redBoundary side seam = redBoundary 2) := by
  constructor
  · rintro ⟨x, hx, heq⟩; exact no_red_internal_mark x hx heq
  · intro side seam
    simp [SquareReductionSide.Compatible, seamColor, redBoundary]

/-- At this fixed boundary the refined counts are zero upstairs and one
on each smoothing, independently of which seam edge receives the mark. -/
theorem literal_count_failure :
    Fintype.card {x // IsSquareExtension redBoundary x ∧ x 0 = redBoundary 2} = 0 ∧
      ∀ side : SquareReductionSide, ∀ seam : Fin 2,
        Fintype.card {_u : Unit // side.Compatible redBoundary ∧
          seamColor redBoundary side seam = redBoundary 2} = 1 := by
  decide +kernel

/-- A colour transposition fixing the boundary fixes neither extension. -/
theorem no_swap_fixed_extension (x : SquareInternalColoring)
    (h : IsSquareExtension redBoundary x) :
    (fun i => Color.swap blue purple (x i)) ≠ x := by
  intro heq
  have hfix := congrFun heq 0
  have hnz := h.1.2.2.1
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (x 0) hnz with hr | hb | hp
  · exact no_red_internal_mark x h hr
  · exact blue_ne_purple (by simpa [hb] using hfix.symm)
  · rw [hp, Color.swap_eq_right] at hfix
    exact blue_ne_purple hfix

/-- Even an arbitrary decoder from a fixed reduction label cannot select a
valid extension naturally under the colour transposition fixing the input. -/
theorem no_equivariant_selector :
    ¬ ∃ choose : Fin 2 → SquareInternalColoring,
      (∀ side, IsSquareExtension redBoundary (choose side)) ∧
      (∀ side i, Color.swap blue purple (choose side i) = choose side i) := by
  rintro ⟨choose, hp, heq⟩
  exact no_swap_fixed_extension (choose 0) (hp 0) (funext (heq 0))

end Mettapedia.GraphTheory.FourColor.MarkedSquareObservable
