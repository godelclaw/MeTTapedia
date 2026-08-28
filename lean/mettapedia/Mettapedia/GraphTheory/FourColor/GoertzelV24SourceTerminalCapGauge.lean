import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceTerminalCapView
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuCapTable
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutColor

/-!
# Color gauges for the source terminal cap view

The source names the two stored connectivity roles relative to the ordered
majority/singleton triple of a good boundary word.  It then globally relabels
that triple to `(red, blue, purple)`.  This file proves that this normalization
is lossless for the cap-composed terminal test.

Only the five boundary colors are relabeled.  The two Boolean strand relations
retain their abstract roles `alphaBeta` and `alphaGamma`; no third pair and no
new receipt field is introduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SourceTerminalCapGauge

open GoertzelV24AnnularFrontierMenu
open GoertzelV24AnnularFrontierMenuCapComposed
open GoertzelV24AnnularFrontierMenuCapMatching
open GoertzelV24AnnularFrontierMenuCapTable
open GoertzelV24SourceCorridorProfile
open GoertzelV24SourceTerminalCapView

/-- Relabel only the color word of a role-indexed cap view.  The two strand
relations retain their abstract source roles. -/
def relabelWord
    (view : SourceTerminalCapView) (relabel : Color ≃ Color) :
    SourceTerminalCapView where
  word := cap5MapBoundaryWord relabel view.word
  strand := view.strand

/-- Relabeling a boundary word preserves the number of occurrences of the
correspondingly relabeled color. -/
theorem cap5BoundaryColorCount_map_equiv
    (relabel : Color ≃ Color) (word : CAP5BoundaryWord) (color : Color) :
    cap5BoundaryColorCount (cap5MapBoundaryWord relabel word) (relabel color) =
      cap5BoundaryColorCount word color := by
  simp [cap5BoundaryColorCount, cap5MapBoundaryWord]

@[simp] theorem cap5MapBoundaryWord_symm_map
    (relabel : Color ≃ Color) (word : CAP5BoundaryWord) :
    cap5MapBoundaryWord relabel.symm (cap5MapBoundaryWord relabel word) = word := by
  funext position
  simp [cap5MapBoundaryWord]

/-- A majority/singleton triple transports under every zero-fixing color
equivalence. -/
theorem AnnularFrontierMajorityTriple.map_equiv
    {word : CAP5BoundaryWord} {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple
      word majority singletonFirst singletonSecond)
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0) :
    AnnularFrontierMajorityTriple (cap5MapBoundaryWord relabel word)
      (relabel majority) (relabel singletonFirst) (relabel singletonSecond) := by
  rcases htriple with ⟨hcolors, hmajority, hfirst, hsecond⟩
  refine ⟨isTaitColorTriple_map_equiv_of_map_zero hzero hcolors, ?_, ?_, ?_⟩
  · simpa [cap5BoundaryColorCount_map_equiv] using hmajority
  · simpa [cap5BoundaryColorCount_map_equiv] using hfirst
  · simpa [cap5BoundaryColorCount_map_equiv] using hsecond

/-- The source role interpreted in an arbitrary ordered Tait gauge. -/
def capComposedMenuBForPairAt
    (view : SourceTerminalCapView)
    (alpha beta gamma : Color) (pair : SourceTrackedColorPair) : Prop :=
  let colors := sourceTrackedColorPairColors alpha beta gamma pair
  ∃ inactive : Fin 5,
    InactivePosition view.word colors.1 colors.2 inactive ∧
      CapComposedMenuB (fun first second =>
        view.strand pair first second = true) inactive

/-- The source terminal test in an arbitrary ordered majority/singleton
gauge. -/
def capComposedMenuBStateAt
    (view : SourceTerminalCapView) (alpha beta gamma : Color) : Prop :=
  AnnularFrontierMajorityTriple view.word alpha beta gamma ∧
    (capComposedMenuBForPairAt view alpha beta gamma .alphaBeta ∨
      capComposedMenuBForPairAt view alpha beta gamma .alphaGamma)

/-- The canonical equivalence normalizing an ordered Tait triple to
`(red, blue, purple)`. -/
noncomputable def normalizeColorEquiv
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) : Color ≃ Color :=
  (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm

@[simp] theorem normalizeColorEquiv_zero
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    normalizeColorEquiv hcolors 0 = 0 := by
  change (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm 0 = 0
  simpa using
    (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm_apply_apply 0

@[simp] theorem normalizeColorEquiv_alpha
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    normalizeColorEquiv hcolors alpha = red := by
  change (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm alpha = red
  simpa using
    (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm_apply_apply red

@[simp] theorem normalizeColorEquiv_beta
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    normalizeColorEquiv hcolors beta = blue := by
  change (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm beta = blue
  simpa using
    (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm_apply_apply blue

@[simp] theorem normalizeColorEquiv_gamma
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    normalizeColorEquiv hcolors gamma = purple := by
  change (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm gamma = purple
  simpa using
    (GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv hcolors).symm_apply_apply purple

@[simp] theorem normalizeColorEquiv_symm_red
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    (normalizeColorEquiv hcolors).symm red = alpha := by
  exact GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_red hcolors

@[simp] theorem normalizeColorEquiv_symm_blue
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    (normalizeColorEquiv hcolors).symm blue = beta := by
  exact GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_blue hcolors

@[simp] theorem normalizeColorEquiv_symm_purple
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    (normalizeColorEquiv hcolors).symm purple = gamma := by
  exact GoertzelV24ThreeEdgeCutColor.taitTripleColorEquiv_purple hcolors

/-- Normalize a cap view using the ordered majority/singleton colors. -/
noncomputable def normalizedCapView
    (view : SourceTerminalCapView) {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) : SourceTerminalCapView :=
  relabelWord view (normalizeColorEquiv hcolors)

/-- Normalization carries either abstract source role to its standard-gauge
pair without changing the role's strand relation. -/
theorem capComposedMenuBForPair_normalized_iff
    (view : SourceTerminalCapView) {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma)
    (pair : SourceTrackedColorPair) :
    (normalizedCapView view hcolors).capComposedMenuBForPair pair ↔
      capComposedMenuBForPairAt view alpha beta gamma pair := by
  constructor
  · rintro ⟨inactive, hinactive, hmenu⟩
    refine ⟨inactive, ?_, hmenu⟩
    have hback := inactivePosition_map_equiv
      (σ := (normalizeColorEquiv hcolors).symm) hinactive
    cases pair <;>
      simpa [normalizedCapView, relabelWord,
        sourceTrackedColorPairColors,
        SourceTerminalCapView.capComposedMenuBForPair,
        capComposedMenuBForPairAt] using hback
  · rintro ⟨inactive, hinactive, hmenu⟩
    refine ⟨inactive, ?_, hmenu⟩
    have hforward := inactivePosition_map_equiv
      (σ := normalizeColorEquiv hcolors) hinactive
    cases pair <;>
      simpa [normalizedCapView, relabelWord,
        sourceTrackedColorPairColors,
        SourceTerminalCapView.capComposedMenuBForPair,
        capComposedMenuBForPairAt] using hforward

/-- The normalized word has the literal standard majority/singleton triple. -/
theorem normalizedCapView_standardTriple
    (view : SourceTerminalCapView) {alpha beta gamma : Color}
    (htriple : AnnularFrontierMajorityTriple view.word alpha beta gamma) :
    AnnularFrontierMajorityTriple (normalizedCapView view htriple.1).word
      red blue purple := by
  have hmapped := AnnularFrontierMajorityTriple.map_equiv htriple
    (normalizeColorEquiv htriple.1) (normalizeColorEquiv_zero htriple.1)
  simpa [normalizedCapView, relabelWord] using hmapped

/-- **Global color normalization is lossless for cap acceptance.** -/
theorem standardGaugeCapComposedMenuBState_normalized_iff
    (view : SourceTerminalCapView) {alpha beta gamma : Color}
    (htriple : AnnularFrontierMajorityTriple view.word alpha beta gamma) :
    (normalizedCapView view htriple.1).standardGaugeCapComposedMenuBState ↔
      capComposedMenuBStateAt view alpha beta gamma := by
  rw [SourceTerminalCapView.standardGaugeCapComposedMenuBState,
    capComposedMenuBStateAt]
  rw [capComposedMenuBForPair_normalized_iff,
    capComposedMenuBForPair_normalized_iff]
  simp only [normalizedCapView_standardTriple view htriple, htriple,
    true_and]

end GoertzelV24SourceTerminalCapGauge

end Mettapedia.GraphTheory.FourColor
