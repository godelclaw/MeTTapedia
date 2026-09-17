import Mettapedia.GraphTheory.FourColor.HypermapEulerTree
import Mettapedia.GraphTheory.FourColor.HypermapWalkupChecks

/-!
# The combinatorial Jordan curve theorem

**A hypermap is planar exactly when it has no Moebius path**: `planar_iff_jordan`.

`Planar` is a count — vanishing Euler defect.  `Jordan` is a statement about
contours — no duplicate-free C-path has crossing node links.  Their equivalence
is the combinatorial content of the Jordan curve theorem, and it is what licenses
arguing about planar maps by separation rather than by counting.  This is the
source's `planarP`.

* `jordan_of_planar` (in `HypermapJordanPlanar`) is the direction the source
  calls `planar_Jordan`: a minimal planar counterexample is cut down by Walkup
  deletions until it is the three-dart genus-one map.
* `planar_of_jordan`, below, is `Jordan_planar`: by induction on the dart count.
  `euler_tree` supplies a dart whose deletion keeps the genus,
  `jordan_walkupE` keeps the Jordan property, and the smaller map is planar.

Nothing is assumed: both directions rest on the genus identities of
`HypermapWalkupGenus`, which in turn rest on the transposition split/merge law
and the orbit-count splitting tools already in this development.
-/

namespace Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability

namespace Hypermap

universe u

/-- The empty hypermap is planar: every count vanishes. -/
theorem planar_of_isEmpty {D : Type u} [Fintype D] [DecidableEq D] [IsEmpty D]
    (H : Hypermap D) : Planar H := by
  have hq : ∀ (s : Setoid D) [Fintype (Quotient s)], Fintype.card (Quotient s) = 0 :=
    fun s _ => Fintype.card_eq_zero_iff.2 ⟨fun q => Quotient.inductionOn q isEmptyElim⟩
  rw [planar_iff_eulerRhs_eq, eulerRhs_eq_card_add_two_mul_compCount, eulerLhs_eq_orbit_sum]
  have hE : orbitCount H.edge = 0 := hq _
  have hN : orbitCount H.node = 0 := hq _
  have hF : orbitCount H.face = 0 := hq _
  have hC : compCount H = 0 := hq _
  rw [hE, hN, hF, hC, Fintype.card_eq_zero]

theorem planar_of_jordan_of_card_le :
    ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] (H : Hypermap D),
      Fintype.card D ≤ n → Jordan H → Planar H := by
  intro n
  induction n with
  | zero =>
      intro D _ _ H hcard _
      have : IsEmpty D := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      exact planar_of_isEmpty H
  | succ n ih =>
      intro D _ _ H hcard hJ
      by_cases hE : IsEmpty D
      · exact planar_of_isEmpty H
      · obtain ⟨x₀⟩ : Nonempty D := not_isEmpty_iff.mp hE
        obtain ⟨y, -, hy⟩ := euler_tree hJ x₀
        have hgen : Degenerate H y ∨ ¬ CrossEdge H y := by
          rcases hy with (h | h) | h
          · exact Or.inl (Or.inr (Or.inl h.symm))
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr h
        have hcard' : Fintype.card {x : D // x ≠ y} ≤ n := by
          have := card_subtype_ne_succ y
          omega
        have hP' := ih {x : D // x ≠ y} (walkupE H y) hcard' (jordan_walkupE H y hJ)
        rw [planar_iff_genus_eq_zero] at hP' ⊢
        rw [← genus_walkupE_eq H y hgen]
        exact hP'

/-- **A hypermap with no Moebius path is planar.**  This is the source's
`Jordan_planar`. -/
theorem planar_of_jordan {D : Type u} [Fintype D] [DecidableEq D] (H : Hypermap D)
    (hJ : Jordan H) : Planar H :=
  planar_of_jordan_of_card_le _ D H le_rfl hJ

/-- **The combinatorial Jordan curve theorem.**  A hypermap is planar — its Euler
defect vanishes — exactly when it carries no Moebius path.  This is the source's
`planarP`. -/
theorem planar_iff_jordan {D : Type u} [Fintype D] [DecidableEq D] (H : Hypermap D) :
    Planar H ↔ Jordan H :=
  ⟨jordan_of_planar H, planar_of_jordan H⟩

/-- Both halves recorded in `HypermapJordan`, discharged on every carrier. -/
theorem jordanImpliesPlanarOn (D : Type u) [Fintype D] [DecidableEq D] :
    JordanImpliesPlanarOn D :=
  fun H hJ => planar_of_jordan H hJ

/-- `walkup_induction` is the principle the proofs run on: the planar-to-Jordan
direction, re-derived from it in one step. -/
example {D : Type u} [Fintype D] [DecidableEq D] (H : Hypermap D) : Planar H → Jordan H :=
  walkup_induction (P := fun _ _ _ K => Planar K → Jordan K)
    (fun _ _ _ _ ih hP => jordan_of_jordanBelow (fun y K' hK' => ih y K' hK') hP) H

/-! ## Checks against the small maps

Each of these was established independently — the Euler counts by the
complete-invariant lemma, the Moebius path and its absence by direct
construction — so their agreement through `planar_iff_jordan` is a genuine
consistency check. -/

example : Planar spherePair ↔ Jordan spherePair :=
  ⟨fun _ => jordan_spherePair, fun _ => planar_spherePair⟩

example : ¬ Planar torusTriple ∧ ¬ Jordan torusTriple :=
  ⟨not_planar_torusTriple, not_jordan_torusTriple⟩

/-- The two-dart planar map is recovered as planar *from its Jordan property*. -/
example : Planar spherePair := planar_of_jordan spherePair jordan_spherePair

/-- The one-dart map is planar, via the Jordan property. -/
example : Planar pointMap := planar_of_jordan pointMap jordan_pointMap

/-- The Walkup transform of the genus-one map is planar, so it has no Moebius
path — even though the map it came from does. -/
example : Jordan (walkupE torusTriple 0) :=
  jordan_of_planar _ planar_walkupE_torusTriple

end Hypermap

end Mettapedia.GraphTheory.FourColor
