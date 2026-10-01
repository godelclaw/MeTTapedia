import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Assembling local coverage without losing its occurrence witness

This is the radius and case argument of Theorem 6.7(iii) of Inoue,
Kawarabayashi, Miyashita, Mohar, Thomassen and Thorup, arXiv:2603.24880v1.
The three local supply laws correspond to Lemmas 8.2, 8.7 and 8.4.
They are explicit hypotheses, not established classification results here.

Balls use the extended graph distance, so disconnected vertices never enter
a finite ball. Recentring retains one and the same occurrence and its entire
support. The graph degrees are actual degrees. The predicate `zero` is a
parameter; an application to discharging must supply the actual charge law.
-/

namespace FourColor.LocalCoverageAssembly

open SimpleGraph

variable {V W : Type*} (G : SimpleGraph V)

/-- Closed graph ball, with the radius convention used by the paper. -/
def closedBall (c : V) (r : ℕ) : Set V := {v | G.edist c v ≤ r}

theorem centre_mem (c : V) (r : ℕ) : c ∈ closedBall G c r := by
  simp [closedBall]

theorem ball_mono {c : V} {r s : ℕ} (h : r ≤ s) :
    closedBall G c r ⊆ closedBall G c s := by
  intro v hv
  change G.edist c v ≤ (r : ℕ∞) at hv
  change G.edist c v ≤ (s : ℕ∞)
  exact hv.trans (by exact_mod_cast h)

/-- The geometric cost of moving the centre is added to the local radius. -/
theorem ball_recenter {c u : V} {a b : ℕ} (h : u ∈ closedBall G c a) :
    closedBall G u b ⊆ closedBall G c (a + b) := by
  intro v hv
  change G.edist c v ≤ ((a + b : ℕ) : ℕ∞)
  rw [Nat.cast_add]
  exact G.edist_triangle.trans (add_le_add h hv)

def OnBall (c : V) (r : ℕ) (P : V → Prop) : Prop :=
  ∀ v ∈ closedBall G c r, P v

variable {G}

theorem OnBall.mono {c : V} {r s : ℕ} {P : V → Prop}
    (h : OnBall G c s P) (hrs : r ≤ s) : OnBall G c r P :=
  fun v hv => h v (ball_mono G hrs hv)

theorem OnBall.recenter {c u : V} {a b r : ℕ} {P : V → Prop}
    (h : OnBall G c r P) (hu : u ∈ closedBall G c a) (hr : a + b ≤ r) :
    OnBall G u b P :=
  fun v hv => h v (ball_mono G hr (ball_recenter G hu hv))

variable (G) (support : W → Set V) (valid : W → Prop)

/-- A genuine occurrence with all of its retained observations in the ball. -/
def Occurs (c : V) (r : ℕ) : Prop :=
  ∃ w, valid w ∧ support w ⊆ closedBall G c r

variable {G support valid}

theorem Occurs.mono {c : V} {r s : ℕ}
    (h : Occurs G support valid c r) (hrs : r ≤ s) :
    Occurs G support valid c s := by
  obtain ⟨w, hw, hs⟩ := h
  exact ⟨w, hw, hs.trans (ball_mono G hrs)⟩

theorem Occurs.recenter {c u : V} {a b : ℕ}
    (h : Occurs G support valid u b) (hu : u ∈ closedBall G c a) :
    Occurs G support valid c (a + b) := by
  obtain ⟨w, hw, hs⟩ := h
  exact ⟨w, hw, hs.trans (ball_recenter G hu)⟩

variable (G support valid) [G.LocallyFinite] (zero : V → Prop)

/-- The remaining local mathematical obligations. An occurrence may be a
certified reduction or an explicitly retained residual, such as an obstructing
cycle. Constructing these fields requires the geometric classification. -/
structure LocalSupply : Prop where
  low : ∀ c, OnBall G c 2 (fun v => G.degree v ≤ 6) →
    Occurs G support valid c 2
  seven : ∀ c, G.degree c = 7 → OnBall G c 3 zero →
    OnBall G c 5 (fun v => G.degree v ≤ 7) → Occurs G support valid c 5
  eight : ∀ c, G.degree c = 8 → OnBall G c 3 zero →
    OnBall G c 5 (fun v => G.degree v ≤ 8) → Occurs G support valid c 5

variable (X : V → Type*) (mate : ∀ c, X c → V → Prop)

/-- A more detailed obligation for the degree-eight case, following the
exceptional-pattern argument in Lemma 8.4. `X c` must describe actual embedded
occurrences centred at `c`; `mate c x u` retains the particular placement of
the second centre within that occurrence. Neither is identified with the
paper's exceptional configuration until its representation is certified.

`classify` includes the neighbour-selection and degenerate cases needed to
apply Lemma 8.3; that selection is not supplied by the radius argument.
`close` is the joint geometric classification, not an independent choice of
boundary colours in the two patterns. -/
structure EightOverlapSupply : Prop where
  classify : ∀ c, G.degree c = 8 → OnBall G c 1 zero →
    OnBall G c 3 (fun v => G.degree v ≤ 8) →
    Occurs G support valid c 3 ∨ Nonempty (X c)
  next : ∀ c (x : X c), ∃ u ∈ closedBall G c 2, G.degree u = 8 ∧ mate c x u
  close : ∀ c (x : X c) u, mate c x u → X u → Occurs G support valid c 5

variable {G support valid zero}
variable {X mate}

/-- Two overlapping exceptional occurrences suffice once their joint closing
law is established. Recentring transports the actual occurrence support. -/
theorem eight_of_overlap
    (laws : EightOverlapSupply G support valid zero X mate) (c : V)
    (hc : G.degree c = 8) (hz : OnBall G c 3 zero)
    (hd : OnBall G c 5 (fun v => G.degree v ≤ 8)) :
    Occurs G support valid c 5 := by
  rcases laws.classify c hc (hz.mono (by decide)) (hd.mono (by decide)) with direct | exceptional
  · exact direct.mono (by decide)
  · obtain ⟨x⟩ := exceptional
    obtain ⟨u, hu, hu8, placement⟩ := laws.next c x
    rcases laws.classify u hu8 (hz.recenter hu (by decide))
      (hd.recenter hu (by decide)) with direct | exceptional'
    · exact direct.recenter hu
    · obtain ⟨y⟩ := exceptional'
      exact laws.close c x u placement y

/-- The overlap mechanism discharges precisely the degree-eight field;
the two other local supply obligations remain visible. -/
theorem localSupply_of_overlap
    (low : ∀ c, OnBall G c 2 (fun v => G.degree v ≤ 6) →
      Occurs G support valid c 2)
    (seven : ∀ c, G.degree c = 7 → OnBall G c 3 zero →
      OnBall G c 5 (fun v => G.degree v ≤ 7) → Occurs G support valid c 5)
    (overlap : EightOverlapSupply G support valid zero X mate) :
    LocalSupply G support valid zero :=
  ⟨low, seven, eight_of_overlap overlap⟩

/-- A degree-seven centre either uses its own local law or finds a degree-eight
centre within five steps. The latter's whole witness stays within ten steps. -/
theorem seven_or_eight (laws : LocalSupply G support valid zero) (c : V)
    (hc : 7 ≤ G.degree c ∧ G.degree c ≤ 8)
    (hz : OnBall G c 8 zero)
    (hd : OnBall G c 10 (fun v => G.degree v ≤ 8)) :
    Occurs G support valid c 10 := by
  classical
  by_cases h8 : G.degree c = 8
  · exact (laws.eight c h8 (hz.mono (by decide)) (hd.mono (by decide))).mono
      (by decide)
  have h7 : G.degree c = 7 := by omega
  by_cases hsmall : OnBall G c 5 (fun v => G.degree v ≤ 7)
  · exact (laws.seven c h7 (hz.mono (by decide)) hsmall).mono (by decide)
  obtain ⟨u, hu, hdu⟩ : ∃ u ∈ closedBall G c 5, ¬ G.degree u ≤ 7 := by
    simpa only [OnBall, not_forall, not_imp, exists_prop] using hsmall
  have hu8 : G.degree u = 8 := by
    have := hd u (ball_mono G (by decide : 5 ≤ 10) hu)
    omega
  have hl := laws.eight u hu8 (hz.recenter hu (by decide))
    (hd.recenter hu (by decide))
  exact hl.recenter hu

/-- The full bounded-radius assembly. The local classification is supplied
only through `laws`; no complete Four Colour theorem is used. Charge zero
is needed within radius ten, while the degree bound uses radius twelve. -/
theorem radius_twelve (laws : LocalSupply G support valid zero) (c : V)
    (hz : OnBall G c 10 zero)
    (hd : OnBall G c 12 (fun v => G.degree v ≤ 8)) :
    Occurs G support valid c 12 := by
  classical
  by_cases hsmall : OnBall G c 2 (fun v => G.degree v ≤ 6)
  · exact (laws.low c hsmall).mono (by decide)
  obtain ⟨u, hu, hdu⟩ : ∃ u ∈ closedBall G c 2, ¬ G.degree u ≤ 6 := by
    simpa only [OnBall, not_forall, not_imp, exists_prop] using hsmall
  have hu78 : 7 ≤ G.degree u ∧ G.degree u ≤ 8 := by
    have := hd u (ball_mono G (by decide : 2 ≤ 12) hu)
    omega
  have hl := seven_or_eight laws u hu78 (hz.recenter hu (by decide))
    (hd.recenter hu (by decide))
  exact hl.recenter hu

end FourColor.LocalCoverageAssembly
