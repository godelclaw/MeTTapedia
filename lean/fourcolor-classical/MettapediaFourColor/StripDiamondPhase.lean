import MettapediaFourColor.StripEndPhase

/-! # Extending the repaired end triangle to the adjacent diamond

For a proper boundary, failure to add core vertex 2 to the restored
triangle has three local equality patterns. Two anchored exchanges handle
all partners. The choices at the shared edge remain joint witnesses.
Only core vertices 0, 1, 2 and 3 are restored here.
-/

namespace FourColor.StripDiamondPhase

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension
open StripPartialColouring KempeBoundarySplit

def Diamond (x y z u v w : Color) : Prop :=
  ∃ a d e c : Color,
    (a ≠ u ∧ a ≠ v ∧ a ≠ w) ∧
    (d ≠ y ∧ d ≠ z ∧ d ≠ u) ∧ e ≠ w ∧ (c ≠ x ∧ c ≠ y) ∧
    a ≠ d ∧ a ≠ e ∧ d ≠ e ∧ d ≠ c ∧ e ≠ c

instance (x y z u v w : Color) : Decidable (Diamond x y z u v w) := by
  unfold Diamond
  infer_instance

def Good (b : Boundary) : Prop := ∃ a c, r1 b a c
instance (b : Boundary) : Decidable (Good b) := by unfold Good; infer_instance

theorem good_iff (b : Boundary) : Good b ↔ Diamond (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) := by
  constructor
  · rintro ⟨e,c,he,hc,hec,d,hd,hr0,hdc⟩
    rcases hr0 with ⟨_,_,hed,a,ha,hea,had⟩
    exact ⟨a,d,e,c,by simpa [unary, attachments] using ha,
      by simpa [unary, attachments] using hd,
      by simpa [unary, attachments] using he,
      by simpa [unary, attachments] using hc,had,hea.symm,hed.symm,hdc,hec⟩
  · rintro ⟨a,d,e,c,ha,hd,he,hc,had,hae,hde,hdc,hec⟩
    have hu1 : unary b 1 e := by simpa [unary, attachments] using he
    have hu3 : unary b 3 d := by simpa [unary, attachments] using hd
    exact ⟨e,c,hu1,by simpa [unary, attachments] using hc,hec,d,hu3,
      ⟨hu1,hu3,hde.symm,a,by simpa [unary, attachments] using ha,hae.symm,had⟩,hdc⟩

/-- The first disjunct has two choices of the final port; the second has one. -/
def Pattern (x y z u v w : Color) : Prop :=
  (z = x ∧ (w = x ∨ w = y) ∧ x ≠ y ∧ x ≠ u ∧ x ≠ v ∧
    y ≠ u ∧ y ≠ v ∧ u ≠ v) ∨
  (u = x ∧ v = z ∧ w = x ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z)

instance (x y z u v w : Color) : Decidable (Pattern x y z u v w) := by
  unfold Pattern
  infer_instance

/-- Six consecutive observations suffice to classify every failed extension. -/
theorem classify : ∀ x y z u v w,
    x ≠ y → y ≠ z → z ≠ u → u ≠ v → v ≠ w →
    StripEndPhase.End y z u v w → ¬ Diamond x y z u v w → Pattern x y z u v w := by
  simp only [← and_imp]
  decide +kernel

def anchor (b : Boundary) : Fin 11 := if b 8 = b 3 then 4 else 3
def difference (b : Boundary) : Color :=
  if b 8 = b 3 then b 4 + b 6 else b 3 + b 6
def inside (a j i : Fin 11) : Bool := decide (min a j < i ∧ i ≤ max a j)
def update (b : Boundary) (j : Fin 11) (i : Fin 11) : Color :=
  if inside (anchor b) j i then difference b + b i else b i

private def localBoundary (x y z u v w : Color) : Boundary :=
  ![c0,c0,c0,x,y,z,u,v,w,c0,c0]

theorem local_active : ∀ x y z u v w, Pattern x y z u v w →
    let b := localBoundary x y z u v w
    difference b ≠ 0 ∧ StripEndPhase.word b (anchor b) ≠ difference b := by
  decide +kernel

/-- No condition on the position or colour of the partner is needed. -/
theorem local_release : ∀ x y z u v w, Pattern x y z u v w →
    ∀ j : Fin 11, j ≠ anchor (localBoundary x y z u v w) →
      let b := update (localBoundary x y z u v w) j
      Diamond (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) := by
  decide +kernel

theorem pattern (b : Boundary) (hb : ProperBoundary b)
    (left : StripEndPhase.Good b) (bad : ¬ Good b) :
    Pattern (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) := by
  exact classify _ _ _ _ _ _ (hb 3 4 (by decide)) (hb 4 5 (by decide))
    (hb 5 6 (by decide)) (hb 6 7 (by decide)) (hb 7 8 (by decide))
    ((StripEndPhase.good_iff b).mp left) (fun h => bad ((good_iff b).mpr h))

theorem active (b : Boundary) (h : Pattern (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)) :
    difference b ≠ 0 ∧ StripEndPhase.word b (anchor b) ≠ difference b := by
  have hh := local_active _ _ _ _ _ _ h
  by_cases eq : b 8 = b 3
  · simpa [localBoundary, difference, anchor, StripEndPhase.word, StripEndPhase.next, eq] using hh
  · simpa [localBoundary, difference, anchor, StripEndPhase.word, StripEndPhase.next, eq] using hh

theorem release (b : Boundary) (hb : ProperBoundary b) (left : StripEndPhase.Good b)
    (bad : ¬ Good b) (j : Fin 11) (hj : j ≠ anchor b) : Good (update b j) := by
  rw [good_iff]
  have hp := pattern b hb left bad
  have hj' : j ≠ anchor (localBoundary (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)) := by
    by_cases eq : b 8 = b 3 <;> simpa [anchor, localBoundary, eq] using hj
  by_cases eq : b 8 = b 3 <;>
    simpa [localBoundary, update, anchor, difference, eq] using local_release _ _ _ _ _ _ hp j hj'

end FourColor.StripDiamondPhase
