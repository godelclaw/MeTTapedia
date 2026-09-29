import MettapediaFourColor.KempeChordMasks

/-!
# Projecting a Kempe exterior to selected chords

Give every opening bracket its position as a label and copy that label to its
closing bracket. A Boolean choice of labels selects whole chords. Projecting
to the masks of selected anchors forgets every other chord while retaining
whether two anchors share a chord and how their partners are coupled.

The reconstruction law holds at arbitrary boundary length. The finite diamond
consumers classify the projected signatures, rather than colour-decorated
exterior chromograms. The action is the classical Kempe exchange action.
-/

namespace FourColor.KempeAnchorProjection

open KempeChordMasks

/-- The two ends of a chord receive its opening position as their common label. -/
def labels : ℕ → List ℕ → List Bool → List ℕ
  | _, _, [] => []
  | k, stack, true :: ds => k :: labels (k + 1) (k :: stack) ds
  | k, a :: stack, false :: ds => a :: labels (k + 1) stack ds
  | _, [], false :: _ => []

/-- Any choice of labels exchanges complete chords of a balanced skeleton. -/
theorem labels_paired (choose : ℕ → Bool) :
    ∀ (ds : List Bool) (k : ℕ) (stack : List ℕ),
      KempeChordMasks.balanced stack.length ds = true →
      paired (stack.map choose) ((labels k stack ds).map choose) ds = true := by
  intro ds
  induction ds with
  | nil =>
    intro k stack h
    cases stack <;> simp_all [KempeChordMasks.balanced, labels, paired]
  | cons d ds ih =>
    intro k stack h
    cases d with
    | true => simpa [labels, paired] using ih (k + 1) (k :: stack) h
    | false =>
      cases stack with
      | nil => simp [KempeChordMasks.balanced] at h
      | cons a stack => simpa [labels, paired] using ih (k + 1) stack h

/-- Paired masks are closed under selecting either of their chord sets. -/
theorem paired_or : ∀ (ds : List Bool) (s t a b : List Bool),
    paired s a ds = true → paired t b ds = true →
    paired (List.zipWith (· || ·) s t) (List.zipWith (· || ·) a b) ds = true := by
  intro ds
  induction ds with
  | nil =>
    intro s t a b ha hb
    cases a <;> cases b <;> cases s <;> cases t <;> simp_all [paired]
  | cons d ds ih =>
    intro s t a b ha hb
    cases a with
    | nil => cases d <;> cases s <;> simp [paired] at ha
    | cons x a =>
      cases b with
      | nil => cases d <;> cases t <;> simp [paired] at hb
      | cons y b =>
        cases d with
        | true => simpa [paired] using ih (x :: s) (y :: t) a b ha hb
        | false =>
          cases s with
          | nil => simp [paired] at ha
          | cons u s =>
            cases t with
            | nil => simp [paired] at hb
            | cons v t =>
              simp only [paired, Bool.and_eq_true, beq_iff_eq] at ha hb
              obtain ⟨rfl, ha⟩ := ha
              obtain ⟨rfl, hb⟩ := hb
              simpa [paired] using ih s t a b ha hb

/-- One complete-chord mask per anchor, retaining the order and any aliases. -/
def project (ds : List Bool) (anchors : List ℕ) : List (List Bool) :=
  let ls := labels 0 [] ds
  anchors.map fun a => ls.map fun l => l == ls[a]?.getD 0

theorem project_paired (ds : List Bool) (anchors : List ℕ)
    (h : KempeChordMasks.balanced 0 ds = true) :
    ∀ m ∈ project ds anchors, paired [] m ds = true := by
  intro m hm
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
  exact labels_paired (fun l => l == (labels 0 [] ds)[a]?.getD 0) ds 0 [] h

/-- Exchange one selected chord or the union of two, including aliased anchors. -/
def exchanges : List (List Bool) → List (List Bool)
  | [] => []
  | m :: ms => m :: (ms.map (List.zipWith (· || ·) m) ++ exchanges ms)

theorem exchanges_paired (ds : List Bool) (ms : List (List Bool))
    (h : ∀ m ∈ ms, paired [] m ds = true) :
    ∀ m ∈ exchanges ms, paired [] m ds = true := by
  induction ms with
  | nil => simp [exchanges]
  | cons m ms ih =>
    intro a ha
    simp only [exchanges, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ha | ha
    · exact h a (by simp)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact paired_or ds [] [] m b (h m (by simp)) (h b (by simp [hb]))
    · exact ih (fun b hb => h b (by simp [hb])) a ha

/-- All unsigned words of a given length; invalid bracket words are filtered later. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

theorem mem_words (ds : List Bool) : ds ∈ words ds.length := by
  induction ds with
  | nil => simp [words]
  | cons d ds ih => cases d <;> simp [words, ih]

/-- Distinct joint signatures; unobserved exterior chords have been eliminated. -/
def signatures (n : ℕ) (anchors : List ℕ) : List (List (List Bool)) :=
  (((words n).filter (KempeChordMasks.balanced 0)).map (fun ds => project ds anchors)).eraseDups

theorem signature_mem (ds : List Bool) (anchors : List ℕ)
    (h : KempeChordMasks.balanced 0 ds = true) :
    project ds anchors ∈ signatures ds.length anchors := by
  simp only [signatures, List.mem_eraseDups, List.mem_map, List.mem_filter]
  exact ⟨ds, ⟨mem_words ds, h⟩, rfl⟩

/-- Every joint signature offers an accepted one- or two-chord exchange. -/
def coverCheck (et : List Color) (anchors : List ℕ) (answers : List (List Color)) : Bool :=
  anchors.all (fun a => decide (a < (active et).length)) &&
    (signatures (active et).length anchors).all fun signature =>
      (exchanges signature).any fun m => answers.contains (recolor m et)

/-- Projected joint coverage reconstructs an answer through the original exterior. -/
theorem coverCheck_sound (et : List Color) (anchors : List ℕ)
    (answers : List (List Color)) (hc : coverCheck et anchors answers = true)
    (w : Chromogram) (hm : matchg [] et w) :
    ∃ answer ∈ answers, matchg [] answer w := by
  obtain ⟨hb, hl⟩ := matched_skeleton w et [] hm
  have hs := signature_mem (skeleton w) anchors hb
  rw [hl] at hs
  rw [coverCheck, Bool.and_eq_true] at hc
  have hall := hc.2
  obtain ⟨m, hmem, ha⟩ := List.any_eq_true.mp (List.all_eq_true.mp hall _ hs)
  refine ⟨recolor m et, (by simpa using ha), ?_⟩
  exact recolor_matches w et m [] [] hm
    (exchanges_paired _ _ (project_paired _ _ hb) m hmem)

end FourColor.KempeAnchorProjection
