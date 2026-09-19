import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkInterfaceSupport

/-!
# Exact projection of fork colour profiles

The full-vertex presentation in `GoertzelV24ForkInterfaceSupport` is a useful
semantic intermediate, but a branch decomposition stores only the middle
vertices of each shore. On a cubic piece, every proper presentation away from
that middle set is fixed by the piece: it is either empty or the entire palette.
Thus restriction to the middle set has a unique completion on realized states.

At a fork we complete both child states, check clashes at *all* vertices, merge,
and only then restrict to the parent middle set. In particular, a vertex that
becomes internal at the fork is checked before it disappears from the state.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24ForkProjection

open GoertzelV24ForkInterfaceSupport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev Boundary (inc : E → Finset V) (S : Finset E) :=
  mid inc S → Finset (Fin 3)

/-- Restrict a full presentation to the shore's middle vertices. -/
def restrict (inc : E → Finset V) (S : Finset E)
    (p : V → Finset (Fin 3)) : Boundary inc S :=
  fun v => p v.1

/-- The unique possible full presentation of a realized boundary state. -/
def complete (inc : E → Finset V) (S : Finset E)
    (b : Boundary inc S) : V → Finset (Fin 3) :=
  fun v => if h : v ∈ mid inc S then b ⟨v, h⟩
    else if (S.filter fun e => v ∈ inc e).Nonempty then Finset.univ else ∅

/-- Realized boundary states are exactly restrictions of literal proper
colourings of the piece. -/
def boundarySupport (inc : E → Finset V) (S : Finset E) :
    Finset (Boundary inc S) :=
  (support inc S).image (restrict inc S)

theorem complete_restrict_profile (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (S : Finset E) {c : E → Fin 3} (hc : Proper inc S c) :
    complete inc S (restrict inc S (profile inc S c)) = profile inc S c := by
  funext v
  by_cases hv : v ∈ mid inc S
  · simp [complete, restrict, hv]
  · simp only [complete, dif_neg hv]
    exact (profile_of_not_mem_mid inc hcubic S hc hv).symm

theorem complete_restrict_of_mem (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (S : Finset E) {p : V → Finset (Fin 3)}
    (hp : p ∈ support inc S) :
    complete inc S (restrict inc S p) = p := by
  obtain ⟨c, hc, rfl⟩ := mem_support.mp hp
  exact complete_restrict_profile inc hcubic S hc

theorem mem_boundarySupport (inc : E → Finset V) (S : Finset E)
    {b : Boundary inc S} :
    b ∈ boundarySupport inc S ↔
      ∃ c : E → Fin 3, Proper inc S c ∧
        restrict inc S (profile inc S c) = b := by
  simp [boundarySupport, Finset.mem_image, mem_support]

/-- A single boundary state is one function on the middle set. The total
carrier of *sets* of possible states is its powerset, so its bound has an
additional exponent. This bound concerns one fixed middle-set type; a global
closure also needs coherent relabelling of the middle sets at different cuts. -/
theorem card_boundarySupport_carrier_le (inc : E → Finset V)
    (S : Finset E) (w : Nat) (hwidth : (mid inc S).card ≤ w) :
    Fintype.card (Finset (Boundary inc S)) ≤ 2 ^ (8 ^ w) := by
  calc
    Fintype.card (Finset (Boundary inc S))
        = 2 ^ (8 ^ (mid inc S).card) := by
            simp only [Fintype.card_finset, Fintype.card_fun,
              Fintype.card_coe, Fintype.card_fin]
            norm_num
    _ ≤ 2 ^ (8 ^ w) :=
      Nat.pow_le_pow_right (by decide)
        (Nat.pow_le_pow_right (by decide) hwidth)

/-! ## An executable local leaf generator -/

/-- A one-edge piece has only three possible colour presentations. This
generator ranges over the palette rather than all functions on the ambient
edge set. -/
def leafSupport (inc : E → Finset V) (edge : E) :
    Finset (Boundary inc {edge}) :=
  (Finset.univ : Finset (Fin 3)).image fun colour =>
    restrict inc {edge} (profile inc {edge} (fun _ => colour))

theorem leafSupport_eq_boundarySupport (inc : E → Finset V) (edge : E) :
    leafSupport inc edge = boundarySupport inc {edge} := by
  unfold leafSupport
  ext b
  rw [mem_boundarySupport]
  constructor
  · intro hb
    obtain ⟨colour, -, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨fun _ => colour, ?_, rfl⟩
    intro a ha c hc hne _
    have ha' : a = edge := Finset.mem_singleton.mp ha
    have hc' : c = edge := Finset.mem_singleton.mp hc
    exact (hne (ha'.trans hc'.symm)).elim
  · rintro ⟨c, -, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨c edge, Finset.mem_univ _, ?_⟩
    funext v
    dsimp [restrict, profile]
    apply Finset.image_congr
    intro a ha
    have hae : a = edge := Finset.mem_singleton.mp (Finset.mem_filter.mp ha).1
    simp [hae]

private instance (inc : E → Finset V) (A B : Finset E) :
    DecidablePred (fun pq : Boundary inc A × Boundary inc B =>
      Compatible (complete inc A pq.1) (complete inc B pq.2)) := by
  intro pq
  unfold Compatible
  infer_instance

/-- The exact fork operation on the two *boundary-only* child states. -/
def forkTransition (inc : E → Finset V) (A B : Finset E)
    (left : Finset (Boundary inc A)) (right : Finset (Boundary inc B)) :
    Finset (Boundary inc (A ∪ B)) :=
  ((left ×ˢ right).filter fun pq : Boundary inc A × Boundary inc B =>
      Compatible (complete inc A pq.1) (complete inc B pq.2)).image
    (fun pq => restrict inc (A ∪ B)
      (merge (complete inc A pq.1) (complete inc B pq.2)))

/-- Literal fork colouring semantics, projected to the parent interface.
Compatibility is checked before projection, so an internalized vertex cannot
silently lose a colour clash. -/
theorem forkTransition_exact (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (A B : Finset E) (hAB : Disjoint A B) :
    boundarySupport inc (A ∪ B) =
      forkTransition inc A B (boundarySupport inc A) (boundarySupport inc B) := by
  unfold forkTransition
  ext b
  constructor
  · intro hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    rw [support_union inc A B hAB] at hp
    obtain ⟨⟨pA, pB⟩, hpair, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hproduct, hcompat⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hproduct
    let bA := restrict inc A pA
    let bB := restrict inc B pB
    have hcA : complete inc A bA = pA := complete_restrict_of_mem inc hcubic A hpA
    have hcB : complete inc B bB = pB := complete_restrict_of_mem inc hcubic B hpB
    apply Finset.mem_image.mpr
    refine ⟨(bA, bB), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨pA, hpA, rfl⟩,
         Finset.mem_image.mpr ⟨pB, hpB, rfl⟩⟩
    · simpa [hcA, hcB] using hcompat
    · simp [hcA, hcB]
  · intro hb
    obtain ⟨⟨bA, bB⟩, hpair, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hproduct, hcompat⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hbA, hbB⟩ := Finset.mem_product.mp hproduct
    obtain ⟨pA, hpA, rfl⟩ := Finset.mem_image.mp hbA
    obtain ⟨pB, hpB, rfl⟩ := Finset.mem_image.mp hbB
    have hcA : complete inc A (restrict inc A pA) = pA :=
      complete_restrict_of_mem inc hcubic A hpA
    have hcB : complete inc B (restrict inc B pB) = pB :=
      complete_restrict_of_mem inc hcubic B hpB
    apply Finset.mem_image.mpr
    refine ⟨merge pA pB, ?_, ?_⟩
    · rw [support_union inc A B hAB]
      exact Finset.mem_image.mpr ⟨(pA, pB),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpA, hpB⟩,
          by simpa [hcA, hcB] using hcompat⟩, rfl⟩
    · simp [hcA, hcB]

/-! ## Changing the names of boundary positions -/

section Labelled

variable {I J K : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Read a middle-set state in any chosen order of interface positions. -/
def labelState (inc : E → Finset V) (S : Finset E)
    (label : I ≃ mid inc S) (b : Boundary inc S) : I → Finset (Fin 3) :=
  fun i => b (label i)

def unlabelState (inc : E → Finset V) (S : Finset E)
    (label : I ≃ mid inc S) (word : I → Finset (Fin 3)) : Boundary inc S :=
  fun v => word (label.symm v)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem unlabel_label (inc : E → Finset V) (S : Finset E)
    (label : I ≃ mid inc S) (b : Boundary inc S) :
    unlabelState inc S label (labelState inc S label b) = b := by
  funext v
  simp [unlabelState, labelState]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem label_unlabel (inc : E → Finset V) (S : Finset E)
    (label : I ≃ mid inc S) (word : I → Finset (Fin 3)) :
    labelState inc S label (unlabelState inc S label word) = word := by
  funext i
  simp [unlabelState, labelState]

def labelledSupport (inc : E → Finset V) (S : Finset E)
    (label : I ≃ mid inc S) : Finset (I → Finset (Fin 3)) :=
  (boundarySupport inc S).image (labelState inc S label)

omit [DecidableEq I] in
theorem mem_labelledSupport_iff (inc : E → Finset V) (S : Finset E)
    (label : I ≃ mid inc S) {word : I → Finset (Fin 3)} :
    word ∈ labelledSupport inc S label ↔
      unlabelState inc S label word ∈ boundarySupport inc S := by
  constructor
  · intro hword
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hword
    simpa only [unlabel_label] using hb
  · intro hword
    exact Finset.mem_image.mpr
      ⟨unlabelState inc S label word, hword,
        label_unlabel inc S label word⟩

private instance labelledCompatibleDecidable (inc : E → Finset V)
    (A B : Finset E) (labelA : I ≃ mid inc A) (labelB : J ≃ mid inc B) :
    DecidablePred (fun pq : (I → Finset (Fin 3)) × (J → Finset (Fin 3)) =>
      Compatible (complete inc A (unlabelState inc A labelA pq.1))
        (complete inc B (unlabelState inc B labelB pq.2))) := by
  intro pq
  unfold Compatible
  infer_instance

/-- The same fork operation with arbitrary finite names for each child's and
the parent's boundary positions. -/
def labelledForkTransition (inc : E → Finset V) (A B : Finset E)
    (labelA : I ≃ mid inc A) (labelB : J ≃ mid inc B)
    (labelParent : K ≃ mid inc (A ∪ B))
    (left : Finset (I → Finset (Fin 3)))
    (right : Finset (J → Finset (Fin 3))) :
    Finset (K → Finset (Fin 3)) :=
  ((left ×ˢ right).filter fun pq =>
    Compatible (complete inc A (unlabelState inc A labelA pq.1))
      (complete inc B (unlabelState inc B labelB pq.2))).image fun pq =>
    labelState inc (A ∪ B) labelParent
      (restrict inc (A ∪ B)
        (merge (complete inc A (unlabelState inc A labelA pq.1))
          (complete inc B (unlabelState inc B labelB pq.2))))

/- Renaming interface positions commutes with exact fork transfer. -/
omit [DecidableEq I] [DecidableEq J] [DecidableEq K] in
theorem labelledForkTransition_exact (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (A B : Finset E) (hAB : Disjoint A B)
    (labelA : I ≃ mid inc A) (labelB : J ≃ mid inc B)
    (labelParent : K ≃ mid inc (A ∪ B)) :
    labelledSupport inc (A ∪ B) labelParent =
      labelledForkTransition inc A B labelA labelB labelParent
        (labelledSupport inc A labelA) (labelledSupport inc B labelB) := by
  ext word
  rw [mem_labelledSupport_iff, forkTransition_exact inc hcubic A B hAB]
  unfold forkTransition labelledForkTransition
  constructor
  · intro hword
    obtain ⟨⟨bA, bB⟩, hpair, hresult⟩ := Finset.mem_image.mp hword
    obtain ⟨hproduct, hcompat⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hbA, hbB⟩ := Finset.mem_product.mp hproduct
    apply Finset.mem_image.mpr
    refine ⟨(labelState inc A labelA bA, labelState inc B labelB bB), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact (mem_labelledSupport_iff inc A labelA).mpr
          (by simpa only [unlabel_label] using hbA)
      · exact (mem_labelledSupport_iff inc B labelB).mpr
          (by simpa only [unlabel_label] using hbB)
      · simpa only [unlabel_label] using hcompat
    · simpa only [unlabel_label, label_unlabel] using
        congrArg (labelState inc (A ∪ B) labelParent) hresult
  · intro hword
    obtain ⟨⟨wordA, wordB⟩, hpair, hresult⟩ := Finset.mem_image.mp hword
    obtain ⟨hproduct, hcompat⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hwordA, hwordB⟩ := Finset.mem_product.mp hproduct
    have hbA := (mem_labelledSupport_iff inc A labelA).mp hwordA
    have hbB := (mem_labelledSupport_iff inc B labelB).mp hwordB
    apply Finset.mem_image.mpr
    refine ⟨(unlabelState inc A labelA wordA,
      unlabelState inc B labelB wordB), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hbA, hbB⟩, hcompat⟩
    · simpa only [label_unlabel, unlabel_label] using
        congrArg (unlabelState inc (A ∪ B) labelParent) hresult

end Labelled

section ForgettingControl

open GoertzelV24ForkInterfaceSupport

private def clashColour : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 2]

private theorem clashColour_left : Proper K4 leftPiece clashColour := by decide +kernel

private theorem clashColour_right : Proper K4 rightPiece clashColour := by decide +kernel

/-- The parent of the `K4` fork has no middle vertices, yet two realized
child states clash at a vertex that has become internal. Checking only after
restriction to the parent boundary would accept this spurious pair. -/
theorem K4_forgotten_vertex_clash :
    mid K4 (leftPiece ∪ rightPiece) = ∅ ∧
      ∃ bL ∈ boundarySupport K4 leftPiece,
        ∃ bR ∈ boundarySupport K4 rightPiece,
          ¬ Compatible (complete K4 leftPiece bL)
              (complete K4 rightPiece bR) := by
  constructor
  · rw [pieces_cover]
    decide +kernel
  · let bL := restrict K4 leftPiece (profile K4 leftPiece clashColour)
    let bR := restrict K4 rightPiece (profile K4 rightPiece clashColour)
    refine ⟨bL, ?_, bR, ?_, ?_⟩
    · exact (mem_boundarySupport K4 leftPiece).mpr
        ⟨clashColour, clashColour_left, rfl⟩
    · exact (mem_boundarySupport K4 rightPiece).mpr
        ⟨clashColour, clashColour_right, rfl⟩
    · have hclash : ¬ Compatible (profile K4 leftPiece clashColour)
          (profile K4 rightPiece clashColour) := by
        intro hcompat
        have hleft : (0 : Fin 3) ∈ profile K4 leftPiece clashColour (1 : Fin 4) := by
          decide +kernel
        have hright : (0 : Fin 3) ∈ profile K4 rightPiece clashColour (1 : Fin 4) := by
          decide +kernel
        exact (Finset.disjoint_left.mp (hcompat 1) hleft) hright
      simpa only [bL, bR,
        complete_restrict_profile K4 K4_cubic leftPiece clashColour_left,
        complete_restrict_profile K4 K4_cubic rightPiece clashColour_right] using hclash

end ForgettingControl

end Mettapedia.GraphTheory.FourColor.GoertzelV24ForkProjection
