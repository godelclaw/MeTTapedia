import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkInterfaceSupport

/-!
# Gluing chosen edge-colouring witnesses

The support fork law forgets which witness realizes a profile. Here the
same incidence semantics is used to glue a specified pair of witnesses,
retaining their colours on the two disjoint edge shores.
-/

namespace Mettapedia.GraphTheory.FourColor.EdgeColouringGluing

open GoertzelV24ForkInterfaceSupport

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable (inc : E → Finset V) (A B : Finset E)

omit [DecidableEq E] in
/-- All cross-shore constraints, expressed through the existing profiles. -/
theorem compatible_iff (a b : E → Fin 3) :
    Compatible (profile inc A a) (profile inc B b) ↔
      ∀ x ∈ A, ∀ y ∈ B, (inc x ∩ inc y).Nonempty → a x ≠ b y := by
  constructor
  · intro h x hx y hy hmeet heq
    obtain ⟨v, hv⟩ := hmeet
    apply Finset.disjoint_left.mp (h v)
      (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, (Finset.mem_inter.mp hv).1⟩, rfl⟩)
    exact Finset.mem_image.mpr
      ⟨y, Finset.mem_filter.mpr ⟨hy, (Finset.mem_inter.mp hv).2⟩, heq.symm⟩
  · intro h v
    apply Finset.disjoint_left.mpr
    intro colour ha hb
    obtain ⟨x, hx, hxc⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, hyc⟩ := Finset.mem_image.mp hb
    obtain ⟨hxA, hvx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyB, hvy⟩ := Finset.mem_filter.mp hy
    exact h x hxA y hyB ⟨v, Finset.mem_inter.mpr ⟨hvx, hvy⟩⟩ (hxc.trans hyc.symm)

/-- The original colour functions may be arbitrary away from their shores. -/
def glue (a b : E → Fin 3) : E → Fin 3 := fun x => if x ∈ A then a x else b x

theorem glue_left (a b : E → Fin 3) {x : E} (hx : x ∈ A) :
    glue A a b x = a x := by simp [glue, hx]

theorem glue_right (hAB : Disjoint A B) (a b : E → Fin 3) {x : E} (hx : x ∈ B) :
    glue A a b x = b x := by simp [glue, Finset.disjoint_right.mp hAB hx]

/-- A selected pair of witnesses glues if and only if both are proper and
their profiles are compatible. The result retains every old edge colour. -/
theorem glue_proper_iff (hAB : Disjoint A B) (a b : E → Fin 3) :
    Proper inc (A ∪ B) (glue A a b) ↔
      Proper inc A a ∧ Proper inc B b ∧ Compatible (profile inc A a) (profile inc B b) := by
  constructor
  · intro h
    refine ⟨?_, ?_, (compatible_iff inc A B a b).mpr ?_⟩
    · intro x hx y hy hxy hmeet
      have hh := h x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy) hxy hmeet
      simpa only [glue_left A a b hx, glue_left A a b hy] using hh
    · intro x hx y hy hxy hmeet
      have hh := h x (Finset.mem_union_right _ hx) y (Finset.mem_union_right _ hy) hxy hmeet
      simpa only [glue_right A B hAB a b hx, glue_right A B hAB a b hy] using hh
    · intro x hx y hy hmeet
      have hxy : x ≠ y := by
        rintro rfl
        exact Finset.disjoint_left.mp hAB hx hy
      have hh := h x (Finset.mem_union_left _ hx) y (Finset.mem_union_right _ hy) hxy hmeet
      simpa only [glue_left A a b hx, glue_right A B hAB a b hy] using hh
  · rintro ⟨ha, hb, hab⟩ x hx y hy hxy hmeet
    have cross := (compatible_iff inc A B a b).mp hab
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · simpa only [glue_left A a b hx, glue_left A a b hy] using ha x hx y hy hxy hmeet
    · simpa only [glue_left A a b hx, glue_right A B hAB a b hy] using cross x hx y hy hmeet
    · have hm : (inc y ∩ inc x).Nonempty := by rwa [Finset.inter_comm]
      simpa only [glue_right A B hAB a b hx, glue_left A a b hy] using (cross y hy x hx hm).symm
    · simpa only [glue_right A B hAB a b hx, glue_right A B hAB a b hy] using hb x hx y hy hxy hmeet

omit [DecidableEq E] in
/-- Outside-shore values play no role in the retained profile. -/
theorem profile_congr (a b : E → Fin 3) (h : ∀ x ∈ A, a x = b x) :
    profile inc A a = profile inc A b := by
  funext v
  apply Finset.image_congr
  intro x hx
  exact h x (Finset.mem_filter.mp hx).1

theorem profile_glue (hAB : Disjoint A B) (a b : E → Fin 3) :
    profile inc (A ∪ B) (glue A a b) = merge (profile inc A a) (profile inc B b) := by
  rw [profile_union,
    profile_congr inc A (glue A a b) a (fun _ hx => glue_left A a b hx),
    profile_congr inc B (glue A a b) b (fun _ hx => glue_right A B hAB a b hx)]

end Mettapedia.GraphTheory.FourColor.EdgeColouringGluing
