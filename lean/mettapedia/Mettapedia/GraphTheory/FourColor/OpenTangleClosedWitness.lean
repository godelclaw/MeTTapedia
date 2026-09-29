import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryView
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationDartColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Closed sewing with independent carrier universes

The exact closed boundary contract retains a colouring of each piece and
agreement at every matched half-edge. Restriction and reconstruction operate
on actual darts. The two pieces may have different vertex and dart carriers.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24RotationDartColoring GoertzelV24TwoEdgeCutMinimality
open TwoSidedOpenTangleData

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V I B W J L R : Type*}

def IsColor (O : OpenTangleData V I B) (c : I ⊕ B → Color) : Prop :=
  (∀ i, c (.inl (O.interiorAlpha i)) = c (.inl i)) ∧
  (∀ {d e}, O.vertOf d = O.vertOf e → d ≠ e → c d ≠ c e) ∧
  ∀ d, c d ≠ 0

variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (O : OpenTangleData V I B) (P : TwoSidedOpenTangleData W J L R) (m : B ≃ L ⊕ R)

abbrev sewn := O.composeRotationSystem (asOpen P) m

theorem sewn_vert (x : (I ⊕ B) ⊕ (J ⊕ (L ⊕ R))) :
    (sewn O P m).vertOf (composeDartEquiv x) =
      Sum.elim (Sum.inl ∘ O.vertOf) (Sum.inr ∘ (asOpen P).vertOf) x := by
  rcases x with (i | b) | (j | p) <;> rfl

private theorem physical_proper {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (T : RotationSystem X Y) (c : T.EdgeColoring Color)
    {a b : T.D} (hv : T.vertOf a = T.vertOf b) (hne : a ≠ b) :
    c (T.edgeOf a) ≠ c (T.edgeOf b) := by
  apply c.valid
  apply T.edgeAdjacencyGraph_adj_iff.mpr
  refine ⟨?_, T.vertOf a, ?_, ?_⟩
  · intro he
    exact hne (T.edgeOf_injOn_dartsAt (T.vertOf a)
      (by simp [RotationSystem.dartsAt]) (by simp [RotationSystem.dartsAt, hv]) he)
  · exact T.mem_endpoints_iff.mpr ⟨a, T.mem_dartsOn.mpr rfl, rfl⟩
  · exact T.mem_endpoints_iff.mpr ⟨b, T.mem_dartsOn.mpr rfl, hv.symm⟩

section Open
variable {C : Type*} [Fintype C] [DecidableEq C]
  (Q : OpenTangleData W J C) (s : B ≃ C)

/-- Closed sewing of two ordinary open tangles. -/
abbrev sewnOpen := O.composeRotationSystem Q s

theorem sewnOpen_vert (x : (I ⊕ B) ⊕ (J ⊕ C)) :
    (sewnOpen O Q s).vertOf (composeDartEquiv x) =
      Sum.elim (Sum.inl ∘ O.vertOf) (Sum.inr ∘ Q.vertOf) x := by
  rcases x with (i | b) | (j | p) <;> rfl

/-- Restrict a genuine physical colouring to both pieces, retaining the joint
boundary equation. -/
theorem restrictOpen (c : (sewnOpen O Q s).EdgeColoring Color)
    (hc : (sewnOpen O Q s).IsTaitEdgeColoring c) :
    ∃ l r, IsColor O l ∧ IsColor Q r ∧
      (∀ b, l (.inr b) = r (.inr (s b))) ∧
      (∀ d, l d = c ((sewnOpen O Q s).edgeOf (composeDartEquiv (.inl d)))) := by
  let l := fun d => c ((sewnOpen O Q s).edgeOf (composeDartEquiv (.inl d)))
  let r := fun d => c ((sewnOpen O Q s).edgeOf (composeDartEquiv (.inr d)))
  refine ⟨l, r, ⟨?_, ?_, fun _ => hc _⟩, ⟨?_, ?_, fun _ => hc _⟩, ?_, fun _ => rfl⟩
  · intro i
    exact congrArg c ((sewnOpen O Q s).edge_alpha (.inl (.inl i)))
  · intro a b hv hne
    apply physical_proper (sewnOpen O Q s) c
    · simp only [sewnOpen_vert, Sum.elim_inl, Function.comp_apply, hv]
    · exact fun h => hne (Sum.inl.inj (composeDartEquiv.injective h))
  · intro j
    exact congrArg c ((sewnOpen O Q s).edge_alpha (.inl (.inr j)))
  · intro a b hv hne
    apply physical_proper (sewnOpen O Q s) c
    · simp only [sewnOpen_vert, Sum.elim_inr, Function.comp_apply, hv]
    · exact fun h => hne (Sum.inr.inj (composeDartEquiv.injective h))
  · intro b
    exact (congrArg c ((sewnOpen O Q s).edge_alpha (.inr (.inl b)))).symm

/-- Compatible witnesses reconstruct a physical colouring. Every exterior
dart reads back its original colour, including darts meeting the seam. -/
theorem glueOpen (l : I ⊕ B → Color) (r : J ⊕ C → Color)
    (hl : IsColor O l) (hr : IsColor Q r)
    (hm : ∀ b, l (.inr b) = r (.inr (s b))) :
    ∃ c : (sewnOpen O Q s).EdgeColoring Color,
      (sewnOpen O Q s).IsTaitEdgeColoring c ∧
      ∀ d, c ((sewnOpen O Q s).edgeOf (composeDartEquiv (.inl d))) = l d := by
  let f : (sewnOpen O Q s).D → Color := Sum.elim l r ∘ composeDartEquiv.symm
  have hf (x) : f (composeDartEquiv x) = Sum.elim l r x :=
    congrArg (Sum.elim l r) (composeDartEquiv.symm_apply_apply x)
  have ha : ∀ d, f ((sewnOpen O Q s).alpha d) = f d := by
    rintro ((i | j) | (b | p))
    · exact hl.1 i
    · exact hr.1 j
    · exact (hm b).symm
    · change l (.inr (s.symm p)) = r (.inr p)
      simpa only [Equiv.apply_symm_apply] using hm (s.symm p)
  have hp : ∀ {a b}, (sewnOpen O Q s).vertOf a = (sewnOpen O Q s).vertOf b →
      a ≠ b → f a ≠ f b := by
    intro a b hv hne
    obtain ⟨x, rfl⟩ := composeDartEquiv.surjective a
    obtain ⟨y, rfl⟩ := composeDartEquiv.surjective b
    rw [sewnOpen_vert, sewnOpen_vert] at hv
    rw [hf, hf]
    rcases x with x | x <;> rcases y with y | y
    · exact hl.2.1 (Sum.inl.inj hv) (fun h => hne (congrArg _ (congrArg Sum.inl h)))
    · exact (Sum.inl_ne_inr hv).elim
    · exact (Sum.inr_ne_inl hv).elim
    · apply hr.2.1
      · exact Sum.inr.inj hv
      · exact fun h => hne (congrArg _ (congrArg Sum.inr h))
  refine ⟨edgeColoringOfDartColor (sewnOpen O Q s) f ha hp,
    edgeColoringOfDartColor_isTait (sewnOpen O Q s) f ha hp ?_, ?_⟩
  · intro d
    obtain ⟨x | x, rfl⟩ := composeDartEquiv.surjective d
    · rw [hf]
      exact hl.2.2 x
    · rw [hf]
      exact hr.2.2 x
  · intro d
    rw [edgeColoringOfDartColor_edgeOf]
    exact hf (.inl d)

end Open

/-- The serial view consumes the ordinary open-tangle restriction without
changing any colouring witness. -/
theorem restrict (c : (sewn O P m).EdgeColoring Color)
    (hc : (sewn O P m).IsTaitEdgeColoring c) :
    ∃ l r, IsColor O l ∧ P.IsTaitColoring r ∧
      (∀ b, l (.inr b) = r (.inr (m b))) ∧
      (∀ d, l d = c ((sewn O P m).edgeOf (composeDartEquiv (.inl d)))) := by
  obtain ⟨l, r, hl, hr, hm, he⟩ := restrictOpen O (asOpen P) m c hc
  exact ⟨l, r, hl, (asOpen_tait_iff P r).mp hr, hm, he⟩

/-- The serial view consumes ordinary open-tangle reconstruction. -/
theorem glue (l : I ⊕ B → Color) (r : P.Coloring)
    (hl : IsColor O l) (hr : P.IsTaitColoring r)
    (hm : ∀ b, l (.inr b) = r (.inr (m b))) :
    ∃ c : (sewn O P m).EdgeColoring Color,
      (sewn O P m).IsTaitEdgeColoring c ∧
      ∀ d, c ((sewn O P m).edgeOf (composeDartEquiv (.inl d))) = l d :=
  glueOpen O (asOpen P) m l r hl ((asOpen_tait_iff P r).mpr hr) hm

variable {W' J' : Type*} [Fintype W'] [DecidableEq W'] [Fintype J'] [DecidableEq J']

/-- A sound boundary-witness replacement acts inside any fixed exterior. -/
theorem replace (Q : TwoSidedOpenTangleData W' J' L R)
    (hs : ∀ x y, P.AcceptsBoundaryWords x y → Q.AcceptsBoundaryWords x y)
    (c : (sewn O P m).EdgeColoring Color) (hc : (sewn O P m).IsTaitEdgeColoring c) :
    ∃ c' : (sewn O Q m).EdgeColoring Color, (sewn O Q m).IsTaitEdgeColoring c' ∧
      ∀ d, c' ((sewn O Q m).edgeOf (composeDartEquiv (.inl d))) =
        c ((sewn O P m).edgeOf (composeDartEquiv (.inl d))) := by
  obtain ⟨l, r, hl, hr, hm, hleft⟩ := restrict O P m c hc
  obtain ⟨s, hs, hx, hy⟩ := hs _ _ ⟨r, hr, rfl, rfl⟩
  have hb (p : L ⊕ R) : s (.inr p) = r (.inr p) := by
    cases p with
    | inl a => exact congrFun hx a
    | inr a => exact congrFun hy a
  obtain ⟨c', hc', hd⟩ := glue O Q m l s hl hs (fun b => (hm b).trans (hb (m b)).symm)
  exact ⟨c', hc', fun d => (hd d).trans (hleft d)⟩

theorem colorable_iff (Q : TwoSidedOpenTangleData W' J' L R)
    (hs : ∀ x y, P.AcceptsBoundaryWords x y ↔ Q.AcceptsBoundaryWords x y) :
    RotationSystemTaitColorable (sewn O P m) ↔ RotationSystemTaitColorable (sewn O Q m) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c', hc', _⟩ := replace O P m Q (fun x y => (hs x y).mp) c hc
    exact ⟨c', hc'⟩
  · rintro ⟨c, hc⟩
    obtain ⟨c', hc', _⟩ := replace O Q m P (fun x y => (hs x y).mpr) c hc
    exact ⟨c', hc'⟩

end
end Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness
