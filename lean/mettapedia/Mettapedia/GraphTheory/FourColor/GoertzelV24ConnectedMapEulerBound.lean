import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBondBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24InvolutionEdgeList
import Mettapedia.GraphTheory.Hypermap.Connectivity
import Mettapedia.GraphTheory.Hypermap.Euler

/-!
# Euler's inequality for a connected rotation map

The generic permutation Euler bound counts components by word reachability
and edges by the length of an involution presentation.  This file identifies
those two quantities for an ordinary connected rotation system:

* the canonical edge list of a fixed-point-free involution has one entry per
  edge orbit;
* primal connectedness together with cyclic vertex rotations makes the word
  action transitive.

Consequently a connected rotation map satisfies `V + F ≤ E + 2` directly at
the orbit-count level.  The result is useful beyond the hub application that
motivated it.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedMapEulerBound

open Equiv Equiv.Perm
open GoertzelV24FaceDualConnectedness
open GoertzelV24InvolutionEdgeList
open GoertzelV24MapEulerBound
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24WordReachability

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Length of the canonical involution presentation -/

/-- Stripping the two-cycle through `a` removes exactly its two points from
the moved set. -/
theorem movedFinset_strip_eq_erase_erase
    (α : Perm D) (a : D) (hinv : Function.Involutive α) :
    movedFinset (Equiv.swap a (α a) * α) =
      ((movedFinset α).erase a).erase (α a) := by
  ext x
  simp only [mem_movedFinset, Finset.mem_erase]
  constructor
  · intro hmoved
    have hxa : x ≠ a := by
      intro h
      subst x
      exact hmoved (strip_apply_left α a)
    have hxb : x ≠ α a := by
      intro h
      subst x
      exact hmoved (strip_apply_right α a hinv)
    have halpha : α x ≠ x := by
      by_contra hfixed
      have hstrip := strip_apply_of_ne α a x hinv hxa hxb
      exact hmoved (hstrip.trans hfixed)
    exact ⟨hxb, hxa, halpha⟩
  · rintro ⟨hxb, hxa, halpha⟩
    rw [strip_apply_of_ne α a x hinv hxa hxb]
    exact halpha

/-- A genuine stripped two-cycle lowers the moved-set cardinality by two. -/
theorem card_movedFinset_strip_add_two
    (α : Perm D) (a : D) (hinv : Function.Involutive α)
    (ha : α a ≠ a) :
    (movedFinset (Equiv.swap a (α a) * α)).card + 2 =
      (movedFinset α).card := by
  have haMem : a ∈ movedFinset α := mem_movedFinset.mpr ha
  have hαaMem : α a ∈ movedFinset α := by
    apply mem_movedFinset.mpr
    rw [hinv a]
    exact ha.symm
  have hαaNe : α a ≠ a := ha
  have htwo : 2 ≤ (movedFinset α).card := by
    have hsubset : ({a, α a} : Finset D) ⊆ movedFinset α := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haMem
      · exact hαaMem
    have hcard := Finset.card_le_card hsubset
    simpa [ha, ha.symm] using hcard
  rw [movedFinset_strip_eq_erase_erase α a hinv]
  rw [Finset.card_erase_of_mem
    (Finset.mem_erase.mpr ⟨hαaNe, hαaMem⟩)]
  rw [Finset.card_erase_of_mem haMem]
  omega

/-- With enough fuel, the canonical edge-list length is half the moved-set
cardinality. -/
theorem two_mul_length_edgeListAux_eq_card_movedFinset (fuel : Nat) :
    ∀ α : Perm D, Function.Involutive α →
      (movedFinset α).card ≤ fuel →
      2 * (edgeListAux fuel α).length = (movedFinset α).card := by
  induction fuel with
  | zero =>
      intro α _ hcard
      have hzero : (movedFinset α).card = 0 := by omega
      simp [edgeListAux, hzero]
  | succ fuel ih =>
      intro α hinv hcard
      by_cases h : ∃ x, α x ≠ x
      · let a := h.choose
        have ha : α a ≠ a := h.choose_spec
        let stripped := Equiv.swap a (α a) * α
        have hstripInv : Function.Involutive stripped := by
          intro x
          by_cases hxa : x = a
          · subst x
            rw [strip_apply_left α a, strip_apply_left α a]
          by_cases hxb : x = α a
          · subst x
            rw [strip_apply_right α a hinv,
              strip_apply_right α a hinv]
          · rw [strip_apply_of_ne α a x hinv hxa hxb]
            have h1 : α x ≠ a := by
              intro heq
              apply hxb
              rw [← heq, hinv x]
            have h2 : α x ≠ α a := by
              intro heq
              exact hxa (α.injective heq)
            rw [strip_apply_of_ne α a (α x) hinv h1 h2, hinv x]
        have hcardDrop := card_movedFinset_strip_add_two α a hinv ha
        have hstripCard : (movedFinset stripped).card ≤ fuel := by
          dsimp only [stripped]
          omega
        have hrec := ih stripped hstripInv hstripCard
        rw [show edgeListAux (fuel + 1) α =
            (a, α a) :: edgeListAux fuel stripped by
          simp only [edgeListAux, dif_pos h, a, stripped]]
        simp only [List.length_cons]
        change 2 * (edgeListAux fuel
          (Equiv.swap a (α a) * α)).length =
            (movedFinset (Equiv.swap a (α a) * α)).card at hrec
        dsimp only [stripped]
        omega
      · have hfixed : ∀ x, α x = x := by
          simpa only [not_exists, not_not] using h
        have hmoved : movedFinset α = ∅ := by
          ext x
          simp [hfixed]
        rw [show edgeListAux (fuel + 1) α = [] by
          simp only [edgeListAux, dif_neg h]]
        simp [hmoved]

/-- The full canonical presentation has half as many swaps as moved points. -/
theorem two_mul_length_edgeList_eq_card_movedFinset (α : Perm D)
    (hinv : Function.Involutive α) :
    2 * (edgeList α).length = (movedFinset α).card := by
  unfold edgeList
  exact two_mul_length_edgeListAux_eq_card_movedFinset
    (Fintype.card D) α hinv (by
      simpa using Finset.card_le_univ (movedFinset α))

/-- For a fixed-point-free involution, the canonical list has one swap for
every permutation orbit. -/
theorem length_edgeList_eq_orbitCount (α : Perm D)
    (hinv : Function.Involutive α) (hfix : ∀ x, α x ≠ x) :
    (edgeList α).length = orbitCount α := by
  have hmoved : movedFinset α = Finset.univ := by
    ext x
    simp [hfix]
  have hlength := two_mul_length_edgeList_eq_card_movedFinset α hinv
  rw [hmoved, Finset.card_univ] at hlength
  have horbits :=
    GoertzelV24CompositeSphericity.card_eq_two_mul_orbitCount_of_involutive
      hinv hfix
  omega

/-! ## Connected rotation systems have one word component -/

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- A rotation step inside one stored vertex is reachable using the rotation
generator. -/
theorem wordReachable_of_rho_sameCycle
    (RS : RotationSystem V E) {left right : RS.D}
    (hsame : RS.rho.SameCycle left right) :
    WordReachable
      (RS.rho :: swapGenerators (edgeList RS.alpha)) left right := by
  obtain ⟨power, hpower⟩ := exists_nat_pow_apply_eq hsame
  have hreach := wordReachable_pow
    (L := RS.rho :: swapGenerators (edgeList RS.alpha))
    (List.mem_cons_self) left power
  rwa [hpower] at hreach

/-- Crossing the paired dart of one edge is reachable using the transposition
presentation of the edge involution. -/
theorem wordReachable_alpha
    (RS : RotationSystem V E) (dart : RS.D) :
    WordReachable
      (RS.rho :: swapGenerators (edgeList RS.alpha))
      dart (RS.alpha dart) := by
  have hreach := wordReachable_swapProduct RS.rho
    (edgeList RS.alpha) dart
  rwa [swapProduct_edgeList RS.alpha RS.alpha_involutive] at hreach

/-- A primal walk lifts through any generator family that realizes vertex
rotation and edge crossing. This separates graph semantics from the choice
of a permutation presentation. -/
theorem wordReachable_of_primalWalk_of_steps
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    (L : List (Perm RS.D))
    (hrotate : ∀ d, WordReachable L d (RS.rho d))
    (hflip : ∀ d, WordReachable L d (RS.alpha d))
    {u v : V} (walk : (rotationPrimalGraph RS).Walk u v) :
    ∀ (left right : RS.D), RS.vertOf left = u → RS.vertOf right = v →
      WordReachable L left right := by
  have hcycle {left right : RS.D} (h : RS.rho.SameCycle left right) :
      WordReachable L left right := by
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq h
    have hp := wordReachable_pow (L := [RS.rho]) (g := RS.rho) (by simp) left n
    rw [hn] at hp
    exact wordReachable_absorb (by
      intro g hg d
      simpa using (List.mem_singleton.mp hg ▸ hrotate d)) hp
  induction walk with
  | nil =>
      intro left right hleft hright
      apply hcycle
      apply hrotation
      exact hleft.trans hright.symm
  | @cons u w v hadj tail ih =>
      intro left right hleft hright
      obtain ⟨crossing, hcrossingU, hcrossingW⟩ :=
        (rotationPrimalGraph_adj_iff RS).1 hadj
      have hturn : WordReachable L left crossing :=
        hcycle
          (hrotation left crossing (hleft.trans hcrossingU.symm))
      have hedge := hflip crossing
      exact hturn.trans (hedge.trans
        (ih (RS.alpha crossing) right hcrossingW hright))

/-- A primal walk lifts to the canonical edge-list presentation. -/
theorem wordReachable_of_primalWalk
    (RS : RotationSystem V E) (hrotation : VertexRotationCyclic RS)
    {u v : V} (walk : (rotationPrimalGraph RS).Walk u v) :
    ∀ (left right : RS.D), RS.vertOf left = u → RS.vertOf right = v →
      WordReachable (RS.rho :: swapGenerators (edgeList RS.alpha)) left right :=
  wordReachable_of_primalWalk_of_steps RS hrotation _
    (wordReachable_step List.mem_cons_self) (wordReachable_alpha RS) walk

/-- The hypermap forgetful map preserves connectedness when each displayed
vertex is a single rotation cycle. -/
theorem hypermap_compCount_eq_one_of_primalConnected
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    Hypermap.compCount (Hypermap.ofRotationSystem RS) = 1 := by
  rw [Hypermap.compCount_ofRotationSystem]
  unfold wordOrbitCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ RS.outer, ?_⟩
  intro component
  induction component using Quotient.inductionOn with
  | h dart =>
    apply Quotient.sound
    obtain ⟨walk⟩ := hconnected (RS.vertOf dart) (RS.vertOf RS.outer)
    exact wordReachable_of_primalWalk_of_steps RS hrotation [RS.rho, RS.alpha]
      (wordReachable_step (by simp)) (wordReachable_step (by simp))
      walk dart RS.outer rfl rfl

/-- Connectedness of the primal graph and cyclicity of the stored vertex
rotations make every two darts word-reachable. -/
theorem wordReachable_all_of_primalConnected
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS)
    (left right : RS.D) :
    WordReachable
      (RS.rho :: swapGenerators (edgeList RS.alpha)) left right := by
  obtain ⟨walk⟩ := hconnected (RS.vertOf left) (RS.vertOf right)
  exact wordReachable_of_primalWalk RS hrotation walk left right rfl rfl

/-- Hence the component count in the generic Euler bound is exactly one. -/
theorem wordOrbitCount_eq_one_of_primalConnected
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    wordOrbitCount
      (RS.rho :: swapGenerators (edgeList RS.alpha)) = 1 := by
  unfold wordOrbitCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ RS.outer, ?_⟩
  intro component
  induction component using Quotient.inductionOn with
  | h dart =>
      exact Quotient.sound (wordReachable_all_of_primalConnected
        RS hconnected hrotation dart RS.outer)

/-! ## The connected map inequality -/

/-- Euler's inequality specialized to a connected rotation map:
`V + F ≤ E + 2`, with all three quantities read as permutation orbits. -/
theorem orbitCount_rho_add_orbitCount_phi_le_edge_add_two
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    orbitCount RS.rho + orbitCount RS.phi ≤
      Fintype.card E + 2 := by
  have heuler := Hypermap.eulerLhs_le_eulerRhs (Hypermap.ofRotationSystem RS)
  have hcomponents := hypermap_compCount_eq_one_of_primalConnected
    RS hconnected hrotation
  have halpha :=
    GoertzelV24CompositeSphericity.two_mul_orbitCount_alpha RS
  have hedges := RS.card_darts_eq_twice_card_edges
  rw [Hypermap.eulerLhs_eq_orbit_sum, Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    Hypermap.ofRotationSystem_edge, Hypermap.orbitCount_node,
    Hypermap.ofRotationSystem_face, hcomponents] at heuler
  omega

end

end GoertzelV24ConnectedMapEulerBound

end Mettapedia.GraphTheory.FourColor
