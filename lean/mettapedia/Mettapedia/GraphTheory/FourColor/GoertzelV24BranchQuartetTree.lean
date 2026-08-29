import Mettapedia.GraphTheory.FourColor.GoertzelV24BranchQuartetCalculus
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionAdapter

/-!
# Quartet replacement on rooted branch-decomposition trees

The rooted binary tree of a branch decomposition is carried together with its
*up-set*: the edges lying outside the subtree.  Every internal vertex of the
underlying ternary tree is then a fork whose three directions are the two
child shores and the up-set, and every tree edge between two internal
vertices is a fork child of a fork.  A *quartet* is such a tree edge whose
four surrounding shores admit a width-preserving re-pairing.

This file defines the potential, the width and quartet-freeness predicates
in this rooted form, performs the two re-pairings as tree rotations, and
proves by strong induction on the potential that every bounded-width tree
can be replaced by a quartet-free tree of the same width on the same leaves.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BranchQuartetTree

open GoertzelV24BranchQuartetCalculus
open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedEdgeShoreMajority
open EdgeLeafTree

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Trees with an up-set -/

/-- A subtree together with its up-set is *genuine* when the leaves are
distinct, disjoint from the up-set, and together with it exhaust the edges;
the up-set is never empty because it always contains the root leaf. -/
structure Genuine (tree : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet) :
    Prop where
  nodup : tree.leafList.Nodup
  disjoint : Disjoint tree.shore up
  cover : tree.shore ∪ up = Finset.univ
  upNonempty : up.Nonempty

theorem mem_shore_iff (tree : EdgeLeafTree G.edgeSet) (edge : G.edgeSet) :
    edge ∈ tree.shore ↔ edge ∈ tree.leafList := by
  simp [EdgeLeafTree.shore]

theorem Genuine.disjoint_children {a b : EdgeLeafTree G.edgeSet}
    {up : Finset G.edgeSet} (h : Genuine (G := G) (fork a b) up) :
    Disjoint a.shore b.shore := by
  have hdisj : List.Disjoint a.leafList b.leafList :=
    List.disjoint_of_nodup_append h.nodup
  rw [Finset.disjoint_left]
  intro edge ha hb
  exact hdisj ((mem_shore_iff a edge).1 ha) ((mem_shore_iff b edge).1 hb)

theorem Genuine.left {a b : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : Genuine (G := G) (fork a b) up) : Genuine (G := G) a (up ∪ b.shore) where
  nodup := (h.nodup : (a.leafList ++ b.leafList).Nodup).of_append_left
  disjoint := by
    have hup := h.disjoint
    rw [shore_fork] at hup
    exact Finset.disjoint_union_right.2
      ⟨Finset.disjoint_union_left.1 hup |>.1, h.disjoint_children⟩
  cover := by
    have hcover := h.cover
    rw [shore_fork] at hcover
    rw [← hcover, Finset.union_comm up b.shore, Finset.union_assoc]
  upNonempty := Finset.Nonempty.mono Finset.subset_union_left h.upNonempty

theorem Genuine.flip {a b : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : Genuine (G := G) (fork a b) up) : Genuine (G := G) (fork b a) up where
  nodup := by
    have := h.nodup
    simp only [leafList_fork] at this ⊢
    exact List.perm_append_comm.nodup_iff.1 this
  disjoint := by
    have := h.disjoint
    rw [shore_fork, Finset.union_comm] at this
    rwa [shore_fork]
  cover := by
    have := h.cover
    rw [shore_fork, Finset.union_comm a.shore] at this
    rwa [shore_fork]
  upNonempty := h.upNonempty

theorem Genuine.right {a b : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : Genuine (G := G) (fork a b) up) : Genuine (G := G) b (up ∪ a.shore) :=
  h.flip.left

theorem Genuine.of_perm {t t' : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : Genuine (G := G) t up) (hperm : t'.leafList.Perm t.leafList) :
    Genuine (G := G) t' up where
  nodup := hperm.nodup_iff.2 h.nodup
  disjoint := by
    have hshore : t'.shore = t.shore := List.toFinset_eq_of_perm _ _ hperm
    rw [hshore]; exact h.disjoint
  cover := by
    have hshore : t'.shore = t.shore := List.toFinset_eq_of_perm _ _ hperm
    rw [hshore]; exact h.cover
  upNonempty := h.upNonempty

theorem Genuine.up_eq {t : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : Genuine (G := G) t up) : up = Finset.univ \ t.shore := by
  ext edge
  rw [Finset.mem_sdiff]
  constructor
  · intro hup
    exact ⟨Finset.mem_univ _, fun hshore => Finset.disjoint_left.1 h.disjoint hshore hup⟩
  · rintro ⟨-, hshore⟩
    have : edge ∈ t.shore ∪ up := by rw [h.cover]; exact Finset.mem_univ _
    exact (Finset.mem_union.1 this).resolve_left hshore

theorem Genuine.shore_eq {t : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : Genuine (G := G) t up) : t.shore = Finset.univ \ up := by
  ext edge
  rw [Finset.mem_sdiff]
  constructor
  · intro hshore
    exact ⟨Finset.mem_univ _, fun hup => Finset.disjoint_left.1 h.disjoint hshore hup⟩
  · rintro ⟨-, hup⟩
    have : edge ∈ t.shore ∪ up := by rw [h.cover]; exact Finset.mem_univ _
    exact (Finset.mem_union.1 this).resolve_right hup

/-! ## Potential, width, connectedness, quartets -/

/-- The sum over all forks of the vertex potential of its three directions. -/
def potential : EdgeLeafTree G.edgeSet → Finset G.edgeSet → ℕ
  | .leaf _, _ => 0
  | .fork a b, up =>
      psi (G := G) a.shore b.shore up +
        potential a (up ∪ b.shore) + potential b (up ∪ a.shore)

/-- Every cut below the tree, including leaf cuts, has boundary of size at
most `w`, with complements expressed through the up-set. -/
def CutWidthLe (w : ℕ) : EdgeLeafTree G.edgeSet → Finset G.edgeSet → Prop
  | .leaf edge, up => (bd (G := G) {edge} up).card ≤ w
  | .fork a b, up =>
      (bd (G := G) (a.shore ∪ b.shore) up).card ≤ w ∧
        CutWidthLe w a (up ∪ b.shore) ∧ CutWidthLe w b (up ∪ a.shore)

/-- Both shores of every cut below the tree are connected. -/
def CutConnected : EdgeLeafTree G.edgeSet → Finset G.edgeSet → Prop
  | .leaf edge, up => EdgeShoreConnected G {edge} ∧ EdgeShoreConnected G up
  | .fork a b, up =>
      EdgeShoreConnected G (a.shore ∪ b.shore) ∧ EdgeShoreConnected G up ∧
        CutConnected a (up ∪ b.shore) ∧ CutConnected b (up ∪ a.shore)

/-- A quartet at a site with child pair `P, Q` and outer pair `R, T`. -/
def QuartetAt (P Q R T : Finset G.edgeSet) : Prop :=
  QuartetPairs (G := G) P Q R T ∨ QuartetPairs (G := G) R T P Q

/-- The tree edge from a fork down to `child` carries no quartet; `sibling`
is the other child shore and `up` the up-set of the fork. -/
def SiteFree : EdgeLeafTree G.edgeSet → Finset G.edgeSet → Finset G.edgeSet → Prop
  | .leaf _, _, _ => True
  | .fork p q, sibling, up => ¬ QuartetAt (G := G) p.shore q.shore sibling up

/-- No tree edge below the tree carries a quartet. -/
def QuartetFree : EdgeLeafTree G.edgeSet → Finset G.edgeSet → Prop
  | .leaf _, _ => True
  | .fork a b, up =>
      SiteFree (G := G) a b.shore up ∧ SiteFree (G := G) b a.shore up ∧
        QuartetFree a (up ∪ b.shore) ∧ QuartetFree b (up ∪ a.shore)

/-! ## Flipping the two children of a fork -/

theorem potential_flip (a b : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet) :
    potential (G := G) (fork b a) up = potential (G := G) (fork a b) up := by
  simp only [potential]
  rw [psi_swap₁₂]
  omega

theorem cutWidthLe_flip {w : ℕ} {a b : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet}
    (h : CutWidthLe (G := G) w (fork a b) up) : CutWidthLe (G := G) w (fork b a) up := by
  obtain ⟨hroot, ha, hb⟩ := h
  refine ⟨?_, hb, ha⟩
  rwa [Finset.union_comm]

theorem leafList_flip_perm (a b : EdgeLeafTree G.edgeSet) :
    (fork b a).leafList.Perm (fork a b).leafList := by
  simp only [leafList_fork]
  exact List.perm_append_comm

/-! ## The two rotations at a fork-of-fork -/

section Rotation

variable (p q s : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet)

theorem potential_rot₁_lt
    (hψ : psi (G := G) p.shore s.shore (up ∪ q.shore) +
        psi (G := G) (p.shore ∪ s.shore) q.shore up <
      psi (G := G) p.shore q.shore (up ∪ s.shore) +
        psi (G := G) (p.shore ∪ q.shore) s.shore up) :
    potential (G := G) (fork (fork p s) q) up <
      potential (G := G) (fork (fork p q) s) up := by
  simp only [potential, shore_fork]
  have e₁ : up ∪ s.shore ∪ q.shore = up ∪ q.shore ∪ s.shore :=
    Finset.union_right_comm _ _ _
  have e₂ : up ∪ s.shore ∪ p.shore = up ∪ (p.shore ∪ s.shore) := by
    rw [Finset.union_assoc, Finset.union_comm s.shore]
  have e₃ : up ∪ (p.shore ∪ q.shore) = up ∪ q.shore ∪ p.shore := by
    rw [Finset.union_assoc, Finset.union_comm q.shore]
  rw [e₁, e₂, e₃]
  omega

theorem potential_rot₂_lt
    (hψ : psi (G := G) p.shore (q.shore ∪ s.shore) up +
        psi (G := G) q.shore s.shore (up ∪ p.shore) <
      psi (G := G) p.shore q.shore (up ∪ s.shore) +
        psi (G := G) (p.shore ∪ q.shore) s.shore up) :
    potential (G := G) (fork p (fork q s)) up <
      potential (G := G) (fork (fork p q) s) up := by
  simp only [potential, shore_fork]
  have e₁ : up ∪ s.shore ∪ q.shore = up ∪ (q.shore ∪ s.shore) := by
    rw [Finset.union_assoc, Finset.union_comm s.shore]
  have e₂ : up ∪ s.shore ∪ p.shore = up ∪ p.shore ∪ s.shore :=
    Finset.union_right_comm _ _ _
  have e₃ : up ∪ (p.shore ∪ q.shore) = up ∪ p.shore ∪ q.shore :=
    (Finset.union_assoc _ _ _).symm
  rw [e₁, e₂, e₃]
  omega

theorem cutWidthLe_rot₁ {w : ℕ}
    (h : CutWidthLe (G := G) w (fork (fork p q) s) up)
    (hnew : (bd (G := G) (p.shore ∪ s.shore) (q.shore ∪ up)).card ≤ w) :
    CutWidthLe (G := G) w (fork (fork p s) q) up := by
  simp only [CutWidthLe, shore_fork] at h ⊢
  obtain ⟨hroot, ⟨hmid, hp, hq⟩, hs⟩ := h
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rwa [Finset.union_right_comm]
  · rwa [Finset.union_comm q.shore up] at hnew
  · rwa [Finset.union_right_comm] at hp
  · rwa [Finset.union_comm p.shore, ← Finset.union_assoc] at hs
  · rwa [Finset.union_right_comm, Finset.union_assoc] at hq

theorem cutWidthLe_rot₂ {w : ℕ}
    (h : CutWidthLe (G := G) w (fork (fork p q) s) up)
    (hnew : (bd (G := G) (q.shore ∪ s.shore) (up ∪ p.shore)).card ≤ w) :
    CutWidthLe (G := G) w (fork p (fork q s)) up := by
  simp only [CutWidthLe, shore_fork] at h ⊢
  obtain ⟨hroot, ⟨hmid, hp, hq⟩, hs⟩ := h
  refine ⟨?_, ?_, ⟨hnew, ?_, ?_⟩⟩
  · rwa [Finset.union_assoc] at hroot
  · rwa [Finset.union_right_comm, Finset.union_assoc] at hp
  · rwa [Finset.union_right_comm] at hq
  · rwa [← Finset.union_assoc] at hs

theorem leafList_rot₁_perm :
    (fork (fork p s) q).leafList.Perm (fork (fork p q) s).leafList := by
  simp only [leafList_fork, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

theorem leafList_rot₂_perm :
    (fork p (fork q s)).leafList.Perm (fork (fork p q) s).leafList := by
  simp only [leafList_fork, List.append_assoc]
  exact List.Perm.refl _

end Rotation

theorem CutWidthLe.root {w : ℕ} :
    ∀ {t : EdgeLeafTree G.edgeSet} {up : Finset G.edgeSet},
      CutWidthLe (G := G) w t up → (bd (G := G) t.shore up).card ≤ w
  | .leaf _, _, h => by simpa [CutWidthLe] using h
  | .fork _ _, _, h => by simpa [CutWidthLe] using h.1

/-- Rotating at the root of a fork-of-fork removes a quartet there. -/
theorem exists_rotation_root {w : ℕ} {p q s : EdgeLeafTree G.edgeSet}
    {up : Finset G.edgeSet}
    (hg : Genuine (G := G) (fork (fork p q) s) up)
    (hw : CutWidthLe (G := G) w (fork (fork p q) s) up)
    (hq : QuartetAt (G := G) p.shore q.shore s.shore up) :
    ∃ t' : EdgeLeafTree G.edgeSet,
      t'.leafList.Perm (fork (fork p q) s).leafList ∧
        CutWidthLe (G := G) w t' up ∧
          potential (G := G) t' up < potential (G := G) (fork (fork p q) s) up := by
  have hPQd : Disjoint p.shore q.shore := hg.left.disjoint_children
  have hSUd : Disjoint s.shore up :=
    (Finset.disjoint_union_right.1 hg.right.disjoint).1
  have hPn : p.shore.Nonempty := shore_nonempty p
  have hQn : q.shore.Nonempty := shore_nonempty q
  have hSn : s.shore.Nonempty := shore_nonempty s
  have hUn : up.Nonempty := hg.upNonempty
  -- the four old cuts in the calculus normal form
  have hcutS : (bd (G := G) s.shore (p.shore ∪ q.shore ∪ up)).card ≤ w := by
    have := hw.2.2.root
    rwa [shore_fork, Finset.union_comm up] at this
  have hcutU : (bd (G := G) up (p.shore ∪ q.shore ∪ s.shore)).card ≤ w := by
    have := hw.1
    rwa [shore_fork, bd_comm] at this
  have hcutP : (bd (G := G) p.shore (s.shore ∪ up ∪ q.shore)).card ≤ w := by
    have := hw.2.1.2.1.root
    rwa [Finset.union_comm up s.shore] at this
  have hcutQ : (bd (G := G) q.shore (s.shore ∪ up ∪ p.shore)).card ≤ w := by
    have := hw.2.1.2.2.root
    rwa [Finset.union_comm up s.shore] at this
  rcases hq with hq | hq
  · -- the child pair `p, q` is vertex-disjoint
    rcases rePair_choice_of_quartetPairs hq hcutS hcutU with
      ⟨hPS, hQU, hnew⟩ | ⟨hPU, hQS, hnew⟩
    · refine ⟨fork (fork p s) q, leafList_rot₁_perm p q s,
        cutWidthLe_rot₁ p q s up hw hnew, ?_⟩
      apply potential_rot₁_lt
      have := psi_rePair_lt (G := G) p.shore q.shore s.shore up hq.1 hPS hQU hSn hUn hPQd hSUd
      rwa [Finset.union_comm q.shore up, Finset.union_comm s.shore up] at this
    · refine ⟨fork p (fork q s), leafList_rot₂_perm p q s, ?_, ?_⟩
      · apply cutWidthLe_rot₂ p q s up hw
        rwa [bd_comm, Finset.union_comm up p.shore]
      · apply potential_rot₂_lt
        have := psi_rePair_lt' (G := G) p.shore q.shore s.shore up hq.1 hPU hQS hSn hUn hPQd hSUd
        rwa [psi_swap₂₃ (G := G) p.shore up, psi_swap₁₃ (G := G) (p.shore ∪ up),
          psi_swap₁₂ (G := G) s.shore, Finset.union_comm p.shore up,
          Finset.union_comm s.shore up] at this
  · -- the outer pair `s, up` is vertex-disjoint
    rcases rePair_choice_of_quartetPairs hq hcutP hcutQ with
      ⟨hSP, hUQ, hnew⟩ | ⟨hSQ, hUP, hnew⟩
    · refine ⟨fork (fork p s) q, leafList_rot₁_perm p q s, ?_, ?_⟩
      · apply cutWidthLe_rot₁ p q s up hw
        rwa [Finset.union_comm s.shore p.shore, Finset.union_comm up q.shore] at hnew
      · apply potential_rot₁_lt
        have := psi_rePair_lt (G := G) s.shore up p.shore q.shore hq.1 hSP hUQ hPn hQn hSUd hPQd
        rw [psi_swap₁₂ (G := G) s.shore p.shore, psi_swap₂₃ (G := G) (s.shore ∪ p.shore),
          Finset.union_comm s.shore p.shore, psi_swap₁₃ (G := G) s.shore up,
          psi_swap₂₃ (G := G) (p.shore ∪ q.shore), psi_swap₁₃ (G := G) (s.shore ∪ up),
          psi_swap₁₂ (G := G) q.shore p.shore, Finset.union_comm s.shore up] at this
        omega
    · refine ⟨fork p (fork q s), leafList_rot₂_perm p q s, ?_, ?_⟩
      · apply cutWidthLe_rot₂ p q s up hw
        rwa [Finset.union_comm s.shore q.shore] at hnew
      · apply potential_rot₂_lt
        have := psi_rePair_lt' (G := G) s.shore up p.shore q.shore hq.1 hSQ hUP hPn hQn hSUd hPQd
        rw [psi_swap₁₂ (G := G) s.shore q.shore, psi_swap₁₃ (G := G) (s.shore ∪ q.shore),
          psi_swap₂₃ (G := G) p.shore up, Finset.union_comm s.shore q.shore,
          psi_swap₁₃ (G := G) s.shore up, psi_swap₂₃ (G := G) (p.shore ∪ q.shore),
          psi_swap₁₃ (G := G) (s.shore ∪ up), psi_swap₁₂ (G := G) q.shore p.shore,
          Finset.union_comm s.shore up] at this
        omega

/-- A tree with a quartet somewhere admits a strictly cheaper tree of the
same width on the same leaves. -/
theorem exists_rotation {w : ℕ} :
    ∀ (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet),
      Genuine (G := G) t up → CutWidthLe (G := G) w t up →
      ¬ QuartetFree (G := G) t up →
      ∃ t' : EdgeLeafTree G.edgeSet,
        t'.leafList.Perm t.leafList ∧ CutWidthLe (G := G) w t' up ∧
          potential (G := G) t' up < potential (G := G) t up
  | .leaf _, _, _, _, hnot => (hnot trivial).elim
  | .fork a b, up, hg, hw, hnot => by
      by_cases hsa : SiteFree (G := G) a b.shore up
      · by_cases hsb : SiteFree (G := G) b a.shore up
        · by_cases hqa : QuartetFree (G := G) a (up ∪ b.shore)
          · by_cases hqb : QuartetFree (G := G) b (up ∪ a.shore)
            · exact (hnot ⟨hsa, hsb, hqa, hqb⟩).elim
            · obtain ⟨b', hperm, hw', hlt⟩ :=
                exists_rotation b (up ∪ a.shore) hg.right hw.2.2 hqb
              have hshore : b'.shore = b.shore := List.toFinset_eq_of_perm _ _ hperm
              refine ⟨fork a b', ?_, ?_, ?_⟩
              · simp only [leafList_fork]
                exact hperm.append_left _
              · refine ⟨?_, ?_, hw'⟩
                · rw [hshore]; exact hw.1
                · rw [hshore]; exact hw.2.1
              · simp only [potential, hshore]
                omega
          · obtain ⟨a', hperm, hw', hlt⟩ :=
              exists_rotation a (up ∪ b.shore) hg.left hw.2.1 hqa
            have hshore : a'.shore = a.shore := List.toFinset_eq_of_perm _ _ hperm
            refine ⟨fork a' b, ?_, ?_, ?_⟩
            · simp only [leafList_fork]
              exact hperm.append_right _
            · refine ⟨?_, hw', ?_⟩
              · rw [hshore]; exact hw.1
              · rw [hshore]; exact hw.2.2
            · simp only [potential, hshore]
              omega
        · cases b with
          | leaf _ => exact (hsb trivial).elim
          | fork p q =>
              have hq : QuartetAt (G := G) p.shore q.shore a.shore up := by
                simpa [SiteFree] using hsb
              obtain ⟨t', hperm, hw', hlt⟩ :=
                exists_rotation_root (w := w) hg.flip (cutWidthLe_flip hw) hq
              refine ⟨t', hperm.trans (leafList_flip_perm a (fork p q)), hw', ?_⟩
              rwa [potential_flip] at hlt
      · cases a with
        | leaf _ => exact (hsa trivial).elim
        | fork p q =>
            have hq : QuartetAt (G := G) p.shore q.shore b.shore up := by
              simpa [SiteFree] using hsa
            exact exists_rotation_root (w := w) hg hw hq

/-- **Make-it-Connected terminates**: every genuine bounded-width tree has a
quartet-free tree of the same width on the same leaves. -/
theorem exists_quartetFree {w : ℕ} (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet)
    (hg : Genuine (G := G) t up) (hw : CutWidthLe (G := G) w t up) :
    ∃ t' : EdgeLeafTree G.edgeSet,
      t'.leafList.Perm t.leafList ∧ CutWidthLe (G := G) w t' up ∧
        QuartetFree (G := G) t' up := by
  induction hn : potential (G := G) t up using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_cases hqf : QuartetFree (G := G) t up
    · exact ⟨t, List.Perm.refl _, hw, hqf⟩
    · obtain ⟨t₁, hperm₁, hw₁, hlt⟩ := exists_rotation t up hg hw hqf
      rw [hn] at hlt
      obtain ⟨t', hperm', hw', hqf'⟩ :=
        ih _ hlt t₁ (hg.of_perm hperm₁) hw₁ rfl
      exact ⟨t', hperm'.trans hperm₁, hw', hqf'⟩

end

end GoertzelV24BranchQuartetTree

end Mettapedia.GraphTheory.FourColor
