import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.ConfigurationFaceGraph
import MettapediaFourColor.ExecutableContract
import MettapediaFourColor.ConfigurationContract
import Mettapedia.GraphTheory.FourColor.TwoDiamondBoundaryElimination
import FourColor.Configurations
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Actual two-diamond configurations with one shared tip

The complete dart permutations and ordered rings are kernel compared with
the reference construction programs. Both configuration graphs have two
diamond interiors sharing a tip. Their common summary retains that colour
and reconstructs genuine witnesses under arbitrary boundary constraints.

Configuration data and construction semantics are reused from Chris Emery's
MIT-licensed port of the Gonthier--Werner and Robertson--Sanders--Seymour--Thomas
development; the original licence is retained in this package.
-/

namespace FourColor.TwoDiamondConfigurations

open ExecutableConfiguration ConfigurationTable
open Mettapedia.GraphTheory.FourColor

def program003 : List Step := [.join, .rotate 1, .join, .rotate 6, .join, .rotate 1, .fork, .rotate 4, .join, .rotate 6, .join, .rotate 6, .join, .rotate 6, .fork, .fork, .rotate 4, .join, .rotate 1, .fork, .rotate 3, .fork, .rotate 1, .fork]

theorem reference003 : evaluate program003 = cfmap cf003 := evaluate_eq _

def table003 : Data 68 where
  base := 33
  edges := "\"!$#&%('*),+.-0/21436587:9<;>=@?BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badc"
  nodes := "&2\"'$,%6(C*=!M.30#1I4)<B8Q:V7H>[@9+LDdF?5PJE/ZNK;^RWT-UbXOA_\\S]c`YaG"
  faces := "#-%2!')$+6&C/V1M\"350(I9=;B7Q?,AH8[E*GL>dK4DPO.JZS:U^<WYTNb]@R_a\\XcF`"
  cancel := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem numbered003 : numbered program003 = table003.map := by
  apply table003.eq_of_tables
  decide +kernel

def vertex003 : Fin 68 → Fin 15 := lookup "BCBOBAAOANAHCDCMCOOMONFGFLFEGHGJGLHNHIHJNMNIMDMIELEKEDDKDILJLKKJKIIJ"
def representative003 : Fin 15 → Fin 68 := lookupBase 33 "&!\".<78,F@T:0*$"

def graph003 : SimpleGraph (Fin 15) :=
  ConfigurationFaceGraph.graph table003.map vertex003
    (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph003.Adj := by unfold graph003; infer_instance

def faces003 : ConfigurationFaceGraph.Presentation table003.map graph003 where
  vertex := vertex003
  representative := representative003
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches (n := 9) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

def realization003 : Realization (cfmap cf003) table003 0 :=
  reference003 ▸
    ({ numbering := (index program003).symm
       map_eq := numbered003
       point_eq := by decide +kernel } : Realization (evaluate program003) table003 0)

def ring003 : List (Fin 68) := [5, 0, 12, 53, 27, 22, 28, 11]
def boundary003 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7]

theorem cpring003 : table003.map.cpring 0 = ring003 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem reducibilityTrace003 (et : List Color) :
    (cfmap cf003).map.RingTrace (cfring cf003).reverse et ↔
      ∃ k : graph003.Coloring Color, et = trace (boundary003.map k) := by
  rw [cfring, List.reverse_reverse, realization003.forwardRingTrace,
    cpring003, faces003.ringTrace_iff]
  rfl

def attachments003 (i : Fin 7) (v : Fin 8) : Prop :=
  match i.val with
  | 0 => v.val = 3 ∨ v.val = 7
  | 1 => v.val = 6 ∨ v.val = 7
  | 2 => v.val = 3 ∨ v.val = 4
  | 3 => v.val = 4 ∨ v.val = 5 ∨ v.val = 6
  | 4 => v.val = 2 ∨ v.val = 3
  | 5 => v.val = 0 ∨ v.val = 7
  | _ => v.val = 0 ∨ v.val = 1 ∨ v.val = 2

instance : ∀ i v, Decidable (attachments003 i v) :=
  fun i v => by unfold attachments003; split <;> infer_instance

def core003 : SimpleGraph (Fin 8 ⊕ Fin 7) :=
  TwoDiamondBoundaryElimination.graph (SimpleGraph.cycleGraph 8) attachments003

instance : DecidableRel core003.Adj := by unfold core003; infer_instance

def graphIso003 : core003 ≃g graph003 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

abbrev Plan003 (C : Type*) :=
  Σ b : (SimpleGraph.cycleGraph 8).Coloring C,
    TwoDiamondBoundaryElimination.Summary attachments003 b

def planEquiv003 (C : Type*) : graph003.Coloring C ≃ Plan003 C :=
  (SimpleGraph.coloringCongr graphIso003.symm (Equiv.refl C)).trans
    (TwoDiamondBoundaryElimination.coloringEquiv _ _)

@[simp] theorem reconstruct_boundary003 (C : Type*) (p : Plan003 C) (v : Fin 8) :
    (planEquiv003 C).symm p (graphIso003 (.inl v)) = p.1 v := by
  change TwoDiamondBoundaryElimination.reconstruct _ _ p.1 p.2
    (graphIso003.symm (graphIso003 (.inl v))) = p.1 v
  rw [graphIso003.symm_apply_apply]
  rfl

theorem context003 {C : Type*} (accepts : (Fin 8 → C) → Prop) :
    (∃ k : graph003.Coloring C, accepts (fun v => k (graphIso003 (.inl v)))) ↔
      ∃ p : Plan003 C, accepts p.1 := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨planEquiv003 C k, hk⟩
  · rintro ⟨p, hp⟩
    refine ⟨(planEquiv003 C).symm p, ?_⟩
    simpa only [reconstruct_boundary003] using hp

theorem summaryTrace003 (et : List Color) :
    (cfmap cf003).map.RingTrace (cfring cf003).reverse et ↔
      ∃ p : Plan003 Color, et = trace ((List.finRange 8).map p.1) := by
  rw [reducibilityTrace003]
  have ports : (List.finRange 8).map (fun v => graphIso003 (.inl v)) = boundary003 := by
    decide +kernel
  simpa only [← ports, List.map_map, Function.comp_def] using
    context003 (fun b => et = trace ((List.finRange 8).map b))

/-- A proper exterior for which the two separate pieces choose different tips. -/
def rejectedBoundary003 : Fin 8 → Fin 4 := lookup "ABACACBC"

def leftChoice003 : DiamondBoundaryElimination.Summary
    (fun i => attachments003 (TwoDiamondBoundaryElimination.left i)) rejectedBoundary003 where
  first := 0
  second := 1
  centres_ne := by decide
  first_allowed := by simp only [DiamondBoundaryElimination.Allows]; decide +kernel
  second_allowed := by simp only [DiamondBoundaryElimination.Allows]; decide +kernel
  lower := ⟨3, by simp only [DiamondBoundaryElimination.Allows]; decide +kernel⟩
  upper := ⟨3, by simp only [DiamondBoundaryElimination.Allows]; decide +kernel⟩

def rightChoice003 : DiamondBoundaryElimination.Summary
    (fun i => attachments003 (TwoDiamondBoundaryElimination.right i)) rejectedBoundary003 where
  first := 1
  second := 3
  centres_ne := by decide
  first_allowed := by simp only [DiamondBoundaryElimination.Allows]; decide +kernel
  second_allowed := by simp only [DiamondBoundaryElimination.Allows]; decide +kernel
  lower := ⟨0, by simp only [DiamondBoundaryElimination.Allows]; decide +kernel⟩
  upper := ⟨2, by simp only [DiamondBoundaryElimination.Allows]; decide +kernel⟩

theorem rejectedBoundary_proper003 :
    ∀ v w, (SimpleGraph.cycleGraph 8).Adj v w → rejectedBoundary003 v ≠ rejectedBoundary003 w := by
  decide +kernel

/-- Forgetting the shared-tip agreement falsely accepts an actual boundary. -/
theorem shared_tip_obstruction003 :
    ¬ Nonempty (TwoDiamondBoundaryElimination.Summary attachments003 rejectedBoundary003) := by
  rintro ⟨s⟩
  have force_left : ∀ a b l u : Fin 4,
      (a ≠ 1 ∧ a ≠ 2) → (b ≠ 2 ∧ b ≠ 0) →
      (u ≠ 0 ∧ u ≠ 2 ∧ u ≠ 1) → (u ≠ a ∧ u ≠ b) →
      (l ≠ 2 ∧ l ≠ a ∧ l ≠ b) → l = 3 := by decide +kernel
  have force_right : ∀ a b l : Fin 4,
      (a ≠ 0 ∧ a ≠ 2) → (b ≠ 0 ∧ b ≠ 2) → a ≠ b →
      (l ≠ 2 ∧ l ≠ a ∧ l ≠ b) → l = 0 := by decide +kernel
  have hl := force_left s.first.first s.first.second s.first.lower.val s.first.upper.val
    ⟨s.first.first_allowed 6 (by decide), s.first.first_allowed 7 (by decide)⟩
    ⟨s.first.second_allowed 3 (by decide), s.first.second_allowed 4 (by decide)⟩
    ⟨s.first.upper.property.1 4 (by decide), s.first.upper.property.1 5 (by decide),
      s.first.upper.property.1 6 (by decide)⟩ s.first.upper.property.2
    ⟨s.first.lower.property.1 3 (by decide), s.first.lower.property.2⟩
  have hr := force_right s.second.first s.second.second s.second.lower.val
    ⟨s.second.first_allowed 2 (by decide), s.second.first_allowed 3 (by decide)⟩
    ⟨s.second.second_allowed 0 (by decide), s.second.second_allowed 7 (by decide)⟩
    s.second.centres_ne
    ⟨s.second.lower.property.1 3 (by decide), s.second.lower.property.2⟩
  exact (by decide : (3 : Fin 4) ≠ 0) (hl.symm.trans (s.shared.trans hr))

def degree003 (v : Fin 15) : ℕ := entry "EDEFEDEFGFFFFFF" v.val
def stars003 : Fin 15 → List (Fin 15) :=
  ConfigurationFaceGraph.star table003.map vertex003 representative003 degree003

def darts003 : List (Fin 68) := [67]

theorem enumeration003 :
    (ctrenum cf003.prog).map realization003.numbering = numberedKernelEdges program003 :=
  Realization.map_numbering_of_heq (n := 68) (t := table003) (p := 0)
    { numbering := (index program003).symm
      map_eq := numbered003
      point_eq := by decide +kernel } reference003 (kernelEdges_heq program003)

set_option maxRecDepth 32768 in
theorem contract003 : (cfcontract cf003).map realization003.numbering = darts003 := by
  unfold cfcontract
  erw [← listMask_map, enumeration003]
  decide +kernel

theorem contractTrace003 (et : List Color) :
    (cfmap cf003).map.CcRingTrace (cfcontract cf003) (cfring cf003).reverse et ↔
      ∃ k : faces003.ContractAssignment darts003,
        et = trace (boundary003.map k.val) := by
  rw [realization003.ccRingTrace, contract003, cfring, List.reverse_reverse,
    realization003.ring, cpring003, faces003.ccRingTrace_iff]
  rfl

def program006 : List Step := [.join, .rotate 2, .join, .rotate 8, .fork, .rotate 4, .join, .rotate 7, .join, .rotate 2, .join, .rotate 7, .fork, .rotate 6, .join, .rotate 1, .fork, .rotate 1, .fork, .rotate 2, .join, .rotate 4, .fork, .rotate 2, .fork, .fork]

theorem reference006 : evaluate program006 = cfmap cf006 := evaluate_eq _

def table006 : Data 72 where
  base := 33
  edges := "\"!$#&%('*),+.-0/21436587:9<;>=@?BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehg"
  nodes := "&Z\"-$',0(G*7%b.)6<2=4B1L8C:35F>T@U;PD?+hHMJ9KQNEO[RA!^V_X#Sc\\WYf`/]gdaeI"
  faces := "#U%Z!-)&+0'G/$(b375<1=9,;L2C?4AF6TE:>PI*Kh8MOJDQSN@[WBY^\"_]RVcaX.fe\\`gHd"
  cancel := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem numbered006 : numbered program006 = table006.map := by
  apply table006.eq_of_tables
  decide +kernel

def vertex006 : Fin 72 → Fin 16 := lookup "BCBMBAIAIKIHAMAKFGFPFEGHGOGPEPENEDPOPNHKHJHOOJONNJNDCDCLCMDJDLMLMKLJLKKJ"
def representative006 : Fin 16 → Fin 72 := lookupBase 33 "&!\"B612,'J*X$@:4"

def graph006 : SimpleGraph (Fin 16) :=
  ConfigurationFaceGraph.graph table006.map vertex006
    (by decide +kernel) (by decide +kernel)

instance : DecidableRel graph006.Adj := by unfold graph006; infer_instance

def faces006 : ConfigurationFaceGraph.Presentation table006.map graph006 where
  vertex := vertex006
  representative := representative006
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches (n := 9) (by decide +kernel)
  adjacent := fun _ _ => Iff.rfl

def realization006 : Realization (cfmap cf006) table006 0 :=
  reference006 ▸
    ({ numbering := (index program006).symm
       map_eq := numbered006
       point_eq := by decide +kernel } : Realization (evaluate program006) table006 0)

def ring006 : List (Fin 72) := [5, 0, 52, 33, 21, 16, 22, 11, 6]
def boundary006 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem cpring006 : table006.map.cpring 0 = ring006 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem reducibilityTrace006 (et : List Color) :
    (cfmap cf006).map.RingTrace (cfring cf006).reverse et ↔
      ∃ k : graph006.Coloring Color, et = trace (boundary006.map k) := by
  rw [cfring, List.reverse_reverse, realization006.forwardRingTrace,
    cpring006, faces006.ringTrace_iff]
  rfl

def attachments006 (i : Fin 7) (v : Fin 9) : Prop :=
  match i.val with
  | 0 => v.val = 3 ∨ v.val = 7
  | 1 => v.val = 0 ∨ v.val = 7 ∨ v.val = 8
  | 2 => v.val = 2 ∨ v.val = 3
  | 3 => v.val = 0 ∨ v.val = 1 ∨ v.val = 2
  | 4 => v.val = 3 ∨ v.val = 4
  | 5 => v.val = 6 ∨ v.val = 7
  | _ => v.val = 4 ∨ v.val = 5 ∨ v.val = 6

instance : ∀ i v, Decidable (attachments006 i v) :=
  fun i v => by unfold attachments006; split <;> infer_instance

def core006 : SimpleGraph (Fin 9 ⊕ Fin 7) :=
  TwoDiamondBoundaryElimination.graph (SimpleGraph.cycleGraph 9) attachments006

instance : DecidableRel core006.Adj := by unfold core006; infer_instance

def graphIso006 : core006 ≃g graph006 where
  toEquiv := finSumFinEquiv
  map_rel_iff' := by decide +kernel

abbrev Plan006 (C : Type*) :=
  Σ b : (SimpleGraph.cycleGraph 9).Coloring C,
    TwoDiamondBoundaryElimination.Summary attachments006 b

def planEquiv006 (C : Type*) : graph006.Coloring C ≃ Plan006 C :=
  (SimpleGraph.coloringCongr graphIso006.symm (Equiv.refl C)).trans
    (TwoDiamondBoundaryElimination.coloringEquiv _ _)

@[simp] theorem reconstruct_boundary006 (C : Type*) (p : Plan006 C) (v : Fin 9) :
    (planEquiv006 C).symm p (graphIso006 (.inl v)) = p.1 v := by
  change TwoDiamondBoundaryElimination.reconstruct _ _ p.1 p.2
    (graphIso006.symm (graphIso006 (.inl v))) = p.1 v
  rw [graphIso006.symm_apply_apply]
  rfl

theorem context006 {C : Type*} (accepts : (Fin 9 → C) → Prop) :
    (∃ k : graph006.Coloring C, accepts (fun v => k (graphIso006 (.inl v)))) ↔
      ∃ p : Plan006 C, accepts p.1 := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨planEquiv006 C k, hk⟩
  · rintro ⟨p, hp⟩
    refine ⟨(planEquiv006 C).symm p, ?_⟩
    simpa only [reconstruct_boundary006] using hp

theorem summaryTrace006 (et : List Color) :
    (cfmap cf006).map.RingTrace (cfring cf006).reverse et ↔
      ∃ p : Plan006 Color, et = trace ((List.finRange 9).map p.1) := by
  rw [reducibilityTrace006]
  have ports : (List.finRange 9).map (fun v => graphIso006 (.inl v)) = boundary006 := by
    decide +kernel
  simpa only [← ports, List.map_map, Function.comp_def] using
    context006 (fun b => et = trace ((List.finRange 9).map b))

def degree006 (v : Fin 16) : ℕ := entry "EDEFEDEFDGGFFFFF" v.val
def stars006 : Fin 16 → List (Fin 16) :=
  ConfigurationFaceGraph.star table006.map vertex006 representative006 degree006

def darts006 : List (Fin 72) := [71]

theorem enumeration006 :
    (ctrenum cf006.prog).map realization006.numbering = numberedKernelEdges program006 :=
  Realization.map_numbering_of_heq (n := 72) (t := table006) (p := 0)
    { numbering := (index program006).symm
      map_eq := numbered006
      point_eq := by decide +kernel } reference006 (kernelEdges_heq program006)

set_option maxRecDepth 32768 in
theorem contract006 : (cfcontract cf006).map realization006.numbering = darts006 := by
  unfold cfcontract
  erw [← listMask_map, enumeration006]
  decide +kernel

theorem contractTrace006 (et : List Color) :
    (cfmap cf006).map.CcRingTrace (cfcontract cf006) (cfring cf006).reverse et ↔
      ∃ k : faces006.ContractAssignment darts006,
        et = trace (boundary006.map k.val) := by
  rw [realization006.ccRingTrace, contract006, cfring, List.reverse_reverse,
    realization006.ring, cpring006, faces006.ccRingTrace_iff]
  rfl

end FourColor.TwoDiamondConfigurations
