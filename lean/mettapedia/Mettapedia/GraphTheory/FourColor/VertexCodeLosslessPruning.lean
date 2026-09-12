import Mettapedia.GraphTheory.FourColor.VertexCodeDefectMonotone
import Mettapedia.GraphTheory.FourColor.VertexCodeTerminalAcceptance

/-!
# Lossless pruning of proper prefixes of connected planar runs

A hidden component remains hidden after attachment and is separated from
the newly born vertex. A handle likewise cannot be removed by later steps.
Thus every proper prefix of a connected zero-defect completion belongs to
the finite viable carrier. This assertion deliberately does not assume the
completion is colourable: uncolourable source objects may not be pruned away.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeLosslessPruning

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamMultigraph SerialTangleSmallCutTransfer
open BoundarySmallCutProfile BoundarySmallCutTransfer BoundarySmallCutViability
open BoundaryConnectivity VertexCodeDefectMonotone
open VertexCodeTrace VertexCodeRealization VertexAttachmentTransfer
open TubeSlab.VertexTransfer VertexCodePartition TwoSidedBoundaryReindex

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L P R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R]

def Hidden (A : TwoSidedOpenTangleData V I L P) : Prop :=
  HasHidden (profile (sideMultigraph (asOpen A)) (asOpen A).boundaryVert)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
theorem hidden_serial (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) [Nonempty W] (ha : Hidden A) :
    Hidden (A.serialCompose B (Equiv.refl P)) ∧
      ¬ (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P)))).Connected := by
  obtain ⟨a, ha, hs, hz, hp⟩ := ha
  let b := state (sideMultigraph (asOpen B)) (asOpen B).boundaryVert (fun _ => false)
  have hb : b ∈ profile (sideMultigraph (asOpen B)) (asOpen B).boundaryVert := ⟨_, rfl⟩
  have hb0 : b.cost.val = 0 := by simp [b, state, cutSize]
  have hbo : b.omitted = true := by simp [b, state]
  have hq : composeState a b ∈ profile
      (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P))))
        (asOpen (A.serialCompose B (Equiv.refl P))).boundaryVert := by
    rw [profile_serial]
    exact ⟨a, ha, b, hb, rfl⟩
  have hqs : (composeState a b).selected = true := by simp [composeState, hs]
  have hqo : (composeState a b).omitted = true := by simp [composeState, hbo]
  have hqz : (composeState a b).cost.val = 0 := by
    change min 2 (a.cost.val + b.cost.val +
      ∑ p, if a.boundary (.inr p) = b.boundary (.inl p) then 0 else 1) = 0
    have hbp (p : P) : b.boundary (.inl p) = false := rfl
    simp only [hz, hb0, hp, hbp, if_true, Finset.sum_const_zero]
    rfl
  have hqp : ∀ p, (composeState a b).boundary p = false := by
    rintro (l | r)
    · exact hp (.inl l)
    · rfl
  refine ⟨⟨composeState a b, hq, hqs, hqz, hqp⟩, ?_⟩
  intro hc
  obtain ⟨s, hs'⟩ := hq
  rw [← hs'] at hqs hqo hqz
  simp only [state, decide_eq_true_eq] at hqs hqo
  obtain ⟨v, hv⟩ := hqs
  obtain ⟨w, hw⟩ := hqo
  have hz' : cutSize (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P)))) s = 0 :=
    (state_cost_zero _ _ s).mp hqz
  have hh := (reach_iff_zero_cuts _ v w).mp (hc v w) s hz'
  simp [hv, hw] at hh

section Reindex
variable {L' R' : Type*} [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R']
omit [Fintype V] [DecidableEq V] [DecidableEq I] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R'] in
theorem hidden_reindex (A : TwoSidedOpenTangleData V I L P) (e : L' ⊕ R' ≃ L ⊕ P) :
    Hidden (reindex A e) ↔ Hidden A := by
  unfold Hidden
  rw [hidden_iff_not_visible, hidden_iff_not_visible, TwoSidedBoundaryJoint.side_reindex]
  have hv : PortVisible (sideMultigraph (asOpen A)) (asOpen (reindex A e)).boundaryVert ↔
      PortVisible (sideMultigraph (asOpen A)) (asOpen A).boundaryVert := by
    constructor
    · intro h v
      obtain ⟨p, hp⟩ := h v
      exact ⟨e p, (TwoSidedBoundaryJoint.boundary_reindex A e p) ▸ hp⟩
    · intro h v
      obtain ⟨p, hp⟩ := h v
      refine ⟨e.symm p, ?_⟩
      rwa [TwoSidedBoundaryJoint.boundary_reindex, Equiv.apply_symm_apply]
  exact not_congr hv
end Reindex

omit [Fintype V] [DecidableEq V] in
theorem hidden_attach {l r : ℕ} (a : Code l r) (h : Valid a)
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) (ht : Hidden T) :
    Hidden (attach a h T) ∧ ¬ (sideMultigraph (asOpen (attach a h T))).Connected := by
  have hi : Hidden (prepared a h T) := (hidden_reindex T _).mpr ht
  have hh := hidden_serial (prepared a h T) (star (starOrder a h)) hi
  exact ⟨(hidden_reindex _ _).mpr hh.1, hh.2⟩

omit [Fintype V] [DecidableEq V] [DecidableEq I] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] in
theorem hidden_decEq (T : TwoSidedOpenTangleData V I L P) (d e : DecidableEq I) :
    (letI := d; Hidden T) ↔ (letI := e; Hidden T) := by
  cases Subsingleton.elim d e
  rfl

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P] in
theorem connected_decEq (T : TwoSidedOpenTangleData V I L P) (d e : DecidableEq I) :
    (letI := d; (sideMultigraph (asOpen T)).Connected) ↔
      (letI := e; (sideMultigraph (asOpen T)).Connected) := by
  cases Subsingleton.elim d e
  rfl

theorem hidden_step {l r : ℕ} (t : Trace l) (a : Code l r) (h : Valid a) (ht : Hidden t.realize) :
    Hidden (Trace.step t a h).realize ∧
      ¬ (sideMultigraph (asOpen (Trace.step t a h).realize)).Connected := by
  letI : DecidableEq t.Interior := Classical.decEq _
  have hh := hidden_attach a h t.realize ht
  exact ⟨(hidden_decEq (attach a h t.realize) inferInstance (Classical.decEq _)).mp hh.1,
    fun hc => hh.2 ((connected_decEq (attach a h t.realize) inferInstance (Classical.decEq _)).mpr hc)⟩

inductive ProperPrefix : {l r : ℕ} → Trace l → Trace r → Prop
  | here {l r} (t : Trace l) (a : Code l r) (h : Valid a) : ProperPrefix t (.step t a h)
  | step {l m r} {s : Trace l} {t : Trace m} (hp : ProperPrefix s t)
      (a : Code m r) (h : Valid a) : ProperPrefix s (.step t a h)

theorem ProperPrefix.prefix {l r} {s : Trace l} {t : Trace r} (h : ProperPrefix s t) : Prefix s t := by
  induction h with
  | here t a h => exact .step (.refl t) a h
  | step _ a h ih => exact .step ih a h

theorem hidden_extension {l r} {s : Trace l} {t : Trace r} (h : ProperPrefix s t) (hs : Hidden s.realize) :
    Hidden t.realize ∧ ¬ (sideMultigraph (asOpen t.realize)).Connected := by
  induction h with
  | here t a h => exact hidden_step t a h hs
  | step _ a h ih => exact hidden_step _ a h (ih hs).1

/-- Losslessness for the structural source class, not merely for already
colourable runs. Proper prefixes may themselves be disconnected. -/
theorem viable_of_connected_planar_completion {l r} {s : Trace l} {t : Trace r}
    (hp : ProperPrefix s t) (hc : (sideMultigraph (asOpen t.realize)).Connected)
    (ht : VertexAttachmentTransfer.defect t.realize = 0) :
    VertexCodeViablePrefix.Viable (ExecutableVertexCode.evaluate s) = true := by
  rw [VertexCodeViablePrefix.viable_iff_visible_planar]
  refine ⟨?_, planar_prefix hp.prefix ht⟩
  by_contra hv
  exact (hidden_extension hp ((hidden_iff_not_visible _ _).mpr hv)).2 hc

theorem viable_of_accepted_completion {l} {s : Trace l} {t : Trace 0}
    (hp : ProperPrefix s t) (ht : VertexCodeTerminalAcceptance.Accepts t = true) :
    VertexCodeViablePrefix.Viable (ExecutableVertexCode.evaluate s) = true := by
  obtain ⟨⟨hc, _⟩, hd, _⟩ := (VertexCodeTerminalAcceptance.accepts_iff_planar_colouring t).mp ht
  exact viable_of_connected_planar_completion hp hc hd

/-- The executable pruning schedule tests an object only when a further
vertex will be attached. In particular it does not test the closed terminal
object as an extendable prefix. -/
def prefixesViable : {r : ℕ} → Trace r → Bool
  | _, .first _ _ => true
  | _, .step t _ _ => prefixesViable t && VertexCodeViablePrefix.Viable (ExecutableVertexCode.evaluate t)

theorem prefixesViable_iff {r} (t : Trace r) : prefixesViable t = true ↔
    ∀ {l} (s : Trace l), ProperPrefix s t →
      VertexCodeViablePrefix.Viable (ExecutableVertexCode.evaluate s) = true := by
  induction t with
  | first a h =>
    constructor
    · intro _ l s hp; cases hp
    · intro _; rfl
  | step t a h ih =>
    rw [prefixesViable, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hp, ht⟩ l s hs
      cases hs with
      | here => exact ht
      | step hs _ _ => exact hp s hs
    · intro hp
      exact ⟨fun s hs => hp s (.step hs a h), hp t (.here t a h)⟩

theorem prefixesViable_of_connected_planar {r} (t : Trace r)
    (hc : (sideMultigraph (asOpen t.realize)).Connected)
    (ht : VertexAttachmentTransfer.defect t.realize = 0) : prefixesViable t = true := by
  rw [prefixesViable_iff]
  exact fun _ hp => viable_of_connected_planar_completion hp hc ht

def prunedAccepts (t : Trace 0) : Bool := prefixesViable t && VertexCodeTerminalAcceptance.Accepts t

/-- Literal terminal acceptance is unchanged by the finite-prefix pruning.
The stronger structural theorem above also covers uncolourable completions. -/
theorem prunedAccepts_eq (t : Trace 0) : prunedAccepts t = VertexCodeTerminalAcceptance.Accepts t := by
  cases ht : VertexCodeTerminalAcceptance.Accepts t with
  | false => simp [prunedAccepts, ht]
  | true =>
    have hp : prefixesViable t = true := (prefixesViable_iff t).mpr
      (fun _ h => viable_of_accepted_completion h ht)
    simp [prunedAccepts, ht, hp]

end
end Mettapedia.GraphTheory.FourColor.VertexCodeLosslessPruning
