import Mettapedia.GraphTheory.FourColor.PartialCubicDartCutBound

/-!
# Completing the unrecorded part of a cubic boundary

An unpaired dart returning to an injectively realized diagram has another
unpaired dart as its mate. If six possible outgoing darts remain, the cubic
parity and cyclic cut bounds force every one of those six to leave.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle GoertzelV24MinimalTriangleFree

noncomputable section
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {P : Diagram W} (F : Realization P G)

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An extra internal edge pairs two of the original candidate ports. -/
theorem unpaired_mate (hv : Function.Injective F.vertex) (p : Unpaired (P := P))
    (hp : F.imageSide (F.dart p.1).snd) :
    ∃ q : Unpaired (P := P), q ≠ p ∧ (F.dart p.1).symm = F.dart q.1 := by
  obtain ⟨v, hv'⟩ := hp
  obtain ⟨s, hs⟩ := F.slots_surjective v (F.dart p.1).symm hv'.symm
  have hq : P.flip (v, s) = none := by
    cases he : P.flip (v, s) with
    | none => rfl
    | some e =>
      have hflip := F.flip_eq _ _ he
      rw [hs, SimpleGraph.Dart.symm_symm] at hflip
      have hep := F.dart_injective hv hflip
      have hr := P.flip_reverse _ _ he
      rw [← hep, p.2] at hr
      contradiction
  refine ⟨⟨(v, s), hq⟩, ?_, hs.symm⟩
  intro he
  have hd : (F.dart p.1).symm = F.dart p.1 := hs.symm.trans (congrArg F.dart (congrArg Subtype.val he))
  exact (F.dart p.1).adj.ne (congrArg (fun d : G.Dart => d.fst) hd).symm

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An unrecorded edge cannot duplicate a recorded edge in a simple graph. -/
theorem unpaired_not_recorded (hv : Function.Injective F.vertex)
    (p q : Unpaired (P := P)) (he : (F.dart p.1).symm = F.dart q.1)
    {a b : Dart W} (hab : P.flip a = some b)
    (ha : a.1 = p.1.1) (hb : b.1 = q.1.1) : False := by
  have hto : (F.dart p.1).snd = F.vertex q.1.1 :=
    (congrArg (fun d : G.Dart => d.fst) he).trans (F.fst _)
  have hd : F.dart a = F.dart p.1 := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (by rw [F.fst, F.fst, ha])
      (by rw [F.snd_of_flip hab, hto, hb])
  have hap := F.dart_injective hv hd
  rw [hap, p.2] at hab
  contradiction

omit [Fintype W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A genuine unrecorded edge cannot close a path of length at most three
in a diagram realized injectively in a graph of girth at least five. -/
theorem unpaired_no_short_path (hv : Function.Injective F.vertex)
    (ht : TriangleFree (G := G)) (hf : FourCycleFree (G := G))
    (p q : Unpaired (P := P)) (he : (F.dart p.1).symm = F.dart q.1) :
    P.pathCheck 1 p.1.1 q.1.1 = false ∧
      P.pathCheck 2 p.1.1 q.1.1 = false ∧ P.pathCheck 3 p.1.1 q.1.1 = false := by
  have hto : (F.dart p.1).snd = F.vertex q.1.1 :=
    (congrArg (fun d : G.Dart => d.fst) he).trans (F.fst _)
  have hedge : G.Adj (F.vertex p.1.1) (F.vertex q.1.1) := by
    simpa only [F.fst, hto] using (F.dart p.1).adj
  refine ⟨?_, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro hp
    obtain ⟨s, e, hs, he'⟩ := P.pathCheck_sound hp
    exact F.unpaired_not_recorded hv p q he hs rfl he'
  · apply Bool.eq_false_iff.mpr
    intro hp
    obtain ⟨s, e, hs, t, f, ht', he'⟩ := P.pathCheck_sound hp
    have hlast := F.adjacent_of_flip ht'
    rw [he'] at hlast
    exact ht _ _ _ (F.adjacent_of_flip hs) hlast hedge.symm
  · apply Bool.eq_false_iff.mpr
    intro hp
    obtain ⟨s, e, hs, t, f, ht', u, g, hu, he'⟩ := P.pathCheck_sound hp
    have hpf : p.1.1 ≠ f.1 := fun hh =>
      F.unpaired_not_recorded hv p q he hu hh.symm he'
    have heq : e.1 ≠ q.1.1 := fun hh =>
      F.unpaired_not_recorded hv p q he hs rfl hh
    have hlast := F.adjacent_of_flip hu
    rw [he'] at hlast
    exact hf _ _ _ _ (F.adjacent_of_flip hs) (F.adjacent_of_flip (d := (e.1, t)) ht')
      hlast hedge.symm (fun hh => hpf (hv hh)) (fun hh => heq (hv hh))

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every recorded diagram path stays inside the realized vertex shore. -/
theorem reachable_of_path {n : ℕ} {u v : W} (hp : P.Path n u v) :
    (G.induce {v | F.imageSide v}).Reachable
      ⟨F.vertex u, ⟨u, rfl⟩⟩ ⟨F.vertex v, ⟨v, rfl⟩⟩ := by
  induction n generalizing u with
  | zero => cases hp; exact .refl _
  | succ n ih =>
    obtain ⟨s, e, he, hp⟩ := hp
    have ha : (G.induce {v | F.imageSide v}).Adj
        ⟨F.vertex u, ⟨u, rfl⟩⟩ ⟨F.vertex e.1, ⟨e.1, rfl⟩⟩ := F.adjacent_of_flip he
    exact ha.reachable.trans (ih hp)

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Connectedness of the recorded edges survives additional internal edges. -/
theorem image_connected (root : W) (hp : ∀ v, ∃ n, P.Path n root v) :
    (G.induce {v | F.imageSide v}).Connected := by
  refine { nonempty := ⟨⟨F.vertex root, ⟨root, rfl⟩⟩⟩, preconnected := ?_ }
  rintro ⟨u, a, rfl⟩ ⟨v, b, rfl⟩
  obtain ⟨na, ha⟩ := hp a
  obtain ⟨nb, hb⟩ := hp b
  exact (F.reachable_of_path ha).symm.trans (F.reachable_of_path hb)

/-- Six remaining candidates saturate the actual cut. No assumption about
how the excluded darts pair with each other is needed. -/
theorem allowed_leaves_of_six
    (hv : Function.Injective F.vertex)
    (allowed : Unpaired (P := P) → Prop) [DecidablePred allowed]
    (hports : Fintype.card {p // allowed p} = 6)
    (hinternal : ∀ p, ¬ allowed p → F.imageSide (F.dart p.1).snd)
    (heven : Even (Fintype.card W)) (hlarge : 4 < Fintype.card W)
    (hspace : Fintype.card W + 3 ≤ Fintype.card V)
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
    (p : Unpaired (P := P)) (hp : allowed p) : ¬ F.imageSide (F.dart p.1).snd := by
  classical
  have hcard := F.card_imageSide hv
  have hle := F.crossing_card_le_of_internal allowed hinternal
  rw [hports] at hle
  have hcycle := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    hcubic F.imageSide (Fintype.card_pos_iff.mp (by omega)) (by omega)
  have hpartition := Fintype.card_subtype_compl F.imageSide
  have hfive := CyclicFiveBoundary.five_le_crossing_card hcubic hcyclic F.imageSide
    hcycle (by omega)
  have hdegree := card_crossingEdgeFinset_add_twice_internal_eq_three_mul (G := G)
    (fun v => (degree_instance_independent v _ _).trans (hcubic v)) F.imageSide
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart] at hdegree
  simp only [Nat.card_eq_fintype_card] at hdegree
  obtain ⟨k, hk⟩ := heven
  have hsix : Fintype.card (CrossingSideDart G F.imageSide) = 6 := by omega
  let f : CrossingSideDart G F.imageSide → {p // allowed p} := fun d =>
    ⟨F.crossingIndex d, by
      by_contra hn
      have hh := hinternal (F.crossingIndex d) hn
      rw [F.crossingIndex_dart] at hh
      exact d.2.2 hh⟩
  have hi : Function.Injective f := by
    intro a b he
    exact F.crossingIndex_injective (congrArg Subtype.val he)
  have hsurj : Function.Surjective f := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective f hi hn
    omega
  obtain ⟨d, hd⟩ := hsurj ⟨p, hp⟩
  have he := F.crossingIndex_dart d
  have hh : F.crossingIndex d = p := congrArg Subtype.val hd
  rw [hh] at he
  exact he.symm ▸ d.2.2

end
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization
