import Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation

/-!
# Certified joint routes through partial cubic diagrams

A route records simultaneous rotations and internal reversals of two
darts. Its terminal separation is justified by distinct cubic slots or
an actual path of length at most four. Four-edge terminals retain the
two distinct opposite corners needed to exclude genuine four-cycles.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation

namespace Diagram
variable {W : Type*} [DecidableEq W] (P : Diagram W)

/-- A genuine four-edge path certificate retains both opposite-corner
distinctions. Arbitrary closed walks are not accepted as four-cycles. -/
def fourPathCheck (u v : W) : Bool :=
  (List.finRange 3).any fun s => match P.flip (u,s) with
    | none => false
    | some b => (List.finRange 3).any fun t => match P.flip (b.1,t) with
      | none => false
      | some c => (List.finRange 3).any fun r => match P.flip (c.1,r) with
        | none => false
        | some d => (List.finRange 3).any fun q => match P.flip (d.1,q) with
          | none => false
          | some e => decide (u ≠ c.1 ∧ b.1 ≠ d.1 ∧ e.1 = v)

def girthApart (a b : Dart W) : Bool := P.apart a b || P.fourPathCheck a.1 b.1

/-- A binary route uses least-significant zero bits for simultaneous
rotation and one bits for internal reversal of both darts. The final
sentinel one performs the terminal test; zero and exhausted fuel reject.
Every successful check reconstructs the same joint transport history. -/
def routeCheck (code : ℕ) : ℕ → Dart W → Dart W → Bool
  | 0, _, _ => false
  | n+1, a, b =>
    if code = 1 then P.girthApart a b
    else if code = 0 then false
    else if code % 2 = 0 then routeCheck (code/2) n (P.rotate a) (P.rotate b)
    else match P.flip a, P.flip b with
      | some a', some b' => routeCheck (code/2) n a' b'
      | _, _ => false

end Diagram

namespace Realization
variable {W V : Type*} [DecidableEq W] {P : Diagram W}
  {G : SimpleGraph V} (F : Realization P G)

theorem fourPathCheck_sound (hfour : FourCycleFree (G := G)) {u v : W}
    (h : P.fourPathCheck u v = true) : F.vertex u ≠ F.vertex v := by
  obtain ⟨s,_,hs⟩ := List.any_eq_true.mp h
  cases hb : P.flip (u,s) with
  | none => simp [hb] at hs
  | some b =>
    obtain ⟨t,_,ht⟩ := List.any_eq_true.mp (by simpa only [hb] using hs)
    cases hc : P.flip (b.1,t) with
    | none => simp [hc] at ht
    | some c =>
      obtain ⟨r,_,hr⟩ := List.any_eq_true.mp (by simpa only [hc] using ht)
      cases hd : P.flip (c.1,r) with
      | none => simp [hd] at hr
      | some d =>
        obtain ⟨q,_,hq⟩ := List.any_eq_true.mp (by simpa only [hd] using hr)
        cases he : P.flip (d.1,q) with
        | none => simp [he] at hq
        | some e =>
          have hh : u ≠ c.1 ∧ b.1 ≠ d.1 ∧ e.1 = v :=
            of_decide_eq_true (by simpa only [he] using hq)
          exact F.ne_of_path_four hfour hh.1 hh.2.1
            ⟨s,b,hb,rfl⟩ ⟨t,c,hc,rfl⟩ ⟨r,d,hd,rfl⟩ ⟨q,e,he,hh.2.2⟩

theorem girthApart_sound (ht : TriangleFree (G := G)) (hf : FourCycleFree (G := G))
    {a b : Dart W} (h : P.girthApart a b = true) : F.dart a ≠ F.dart b := by
  simp only [Diagram.girthApart, Bool.or_eq_true] at h
  rcases h with ha | hb
  · exact F.apart_sound ht ha
  · intro he
    apply F.fourPathCheck_sound hf hb
    simpa only [F.fst] using congrArg (fun d : G.Dart => d.fst) he

/-- A checked route preserves the same proposed dart equality at every
step; it does not replace it by independent marginal choices. -/
theorem routeCheck_sound (ht : TriangleFree (G := G)) (hf : FourCycleFree (G := G))
    (code : ℕ) {n : ℕ} {a b : Dart W}
    (h : P.routeCheck code n a b = true) : F.dart a ≠ F.dart b := by
  induction n generalizing code a b with
  | zero => simp [Diagram.routeCheck] at h
  | succ n ih =>
    intro he
    simp only [Diagram.routeCheck] at h
    split at h
    · exact F.girthApart_sound ht hf h he
    · split at h
      · simp at h
      · split at h
        · apply ih (code/2) h
          rw [F.rotate_eq, F.rotate_eq, he]
        · cases ha : P.flip a with
          | none => simp [ha] at h
          | some a' =>
            cases hb : P.flip b with
            | none => simp [ha,hb] at h
            | some b' =>
              apply ih (code/2) (by simpa only [ha,hb] using h)
              exact (F.flip_eq a a' ha).symm.trans
                ((congrArg SimpleGraph.Dart.symm he).trans (F.flip_eq b b' hb))

end Realization
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation
