import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Separating vertices by transporting equalities of partial cubic darts

A partial cubic diagram specifies three slots at each vertex, a rotation,
and the internal edge reversals. A realization preserves actual darts and
these operations. Equal darts remain equal when the same operation is
applied to both. A bounded search can therefore refute a proposed equality
by reaching two distinct slots, a loop, or a short closed path.

Triangle-freeness and local slot injectivity justify the terminal tests.
The search theorem is independent of the diagram's size or its exterior.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation

open _root_.SimpleGraph

abbrev Dart (W : Type*) := W × Fin 3

structure Diagram (W : Type*) where
  rotate : Dart W → Dart W
  flip : Dart W → Option (Dart W)
  flip_reverse : ∀ d e, flip d = some e → flip e = some d

namespace Diagram
variable {W : Type*} (P : Diagram W)

def Path (P : Diagram W) : ℕ → W → W → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ s e, P.flip (u, s) = some e ∧ Path P n e.1 v

variable [DecidableEq W]

def pathCheck (P : Diagram W) : ℕ → W → W → Bool
  | 0, u, v => decide (u = v)
  | n + 1, u, v => (List.finRange 3).any fun s =>
      match P.flip (u, s) with
      | none => false
      | some e => pathCheck P n e.1 v

theorem pathCheck_sound {n : ℕ} {u v : W} (h : P.pathCheck n u v = true) :
    P.Path n u v := by
  induction n generalizing u with
  | zero =>
    change u = v
    exact of_decide_eq_true h
  | succ n ih =>
    obtain ⟨s, _, hs⟩ := List.any_eq_true.mp h
    cases he : P.flip (u, s) with
    | none => simp [he] at hs
    | some e => exact ⟨s, e, he, ih (by simpa [he] using hs)⟩

def apart (a b : Dart W) : Bool :=
  if a.1 = b.1 then decide (a.2 ≠ b.2)
  else P.pathCheck 1 a.1 b.1 || P.pathCheck 2 a.1 b.1 || P.pathCheck 3 a.1 b.1

/-- Both sides take the same operation and keep their joint state. -/
def separates (P : Diagram W) : ℕ → Dart W → Dart W → Bool
  | 0, a, b => P.apart a b
  | n + 1, a, b => P.apart a b || separates P n (P.rotate a) (P.rotate b) ||
      match P.flip a, P.flip b with
      | some a', some b' => separates P n a' b'
      | _, _ => false

end Diagram

variable {W V : Type*} {G : SimpleGraph V}

/-- An actual interpretation of the partial diagram. All three slots are
real graph darts; their geometric properties are proved by the consumer. -/
structure Realization (P : Diagram W) (G : SimpleGraph V) where
  vertex : W → V
  dart : Dart W → G.Dart
  fst : ∀ d, (dart d).fst = vertex d.1
  slots_injective : ∀ v, Function.Injective (fun s => dart (v, s))
  slots_surjective : ∀ v d, d.fst = vertex v → ∃ s, dart (v, s) = d
  rotation : G.Dart → G.Dart
  rotate_eq : ∀ d, dart (P.rotate d) = rotation (dart d)
  flip_eq : ∀ d e, P.flip d = some e → (dart d).symm = dart e

namespace Realization
variable {P : Diagram W} (F : Realization P G)

/-- Triangle-freeness is stated directly in the target graph. -/
def TriangleFree : Prop := ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False

theorem snd_of_flip {d e : Dart W} (he : P.flip d = some e) :
    (F.dart d).snd = F.vertex e.1 := by
  have h := congrArg (fun d : G.Dart => d.fst) (F.flip_eq d e he)
  change (F.dart d).snd = (F.dart e).fst at h
  exact h.trans (F.fst e)

theorem adjacent_of_flip {d e : Dart W} (he : P.flip d = some e) :
    G.Adj (F.vertex d.1) (F.vertex e.1) := by
  have h := (F.dart d).adj
  rwa [F.fst, F.snd_of_flip he] at h

theorem neighbor_unique {u : W} {s t : Fin 3} {e f : Dart W}
    (he : P.flip (u, s) = some e) (hf : P.flip (u, t) = some f)
    (hv : F.vertex e.1 = F.vertex f.1) : e.1 = f.1 := by
  have hd : F.dart (u, s) = F.dart (u, t) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((F.fst (u, s)).trans (F.fst (u, t)).symm)
      ((F.snd_of_flip he).trans (hv.trans (F.snd_of_flip hf).symm))
  have hs := F.slots_injective u hd
  subst t
  exact congrArg Prod.fst (Option.some.inj (he.symm.trans hf))

theorem adjacent_of_path_one {u v : W} (h : P.Path 1 u v) :
    G.Adj (F.vertex u) (F.vertex v) := by
  obtain ⟨s, e, he, hv⟩ := h
  change e.1 = v at hv
  simpa only [hv] using F.adjacent_of_flip he

theorem ne_of_path_two {u v : W} (hne : u ≠ v) (h : P.Path 2 u v) :
    F.vertex u ≠ F.vertex v := by
  obtain ⟨s, e, he, t, f, hf, hv⟩ := h
  change f.1 = v at hv
  intro hc
  have hback := P.flip_reverse (u, s) e he
  have hsame := F.neighbor_unique hback hf (by simpa [hv] using hc)
  exact hne (hsame.trans hv)

theorem ne_of_path_three (ht : TriangleFree (G := G)) {u v : W}
    (h : P.Path 3 u v) : F.vertex u ≠ F.vertex v := by
  obtain ⟨s, e, he, t, f, hf, q, g, hg, hv⟩ := h
  change g.1 = v at hv
  intro hc
  have hlast := F.adjacent_of_flip hg
  rw [hv, ← hc] at hlast
  exact ht (F.vertex u) (F.vertex e.1) (F.vertex f.1)
    (F.adjacent_of_flip (d := (u, s)) he) (F.adjacent_of_flip (d := (e.1, t)) hf) hlast

variable [DecidableEq W]

theorem apart_sound (ht : TriangleFree (G := G)) {a b : Dart W}
    (h : P.apart a b = true) : F.dart a ≠ F.dart b := by
  intro he
  have hv : F.vertex a.1 = F.vertex b.1 := by
    simpa only [F.fst] using congrArg (fun d : G.Dart => d.fst) he
  unfold Diagram.apart at h
  split at h
  · rename_i hab
    have hs : a.2 ≠ b.2 := of_decide_eq_true h
    have he' : F.dart (a.1, a.2) = F.dart (a.1, b.2) := by
      exact he.trans (congrArg F.dart (Prod.ext hab.symm rfl))
    exact hs (F.slots_injective _ he')
  · rename_i hab
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rcases h with h | h
      · exact (F.adjacent_of_path_one (P.pathCheck_sound h)).ne hv
      · exact F.ne_of_path_two hab (P.pathCheck_sound h) hv
    · exact F.ne_of_path_three ht (P.pathCheck_sound h) hv

/-- Equality preservation along the pair of paths lifts every successful
finite separation check to a proof about genuine graph darts. -/
theorem separates_sound (ht : TriangleFree (G := G)) {n : ℕ} {a b : Dart W}
    (h : P.separates n a b = true) : F.dart a ≠ F.dart b := by
  induction n generalizing a b with
  | zero => exact F.apart_sound ht h
  | succ n ih =>
    intro he
    simp only [Diagram.separates, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases h with h | h
      · exact F.apart_sound ht h he
      · apply ih h
        rw [F.rotate_eq, F.rotate_eq, he]
    · cases ha : P.flip a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : P.flip b with
        | none => simp [ha, hb] at h
        | some b' =>
          apply ih (by simpa [ha, hb] using h)
          exact (F.flip_eq a a' ha).symm.trans
            ((congrArg SimpleGraph.Dart.symm he).trans (F.flip_eq b b' hb))

/-- One checked finite diagram can be used in every target graph satisfying
the realization laws and triangle-freeness. -/
theorem vertex_injective (ht : TriangleFree (G := G)) (n : ℕ)
    (hc : ∀ u v, u ≠ v → ∀ s, P.separates n (u, 0) (v, s) = true) :
    Function.Injective F.vertex := by
  intro u v he
  by_contra hne
  obtain ⟨s, hs⟩ := F.slots_surjective v (F.dart (u, 0)) ((F.fst _).trans he)
  exact F.separates_sound ht (hc u v hne s) hs.symm

end Realization
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation
