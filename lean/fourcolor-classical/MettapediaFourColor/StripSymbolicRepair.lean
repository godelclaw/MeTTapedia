import MettapediaFourColor.StripSourceExtension
import MettapediaFourColor.KempeMajorityRepair
import MettapediaFourColor.KempeChordComposition
import MettapediaFourColor.KempeChromogramMatching

/-!
# A variable boundary segment with one composed repair strategy

The boundary segment has three forms, changing the exterior's possible
component choices. Two use one anchor exchange followed by the majority
law; the third may use a further anchor exchange before that same law.
Successful answers are reconstructed from symbolic ear relations; no
stored list of full colouring witnesses is consumed. The exterior matching
is recovered by a uniform chord scan at arbitrary width.
-/

namespace FourColor.StripSymbolicRepair

open Color TriangleStripAnchors KempeBoundarySplit KempeMatchingChromogram
open StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

abbrev Terminal := GraphTrace input0099.graph input0099.boundary

def readBoundary (et : List Color) (i : Fin 11) : Color :=
  (untrace 0 et)[i.val]?.getD 0

/-- Re-evaluate the symbolic joins at the changed boundary. -/
def Direct (et : List Color) : Prop :=
  trace (List.ofFn (readBoundary et)) = et ∧
    ProperBoundary (readBoundary et) ∧ ∃ a c, r5 (readBoundary et) a c

instance (et : List Color) : Decidable (Direct et) := by
  unfold Direct
  infer_instance

theorem direct_sound {et : List Color} (h : Direct et) : Terminal et :=
  h.1 ▸ graphTrace (readBoundary et) h.2.1 h.2.2

theorem direct_coclosure {et : List Color} (h : Direct et) : KempeCoclosure Terminal et := by
  intro outside _ hold
  exact ⟨et, direct_sound h, hold⟩

def segment (x y z : Color) : Boundary :=
  ![c0,c1,c0,c1,c3,x,y,z,c1,c0,c1]

/-- Both ends next to the forced-colour ear use 0 and 3; the adjacent
interior vertex retains colour 1 as a possible choice. -/
def Admissible (x y z : Color) : Prop :=
  x ≠ c1 ∧ x ≠ c3 ∧ ((y = c0 ∧ z = c3) ∨ (y = c3 ∧ z = c0)) ∧ x ≠ y

instance (x y z : Color) : Decidable (Admissible x y z) := by
  unfold Admissible
  infer_instance

def colours (s phase : Bool) : Boundary :=
  ![c0,c1,c0,c1,c3,if s then c0 else c2,if s then c3 else c0,
    if s then c0 else c3,c1,if phase then c3 else c0,c1]

def word (s phase : Bool) (i : Fin 11) : Color :=
  colours s phase i + colours s phase ⟨(i.val + 1) % 11, Nat.mod_lt _ (by decide)⟩

theorem word_trace : ∀ s phase,
    List.ofFn (word s phase) = trace (List.ofFn (colours s phase)) := by decide +kernel

def embed : Bool → Fin 6 → Fin 11
  | false => ![7,8,9,3,5,6]
  | true => ![6,8,9,3,4,5]

def rank (s : Bool) (i : Fin 11) : Fin 6 :=
  if i = embed s 0 then 0 else if i = embed s 1 then 1 else
    if i = embed s 2 then 2 else if i = embed s 3 then 3 else
    if i = embed s 4 then 4 else 5

theorem coordinates : ∀ s,
    (∀ i, rank s (embed s i) = i) ∧
    (∀ i, word s true i ≠ c1 → embed s (rank s i) = i) ∧
    (∀ i, word s true (embed s i) ≠ c1) ∧ (∀ i, word s true i ≠ 0) := by decide +kernel

private instance {n : ℕ} (a b c d : Fin n) : Decidable (ChordsCross a b c d) := by
  unfold ChordsCross
  infer_instance

theorem order : ∀ s a b x y,
    ¬ ChordsCross (embed s a) (embed s x) (embed s b) (embed s y) →
      ¬ ChordsCross a x b y := by decide +kernel

def block : Finset (Fin 6) := {0,1,2,3}

theorem convex : ∀ a ∈ block, ∀ b ∈ block, ∀ x, a < x → x < b → x ∈ block := by
  decide +kernel

theorem majority : 6 < 2 * block.card := by decide +kernel

def good (s : Bool) (a b : Fin 11) : Bool :=
  ([(if s then 6 else 7,8),(8,9),(3,9)] : List (Fin 11 × Fin 11)).contains
    (min a b, max a b)

theorem successful : ∀ s, ∀ a ∈ block, ∀ b ∈ block, b.val = a.val + 1 →
    good s (embed s a) (embed s b) = true := by decide +kernel

/-- All successful pair choices are certified by the same symbolic joins. -/
theorem direct_pairs : ∀ s a b, good s a b = true →
    Direct (List.ofFn (KempeIntervalRepair.switch (word s true) a b)) := by decide +kernel

theorem initial_answers : ∀ s, ∀ t ∈ KempeChordExchange.answers
    ((List.ofFn (word s false)).map EdgePerm.e321) 9,
    Direct (t.map EdgePerm.e321) ∨ t.map EdgePerm.e321 = List.ofFn (word s true) := by
  decide +kernel

theorem initial_active : ∀ s,
    ((((List.ofFn (word s false)).map EdgePerm.e321).rotate 9).headD 0).hi = true := by
  decide +kernel

def residual : List Color := [c1,c1,c1,c2,c1,c1,c3,c1,c1,c1,c1]

/-- The guard has two strategy inputs and one additional residual form.
This is a finite source-domain classification, not a repair assertion. -/
theorem classify : ∀ x y z, Admissible x y z →
    (∃ s, trace (List.ofFn (segment x y z)) = List.ofFn (word s false)) ∨
      trace (List.ofFn (segment x y z)) = residual := by decide +kernel

theorem guard_ear : ∀ x y z, Admissible x y z →
    (∀ c, unary (segment x y z) 0 c ↔ c = c2) ∧ unary (segment x y z) 3 c1 := by
  decide +kernel

/-- The same majority block supplies a successful whole component in either
boundary form, while preserving the exterior's original chromogram. -/
theorem majority_answer (s : Bool) (m : Fin 11 → Fin 11)
    (hinv : Function.Involutive m) (hnc : Noncrossing m)
    (hf : ∀ i, m i = i ↔ word s true i = c1) :
    ∃ et, Terminal et ∧ matchg [] et (gram m (word s true)) := by
  have terminal : ∀ a b, good s a b = true →
      Terminal (List.ofFn (KempeIntervalRepair.switch (word s true) a b)) :=
    fun a b h => direct_sound (direct_pairs s a b h)
  have lift := (KempeMajorityRepair.active_mate (word s true) m hinv hf
    (embed s) (rank s) (coordinates s).1 (coordinates s).2.1 (coordinates s).2.2.1).1
  have horder : IsNoncrossingMatching (fun i => rank s (m (embed s i))) := by
    intro a b
    apply order s a b
    rw [lift, lift]
    exact hnc (embed s a) (embed s b)
  obtain ⟨_, _, ht, hm⟩ := KempeMajorityRepair.answer
    (word s true) (good s) Terminal terminal (embed s) (rank s)
    (coordinates s).1 (coordinates s).2.1 (coordinates s).2.2.1
    block convex majority (successful s) m hinv hnc (coordinates s).2.2.2 hf horder
  exact ⟨_, ht, hm⟩

theorem majority_coclosure (s : Bool) : KempeCoclosure Terminal (List.ofFn (word s true)) := by
  apply KempeChromogramMatching.majority_coclosure (word s true) (embed s) (rank s)
    (coordinates s).1 (coordinates s).2.1 (coordinates s).2.2.1
    (order s) block convex majority
  intro a ha b hb hadj
  exact direct_coclosure (direct_pairs s _ _ (successful s a ha b hb hadj))

/-- Both initial boundaries follow the same two-stage argument. All colour
witnesses come from source reconstruction after symbolic elimination. -/
theorem source_repair (s : Bool) : KempeCoclosure Terminal (List.ofFn (word s false)) := by
  apply kempeCoclosure_of_map EdgePerm.e321
  apply KempeChordExchange.coclosure_of_answers _ 9 (by simp) (initial_active s)
  intro t ht
  apply kempeCoclosure_of_map EdgePerm.e321
  rcases initial_answers s t ht with hd | hj
  · exact direct_coclosure hd
  · rw [hj]
    exact majority_coclosure s

def residualAnswer : Bool → List Color
  | false => [c1,c1,c1,c2,c1,c1,c3,c1,c2,c2,c1]
  | true => [c1,c1,c1,c2,c1,c2,c3,c1,c1,c2,c1]

def residualPalette (s : Bool) : EdgePerm := if s then .e321 else .e123
def residualAnchor (s : Bool) : ℕ := if s then 7 else 3

theorem residual_active : ∀ s,
    residualAnchor s ≤ ((residualAnswer s).map (residualPalette s)).length ∧
    ((((residualAnswer s).map (residualPalette s)).rotate (residualAnchor s)).headD 0).hi = true :=
  by decide +kernel

theorem residual_answers : ∀ s, ∀ t ∈ KempeChordExchange.answers
    ((residualAnswer s).map (residualPalette s)) (residualAnchor s),
    Direct (t.map (residualPalette s)) ∨
      t.map (residualPalette s) = List.ofFn (word false true) := by decide +kernel

theorem residual_first : ∀ t ∈ KempeChordExchange.answers (residual.map EdgePerm.e321) 9,
    Direct (t.map EdgePerm.e321) ∨ ∃ s, t.map EdgePerm.e321 = residualAnswer s := by
  decide +kernel

/-- The harder intermediate returns to the existing majority consumer;
the other needs only one further anchor exchange. -/
theorem residual_continuation (s : Bool) : KempeCoclosure Terminal (residualAnswer s) := by
  apply kempeCoclosure_of_map (residualPalette s)
  apply KempeChordExchange.coclosure_of_answers _ (residualAnchor s)
    (residual_active s).1 (residual_active s).2
  intro t ht
  apply kempeCoclosure_of_map (residualPalette s)
  rcases residual_answers s t ht with hd | hm
  · exact direct_coclosure hd
  · rw [hm]
    exact majority_coclosure false

theorem residual_repair : KempeCoclosure Terminal residual := by
  apply kempeCoclosure_of_map EdgePerm.e321
  apply KempeChordExchange.coclosure_of_answers _ 9 (by decide) (by decide)
  intro t ht
  apply kempeCoclosure_of_map EdgePerm.e321
  rcases residual_first t ht with hd | ⟨s, he⟩
  · exact direct_coclosure hd
  · rw [he]
    exact residual_continuation s

/-- All three admissible boundary forms reconstruct an actual source
colouring in the same arbitrary Kempe-closed exterior. -/
theorem guarded_repair (x y z : Color) (h : Admissible x y z) :
    KempeCoclosure Terminal (trace (List.ofFn (segment x y z))) := by
  rcases classify x y z h with ⟨s, he⟩ | he
  · rw [he]
    exact source_repair s
  · rw [he]
    exact residual_repair

/-- The boundary observation lost by the evaluated summary is retained. -/
theorem previous_counterexample_excluded (x y z : Color) :
    segment x y z ≠ StripResponseSummary.boundary true := by
  intro h
  have he := congrFun h 2
  simp [segment, StripResponseSummary.boundary] at he

end FourColor.StripSymbolicRepair
