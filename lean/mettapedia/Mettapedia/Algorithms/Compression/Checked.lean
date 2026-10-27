import Mettapedia.Computability.KolmogorovComplexity.CompressiveFeature

/-!
# Checked incremental decomposition

The incremental feature/residual approach is due to Arthur Franz, Oleksandr
Antonenko and Roman Soletskyi, "A theory of incremental compression" (2021),
https://doi.org/10.1016/j.ins.2020.08.035. WILLIAM
(https://gitlab.com/occam_ua/william) supplies implementation inspiration and
comparison task families. This module specifies the independent checked
acceptance/composition kernel, not the complete ALICE algorithm or WILLIAM.

An executable acceptance and composition algorithm, independent of a host
language, search heuristic, or value representation. Costs are declared natural
number observations; they are not automatically prefix-code lengths. A rejected
proposal means only that this checker did not accept it. A finite proposal list
and finite fuel do not establish global optimality or search completeness.
When an inverse has several answers, a proposal includes its chosen extraction
program/branch. Those alternatives must be enumerated explicitly; this kernel
does not silently discard inverse answers inside an operation.

The final adapter instantiates the algorithm with binary programs and constructs
the existing KolmogorovComplexity.CompressionStep, rather than introducing a
second mathematical notion of a compressive feature.
-/

namespace Mettapedia.Algorithms.Compression.Checked

universe u v

structure Model (Data : Type u) (Feature : Type v) where
  extract : Feature → Data → Option Data
  expand : Feature → Data → Option Data
  featureCost : Feature → Nat
  dataCost : Data → Nat

variable {D : Type u} {F : Type v} [DecidableEq D]

/-- Compute the residual, check reconstruction, then require a strict gain. -/
def accept (m : Model D F) (source : D) (feature : F) : Option D :=
  match m.extract feature source with
  | none => none
  | some residual =>
      if m.expand feature residual = some source ∧
          m.featureCost feature + m.dataCost residual < m.dataCost source then
        some residual
      else none

theorem accept_iff (m : Model D F) (source : D) (feature : F) (residual : D) :
    accept m source feature = some residual ↔
      m.extract feature source = some residual ∧
      m.expand feature residual = some source ∧
      m.featureCost feature + m.dataCost residual < m.dataCost source := by
  cases hx : m.extract feature source with
  | none => simp [accept, hx]
  | some value =>
      by_cases good : m.expand feature value = some source ∧
          m.featureCost feature + m.dataCost value < m.dataCost source
      · simp only [accept, hx, if_pos good, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨rfl, good⟩
        · intro h
          exact h.1
      · simp only [accept, hx, if_neg good, Option.some.injEq]
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨rfl, reconstructed, smaller⟩
          exact False.elim (good ⟨reconstructed, smaller⟩)

/-- Policy: first accepted proposal, not first inverse answer or best score. -/
def select (m : Model D F) (source : D) : List F → Option (F × D)
  | [] => none
  | feature :: rest =>
      match accept m source feature with
      | some residual => some (feature, residual)
      | none => select m source rest

theorem select_sound (m : Model D F) (source : D) (proposals : List F)
    (feature : F) (residual : D)
    (h : select m source proposals = some (feature, residual)) :
    feature ∈ proposals ∧ accept m source feature = some residual := by
  induction proposals with
  | nil => simp [select] at h
  | cons first rest ih =>
      cases ha : accept m source first with
      | none =>
          have tail := ih (by simpa [select, ha] using h)
          exact ⟨List.mem_cons_of_mem _ tail.1, tail.2⟩
      | some value =>
          have equal : (first, value) = (feature, residual) := by
            simpa [select, ha] using h
          cases equal
          exact ⟨List.mem_cons_self, ha⟩

theorem select_none_iff (m : Model D F) (source : D) (proposals : List F) :
    select m source proposals = none ↔
      ∀ feature ∈ proposals, accept m source feature = none := by
  induction proposals with
  | nil => simp [select]
  | cons feature rest ih =>
      cases ha : accept m source feature <;> simp [select, ha, ih]

/-- Reconstruct in reverse extraction order. -/
def restore (m : Model D F) : List F → D → Option D
  | [], residual => some residual
  | feature :: rest, residual =>
      (restore m rest residual).bind (m.expand feature)

def cost (m : Model D F) (features : List F) (residual : D) : Nat :=
  (features.map m.featureCost).sum + m.dataCost residual

/-- Bounded search over the supplied finite proposal family at each residual. -/
def compress (m : Model D F) (propose : D → List F) : Nat → D → List F × D
  | 0, source => ([], source)
  | fuel + 1, source =>
      match select m source (propose source) with
      | none => ([], source)
      | some (feature, residual) =>
          let tail := compress m propose fuel residual
          (feature :: tail.1, tail.2)

/-- Acceptance checks suffice for the complete resulting chain, regardless
of how proposals were generated or ordered. This proves the actual recursive
algorithm, not a property assumed of its returned plan. -/
theorem compress_correct (m : Model D F) (propose : D → List F)
    (fuel : Nat) (source : D) :
    restore m (compress m propose fuel source).1
      (compress m propose fuel source).2 = some source ∧
    cost m (compress m propose fuel source).1
      (compress m propose fuel source).2 ≤ m.dataCost source ∧
    (compress m propose fuel source).1.length ≤ fuel ∧
    (compress m propose fuel source).1.length ≤ m.dataCost source := by
  induction fuel generalizing source with
  | zero => simp [compress, restore, cost]
  | succ fuel ih =>
      cases hs : select m source (propose source) with
      | none => simp [compress, hs, restore, cost]
      | some result =>
          rcases result with ⟨feature, residual⟩
          have checked := (accept_iff m source feature residual).mp
            (select_sound m source (propose source) feature residual hs).2
          rcases ih residual with ⟨decoded, bounded, fuelBound, costBound⟩
          have smaller := checked.2.2
          have residualSmaller : m.dataCost residual < m.dataCost source := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [compress, hs, restore, decoded] using checked.2.1
          · simp only [compress, hs, cost, List.map_cons, List.sum_cons]
            unfold cost at bounded
            omega
          · simp only [compress, hs, List.length_cons]
            omega
          · simp only [compress, hs, List.length_cons]
            omega

theorem compress_strict_of_nonempty (m : Model D F) (propose : D → List F)
    (fuel : Nat) (source : D)
    (nonempty : (compress m propose fuel source).1 ≠ []) :
    cost m (compress m propose fuel source).1
      (compress m propose fuel source).2 < m.dataCost source := by
  cases fuel with
  | zero => simp [compress] at nonempty
  | succ fuel =>
      cases hs : select m source (propose source) with
      | none => simp [compress, hs] at nonempty
      | some result =>
          rcases result with ⟨feature, residual⟩
          have checked := (accept_iff m source feature residual).mp
            (select_sound m source (propose source) feature residual hs).2
          have bounded := (compress_correct m propose fuel residual).2.1
          have smaller := checked.2.2
          simp only [compress, hs, cost, List.map_cons, List.sum_cons]
          unfold cost at bounded
          omega

theorem identity_not_accepted (m : Model D F) (source : D) (feature : F)
    (extracts : m.extract feature source = some source) :
    accept m source feature = none := by
  simp [accept, extracts]

/-- Binary program instance of the same executable checker. Encoding costs
here are precisely the single-step costs of the existing mathematical record;
serialization overhead for a complete chain needs its own codec. -/
def programModel
    (run : KolmogorovComplexity.BinString → KolmogorovComplexity.BinString →
      Option KolmogorovComplexity.BinString) :
    Model KolmogorovComplexity.BinString
      (KolmogorovComplexity.BinString × KolmogorovComplexity.BinString) where
  extract feature source := run feature.1 source
  expand feature residual := run feature.2 residual
  featureCost feature := feature.2.length
  dataCost source := source.length

def checkedProgramStep
    (run : KolmogorovComplexity.BinString → KolmogorovComplexity.BinString →
      Option KolmogorovComplexity.BinString)
    (source encoder decoder residual : KolmogorovComplexity.BinString)
    (accepted : accept (programModel run) source (encoder, decoder) = some residual) :
    KolmogorovComplexity.CompressionStep
      (fun program input => Part.ofOption (run program input)) source := by
  obtain ⟨extracts, reconstructs, compresses⟩ :=
    (accept_iff (programModel run) source (encoder, decoder) residual).mp accepted
  refine ⟨decoder, encoder, residual, ?_, ?_, compresses⟩
  · simpa [programModel, extracts] using extracts
  · simpa [programModel, reconstructs] using reconstructs

end Mettapedia.Algorithms.Compression.Checked
