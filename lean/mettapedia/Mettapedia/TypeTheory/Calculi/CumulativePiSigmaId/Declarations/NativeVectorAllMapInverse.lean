import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllMapComputation

/-!
# Round-trip structure of the All universe maps

The opposite map uses the other checked universe direction. The round trip is
typed at the original carrier. Its local equations prepare the object-level
inverse proof; these equations alone do not identify a neutral round trip
with its supplied evidence.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapInverse
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps
open NativeVectorAllMapComputation

def opposite : Direction → Direction
  | .forward => .backward
  | .backward => .forward

theorem source_opposite (direction : Direction) : source (opposite direction) = target direction := by
  cases direction <;> rfl

theorem target_opposite (direction : Direction) : target (opposite direction) = source direction := by
  cases direction <;> rfl

theorem opposite_twice (direction : Direction) : opposite (opposite direction) = direction := by
  cases direction <;> rfl

def mapped {n : Nat} (direction : Direction) (element predicate number vector evidence : Tower.Tm n) : Tower.Tm n :=
  .app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map
    (source direction) (target direction) element predicate number vector) evidence

def roundtrip {n : Nat} (direction : Direction) (element predicate number vector evidence : Tower.Tm n) : Tower.Tm n :=
  mapped (opposite direction) element predicate number vector (mapped direction element predicate number vector evidence)

theorem mapped_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)) :
    Typed rules context (mapped direction element predicate number vector evidence)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number vector) := by
  have applied := Derivable.appElim (map_typed_at direction elementTyped predicateTyped numberTyped vectorTyped) evidenceTyped
  simpa only [mapped, NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType, inst0_rename_wk] using applied

theorem mapped_congr (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector first second : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number))
    (same : Equal rules context first second
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)) :
    Equal rules context (mapped direction element predicate number vector first) (mapped direction element predicate number vector second)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number vector) := by
  have applied := Derivable.appCong (.refl (map_typed_at direction elementTyped predicateTyped numberTyped vectorTyped)) same
  simpa only [mapped, NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.functionType, inst0_rename_wk] using applied

theorem roundtrip_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)) :
    Typed rules context (roundtrip direction element predicate number vector evidence)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector) := by
  cases direction
  · exact mapped_typed .backward elementTyped predicateTyped numberTyped vectorTyped
      (mapped_typed .forward elementTyped predicateTyped numberTyped vectorTyped evidenceTyped)
  · exact mapped_typed .forward elementTyped predicateTyped numberTyped vectorTyped
      (mapped_typed .backward elementTyped predicateTyped numberTyped vectorTyped evidenceTyped)

theorem nil_levels_equal (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel))) :
    Equal rules context
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element))
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element))
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have linked := (nil_carriers_equal direction).substitute (nil_inputs_typed elementTyped predicateTyped)
  rw [nil_carrier_readback, nil_carrier_readback] at linked
  exact linked

theorem roundtrip_nil_equal (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (evidenceTyped : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element))) :
    Equal rules context (roundtrip direction element predicate NativeNaturalVectorFamilies.zeroTm
      (NativeNaturalVectorFamilies.vnilApp element) evidence) evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element)) := by
  have nilTyped := Derivable.appElim (primitive_typed context 5) elementTyped
  have zeroTyped := Congruence.NaturalControl.zero_typed context
  have atTarget := Derivable.conv evidenceTyped (nil_levels_equal direction elementTyped predicateTyped) (.sort _)
  cases direction
  · exact .trans (mapped_congr .backward elementTyped predicateTyped zeroTyped nilTyped
      (nil_application_equal_at .forward elementTyped predicateTyped evidenceTyped))
      (nil_application_equal_at .backward elementTyped predicateTyped atTarget)
  · exact .trans (mapped_congr .forward elementTyped predicateTyped zeroTyped nilTyped
      (nil_application_equal_at .backward elementTyped predicateTyped evidenceTyped))
      (nil_application_equal_at .forward elementTyped predicateTyped atTarget)

def consResult {n : Nat} (direction : Direction)
    (element predicate number _head tail evidence : Tower.Tm n) : Tower.Tm n :=
  .pair (.fst evidence) (mapped direction element predicate number tail (.snd evidence))

theorem cons_pair_formed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (consPair (target direction) element predicate number head tail)
      (sortTm (.max NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel)) := by
  have firstTyped : Typed rules context (.app predicate head)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
    .sub (.appElim predicateTyped headTyped)
      (.subUniv (by intro valuation; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
  exact .sigmaForm firstTyped (.sort _)
    (target_all_formed direction elementTyped predicateTyped numberTyped tailTyped).weaken (.sort _) (.sorts _ _)

theorem cons_head_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Typed rules context (.fst evidence) (.app predicate head) :=
  .fstElim (.conv evidenceTyped
    (cons_source_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _))

theorem cons_tail_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Typed rules context (.snd evidence)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail) := by
  have pairTyped := Derivable.conv evidenceTyped
    (cons_source_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _)
  have secondTyped := Derivable.sndElim pairTyped
  simpa only [consPair, inst0_rename_wk] using secondTyped

theorem cons_mapped_tail_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Typed rules context (mapped direction element predicate number tail (.snd evidence))
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number tail) :=
  mapped_typed direction elementTyped predicateTyped numberTyped tailTyped
    (cons_tail_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped)

theorem cons_result_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Typed rules context (consResult direction element predicate number head tail evidence)
      (consCarrier (target direction) element predicate number head tail) := by
  have newTail := cons_mapped_tail_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have tailAt : Typed rules context (mapped direction element predicate number tail (.snd evidence))
      (inst0 (.fst evidence) (rename wk
        (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number tail))) := by
    rw [inst0_rename_wk]
    exact newTail
  have pairTyped := Derivable.pairIntro
    (cons_pair_formed direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _)
    (cons_head_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped) tailAt
  exact .conv pairTyped
    (.symm (cons_target_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped)) (.sort _)

theorem cons_result_fst_equal (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Equal rules context (.fst (consResult direction element predicate number head tail evidence)) (.fst evidence) (.app predicate head) := by
  have tailAt : Typed rules context (mapped direction element predicate number tail (.snd evidence))
      (inst0 (.fst evidence) (rename wk
        (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number tail))) := by
    rw [inst0_rename_wk]
    exact cons_mapped_tail_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  exact .betaFst (cons_pair_formed direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _)
    (cons_head_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped) tailAt

theorem cons_result_snd_equal (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Equal rules context (.snd (consResult direction element predicate number head tail evidence))
      (mapped direction element predicate number tail (.snd evidence))
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number tail) := by
  have tailAt : Typed rules context (mapped direction element predicate number tail (.snd evidence))
      (inst0 (.fst evidence) (rename wk
        (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number tail))) := by
    rw [inst0_rename_wk]
    exact cons_mapped_tail_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have beta := Derivable.betaSnd (cons_pair_formed direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _)
    (cons_head_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped) tailAt
  simpa only [consResult, inst0_rename_wk] using beta

theorem opposite_mapped_congr (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector first second : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number))
    (same : Equal rules context first second
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (target direction) element predicate number vector)) :
    Equal rules context (mapped (opposite direction) element predicate number vector first)
      (mapped (opposite direction) element predicate number vector second)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector) := by
  cases direction
  · exact mapped_congr .backward elementTyped predicateTyped numberTyped vectorTyped same
  · exact mapped_congr .forward elementTyped predicateTyped numberTyped vectorTyped same

theorem opposite_cons_equal (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (target direction) element predicate number head tail)) :
    Equal rules context (mapped (opposite direction) element predicate (NativeNaturalVectorFamilies.succApp number)
      (NativeNaturalVectorFamilies.vconsApp element number head tail) evidence)
      (consResult (opposite direction) element predicate number head tail evidence)
      (consCarrier (source direction) element predicate number head tail) := by
  cases direction
  · exact cons_application_equal_at .backward elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  · exact cons_application_equal_at .forward elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped

theorem source_cons_pair_formed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (consPair (source direction) element predicate number head tail)
      (sortTm (.max NativeVectorAll.Universes.CumulativeElimination.upperLevel NativeVectorAll.Universes.CumulativeElimination.upperLevel)) := by
  simpa only [target_opposite] using
    cons_pair_formed (opposite direction) elementTyped predicateTyped numberTyped headTyped tailTyped

theorem roundtrip_cons_equal (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number head tail evidence : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (headTyped : Typed rules context head element)
    (tailTyped : Typed rules context tail (NativeNaturalVectorFamilies.vecApp element number))
    (evidenceTyped : Typed rules context evidence (consCarrier (source direction) element predicate number head tail)) :
    Equal rules context (roundtrip direction element predicate (NativeNaturalVectorFamilies.succApp number)
      (NativeNaturalVectorFamilies.vconsApp element number head tail) evidence)
      (.pair (.fst evidence) (roundtrip direction element predicate number tail (.snd evidence)))
      (consCarrier (source direction) element predicate number head tail) := by
  have nextTyped := Derivable.appElim (primitive_typed context 2) numberTyped
  have constructorTyped := cons_constructor_typed elementTyped predicateTyped numberTyped headTyped tailTyped
  have firstCons : Equal rules context
      (mapped direction element predicate (NativeNaturalVectorFamilies.succApp number)
        (NativeNaturalVectorFamilies.vconsApp element number head tail) evidence)
      (consResult direction element predicate number head tail evidence)
      (consCarrier (target direction) element predicate number head tail) :=
    cons_application_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have carried := opposite_mapped_congr direction elementTyped predicateTyped nextTyped constructorTyped firstCons
  have secondCons := opposite_cons_equal direction elementTyped predicateTyped numberTyped headTyped tailTyped
    (cons_result_typed direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped)
  have firstProjection := cons_result_fst_equal direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped
  have secondProjection := opposite_mapped_congr direction elementTyped predicateTyped numberTyped tailTyped
    (cons_result_snd_equal direction elementTyped predicateTyped numberTyped headTyped tailTyped evidenceTyped)
  have fiber : Equal rules context
      (mapped (opposite direction) element predicate number tail
        (.snd (consResult direction element predicate number head tail evidence)))
      (roundtrip direction element predicate number tail (.snd evidence))
      (inst0 (.fst (consResult direction element predicate number head tail evidence))
        (rename wk (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number tail))) := by
    rw [inst0_rename_wk]
    exact secondProjection
  have pairEquality := Derivable.pairCong
    (source_cons_pair_formed direction elementTyped predicateTyped numberTyped headTyped tailTyped) (.sort _)
    firstProjection fiber
  have atCarrier := Derivable.convEq pairEquality
    (.symm (cons_source_equal_at direction elementTyped predicateTyped numberTyped headTyped tailTyped)) (.sort _)
  exact .trans carried (.trans secondCons atCarrier)

#print axioms roundtrip_typed
#print axioms roundtrip_nil_equal
#print axioms cons_result_typed
#print axioms cons_result_snd_equal
#print axioms roundtrip_cons_equal

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllMapInverse
