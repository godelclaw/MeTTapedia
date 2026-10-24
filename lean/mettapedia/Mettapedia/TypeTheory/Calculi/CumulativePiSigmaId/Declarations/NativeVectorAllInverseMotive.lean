import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllMapInverse

/-!
# Formation of the value-level All inverse motive

The motive asks for identity of each supplied evidence value with its round
trip, over an unknown length and vector. Its carrier is the original All
type, rather than the universe containing that type. Formation does not
construct the identity proof or its induction methods.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverseMotive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps
open NativeVectorAllMapComputation
open NativeVectorAllMapInverse

theorem rename_all {n m : Nat} (rho : Ren n m) (level : LevelExpr Nat)
    (element predicate number vector : Tower.Tm n) :
    rename rho (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate number vector) =
      NativeVectorAll.Universes.Canonical.allTypeAtUniverse level
        (rename rho element) (rename rho predicate) (rename rho number) (rename rho vector) := by
  simpa only [subst_renSub] using
    NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse (renSub rho) level element predicate number vector

theorem substitute_mapped {n m : Nat} (sigma : Sub Tower.Head n m) (direction : Direction)
    (element predicate number vector evidence : Tower.Tm n) :
    subst sigma (mapped direction element predicate number vector evidence) =
      mapped direction (subst sigma element) (subst sigma predicate) (subst sigma number)
        (subst sigma vector) (subst sigma evidence) := by
  simp only [mapped, subst, NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_map]

theorem substitute_roundtrip {n m : Nat} (sigma : Sub Tower.Head n m) (direction : Direction)
    (element predicate number vector evidence : Tower.Tm n) :
    subst sigma (roundtrip direction element predicate number vector evidence) =
      roundtrip direction (subst sigma element) (subst sigma predicate) (subst sigma number)
        (subst sigma vector) (subst sigma evidence) := by
  simp only [roundtrip, substitute_mapped]

def goalType {n : Nat} (direction : Direction) (element predicate number vector : Tower.Tm n) : Tower.Tm n :=
  .pi (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)
    (.id (rename wk (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector))
      (roundtrip direction (rename wk element) (rename wk predicate) (rename wk number) (rename wk vector) (.var 0)) (.var 0))

theorem substitute_goalType {n m : Nat} (sigma : Sub Tower.Head n m) (direction : Direction)
    (element predicate number vector : Tower.Tm n) :
    subst sigma (goalType direction element predicate number vector) =
      goalType direction (subst sigma element) (subst sigma predicate) (subst sigma number) (subst sigma vector) := by
  simp only [goalType, subst, NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse,
    subst_liftSub_wk, substitute_roundtrip, liftSub_zero]

theorem rename_goalType {n m : Nat} (rho : Ren n m) (direction : Direction)
    (element predicate number vector : Tower.Tm n) :
    rename rho (goalType direction element predicate number vector) =
      goalType direction (rename rho element) (rename rho predicate) (rename rho number) (rename rho vector) := by
  simpa only [subst_renSub] using substitute_goalType (renSub rho) direction element predicate number vector

theorem goal_type_formed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Typed rules context (goalType direction element predicate number vector)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have carrierTyped := source_all_formed direction elementTyped predicateTyped numberTyped vectorTyped
  let carrier := NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector
  have evidenceTyped : Typed rules (.snoc context carrier) (.var 0)
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction)
        (rename wk element) (rename wk predicate) (rename wk number) (rename wk vector)) := by
    have checked := Derivable.var (R := rules) (Γ := .snoc context carrier) 0
    change Typed rules (.snoc context carrier) (.var 0) (rename wk carrier) at checked
    dsimp only [carrier] at checked
    rw [rename_all] at checked
    exact checked
  have vectorWeak : Typed rules (.snoc context carrier) (rename wk vector)
      (NativeNaturalVectorFamilies.vecApp (rename wk element) (rename wk number)) := by
    simpa only [NativeNaturalVectorFamilies.rename_vecApp] using vectorTyped.weaken
  have roundtripTyped := roundtrip_typed direction elementTyped.weaken predicateTyped.weaken numberTyped.weaken vectorWeak evidenceTyped
  have carrierReadback := rename_all wk (source direction) element predicate number vector
  rw [← carrierReadback] at roundtripTyped evidenceTyped
  exact NativeVectorAllMapMethods.pi_upper carrierTyped
    (.idForm carrierTyped.weaken (.sort _) roundtripTyped evidenceTyped)

theorem goal_apply_typed (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector proof evidence : Tower.Tm n}
    (proofTyped : Typed rules context proof (goalType direction element predicate number vector))
    (evidenceTyped : Typed rules context evidence
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)) :
    Typed rules context (.app proof evidence)
      (.id (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) element predicate number vector)
        (roundtrip direction element predicate number vector evidence) evidence) := by
  have applied := Derivable.appElim proofTyped evidenceTyped
  have openingWeakening {k : Nat} (value body : Tower.Tm k) :
      subst (subst0 value) (rename wk body) = body := inst0_rename_wk value body
  simpa only [goalType, inst0, subst, openingWeakening, substitute_roundtrip, subst0_zero] using applied

def motive {n : Nat} (direction : Direction) (element predicate : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (goalType direction (rename wk (rename wk element)) (rename wk (rename wk predicate))
    (.var (Fin.succ 0)) (.var 0)))

theorem substitute_motive {n m : Nat} (sigma : Sub Tower.Head n m) (direction : Direction)
    (element predicate : Tower.Tm n) :
    subst sigma (motive direction element predicate) = motive direction (subst sigma element) (subst sigma predicate) := by
  simp only [motive, subst, substitute_goalType, subst_liftSub_wk, liftSub_zero, liftSub_succ]
  rfl

theorem rename_motive {n m : Nat} (rho : Ren n m) (direction : Direction)
    (element predicate : Tower.Tm n) :
    rename rho (motive direction element predicate) = motive direction (rename rho element) (rename rho predicate) := by
  simpa only [subst_renSub] using substitute_motive (renSub rho) direction element predicate

theorem motive_body_formed (direction : Direction) : Typed rules NativeVectorAllMapMethods.Motive.context
    (goalType direction (.var 5) (.var 4) (.var 1) (.var 0))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) :=
  goal_type_formed direction (context := NativeVectorAllMapMethods.Motive.context)
    (element := .var 5) (predicate := .var 4) (number := .var 1) (vector := .var 0)
    (.var 5) (.var 4) (.var 1) (.var 0)

theorem motive_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (motive direction (.var 3) (.var 2)) NativeVectorAllMapMethods.Motive.type :=
  .lamIntro NativeVectorAllMapMethods.Motive.type_formed (.sort _)
    (.lamIntro NativeVectorAllMapMethods.Motive.inner_formed (.sort _) (motive_body_formed direction))

theorem motive_beta (direction : Direction) : Equal rules NativeVectorAll.Universes.context
    (.app (.app (motive direction (.var 3) (.var 2)) (.var 1)) (.var 0))
    (goalType direction (.var 3) (.var 2) (.var 1) (.var 0))
    (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  have equation := betaPi_two NativeVectorAllMapMethods.Motive.type_formed (.sort _)
    NativeVectorAllMapMethods.Motive.inner_formed (.sort _) (motive_body_formed direction)
    (first := .var 1) (second := .var 0) (.var 1) (.var 0)
  rw [substitute_goalType] at equation
  exact equation

theorem motive_beta_at (direction : Direction) {n : Nat} {context : Tower.Ctx n}
    {element predicate number vector : Tower.Tm n}
    (elementTyped : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (numberTyped : Typed rules context number NativeNaturalVectorFamilies.natTm)
    (vectorTyped : Typed rules context vector (NativeNaturalVectorFamilies.vecApp element number)) :
    Equal rules context (.app (.app (motive direction element predicate) number) vector)
      (goalType direction element predicate number vector)
      (sortTm NativeVectorAll.Universes.CumulativeElimination.upperLevel) := by
  let sigma := NativeVectorAll.Universes.arguments element predicate number vector
  have linked := (motive_beta direction).substitute
    (all_inputs_typed elementTyped predicateTyped numberTyped vectorTyped)
  have leftReadback : subst sigma (.app (.app (motive direction (.var 3) (.var 2)) (.var 1)) (.var 0)) =
      .app (.app (motive direction element predicate) number) vector := by
    simp only [subst, substitute_motive]
    rfl
  have rightReadback : subst sigma (goalType direction (.var 3) (.var 2) (.var 1) (.var 0)) =
      goalType direction element predicate number vector := by
    rw [substitute_goalType]
    rfl
  rw [leftReadback, rightReadback] at linked
  exact linked

theorem native_motive_typed (direction : Direction) : Typed rules NativeVectorAll.Universes.context
    (motive direction (.var 3) (.var 2)) (motiveTypeAt (.var 3)) := by
  have innerForm : Typed rules NativeVectorAllMapMethods.lengthContext
      (.pi (NativeNaturalVectorFamilies.vecApp (.var 4) (.var 0))
        (sortTm (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)))
      (sortTm (.max NativeVectorAll.Universes.dataLevel
        (.succ (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)))) :=
    .piForm NativeVectorAllMapMethods.Motive.vector_typed (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)
  have body : Typed rules NativeVectorAllMapMethods.Motive.context
      (goalType direction (.var 5) (.var 4) (.var 1) (.var 0))
      (sortTm (.succ NativeVectorAll.Universes.CumulativeElimination.upperLevel)) :=
    Derivable.sub (motive_body_formed direction)
    (.subUniv (by intro valuation; exact Nat.le_succ _))
  exact .lamIntro (motive_type_formed (element := .var 3) (.var 3)) (.sort _)
    (.lamIntro innerForm (.sort _) body)

#print axioms goal_type_formed
#print axioms motive_typed
#print axioms native_motive_typed
#print axioms motive_beta_at

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverseMotive
