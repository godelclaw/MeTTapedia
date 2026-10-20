import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Eliminators
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PackageSum

/-!
# The declared natural fragment in the existing domain interpretation

The original natural type, constructors and dependent recursor use the
existing nontrivial numeral ideals and type-projected constants. Lookup
stages avoid a recursive definition of the reading. The other declarations
remain opaque in this natural-fragment interpretation; their computation
is not validated here. Semantic root validity is distinct from logical-relation
adequacy, annotated former facts, normalization and implementation refinement.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.Annotated.NaturalDomain

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated TypedEquality.Impredicative.Domain
open Ideal

def names : NumNames Tower.Head where
  univ := RussellTarski.substLevelsHead levels (.sort motiveLevel)
  num := natName
  zero := zeroName
  suc := succName

def baseReading : Reading Tower.Head where
  head := (headReading ComputationProfiles.naturalOnly).read
  const name := if name = natName then natI else Ideal.bot

def constructorReading : Reading Tower.Head where
  head := baseReading.head
  const name := if name = zeroName then zeroConst baseReading names
    else if name = succName then sucConst baseReading names else baseReading.const name

def reading : Reading Tower.Head where
  head := constructorReading.head
  const name := if name = natEliminateName then nrConst constructorReading names
    else constructorReading.const name

theorem reading_nat : reading.const natName = natI := rfl

theorem reading_zero : reading.const zeroName = zeroI :=
  zeroConst_eq (Rd := baseReading) (N := names) rfl

theorem reading_successor : reading.const succName = sucConst reading names := rfl

theorem reading_recursor : reading.const natEliminateName = nrConst reading names := rfl

theorem nat_declared (enabled : ComputationProfiles.Selection) :
    (church enabled).constantType natName = some (.head (.sort Tower.zero)) := by
  rw [constantType_eq enabled]
  decide +kernel

theorem zero_declared (enabled : ComputationProfiles.Selection) :
    (church enabled).constantType zeroName = some (.const natName) := by
  rw [constantType_eq enabled]
  decide +kernel

theorem successor_declared (enabled : ComputationProfiles.Selection) :
    (church enabled).constantType succName = some (sucTypeC names) := by
  rw [constantType_eq enabled]
  decide +kernel

theorem recursor_declared (enabled : ComputationProfiles.Selection) :
    (church enabled).constantType natEliminateName = some (nrTypeC names) := by
  rw [constantType_eq enabled]
  decide +kernel

/-- Every original declaration has a value in its declared type in this
reading. Only the four natural declarations have a non-bottom interpretation. -/
theorem constants_valid (enabled : ComputationProfiles.Selection)
    {name : DeclName} {type : CTm Tower.Head 0}
    (known : (church enabled).constantType name = some type)
    (_generated : TypeGenerated (cinterp reading type Env.nil)) :
    projT (cinterp reading type Env.nil) (reading.const name) = reading.const name := by
  by_cases isNat : name = natName
  · subst name
    have same : type = .head (.sort Tower.zero) :=
      Option.some.inj (known.symm.trans (nat_declared enabled))
    subst type
    rw [reading_nat]
    exact projT_univ_eq_self_iff.2 typeGenerated_natI
  by_cases isZero : name = zeroName
  · subst name
    have same : type = .const natName :=
      Option.some.inj (known.symm.trans (zero_declared enabled))
    subst type
    rw [reading_zero]
    exact projT_natI_zeroI
  by_cases isSuccessor : name = succName
  · subst name
    have same : type = sucTypeC names :=
      Option.some.inj (known.symm.trans (successor_declared enabled))
    subst type
    rw [reading_successor, sucConst]
    exact projT_projT _ _
  by_cases isRecursor : name = natEliminateName
  · subst name
    have same : type = nrTypeC names :=
      Option.some.inj (known.symm.trans (recursor_declared enabled))
    subst type
    rw [reading_recursor, nrConst]
    exact projT_projT _ _
  have bottom : reading.const name = Ideal.bot := by
    simp only [reading, constructorReading, baseReading, if_neg isRecursor,
      if_neg isZero, if_neg isSuccessor, if_neg isNat]
  rw [bottom]
  exact Ideal.le_antisymm (projT_le _ _) (Ideal.bot_le _)

/-- Actual declaration lookup turns the syntactic argument-spine facts into
the existing dependent semantic telescope facts. -/
theorem recursor_spine (enabled : ComputationProfiles.Selection) {n : Nat} {ρ : Env n}
    {arguments : List (CTm Tower.Head n)} {type : Ideal}
    (facts : Annotated.SpineFacts reading (church enabled)
      (CTm.appSpine (.const natEliminateName) arguments) type ρ) :
    Ideal.SpineFacts (nrTypeI reading names) (arguments.map (cinterp reading · ρ)) type :=
  (Annotated.SpineFacts.constSpine (recursor_declared enabled) facts).1

theorem zero_valid (enabled : ComputationProfiles.Selection) {n : Nat} {ρ : Env n}
    {motive zeroCase successorCase : CTm Tower.Head n} {type : Ideal}
    (facts : Annotated.SpineFacts reading (church enabled)
      (CTm.appSpine (.const natEliminateName) [motive, zeroCase, successorCase, .const zeroName]) type ρ)
    (right : projT type (cinterp reading zeroCase ρ) = cinterp reading zeroCase ρ) :
    cinterp reading
      (CTm.appSpine (.const natEliminateName) [motive, zeroCase, successorCase, .const zeroName]) ρ =
      cinterp reading zeroCase ρ := by
  have spine := recursor_spine enabled facts
  simp only [List.map_cons, List.map_nil, cinterp, reading_zero] at spine
  have equation := nrConst_iotaZero spine right
  simpa only [cinterp_appSpine, cinterp, reading_recursor, reading_zero,
    List.map_cons, List.map_nil] using equation

theorem successor_valid (enabled : ComputationProfiles.Selection) {n : Nat} {ρ : Env n}
    {motive zeroCase successorCase number : CTm Tower.Head n} {type : Ideal}
    (facts : Annotated.SpineFacts reading (church enabled)
      (CTm.appSpine (.const natEliminateName)
        [motive, zeroCase, successorCase, .app (.const succName) number]) type ρ)
    (right : projT type (cinterp reading
        (.app (.app successorCase number)
          (CTm.appSpine (.const natEliminateName) [motive, zeroCase, successorCase, number])) ρ) =
      cinterp reading
        (.app (.app successorCase number)
          (CTm.appSpine (.const natEliminateName) [motive, zeroCase, successorCase, number])) ρ) :
    cinterp reading
      (CTm.appSpine (.const natEliminateName)
        [motive, zeroCase, successorCase, .app (.const succName) number]) ρ =
      cinterp reading
        (.app (.app successorCase number)
          (CTm.appSpine (.const natEliminateName) [motive, zeroCase, successorCase, number])) ρ := by
  have spine := recursor_spine enabled facts
  simp only [List.map_cons, List.map_nil, cinterp, reading_successor] at spine
  have target := right
  simp only [cinterp_appSpine, cinterp, reading_recursor, List.map_cons, List.map_nil] at target
  have equation := nrConst_iotaSucc (Rd := reading) (N := names) reading_nat spine target
  simpa only [cinterp_appSpine, cinterp, reading_recursor, reading_successor,
    List.map_cons, List.map_nil] using equation

/-- The actual selected table has precisely the two natural computation
rows. Their arguments retain their annotations and semantic typing premises. -/
theorem roots_valid {n : Nat} {left right : CTm Tower.Head n} {type : Ideal} {ρ : Env n}
    (root : (church ComputationProfiles.naturalOnly).computation.step left right)
    (_generated : TypeGenerated type)
    (_leftTyped : projT type (cinterp reading left ρ) = cinterp reading left ρ)
    (facts : Annotated.SpineFacts reading (church ComputationProfiles.naturalOnly) left type ρ)
    (rightTyped : projT type (cinterp reading right ρ) = cinterp reading right ρ)
    (_rightFacts : Annotated.SpineFacts reading (church ComputationProfiles.naturalOnly) right type ρ) :
    cinterp reading left ρ = cinterp reading right ρ := by
  cases root with
  | instantiate elaborated assignment =>
      obtain ⟨L, R, selected, rfl, rfl⟩ := elaborated
      obtain ⟨index, permitted, row⟩ := selected
      rw [table_row index] at row
      cases row
      have leftEq := elaborated_left ComputationProfiles.naturalOnly index
      have rightEq := elaborated_right ComputationProfiles.naturalOnly index
      change elabLeft (elabDeclarations (ComputationProfiles.rules
        ComputationProfiles.naturalOnly).constantType) (Programs.Annotated.left index) = _ at leftEq
      change elabRight (elabDeclarations (ComputationProfiles.rules
        ComputationProfiles.naturalOnly).constantType) (Programs.Annotated.left index)
        (Programs.Annotated.right index) = _ at rightEq
      rw [leftEq, rightEq] at *
      clear _generated _leftTyped _rightFacts leftEq rightEq
      fin_cases index
      · change CSub Tower.Head 3 n at assignment
        exact zero_valid _ (motive := assignment 2) (zeroCase := assignment 1)
          (successorCase := assignment 0) facts rightTyped
      · change CSub Tower.Head 4 n at assignment
        exact successor_valid _ (motive := assignment 3) (zeroCase := assignment 2)
          (successorCase := assignment 1) (number := assignment 0) facts rightTyped
      · contradiction
      · contradiction

/-- A nontrivial reading of the original declaration package with natural
computation enabled. This is semantic validity, not logical-relation adequacy. -/
theorem valid : ReadingValid reading (church ComputationProfiles.naturalOnly) :=
  ReadingValid.ofLevels (levelModel ComputationProfiles.naturalOnly)
    (headReading ComputationProfiles.naturalOnly).universes
    (headReading ComputationProfiles.naturalOnly).types
    (headReading ComputationProfiles.naturalOnly).headEq (constants_valid _) roots_valid

theorem one_plus_zero :
    cinterp reading (Functions.add (Functions.successor Functions.zero) Functions.zero) Env.nil =
      cinterp reading (Functions.successor Functions.zero) Env.nil :=
  Functions.one_plus_zero.sound valid trivial

/-- The successor has its original numeral interpretation, rather than
collapsing every closed value to the least ideal. -/
theorem successor_zero :
    cinterp reading (Functions.successor (Functions.zero : CTm Tower.Head 0)) Env.nil =
      succI zeroI := by
  change Ideal.app (reading.const succName) (reading.const zeroName) = _
  rw [reading_successor, reading_zero, app_sucConst reading names reading_nat, projT_natI_zeroI]

theorem one_plus_zero_value :
    cinterp reading (Functions.add (Functions.successor Functions.zero) Functions.zero) Env.nil =
      succI zeroI := one_plus_zero.trans successor_zero

theorem zero_ne_successor_zero :
    cinterp reading (Functions.zero : CTm Tower.Head 0) Env.nil ≠
      cinterp reading (Functions.successor (Functions.zero : CTm Tower.Head 0)) Env.nil := by
  change reading.const zeroName ≠ _
  rw [reading_zero, successor_zero]
  intro equal
  exact zeroI_not_mem_succ (equal.symm ▸ succI_mem_succ zeroI)

/-- The selected annotated judgment cannot certify this false constructor
equation. This uses the actual rule table and the nontrivial interpretation. -/
theorem zero_equal_successor_refused :
    ¬ CEqual (church ComputationProfiles.naturalOnly) .nil
      Functions.zero (Functions.successor Functions.zero) Functions.natural := by
  intro equal
  exact zero_ne_successor_zero (equal.sound valid trivial)

namespace Decoder

def smallUniverse : Tower.Head := .sort Tower.zero
def successorUniverse : Tower.Head := .sort (.succ Tower.zero)

/-- The existing two opaque decoder declarations, at names fresh for the
original natural/vector signature. They add no computation or identity rule. -/
def rules : Rules Tower.Head :=
  { Tower.rules with constantType := fun name =>
      (RigidExtension.decls smallUniverse successorUniverse name).map CTm.erase }

def declarations : ChurchRules rules where
  constantType := RigidExtension.decls smallUniverse successorUniverse
  computation := .empty
  erase_constantType := fun _ => rfl
  erase_step := fun impossible => impossible.elim

def package := (church ComputationProfiles.naturalOnly).sum declarations

theorem fresh_prop :
    (church ComputationProfiles.naturalOnly).constantType RigidExtension.prop = none := by
  decide +kernel

theorem fresh_holds :
    (church ComputationProfiles.naturalOnly).constantType RigidExtension.holds = none := by
  decide +kernel

theorem prop_declared : package.constantType RigidExtension.prop = some (.head successorUniverse) :=
  (sumDecls_right fresh_prop).trans (RigidExtension.decls_prop smallUniverse successorUniverse)

theorem holds_declared : package.constantType RigidExtension.holds =
    some (.pi (.const RigidExtension.prop) (.head smallUniverse)) :=
  (sumDecls_right fresh_holds).trans (RigidExtension.decls_holds smallUniverse successorUniverse)

/-- The new opaque names have no observations in this reading. The original
natural constructors and recursor keep their nontrivial interpretation. -/
theorem declarations_valid : ReadingValid reading declarations := by
  apply ReadingValid.ofLevels (Rd := reading) (P := declarations)
    ({ Normalization.TowerModel.levels (fun _ => 0) with } : Normalization.LevelModel rules Nat)
    (headReading ComputationProfiles.naturalOnly).universes
    (headReading ComputationProfiles.naturalOnly).types
    (headReading ComputationProfiles.naturalOnly).headEq
  · intro name type known _generated
    have bottom : reading.const name = Ideal.bot := by
      change RigidExtension.decls smallUniverse successorUniverse name = some type at known
      unfold RigidExtension.decls at known
      split at known
      · rename_i same
        subst name
        rfl
      · split at known
        · rename_i _ same
          subst name
          rfl
        · cases known
    rw [bottom]
    exact Ideal.le_antisymm (projT_le _ _) (Ideal.bot_le _)
  · intro n left right type ρ impossible
    exact impossible.elim

theorem valid : ReadingValid reading package :=
  NaturalDomain.valid.sum_opaque declarations_valid (fun impossible => impossible.elim)

/-- Both original root cases remain, with no additional case. This does not
replace the selected table by the no-root extension used for opaque packages. -/
theorem roots_iff {n : Nat} {left right : CTm Tower.Head n} :
    package.computation.step left right ↔
      (church ComputationProfiles.naturalOnly).computation.step left right :=
  ⟨fun step => step.elim id False.elim, Or.inl⟩

/-- Required evidence is unchanged for every actual original root. -/
theorem premises_iff {n : Nat} {left right : CTm Tower.Head n}
    {premises : List (CPremise Tower.Head n)}
    (root : (church ComputationProfiles.naturalOnly).computation.step left right) :
    package.computation.requires left right premises ↔
      (church ComputationProfiles.naturalOnly).computation.requires left right premises := by
  constructor
  · exact fun required => required.elim And.right (fun impossible => impossible.1.elim)
  · exact fun required => .inl ⟨root, required⟩

theorem one_plus_zero : CEqual package .nil
    (Functions.add (Functions.successor Functions.zero) Functions.zero)
    (Functions.successor Functions.zero) Functions.natural :=
  Functions.one_plus_zero.sum_left declarations

theorem zero_root : package.computation.step
    (Functions.add Functions.zero Functions.zero : CTm Tower.Head 0) Functions.zero := by
  let assignment : CSub Tower.Head 3 0 := fun index =>
    Functions.arguments Functions.motive Functions.zero Functions.step Functions.zero index.succ
  exact roots_iff.mpr (instantiated_step ComputationProfiles.naturalOnly
    Functions.zeroRow rfl assignment)

theorem zero_equal_successor_refused :
    ¬ CEqual package .nil Functions.zero
      (Functions.successor Functions.zero) Functions.natural := by
  intro equal
  exact NaturalDomain.zero_ne_successor_zero (equal.sound valid trivial)

end Decoder

end Programs.Annotated.NaturalDomain
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
