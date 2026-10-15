import Mettapedia.GSLT.Causality.DoCalculus.BackDoorCheck
import Mettapedia.GSLT.Causality.DoCalculus.Identification
import Mettapedia.GSLT.Causality.DoCalculus.QueryCounts

/-!
# Interventional counts read off the adjustment formula

The smoking table and the door table are integer joints. `frontDoorCounts`
is the canonical `(n⁺, n⁻)` state of the front-door ratio on that smoking
table. `backDoorCounts` is the canonical state of the back-door ratio on the
door table. Neither ratio is the observational conditional. Pooling an
experimental observation revises only the interventional state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.Logic.EvidenceStateInsufficiency

/-! ## Smoking front door, cells `(s, t, c)` -/

def smokeCell : Bool → Bool → Bool → Nat
  | false, false, false => 8
  | false, false, true => 2
  | false, true, false => 1
  | false, true, true => 1
  | true, false, false => 1
  | true, false, true => 1
  | true, true, false => 2
  | true, true, true => 8

def smokeN (s : Bool) : Nat :=
  smokeCell s false false + smokeCell s false true +
    smokeCell s true false + smokeCell s true true

def smokeNT (s t : Bool) : Nat :=
  smokeCell s t false + smokeCell s t true

def smokeNC (s t : Bool) : Nat :=
  smokeCell s t true

def smokeTotal : Nat :=
  smokeN false + smokeN true

def smokeProdT : Nat :=
  smokeNT false false * smokeNT false true * smokeNT true false * smokeNT true true

def smokeExcept (s t : Bool) : Nat :=
  smokeProdT / smokeNT s t

def smokeContrib (t s' : Bool) : Nat :=
  smokeNT true t * smokeNC s' t * smokeN s' * smokeExcept s' t

/-- Cleared numerator of `Σ_t P(t | s = true) Σ_s' P(c = true | t, s') P(s')`. -/
def frontDoorNum : Nat :=
  smokeContrib false false + smokeContrib false true +
    smokeContrib true false + smokeContrib true true

/-- Cleared denominator of that front-door ratio. -/
def frontDoorDen : Nat :=
  smokeN true * smokeTotal * smokeProdT

def frontDoorCounts : Counts :=
  countsOfRatio frontDoorNum frontDoorDen

def smokeObsCounts : Counts :=
  ⟨smokeCell true false true + smokeCell true true true,
    smokeCell true false false + smokeCell true true false⟩

def frontDoorState : QueryState where
  observational := smokeObsCounts
  interventional := frontDoorCounts

theorem frontDoorCounts_canonical : frontDoorCounts = ⟨3, 2⟩ := by
  decide

theorem smokeObsCounts_canonical : smokeObsCounts = ⟨9, 3⟩ := by
  decide

theorem front_door_count_strength : frontDoorCounts.strength = 3 / 5 := by
  rw [frontDoorCounts_canonical]
  norm_num [Counts.strength, Counts.total]

theorem smoke_obs_count_strength : smokeObsCounts.strength = 3 / 4 := by
  rw [smokeObsCounts_canonical]
  norm_num [Counts.strength, Counts.total]

theorem front_door_count_differs_from_observation :
    frontDoorCounts.strength ≠ smokeObsCounts.strength := by
  rw [front_door_count_strength, smoke_obs_count_strength]
  norm_num

theorem front_door_pool_is_one_revision (experiment : Bool) :
    (poolInterventional frontDoorState experiment).interventional =
        frontDoorCounts.revise experiment ∧
      (poolInterventional frontDoorState experiment).observational =
        smokeObsCounts := by
  have hpool := pool_interventional_keeps_observational frontDoorState experiment
  refine ⟨?_, ?_⟩
  · simpa [frontDoorState] using hpool.2
  · simpa [frontDoorState] using hpool.1

/-! ## Door back door, cells `(z, x, y)` -/

def doorCell : Bool → Bool → Bool → Nat
  | false, false, false => 8
  | false, true, false => 1
  | true, false, true => 1
  | true, true, true => 8
  | _, _, _ => 0

def doorNZ (z : Bool) : Nat :=
  doorCell z false false + doorCell z false true +
    doorCell z true false + doorCell z true true

def doorNX (z : Bool) : Nat :=
  doorCell z true false + doorCell z true true

def doorNY (z : Bool) : Nat :=
  doorCell z true true

def doorTotal : Nat :=
  doorNZ false + doorNZ true

/-- Cleared numerator of `Σ_z P(y = true | x = true, z) P(z)`. -/
def backDoorNum : Nat :=
  doorNY false * doorNZ false * doorNX true +
    doorNY true * doorNZ true * doorNX false

def backDoorDen : Nat :=
  doorTotal * doorNX false * doorNX true

def backDoorCounts : Counts :=
  countsOfRatio backDoorNum backDoorDen

def doorObsCounts : Counts :=
  ⟨doorCell false true true + doorCell true true true,
    doorCell false true false + doorCell true true false⟩

def backDoorState : QueryState where
  observational := doorObsCounts
  interventional := backDoorCounts

theorem backDoorCounts_canonical : backDoorCounts = ⟨1, 1⟩ := by
  decide

theorem doorObsCounts_canonical : doorObsCounts = ⟨8, 1⟩ := by
  decide

theorem back_door_count_strength : backDoorCounts.strength = 1 / 2 := by
  rw [backDoorCounts_canonical]
  norm_num [Counts.strength, Counts.total]

theorem door_obs_count_strength : doorObsCounts.strength = 8 / 9 := by
  rw [doorObsCounts_canonical]
  norm_num [Counts.strength, Counts.total]

theorem back_door_count_differs_from_observation :
    backDoorCounts.strength ≠ doorObsCounts.strength := by
  rw [back_door_count_strength, door_obs_count_strength]
  norm_num

theorem back_door_pool_is_one_revision (experiment : Bool) :
    (poolInterventional backDoorState experiment).interventional =
        backDoorCounts.revise experiment ∧
      (poolInterventional backDoorState experiment).observational =
        doorObsCounts := by
  have hpool := pool_interventional_keeps_observational backDoorState experiment
  refine ⟨?_, ?_⟩
  · simpa [backDoorState] using hpool.2
  · simpa [backDoorState] using hpool.1

/-- `identify` returns the do-free front-door expression, and the count read
off that formula revises as one interventional quantity. -/
theorem front_door_identify_count_licence (experiment : Bool) :
    identify smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke) =
        .doFree frontDoorExpr ∧
      frontDoorCounts.strength = 3 / 5 ∧
      smokeObsCounts.strength = 3 / 4 ∧
      (poolInterventional frontDoorState experiment).interventional =
        frontDoorCounts.revise experiment ∧
      (poolInterventional frontDoorState experiment).observational =
        smokeObsCounts := by
  refine ⟨front_door_separates_id.2.1, front_door_count_strength,
    smoke_obs_count_strength, ?_⟩
  exact front_door_pool_is_one_revision experiment

def doorEnum : List Door := [Door.z, Door.x, Door.y]

theorem door_parents_fail :
    parentsIn doorGraph doorX (∅ : Finset Door) (∅ : Finset Door) = false := by
  decide

theorem door_delete_fail :
    deleteOK doorGraph doorY doorX (∅ : Finset Door) = false := by
  decide

theorem door_no_front_mediator :
    findVertex doorEnum (fun v =>
      outsideQuery (∅ : Finset Door) doorY doorX v &&
        frontDoorReady doorGraph doorX {v} doorY) = none := by
  decide

theorem door_no_napkin :
    findNapkin doorGraph doorEnum (∅ : Finset Door) doorY doorX = none := by
  decide

theorem door_singleton_backdoor :
    findVertex doorEnum (fun v =>
      outsideQuery (∅ : Finset Door) doorY doorX v &&
        backDoorReady doorGraph doorX {v} doorY) = some Door.z := by
  decide

/-- `identify` returns the do-free back-door sum, and the count read off that
formula revises as one interventional quantity. -/
theorem back_door_identify_count_licence (experiment : Bool) :
    identify doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX (∅ : Finset Door) =
        .doFree (backDoorShape doorX doorY doorZ) ∧
      backDoorCounts.strength = 1 / 2 ∧
      doorObsCounts.strength = 8 / 9 ∧
      (poolInterventional backDoorState experiment).interventional =
        backDoorCounts.revise experiment ∧
      (poolInterventional backDoorState experiment).observational =
        doorObsCounts := by
  refine ⟨?_, back_door_count_strength, door_obs_count_strength, ?_⟩
  · unfold identify
    have hparents :
        ¬ parentsIn doorGraph doorX (∅ : Finset Door) (∅ : Finset Door) = true := by
      simp [door_parents_fail]
    have hdelete : ¬ deleteOK doorGraph doorY doorX (∅ : Finset Door) = true := by
      simp [door_delete_fail]
    split
    · rename_i hzero
      cases hzero
    · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset Door) = ∅)]
      rw [door_no_front_mediator, door_no_napkin, door_singleton_backdoor]
      simp [doorZ]
  · exact back_door_pool_is_one_revision experiment

end Mettapedia.GSLT.Causality.DoCalculus
