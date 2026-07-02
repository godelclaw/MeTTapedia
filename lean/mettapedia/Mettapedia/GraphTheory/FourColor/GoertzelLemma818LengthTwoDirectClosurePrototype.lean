import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Prototype direct closure bridge for one generated length-two fiber

This module checks the proof shape for converting generated parent rows into
a `chainFiberConnected` theorem without reducing `closeChainFiber` directly.
It covers only the first nonempty `tau,tau` fiber; the full bridge is generated
separately once this shape is stable.
-/

namespace GoertzelLemma818LengthTwoDirectClosurePrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber3StateAt (i : Nat) : List TauState :=
  directStates (ttFiber3RowAt i).sourceLeft (ttFiber3RowAt i).sourceRight

def ttFiber3ParentStateAt (i : Nat) : List TauState :=
  directStates (ttFiber3RowAt i).parentLeft (ttFiber3RowAt i).parentRight

def ttFiber3DirectStates : List (List TauState) :=
  [ ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3
  , ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7
  ]

def ttFiber3Prefix0 : List (List TauState) :=
  [ttFiber3StateAt 0]

def ttFiber3Prefix1 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1]

def ttFiber3Prefix2 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2]

def ttFiber3Prefix3 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3]

def ttFiber3Prefix4 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4]

def ttFiber3Prefix5 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5]

def ttFiber3Prefix6 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6]

def ttFiber3Prefix7 : List (List TauState) :=
  [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7]

theorem ttFiber3ReverseSpecifiedStep1 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 1)
      (ttFiber3RowAt 1).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 1) (by decide) ttFiber3ReverseRow_1_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSpecifiedStep2 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 1) (ttFiber3StateAt 2)
      (ttFiber3RowAt 2).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 2) (by decide) ttFiber3ReverseRow_2_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSpecifiedStep3 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 3)
      (ttFiber3RowAt 3).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 3) (by decide) ttFiber3ReverseRow_3_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSpecifiedStep4 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 4)
      (ttFiber3RowAt 4).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 4) (by decide) ttFiber3ReverseRow_4_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSpecifiedStep5 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 1) (ttFiber3StateAt 5)
      (ttFiber3RowAt 5).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 5) (by decide) ttFiber3ReverseRow_5_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSpecifiedStep6 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 2) (ttFiber3StateAt 6)
      (ttFiber3RowAt 6).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 6) (by decide) ttFiber3ReverseRow_6_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSpecifiedStep7 :
    chainSpecifiedKempeStep ttWord (ttFiber3StateAt 3) (ttFiber3StateAt 7)
      (ttFiber3RowAt 7).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber3Key ttFiber3Expected
    (ttFiber3RowAt 7) (by decide) ttFiber3ReverseRow_7_ok
  simpa [ttFiber3StateAt, ttFiber3RowAt, ttFiber3Rows, listGetD, directRow] using h

theorem ttFiber3ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 1)
    (ttFiber3RowAt 1).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep1

theorem ttFiber3ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 1) (ttFiber3StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 1) (ttFiber3StateAt 2)
    (ttFiber3RowAt 2).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep2

theorem ttFiber3ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 3)
    (ttFiber3RowAt 3).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep3

theorem ttFiber3ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 0) (ttFiber3StateAt 4)
    (ttFiber3RowAt 4).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep4

theorem ttFiber3ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 1) (ttFiber3StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 1) (ttFiber3StateAt 5)
    (ttFiber3RowAt 5).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep5

theorem ttFiber3ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 2) (ttFiber3StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 2) (ttFiber3StateAt 6)
    (ttFiber3RowAt 6).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep6

theorem ttFiber3ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber3StateAt 3) (ttFiber3StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber3StateAt 3) (ttFiber3StateAt 7)
    (ttFiber3RowAt 7).move (by decide) (by decide) ttFiber3ReverseSpecifiedStep7

theorem ttFiber3State0_in_prefix0 :
    ttFiber3StateAt 0 ∈ chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0] := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber3Prefix0 [ttFiber3StateAt 0]
    (ttFiber3StateAt 0) (by decide)

theorem ttFiber3State1_in_prefix1 :
    ttFiber3StateAt 1 ∈ chainClosureStep ttWord ttFiber3Prefix1 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 0 ∈
      chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0] :=
    ttFiber3State0_in_prefix0
  have hparentBefore : ttFiber3StateAt 0 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0] = ttFiber3Prefix0 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0])
      (ttFiber3StateAt 0) hparentPrefix
  rw [show ttFiber3Prefix1 = [ttFiber3StateAt 0] ++ [ttFiber3StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 1) []
    (chainClosureStep ttWord [ttFiber3StateAt 0] [ttFiber3StateAt 0])
    (ttFiber3StateAt 0) hparentBefore
    ttFiber3ReverseSingleStep1

theorem ttFiber3State2_in_prefix2 :
    ttFiber3StateAt 2 ∈ chainClosureStep ttWord ttFiber3Prefix2 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 1 ∈
      chainClosureStep ttWord ttFiber3Prefix1 [ttFiber3StateAt 0] :=
    ttFiber3State1_in_prefix1
  have hparentBefore : ttFiber3StateAt 1 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0, ttFiber3StateAt 1] = ttFiber3Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber3Prefix1 [ttFiber3StateAt 0])
      (ttFiber3StateAt 1) hparentPrefix
  rw [show ttFiber3Prefix2 = [ttFiber3StateAt 0, ttFiber3StateAt 1] ++ [ttFiber3StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 2) []
    (chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1] [ttFiber3StateAt 0])
    (ttFiber3StateAt 1) hparentBefore
    ttFiber3ReverseSingleStep2

theorem ttFiber3State3_in_prefix3 :
    ttFiber3StateAt 3 ∈ chainClosureStep ttWord ttFiber3Prefix3 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 0 ∈
      chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0] :=
    ttFiber3State0_in_prefix0
  have hparentBefore : ttFiber3StateAt 0 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2] = ttFiber3Prefix0 ++ [ttFiber3StateAt 1, ttFiber3StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 1, ttFiber3StateAt 2]
      (chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0])
      (ttFiber3StateAt 0) hparentPrefix
  rw [show ttFiber3Prefix3 = [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2] ++ [ttFiber3StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 3) []
    (chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2] [ttFiber3StateAt 0])
    (ttFiber3StateAt 0) hparentBefore
    ttFiber3ReverseSingleStep3

theorem ttFiber3State4_in_prefix4 :
    ttFiber3StateAt 4 ∈ chainClosureStep ttWord ttFiber3Prefix4 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 0 ∈
      chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0] :=
    ttFiber3State0_in_prefix0
  have hparentBefore : ttFiber3StateAt 0 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3] = ttFiber3Prefix0 ++ [ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3]
      (chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0])
      (ttFiber3StateAt 0) hparentPrefix
  rw [show ttFiber3Prefix4 = [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3] ++ [ttFiber3StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 4) []
    (chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3] [ttFiber3StateAt 0])
    (ttFiber3StateAt 0) hparentBefore
    ttFiber3ReverseSingleStep4

theorem ttFiber3State5_in_prefix5 :
    ttFiber3StateAt 5 ∈ chainClosureStep ttWord ttFiber3Prefix5 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 1 ∈
      chainClosureStep ttWord ttFiber3Prefix1 [ttFiber3StateAt 0] :=
    ttFiber3State1_in_prefix1
  have hparentBefore : ttFiber3StateAt 1 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4] = ttFiber3Prefix1 ++ [ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4]
      (chainClosureStep ttWord ttFiber3Prefix1 [ttFiber3StateAt 0])
      (ttFiber3StateAt 1) hparentPrefix
  rw [show ttFiber3Prefix5 = [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4] ++ [ttFiber3StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 5) []
    (chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4] [ttFiber3StateAt 0])
    (ttFiber3StateAt 1) hparentBefore
    ttFiber3ReverseSingleStep5

theorem ttFiber3State6_in_prefix6 :
    ttFiber3StateAt 6 ∈ chainClosureStep ttWord ttFiber3Prefix6 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 2 ∈
      chainClosureStep ttWord ttFiber3Prefix2 [ttFiber3StateAt 0] :=
    ttFiber3State2_in_prefix2
  have hparentBefore : ttFiber3StateAt 2 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5] = ttFiber3Prefix2 ++ [ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5]
      (chainClosureStep ttWord ttFiber3Prefix2 [ttFiber3StateAt 0])
      (ttFiber3StateAt 2) hparentPrefix
  rw [show ttFiber3Prefix6 = [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5] ++ [ttFiber3StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 6) []
    (chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5] [ttFiber3StateAt 0])
    (ttFiber3StateAt 2) hparentBefore
    ttFiber3ReverseSingleStep6

theorem ttFiber3State7_in_prefix7 :
    ttFiber3StateAt 7 ∈ chainClosureStep ttWord ttFiber3Prefix7 [ttFiber3StateAt 0] := by
  have hparentPrefix : ttFiber3StateAt 3 ∈
      chainClosureStep ttWord ttFiber3Prefix3 [ttFiber3StateAt 0] :=
    ttFiber3State3_in_prefix3
  have hparentBefore : ttFiber3StateAt 3 ∈
      chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6] [ttFiber3StateAt 0] := by
    rw [show [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6] = ttFiber3Prefix3 ++ [ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6]
      (chainClosureStep ttWord ttFiber3Prefix3 [ttFiber3StateAt 0])
      (ttFiber3StateAt 3) hparentPrefix
  rw [show ttFiber3Prefix7 = [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6] ++ [ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber3StateAt 7) []
    (chainClosureStep ttWord [ttFiber3StateAt 0, ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6] [ttFiber3StateAt 0])
    (ttFiber3StateAt 3) hparentBefore
    ttFiber3ReverseSingleStep7

theorem ttFiber3State0_in_closureStep :
    ttFiber3StateAt 0 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix0 ++ [ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 1, ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix0 [ttFiber3StateAt 0])
    (ttFiber3StateAt 0) ttFiber3State0_in_prefix0

theorem ttFiber3State1_in_closureStep :
    ttFiber3StateAt 1 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix1 ++ [ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 2, ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix1 [ttFiber3StateAt 0])
    (ttFiber3StateAt 1) ttFiber3State1_in_prefix1

theorem ttFiber3State2_in_closureStep :
    ttFiber3StateAt 2 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix2 ++ [ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 3, ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix2 [ttFiber3StateAt 0])
    (ttFiber3StateAt 2) ttFiber3State2_in_prefix2

theorem ttFiber3State3_in_closureStep :
    ttFiber3StateAt 3 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix3 ++ [ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 4, ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix3 [ttFiber3StateAt 0])
    (ttFiber3StateAt 3) ttFiber3State3_in_prefix3

theorem ttFiber3State4_in_closureStep :
    ttFiber3StateAt 4 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix4 ++ [ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 5, ttFiber3StateAt 6, ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix4 [ttFiber3StateAt 0])
    (ttFiber3StateAt 4) ttFiber3State4_in_prefix4

theorem ttFiber3State5_in_closureStep :
    ttFiber3StateAt 5 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix5 ++ [ttFiber3StateAt 6, ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 6, ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix5 [ttFiber3StateAt 0])
    (ttFiber3StateAt 5) ttFiber3State5_in_prefix5

theorem ttFiber3State6_in_closureStep :
    ttFiber3StateAt 6 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix6 ++ [ttFiber3StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber3StateAt 7]
    (chainClosureStep ttWord ttFiber3Prefix6 [ttFiber3StateAt 0])
    (ttFiber3StateAt 6) ttFiber3State6_in_prefix6

theorem ttFiber3State7_in_closureStep :
    ttFiber3StateAt 7 ∈ chainClosureStep ttWord ttFiber3DirectStates [ttFiber3StateAt 0] := by
  rw [show ttFiber3DirectStates = ttFiber3Prefix7 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber3Prefix7 [ttFiber3StateAt 0])
    (ttFiber3StateAt 7) ttFiber3State7_in_prefix7

theorem ttFiber3State0_in_close :
    ttFiber3StateAt 0 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 0 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 0) ttFiber3State0_in_closureStep

theorem ttFiber3State1_in_close :
    ttFiber3StateAt 1 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 1 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 1) ttFiber3State1_in_closureStep

theorem ttFiber3State2_in_close :
    ttFiber3StateAt 2 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 2 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 2) ttFiber3State2_in_closureStep

theorem ttFiber3State3_in_close :
    ttFiber3StateAt 3 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 3 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 3) ttFiber3State3_in_closureStep

theorem ttFiber3State4_in_close :
    ttFiber3StateAt 4 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 4 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 4) ttFiber3State4_in_closureStep

theorem ttFiber3State5_in_close :
    ttFiber3StateAt 5 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 5 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 5) ttFiber3State5_in_closureStep

theorem ttFiber3State6_in_close :
    ttFiber3StateAt 6 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 6 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 6) ttFiber3State6_in_closureStep

theorem ttFiber3State7_in_close :
    ttFiber3StateAt 7 ∈
      closeChainFiber ttWord ttFiber3DirectStates ttFiber3DirectStates.length
        [ttFiber3StateAt 0] := by
  change ttFiber3StateAt 7 ∈ closeChainFiber ttWord ttFiber3DirectStates (7 + 1)
    [ttFiber3StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber3DirectStates 7
    [ttFiber3StateAt 0] (ttFiber3StateAt 7) ttFiber3State7_in_closureStep

theorem ttFiber3DirectConnected :
    chainFiberConnected ttWord ttFiber3DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber3DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber3State0_in_close
  · subst state
    exact ttFiber3State1_in_close
  · subst state
    exact ttFiber3State2_in_close
  · subst state
    exact ttFiber3State3_in_close
  · subst state
    exact ttFiber3State4_in_close
  · subst state
    exact ttFiber3State5_in_close
  · subst state
    exact ttFiber3State6_in_close
  · subst state
    exact ttFiber3State7_in_close
  · cases h

def ttFiber5StateAt (i : Nat) : List TauState :=
  directStates (ttFiber5RowAt i).sourceLeft (ttFiber5RowAt i).sourceRight

def ttFiber5ParentStateAt (i : Nat) : List TauState :=
  directStates (ttFiber5RowAt i).parentLeft (ttFiber5RowAt i).parentRight

def ttFiber5DirectStates : List (List TauState) :=
  [ ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3
  , ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7
  ]

def ttFiber5Prefix0 : List (List TauState) :=
  [ttFiber5StateAt 0]

def ttFiber5Prefix1 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1]

def ttFiber5Prefix2 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2]

def ttFiber5Prefix3 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3]

def ttFiber5Prefix4 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4]

def ttFiber5Prefix5 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5]

def ttFiber5Prefix6 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6]

def ttFiber5Prefix7 : List (List TauState) :=
  [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7]

theorem ttFiber5ReverseRow_1_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk0] at h
  exact h.2

theorem ttFiber5ReverseRow_2_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk1] at h
  exact h.1

theorem ttFiber5ReverseRow_3_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk1] at h
  exact h.2

theorem ttFiber5ReverseRow_4_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk2] at h
  exact h.1

theorem ttFiber5ReverseRow_5_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk2] at h
  exact h.2

theorem ttFiber5ReverseRow_6_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk3] at h
  exact h.1

theorem ttFiber5ReverseRow_7_ok :
    directRowReverseValid ttFiber5Key ttFiber5Expected (ttFiber5RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber5Chunk3] at h
  exact h.2

theorem ttFiber5ReverseSpecifiedStep1 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 1)
      (ttFiber5RowAt 1).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 1) (by decide) ttFiber5ReverseRow_1_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSpecifiedStep2 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 1) (ttFiber5StateAt 2)
      (ttFiber5RowAt 2).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 2) (by decide) ttFiber5ReverseRow_2_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSpecifiedStep3 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 3)
      (ttFiber5RowAt 3).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 3) (by decide) ttFiber5ReverseRow_3_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSpecifiedStep4 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 4)
      (ttFiber5RowAt 4).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 4) (by decide) ttFiber5ReverseRow_4_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSpecifiedStep5 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 1) (ttFiber5StateAt 5)
      (ttFiber5RowAt 5).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 5) (by decide) ttFiber5ReverseRow_5_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSpecifiedStep6 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 2) (ttFiber5StateAt 6)
      (ttFiber5RowAt 6).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 6) (by decide) ttFiber5ReverseRow_6_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSpecifiedStep7 :
    chainSpecifiedKempeStep ttWord (ttFiber5StateAt 3) (ttFiber5StateAt 7)
      (ttFiber5RowAt 7).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber5Key ttFiber5Expected
    (ttFiber5RowAt 7) (by decide) ttFiber5ReverseRow_7_ok
  simpa [ttFiber5StateAt, ttFiber5RowAt, ttFiber5Rows, listGetD, directRow] using h

theorem ttFiber5ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 1)
    (ttFiber5RowAt 1).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep1

theorem ttFiber5ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 1) (ttFiber5StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 1) (ttFiber5StateAt 2)
    (ttFiber5RowAt 2).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep2

theorem ttFiber5ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 3)
    (ttFiber5RowAt 3).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep3

theorem ttFiber5ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 0) (ttFiber5StateAt 4)
    (ttFiber5RowAt 4).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep4

theorem ttFiber5ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 1) (ttFiber5StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 1) (ttFiber5StateAt 5)
    (ttFiber5RowAt 5).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep5

theorem ttFiber5ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 2) (ttFiber5StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 2) (ttFiber5StateAt 6)
    (ttFiber5RowAt 6).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep6

theorem ttFiber5ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber5StateAt 3) (ttFiber5StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber5StateAt 3) (ttFiber5StateAt 7)
    (ttFiber5RowAt 7).move (by decide) (by decide) ttFiber5ReverseSpecifiedStep7

theorem ttFiber5State0_in_prefix0 :
    ttFiber5StateAt 0 ∈ chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0] := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber5Prefix0 [ttFiber5StateAt 0]
    (ttFiber5StateAt 0) (by decide)

theorem ttFiber5State1_in_prefix1 :
    ttFiber5StateAt 1 ∈ chainClosureStep ttWord ttFiber5Prefix1 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 0 ∈
      chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0] :=
    ttFiber5State0_in_prefix0
  have hparentBefore : ttFiber5StateAt 0 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0] = ttFiber5Prefix0 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0])
      (ttFiber5StateAt 0) hparentPrefix
  rw [show ttFiber5Prefix1 = [ttFiber5StateAt 0] ++ [ttFiber5StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 1) []
    (chainClosureStep ttWord [ttFiber5StateAt 0] [ttFiber5StateAt 0])
    (ttFiber5StateAt 0) hparentBefore
    ttFiber5ReverseSingleStep1

theorem ttFiber5State2_in_prefix2 :
    ttFiber5StateAt 2 ∈ chainClosureStep ttWord ttFiber5Prefix2 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 1 ∈
      chainClosureStep ttWord ttFiber5Prefix1 [ttFiber5StateAt 0] :=
    ttFiber5State1_in_prefix1
  have hparentBefore : ttFiber5StateAt 1 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0, ttFiber5StateAt 1] = ttFiber5Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber5Prefix1 [ttFiber5StateAt 0])
      (ttFiber5StateAt 1) hparentPrefix
  rw [show ttFiber5Prefix2 = [ttFiber5StateAt 0, ttFiber5StateAt 1] ++ [ttFiber5StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 2) []
    (chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1] [ttFiber5StateAt 0])
    (ttFiber5StateAt 1) hparentBefore
    ttFiber5ReverseSingleStep2

theorem ttFiber5State3_in_prefix3 :
    ttFiber5StateAt 3 ∈ chainClosureStep ttWord ttFiber5Prefix3 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 0 ∈
      chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0] :=
    ttFiber5State0_in_prefix0
  have hparentBefore : ttFiber5StateAt 0 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2] = ttFiber5Prefix0 ++ [ttFiber5StateAt 1, ttFiber5StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 1, ttFiber5StateAt 2]
      (chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0])
      (ttFiber5StateAt 0) hparentPrefix
  rw [show ttFiber5Prefix3 = [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2] ++ [ttFiber5StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 3) []
    (chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2] [ttFiber5StateAt 0])
    (ttFiber5StateAt 0) hparentBefore
    ttFiber5ReverseSingleStep3

theorem ttFiber5State4_in_prefix4 :
    ttFiber5StateAt 4 ∈ chainClosureStep ttWord ttFiber5Prefix4 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 0 ∈
      chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0] :=
    ttFiber5State0_in_prefix0
  have hparentBefore : ttFiber5StateAt 0 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3] = ttFiber5Prefix0 ++ [ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3]
      (chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0])
      (ttFiber5StateAt 0) hparentPrefix
  rw [show ttFiber5Prefix4 = [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3] ++ [ttFiber5StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 4) []
    (chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3] [ttFiber5StateAt 0])
    (ttFiber5StateAt 0) hparentBefore
    ttFiber5ReverseSingleStep4

theorem ttFiber5State5_in_prefix5 :
    ttFiber5StateAt 5 ∈ chainClosureStep ttWord ttFiber5Prefix5 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 1 ∈
      chainClosureStep ttWord ttFiber5Prefix1 [ttFiber5StateAt 0] :=
    ttFiber5State1_in_prefix1
  have hparentBefore : ttFiber5StateAt 1 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4] = ttFiber5Prefix1 ++ [ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4]
      (chainClosureStep ttWord ttFiber5Prefix1 [ttFiber5StateAt 0])
      (ttFiber5StateAt 1) hparentPrefix
  rw [show ttFiber5Prefix5 = [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4] ++ [ttFiber5StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 5) []
    (chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4] [ttFiber5StateAt 0])
    (ttFiber5StateAt 1) hparentBefore
    ttFiber5ReverseSingleStep5

theorem ttFiber5State6_in_prefix6 :
    ttFiber5StateAt 6 ∈ chainClosureStep ttWord ttFiber5Prefix6 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 2 ∈
      chainClosureStep ttWord ttFiber5Prefix2 [ttFiber5StateAt 0] :=
    ttFiber5State2_in_prefix2
  have hparentBefore : ttFiber5StateAt 2 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5] = ttFiber5Prefix2 ++ [ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5]
      (chainClosureStep ttWord ttFiber5Prefix2 [ttFiber5StateAt 0])
      (ttFiber5StateAt 2) hparentPrefix
  rw [show ttFiber5Prefix6 = [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5] ++ [ttFiber5StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 6) []
    (chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5] [ttFiber5StateAt 0])
    (ttFiber5StateAt 2) hparentBefore
    ttFiber5ReverseSingleStep6

theorem ttFiber5State7_in_prefix7 :
    ttFiber5StateAt 7 ∈ chainClosureStep ttWord ttFiber5Prefix7 [ttFiber5StateAt 0] := by
  have hparentPrefix : ttFiber5StateAt 3 ∈
      chainClosureStep ttWord ttFiber5Prefix3 [ttFiber5StateAt 0] :=
    ttFiber5State3_in_prefix3
  have hparentBefore : ttFiber5StateAt 3 ∈
      chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6] [ttFiber5StateAt 0] := by
    rw [show [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6] = ttFiber5Prefix3 ++ [ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6]
      (chainClosureStep ttWord ttFiber5Prefix3 [ttFiber5StateAt 0])
      (ttFiber5StateAt 3) hparentPrefix
  rw [show ttFiber5Prefix7 = [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6] ++ [ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber5StateAt 7) []
    (chainClosureStep ttWord [ttFiber5StateAt 0, ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6] [ttFiber5StateAt 0])
    (ttFiber5StateAt 3) hparentBefore
    ttFiber5ReverseSingleStep7

theorem ttFiber5State0_in_closureStep :
    ttFiber5StateAt 0 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix0 ++ [ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 1, ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix0 [ttFiber5StateAt 0])
    (ttFiber5StateAt 0) ttFiber5State0_in_prefix0

theorem ttFiber5State1_in_closureStep :
    ttFiber5StateAt 1 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix1 ++ [ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 2, ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix1 [ttFiber5StateAt 0])
    (ttFiber5StateAt 1) ttFiber5State1_in_prefix1

theorem ttFiber5State2_in_closureStep :
    ttFiber5StateAt 2 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix2 ++ [ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 3, ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix2 [ttFiber5StateAt 0])
    (ttFiber5StateAt 2) ttFiber5State2_in_prefix2

theorem ttFiber5State3_in_closureStep :
    ttFiber5StateAt 3 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix3 ++ [ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 4, ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix3 [ttFiber5StateAt 0])
    (ttFiber5StateAt 3) ttFiber5State3_in_prefix3

theorem ttFiber5State4_in_closureStep :
    ttFiber5StateAt 4 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix4 ++ [ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 5, ttFiber5StateAt 6, ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix4 [ttFiber5StateAt 0])
    (ttFiber5StateAt 4) ttFiber5State4_in_prefix4

theorem ttFiber5State5_in_closureStep :
    ttFiber5StateAt 5 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix5 ++ [ttFiber5StateAt 6, ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 6, ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix5 [ttFiber5StateAt 0])
    (ttFiber5StateAt 5) ttFiber5State5_in_prefix5

theorem ttFiber5State6_in_closureStep :
    ttFiber5StateAt 6 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix6 ++ [ttFiber5StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber5StateAt 7]
    (chainClosureStep ttWord ttFiber5Prefix6 [ttFiber5StateAt 0])
    (ttFiber5StateAt 6) ttFiber5State6_in_prefix6

theorem ttFiber5State7_in_closureStep :
    ttFiber5StateAt 7 ∈ chainClosureStep ttWord ttFiber5DirectStates [ttFiber5StateAt 0] := by
  rw [show ttFiber5DirectStates = ttFiber5Prefix7 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber5Prefix7 [ttFiber5StateAt 0])
    (ttFiber5StateAt 7) ttFiber5State7_in_prefix7

theorem ttFiber5State0_in_close :
    ttFiber5StateAt 0 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 0 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 0) ttFiber5State0_in_closureStep

theorem ttFiber5State1_in_close :
    ttFiber5StateAt 1 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 1 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 1) ttFiber5State1_in_closureStep

theorem ttFiber5State2_in_close :
    ttFiber5StateAt 2 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 2 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 2) ttFiber5State2_in_closureStep

theorem ttFiber5State3_in_close :
    ttFiber5StateAt 3 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 3 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 3) ttFiber5State3_in_closureStep

theorem ttFiber5State4_in_close :
    ttFiber5StateAt 4 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 4 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 4) ttFiber5State4_in_closureStep

theorem ttFiber5State5_in_close :
    ttFiber5StateAt 5 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 5 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 5) ttFiber5State5_in_closureStep

theorem ttFiber5State6_in_close :
    ttFiber5StateAt 6 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 6 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 6) ttFiber5State6_in_closureStep

theorem ttFiber5State7_in_close :
    ttFiber5StateAt 7 ∈
      closeChainFiber ttWord ttFiber5DirectStates ttFiber5DirectStates.length
        [ttFiber5StateAt 0] := by
  change ttFiber5StateAt 7 ∈ closeChainFiber ttWord ttFiber5DirectStates (7 + 1)
    [ttFiber5StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber5DirectStates 7
    [ttFiber5StateAt 0] (ttFiber5StateAt 7) ttFiber5State7_in_closureStep

theorem ttFiber5DirectConnected :
    chainFiberConnected ttWord ttFiber5DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber5DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber5State0_in_close
  · subst state
    exact ttFiber5State1_in_close
  · subst state
    exact ttFiber5State2_in_close
  · subst state
    exact ttFiber5State3_in_close
  · subst state
    exact ttFiber5State4_in_close
  · subst state
    exact ttFiber5State5_in_close
  · subst state
    exact ttFiber5State6_in_close
  · subst state
    exact ttFiber5State7_in_close
  · cases h

theorem directConnected8ShapeB
    (word : List TauOrient) (s : Nat → List TauState)
    (h01 : chainSingleKempeStep word (s 0) (s 1) = true)
    (h02 : chainSingleKempeStep word (s 0) (s 2) = true)
    (h13 : chainSingleKempeStep word (s 1) (s 3) = true)
    (h04 : chainSingleKempeStep word (s 0) (s 4) = true)
    (h15 : chainSingleKempeStep word (s 1) (s 5) = true)
    (h26 : chainSingleKempeStep word (s 2) (s 6) = true)
    (h37 : chainSingleKempeStep word (s 3) (s 7) = true) :
    chainFiberConnected word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] = true := by
  have h0_prefix :
      s 0 ∈ chainClosureStep word [s 0] [s 0] := by
    exact chainClosureStep_mem_of_seen word [s 0] [s 0] (s 0) (by simp)
  have h1_prefix :
      s 1 ∈ chainClosureStep word [s 0, s 1] [s 0] := by
    rw [show [s 0, s 1] = [s 0] ++ [s 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 1) []
      (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix h01
  have h2_prefix :
      s 2 ∈ chainClosureStep word [s 0, s 1, s 2] [s 0] := by
    have hparentBefore :
        s 0 ∈ chainClosureStep word [s 0, s 1] [s 0] := by
      rw [show [s 0, s 1] = [s 0] ++ [s 1] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 1]
        (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix
    rw [show [s 0, s 1, s 2] = [s 0, s 1] ++ [s 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 2) []
      (chainClosureStep word [s 0, s 1] [s 0]) (s 0) hparentBefore h02
  have h3_prefix :
      s 3 ∈ chainClosureStep word [s 0, s 1, s 2, s 3] [s 0] := by
    have hparentBefore :
        s 1 ∈ chainClosureStep word [s 0, s 1, s 2] [s 0] := by
      rw [show [s 0, s 1, s 2] = [s 0, s 1] ++ [s 2] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 2]
        (chainClosureStep word [s 0, s 1] [s 0]) (s 1) h1_prefix
    rw [show [s 0, s 1, s 2, s 3] = [s 0, s 1, s 2] ++ [s 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 3) []
      (chainClosureStep word [s 0, s 1, s 2] [s 0]) (s 1) hparentBefore h13
  have h4_prefix :
      s 4 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0] := by
    have hparentBefore :
        s 0 ∈ chainClosureStep word [s 0, s 1, s 2, s 3] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3] = [s 0] ++ [s 1, s 2, s 3] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 1, s 2, s 3]
        (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4] =
      [s 0, s 1, s 2, s 3] ++ [s 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 4) []
      (chainClosureStep word [s 0, s 1, s 2, s 3] [s 0])
      (s 0) hparentBefore h04
  have h5_prefix :
      s 5 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0] := by
    have hparentBefore :
        s 1 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3, s 4] =
        [s 0, s 1] ++ [s 2, s 3, s 4] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 2, s 3, s 4]
        (chainClosureStep word [s 0, s 1] [s 0]) (s 1) h1_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5] =
      [s 0, s 1, s 2, s 3, s 4] ++ [s 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 5) []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0])
      (s 1) hparentBefore h15
  have h6_prefix :
      s 6 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0] := by
    have hparentBefore :
        s 2 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3, s 4, s 5] =
        [s 0, s 1, s 2] ++ [s 3, s 4, s 5] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 3, s 4, s 5]
        (chainClosureStep word [s 0, s 1, s 2] [s 0]) (s 2) h2_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6] =
      [s 0, s 1, s 2, s 3, s 4, s 5] ++ [s 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 6) []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0])
      (s 2) hparentBefore h26
  have h7_prefix :
      s 7 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    have hparentBefore :
        s 3 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6] =
        [s 0, s 1, s 2, s 3] ++ [s 4, s 5, s 6] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 4, s 5, s 6]
        (chainClosureStep word [s 0, s 1, s 2, s 3] [s 0]) (s 3) h3_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6] ++ [s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 7) []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0])
      (s 3) hparentBefore h37
  have h0_closure :
      s 0 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0] ++ [s 1, s 2, s 3, s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix
  have h1_closure :
      s 1 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1] ++ [s 2, s 3, s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 2, s 3, s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1] [s 0]) (s 1) h1_prefix
  have h2_closure :
      s 2 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2] ++ [s 3, s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 3, s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2] [s 0]) (s 2) h2_prefix
  have h3_closure :
      s 3 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3] ++ [s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3] [s 0]) (s 3) h3_prefix
  have h4_closure :
      s 4 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4] ++ [s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0]) (s 4) h4_prefix
  have h5_closure :
      s 5 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5] ++ [s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0]) (s 5) h5_prefix
  have h6_closure :
      s 6 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6] ++ [s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0]) (s 6) h6_prefix
  have h7_closure :
      s 7 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] ++ [] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0])
      (s 7) h7_prefix
  have h0_close :
      s 0 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 0 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 0) h0_closure
  have h1_close :
      s 1 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 1 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 1) h1_closure
  have h2_close :
      s 2 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 2 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 2) h2_closure
  have h3_close :
      s 3 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 3 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 3) h3_closure
  have h4_close :
      s 4 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 4 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 4) h4_closure
  have h5_close :
      s 5 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 5 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 5) h5_closure
  have h6_close :
      s 6 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 6 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 6) h6_closure
  have h7_close :
      s 7 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 7 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 7) h7_closure
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact h0_close
  · subst state
    exact h1_close
  · subst state
    exact h2_close
  · subst state
    exact h3_close
  · subst state
    exact h4_close
  · subst state
    exact h5_close
  · subst state
    exact h6_close
  · subst state
    exact h7_close
  · cases h

theorem directConnected8ShapeA
    (word : List TauOrient) (s : Nat → List TauState)
    (h01 : chainSingleKempeStep word (s 0) (s 1) = true)
    (h12 : chainSingleKempeStep word (s 1) (s 2) = true)
    (h03 : chainSingleKempeStep word (s 0) (s 3) = true)
    (h04 : chainSingleKempeStep word (s 0) (s 4) = true)
    (h15 : chainSingleKempeStep word (s 1) (s 5) = true)
    (h26 : chainSingleKempeStep word (s 2) (s 6) = true)
    (h37 : chainSingleKempeStep word (s 3) (s 7) = true) :
    chainFiberConnected word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] = true := by
  have h0_prefix :
      s 0 ∈ chainClosureStep word [s 0] [s 0] := by
    exact chainClosureStep_mem_of_seen word [s 0] [s 0] (s 0) (by simp)
  have h1_prefix :
      s 1 ∈ chainClosureStep word [s 0, s 1] [s 0] := by
    rw [show [s 0, s 1] = [s 0] ++ [s 1] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 1) []
      (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix h01
  have h2_prefix :
      s 2 ∈ chainClosureStep word [s 0, s 1, s 2] [s 0] := by
    rw [show [s 0, s 1, s 2] = [s 0, s 1] ++ [s 2] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 2) []
      (chainClosureStep word [s 0, s 1] [s 0]) (s 1) h1_prefix h12
  have h3_prefix :
      s 3 ∈ chainClosureStep word [s 0, s 1, s 2, s 3] [s 0] := by
    have hparentBefore :
        s 0 ∈ chainClosureStep word [s 0, s 1, s 2] [s 0] := by
      rw [show [s 0, s 1, s 2] = [s 0] ++ [s 1, s 2] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 1, s 2]
        (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix
    rw [show [s 0, s 1, s 2, s 3] = [s 0, s 1, s 2] ++ [s 3] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 3) []
      (chainClosureStep word [s 0, s 1, s 2] [s 0]) (s 0) hparentBefore h03
  have h4_prefix :
      s 4 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0] := by
    have hparentBefore :
        s 0 ∈ chainClosureStep word [s 0, s 1, s 2, s 3] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3] = [s 0] ++ [s 1, s 2, s 3] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 1, s 2, s 3]
        (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4] =
      [s 0, s 1, s 2, s 3] ++ [s 4] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 4) []
      (chainClosureStep word [s 0, s 1, s 2, s 3] [s 0])
      (s 0) hparentBefore h04
  have h5_prefix :
      s 5 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0] := by
    have hparentBefore :
        s 1 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3, s 4] =
        [s 0, s 1] ++ [s 2, s 3, s 4] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 2, s 3, s 4]
        (chainClosureStep word [s 0, s 1] [s 0]) (s 1) h1_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5] =
      [s 0, s 1, s 2, s 3, s 4] ++ [s 5] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 5) []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0])
      (s 1) hparentBefore h15
  have h6_prefix :
      s 6 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0] := by
    have hparentBefore :
        s 2 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3, s 4, s 5] =
        [s 0, s 1, s 2] ++ [s 3, s 4, s 5] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 3, s 4, s 5]
        (chainClosureStep word [s 0, s 1, s 2] [s 0]) (s 2) h2_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6] =
      [s 0, s 1, s 2, s 3, s 4, s 5] ++ [s 6] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 6) []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0])
      (s 2) hparentBefore h26
  have h7_prefix :
      s 7 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    have hparentBefore :
        s 3 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0] := by
      rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6] =
        [s 0, s 1, s 2, s 3] ++ [s 4, s 5, s 6] by rfl]
      rw [chainClosureStep_append]
      exact chainClosureStep_mem_of_seen word [s 4, s 5, s 6]
        (chainClosureStep word [s 0, s 1, s 2, s 3] [s 0]) (s 3) h3_prefix
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6] ++ [s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_cons_mem_of_seen_step word (s 7) []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0])
      (s 3) hparentBefore h37
  have h0_closure :
      s 0 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0] ++ [s 1, s 2, s 3, s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0] [s 0]) (s 0) h0_prefix
  have h1_closure :
      s 1 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1] ++ [s 2, s 3, s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 2, s 3, s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1] [s 0]) (s 1) h1_prefix
  have h2_closure :
      s 2 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2] ++ [s 3, s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 3, s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2] [s 0]) (s 2) h2_prefix
  have h3_closure :
      s 3 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3] ++ [s 4, s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 4, s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3] [s 0]) (s 3) h3_prefix
  have h4_closure :
      s 4 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4] ++ [s 5, s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 5, s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4] [s 0]) (s 4) h4_prefix
  have h5_closure :
      s 5 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5] ++ [s 6, s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 6, s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5] [s 0]) (s 5) h5_prefix
  have h6_closure :
      s 6 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6] ++ [s 7] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word [s 7]
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6] [s 0]) (s 6) h6_prefix
  have h7_closure :
      s 7 ∈ chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0] := by
    rw [show [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] =
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] ++ [] by rfl]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen word []
      (chainClosureStep word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] [s 0])
      (s 7) h7_prefix
  have h0_close :
      s 0 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 0 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 0) h0_closure
  have h1_close :
      s 1 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 1 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 1) h1_closure
  have h2_close :
      s 2 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 2 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 2) h2_closure
  have h3_close :
      s 3 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 3 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 3) h3_closure
  have h4_close :
      s 4 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 4 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 4) h4_closure
  have h5_close :
      s 5 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 5 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 5) h5_closure
  have h6_close :
      s 6 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 6 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 6) h6_closure
  have h7_close :
      s 7 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
        [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7].length [s 0] := by
    change s 7 ∈ closeChainFiber word [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7]
      (7 + 1) [s 0]
    exact closeChainFiber_mem_of_closureStep word
      [s 0, s 1, s 2, s 3, s 4, s 5, s 6, s 7] 7 [s 0] (s 7) h7_closure
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · subst state
    exact h0_close
  · subst state
    exact h1_close
  · subst state
    exact h2_close
  · subst state
    exact h3_close
  · subst state
    exact h4_close
  · subst state
    exact h5_close
  · subst state
    exact h6_close
  · subst state
    exact h7_close
  · cases h

def ttFiber6StateAt (i : Nat) : List TauState :=
  directStates (ttFiber6RowAt i).sourceLeft (ttFiber6RowAt i).sourceRight

def ttFiber6ParentStateAt (i : Nat) : List TauState :=
  directStates (ttFiber6RowAt i).parentLeft (ttFiber6RowAt i).parentRight

def ttFiber6DirectStates : List (List TauState) :=
  [ ttFiber6StateAt 0, ttFiber6StateAt 1, ttFiber6StateAt 2, ttFiber6StateAt 3
  , ttFiber6StateAt 4, ttFiber6StateAt 5, ttFiber6StateAt 6, ttFiber6StateAt 7
  ]

theorem ttFiber6ReverseRow_1_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk0] at h
  exact h.2

theorem ttFiber6ReverseRow_2_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk1] at h
  exact h.1

theorem ttFiber6ReverseRow_3_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk1] at h
  exact h.2

theorem ttFiber6ReverseRow_4_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk2] at h
  exact h.1

theorem ttFiber6ReverseRow_5_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk2] at h
  exact h.2

theorem ttFiber6ReverseRow_6_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk3] at h
  exact h.1

theorem ttFiber6ReverseRow_7_ok :
    directRowReverseValid ttFiber6Key ttFiber6Expected (ttFiber6RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber6Chunk3] at h
  exact h.2

theorem ttFiber6ReverseSpecifiedStep1 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 1)
      (ttFiber6RowAt 1).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 1) (by decide) ttFiber6ReverseRow_1_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSpecifiedStep2 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 2)
      (ttFiber6RowAt 2).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 2) (by decide) ttFiber6ReverseRow_2_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSpecifiedStep3 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 1) (ttFiber6StateAt 3)
      (ttFiber6RowAt 3).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 3) (by decide) ttFiber6ReverseRow_3_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSpecifiedStep4 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 4)
      (ttFiber6RowAt 4).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 4) (by decide) ttFiber6ReverseRow_4_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSpecifiedStep5 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 1) (ttFiber6StateAt 5)
      (ttFiber6RowAt 5).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 5) (by decide) ttFiber6ReverseRow_5_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSpecifiedStep6 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 2) (ttFiber6StateAt 6)
      (ttFiber6RowAt 6).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 6) (by decide) ttFiber6ReverseRow_6_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSpecifiedStep7 :
    chainSpecifiedKempeStep ttWord (ttFiber6StateAt 3) (ttFiber6StateAt 7)
      (ttFiber6RowAt 7).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber6Key ttFiber6Expected
    (ttFiber6RowAt 7) (by decide) ttFiber6ReverseRow_7_ok
  simpa [ttFiber6StateAt, ttFiber6RowAt, ttFiber6Rows, listGetD, directRow] using h

theorem ttFiber6ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 1)
    (ttFiber6RowAt 1).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep1

theorem ttFiber6ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 2)
    (ttFiber6RowAt 2).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep2

theorem ttFiber6ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 1) (ttFiber6StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 1) (ttFiber6StateAt 3)
    (ttFiber6RowAt 3).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep3

theorem ttFiber6ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 0) (ttFiber6StateAt 4)
    (ttFiber6RowAt 4).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep4

theorem ttFiber6ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 1) (ttFiber6StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 1) (ttFiber6StateAt 5)
    (ttFiber6RowAt 5).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep5

theorem ttFiber6ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 2) (ttFiber6StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 2) (ttFiber6StateAt 6)
    (ttFiber6RowAt 6).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep6

theorem ttFiber6ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber6StateAt 3) (ttFiber6StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber6StateAt 3) (ttFiber6StateAt 7)
    (ttFiber6RowAt 7).move (by decide) (by decide) ttFiber6ReverseSpecifiedStep7

theorem ttFiber6DirectConnected :
    chainFiberConnected ttWord ttFiber6DirectStates = true := by
  simpa [ttFiber6DirectStates] using
    directConnected8ShapeB ttWord ttFiber6StateAt
      ttFiber6ReverseSingleStep1
      ttFiber6ReverseSingleStep2
      ttFiber6ReverseSingleStep3
      ttFiber6ReverseSingleStep4
      ttFiber6ReverseSingleStep5
      ttFiber6ReverseSingleStep6
      ttFiber6ReverseSingleStep7

def ttFiber7StateAt (i : Nat) : List TauState :=
  directStates (ttFiber7RowAt i).sourceLeft (ttFiber7RowAt i).sourceRight

def ttFiber7ParentStateAt (i : Nat) : List TauState :=
  directStates (ttFiber7RowAt i).parentLeft (ttFiber7RowAt i).parentRight

def ttFiber7DirectStates : List (List TauState) :=
  [ ttFiber7StateAt 0, ttFiber7StateAt 1, ttFiber7StateAt 2, ttFiber7StateAt 3
  , ttFiber7StateAt 4, ttFiber7StateAt 5, ttFiber7StateAt 6, ttFiber7StateAt 7
  ]

theorem ttFiber7ReverseRow_1_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk0] at h
  exact h.2

theorem ttFiber7ReverseRow_2_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk1] at h
  exact h.1

theorem ttFiber7ReverseRow_3_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk1] at h
  exact h.2

theorem ttFiber7ReverseRow_4_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk2] at h
  exact h.1

theorem ttFiber7ReverseRow_5_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk2] at h
  exact h.2

theorem ttFiber7ReverseRow_6_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk3] at h
  exact h.1

theorem ttFiber7ReverseRow_7_ok :
    directRowReverseValid ttFiber7Key ttFiber7Expected (ttFiber7RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber7Chunk3] at h
  exact h.2

theorem ttFiber7ReverseSpecifiedStep1 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 1)
      (ttFiber7RowAt 1).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 1) (by decide) ttFiber7ReverseRow_1_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSpecifiedStep2 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 2)
      (ttFiber7RowAt 2).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 2) (by decide) ttFiber7ReverseRow_2_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSpecifiedStep3 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 1) (ttFiber7StateAt 3)
      (ttFiber7RowAt 3).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 3) (by decide) ttFiber7ReverseRow_3_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSpecifiedStep4 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 4)
      (ttFiber7RowAt 4).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 4) (by decide) ttFiber7ReverseRow_4_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSpecifiedStep5 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 1) (ttFiber7StateAt 5)
      (ttFiber7RowAt 5).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 5) (by decide) ttFiber7ReverseRow_5_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSpecifiedStep6 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 2) (ttFiber7StateAt 6)
      (ttFiber7RowAt 6).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 6) (by decide) ttFiber7ReverseRow_6_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSpecifiedStep7 :
    chainSpecifiedKempeStep ttWord (ttFiber7StateAt 3) (ttFiber7StateAt 7)
      (ttFiber7RowAt 7).move = true := by
  have h := directRowReverseValid_step_of_ne ttFiber7Key ttFiber7Expected
    (ttFiber7RowAt 7) (by decide) ttFiber7ReverseRow_7_ok
  simpa [ttFiber7StateAt, ttFiber7RowAt, ttFiber7Rows, listGetD, directRow] using h

theorem ttFiber7ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 1)
    (ttFiber7RowAt 1).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep1

theorem ttFiber7ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 2)
    (ttFiber7RowAt 2).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep2

theorem ttFiber7ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 1) (ttFiber7StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 1) (ttFiber7StateAt 3)
    (ttFiber7RowAt 3).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep3

theorem ttFiber7ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 0) (ttFiber7StateAt 4)
    (ttFiber7RowAt 4).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep4

theorem ttFiber7ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 1) (ttFiber7StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 1) (ttFiber7StateAt 5)
    (ttFiber7RowAt 5).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep5

theorem ttFiber7ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 2) (ttFiber7StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 2) (ttFiber7StateAt 6)
    (ttFiber7RowAt 6).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep6

theorem ttFiber7ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber7StateAt 3) (ttFiber7StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber7StateAt 3) (ttFiber7StateAt 7)
    (ttFiber7RowAt 7).move (by decide) (by decide) ttFiber7ReverseSpecifiedStep7

theorem ttFiber7DirectConnected :
    chainFiberConnected ttWord ttFiber7DirectStates = true := by
  simpa [ttFiber7DirectStates] using
    directConnected8ShapeB ttWord ttFiber7StateAt
      ttFiber7ReverseSingleStep1
      ttFiber7ReverseSingleStep2
      ttFiber7ReverseSingleStep3
      ttFiber7ReverseSingleStep4
      ttFiber7ReverseSingleStep5
      ttFiber7ReverseSingleStep6
      ttFiber7ReverseSingleStep7

def ttFiber9StateAt (i : Nat) : List TauState :=
  directStates (ttFiber9RowAt i).sourceLeft (ttFiber9RowAt i).sourceRight

def ttFiber9ParentStateAt (i : Nat) : List TauState :=
  directStates (ttFiber9RowAt i).parentLeft (ttFiber9RowAt i).parentRight

def ttFiber9DirectStates : List (List TauState) :=
  [ ttFiber9StateAt 0, ttFiber9StateAt 1, ttFiber9StateAt 2, ttFiber9StateAt 3
  , ttFiber9StateAt 4, ttFiber9StateAt 5, ttFiber9StateAt 6, ttFiber9StateAt 7
  ]

theorem ttFiber9ReverseRow_1_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk0] at h
  exact h.2

theorem ttFiber9ReverseRow_2_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk1] at h
  exact h.1

theorem ttFiber9ReverseRow_3_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk1] at h
  exact h.2

theorem ttFiber9ReverseRow_4_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk2] at h
  exact h.1

theorem ttFiber9ReverseRow_5_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk2] at h
  exact h.2

theorem ttFiber9ReverseRow_6_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk3] at h
  exact h.1

theorem ttFiber9ReverseRow_7_ok :
    directRowReverseValid ttFiber9Key ttFiber9Expected (ttFiber9RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber9Chunk3] at h
  exact h.2

theorem ttFiber9ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 0) (ttFiber9StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 0) (ttFiber9StateAt 1)
    (ttFiber9RowAt 1).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 1) (by decide) ttFiber9ReverseRow_1_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 1) (ttFiber9StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 1) (ttFiber9StateAt 2)
    (ttFiber9RowAt 2).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 2) (by decide) ttFiber9ReverseRow_2_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 0) (ttFiber9StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 0) (ttFiber9StateAt 3)
    (ttFiber9RowAt 3).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 3) (by decide) ttFiber9ReverseRow_3_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 0) (ttFiber9StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 0) (ttFiber9StateAt 4)
    (ttFiber9RowAt 4).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 4) (by decide) ttFiber9ReverseRow_4_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 1) (ttFiber9StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 1) (ttFiber9StateAt 5)
    (ttFiber9RowAt 5).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 5) (by decide) ttFiber9ReverseRow_5_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 2) (ttFiber9StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 2) (ttFiber9StateAt 6)
    (ttFiber9RowAt 6).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 6) (by decide) ttFiber9ReverseRow_6_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber9StateAt 3) (ttFiber9StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber9StateAt 3) (ttFiber9StateAt 7)
    (ttFiber9RowAt 7).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber9Key ttFiber9Expected
        (ttFiber9RowAt 7) (by decide) ttFiber9ReverseRow_7_ok
      simpa [ttFiber9StateAt, ttFiber9RowAt, ttFiber9Rows, listGetD, directRow] using h)

theorem ttFiber9DirectConnected :
    chainFiberConnected ttWord ttFiber9DirectStates = true := by
  simpa [ttFiber9DirectStates] using
    directConnected8ShapeA ttWord ttFiber9StateAt
      ttFiber9ReverseSingleStep1
      ttFiber9ReverseSingleStep2
      ttFiber9ReverseSingleStep3
      ttFiber9ReverseSingleStep4
      ttFiber9ReverseSingleStep5
      ttFiber9ReverseSingleStep6
      ttFiber9ReverseSingleStep7

def ttFiber11StateAt (i : Nat) : List TauState :=
  directStates (ttFiber11RowAt i).sourceLeft (ttFiber11RowAt i).sourceRight

def ttFiber11ParentStateAt (i : Nat) : List TauState :=
  directStates (ttFiber11RowAt i).parentLeft (ttFiber11RowAt i).parentRight

def ttFiber11DirectStates : List (List TauState) :=
  [ ttFiber11StateAt 0, ttFiber11StateAt 1, ttFiber11StateAt 2, ttFiber11StateAt 3
  , ttFiber11StateAt 4, ttFiber11StateAt 5, ttFiber11StateAt 6, ttFiber11StateAt 7
  ]

theorem ttFiber11ReverseRow_1_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk0] at h
  exact h.2

theorem ttFiber11ReverseRow_2_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk1] at h
  exact h.1

theorem ttFiber11ReverseRow_3_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk1] at h
  exact h.2

theorem ttFiber11ReverseRow_4_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk2] at h
  exact h.1

theorem ttFiber11ReverseRow_5_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk2] at h
  exact h.2

theorem ttFiber11ReverseRow_6_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk3] at h
  exact h.1

theorem ttFiber11ReverseRow_7_ok :
    directRowReverseValid ttFiber11Key ttFiber11Expected (ttFiber11RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber11Chunk3] at h
  exact h.2

theorem ttFiber11ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 0) (ttFiber11StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 0) (ttFiber11StateAt 1)
    (ttFiber11RowAt 1).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 1) (by decide) ttFiber11ReverseRow_1_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 1) (ttFiber11StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 1) (ttFiber11StateAt 2)
    (ttFiber11RowAt 2).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 2) (by decide) ttFiber11ReverseRow_2_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 0) (ttFiber11StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 0) (ttFiber11StateAt 3)
    (ttFiber11RowAt 3).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 3) (by decide) ttFiber11ReverseRow_3_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 0) (ttFiber11StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 0) (ttFiber11StateAt 4)
    (ttFiber11RowAt 4).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 4) (by decide) ttFiber11ReverseRow_4_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 1) (ttFiber11StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 1) (ttFiber11StateAt 5)
    (ttFiber11RowAt 5).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 5) (by decide) ttFiber11ReverseRow_5_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 2) (ttFiber11StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 2) (ttFiber11StateAt 6)
    (ttFiber11RowAt 6).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 6) (by decide) ttFiber11ReverseRow_6_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber11StateAt 3) (ttFiber11StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single ttWord (ttFiber11StateAt 3) (ttFiber11StateAt 7)
    (ttFiber11RowAt 7).move (by decide) (by decide) (by
      have h := directRowReverseValid_step_of_ne ttFiber11Key ttFiber11Expected
        (ttFiber11RowAt 7) (by decide) ttFiber11ReverseRow_7_ok
      simpa [ttFiber11StateAt, ttFiber11RowAt, ttFiber11Rows, listGetD, directRow] using h)

theorem ttFiber11DirectConnected :
    chainFiberConnected ttWord ttFiber11DirectStates = true := by
  simpa [ttFiber11DirectStates] using
    directConnected8ShapeA ttWord ttFiber11StateAt
      ttFiber11ReverseSingleStep1
      ttFiber11ReverseSingleStep2
      ttFiber11ReverseSingleStep3
      ttFiber11ReverseSingleStep4
      ttFiber11ReverseSingleStep5
      ttFiber11ReverseSingleStep6
      ttFiber11ReverseSingleStep7

end GoertzelLemma818LengthTwoDirectClosurePrototype

end Mettapedia.GraphTheory.FourColor
