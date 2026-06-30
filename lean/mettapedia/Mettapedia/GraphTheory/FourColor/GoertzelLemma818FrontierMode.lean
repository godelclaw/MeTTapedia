import Mathlib.Data.List.Basic

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: lab-facing frontier mode table

This module records the finite profile-mode DFA extracted from the
frontier-automaton lab for the canonical `tau`/mirror-`tau` chain.  It is a
small table checkpoint for the replacement Lemma 8.18/8.19 composition
invariant.  It does not by itself prove all-chain `LKR_in`.
-/

namespace GoertzelLemma818FrontierMode

/-- The two orientations of the canonical three-cell gadget in the chain. -/
inductive TauOrient
  | tau
  | mirror
  deriving DecidableEq, BEq, Repr, Inhabited

def allOrientations : List TauOrient :=
  [TauOrient.tau, TauOrient.mirror]

def TauOrient.code : TauOrient → String
  | TauOrient.tau => "T"
  | TauOrient.mirror => "M"

/--
The 20 profile modes from
`fourcolor-lemma818-frontier-profile-mode-dfa-closure-20260630.json`.

The constructor numbers follow the sorted profile-hash order in that report.
-/
inductive FrontierMode
  | mode00
  | mode01
  | mode02
  | mode03
  | mode04
  | mode05
  | mode06
  | mode07
  | mode08
  | mode09
  | mode10
  | mode11
  | mode12
  | mode13
  | mode14
  | mode15
  | mode16
  | mode17
  | mode18
  | mode19
  deriving DecidableEq, BEq, Repr, Inhabited

def allModes : List FrontierMode :=
  [ FrontierMode.mode00
  , FrontierMode.mode01
  , FrontierMode.mode02
  , FrontierMode.mode03
  , FrontierMode.mode04
  , FrontierMode.mode05
  , FrontierMode.mode06
  , FrontierMode.mode07
  , FrontierMode.mode08
  , FrontierMode.mode09
  , FrontierMode.mode10
  , FrontierMode.mode11
  , FrontierMode.mode12
  , FrontierMode.mode13
  , FrontierMode.mode14
  , FrontierMode.mode15
  , FrontierMode.mode16
  , FrontierMode.mode17
  , FrontierMode.mode18
  , FrontierMode.mode19
  ]

def FrontierMode.profileHash : FrontierMode → String
  | FrontierMode.mode00 => "1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346"
  | FrontierMode.mode01 => "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b"
  | FrontierMode.mode02 => "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0"
  | FrontierMode.mode03 => "45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9"
  | FrontierMode.mode04 => "61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490"
  | FrontierMode.mode05 => "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324"
  | FrontierMode.mode06 => "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220"
  | FrontierMode.mode07 => "9b07069297dcf0a45b1ad3c8f672c21d2f1ecfb3889b6a6f01b16423fda14344"
  | FrontierMode.mode08 => "9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956"
  | FrontierMode.mode09 => "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff"
  | FrontierMode.mode10 => "abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc"
  | FrontierMode.mode11 => "c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931"
  | FrontierMode.mode12 => "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc"
  | FrontierMode.mode13 => "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd"
  | FrontierMode.mode14 => "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31"
  | FrontierMode.mode15 => "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4"
  | FrontierMode.mode16 => "ebccdaf35fc51d2e09dc7a18bca456d4ba509e742adeb9ed6bbbadf41e92f33d"
  | FrontierMode.mode17 => "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63"
  | FrontierMode.mode18 => "ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d"
  | FrontierMode.mode19 => "fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d"

def modeOfProfileHash (hash : String) : Option FrontierMode :=
  if hash == "1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346" then
    some FrontierMode.mode00
  else if hash == "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b" then
    some FrontierMode.mode01
  else if hash == "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0" then
    some FrontierMode.mode02
  else if hash == "45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9" then
    some FrontierMode.mode03
  else if hash == "61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490" then
    some FrontierMode.mode04
  else if hash == "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" then
    some FrontierMode.mode05
  else if hash == "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220" then
    some FrontierMode.mode06
  else if hash == "9b07069297dcf0a45b1ad3c8f672c21d2f1ecfb3889b6a6f01b16423fda14344" then
    some FrontierMode.mode07
  else if hash == "9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956" then
    some FrontierMode.mode08
  else if hash == "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" then
    some FrontierMode.mode09
  else if hash == "abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc" then
    some FrontierMode.mode10
  else if hash == "c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931" then
    some FrontierMode.mode11
  else if hash == "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" then
    some FrontierMode.mode12
  else if hash == "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd" then
    some FrontierMode.mode13
  else if hash == "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31" then
    some FrontierMode.mode14
  else if hash == "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4" then
    some FrontierMode.mode15
  else if hash == "ebccdaf35fc51d2e09dc7a18bca456d4ba509e742adeb9ed6bbbadf41e92f33d" then
    some FrontierMode.mode16
  else if hash == "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" then
    some FrontierMode.mode17
  else if hash == "ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d" then
    some FrontierMode.mode18
  else if hash == "fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d" then
    some FrontierMode.mode19
  else
    none

def profileHashLookupCheck : Bool :=
  allModes.all (fun mode =>
    modeOfProfileHash (FrontierMode.profileHash mode) == some mode)

theorem profileHashLookupCheck_ok :
    profileHashLookupCheck = true := by
  rfl

def FrontierMode.witnessWords : FrontierMode → List String
  | FrontierMode.mode00 => ["MTM"]
  | FrontierMode.mode01 => ["MMT", "MTT"]
  | FrontierMode.mode02 => ["MMMT", "MMTT", "MTTT"]
  | FrontierMode.mode03 => ["TMT"]
  | FrontierMode.mode04 => ["MM"]
  | FrontierMode.mode05 => ["MMM", "MTMTM", "MTTMM", "MTTTM"]
  | FrontierMode.mode06 => ["TMM", "TTM"]
  | FrontierMode.mode07 => ["T"]
  | FrontierMode.mode08 => ["MTMT"]
  | FrontierMode.mode09 => ["TMTMT", "TTT", "TTTMT", "TTTTT"]
  | FrontierMode.mode10 => ["TT"]
  | FrontierMode.mode11 => ["MT"]
  | FrontierMode.mode12 => ["TMMT", "TMTT", "TTMT", "TTTT"]
  | FrontierMode.mode13 => ["TMTMM", "TTTMM", "TTTTM"]
  | FrontierMode.mode14 => ["TMMM", "TTMM", "TTTM"]
  | FrontierMode.mode15 => ["MTMTT", "MTTMT", "MTTTT"]
  | FrontierMode.mode16 => ["M"]
  | FrontierMode.mode17 => ["MMMM", "MMTM", "MTMM", "MTTM"]
  | FrontierMode.mode18 => ["TM"]
  | FrontierMode.mode19 => ["TMTM"]

/-- The profile-mode transition observed/inferred by the finite lab DFA. -/
def step : FrontierMode → TauOrient → FrontierMode
  | FrontierMode.mode00, TauOrient.tau => FrontierMode.mode08
  | FrontierMode.mode00, TauOrient.mirror => FrontierMode.mode17
  | FrontierMode.mode01, TauOrient.tau => FrontierMode.mode02
  | FrontierMode.mode01, TauOrient.mirror => FrontierMode.mode17
  | FrontierMode.mode02, TauOrient.tau => FrontierMode.mode15
  | FrontierMode.mode02, TauOrient.mirror => FrontierMode.mode05
  | FrontierMode.mode03, TauOrient.tau => FrontierMode.mode12
  | FrontierMode.mode03, TauOrient.mirror => FrontierMode.mode19
  | FrontierMode.mode04, TauOrient.tau => FrontierMode.mode01
  | FrontierMode.mode04, TauOrient.mirror => FrontierMode.mode05
  | FrontierMode.mode05, TauOrient.tau => FrontierMode.mode02
  | FrontierMode.mode05, TauOrient.mirror => FrontierMode.mode17
  | FrontierMode.mode06, TauOrient.tau => FrontierMode.mode12
  | FrontierMode.mode06, TauOrient.mirror => FrontierMode.mode14
  | FrontierMode.mode07, TauOrient.tau => FrontierMode.mode10
  | FrontierMode.mode07, TauOrient.mirror => FrontierMode.mode18
  | FrontierMode.mode08, TauOrient.tau => FrontierMode.mode15
  | FrontierMode.mode08, TauOrient.mirror => FrontierMode.mode05
  | FrontierMode.mode09, TauOrient.tau => FrontierMode.mode12
  | FrontierMode.mode09, TauOrient.mirror => FrontierMode.mode14
  | FrontierMode.mode10, TauOrient.tau => FrontierMode.mode09
  | FrontierMode.mode10, TauOrient.mirror => FrontierMode.mode06
  | FrontierMode.mode11, TauOrient.tau => FrontierMode.mode01
  | FrontierMode.mode11, TauOrient.mirror => FrontierMode.mode00
  | FrontierMode.mode12, TauOrient.tau => FrontierMode.mode09
  | FrontierMode.mode12, TauOrient.mirror => FrontierMode.mode13
  | FrontierMode.mode13, TauOrient.tau => FrontierMode.mode12
  | FrontierMode.mode13, TauOrient.mirror => FrontierMode.mode14
  | FrontierMode.mode14, TauOrient.tau => FrontierMode.mode09
  | FrontierMode.mode14, TauOrient.mirror => FrontierMode.mode13
  | FrontierMode.mode15, TauOrient.tau => FrontierMode.mode02
  | FrontierMode.mode15, TauOrient.mirror => FrontierMode.mode17
  | FrontierMode.mode16, TauOrient.tau => FrontierMode.mode11
  | FrontierMode.mode16, TauOrient.mirror => FrontierMode.mode04
  | FrontierMode.mode17, TauOrient.tau => FrontierMode.mode15
  | FrontierMode.mode17, TauOrient.mirror => FrontierMode.mode05
  | FrontierMode.mode18, TauOrient.tau => FrontierMode.mode03
  | FrontierMode.mode18, TauOrient.mirror => FrontierMode.mode06
  | FrontierMode.mode19, TauOrient.tau => FrontierMode.mode09
  | FrontierMode.mode19, TauOrient.mirror => FrontierMode.mode13

def allTransitions : List (FrontierMode × TauOrient × FrontierMode) :=
  allModes.flatMap (fun mode =>
    allOrientations.map (fun orient => (mode, orient, step mode orient)))

def tableClosedCheck : Bool :=
  allModes.length == 20
  && allOrientations.length == 2
  && allTransitions.length == 40
  && allModes.all (fun mode =>
    allOrientations.all (fun orient => allModes.contains (step mode orient)))

theorem tableClosedCheck_ok : tableClosedCheck = true := by
  rfl

def initialMode : TauOrient → FrontierMode
  | TauOrient.tau => FrontierMode.mode07
  | TauOrient.mirror => FrontierMode.mode16

def wordMode : List TauOrient → Option FrontierMode
  | [] => none
  | orient :: rest => some (rest.foldl step (initialMode orient))

def representativeWords : FrontierMode → List (List TauOrient)
  | FrontierMode.mode00 => [[TauOrient.mirror, TauOrient.tau, TauOrient.mirror]]
  | FrontierMode.mode01 =>
      [ [TauOrient.mirror, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau]
      ]
  | FrontierMode.mode02 =>
      [ [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.mirror, TauOrient.mirror, TauOrient.tau, TauOrient.tau]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.tau]
      ]
  | FrontierMode.mode03 => [[TauOrient.tau, TauOrient.mirror, TauOrient.tau]]
  | FrontierMode.mode04 => [[TauOrient.mirror, TauOrient.mirror]]
  | FrontierMode.mode05 =>
      [ [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.mirror]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.mirror]
      ]
  | FrontierMode.mode06 =>
      [ [TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.tau, TauOrient.tau, TauOrient.mirror]
      ]
  | FrontierMode.mode07 => [[TauOrient.tau]]
  | FrontierMode.mode08 =>
      [[TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.tau]]
  | FrontierMode.mode09 =>
      [ [TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau]
      ]
  | FrontierMode.mode10 => [[TauOrient.tau, TauOrient.tau]]
  | FrontierMode.mode11 => [[TauOrient.mirror, TauOrient.tau]]
  | FrontierMode.mode12 =>
      [ [TauOrient.tau, TauOrient.mirror, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.tau]
      , [TauOrient.tau, TauOrient.tau, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau]
      ]
  | FrontierMode.mode13 =>
      [ [TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.mirror]
      ]
  | FrontierMode.mode14 =>
      [ [TauOrient.tau, TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.tau, TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.mirror]
      ]
  | FrontierMode.mode15 =>
      [ [TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.tau]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.mirror, TauOrient.tau]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.tau, TauOrient.tau]
      ]
  | FrontierMode.mode16 => [[TauOrient.mirror]]
  | FrontierMode.mode17 =>
      [ [TauOrient.mirror, TauOrient.mirror, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.mirror, TauOrient.mirror, TauOrient.tau, TauOrient.mirror]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.mirror, TauOrient.mirror]
      , [TauOrient.mirror, TauOrient.tau, TauOrient.tau, TauOrient.mirror]
      ]
  | FrontierMode.mode18 => [[TauOrient.tau, TauOrient.mirror]]
  | FrontierMode.mode19 =>
      [[TauOrient.tau, TauOrient.mirror, TauOrient.tau, TauOrient.mirror]]

def modeWitnessWord : FrontierMode → List TauOrient
  | mode => (representativeWords mode).headD []

def representativeWordsSoundCheck : Bool :=
  allModes.all (fun mode =>
    (representativeWords mode).all (fun word => wordMode word == some mode))

def representativeWordsNonemptyCheck : Bool :=
  allModes.all (fun mode =>
    (representativeWords mode).any (fun word => wordMode word == some mode))

def representativeCoverageCheck : Bool :=
  representativeWordsSoundCheck && representativeWordsNonemptyCheck

theorem representativeWordsSoundCheck_ok :
    representativeWordsSoundCheck = true := by
  rfl

theorem representativeCoverageCheck_ok :
    representativeCoverageCheck = true := by
  rfl

theorem modeWitnessWord_sound (mode : FrontierMode) :
    wordMode (modeWitnessWord mode) = some mode := by
  cases mode <;> rfl

def knownProfileWordHashes : List (List TauOrient × String) :=
  allModes.flatMap (fun mode =>
    (representativeWords mode).map (fun word =>
      (word, FrontierMode.profileHash mode)))

def knownProfileWordHashCheck : Bool :=
  knownProfileWordHashes.length == 42
  && knownProfileWordHashes.all (fun item =>
    modeOfProfileHash item.2 == wordMode item.1)

theorem knownProfileWordHashCheck_ok :
    knownProfileWordHashCheck = true := by
  rfl

def knownTransitionHashes : List (String × TauOrient × String) :=
  [ ("1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346", TauOrient.mirror, "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63")
  , ("1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346", TauOrient.tau, "9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956")
  , ("1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b", TauOrient.mirror, "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63")
  , ("1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b", TauOrient.tau, "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0")
  , ("31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0", TauOrient.mirror, "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324")
  , ("31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0", TauOrient.tau, "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4")
  , ("45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9", TauOrient.mirror, "fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d")
  , ("45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9", TauOrient.tau, "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc")
  , ("61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490", TauOrient.mirror, "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324")
  , ("61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490", TauOrient.tau, "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b")
  , ("6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324", TauOrient.mirror, "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63")
  , ("6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324", TauOrient.tau, "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0")
  , ("9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220", TauOrient.mirror, "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31")
  , ("9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220", TauOrient.tau, "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc")
  , ("9b07069297dcf0a45b1ad3c8f672c21d2f1ecfb3889b6a6f01b16423fda14344", TauOrient.mirror, "ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d")
  , ("9b07069297dcf0a45b1ad3c8f672c21d2f1ecfb3889b6a6f01b16423fda14344", TauOrient.tau, "abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc")
  , ("9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956", TauOrient.mirror, "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324")
  , ("9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956", TauOrient.tau, "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4")
  , ("9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff", TauOrient.mirror, "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31")
  , ("9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff", TauOrient.tau, "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc")
  , ("abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc", TauOrient.mirror, "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220")
  , ("abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc", TauOrient.tau, "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff")
  , ("c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931", TauOrient.mirror, "1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346")
  , ("c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931", TauOrient.tau, "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b")
  , ("c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc", TauOrient.mirror, "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd")
  , ("c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc", TauOrient.tau, "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff")
  , ("c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd", TauOrient.mirror, "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31")
  , ("c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd", TauOrient.tau, "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc")
  , ("ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31", TauOrient.mirror, "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd")
  , ("ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31", TauOrient.tau, "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff")
  , ("de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4", TauOrient.mirror, "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63")
  , ("de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4", TauOrient.tau, "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0")
  , ("ebccdaf35fc51d2e09dc7a18bca456d4ba509e742adeb9ed6bbbadf41e92f33d", TauOrient.mirror, "61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490")
  , ("ebccdaf35fc51d2e09dc7a18bca456d4ba509e742adeb9ed6bbbadf41e92f33d", TauOrient.tau, "c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931")
  , ("ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63", TauOrient.mirror, "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324")
  , ("ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63", TauOrient.tau, "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4")
  , ("ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d", TauOrient.mirror, "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220")
  , ("ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d", TauOrient.tau, "45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9")
  , ("fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d", TauOrient.mirror, "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd")
  , ("fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d", TauOrient.tau, "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff")
  ]

def transitionHashDirectCheck
    (sourceHash : String) (sourceMode : FrontierMode)
    (orient : TauOrient) (targetHash : String) (targetMode : FrontierMode) :
    Bool :=
  (modeOfProfileHash sourceHash == some sourceMode)
  && (modeOfProfileHash targetHash == some targetMode)
  && (step sourceMode orient == targetMode)

def knownTransitionHashDirectChecks : List Bool :=
  [ transitionHashDirectCheck "1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346" FrontierMode.mode00 TauOrient.mirror "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" FrontierMode.mode17
  , transitionHashDirectCheck "1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346" FrontierMode.mode00 TauOrient.tau "9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956" FrontierMode.mode08
  , transitionHashDirectCheck "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b" FrontierMode.mode01 TauOrient.mirror "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" FrontierMode.mode17
  , transitionHashDirectCheck "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b" FrontierMode.mode01 TauOrient.tau "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0" FrontierMode.mode02
  , transitionHashDirectCheck "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0" FrontierMode.mode02 TauOrient.mirror "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" FrontierMode.mode05
  , transitionHashDirectCheck "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0" FrontierMode.mode02 TauOrient.tau "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4" FrontierMode.mode15
  , transitionHashDirectCheck "45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9" FrontierMode.mode03 TauOrient.mirror "fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d" FrontierMode.mode19
  , transitionHashDirectCheck "45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9" FrontierMode.mode03 TauOrient.tau "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" FrontierMode.mode12
  , transitionHashDirectCheck "61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490" FrontierMode.mode04 TauOrient.mirror "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" FrontierMode.mode05
  , transitionHashDirectCheck "61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490" FrontierMode.mode04 TauOrient.tau "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b" FrontierMode.mode01
  , transitionHashDirectCheck "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" FrontierMode.mode05 TauOrient.mirror "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" FrontierMode.mode17
  , transitionHashDirectCheck "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" FrontierMode.mode05 TauOrient.tau "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0" FrontierMode.mode02
  , transitionHashDirectCheck "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220" FrontierMode.mode06 TauOrient.mirror "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31" FrontierMode.mode14
  , transitionHashDirectCheck "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220" FrontierMode.mode06 TauOrient.tau "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" FrontierMode.mode12
  , transitionHashDirectCheck "9b07069297dcf0a45b1ad3c8f672c21d2f1ecfb3889b6a6f01b16423fda14344" FrontierMode.mode07 TauOrient.mirror "ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d" FrontierMode.mode18
  , transitionHashDirectCheck "9b07069297dcf0a45b1ad3c8f672c21d2f1ecfb3889b6a6f01b16423fda14344" FrontierMode.mode07 TauOrient.tau "abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc" FrontierMode.mode10
  , transitionHashDirectCheck "9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956" FrontierMode.mode08 TauOrient.mirror "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" FrontierMode.mode05
  , transitionHashDirectCheck "9dbefb6157618a01e724f2961504a6e733d54d751aabd27889bdada506804956" FrontierMode.mode08 TauOrient.tau "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4" FrontierMode.mode15
  , transitionHashDirectCheck "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" FrontierMode.mode09 TauOrient.mirror "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31" FrontierMode.mode14
  , transitionHashDirectCheck "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" FrontierMode.mode09 TauOrient.tau "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" FrontierMode.mode12
  , transitionHashDirectCheck "abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc" FrontierMode.mode10 TauOrient.mirror "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220" FrontierMode.mode06
  , transitionHashDirectCheck "abaad60a99389d64a9b52c6be4496f49a1b8a434e8ca4cb930ee2deae4807abc" FrontierMode.mode10 TauOrient.tau "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" FrontierMode.mode09
  , transitionHashDirectCheck "c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931" FrontierMode.mode11 TauOrient.mirror "1ac3ffcefef0e72e6d7ca7523253d47490558ba9755a3581090ca0e3031cc346" FrontierMode.mode00
  , transitionHashDirectCheck "c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931" FrontierMode.mode11 TauOrient.tau "1c719d44a7c47a9a05f69ffdae83288968d51a47c878745afd834202333e731b" FrontierMode.mode01
  , transitionHashDirectCheck "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" FrontierMode.mode12 TauOrient.mirror "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd" FrontierMode.mode13
  , transitionHashDirectCheck "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" FrontierMode.mode12 TauOrient.tau "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" FrontierMode.mode09
  , transitionHashDirectCheck "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd" FrontierMode.mode13 TauOrient.mirror "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31" FrontierMode.mode14
  , transitionHashDirectCheck "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd" FrontierMode.mode13 TauOrient.tau "c797b98adfe7aca087274c6ff03bdc56449078fcfdc54bec9dc489cf1fa8ebfc" FrontierMode.mode12
  , transitionHashDirectCheck "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31" FrontierMode.mode14 TauOrient.mirror "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd" FrontierMode.mode13
  , transitionHashDirectCheck "ce046c768ea8a600c35974f97b38652149e7175eff70cc28f506e09dedacfb31" FrontierMode.mode14 TauOrient.tau "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" FrontierMode.mode09
  , transitionHashDirectCheck "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4" FrontierMode.mode15 TauOrient.mirror "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" FrontierMode.mode17
  , transitionHashDirectCheck "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4" FrontierMode.mode15 TauOrient.tau "31e0381fca6cfb76796fbe9ee63f3447b730f8e5a830e3202e1ae637e8eb8da0" FrontierMode.mode02
  , transitionHashDirectCheck "ebccdaf35fc51d2e09dc7a18bca456d4ba509e742adeb9ed6bbbadf41e92f33d" FrontierMode.mode16 TauOrient.mirror "61c5d954e3ad806b77ddfab87032a265a0fc404a55cced477b0e2fda3ebe4490" FrontierMode.mode04
  , transitionHashDirectCheck "ebccdaf35fc51d2e09dc7a18bca456d4ba509e742adeb9ed6bbbadf41e92f33d" FrontierMode.mode16 TauOrient.tau "c55532ec739ee43c3df016eeb3a1ac488e4e478df70ecb870cc886cfd49d7931" FrontierMode.mode11
  , transitionHashDirectCheck "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" FrontierMode.mode17 TauOrient.mirror "6c0a99870e3f8ab863f3e90fefc269e0d0703d6ec0dbf434a770553deb986324" FrontierMode.mode05
  , transitionHashDirectCheck "ed111eea780e730925edcf7921b337533c1d4954665d245b6676de3ca57c2a63" FrontierMode.mode17 TauOrient.tau "de80ad0377b63e410b0feceafbebdac0e6bb5b9133f37ebb35e9ea7eeefd91e4" FrontierMode.mode15
  , transitionHashDirectCheck "ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d" FrontierMode.mode18 TauOrient.mirror "9318012cf65c57b5cb19668eb29c73030d6bbfd2eb80a6feead9c9d110f5a220" FrontierMode.mode06
  , transitionHashDirectCheck "ee430509815c4119619027004ad84897eedaa41083f0943d0bbe5cf897c3318d" FrontierMode.mode18 TauOrient.tau "45249313d2951ddb58981181ef744871e6447e025a3a24b89dcb4655b8f8aac9" FrontierMode.mode03
  , transitionHashDirectCheck "fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d" FrontierMode.mode19 TauOrient.mirror "c9150749204c8e0fd1c5f72fa01ed17a3c9e8ab2d801c61013ab1772569daacd" FrontierMode.mode13
  , transitionHashDirectCheck "fee62bcd43e995b828267ffbc5884830c37ba523e054f90e234c3462e21f797d" FrontierMode.mode19 TauOrient.tau "9faaa7e69dd874b8116994c980dff5b7dd32a797e27eebf1be40a198901cd3ff" FrontierMode.mode09
  ]

def knownTransitionHashCheck : Bool :=
  knownTransitionHashes.length == 40
  && knownTransitionHashDirectChecks.length == 40
  && knownTransitionHashDirectChecks.all id

theorem knownTransitionHashCheck_ok :
    knownTransitionHashCheck = true := by
  rfl

def modeInTable (mode : FrontierMode) : Bool :=
  allModes.contains mode

theorem initialMode_inTable (orient : TauOrient) :
    modeInTable (initialMode orient) = true := by
  cases orient <;> rfl

theorem step_inTable (mode : FrontierMode) (orient : TauOrient) :
    modeInTable (step mode orient) = true := by
  cases mode <;> cases orient <;> rfl

theorem foldl_step_inTable
    (rest : List TauOrient) {mode : FrontierMode}
    (hmode : modeInTable mode = true) :
    modeInTable (rest.foldl step mode) = true := by
  induction rest generalizing mode with
  | nil =>
      exact hmode
  | cons orient rest ih =>
      simpa [List.foldl] using ih (step_inTable mode orient)

theorem wordMode_inTable
    {word : List TauOrient} {mode : FrontierMode}
    (hmode : wordMode word = some mode) :
    modeInTable mode = true := by
  cases word with
  | nil =>
      change none = some mode at hmode
      contradiction
  | cons orient rest =>
      change some (rest.foldl step (initialMode orient)) = some mode at hmode
      injection hmode with hfold
      rw [← hfold]
      exact foldl_step_inTable rest (initialMode_inTable orient)

theorem foldl_step_induction
    {P : FrontierMode → Prop}
    (hStep : ∀ mode orient, P mode → P (step mode orient))
    (rest : List TauOrient) {mode : FrontierMode}
    (hmode : P mode) :
    P (rest.foldl step mode) := by
  induction rest generalizing mode with
  | nil =>
      exact hmode
  | cons orient rest ih =>
      exact ih (hStep mode orient hmode)

theorem wordMode_induction
    {P : FrontierMode → Prop}
    (hInitial : ∀ orient, P (initialMode orient))
    (hStep : ∀ mode orient, P mode → P (step mode orient))
    {word : List TauOrient} {mode : FrontierMode}
    (hmode : wordMode word = some mode) :
    P mode := by
  cases word with
  | nil =>
      change none = some mode at hmode
      contradiction
  | cons orient rest =>
      change some (rest.foldl step (initialMode orient)) = some mode at hmode
      injection hmode with hfold
      rw [← hfold]
      exact foldl_step_induction hStep rest (hInitial orient)

theorem foldl_step_bool_induction
    (good : FrontierMode → Bool)
    (hStep : ∀ mode orient, good mode = true → good (step mode orient) = true)
    (rest : List TauOrient) {mode : FrontierMode}
    (hmode : good mode = true) :
    good (rest.foldl step mode) = true :=
  foldl_step_induction hStep rest hmode

theorem wordMode_bool_induction
    (good : FrontierMode → Bool)
    (hInitial : ∀ orient, good (initialMode orient) = true)
    (hStep : ∀ mode orient, good mode = true → good (step mode orient) = true)
    {word : List TauOrient} {mode : FrontierMode}
    (hmode : wordMode word = some mode) :
    good mode = true :=
  wordMode_induction hInitial hStep hmode

end GoertzelLemma818FrontierMode

end Mettapedia.GraphTheory.FourColor
