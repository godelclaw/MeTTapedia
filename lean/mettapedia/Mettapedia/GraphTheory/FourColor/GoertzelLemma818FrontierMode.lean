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

end GoertzelLemma818FrontierMode

end Mettapedia.GraphTheory.FourColor
