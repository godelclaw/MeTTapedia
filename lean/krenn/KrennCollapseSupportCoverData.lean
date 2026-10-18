import KrennCollapseSupportCover

/-! Compatibility interface for the reduced C6 Boolean support cover.

The split modules own the numeric strata and their kernel-checked certificates.
This interface preserves the original records, predicates and theorem statements
without repeating the case proofs.
-/

namespace Krenn.CollapseSupportCoverData

structure Stratum where
  zero : BitVec 26
  component : Nat
deriving DecidableEq, Repr

structure ActiveCover where
  active : BitVec 14
  strata : List Stratum
deriving DecidableEq, Repr

def subsetMask (support pattern : BitVec 26) : Bool :=
  (support &&& pattern) == support

def relationSupports : Fin 14 → BitVec 26 × BitVec 26
  | 0 => (BitVec.ofNat 26 129, BitVec.ofNat 26 36)
  | 1 => (BitVec.ofNat 26 8193, BitVec.ofNat 26 8519680)
  | 2 => (BitVec.ofNat 26 258, BitVec.ofNat 26 72)
  | 3 => (BitVec.ofNat 26 8388610, BitVec.ofNat 26 4194308)
  | 4 => (BitVec.ofNat 26 33554440, BitVec.ofNat 26 16777232)
  | 5 => (BitVec.ofNat 26 1048592, BitVec.ofNat 26 2097408)
  | 6 => (BitVec.ofNat 26 8224, BitVec.ofNat 26 528384)
  | 7 => (BitVec.ofNat 26 524352, BitVec.ofNat 26 262272)
  | 8 => (BitVec.ofNat 26 66048, BitVec.ofNat 26 18432)
  | 9 => (BitVec.ofNat 26 262656, BitVec.ofNat 26 1048576)
  | 10 => (BitVec.ofNat 26 132096, BitVec.ofNat 26 36864)
  | 11 => (BitVec.ofNat 26 2098176, BitVec.ofNat 26 2048)
  | 12 => (BitVec.ofNat 26 4210688, BitVec.ofNat 26 16777216)
  | 13 => (BitVec.ofNat 26 33587200, BitVec.ofNat 26 65536)

def relationActive (pattern : BitVec 26) (index : Fin 14) : Bool :=
  subsetMask (relationSupports index).1 pattern

def feasible (pattern : BitVec 26) : Bool :=
  (relationActive pattern 0 == subsetMask (relationSupports 0).2 pattern) &&
    (relationActive pattern 1 == subsetMask (relationSupports 1).2 pattern) &&
    (relationActive pattern 2 == subsetMask (relationSupports 2).2 pattern) &&
    (relationActive pattern 3 == subsetMask (relationSupports 3).2 pattern) &&
    (relationActive pattern 4 == subsetMask (relationSupports 4).2 pattern) &&
    (relationActive pattern 5 == subsetMask (relationSupports 5).2 pattern) &&
    (relationActive pattern 6 == subsetMask (relationSupports 6).2 pattern) &&
    (relationActive pattern 7 == subsetMask (relationSupports 7).2 pattern) &&
    (relationActive pattern 8 == subsetMask (relationSupports 8).2 pattern) &&
    (relationActive pattern 9 == subsetMask (relationSupports 9).2 pattern) &&
    (relationActive pattern 10 == subsetMask (relationSupports 10).2 pattern) &&
    (relationActive pattern 11 == subsetMask (relationSupports 11).2 pattern) &&
    (relationActive pattern 12 == subsetMask (relationSupports 12).2 pattern) &&
    (relationActive pattern 13 == subsetMask (relationSupports 13).2 pattern)

private def stratumOfBase (stratum : CollapseSupportCover.Stratum) : Stratum :=
  { zero := stratum.zero, component := stratum.component }

private def coverOfBase (cover : CollapseSupportCover.ActiveCover) : ActiveCover :=
  { active := cover.active, strata := cover.strata.map stratumOfBase }

def cover0 : ActiveCover := coverOfBase CollapseSupportCover.Mask000.data

def cover1 : ActiveCover := coverOfBase CollapseSupportCover.Mask001.data

def cover2 : ActiveCover := coverOfBase CollapseSupportCover.Mask002.data

def cover3 : ActiveCover := coverOfBase CollapseSupportCover.Mask003.data

def cover4 : ActiveCover := coverOfBase CollapseSupportCover.Mask004.data

def cover5 : ActiveCover := coverOfBase CollapseSupportCover.Mask005.data

def cover6 : ActiveCover := coverOfBase CollapseSupportCover.Mask006.data

def cover7 : ActiveCover := coverOfBase CollapseSupportCover.Mask007.data

def cover8 : ActiveCover := coverOfBase CollapseSupportCover.Mask008.data

def cover9 : ActiveCover := coverOfBase CollapseSupportCover.Mask009.data

def cover10 : ActiveCover := coverOfBase CollapseSupportCover.Mask010.data

def cover11 : ActiveCover := coverOfBase CollapseSupportCover.Mask011.data

def cover12 : ActiveCover := coverOfBase CollapseSupportCover.Mask012.data

def cover13 : ActiveCover := coverOfBase CollapseSupportCover.Mask013.data

def cover14 : ActiveCover := coverOfBase CollapseSupportCover.Mask014.data

def cover15 : ActiveCover := coverOfBase CollapseSupportCover.Mask015.data

def cover16 : ActiveCover := coverOfBase CollapseSupportCover.Mask016.data

def cover17 : ActiveCover := coverOfBase CollapseSupportCover.Mask017.data

def cover18 : ActiveCover := coverOfBase CollapseSupportCover.Mask018.data

def cover19 : ActiveCover := coverOfBase CollapseSupportCover.Mask019.data

def cover20 : ActiveCover := coverOfBase CollapseSupportCover.Mask020.data

def cover21 : ActiveCover := coverOfBase CollapseSupportCover.Mask021.data

def cover22 : ActiveCover := coverOfBase CollapseSupportCover.Mask022.data

def cover23 : ActiveCover := coverOfBase CollapseSupportCover.Mask023.data

def cover24 : ActiveCover := coverOfBase CollapseSupportCover.Mask024.data

def cover25 : ActiveCover := coverOfBase CollapseSupportCover.Mask025.data

def cover26 : ActiveCover := coverOfBase CollapseSupportCover.Mask026.data

def cover27 : ActiveCover := coverOfBase CollapseSupportCover.Mask027.data

def cover28 : ActiveCover := coverOfBase CollapseSupportCover.Mask028.data

def cover29 : ActiveCover := coverOfBase CollapseSupportCover.Mask029.data

def cover30 : ActiveCover := coverOfBase CollapseSupportCover.Mask030.data

def cover31 : ActiveCover := coverOfBase CollapseSupportCover.Mask031.data

def cover32 : ActiveCover := coverOfBase CollapseSupportCover.Mask032.data

def cover33 : ActiveCover := coverOfBase CollapseSupportCover.Mask033.data

def cover34 : ActiveCover := coverOfBase CollapseSupportCover.Mask034.data

def cover35 : ActiveCover := coverOfBase CollapseSupportCover.Mask035.data

def cover36 : ActiveCover := coverOfBase CollapseSupportCover.Mask036.data

def cover37 : ActiveCover := coverOfBase CollapseSupportCover.Mask037.data

def cover38 : ActiveCover := coverOfBase CollapseSupportCover.Mask038.data

def cover39 : ActiveCover := coverOfBase CollapseSupportCover.Mask039.data

def cover40 : ActiveCover := coverOfBase CollapseSupportCover.Mask040.data

def cover41 : ActiveCover := coverOfBase CollapseSupportCover.Mask041.data

def cover42 : ActiveCover := coverOfBase CollapseSupportCover.Mask042.data

def cover43 : ActiveCover := coverOfBase CollapseSupportCover.Mask043.data

def cover44 : ActiveCover := coverOfBase CollapseSupportCover.Mask044.data

def cover45 : ActiveCover := coverOfBase CollapseSupportCover.Mask045.data

def cover46 : ActiveCover := coverOfBase CollapseSupportCover.Mask046.data

def cover47 : ActiveCover := coverOfBase CollapseSupportCover.Mask047.data

def cover48 : ActiveCover := coverOfBase CollapseSupportCover.Mask048.data

def cover49 : ActiveCover := coverOfBase CollapseSupportCover.Mask049.data

def cover50 : ActiveCover := coverOfBase CollapseSupportCover.Mask050.data

def cover51 : ActiveCover := coverOfBase CollapseSupportCover.Mask051.data

def cover52 : ActiveCover := coverOfBase CollapseSupportCover.Mask052.data

def cover53 : ActiveCover := coverOfBase CollapseSupportCover.Mask053.data

def cover54 : ActiveCover := coverOfBase CollapseSupportCover.Mask054.data

def cover55 : ActiveCover := coverOfBase CollapseSupportCover.Mask055.data

def cover56 : ActiveCover := coverOfBase CollapseSupportCover.Mask056.data

def cover57 : ActiveCover := coverOfBase CollapseSupportCover.Mask057.data

def cover58 : ActiveCover := coverOfBase CollapseSupportCover.Mask058.data

def cover59 : ActiveCover := coverOfBase CollapseSupportCover.Mask059.data

def cover60 : ActiveCover := coverOfBase CollapseSupportCover.Mask060.data

def cover61 : ActiveCover := coverOfBase CollapseSupportCover.Mask061.data

def cover62 : ActiveCover := coverOfBase CollapseSupportCover.Mask062.data

def cover63 : ActiveCover := coverOfBase CollapseSupportCover.Mask063.data

def cover64 : ActiveCover := coverOfBase CollapseSupportCover.Mask064.data

def cover65 : ActiveCover := coverOfBase CollapseSupportCover.Mask065.data

def cover66 : ActiveCover := coverOfBase CollapseSupportCover.Mask066.data

def cover67 : ActiveCover := coverOfBase CollapseSupportCover.Mask067.data

def cover68 : ActiveCover := coverOfBase CollapseSupportCover.Mask068.data

def cover69 : ActiveCover := coverOfBase CollapseSupportCover.Mask069.data

def cover70 : ActiveCover := coverOfBase CollapseSupportCover.Mask070.data

def cover71 : ActiveCover := coverOfBase CollapseSupportCover.Mask071.data

def cover72 : ActiveCover := coverOfBase CollapseSupportCover.Mask072.data

def cover73 : ActiveCover := coverOfBase CollapseSupportCover.Mask073.data

def cover74 : ActiveCover := coverOfBase CollapseSupportCover.Mask074.data

def cover75 : ActiveCover := coverOfBase CollapseSupportCover.Mask075.data

def cover76 : ActiveCover := coverOfBase CollapseSupportCover.Mask076.data

def cover77 : ActiveCover := coverOfBase CollapseSupportCover.Mask077.data

def cover78 : ActiveCover := coverOfBase CollapseSupportCover.Mask078.data

def cover79 : ActiveCover := coverOfBase CollapseSupportCover.Mask079.data

def cover80 : ActiveCover := coverOfBase CollapseSupportCover.Mask080.data

def cover81 : ActiveCover := coverOfBase CollapseSupportCover.Mask081.data

def cover82 : ActiveCover := coverOfBase CollapseSupportCover.Mask082.data

def cover83 : ActiveCover := coverOfBase CollapseSupportCover.Mask083.data

def cover84 : ActiveCover := coverOfBase CollapseSupportCover.Mask084.data

def cover85 : ActiveCover := coverOfBase CollapseSupportCover.Mask085.data

def cover86 : ActiveCover := coverOfBase CollapseSupportCover.Mask086.data

def cover87 : ActiveCover := coverOfBase CollapseSupportCover.Mask087.data

def cover88 : ActiveCover := coverOfBase CollapseSupportCover.Mask088.data

def cover89 : ActiveCover := coverOfBase CollapseSupportCover.Mask089.data

def cover90 : ActiveCover := coverOfBase CollapseSupportCover.Mask090.data

def cover91 : ActiveCover := coverOfBase CollapseSupportCover.Mask091.data

def cover92 : ActiveCover := coverOfBase CollapseSupportCover.Mask092.data

def cover93 : ActiveCover := coverOfBase CollapseSupportCover.Mask093.data

def cover94 : ActiveCover := coverOfBase CollapseSupportCover.Mask094.data

def cover95 : ActiveCover := coverOfBase CollapseSupportCover.Mask095.data

def cover96 : ActiveCover := coverOfBase CollapseSupportCover.Mask096.data

def cover97 : ActiveCover := coverOfBase CollapseSupportCover.Mask097.data

def cover98 : ActiveCover := coverOfBase CollapseSupportCover.Mask098.data

def cover99 : ActiveCover := coverOfBase CollapseSupportCover.Mask099.data

def cover100 : ActiveCover := coverOfBase CollapseSupportCover.Mask100.data

def cover101 : ActiveCover := coverOfBase CollapseSupportCover.Mask101.data

def cover102 : ActiveCover := coverOfBase CollapseSupportCover.Mask102.data

def cover103 : ActiveCover := coverOfBase CollapseSupportCover.Mask103.data

def cover104 : ActiveCover := coverOfBase CollapseSupportCover.Mask104.data

def cover105 : ActiveCover := coverOfBase CollapseSupportCover.Mask105.data

def cover106 : ActiveCover := coverOfBase CollapseSupportCover.Mask106.data

def cover107 : ActiveCover := coverOfBase CollapseSupportCover.Mask107.data

def cover108 : ActiveCover := coverOfBase CollapseSupportCover.Mask108.data

def cover109 : ActiveCover := coverOfBase CollapseSupportCover.Mask109.data

def cover110 : ActiveCover := coverOfBase CollapseSupportCover.Mask110.data

def cover111 : ActiveCover := coverOfBase CollapseSupportCover.Mask111.data

def cover112 : ActiveCover := coverOfBase CollapseSupportCover.Mask112.data

def cover113 : ActiveCover := coverOfBase CollapseSupportCover.Mask113.data

def cover114 : ActiveCover := coverOfBase CollapseSupportCover.Mask114.data

def cover115 : ActiveCover := coverOfBase CollapseSupportCover.Mask115.data

def cover116 : ActiveCover := coverOfBase CollapseSupportCover.Mask116.data

def cover117 : ActiveCover := coverOfBase CollapseSupportCover.Mask117.data

def cover118 : ActiveCover := coverOfBase CollapseSupportCover.Mask118.data

def cover119 : ActiveCover := coverOfBase CollapseSupportCover.Mask119.data

def cover120 : ActiveCover := coverOfBase CollapseSupportCover.Mask120.data

def cover121 : ActiveCover := coverOfBase CollapseSupportCover.Mask121.data

def cover122 : ActiveCover := coverOfBase CollapseSupportCover.Mask122.data

def cover123 : ActiveCover := coverOfBase CollapseSupportCover.Mask123.data

def cover124 : ActiveCover := coverOfBase CollapseSupportCover.Mask124.data

def cover125 : ActiveCover := coverOfBase CollapseSupportCover.Mask125.data

def cover126 : ActiveCover := coverOfBase CollapseSupportCover.Mask126.data

def cover127 : ActiveCover := coverOfBase CollapseSupportCover.Mask127.data

def cover128 : ActiveCover := coverOfBase CollapseSupportCover.Mask128.data

def cover129 : ActiveCover := coverOfBase CollapseSupportCover.Mask129.data

def cover130 : ActiveCover := coverOfBase CollapseSupportCover.Mask130.data

def cover131 : ActiveCover := coverOfBase CollapseSupportCover.Mask131.data

def cover132 : ActiveCover := coverOfBase CollapseSupportCover.Mask132.data

def cover133 : ActiveCover := coverOfBase CollapseSupportCover.Mask133.data

def cover134 : ActiveCover := coverOfBase CollapseSupportCover.Mask134.data

def cover135 : ActiveCover := coverOfBase CollapseSupportCover.Mask135.data

def cover136 : ActiveCover := coverOfBase CollapseSupportCover.Mask136.data

def cover137 : ActiveCover := coverOfBase CollapseSupportCover.Mask137.data

def cover138 : ActiveCover := coverOfBase CollapseSupportCover.Mask138.data

def cover139 : ActiveCover := coverOfBase CollapseSupportCover.Mask139.data

def cover140 : ActiveCover := coverOfBase CollapseSupportCover.Mask140.data

def cover141 : ActiveCover := coverOfBase CollapseSupportCover.Mask141.data

def cover142 : ActiveCover := coverOfBase CollapseSupportCover.Mask142.data

def cover143 : ActiveCover := coverOfBase CollapseSupportCover.Mask143.data

def cover144 : ActiveCover := coverOfBase CollapseSupportCover.Mask144.data

def cover145 : ActiveCover := coverOfBase CollapseSupportCover.Mask145.data

def cover146 : ActiveCover := coverOfBase CollapseSupportCover.Mask146.data

def cover147 : ActiveCover := coverOfBase CollapseSupportCover.Mask147.data

def cover148 : ActiveCover := coverOfBase CollapseSupportCover.Mask148.data

def cover149 : ActiveCover := coverOfBase CollapseSupportCover.Mask149.data

def cover150 : ActiveCover := coverOfBase CollapseSupportCover.Mask150.data

def cover151 : ActiveCover := coverOfBase CollapseSupportCover.Mask151.data

def cover152 : ActiveCover := coverOfBase CollapseSupportCover.Mask152.data

def cover153 : ActiveCover := coverOfBase CollapseSupportCover.Mask153.data

def cover154 : ActiveCover := coverOfBase CollapseSupportCover.Mask154.data

def cover155 : ActiveCover := coverOfBase CollapseSupportCover.Mask155.data

def cover156 : ActiveCover := coverOfBase CollapseSupportCover.Mask156.data

def cover157 : ActiveCover := coverOfBase CollapseSupportCover.Mask157.data

def cover158 : ActiveCover := coverOfBase CollapseSupportCover.Mask158.data

def cover159 : ActiveCover := coverOfBase CollapseSupportCover.Mask159.data

def cover160 : ActiveCover := coverOfBase CollapseSupportCover.Mask160.data

def cover161 : ActiveCover := coverOfBase CollapseSupportCover.Mask161.data

def cover162 : ActiveCover := coverOfBase CollapseSupportCover.Mask162.data

def cover163 : ActiveCover := coverOfBase CollapseSupportCover.Mask163.data

def cover164 : ActiveCover := coverOfBase CollapseSupportCover.Mask164.data

def cover165 : ActiveCover := coverOfBase CollapseSupportCover.Mask165.data

def cover166 : ActiveCover := coverOfBase CollapseSupportCover.Mask166.data

def cover167 : ActiveCover := coverOfBase CollapseSupportCover.Mask167.data

def cover168 : ActiveCover := coverOfBase CollapseSupportCover.Mask168.data

def cover169 : ActiveCover := coverOfBase CollapseSupportCover.Mask169.data

def cover170 : ActiveCover := coverOfBase CollapseSupportCover.Mask170.data

def cover171 : ActiveCover := coverOfBase CollapseSupportCover.Mask171.data

def cover172 : ActiveCover := coverOfBase CollapseSupportCover.Mask172.data

def cover173 : ActiveCover := coverOfBase CollapseSupportCover.Mask173.data

def cover174 : ActiveCover := coverOfBase CollapseSupportCover.Mask174.data

def cover175 : ActiveCover := coverOfBase CollapseSupportCover.Mask175.data

def cover176 : ActiveCover := coverOfBase CollapseSupportCover.Mask176.data

def cover177 : ActiveCover := coverOfBase CollapseSupportCover.Mask177.data

def cover178 : ActiveCover := coverOfBase CollapseSupportCover.Mask178.data

def cover179 : ActiveCover := coverOfBase CollapseSupportCover.Mask179.data

def cover180 : ActiveCover := coverOfBase CollapseSupportCover.Mask180.data

def cover181 : ActiveCover := coverOfBase CollapseSupportCover.Mask181.data

def cover182 : ActiveCover := coverOfBase CollapseSupportCover.Mask182.data

def cover183 : ActiveCover := coverOfBase CollapseSupportCover.Mask183.data

def cover184 : ActiveCover := coverOfBase CollapseSupportCover.Mask184.data

def cover185 : ActiveCover := coverOfBase CollapseSupportCover.Mask185.data

def cover186 : ActiveCover := coverOfBase CollapseSupportCover.Mask186.data

def cover187 : ActiveCover := coverOfBase CollapseSupportCover.Mask187.data

def cover188 : ActiveCover := coverOfBase CollapseSupportCover.Mask188.data

def cover189 : ActiveCover := coverOfBase CollapseSupportCover.Mask189.data

def cover190 : ActiveCover := coverOfBase CollapseSupportCover.Mask190.data

def cover191 : ActiveCover := coverOfBase CollapseSupportCover.Mask191.data

def cover192 : ActiveCover := coverOfBase CollapseSupportCover.Mask192.data

def cover193 : ActiveCover := coverOfBase CollapseSupportCover.Mask193.data

def cover194 : ActiveCover := coverOfBase CollapseSupportCover.Mask194.data

def cover195 : ActiveCover := coverOfBase CollapseSupportCover.Mask195.data

def cover196 : ActiveCover := coverOfBase CollapseSupportCover.Mask196.data

def cover197 : ActiveCover := coverOfBase CollapseSupportCover.Mask197.data

def cover198 : ActiveCover := coverOfBase CollapseSupportCover.Mask198.data

def cover199 : ActiveCover := coverOfBase CollapseSupportCover.Mask199.data

def cover200 : ActiveCover := coverOfBase CollapseSupportCover.Mask200.data

def cover201 : ActiveCover := coverOfBase CollapseSupportCover.Mask201.data

def cover202 : ActiveCover := coverOfBase CollapseSupportCover.Mask202.data

def cover203 : ActiveCover := coverOfBase CollapseSupportCover.Mask203.data

def cover204 : ActiveCover := coverOfBase CollapseSupportCover.Mask204.data

def cover205 : ActiveCover := coverOfBase CollapseSupportCover.Mask205.data

def cover206 : ActiveCover := coverOfBase CollapseSupportCover.Mask206.data

def cover207 : ActiveCover := coverOfBase CollapseSupportCover.Mask207.data

def cover208 : ActiveCover := coverOfBase CollapseSupportCover.Mask208.data

def cover209 : ActiveCover := coverOfBase CollapseSupportCover.Mask209.data

def cover210 : ActiveCover := coverOfBase CollapseSupportCover.Mask210.data

def cover211 : ActiveCover := coverOfBase CollapseSupportCover.Mask211.data

def cover212 : ActiveCover := coverOfBase CollapseSupportCover.Mask212.data

def cover213 : ActiveCover := coverOfBase CollapseSupportCover.Mask213.data

def cover214 : ActiveCover := coverOfBase CollapseSupportCover.Mask214.data

def cover215 : ActiveCover := coverOfBase CollapseSupportCover.Mask215.data

def cover216 : ActiveCover := coverOfBase CollapseSupportCover.Mask216.data

def cover217 : ActiveCover := coverOfBase CollapseSupportCover.Mask217.data

def cover218 : ActiveCover := coverOfBase CollapseSupportCover.Mask218.data

def cover219 : ActiveCover := coverOfBase CollapseSupportCover.Mask219.data

def cover220 : ActiveCover := coverOfBase CollapseSupportCover.Mask220.data

def cover221 : ActiveCover := coverOfBase CollapseSupportCover.Mask221.data

def cover222 : ActiveCover := coverOfBase CollapseSupportCover.Mask222.data

def cover223 : ActiveCover := coverOfBase CollapseSupportCover.Mask223.data

def cover224 : ActiveCover := coverOfBase CollapseSupportCover.Mask224.data

def cover225 : ActiveCover := coverOfBase CollapseSupportCover.Mask225.data

def cover226 : ActiveCover := coverOfBase CollapseSupportCover.Mask226.data

def cover227 : ActiveCover := coverOfBase CollapseSupportCover.Mask227.data

def cover228 : ActiveCover := coverOfBase CollapseSupportCover.Mask228.data

def cover229 : ActiveCover := coverOfBase CollapseSupportCover.Mask229.data

def cover230 : ActiveCover := coverOfBase CollapseSupportCover.Mask230.data

def cover231 : ActiveCover := coverOfBase CollapseSupportCover.Mask231.data

def cover232 : ActiveCover := coverOfBase CollapseSupportCover.Mask232.data

def cover233 : ActiveCover := coverOfBase CollapseSupportCover.Mask233.data

def cover234 : ActiveCover := coverOfBase CollapseSupportCover.Mask234.data

def cover235 : ActiveCover := coverOfBase CollapseSupportCover.Mask235.data

def cover236 : ActiveCover := coverOfBase CollapseSupportCover.Mask236.data

def cover237 : ActiveCover := coverOfBase CollapseSupportCover.Mask237.data

def cover238 : ActiveCover := coverOfBase CollapseSupportCover.Mask238.data

def cover239 : ActiveCover := coverOfBase CollapseSupportCover.Mask239.data

def cover240 : ActiveCover := coverOfBase CollapseSupportCover.Mask240.data

def cover241 : ActiveCover := coverOfBase CollapseSupportCover.Mask241.data

def cover242 : ActiveCover := coverOfBase CollapseSupportCover.Mask242.data

def cover243 : ActiveCover := coverOfBase CollapseSupportCover.Mask243.data

def cover244 : ActiveCover := coverOfBase CollapseSupportCover.Mask244.data

def cover245 : ActiveCover := coverOfBase CollapseSupportCover.Mask245.data

def cover246 : ActiveCover := coverOfBase CollapseSupportCover.Mask246.data

def cover247 : ActiveCover := coverOfBase CollapseSupportCover.Mask247.data

def cover248 : ActiveCover := coverOfBase CollapseSupportCover.Mask248.data

def cover249 : ActiveCover := coverOfBase CollapseSupportCover.Mask249.data

def cover250 : ActiveCover := coverOfBase CollapseSupportCover.Mask250.data

def cover251 : ActiveCover := coverOfBase CollapseSupportCover.Mask251.data

def cover252 : ActiveCover := coverOfBase CollapseSupportCover.Mask252.data

def cover253 : ActiveCover := coverOfBase CollapseSupportCover.Mask253.data

def cover254 : ActiveCover := coverOfBase CollapseSupportCover.Mask254.data

def cover255 : ActiveCover := coverOfBase CollapseSupportCover.Mask255.data

def cover256 : ActiveCover := coverOfBase CollapseSupportCover.Mask256.data

def cover257 : ActiveCover := coverOfBase CollapseSupportCover.Mask257.data

def cover258 : ActiveCover := coverOfBase CollapseSupportCover.Mask258.data

def cover259 : ActiveCover := coverOfBase CollapseSupportCover.Mask259.data

def cover260 : ActiveCover := coverOfBase CollapseSupportCover.Mask260.data

def cover261 : ActiveCover := coverOfBase CollapseSupportCover.Mask261.data

def cover262 : ActiveCover := coverOfBase CollapseSupportCover.Mask262.data

def cover263 : ActiveCover := coverOfBase CollapseSupportCover.Mask263.data

def cover264 : ActiveCover := coverOfBase CollapseSupportCover.Mask264.data

def cover265 : ActiveCover := coverOfBase CollapseSupportCover.Mask265.data

def cover266 : ActiveCover := coverOfBase CollapseSupportCover.Mask266.data

def cover267 : ActiveCover := coverOfBase CollapseSupportCover.Mask267.data

def cover268 : ActiveCover := coverOfBase CollapseSupportCover.Mask268.data

def cover269 : ActiveCover := coverOfBase CollapseSupportCover.Mask269.data

def cover270 : ActiveCover := coverOfBase CollapseSupportCover.Mask270.data

def cover271 : ActiveCover := coverOfBase CollapseSupportCover.Mask271.data

def cover272 : ActiveCover := coverOfBase CollapseSupportCover.Mask272.data

def cover273 : ActiveCover := coverOfBase CollapseSupportCover.Mask273.data

def cover274 : ActiveCover := coverOfBase CollapseSupportCover.Mask274.data

def cover275 : ActiveCover := coverOfBase CollapseSupportCover.Mask275.data

def cover276 : ActiveCover := coverOfBase CollapseSupportCover.Mask276.data

def cover277 : ActiveCover := coverOfBase CollapseSupportCover.Mask277.data

def cover278 : ActiveCover := coverOfBase CollapseSupportCover.Mask278.data

def cover279 : ActiveCover := coverOfBase CollapseSupportCover.Mask279.data

def cover280 : ActiveCover := coverOfBase CollapseSupportCover.Mask280.data

def cover281 : ActiveCover := coverOfBase CollapseSupportCover.Mask281.data

def cover282 : ActiveCover := coverOfBase CollapseSupportCover.Mask282.data

def cover283 : ActiveCover := coverOfBase CollapseSupportCover.Mask283.data

def cover284 : ActiveCover := coverOfBase CollapseSupportCover.Mask284.data

def cover285 : ActiveCover := coverOfBase CollapseSupportCover.Mask285.data

def cover286 : ActiveCover := coverOfBase CollapseSupportCover.Mask286.data

def cover287 : ActiveCover := coverOfBase CollapseSupportCover.Mask287.data

def cover288 : ActiveCover := coverOfBase CollapseSupportCover.Mask288.data

def cover289 : ActiveCover := coverOfBase CollapseSupportCover.Mask289.data

def cover290 : ActiveCover := coverOfBase CollapseSupportCover.Mask290.data

def cover291 : ActiveCover := coverOfBase CollapseSupportCover.Mask291.data

def cover292 : ActiveCover := coverOfBase CollapseSupportCover.Mask292.data

def cover293 : ActiveCover := coverOfBase CollapseSupportCover.Mask293.data

def cover294 : ActiveCover := coverOfBase CollapseSupportCover.Mask294.data

def cover295 : ActiveCover := coverOfBase CollapseSupportCover.Mask295.data

def cover296 : ActiveCover := coverOfBase CollapseSupportCover.Mask296.data

def cover297 : ActiveCover := coverOfBase CollapseSupportCover.Mask297.data

def cover298 : ActiveCover := coverOfBase CollapseSupportCover.Mask298.data

def cover299 : ActiveCover := coverOfBase CollapseSupportCover.Mask299.data

def cover300 : ActiveCover := coverOfBase CollapseSupportCover.Mask300.data

def cover301 : ActiveCover := coverOfBase CollapseSupportCover.Mask301.data

def cover302 : ActiveCover := coverOfBase CollapseSupportCover.Mask302.data

def cover303 : ActiveCover := coverOfBase CollapseSupportCover.Mask303.data

def cover304 : ActiveCover := coverOfBase CollapseSupportCover.Mask304.data

def cover305 : ActiveCover := coverOfBase CollapseSupportCover.Mask305.data

def cover306 : ActiveCover := coverOfBase CollapseSupportCover.Mask306.data

def cover307 : ActiveCover := coverOfBase CollapseSupportCover.Mask307.data

def cover308 : ActiveCover := coverOfBase CollapseSupportCover.Mask308.data

def cover309 : ActiveCover := coverOfBase CollapseSupportCover.Mask309.data

def cover310 : ActiveCover := coverOfBase CollapseSupportCover.Mask310.data

def cover311 : ActiveCover := coverOfBase CollapseSupportCover.Mask311.data

def cover312 : ActiveCover := coverOfBase CollapseSupportCover.Mask312.data

def cover313 : ActiveCover := coverOfBase CollapseSupportCover.Mask313.data

def cover314 : ActiveCover := coverOfBase CollapseSupportCover.Mask314.data

def cover315 : ActiveCover := coverOfBase CollapseSupportCover.Mask315.data

def cover316 : ActiveCover := coverOfBase CollapseSupportCover.Mask316.data

def cover317 : ActiveCover := coverOfBase CollapseSupportCover.Mask317.data

def cover318 : ActiveCover := coverOfBase CollapseSupportCover.Mask318.data

def cover319 : ActiveCover := coverOfBase CollapseSupportCover.Mask319.data

def cover320 : ActiveCover := coverOfBase CollapseSupportCover.Mask320.data

def cover321 : ActiveCover := coverOfBase CollapseSupportCover.Mask321.data

def cover322 : ActiveCover := coverOfBase CollapseSupportCover.Mask322.data

def cover323 : ActiveCover := coverOfBase CollapseSupportCover.Mask323.data

def cover324 : ActiveCover := coverOfBase CollapseSupportCover.Mask324.data

def cover325 : ActiveCover := coverOfBase CollapseSupportCover.Mask325.data

def cover326 : ActiveCover := coverOfBase CollapseSupportCover.Mask326.data

def cover327 : ActiveCover := coverOfBase CollapseSupportCover.Mask327.data

def cover328 : ActiveCover := coverOfBase CollapseSupportCover.Mask328.data

def cover329 : ActiveCover := coverOfBase CollapseSupportCover.Mask329.data

def cover330 : ActiveCover := coverOfBase CollapseSupportCover.Mask330.data

def cover331 : ActiveCover := coverOfBase CollapseSupportCover.Mask331.data

def cover332 : ActiveCover := coverOfBase CollapseSupportCover.Mask332.data

def cover333 : ActiveCover := coverOfBase CollapseSupportCover.Mask333.data

def cover334 : ActiveCover := coverOfBase CollapseSupportCover.Mask334.data

def cover335 : ActiveCover := coverOfBase CollapseSupportCover.Mask335.data

def cover336 : ActiveCover := coverOfBase CollapseSupportCover.Mask336.data

def cover337 : ActiveCover := coverOfBase CollapseSupportCover.Mask337.data

def cover338 : ActiveCover := coverOfBase CollapseSupportCover.Mask338.data

def cover339 : ActiveCover := coverOfBase CollapseSupportCover.Mask339.data

def cover340 : ActiveCover := coverOfBase CollapseSupportCover.Mask340.data

def cover341 : ActiveCover := coverOfBase CollapseSupportCover.Mask341.data

def cover342 : ActiveCover := coverOfBase CollapseSupportCover.Mask342.data

def cover343 : ActiveCover := coverOfBase CollapseSupportCover.Mask343.data

def cover344 : ActiveCover := coverOfBase CollapseSupportCover.Mask344.data

def cover345 : ActiveCover := coverOfBase CollapseSupportCover.Mask345.data

def cover346 : ActiveCover := coverOfBase CollapseSupportCover.Mask346.data

def cover347 : ActiveCover := coverOfBase CollapseSupportCover.Mask347.data

def cover348 : ActiveCover := coverOfBase CollapseSupportCover.Mask348.data

def cover349 : ActiveCover := coverOfBase CollapseSupportCover.Mask349.data

def cover350 : ActiveCover := coverOfBase CollapseSupportCover.Mask350.data

def cover351 : ActiveCover := coverOfBase CollapseSupportCover.Mask351.data

def cover352 : ActiveCover := coverOfBase CollapseSupportCover.Mask352.data

def cover353 : ActiveCover := coverOfBase CollapseSupportCover.Mask353.data

def cover354 : ActiveCover := coverOfBase CollapseSupportCover.Mask354.data

def cover355 : ActiveCover := coverOfBase CollapseSupportCover.Mask355.data

def cover356 : ActiveCover := coverOfBase CollapseSupportCover.Mask356.data

def cover357 : ActiveCover := coverOfBase CollapseSupportCover.Mask357.data

def cover358 : ActiveCover := coverOfBase CollapseSupportCover.Mask358.data

def cover359 : ActiveCover := coverOfBase CollapseSupportCover.Mask359.data

def cover360 : ActiveCover := coverOfBase CollapseSupportCover.Mask360.data

def cover361 : ActiveCover := coverOfBase CollapseSupportCover.Mask361.data

def cover362 : ActiveCover := coverOfBase CollapseSupportCover.Mask362.data

def cover363 : ActiveCover := coverOfBase CollapseSupportCover.Mask363.data

def cover364 : ActiveCover := coverOfBase CollapseSupportCover.Mask364.data

def cover365 : ActiveCover := coverOfBase CollapseSupportCover.Mask365.data

def cover366 : ActiveCover := coverOfBase CollapseSupportCover.Mask366.data

def cover367 : ActiveCover := coverOfBase CollapseSupportCover.Mask367.data

def cover368 : ActiveCover := coverOfBase CollapseSupportCover.Mask368.data

def cover369 : ActiveCover := coverOfBase CollapseSupportCover.Mask369.data

def cover370 : ActiveCover := coverOfBase CollapseSupportCover.Mask370.data

def cover371 : ActiveCover := coverOfBase CollapseSupportCover.Mask371.data

def cover372 : ActiveCover := coverOfBase CollapseSupportCover.Mask372.data

def cover373 : ActiveCover := coverOfBase CollapseSupportCover.Mask373.data

def cover374 : ActiveCover := coverOfBase CollapseSupportCover.Mask374.data

def cover375 : ActiveCover := coverOfBase CollapseSupportCover.Mask375.data

def cover376 : ActiveCover := coverOfBase CollapseSupportCover.Mask376.data

def cover377 : ActiveCover := coverOfBase CollapseSupportCover.Mask377.data

def cover378 : ActiveCover := coverOfBase CollapseSupportCover.Mask378.data

def cover379 : ActiveCover := coverOfBase CollapseSupportCover.Mask379.data

def cover380 : ActiveCover := coverOfBase CollapseSupportCover.Mask380.data

def cover381 : ActiveCover := coverOfBase CollapseSupportCover.Mask381.data

def cover382 : ActiveCover := coverOfBase CollapseSupportCover.Mask382.data

def cover383 : ActiveCover := coverOfBase CollapseSupportCover.Mask383.data

def cover384 : ActiveCover := coverOfBase CollapseSupportCover.Mask384.data

def cover385 : ActiveCover := coverOfBase CollapseSupportCover.Mask385.data

def cover386 : ActiveCover := coverOfBase CollapseSupportCover.Mask386.data

def cover387 : ActiveCover := coverOfBase CollapseSupportCover.Mask387.data

def cover388 : ActiveCover := coverOfBase CollapseSupportCover.Mask388.data

def cover389 : ActiveCover := coverOfBase CollapseSupportCover.Mask389.data

def cover390 : ActiveCover := coverOfBase CollapseSupportCover.Mask390.data

def cover391 : ActiveCover := coverOfBase CollapseSupportCover.Mask391.data

def cover392 : ActiveCover := coverOfBase CollapseSupportCover.Mask392.data

def cover393 : ActiveCover := coverOfBase CollapseSupportCover.Mask393.data

def cover394 : ActiveCover := coverOfBase CollapseSupportCover.Mask394.data

set_option maxRecDepth 1000000 in
def covers : List ActiveCover := [
  cover0, cover1, cover2, cover3, cover4, cover5, cover6, cover7, cover8, cover9, cover10, cover11, cover12, cover13, cover14, cover15, cover16, cover17, cover18, cover19, cover20, cover21, cover22, cover23, cover24, cover25, cover26, cover27, cover28, cover29, cover30, cover31, cover32, cover33, cover34, cover35, cover36, cover37, cover38, cover39, cover40, cover41, cover42, cover43, cover44, cover45, cover46, cover47, cover48, cover49, cover50, cover51, cover52, cover53, cover54, cover55, cover56, cover57, cover58, cover59, cover60, cover61, cover62, cover63, cover64, cover65, cover66, cover67, cover68, cover69, cover70, cover71, cover72, cover73, cover74, cover75, cover76, cover77, cover78, cover79, cover80, cover81, cover82, cover83, cover84, cover85, cover86, cover87, cover88, cover89, cover90, cover91, cover92, cover93, cover94, cover95, cover96, cover97, cover98, cover99, cover100, cover101, cover102, cover103, cover104, cover105, cover106, cover107, cover108, cover109, cover110, cover111, cover112, cover113, cover114, cover115, cover116, cover117, cover118, cover119, cover120, cover121, cover122, cover123, cover124, cover125, cover126, cover127, cover128, cover129, cover130, cover131, cover132, cover133, cover134, cover135, cover136, cover137, cover138, cover139, cover140, cover141, cover142, cover143, cover144, cover145, cover146, cover147, cover148, cover149, cover150, cover151, cover152, cover153, cover154, cover155, cover156, cover157, cover158, cover159, cover160, cover161, cover162, cover163, cover164, cover165, cover166, cover167, cover168, cover169, cover170, cover171, cover172, cover173, cover174, cover175, cover176, cover177, cover178, cover179, cover180, cover181, cover182, cover183, cover184, cover185, cover186, cover187, cover188, cover189, cover190, cover191, cover192, cover193, cover194, cover195, cover196, cover197, cover198, cover199, cover200, cover201, cover202, cover203, cover204, cover205, cover206, cover207, cover208, cover209, cover210, cover211, cover212, cover213, cover214, cover215, cover216, cover217, cover218, cover219, cover220, cover221, cover222, cover223, cover224, cover225, cover226, cover227, cover228, cover229, cover230, cover231, cover232, cover233, cover234, cover235, cover236, cover237, cover238, cover239, cover240, cover241, cover242, cover243, cover244, cover245, cover246, cover247, cover248, cover249, cover250, cover251, cover252, cover253, cover254, cover255, cover256, cover257, cover258, cover259, cover260, cover261, cover262, cover263, cover264, cover265, cover266, cover267, cover268, cover269, cover270, cover271, cover272, cover273, cover274, cover275, cover276, cover277, cover278, cover279, cover280, cover281, cover282, cover283, cover284, cover285, cover286, cover287, cover288, cover289, cover290, cover291, cover292, cover293, cover294, cover295, cover296, cover297, cover298, cover299, cover300, cover301, cover302, cover303, cover304, cover305, cover306, cover307, cover308, cover309, cover310, cover311, cover312, cover313, cover314, cover315, cover316, cover317, cover318, cover319, cover320, cover321, cover322, cover323, cover324, cover325, cover326, cover327, cover328, cover329, cover330, cover331, cover332, cover333, cover334, cover335, cover336, cover337, cover338, cover339, cover340, cover341, cover342, cover343, cover344, cover345, cover346, cover347, cover348, cover349, cover350, cover351, cover352, cover353, cover354, cover355, cover356, cover357, cover358, cover359, cover360, cover361, cover362, cover363, cover364, cover365, cover366, cover367, cover368, cover369, cover370, cover371, cover372, cover373, cover374, cover375, cover376, cover377, cover378, cover379, cover380, cover381, cover382, cover383, cover384, cover385, cover386, cover387, cover388, cover389, cover390, cover391, cover392, cover393, cover394
]

def activeMatches (active : BitVec 14) (pattern : BitVec 26) : Bool :=
  (active.getLsbD 0 == relationActive pattern 0) &&
    (active.getLsbD 1 == relationActive pattern 1) &&
    (active.getLsbD 2 == relationActive pattern 2) &&
    (active.getLsbD 3 == relationActive pattern 3) &&
    (active.getLsbD 4 == relationActive pattern 4) &&
    (active.getLsbD 5 == relationActive pattern 5) &&
    (active.getLsbD 6 == relationActive pattern 6) &&
    (active.getLsbD 7 == relationActive pattern 7) &&
    (active.getLsbD 8 == relationActive pattern 8) &&
    (active.getLsbD 9 == relationActive pattern 9) &&
    (active.getLsbD 10 == relationActive pattern 10) &&
    (active.getLsbD 11 == relationActive pattern 11) &&
    (active.getLsbD 12 == relationActive pattern 12) &&
    (active.getLsbD 13 == relationActive pattern 13)

def stratumMatches (stratum : Stratum) (pattern : BitVec 26) : Bool :=
  (stratum.zero &&& pattern) == 0

def activeCoverMatches (cover : ActiveCover) (pattern : BitVec 26) : Bool :=
  activeMatches cover.active pattern &&
    cover.strata.any fun stratum => stratumMatches stratum pattern

def covered (pattern : BitVec 26) : Bool :=
  covers.any fun cover => activeCoverMatches cover pattern

def relationLeftActiveProp (pattern : Fin 26 → Prop) : Fin 14 → Prop
  | 0 => pattern 0 ∧ pattern 7
  | 1 => pattern 0 ∧ pattern 13
  | 2 => pattern 1 ∧ pattern 8
  | 3 => pattern 1 ∧ pattern 23
  | 4 => pattern 3 ∧ pattern 25
  | 5 => pattern 4 ∧ pattern 20
  | 6 => pattern 5 ∧ pattern 13
  | 7 => pattern 6 ∧ pattern 19
  | 8 => pattern 9 ∧ pattern 16
  | 9 => pattern 9 ∧ pattern 18
  | 10 => pattern 10 ∧ pattern 17
  | 11 => pattern 10 ∧ pattern 21
  | 12 => pattern 14 ∧ pattern 22
  | 13 => pattern 15 ∧ pattern 25

def relationRightActiveProp (pattern : Fin 26 → Prop) : Fin 14 → Prop
  | 0 => pattern 2 ∧ pattern 5
  | 1 => pattern 17 ∧ pattern 23
  | 2 => pattern 3 ∧ pattern 6
  | 3 => pattern 2 ∧ pattern 22
  | 4 => pattern 4 ∧ pattern 24
  | 5 => pattern 8 ∧ pattern 21
  | 6 => pattern 12 ∧ pattern 19
  | 7 => pattern 7 ∧ pattern 18
  | 8 => pattern 11 ∧ pattern 14
  | 9 => pattern 20
  | 10 => pattern 12 ∧ pattern 15
  | 11 => pattern 11
  | 12 => pattern 24
  | 13 => pattern 16

def feasibleProp (pattern : Fin 26 → Prop) : Prop :=
  (relationLeftActiveProp pattern 0 ↔ relationRightActiveProp pattern 0) ∧
    (relationLeftActiveProp pattern 1 ↔ relationRightActiveProp pattern 1) ∧
    (relationLeftActiveProp pattern 2 ↔ relationRightActiveProp pattern 2) ∧
    (relationLeftActiveProp pattern 3 ↔ relationRightActiveProp pattern 3) ∧
    (relationLeftActiveProp pattern 4 ↔ relationRightActiveProp pattern 4) ∧
    (relationLeftActiveProp pattern 5 ↔ relationRightActiveProp pattern 5) ∧
    (relationLeftActiveProp pattern 6 ↔ relationRightActiveProp pattern 6) ∧
    (relationLeftActiveProp pattern 7 ↔ relationRightActiveProp pattern 7) ∧
    (relationLeftActiveProp pattern 8 ↔ relationRightActiveProp pattern 8) ∧
    (relationLeftActiveProp pattern 9 ↔ relationRightActiveProp pattern 9) ∧
    (relationLeftActiveProp pattern 10 ↔ relationRightActiveProp pattern 10) ∧
    (relationLeftActiveProp pattern 11 ↔ relationRightActiveProp pattern 11) ∧
    (relationLeftActiveProp pattern 12 ↔ relationRightActiveProp pattern 12) ∧
    (relationLeftActiveProp pattern 13 ↔ relationRightActiveProp pattern 13)

def activeMatchesProp (active : BitVec 14) (pattern : Fin 26 → Prop) : Prop :=
  (active.getLsbD 0 = true ↔ relationLeftActiveProp pattern 0) ∧
    (active.getLsbD 1 = true ↔ relationLeftActiveProp pattern 1) ∧
    (active.getLsbD 2 = true ↔ relationLeftActiveProp pattern 2) ∧
    (active.getLsbD 3 = true ↔ relationLeftActiveProp pattern 3) ∧
    (active.getLsbD 4 = true ↔ relationLeftActiveProp pattern 4) ∧
    (active.getLsbD 5 = true ↔ relationLeftActiveProp pattern 5) ∧
    (active.getLsbD 6 = true ↔ relationLeftActiveProp pattern 6) ∧
    (active.getLsbD 7 = true ↔ relationLeftActiveProp pattern 7) ∧
    (active.getLsbD 8 = true ↔ relationLeftActiveProp pattern 8) ∧
    (active.getLsbD 9 = true ↔ relationLeftActiveProp pattern 9) ∧
    (active.getLsbD 10 = true ↔ relationLeftActiveProp pattern 10) ∧
    (active.getLsbD 11 = true ↔ relationLeftActiveProp pattern 11) ∧
    (active.getLsbD 12 = true ↔ relationLeftActiveProp pattern 12) ∧
    (active.getLsbD 13 = true ↔ relationLeftActiveProp pattern 13)

def zeroMatchesProp (zero : BitVec 26) (pattern : Fin 26 → Prop) : Prop :=
  (zero.getLsbD 0 = true → ¬ pattern 0) ∧
    (zero.getLsbD 1 = true → ¬ pattern 1) ∧
    (zero.getLsbD 2 = true → ¬ pattern 2) ∧
    (zero.getLsbD 3 = true → ¬ pattern 3) ∧
    (zero.getLsbD 4 = true → ¬ pattern 4) ∧
    (zero.getLsbD 5 = true → ¬ pattern 5) ∧
    (zero.getLsbD 6 = true → ¬ pattern 6) ∧
    (zero.getLsbD 7 = true → ¬ pattern 7) ∧
    (zero.getLsbD 8 = true → ¬ pattern 8) ∧
    (zero.getLsbD 9 = true → ¬ pattern 9) ∧
    (zero.getLsbD 10 = true → ¬ pattern 10) ∧
    (zero.getLsbD 11 = true → ¬ pattern 11) ∧
    (zero.getLsbD 12 = true → ¬ pattern 12) ∧
    (zero.getLsbD 13 = true → ¬ pattern 13) ∧
    (zero.getLsbD 14 = true → ¬ pattern 14) ∧
    (zero.getLsbD 15 = true → ¬ pattern 15) ∧
    (zero.getLsbD 16 = true → ¬ pattern 16) ∧
    (zero.getLsbD 17 = true → ¬ pattern 17) ∧
    (zero.getLsbD 18 = true → ¬ pattern 18) ∧
    (zero.getLsbD 19 = true → ¬ pattern 19) ∧
    (zero.getLsbD 20 = true → ¬ pattern 20) ∧
    (zero.getLsbD 21 = true → ¬ pattern 21) ∧
    (zero.getLsbD 22 = true → ¬ pattern 22) ∧
    (zero.getLsbD 23 = true → ¬ pattern 23) ∧
    (zero.getLsbD 24 = true → ¬ pattern 24) ∧
    (zero.getLsbD 25 = true → ¬ pattern 25)

def activeCoverMatchesProp (cover : ActiveCover) (pattern : Fin 26 → Prop) : Prop :=
  activeMatchesProp cover.active pattern ∧
    ∃ stratum ∈ cover.strata, zeroMatchesProp stratum.zero pattern

private theorem zeroCoveredOfBase
    (certificate : CollapseSupportCover.CertifiedCover)
    (pattern : Fin 26 → Prop) (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp (coverOfBase certificate.data).active pattern) :
    ∃ stratum ∈ (coverOfBase certificate.data).strata,
      zeroMatchesProp stratum.zero pattern := by
  obtain ⟨stratum, member, zero⟩ :=
    certificate.zeroCovered pattern feasiblePattern activePattern
  exact ⟨stratumOfBase stratum, List.mem_map.mpr ⟨stratum, member, rfl⟩, zero⟩

theorem cover0ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover0.active pattern) :
    ∃ stratum ∈ cover0.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified0 pattern feasiblePattern activePattern

theorem cover1ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover1.active pattern) :
    ∃ stratum ∈ cover1.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified1 pattern feasiblePattern activePattern

theorem cover2ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover2.active pattern) :
    ∃ stratum ∈ cover2.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified2 pattern feasiblePattern activePattern

theorem cover3ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover3.active pattern) :
    ∃ stratum ∈ cover3.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified3 pattern feasiblePattern activePattern

theorem cover4ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover4.active pattern) :
    ∃ stratum ∈ cover4.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified4 pattern feasiblePattern activePattern

theorem cover5ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover5.active pattern) :
    ∃ stratum ∈ cover5.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified5 pattern feasiblePattern activePattern

theorem cover6ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover6.active pattern) :
    ∃ stratum ∈ cover6.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified6 pattern feasiblePattern activePattern

theorem cover7ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover7.active pattern) :
    ∃ stratum ∈ cover7.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified7 pattern feasiblePattern activePattern

theorem cover8ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover8.active pattern) :
    ∃ stratum ∈ cover8.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified8 pattern feasiblePattern activePattern

theorem cover9ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover9.active pattern) :
    ∃ stratum ∈ cover9.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified9 pattern feasiblePattern activePattern

theorem cover10ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover10.active pattern) :
    ∃ stratum ∈ cover10.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified10 pattern feasiblePattern activePattern

theorem cover11ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover11.active pattern) :
    ∃ stratum ∈ cover11.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified11 pattern feasiblePattern activePattern

theorem cover12ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover12.active pattern) :
    ∃ stratum ∈ cover12.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified12 pattern feasiblePattern activePattern

theorem cover13ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover13.active pattern) :
    ∃ stratum ∈ cover13.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified13 pattern feasiblePattern activePattern

theorem cover14ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover14.active pattern) :
    ∃ stratum ∈ cover14.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified14 pattern feasiblePattern activePattern

theorem cover15ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover15.active pattern) :
    ∃ stratum ∈ cover15.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified15 pattern feasiblePattern activePattern

theorem cover16ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover16.active pattern) :
    ∃ stratum ∈ cover16.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified16 pattern feasiblePattern activePattern

theorem cover17ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover17.active pattern) :
    ∃ stratum ∈ cover17.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified17 pattern feasiblePattern activePattern

theorem cover18ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover18.active pattern) :
    ∃ stratum ∈ cover18.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified18 pattern feasiblePattern activePattern

theorem cover19ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover19.active pattern) :
    ∃ stratum ∈ cover19.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified19 pattern feasiblePattern activePattern

theorem cover20ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover20.active pattern) :
    ∃ stratum ∈ cover20.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified20 pattern feasiblePattern activePattern

theorem cover21ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover21.active pattern) :
    ∃ stratum ∈ cover21.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified21 pattern feasiblePattern activePattern

theorem cover22ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover22.active pattern) :
    ∃ stratum ∈ cover22.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified22 pattern feasiblePattern activePattern

theorem cover23ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover23.active pattern) :
    ∃ stratum ∈ cover23.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified23 pattern feasiblePattern activePattern

theorem cover24ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover24.active pattern) :
    ∃ stratum ∈ cover24.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified24 pattern feasiblePattern activePattern

theorem cover25ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover25.active pattern) :
    ∃ stratum ∈ cover25.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified25 pattern feasiblePattern activePattern

theorem cover26ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover26.active pattern) :
    ∃ stratum ∈ cover26.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified26 pattern feasiblePattern activePattern

theorem cover27ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover27.active pattern) :
    ∃ stratum ∈ cover27.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified27 pattern feasiblePattern activePattern

theorem cover28ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover28.active pattern) :
    ∃ stratum ∈ cover28.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified28 pattern feasiblePattern activePattern

theorem cover29ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover29.active pattern) :
    ∃ stratum ∈ cover29.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified29 pattern feasiblePattern activePattern

theorem cover30ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover30.active pattern) :
    ∃ stratum ∈ cover30.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified30 pattern feasiblePattern activePattern

theorem cover31ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover31.active pattern) :
    ∃ stratum ∈ cover31.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified31 pattern feasiblePattern activePattern

theorem cover32ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover32.active pattern) :
    ∃ stratum ∈ cover32.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified32 pattern feasiblePattern activePattern

theorem cover33ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover33.active pattern) :
    ∃ stratum ∈ cover33.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified33 pattern feasiblePattern activePattern

theorem cover34ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover34.active pattern) :
    ∃ stratum ∈ cover34.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified34 pattern feasiblePattern activePattern

theorem cover35ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover35.active pattern) :
    ∃ stratum ∈ cover35.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified35 pattern feasiblePattern activePattern

theorem cover36ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover36.active pattern) :
    ∃ stratum ∈ cover36.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified36 pattern feasiblePattern activePattern

theorem cover37ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover37.active pattern) :
    ∃ stratum ∈ cover37.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified37 pattern feasiblePattern activePattern

theorem cover38ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover38.active pattern) :
    ∃ stratum ∈ cover38.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified38 pattern feasiblePattern activePattern

theorem cover39ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover39.active pattern) :
    ∃ stratum ∈ cover39.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified39 pattern feasiblePattern activePattern

theorem cover40ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover40.active pattern) :
    ∃ stratum ∈ cover40.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified40 pattern feasiblePattern activePattern

theorem cover41ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover41.active pattern) :
    ∃ stratum ∈ cover41.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified41 pattern feasiblePattern activePattern

theorem cover42ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover42.active pattern) :
    ∃ stratum ∈ cover42.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified42 pattern feasiblePattern activePattern

theorem cover43ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover43.active pattern) :
    ∃ stratum ∈ cover43.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified43 pattern feasiblePattern activePattern

theorem cover44ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover44.active pattern) :
    ∃ stratum ∈ cover44.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified44 pattern feasiblePattern activePattern

theorem cover45ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover45.active pattern) :
    ∃ stratum ∈ cover45.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified45 pattern feasiblePattern activePattern

theorem cover46ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover46.active pattern) :
    ∃ stratum ∈ cover46.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified46 pattern feasiblePattern activePattern

theorem cover47ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover47.active pattern) :
    ∃ stratum ∈ cover47.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified47 pattern feasiblePattern activePattern

theorem cover48ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover48.active pattern) :
    ∃ stratum ∈ cover48.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified48 pattern feasiblePattern activePattern

theorem cover49ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover49.active pattern) :
    ∃ stratum ∈ cover49.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified49 pattern feasiblePattern activePattern

theorem cover50ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover50.active pattern) :
    ∃ stratum ∈ cover50.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified50 pattern feasiblePattern activePattern

theorem cover51ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover51.active pattern) :
    ∃ stratum ∈ cover51.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified51 pattern feasiblePattern activePattern

theorem cover52ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover52.active pattern) :
    ∃ stratum ∈ cover52.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified52 pattern feasiblePattern activePattern

theorem cover53ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover53.active pattern) :
    ∃ stratum ∈ cover53.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified53 pattern feasiblePattern activePattern

theorem cover54ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover54.active pattern) :
    ∃ stratum ∈ cover54.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified54 pattern feasiblePattern activePattern

theorem cover55ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover55.active pattern) :
    ∃ stratum ∈ cover55.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified55 pattern feasiblePattern activePattern

theorem cover56ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover56.active pattern) :
    ∃ stratum ∈ cover56.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified56 pattern feasiblePattern activePattern

theorem cover57ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover57.active pattern) :
    ∃ stratum ∈ cover57.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified57 pattern feasiblePattern activePattern

theorem cover58ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover58.active pattern) :
    ∃ stratum ∈ cover58.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified58 pattern feasiblePattern activePattern

theorem cover59ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover59.active pattern) :
    ∃ stratum ∈ cover59.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified59 pattern feasiblePattern activePattern

theorem cover60ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover60.active pattern) :
    ∃ stratum ∈ cover60.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified60 pattern feasiblePattern activePattern

theorem cover61ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover61.active pattern) :
    ∃ stratum ∈ cover61.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified61 pattern feasiblePattern activePattern

theorem cover62ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover62.active pattern) :
    ∃ stratum ∈ cover62.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified62 pattern feasiblePattern activePattern

theorem cover63ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover63.active pattern) :
    ∃ stratum ∈ cover63.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified63 pattern feasiblePattern activePattern

theorem cover64ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover64.active pattern) :
    ∃ stratum ∈ cover64.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified64 pattern feasiblePattern activePattern

theorem cover65ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover65.active pattern) :
    ∃ stratum ∈ cover65.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified65 pattern feasiblePattern activePattern

theorem cover66ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover66.active pattern) :
    ∃ stratum ∈ cover66.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified66 pattern feasiblePattern activePattern

theorem cover67ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover67.active pattern) :
    ∃ stratum ∈ cover67.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified67 pattern feasiblePattern activePattern

theorem cover68ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover68.active pattern) :
    ∃ stratum ∈ cover68.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified68 pattern feasiblePattern activePattern

theorem cover69ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover69.active pattern) :
    ∃ stratum ∈ cover69.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified69 pattern feasiblePattern activePattern

theorem cover70ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover70.active pattern) :
    ∃ stratum ∈ cover70.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified70 pattern feasiblePattern activePattern

theorem cover71ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover71.active pattern) :
    ∃ stratum ∈ cover71.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified71 pattern feasiblePattern activePattern

theorem cover72ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover72.active pattern) :
    ∃ stratum ∈ cover72.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified72 pattern feasiblePattern activePattern

theorem cover73ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover73.active pattern) :
    ∃ stratum ∈ cover73.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified73 pattern feasiblePattern activePattern

theorem cover74ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover74.active pattern) :
    ∃ stratum ∈ cover74.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified74 pattern feasiblePattern activePattern

theorem cover75ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover75.active pattern) :
    ∃ stratum ∈ cover75.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified75 pattern feasiblePattern activePattern

theorem cover76ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover76.active pattern) :
    ∃ stratum ∈ cover76.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified76 pattern feasiblePattern activePattern

theorem cover77ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover77.active pattern) :
    ∃ stratum ∈ cover77.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified77 pattern feasiblePattern activePattern

theorem cover78ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover78.active pattern) :
    ∃ stratum ∈ cover78.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified78 pattern feasiblePattern activePattern

theorem cover79ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover79.active pattern) :
    ∃ stratum ∈ cover79.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified79 pattern feasiblePattern activePattern

theorem cover80ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover80.active pattern) :
    ∃ stratum ∈ cover80.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified80 pattern feasiblePattern activePattern

theorem cover81ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover81.active pattern) :
    ∃ stratum ∈ cover81.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified81 pattern feasiblePattern activePattern

theorem cover82ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover82.active pattern) :
    ∃ stratum ∈ cover82.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified82 pattern feasiblePattern activePattern

theorem cover83ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover83.active pattern) :
    ∃ stratum ∈ cover83.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified83 pattern feasiblePattern activePattern

theorem cover84ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover84.active pattern) :
    ∃ stratum ∈ cover84.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified84 pattern feasiblePattern activePattern

theorem cover85ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover85.active pattern) :
    ∃ stratum ∈ cover85.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified85 pattern feasiblePattern activePattern

theorem cover86ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover86.active pattern) :
    ∃ stratum ∈ cover86.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified86 pattern feasiblePattern activePattern

theorem cover87ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover87.active pattern) :
    ∃ stratum ∈ cover87.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified87 pattern feasiblePattern activePattern

theorem cover88ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover88.active pattern) :
    ∃ stratum ∈ cover88.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified88 pattern feasiblePattern activePattern

theorem cover89ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover89.active pattern) :
    ∃ stratum ∈ cover89.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified89 pattern feasiblePattern activePattern

theorem cover90ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover90.active pattern) :
    ∃ stratum ∈ cover90.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified90 pattern feasiblePattern activePattern

theorem cover91ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover91.active pattern) :
    ∃ stratum ∈ cover91.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified91 pattern feasiblePattern activePattern

theorem cover92ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover92.active pattern) :
    ∃ stratum ∈ cover92.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified92 pattern feasiblePattern activePattern

theorem cover93ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover93.active pattern) :
    ∃ stratum ∈ cover93.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified93 pattern feasiblePattern activePattern

theorem cover94ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover94.active pattern) :
    ∃ stratum ∈ cover94.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified94 pattern feasiblePattern activePattern

theorem cover95ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover95.active pattern) :
    ∃ stratum ∈ cover95.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified95 pattern feasiblePattern activePattern

theorem cover96ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover96.active pattern) :
    ∃ stratum ∈ cover96.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified96 pattern feasiblePattern activePattern

theorem cover97ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover97.active pattern) :
    ∃ stratum ∈ cover97.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified97 pattern feasiblePattern activePattern

theorem cover98ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover98.active pattern) :
    ∃ stratum ∈ cover98.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified98 pattern feasiblePattern activePattern

theorem cover99ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover99.active pattern) :
    ∃ stratum ∈ cover99.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified99 pattern feasiblePattern activePattern

theorem cover100ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover100.active pattern) :
    ∃ stratum ∈ cover100.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified100 pattern feasiblePattern activePattern

theorem cover101ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover101.active pattern) :
    ∃ stratum ∈ cover101.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified101 pattern feasiblePattern activePattern

theorem cover102ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover102.active pattern) :
    ∃ stratum ∈ cover102.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified102 pattern feasiblePattern activePattern

theorem cover103ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover103.active pattern) :
    ∃ stratum ∈ cover103.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified103 pattern feasiblePattern activePattern

theorem cover104ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover104.active pattern) :
    ∃ stratum ∈ cover104.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified104 pattern feasiblePattern activePattern

theorem cover105ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover105.active pattern) :
    ∃ stratum ∈ cover105.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified105 pattern feasiblePattern activePattern

theorem cover106ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover106.active pattern) :
    ∃ stratum ∈ cover106.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified106 pattern feasiblePattern activePattern

theorem cover107ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover107.active pattern) :
    ∃ stratum ∈ cover107.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified107 pattern feasiblePattern activePattern

theorem cover108ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover108.active pattern) :
    ∃ stratum ∈ cover108.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified108 pattern feasiblePattern activePattern

theorem cover109ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover109.active pattern) :
    ∃ stratum ∈ cover109.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified109 pattern feasiblePattern activePattern

theorem cover110ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover110.active pattern) :
    ∃ stratum ∈ cover110.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified110 pattern feasiblePattern activePattern

theorem cover111ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover111.active pattern) :
    ∃ stratum ∈ cover111.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified111 pattern feasiblePattern activePattern

theorem cover112ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover112.active pattern) :
    ∃ stratum ∈ cover112.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified112 pattern feasiblePattern activePattern

theorem cover113ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover113.active pattern) :
    ∃ stratum ∈ cover113.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified113 pattern feasiblePattern activePattern

theorem cover114ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover114.active pattern) :
    ∃ stratum ∈ cover114.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified114 pattern feasiblePattern activePattern

theorem cover115ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover115.active pattern) :
    ∃ stratum ∈ cover115.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified115 pattern feasiblePattern activePattern

theorem cover116ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover116.active pattern) :
    ∃ stratum ∈ cover116.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified116 pattern feasiblePattern activePattern

theorem cover117ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover117.active pattern) :
    ∃ stratum ∈ cover117.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified117 pattern feasiblePattern activePattern

theorem cover118ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover118.active pattern) :
    ∃ stratum ∈ cover118.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified118 pattern feasiblePattern activePattern

theorem cover119ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover119.active pattern) :
    ∃ stratum ∈ cover119.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified119 pattern feasiblePattern activePattern

theorem cover120ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover120.active pattern) :
    ∃ stratum ∈ cover120.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified120 pattern feasiblePattern activePattern

theorem cover121ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover121.active pattern) :
    ∃ stratum ∈ cover121.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified121 pattern feasiblePattern activePattern

theorem cover122ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover122.active pattern) :
    ∃ stratum ∈ cover122.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified122 pattern feasiblePattern activePattern

theorem cover123ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover123.active pattern) :
    ∃ stratum ∈ cover123.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified123 pattern feasiblePattern activePattern

theorem cover124ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover124.active pattern) :
    ∃ stratum ∈ cover124.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified124 pattern feasiblePattern activePattern

theorem cover125ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover125.active pattern) :
    ∃ stratum ∈ cover125.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified125 pattern feasiblePattern activePattern

theorem cover126ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover126.active pattern) :
    ∃ stratum ∈ cover126.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified126 pattern feasiblePattern activePattern

theorem cover127ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover127.active pattern) :
    ∃ stratum ∈ cover127.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified127 pattern feasiblePattern activePattern

theorem cover128ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover128.active pattern) :
    ∃ stratum ∈ cover128.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified128 pattern feasiblePattern activePattern

theorem cover129ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover129.active pattern) :
    ∃ stratum ∈ cover129.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified129 pattern feasiblePattern activePattern

theorem cover130ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover130.active pattern) :
    ∃ stratum ∈ cover130.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified130 pattern feasiblePattern activePattern

theorem cover131ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover131.active pattern) :
    ∃ stratum ∈ cover131.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified131 pattern feasiblePattern activePattern

theorem cover132ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover132.active pattern) :
    ∃ stratum ∈ cover132.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified132 pattern feasiblePattern activePattern

theorem cover133ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover133.active pattern) :
    ∃ stratum ∈ cover133.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified133 pattern feasiblePattern activePattern

theorem cover134ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover134.active pattern) :
    ∃ stratum ∈ cover134.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified134 pattern feasiblePattern activePattern

theorem cover135ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover135.active pattern) :
    ∃ stratum ∈ cover135.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified135 pattern feasiblePattern activePattern

theorem cover136ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover136.active pattern) :
    ∃ stratum ∈ cover136.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified136 pattern feasiblePattern activePattern

theorem cover137ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover137.active pattern) :
    ∃ stratum ∈ cover137.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified137 pattern feasiblePattern activePattern

theorem cover138ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover138.active pattern) :
    ∃ stratum ∈ cover138.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified138 pattern feasiblePattern activePattern

theorem cover139ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover139.active pattern) :
    ∃ stratum ∈ cover139.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified139 pattern feasiblePattern activePattern

theorem cover140ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover140.active pattern) :
    ∃ stratum ∈ cover140.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified140 pattern feasiblePattern activePattern

theorem cover141ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover141.active pattern) :
    ∃ stratum ∈ cover141.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified141 pattern feasiblePattern activePattern

theorem cover142ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover142.active pattern) :
    ∃ stratum ∈ cover142.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified142 pattern feasiblePattern activePattern

theorem cover143ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover143.active pattern) :
    ∃ stratum ∈ cover143.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified143 pattern feasiblePattern activePattern

theorem cover144ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover144.active pattern) :
    ∃ stratum ∈ cover144.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified144 pattern feasiblePattern activePattern

theorem cover145ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover145.active pattern) :
    ∃ stratum ∈ cover145.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified145 pattern feasiblePattern activePattern

theorem cover146ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover146.active pattern) :
    ∃ stratum ∈ cover146.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified146 pattern feasiblePattern activePattern

theorem cover147ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover147.active pattern) :
    ∃ stratum ∈ cover147.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified147 pattern feasiblePattern activePattern

theorem cover148ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover148.active pattern) :
    ∃ stratum ∈ cover148.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified148 pattern feasiblePattern activePattern

theorem cover149ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover149.active pattern) :
    ∃ stratum ∈ cover149.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified149 pattern feasiblePattern activePattern

theorem cover150ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover150.active pattern) :
    ∃ stratum ∈ cover150.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified150 pattern feasiblePattern activePattern

theorem cover151ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover151.active pattern) :
    ∃ stratum ∈ cover151.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified151 pattern feasiblePattern activePattern

theorem cover152ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover152.active pattern) :
    ∃ stratum ∈ cover152.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified152 pattern feasiblePattern activePattern

theorem cover153ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover153.active pattern) :
    ∃ stratum ∈ cover153.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified153 pattern feasiblePattern activePattern

theorem cover154ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover154.active pattern) :
    ∃ stratum ∈ cover154.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified154 pattern feasiblePattern activePattern

theorem cover155ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover155.active pattern) :
    ∃ stratum ∈ cover155.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified155 pattern feasiblePattern activePattern

theorem cover156ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover156.active pattern) :
    ∃ stratum ∈ cover156.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified156 pattern feasiblePattern activePattern

theorem cover157ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover157.active pattern) :
    ∃ stratum ∈ cover157.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified157 pattern feasiblePattern activePattern

theorem cover158ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover158.active pattern) :
    ∃ stratum ∈ cover158.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified158 pattern feasiblePattern activePattern

theorem cover159ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover159.active pattern) :
    ∃ stratum ∈ cover159.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified159 pattern feasiblePattern activePattern

theorem cover160ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover160.active pattern) :
    ∃ stratum ∈ cover160.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified160 pattern feasiblePattern activePattern

theorem cover161ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover161.active pattern) :
    ∃ stratum ∈ cover161.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified161 pattern feasiblePattern activePattern

theorem cover162ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover162.active pattern) :
    ∃ stratum ∈ cover162.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified162 pattern feasiblePattern activePattern

theorem cover163ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover163.active pattern) :
    ∃ stratum ∈ cover163.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified163 pattern feasiblePattern activePattern

theorem cover164ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover164.active pattern) :
    ∃ stratum ∈ cover164.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified164 pattern feasiblePattern activePattern

theorem cover165ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover165.active pattern) :
    ∃ stratum ∈ cover165.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified165 pattern feasiblePattern activePattern

theorem cover166ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover166.active pattern) :
    ∃ stratum ∈ cover166.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified166 pattern feasiblePattern activePattern

theorem cover167ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover167.active pattern) :
    ∃ stratum ∈ cover167.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified167 pattern feasiblePattern activePattern

theorem cover168ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover168.active pattern) :
    ∃ stratum ∈ cover168.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified168 pattern feasiblePattern activePattern

theorem cover169ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover169.active pattern) :
    ∃ stratum ∈ cover169.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified169 pattern feasiblePattern activePattern

theorem cover170ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover170.active pattern) :
    ∃ stratum ∈ cover170.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified170 pattern feasiblePattern activePattern

theorem cover171ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover171.active pattern) :
    ∃ stratum ∈ cover171.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified171 pattern feasiblePattern activePattern

theorem cover172ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover172.active pattern) :
    ∃ stratum ∈ cover172.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified172 pattern feasiblePattern activePattern

theorem cover173ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover173.active pattern) :
    ∃ stratum ∈ cover173.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified173 pattern feasiblePattern activePattern

theorem cover174ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover174.active pattern) :
    ∃ stratum ∈ cover174.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified174 pattern feasiblePattern activePattern

theorem cover175ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover175.active pattern) :
    ∃ stratum ∈ cover175.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified175 pattern feasiblePattern activePattern

theorem cover176ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover176.active pattern) :
    ∃ stratum ∈ cover176.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified176 pattern feasiblePattern activePattern

theorem cover177ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover177.active pattern) :
    ∃ stratum ∈ cover177.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified177 pattern feasiblePattern activePattern

theorem cover178ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover178.active pattern) :
    ∃ stratum ∈ cover178.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified178 pattern feasiblePattern activePattern

theorem cover179ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover179.active pattern) :
    ∃ stratum ∈ cover179.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified179 pattern feasiblePattern activePattern

theorem cover180ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover180.active pattern) :
    ∃ stratum ∈ cover180.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified180 pattern feasiblePattern activePattern

theorem cover181ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover181.active pattern) :
    ∃ stratum ∈ cover181.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified181 pattern feasiblePattern activePattern

theorem cover182ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover182.active pattern) :
    ∃ stratum ∈ cover182.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified182 pattern feasiblePattern activePattern

theorem cover183ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover183.active pattern) :
    ∃ stratum ∈ cover183.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified183 pattern feasiblePattern activePattern

theorem cover184ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover184.active pattern) :
    ∃ stratum ∈ cover184.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified184 pattern feasiblePattern activePattern

theorem cover185ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover185.active pattern) :
    ∃ stratum ∈ cover185.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified185 pattern feasiblePattern activePattern

theorem cover186ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover186.active pattern) :
    ∃ stratum ∈ cover186.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified186 pattern feasiblePattern activePattern

theorem cover187ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover187.active pattern) :
    ∃ stratum ∈ cover187.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified187 pattern feasiblePattern activePattern

theorem cover188ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover188.active pattern) :
    ∃ stratum ∈ cover188.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified188 pattern feasiblePattern activePattern

theorem cover189ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover189.active pattern) :
    ∃ stratum ∈ cover189.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified189 pattern feasiblePattern activePattern

theorem cover190ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover190.active pattern) :
    ∃ stratum ∈ cover190.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified190 pattern feasiblePattern activePattern

theorem cover191ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover191.active pattern) :
    ∃ stratum ∈ cover191.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified191 pattern feasiblePattern activePattern

theorem cover192ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover192.active pattern) :
    ∃ stratum ∈ cover192.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified192 pattern feasiblePattern activePattern

theorem cover193ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover193.active pattern) :
    ∃ stratum ∈ cover193.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified193 pattern feasiblePattern activePattern

theorem cover194ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover194.active pattern) :
    ∃ stratum ∈ cover194.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified194 pattern feasiblePattern activePattern

theorem cover195ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover195.active pattern) :
    ∃ stratum ∈ cover195.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified195 pattern feasiblePattern activePattern

theorem cover196ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover196.active pattern) :
    ∃ stratum ∈ cover196.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified196 pattern feasiblePattern activePattern

theorem cover197ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover197.active pattern) :
    ∃ stratum ∈ cover197.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified197 pattern feasiblePattern activePattern

theorem cover198ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover198.active pattern) :
    ∃ stratum ∈ cover198.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified198 pattern feasiblePattern activePattern

theorem cover199ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover199.active pattern) :
    ∃ stratum ∈ cover199.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified199 pattern feasiblePattern activePattern

theorem cover200ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover200.active pattern) :
    ∃ stratum ∈ cover200.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified200 pattern feasiblePattern activePattern

theorem cover201ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover201.active pattern) :
    ∃ stratum ∈ cover201.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified201 pattern feasiblePattern activePattern

theorem cover202ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover202.active pattern) :
    ∃ stratum ∈ cover202.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified202 pattern feasiblePattern activePattern

theorem cover203ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover203.active pattern) :
    ∃ stratum ∈ cover203.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified203 pattern feasiblePattern activePattern

theorem cover204ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover204.active pattern) :
    ∃ stratum ∈ cover204.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified204 pattern feasiblePattern activePattern

theorem cover205ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover205.active pattern) :
    ∃ stratum ∈ cover205.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified205 pattern feasiblePattern activePattern

theorem cover206ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover206.active pattern) :
    ∃ stratum ∈ cover206.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified206 pattern feasiblePattern activePattern

theorem cover207ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover207.active pattern) :
    ∃ stratum ∈ cover207.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified207 pattern feasiblePattern activePattern

theorem cover208ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover208.active pattern) :
    ∃ stratum ∈ cover208.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified208 pattern feasiblePattern activePattern

theorem cover209ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover209.active pattern) :
    ∃ stratum ∈ cover209.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified209 pattern feasiblePattern activePattern

theorem cover210ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover210.active pattern) :
    ∃ stratum ∈ cover210.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified210 pattern feasiblePattern activePattern

theorem cover211ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover211.active pattern) :
    ∃ stratum ∈ cover211.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified211 pattern feasiblePattern activePattern

theorem cover212ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover212.active pattern) :
    ∃ stratum ∈ cover212.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified212 pattern feasiblePattern activePattern

theorem cover213ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover213.active pattern) :
    ∃ stratum ∈ cover213.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified213 pattern feasiblePattern activePattern

theorem cover214ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover214.active pattern) :
    ∃ stratum ∈ cover214.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified214 pattern feasiblePattern activePattern

theorem cover215ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover215.active pattern) :
    ∃ stratum ∈ cover215.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified215 pattern feasiblePattern activePattern

theorem cover216ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover216.active pattern) :
    ∃ stratum ∈ cover216.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified216 pattern feasiblePattern activePattern

theorem cover217ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover217.active pattern) :
    ∃ stratum ∈ cover217.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified217 pattern feasiblePattern activePattern

theorem cover218ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover218.active pattern) :
    ∃ stratum ∈ cover218.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified218 pattern feasiblePattern activePattern

theorem cover219ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover219.active pattern) :
    ∃ stratum ∈ cover219.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified219 pattern feasiblePattern activePattern

theorem cover220ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover220.active pattern) :
    ∃ stratum ∈ cover220.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified220 pattern feasiblePattern activePattern

theorem cover221ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover221.active pattern) :
    ∃ stratum ∈ cover221.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified221 pattern feasiblePattern activePattern

theorem cover222ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover222.active pattern) :
    ∃ stratum ∈ cover222.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified222 pattern feasiblePattern activePattern

theorem cover223ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover223.active pattern) :
    ∃ stratum ∈ cover223.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified223 pattern feasiblePattern activePattern

theorem cover224ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover224.active pattern) :
    ∃ stratum ∈ cover224.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified224 pattern feasiblePattern activePattern

theorem cover225ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover225.active pattern) :
    ∃ stratum ∈ cover225.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified225 pattern feasiblePattern activePattern

theorem cover226ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover226.active pattern) :
    ∃ stratum ∈ cover226.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified226 pattern feasiblePattern activePattern

theorem cover227ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover227.active pattern) :
    ∃ stratum ∈ cover227.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified227 pattern feasiblePattern activePattern

theorem cover228ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover228.active pattern) :
    ∃ stratum ∈ cover228.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified228 pattern feasiblePattern activePattern

theorem cover229ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover229.active pattern) :
    ∃ stratum ∈ cover229.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified229 pattern feasiblePattern activePattern

theorem cover230ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover230.active pattern) :
    ∃ stratum ∈ cover230.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified230 pattern feasiblePattern activePattern

theorem cover231ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover231.active pattern) :
    ∃ stratum ∈ cover231.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified231 pattern feasiblePattern activePattern

theorem cover232ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover232.active pattern) :
    ∃ stratum ∈ cover232.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified232 pattern feasiblePattern activePattern

theorem cover233ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover233.active pattern) :
    ∃ stratum ∈ cover233.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified233 pattern feasiblePattern activePattern

theorem cover234ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover234.active pattern) :
    ∃ stratum ∈ cover234.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified234 pattern feasiblePattern activePattern

theorem cover235ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover235.active pattern) :
    ∃ stratum ∈ cover235.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified235 pattern feasiblePattern activePattern

theorem cover236ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover236.active pattern) :
    ∃ stratum ∈ cover236.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified236 pattern feasiblePattern activePattern

theorem cover237ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover237.active pattern) :
    ∃ stratum ∈ cover237.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified237 pattern feasiblePattern activePattern

theorem cover238ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover238.active pattern) :
    ∃ stratum ∈ cover238.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified238 pattern feasiblePattern activePattern

theorem cover239ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover239.active pattern) :
    ∃ stratum ∈ cover239.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified239 pattern feasiblePattern activePattern

theorem cover240ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover240.active pattern) :
    ∃ stratum ∈ cover240.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified240 pattern feasiblePattern activePattern

theorem cover241ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover241.active pattern) :
    ∃ stratum ∈ cover241.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified241 pattern feasiblePattern activePattern

theorem cover242ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover242.active pattern) :
    ∃ stratum ∈ cover242.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified242 pattern feasiblePattern activePattern

theorem cover243ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover243.active pattern) :
    ∃ stratum ∈ cover243.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified243 pattern feasiblePattern activePattern

theorem cover244ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover244.active pattern) :
    ∃ stratum ∈ cover244.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified244 pattern feasiblePattern activePattern

theorem cover245ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover245.active pattern) :
    ∃ stratum ∈ cover245.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified245 pattern feasiblePattern activePattern

theorem cover246ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover246.active pattern) :
    ∃ stratum ∈ cover246.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified246 pattern feasiblePattern activePattern

theorem cover247ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover247.active pattern) :
    ∃ stratum ∈ cover247.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified247 pattern feasiblePattern activePattern

theorem cover248ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover248.active pattern) :
    ∃ stratum ∈ cover248.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified248 pattern feasiblePattern activePattern

theorem cover249ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover249.active pattern) :
    ∃ stratum ∈ cover249.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified249 pattern feasiblePattern activePattern

theorem cover250ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover250.active pattern) :
    ∃ stratum ∈ cover250.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified250 pattern feasiblePattern activePattern

theorem cover251ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover251.active pattern) :
    ∃ stratum ∈ cover251.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified251 pattern feasiblePattern activePattern

theorem cover252ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover252.active pattern) :
    ∃ stratum ∈ cover252.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified252 pattern feasiblePattern activePattern

theorem cover253ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover253.active pattern) :
    ∃ stratum ∈ cover253.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified253 pattern feasiblePattern activePattern

theorem cover254ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover254.active pattern) :
    ∃ stratum ∈ cover254.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified254 pattern feasiblePattern activePattern

theorem cover255ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover255.active pattern) :
    ∃ stratum ∈ cover255.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified255 pattern feasiblePattern activePattern

theorem cover256ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover256.active pattern) :
    ∃ stratum ∈ cover256.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified256 pattern feasiblePattern activePattern

theorem cover257ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover257.active pattern) :
    ∃ stratum ∈ cover257.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified257 pattern feasiblePattern activePattern

theorem cover258ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover258.active pattern) :
    ∃ stratum ∈ cover258.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified258 pattern feasiblePattern activePattern

theorem cover259ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover259.active pattern) :
    ∃ stratum ∈ cover259.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified259 pattern feasiblePattern activePattern

theorem cover260ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover260.active pattern) :
    ∃ stratum ∈ cover260.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified260 pattern feasiblePattern activePattern

theorem cover261ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover261.active pattern) :
    ∃ stratum ∈ cover261.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified261 pattern feasiblePattern activePattern

theorem cover262ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover262.active pattern) :
    ∃ stratum ∈ cover262.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified262 pattern feasiblePattern activePattern

theorem cover263ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover263.active pattern) :
    ∃ stratum ∈ cover263.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified263 pattern feasiblePattern activePattern

theorem cover264ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover264.active pattern) :
    ∃ stratum ∈ cover264.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified264 pattern feasiblePattern activePattern

theorem cover265ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover265.active pattern) :
    ∃ stratum ∈ cover265.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified265 pattern feasiblePattern activePattern

theorem cover266ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover266.active pattern) :
    ∃ stratum ∈ cover266.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified266 pattern feasiblePattern activePattern

theorem cover267ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover267.active pattern) :
    ∃ stratum ∈ cover267.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified267 pattern feasiblePattern activePattern

theorem cover268ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover268.active pattern) :
    ∃ stratum ∈ cover268.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified268 pattern feasiblePattern activePattern

theorem cover269ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover269.active pattern) :
    ∃ stratum ∈ cover269.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified269 pattern feasiblePattern activePattern

theorem cover270ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover270.active pattern) :
    ∃ stratum ∈ cover270.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified270 pattern feasiblePattern activePattern

theorem cover271ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover271.active pattern) :
    ∃ stratum ∈ cover271.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified271 pattern feasiblePattern activePattern

theorem cover272ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover272.active pattern) :
    ∃ stratum ∈ cover272.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified272 pattern feasiblePattern activePattern

theorem cover273ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover273.active pattern) :
    ∃ stratum ∈ cover273.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified273 pattern feasiblePattern activePattern

theorem cover274ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover274.active pattern) :
    ∃ stratum ∈ cover274.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified274 pattern feasiblePattern activePattern

theorem cover275ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover275.active pattern) :
    ∃ stratum ∈ cover275.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified275 pattern feasiblePattern activePattern

theorem cover276ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover276.active pattern) :
    ∃ stratum ∈ cover276.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified276 pattern feasiblePattern activePattern

theorem cover277ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover277.active pattern) :
    ∃ stratum ∈ cover277.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified277 pattern feasiblePattern activePattern

theorem cover278ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover278.active pattern) :
    ∃ stratum ∈ cover278.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified278 pattern feasiblePattern activePattern

theorem cover279ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover279.active pattern) :
    ∃ stratum ∈ cover279.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified279 pattern feasiblePattern activePattern

theorem cover280ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover280.active pattern) :
    ∃ stratum ∈ cover280.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified280 pattern feasiblePattern activePattern

theorem cover281ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover281.active pattern) :
    ∃ stratum ∈ cover281.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified281 pattern feasiblePattern activePattern

theorem cover282ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover282.active pattern) :
    ∃ stratum ∈ cover282.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified282 pattern feasiblePattern activePattern

theorem cover283ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover283.active pattern) :
    ∃ stratum ∈ cover283.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified283 pattern feasiblePattern activePattern

theorem cover284ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover284.active pattern) :
    ∃ stratum ∈ cover284.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified284 pattern feasiblePattern activePattern

theorem cover285ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover285.active pattern) :
    ∃ stratum ∈ cover285.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified285 pattern feasiblePattern activePattern

theorem cover286ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover286.active pattern) :
    ∃ stratum ∈ cover286.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified286 pattern feasiblePattern activePattern

theorem cover287ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover287.active pattern) :
    ∃ stratum ∈ cover287.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified287 pattern feasiblePattern activePattern

theorem cover288ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover288.active pattern) :
    ∃ stratum ∈ cover288.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified288 pattern feasiblePattern activePattern

theorem cover289ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover289.active pattern) :
    ∃ stratum ∈ cover289.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified289 pattern feasiblePattern activePattern

theorem cover290ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover290.active pattern) :
    ∃ stratum ∈ cover290.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified290 pattern feasiblePattern activePattern

theorem cover291ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover291.active pattern) :
    ∃ stratum ∈ cover291.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified291 pattern feasiblePattern activePattern

theorem cover292ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover292.active pattern) :
    ∃ stratum ∈ cover292.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified292 pattern feasiblePattern activePattern

theorem cover293ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover293.active pattern) :
    ∃ stratum ∈ cover293.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified293 pattern feasiblePattern activePattern

theorem cover294ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover294.active pattern) :
    ∃ stratum ∈ cover294.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified294 pattern feasiblePattern activePattern

theorem cover295ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover295.active pattern) :
    ∃ stratum ∈ cover295.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified295 pattern feasiblePattern activePattern

theorem cover296ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover296.active pattern) :
    ∃ stratum ∈ cover296.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified296 pattern feasiblePattern activePattern

theorem cover297ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover297.active pattern) :
    ∃ stratum ∈ cover297.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified297 pattern feasiblePattern activePattern

theorem cover298ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover298.active pattern) :
    ∃ stratum ∈ cover298.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified298 pattern feasiblePattern activePattern

theorem cover299ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover299.active pattern) :
    ∃ stratum ∈ cover299.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified299 pattern feasiblePattern activePattern

theorem cover300ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover300.active pattern) :
    ∃ stratum ∈ cover300.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified300 pattern feasiblePattern activePattern

theorem cover301ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover301.active pattern) :
    ∃ stratum ∈ cover301.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified301 pattern feasiblePattern activePattern

theorem cover302ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover302.active pattern) :
    ∃ stratum ∈ cover302.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified302 pattern feasiblePattern activePattern

theorem cover303ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover303.active pattern) :
    ∃ stratum ∈ cover303.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified303 pattern feasiblePattern activePattern

theorem cover304ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover304.active pattern) :
    ∃ stratum ∈ cover304.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified304 pattern feasiblePattern activePattern

theorem cover305ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover305.active pattern) :
    ∃ stratum ∈ cover305.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified305 pattern feasiblePattern activePattern

theorem cover306ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover306.active pattern) :
    ∃ stratum ∈ cover306.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified306 pattern feasiblePattern activePattern

theorem cover307ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover307.active pattern) :
    ∃ stratum ∈ cover307.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified307 pattern feasiblePattern activePattern

theorem cover308ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover308.active pattern) :
    ∃ stratum ∈ cover308.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified308 pattern feasiblePattern activePattern

theorem cover309ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover309.active pattern) :
    ∃ stratum ∈ cover309.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified309 pattern feasiblePattern activePattern

theorem cover310ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover310.active pattern) :
    ∃ stratum ∈ cover310.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified310 pattern feasiblePattern activePattern

theorem cover311ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover311.active pattern) :
    ∃ stratum ∈ cover311.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified311 pattern feasiblePattern activePattern

theorem cover312ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover312.active pattern) :
    ∃ stratum ∈ cover312.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified312 pattern feasiblePattern activePattern

theorem cover313ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover313.active pattern) :
    ∃ stratum ∈ cover313.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified313 pattern feasiblePattern activePattern

theorem cover314ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover314.active pattern) :
    ∃ stratum ∈ cover314.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified314 pattern feasiblePattern activePattern

theorem cover315ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover315.active pattern) :
    ∃ stratum ∈ cover315.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified315 pattern feasiblePattern activePattern

theorem cover316ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover316.active pattern) :
    ∃ stratum ∈ cover316.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified316 pattern feasiblePattern activePattern

theorem cover317ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover317.active pattern) :
    ∃ stratum ∈ cover317.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified317 pattern feasiblePattern activePattern

theorem cover318ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover318.active pattern) :
    ∃ stratum ∈ cover318.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified318 pattern feasiblePattern activePattern

theorem cover319ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover319.active pattern) :
    ∃ stratum ∈ cover319.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified319 pattern feasiblePattern activePattern

theorem cover320ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover320.active pattern) :
    ∃ stratum ∈ cover320.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified320 pattern feasiblePattern activePattern

theorem cover321ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover321.active pattern) :
    ∃ stratum ∈ cover321.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified321 pattern feasiblePattern activePattern

theorem cover322ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover322.active pattern) :
    ∃ stratum ∈ cover322.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified322 pattern feasiblePattern activePattern

theorem cover323ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover323.active pattern) :
    ∃ stratum ∈ cover323.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified323 pattern feasiblePattern activePattern

theorem cover324ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover324.active pattern) :
    ∃ stratum ∈ cover324.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified324 pattern feasiblePattern activePattern

theorem cover325ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover325.active pattern) :
    ∃ stratum ∈ cover325.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified325 pattern feasiblePattern activePattern

theorem cover326ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover326.active pattern) :
    ∃ stratum ∈ cover326.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified326 pattern feasiblePattern activePattern

theorem cover327ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover327.active pattern) :
    ∃ stratum ∈ cover327.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified327 pattern feasiblePattern activePattern

theorem cover328ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover328.active pattern) :
    ∃ stratum ∈ cover328.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified328 pattern feasiblePattern activePattern

theorem cover329ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover329.active pattern) :
    ∃ stratum ∈ cover329.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified329 pattern feasiblePattern activePattern

theorem cover330ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover330.active pattern) :
    ∃ stratum ∈ cover330.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified330 pattern feasiblePattern activePattern

theorem cover331ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover331.active pattern) :
    ∃ stratum ∈ cover331.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified331 pattern feasiblePattern activePattern

theorem cover332ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover332.active pattern) :
    ∃ stratum ∈ cover332.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified332 pattern feasiblePattern activePattern

theorem cover333ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover333.active pattern) :
    ∃ stratum ∈ cover333.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified333 pattern feasiblePattern activePattern

theorem cover334ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover334.active pattern) :
    ∃ stratum ∈ cover334.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified334 pattern feasiblePattern activePattern

theorem cover335ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover335.active pattern) :
    ∃ stratum ∈ cover335.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified335 pattern feasiblePattern activePattern

theorem cover336ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover336.active pattern) :
    ∃ stratum ∈ cover336.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified336 pattern feasiblePattern activePattern

theorem cover337ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover337.active pattern) :
    ∃ stratum ∈ cover337.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified337 pattern feasiblePattern activePattern

theorem cover338ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover338.active pattern) :
    ∃ stratum ∈ cover338.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified338 pattern feasiblePattern activePattern

theorem cover339ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover339.active pattern) :
    ∃ stratum ∈ cover339.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified339 pattern feasiblePattern activePattern

theorem cover340ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover340.active pattern) :
    ∃ stratum ∈ cover340.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified340 pattern feasiblePattern activePattern

theorem cover341ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover341.active pattern) :
    ∃ stratum ∈ cover341.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified341 pattern feasiblePattern activePattern

theorem cover342ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover342.active pattern) :
    ∃ stratum ∈ cover342.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified342 pattern feasiblePattern activePattern

theorem cover343ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover343.active pattern) :
    ∃ stratum ∈ cover343.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified343 pattern feasiblePattern activePattern

theorem cover344ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover344.active pattern) :
    ∃ stratum ∈ cover344.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified344 pattern feasiblePattern activePattern

theorem cover345ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover345.active pattern) :
    ∃ stratum ∈ cover345.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified345 pattern feasiblePattern activePattern

theorem cover346ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover346.active pattern) :
    ∃ stratum ∈ cover346.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified346 pattern feasiblePattern activePattern

theorem cover347ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover347.active pattern) :
    ∃ stratum ∈ cover347.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified347 pattern feasiblePattern activePattern

theorem cover348ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover348.active pattern) :
    ∃ stratum ∈ cover348.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified348 pattern feasiblePattern activePattern

theorem cover349ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover349.active pattern) :
    ∃ stratum ∈ cover349.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified349 pattern feasiblePattern activePattern

theorem cover350ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover350.active pattern) :
    ∃ stratum ∈ cover350.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified350 pattern feasiblePattern activePattern

theorem cover351ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover351.active pattern) :
    ∃ stratum ∈ cover351.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified351 pattern feasiblePattern activePattern

theorem cover352ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover352.active pattern) :
    ∃ stratum ∈ cover352.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified352 pattern feasiblePattern activePattern

theorem cover353ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover353.active pattern) :
    ∃ stratum ∈ cover353.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified353 pattern feasiblePattern activePattern

theorem cover354ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover354.active pattern) :
    ∃ stratum ∈ cover354.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified354 pattern feasiblePattern activePattern

theorem cover355ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover355.active pattern) :
    ∃ stratum ∈ cover355.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified355 pattern feasiblePattern activePattern

theorem cover356ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover356.active pattern) :
    ∃ stratum ∈ cover356.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified356 pattern feasiblePattern activePattern

theorem cover357ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover357.active pattern) :
    ∃ stratum ∈ cover357.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified357 pattern feasiblePattern activePattern

theorem cover358ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover358.active pattern) :
    ∃ stratum ∈ cover358.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified358 pattern feasiblePattern activePattern

theorem cover359ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover359.active pattern) :
    ∃ stratum ∈ cover359.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified359 pattern feasiblePattern activePattern

theorem cover360ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover360.active pattern) :
    ∃ stratum ∈ cover360.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified360 pattern feasiblePattern activePattern

theorem cover361ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover361.active pattern) :
    ∃ stratum ∈ cover361.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified361 pattern feasiblePattern activePattern

theorem cover362ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover362.active pattern) :
    ∃ stratum ∈ cover362.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified362 pattern feasiblePattern activePattern

theorem cover363ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover363.active pattern) :
    ∃ stratum ∈ cover363.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified363 pattern feasiblePattern activePattern

theorem cover364ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover364.active pattern) :
    ∃ stratum ∈ cover364.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified364 pattern feasiblePattern activePattern

theorem cover365ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover365.active pattern) :
    ∃ stratum ∈ cover365.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified365 pattern feasiblePattern activePattern

theorem cover366ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover366.active pattern) :
    ∃ stratum ∈ cover366.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified366 pattern feasiblePattern activePattern

theorem cover367ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover367.active pattern) :
    ∃ stratum ∈ cover367.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified367 pattern feasiblePattern activePattern

theorem cover368ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover368.active pattern) :
    ∃ stratum ∈ cover368.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified368 pattern feasiblePattern activePattern

theorem cover369ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover369.active pattern) :
    ∃ stratum ∈ cover369.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified369 pattern feasiblePattern activePattern

theorem cover370ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover370.active pattern) :
    ∃ stratum ∈ cover370.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified370 pattern feasiblePattern activePattern

theorem cover371ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover371.active pattern) :
    ∃ stratum ∈ cover371.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified371 pattern feasiblePattern activePattern

theorem cover372ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover372.active pattern) :
    ∃ stratum ∈ cover372.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified372 pattern feasiblePattern activePattern

theorem cover373ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover373.active pattern) :
    ∃ stratum ∈ cover373.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified373 pattern feasiblePattern activePattern

theorem cover374ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover374.active pattern) :
    ∃ stratum ∈ cover374.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified374 pattern feasiblePattern activePattern

theorem cover375ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover375.active pattern) :
    ∃ stratum ∈ cover375.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified375 pattern feasiblePattern activePattern

theorem cover376ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover376.active pattern) :
    ∃ stratum ∈ cover376.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified376 pattern feasiblePattern activePattern

theorem cover377ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover377.active pattern) :
    ∃ stratum ∈ cover377.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified377 pattern feasiblePattern activePattern

theorem cover378ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover378.active pattern) :
    ∃ stratum ∈ cover378.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified378 pattern feasiblePattern activePattern

theorem cover379ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover379.active pattern) :
    ∃ stratum ∈ cover379.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified379 pattern feasiblePattern activePattern

theorem cover380ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover380.active pattern) :
    ∃ stratum ∈ cover380.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified380 pattern feasiblePattern activePattern

theorem cover381ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover381.active pattern) :
    ∃ stratum ∈ cover381.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified381 pattern feasiblePattern activePattern

theorem cover382ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover382.active pattern) :
    ∃ stratum ∈ cover382.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified382 pattern feasiblePattern activePattern

theorem cover383ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover383.active pattern) :
    ∃ stratum ∈ cover383.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified383 pattern feasiblePattern activePattern

theorem cover384ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover384.active pattern) :
    ∃ stratum ∈ cover384.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified384 pattern feasiblePattern activePattern

theorem cover385ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover385.active pattern) :
    ∃ stratum ∈ cover385.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified385 pattern feasiblePattern activePattern

theorem cover386ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover386.active pattern) :
    ∃ stratum ∈ cover386.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified386 pattern feasiblePattern activePattern

theorem cover387ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover387.active pattern) :
    ∃ stratum ∈ cover387.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified387 pattern feasiblePattern activePattern

theorem cover388ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover388.active pattern) :
    ∃ stratum ∈ cover388.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified388 pattern feasiblePattern activePattern

theorem cover389ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover389.active pattern) :
    ∃ stratum ∈ cover389.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified389 pattern feasiblePattern activePattern

theorem cover390ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover390.active pattern) :
    ∃ stratum ∈ cover390.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified390 pattern feasiblePattern activePattern

theorem cover391ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover391.active pattern) :
    ∃ stratum ∈ cover391.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified391 pattern feasiblePattern activePattern

theorem cover392ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover392.active pattern) :
    ∃ stratum ∈ cover392.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified392 pattern feasiblePattern activePattern

theorem cover393ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover393.active pattern) :
    ∃ stratum ∈ cover393.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified393 pattern feasiblePattern activePattern

theorem cover394ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover394.active pattern) :
    ∃ stratum ∈ cover394.strata, zeroMatchesProp stratum.zero pattern := by
  exact zeroCoveredOfBase CollapseSupportCover.certified394 pattern feasiblePattern activePattern

structure CertifiedCover where
  data : ActiveCover
  zeroCovered : ∀ pattern, feasibleProp pattern →
    activeMatchesProp data.active pattern →
    ∃ stratum ∈ data.strata, zeroMatchesProp stratum.zero pattern

def certified0 : CertifiedCover := ⟨cover0, cover0ZeroCovered⟩
def certified1 : CertifiedCover := ⟨cover1, cover1ZeroCovered⟩
def certified2 : CertifiedCover := ⟨cover2, cover2ZeroCovered⟩
def certified3 : CertifiedCover := ⟨cover3, cover3ZeroCovered⟩
def certified4 : CertifiedCover := ⟨cover4, cover4ZeroCovered⟩
def certified5 : CertifiedCover := ⟨cover5, cover5ZeroCovered⟩
def certified6 : CertifiedCover := ⟨cover6, cover6ZeroCovered⟩
def certified7 : CertifiedCover := ⟨cover7, cover7ZeroCovered⟩
def certified8 : CertifiedCover := ⟨cover8, cover8ZeroCovered⟩
def certified9 : CertifiedCover := ⟨cover9, cover9ZeroCovered⟩
def certified10 : CertifiedCover := ⟨cover10, cover10ZeroCovered⟩
def certified11 : CertifiedCover := ⟨cover11, cover11ZeroCovered⟩
def certified12 : CertifiedCover := ⟨cover12, cover12ZeroCovered⟩
def certified13 : CertifiedCover := ⟨cover13, cover13ZeroCovered⟩
def certified14 : CertifiedCover := ⟨cover14, cover14ZeroCovered⟩
def certified15 : CertifiedCover := ⟨cover15, cover15ZeroCovered⟩
def certified16 : CertifiedCover := ⟨cover16, cover16ZeroCovered⟩
def certified17 : CertifiedCover := ⟨cover17, cover17ZeroCovered⟩
def certified18 : CertifiedCover := ⟨cover18, cover18ZeroCovered⟩
def certified19 : CertifiedCover := ⟨cover19, cover19ZeroCovered⟩
def certified20 : CertifiedCover := ⟨cover20, cover20ZeroCovered⟩
def certified21 : CertifiedCover := ⟨cover21, cover21ZeroCovered⟩
def certified22 : CertifiedCover := ⟨cover22, cover22ZeroCovered⟩
def certified23 : CertifiedCover := ⟨cover23, cover23ZeroCovered⟩
def certified24 : CertifiedCover := ⟨cover24, cover24ZeroCovered⟩
def certified25 : CertifiedCover := ⟨cover25, cover25ZeroCovered⟩
def certified26 : CertifiedCover := ⟨cover26, cover26ZeroCovered⟩
def certified27 : CertifiedCover := ⟨cover27, cover27ZeroCovered⟩
def certified28 : CertifiedCover := ⟨cover28, cover28ZeroCovered⟩
def certified29 : CertifiedCover := ⟨cover29, cover29ZeroCovered⟩
def certified30 : CertifiedCover := ⟨cover30, cover30ZeroCovered⟩
def certified31 : CertifiedCover := ⟨cover31, cover31ZeroCovered⟩
def certified32 : CertifiedCover := ⟨cover32, cover32ZeroCovered⟩
def certified33 : CertifiedCover := ⟨cover33, cover33ZeroCovered⟩
def certified34 : CertifiedCover := ⟨cover34, cover34ZeroCovered⟩
def certified35 : CertifiedCover := ⟨cover35, cover35ZeroCovered⟩
def certified36 : CertifiedCover := ⟨cover36, cover36ZeroCovered⟩
def certified37 : CertifiedCover := ⟨cover37, cover37ZeroCovered⟩
def certified38 : CertifiedCover := ⟨cover38, cover38ZeroCovered⟩
def certified39 : CertifiedCover := ⟨cover39, cover39ZeroCovered⟩
def certified40 : CertifiedCover := ⟨cover40, cover40ZeroCovered⟩
def certified41 : CertifiedCover := ⟨cover41, cover41ZeroCovered⟩
def certified42 : CertifiedCover := ⟨cover42, cover42ZeroCovered⟩
def certified43 : CertifiedCover := ⟨cover43, cover43ZeroCovered⟩
def certified44 : CertifiedCover := ⟨cover44, cover44ZeroCovered⟩
def certified45 : CertifiedCover := ⟨cover45, cover45ZeroCovered⟩
def certified46 : CertifiedCover := ⟨cover46, cover46ZeroCovered⟩
def certified47 : CertifiedCover := ⟨cover47, cover47ZeroCovered⟩
def certified48 : CertifiedCover := ⟨cover48, cover48ZeroCovered⟩
def certified49 : CertifiedCover := ⟨cover49, cover49ZeroCovered⟩
def certified50 : CertifiedCover := ⟨cover50, cover50ZeroCovered⟩
def certified51 : CertifiedCover := ⟨cover51, cover51ZeroCovered⟩
def certified52 : CertifiedCover := ⟨cover52, cover52ZeroCovered⟩
def certified53 : CertifiedCover := ⟨cover53, cover53ZeroCovered⟩
def certified54 : CertifiedCover := ⟨cover54, cover54ZeroCovered⟩
def certified55 : CertifiedCover := ⟨cover55, cover55ZeroCovered⟩
def certified56 : CertifiedCover := ⟨cover56, cover56ZeroCovered⟩
def certified57 : CertifiedCover := ⟨cover57, cover57ZeroCovered⟩
def certified58 : CertifiedCover := ⟨cover58, cover58ZeroCovered⟩
def certified59 : CertifiedCover := ⟨cover59, cover59ZeroCovered⟩
def certified60 : CertifiedCover := ⟨cover60, cover60ZeroCovered⟩
def certified61 : CertifiedCover := ⟨cover61, cover61ZeroCovered⟩
def certified62 : CertifiedCover := ⟨cover62, cover62ZeroCovered⟩
def certified63 : CertifiedCover := ⟨cover63, cover63ZeroCovered⟩
def certified64 : CertifiedCover := ⟨cover64, cover64ZeroCovered⟩
def certified65 : CertifiedCover := ⟨cover65, cover65ZeroCovered⟩
def certified66 : CertifiedCover := ⟨cover66, cover66ZeroCovered⟩
def certified67 : CertifiedCover := ⟨cover67, cover67ZeroCovered⟩
def certified68 : CertifiedCover := ⟨cover68, cover68ZeroCovered⟩
def certified69 : CertifiedCover := ⟨cover69, cover69ZeroCovered⟩
def certified70 : CertifiedCover := ⟨cover70, cover70ZeroCovered⟩
def certified71 : CertifiedCover := ⟨cover71, cover71ZeroCovered⟩
def certified72 : CertifiedCover := ⟨cover72, cover72ZeroCovered⟩
def certified73 : CertifiedCover := ⟨cover73, cover73ZeroCovered⟩
def certified74 : CertifiedCover := ⟨cover74, cover74ZeroCovered⟩
def certified75 : CertifiedCover := ⟨cover75, cover75ZeroCovered⟩
def certified76 : CertifiedCover := ⟨cover76, cover76ZeroCovered⟩
def certified77 : CertifiedCover := ⟨cover77, cover77ZeroCovered⟩
def certified78 : CertifiedCover := ⟨cover78, cover78ZeroCovered⟩
def certified79 : CertifiedCover := ⟨cover79, cover79ZeroCovered⟩
def certified80 : CertifiedCover := ⟨cover80, cover80ZeroCovered⟩
def certified81 : CertifiedCover := ⟨cover81, cover81ZeroCovered⟩
def certified82 : CertifiedCover := ⟨cover82, cover82ZeroCovered⟩
def certified83 : CertifiedCover := ⟨cover83, cover83ZeroCovered⟩
def certified84 : CertifiedCover := ⟨cover84, cover84ZeroCovered⟩
def certified85 : CertifiedCover := ⟨cover85, cover85ZeroCovered⟩
def certified86 : CertifiedCover := ⟨cover86, cover86ZeroCovered⟩
def certified87 : CertifiedCover := ⟨cover87, cover87ZeroCovered⟩
def certified88 : CertifiedCover := ⟨cover88, cover88ZeroCovered⟩
def certified89 : CertifiedCover := ⟨cover89, cover89ZeroCovered⟩
def certified90 : CertifiedCover := ⟨cover90, cover90ZeroCovered⟩
def certified91 : CertifiedCover := ⟨cover91, cover91ZeroCovered⟩
def certified92 : CertifiedCover := ⟨cover92, cover92ZeroCovered⟩
def certified93 : CertifiedCover := ⟨cover93, cover93ZeroCovered⟩
def certified94 : CertifiedCover := ⟨cover94, cover94ZeroCovered⟩
def certified95 : CertifiedCover := ⟨cover95, cover95ZeroCovered⟩
def certified96 : CertifiedCover := ⟨cover96, cover96ZeroCovered⟩
def certified97 : CertifiedCover := ⟨cover97, cover97ZeroCovered⟩
def certified98 : CertifiedCover := ⟨cover98, cover98ZeroCovered⟩
def certified99 : CertifiedCover := ⟨cover99, cover99ZeroCovered⟩
def certified100 : CertifiedCover := ⟨cover100, cover100ZeroCovered⟩
def certified101 : CertifiedCover := ⟨cover101, cover101ZeroCovered⟩
def certified102 : CertifiedCover := ⟨cover102, cover102ZeroCovered⟩
def certified103 : CertifiedCover := ⟨cover103, cover103ZeroCovered⟩
def certified104 : CertifiedCover := ⟨cover104, cover104ZeroCovered⟩
def certified105 : CertifiedCover := ⟨cover105, cover105ZeroCovered⟩
def certified106 : CertifiedCover := ⟨cover106, cover106ZeroCovered⟩
def certified107 : CertifiedCover := ⟨cover107, cover107ZeroCovered⟩
def certified108 : CertifiedCover := ⟨cover108, cover108ZeroCovered⟩
def certified109 : CertifiedCover := ⟨cover109, cover109ZeroCovered⟩
def certified110 : CertifiedCover := ⟨cover110, cover110ZeroCovered⟩
def certified111 : CertifiedCover := ⟨cover111, cover111ZeroCovered⟩
def certified112 : CertifiedCover := ⟨cover112, cover112ZeroCovered⟩
def certified113 : CertifiedCover := ⟨cover113, cover113ZeroCovered⟩
def certified114 : CertifiedCover := ⟨cover114, cover114ZeroCovered⟩
def certified115 : CertifiedCover := ⟨cover115, cover115ZeroCovered⟩
def certified116 : CertifiedCover := ⟨cover116, cover116ZeroCovered⟩
def certified117 : CertifiedCover := ⟨cover117, cover117ZeroCovered⟩
def certified118 : CertifiedCover := ⟨cover118, cover118ZeroCovered⟩
def certified119 : CertifiedCover := ⟨cover119, cover119ZeroCovered⟩
def certified120 : CertifiedCover := ⟨cover120, cover120ZeroCovered⟩
def certified121 : CertifiedCover := ⟨cover121, cover121ZeroCovered⟩
def certified122 : CertifiedCover := ⟨cover122, cover122ZeroCovered⟩
def certified123 : CertifiedCover := ⟨cover123, cover123ZeroCovered⟩
def certified124 : CertifiedCover := ⟨cover124, cover124ZeroCovered⟩
def certified125 : CertifiedCover := ⟨cover125, cover125ZeroCovered⟩
def certified126 : CertifiedCover := ⟨cover126, cover126ZeroCovered⟩
def certified127 : CertifiedCover := ⟨cover127, cover127ZeroCovered⟩
def certified128 : CertifiedCover := ⟨cover128, cover128ZeroCovered⟩
def certified129 : CertifiedCover := ⟨cover129, cover129ZeroCovered⟩
def certified130 : CertifiedCover := ⟨cover130, cover130ZeroCovered⟩
def certified131 : CertifiedCover := ⟨cover131, cover131ZeroCovered⟩
def certified132 : CertifiedCover := ⟨cover132, cover132ZeroCovered⟩
def certified133 : CertifiedCover := ⟨cover133, cover133ZeroCovered⟩
def certified134 : CertifiedCover := ⟨cover134, cover134ZeroCovered⟩
def certified135 : CertifiedCover := ⟨cover135, cover135ZeroCovered⟩
def certified136 : CertifiedCover := ⟨cover136, cover136ZeroCovered⟩
def certified137 : CertifiedCover := ⟨cover137, cover137ZeroCovered⟩
def certified138 : CertifiedCover := ⟨cover138, cover138ZeroCovered⟩
def certified139 : CertifiedCover := ⟨cover139, cover139ZeroCovered⟩
def certified140 : CertifiedCover := ⟨cover140, cover140ZeroCovered⟩
def certified141 : CertifiedCover := ⟨cover141, cover141ZeroCovered⟩
def certified142 : CertifiedCover := ⟨cover142, cover142ZeroCovered⟩
def certified143 : CertifiedCover := ⟨cover143, cover143ZeroCovered⟩
def certified144 : CertifiedCover := ⟨cover144, cover144ZeroCovered⟩
def certified145 : CertifiedCover := ⟨cover145, cover145ZeroCovered⟩
def certified146 : CertifiedCover := ⟨cover146, cover146ZeroCovered⟩
def certified147 : CertifiedCover := ⟨cover147, cover147ZeroCovered⟩
def certified148 : CertifiedCover := ⟨cover148, cover148ZeroCovered⟩
def certified149 : CertifiedCover := ⟨cover149, cover149ZeroCovered⟩
def certified150 : CertifiedCover := ⟨cover150, cover150ZeroCovered⟩
def certified151 : CertifiedCover := ⟨cover151, cover151ZeroCovered⟩
def certified152 : CertifiedCover := ⟨cover152, cover152ZeroCovered⟩
def certified153 : CertifiedCover := ⟨cover153, cover153ZeroCovered⟩
def certified154 : CertifiedCover := ⟨cover154, cover154ZeroCovered⟩
def certified155 : CertifiedCover := ⟨cover155, cover155ZeroCovered⟩
def certified156 : CertifiedCover := ⟨cover156, cover156ZeroCovered⟩
def certified157 : CertifiedCover := ⟨cover157, cover157ZeroCovered⟩
def certified158 : CertifiedCover := ⟨cover158, cover158ZeroCovered⟩
def certified159 : CertifiedCover := ⟨cover159, cover159ZeroCovered⟩
def certified160 : CertifiedCover := ⟨cover160, cover160ZeroCovered⟩
def certified161 : CertifiedCover := ⟨cover161, cover161ZeroCovered⟩
def certified162 : CertifiedCover := ⟨cover162, cover162ZeroCovered⟩
def certified163 : CertifiedCover := ⟨cover163, cover163ZeroCovered⟩
def certified164 : CertifiedCover := ⟨cover164, cover164ZeroCovered⟩
def certified165 : CertifiedCover := ⟨cover165, cover165ZeroCovered⟩
def certified166 : CertifiedCover := ⟨cover166, cover166ZeroCovered⟩
def certified167 : CertifiedCover := ⟨cover167, cover167ZeroCovered⟩
def certified168 : CertifiedCover := ⟨cover168, cover168ZeroCovered⟩
def certified169 : CertifiedCover := ⟨cover169, cover169ZeroCovered⟩
def certified170 : CertifiedCover := ⟨cover170, cover170ZeroCovered⟩
def certified171 : CertifiedCover := ⟨cover171, cover171ZeroCovered⟩
def certified172 : CertifiedCover := ⟨cover172, cover172ZeroCovered⟩
def certified173 : CertifiedCover := ⟨cover173, cover173ZeroCovered⟩
def certified174 : CertifiedCover := ⟨cover174, cover174ZeroCovered⟩
def certified175 : CertifiedCover := ⟨cover175, cover175ZeroCovered⟩
def certified176 : CertifiedCover := ⟨cover176, cover176ZeroCovered⟩
def certified177 : CertifiedCover := ⟨cover177, cover177ZeroCovered⟩
def certified178 : CertifiedCover := ⟨cover178, cover178ZeroCovered⟩
def certified179 : CertifiedCover := ⟨cover179, cover179ZeroCovered⟩
def certified180 : CertifiedCover := ⟨cover180, cover180ZeroCovered⟩
def certified181 : CertifiedCover := ⟨cover181, cover181ZeroCovered⟩
def certified182 : CertifiedCover := ⟨cover182, cover182ZeroCovered⟩
def certified183 : CertifiedCover := ⟨cover183, cover183ZeroCovered⟩
def certified184 : CertifiedCover := ⟨cover184, cover184ZeroCovered⟩
def certified185 : CertifiedCover := ⟨cover185, cover185ZeroCovered⟩
def certified186 : CertifiedCover := ⟨cover186, cover186ZeroCovered⟩
def certified187 : CertifiedCover := ⟨cover187, cover187ZeroCovered⟩
def certified188 : CertifiedCover := ⟨cover188, cover188ZeroCovered⟩
def certified189 : CertifiedCover := ⟨cover189, cover189ZeroCovered⟩
def certified190 : CertifiedCover := ⟨cover190, cover190ZeroCovered⟩
def certified191 : CertifiedCover := ⟨cover191, cover191ZeroCovered⟩
def certified192 : CertifiedCover := ⟨cover192, cover192ZeroCovered⟩
def certified193 : CertifiedCover := ⟨cover193, cover193ZeroCovered⟩
def certified194 : CertifiedCover := ⟨cover194, cover194ZeroCovered⟩
def certified195 : CertifiedCover := ⟨cover195, cover195ZeroCovered⟩
def certified196 : CertifiedCover := ⟨cover196, cover196ZeroCovered⟩
def certified197 : CertifiedCover := ⟨cover197, cover197ZeroCovered⟩
def certified198 : CertifiedCover := ⟨cover198, cover198ZeroCovered⟩
def certified199 : CertifiedCover := ⟨cover199, cover199ZeroCovered⟩
def certified200 : CertifiedCover := ⟨cover200, cover200ZeroCovered⟩
def certified201 : CertifiedCover := ⟨cover201, cover201ZeroCovered⟩
def certified202 : CertifiedCover := ⟨cover202, cover202ZeroCovered⟩
def certified203 : CertifiedCover := ⟨cover203, cover203ZeroCovered⟩
def certified204 : CertifiedCover := ⟨cover204, cover204ZeroCovered⟩
def certified205 : CertifiedCover := ⟨cover205, cover205ZeroCovered⟩
def certified206 : CertifiedCover := ⟨cover206, cover206ZeroCovered⟩
def certified207 : CertifiedCover := ⟨cover207, cover207ZeroCovered⟩
def certified208 : CertifiedCover := ⟨cover208, cover208ZeroCovered⟩
def certified209 : CertifiedCover := ⟨cover209, cover209ZeroCovered⟩
def certified210 : CertifiedCover := ⟨cover210, cover210ZeroCovered⟩
def certified211 : CertifiedCover := ⟨cover211, cover211ZeroCovered⟩
def certified212 : CertifiedCover := ⟨cover212, cover212ZeroCovered⟩
def certified213 : CertifiedCover := ⟨cover213, cover213ZeroCovered⟩
def certified214 : CertifiedCover := ⟨cover214, cover214ZeroCovered⟩
def certified215 : CertifiedCover := ⟨cover215, cover215ZeroCovered⟩
def certified216 : CertifiedCover := ⟨cover216, cover216ZeroCovered⟩
def certified217 : CertifiedCover := ⟨cover217, cover217ZeroCovered⟩
def certified218 : CertifiedCover := ⟨cover218, cover218ZeroCovered⟩
def certified219 : CertifiedCover := ⟨cover219, cover219ZeroCovered⟩
def certified220 : CertifiedCover := ⟨cover220, cover220ZeroCovered⟩
def certified221 : CertifiedCover := ⟨cover221, cover221ZeroCovered⟩
def certified222 : CertifiedCover := ⟨cover222, cover222ZeroCovered⟩
def certified223 : CertifiedCover := ⟨cover223, cover223ZeroCovered⟩
def certified224 : CertifiedCover := ⟨cover224, cover224ZeroCovered⟩
def certified225 : CertifiedCover := ⟨cover225, cover225ZeroCovered⟩
def certified226 : CertifiedCover := ⟨cover226, cover226ZeroCovered⟩
def certified227 : CertifiedCover := ⟨cover227, cover227ZeroCovered⟩
def certified228 : CertifiedCover := ⟨cover228, cover228ZeroCovered⟩
def certified229 : CertifiedCover := ⟨cover229, cover229ZeroCovered⟩
def certified230 : CertifiedCover := ⟨cover230, cover230ZeroCovered⟩
def certified231 : CertifiedCover := ⟨cover231, cover231ZeroCovered⟩
def certified232 : CertifiedCover := ⟨cover232, cover232ZeroCovered⟩
def certified233 : CertifiedCover := ⟨cover233, cover233ZeroCovered⟩
def certified234 : CertifiedCover := ⟨cover234, cover234ZeroCovered⟩
def certified235 : CertifiedCover := ⟨cover235, cover235ZeroCovered⟩
def certified236 : CertifiedCover := ⟨cover236, cover236ZeroCovered⟩
def certified237 : CertifiedCover := ⟨cover237, cover237ZeroCovered⟩
def certified238 : CertifiedCover := ⟨cover238, cover238ZeroCovered⟩
def certified239 : CertifiedCover := ⟨cover239, cover239ZeroCovered⟩
def certified240 : CertifiedCover := ⟨cover240, cover240ZeroCovered⟩
def certified241 : CertifiedCover := ⟨cover241, cover241ZeroCovered⟩
def certified242 : CertifiedCover := ⟨cover242, cover242ZeroCovered⟩
def certified243 : CertifiedCover := ⟨cover243, cover243ZeroCovered⟩
def certified244 : CertifiedCover := ⟨cover244, cover244ZeroCovered⟩
def certified245 : CertifiedCover := ⟨cover245, cover245ZeroCovered⟩
def certified246 : CertifiedCover := ⟨cover246, cover246ZeroCovered⟩
def certified247 : CertifiedCover := ⟨cover247, cover247ZeroCovered⟩
def certified248 : CertifiedCover := ⟨cover248, cover248ZeroCovered⟩
def certified249 : CertifiedCover := ⟨cover249, cover249ZeroCovered⟩
def certified250 : CertifiedCover := ⟨cover250, cover250ZeroCovered⟩
def certified251 : CertifiedCover := ⟨cover251, cover251ZeroCovered⟩
def certified252 : CertifiedCover := ⟨cover252, cover252ZeroCovered⟩
def certified253 : CertifiedCover := ⟨cover253, cover253ZeroCovered⟩
def certified254 : CertifiedCover := ⟨cover254, cover254ZeroCovered⟩
def certified255 : CertifiedCover := ⟨cover255, cover255ZeroCovered⟩
def certified256 : CertifiedCover := ⟨cover256, cover256ZeroCovered⟩
def certified257 : CertifiedCover := ⟨cover257, cover257ZeroCovered⟩
def certified258 : CertifiedCover := ⟨cover258, cover258ZeroCovered⟩
def certified259 : CertifiedCover := ⟨cover259, cover259ZeroCovered⟩
def certified260 : CertifiedCover := ⟨cover260, cover260ZeroCovered⟩
def certified261 : CertifiedCover := ⟨cover261, cover261ZeroCovered⟩
def certified262 : CertifiedCover := ⟨cover262, cover262ZeroCovered⟩
def certified263 : CertifiedCover := ⟨cover263, cover263ZeroCovered⟩
def certified264 : CertifiedCover := ⟨cover264, cover264ZeroCovered⟩
def certified265 : CertifiedCover := ⟨cover265, cover265ZeroCovered⟩
def certified266 : CertifiedCover := ⟨cover266, cover266ZeroCovered⟩
def certified267 : CertifiedCover := ⟨cover267, cover267ZeroCovered⟩
def certified268 : CertifiedCover := ⟨cover268, cover268ZeroCovered⟩
def certified269 : CertifiedCover := ⟨cover269, cover269ZeroCovered⟩
def certified270 : CertifiedCover := ⟨cover270, cover270ZeroCovered⟩
def certified271 : CertifiedCover := ⟨cover271, cover271ZeroCovered⟩
def certified272 : CertifiedCover := ⟨cover272, cover272ZeroCovered⟩
def certified273 : CertifiedCover := ⟨cover273, cover273ZeroCovered⟩
def certified274 : CertifiedCover := ⟨cover274, cover274ZeroCovered⟩
def certified275 : CertifiedCover := ⟨cover275, cover275ZeroCovered⟩
def certified276 : CertifiedCover := ⟨cover276, cover276ZeroCovered⟩
def certified277 : CertifiedCover := ⟨cover277, cover277ZeroCovered⟩
def certified278 : CertifiedCover := ⟨cover278, cover278ZeroCovered⟩
def certified279 : CertifiedCover := ⟨cover279, cover279ZeroCovered⟩
def certified280 : CertifiedCover := ⟨cover280, cover280ZeroCovered⟩
def certified281 : CertifiedCover := ⟨cover281, cover281ZeroCovered⟩
def certified282 : CertifiedCover := ⟨cover282, cover282ZeroCovered⟩
def certified283 : CertifiedCover := ⟨cover283, cover283ZeroCovered⟩
def certified284 : CertifiedCover := ⟨cover284, cover284ZeroCovered⟩
def certified285 : CertifiedCover := ⟨cover285, cover285ZeroCovered⟩
def certified286 : CertifiedCover := ⟨cover286, cover286ZeroCovered⟩
def certified287 : CertifiedCover := ⟨cover287, cover287ZeroCovered⟩
def certified288 : CertifiedCover := ⟨cover288, cover288ZeroCovered⟩
def certified289 : CertifiedCover := ⟨cover289, cover289ZeroCovered⟩
def certified290 : CertifiedCover := ⟨cover290, cover290ZeroCovered⟩
def certified291 : CertifiedCover := ⟨cover291, cover291ZeroCovered⟩
def certified292 : CertifiedCover := ⟨cover292, cover292ZeroCovered⟩
def certified293 : CertifiedCover := ⟨cover293, cover293ZeroCovered⟩
def certified294 : CertifiedCover := ⟨cover294, cover294ZeroCovered⟩
def certified295 : CertifiedCover := ⟨cover295, cover295ZeroCovered⟩
def certified296 : CertifiedCover := ⟨cover296, cover296ZeroCovered⟩
def certified297 : CertifiedCover := ⟨cover297, cover297ZeroCovered⟩
def certified298 : CertifiedCover := ⟨cover298, cover298ZeroCovered⟩
def certified299 : CertifiedCover := ⟨cover299, cover299ZeroCovered⟩
def certified300 : CertifiedCover := ⟨cover300, cover300ZeroCovered⟩
def certified301 : CertifiedCover := ⟨cover301, cover301ZeroCovered⟩
def certified302 : CertifiedCover := ⟨cover302, cover302ZeroCovered⟩
def certified303 : CertifiedCover := ⟨cover303, cover303ZeroCovered⟩
def certified304 : CertifiedCover := ⟨cover304, cover304ZeroCovered⟩
def certified305 : CertifiedCover := ⟨cover305, cover305ZeroCovered⟩
def certified306 : CertifiedCover := ⟨cover306, cover306ZeroCovered⟩
def certified307 : CertifiedCover := ⟨cover307, cover307ZeroCovered⟩
def certified308 : CertifiedCover := ⟨cover308, cover308ZeroCovered⟩
def certified309 : CertifiedCover := ⟨cover309, cover309ZeroCovered⟩
def certified310 : CertifiedCover := ⟨cover310, cover310ZeroCovered⟩
def certified311 : CertifiedCover := ⟨cover311, cover311ZeroCovered⟩
def certified312 : CertifiedCover := ⟨cover312, cover312ZeroCovered⟩
def certified313 : CertifiedCover := ⟨cover313, cover313ZeroCovered⟩
def certified314 : CertifiedCover := ⟨cover314, cover314ZeroCovered⟩
def certified315 : CertifiedCover := ⟨cover315, cover315ZeroCovered⟩
def certified316 : CertifiedCover := ⟨cover316, cover316ZeroCovered⟩
def certified317 : CertifiedCover := ⟨cover317, cover317ZeroCovered⟩
def certified318 : CertifiedCover := ⟨cover318, cover318ZeroCovered⟩
def certified319 : CertifiedCover := ⟨cover319, cover319ZeroCovered⟩
def certified320 : CertifiedCover := ⟨cover320, cover320ZeroCovered⟩
def certified321 : CertifiedCover := ⟨cover321, cover321ZeroCovered⟩
def certified322 : CertifiedCover := ⟨cover322, cover322ZeroCovered⟩
def certified323 : CertifiedCover := ⟨cover323, cover323ZeroCovered⟩
def certified324 : CertifiedCover := ⟨cover324, cover324ZeroCovered⟩
def certified325 : CertifiedCover := ⟨cover325, cover325ZeroCovered⟩
def certified326 : CertifiedCover := ⟨cover326, cover326ZeroCovered⟩
def certified327 : CertifiedCover := ⟨cover327, cover327ZeroCovered⟩
def certified328 : CertifiedCover := ⟨cover328, cover328ZeroCovered⟩
def certified329 : CertifiedCover := ⟨cover329, cover329ZeroCovered⟩
def certified330 : CertifiedCover := ⟨cover330, cover330ZeroCovered⟩
def certified331 : CertifiedCover := ⟨cover331, cover331ZeroCovered⟩
def certified332 : CertifiedCover := ⟨cover332, cover332ZeroCovered⟩
def certified333 : CertifiedCover := ⟨cover333, cover333ZeroCovered⟩
def certified334 : CertifiedCover := ⟨cover334, cover334ZeroCovered⟩
def certified335 : CertifiedCover := ⟨cover335, cover335ZeroCovered⟩
def certified336 : CertifiedCover := ⟨cover336, cover336ZeroCovered⟩
def certified337 : CertifiedCover := ⟨cover337, cover337ZeroCovered⟩
def certified338 : CertifiedCover := ⟨cover338, cover338ZeroCovered⟩
def certified339 : CertifiedCover := ⟨cover339, cover339ZeroCovered⟩
def certified340 : CertifiedCover := ⟨cover340, cover340ZeroCovered⟩
def certified341 : CertifiedCover := ⟨cover341, cover341ZeroCovered⟩
def certified342 : CertifiedCover := ⟨cover342, cover342ZeroCovered⟩
def certified343 : CertifiedCover := ⟨cover343, cover343ZeroCovered⟩
def certified344 : CertifiedCover := ⟨cover344, cover344ZeroCovered⟩
def certified345 : CertifiedCover := ⟨cover345, cover345ZeroCovered⟩
def certified346 : CertifiedCover := ⟨cover346, cover346ZeroCovered⟩
def certified347 : CertifiedCover := ⟨cover347, cover347ZeroCovered⟩
def certified348 : CertifiedCover := ⟨cover348, cover348ZeroCovered⟩
def certified349 : CertifiedCover := ⟨cover349, cover349ZeroCovered⟩
def certified350 : CertifiedCover := ⟨cover350, cover350ZeroCovered⟩
def certified351 : CertifiedCover := ⟨cover351, cover351ZeroCovered⟩
def certified352 : CertifiedCover := ⟨cover352, cover352ZeroCovered⟩
def certified353 : CertifiedCover := ⟨cover353, cover353ZeroCovered⟩
def certified354 : CertifiedCover := ⟨cover354, cover354ZeroCovered⟩
def certified355 : CertifiedCover := ⟨cover355, cover355ZeroCovered⟩
def certified356 : CertifiedCover := ⟨cover356, cover356ZeroCovered⟩
def certified357 : CertifiedCover := ⟨cover357, cover357ZeroCovered⟩
def certified358 : CertifiedCover := ⟨cover358, cover358ZeroCovered⟩
def certified359 : CertifiedCover := ⟨cover359, cover359ZeroCovered⟩
def certified360 : CertifiedCover := ⟨cover360, cover360ZeroCovered⟩
def certified361 : CertifiedCover := ⟨cover361, cover361ZeroCovered⟩
def certified362 : CertifiedCover := ⟨cover362, cover362ZeroCovered⟩
def certified363 : CertifiedCover := ⟨cover363, cover363ZeroCovered⟩
def certified364 : CertifiedCover := ⟨cover364, cover364ZeroCovered⟩
def certified365 : CertifiedCover := ⟨cover365, cover365ZeroCovered⟩
def certified366 : CertifiedCover := ⟨cover366, cover366ZeroCovered⟩
def certified367 : CertifiedCover := ⟨cover367, cover367ZeroCovered⟩
def certified368 : CertifiedCover := ⟨cover368, cover368ZeroCovered⟩
def certified369 : CertifiedCover := ⟨cover369, cover369ZeroCovered⟩
def certified370 : CertifiedCover := ⟨cover370, cover370ZeroCovered⟩
def certified371 : CertifiedCover := ⟨cover371, cover371ZeroCovered⟩
def certified372 : CertifiedCover := ⟨cover372, cover372ZeroCovered⟩
def certified373 : CertifiedCover := ⟨cover373, cover373ZeroCovered⟩
def certified374 : CertifiedCover := ⟨cover374, cover374ZeroCovered⟩
def certified375 : CertifiedCover := ⟨cover375, cover375ZeroCovered⟩
def certified376 : CertifiedCover := ⟨cover376, cover376ZeroCovered⟩
def certified377 : CertifiedCover := ⟨cover377, cover377ZeroCovered⟩
def certified378 : CertifiedCover := ⟨cover378, cover378ZeroCovered⟩
def certified379 : CertifiedCover := ⟨cover379, cover379ZeroCovered⟩
def certified380 : CertifiedCover := ⟨cover380, cover380ZeroCovered⟩
def certified381 : CertifiedCover := ⟨cover381, cover381ZeroCovered⟩
def certified382 : CertifiedCover := ⟨cover382, cover382ZeroCovered⟩
def certified383 : CertifiedCover := ⟨cover383, cover383ZeroCovered⟩
def certified384 : CertifiedCover := ⟨cover384, cover384ZeroCovered⟩
def certified385 : CertifiedCover := ⟨cover385, cover385ZeroCovered⟩
def certified386 : CertifiedCover := ⟨cover386, cover386ZeroCovered⟩
def certified387 : CertifiedCover := ⟨cover387, cover387ZeroCovered⟩
def certified388 : CertifiedCover := ⟨cover388, cover388ZeroCovered⟩
def certified389 : CertifiedCover := ⟨cover389, cover389ZeroCovered⟩
def certified390 : CertifiedCover := ⟨cover390, cover390ZeroCovered⟩
def certified391 : CertifiedCover := ⟨cover391, cover391ZeroCovered⟩
def certified392 : CertifiedCover := ⟨cover392, cover392ZeroCovered⟩
def certified393 : CertifiedCover := ⟨cover393, cover393ZeroCovered⟩
def certified394 : CertifiedCover := ⟨cover394, cover394ZeroCovered⟩

theorem feasibleHasCertifiedCover (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern) :
    ∃ certificate : CertifiedCover,
      activeMatchesProp certificate.data.active pattern := by
  obtain ⟨certificate, activePattern⟩ :=
    CollapseSupportCover.feasibleHasCertifiedCover pattern feasiblePattern
  exact ⟨⟨coverOfBase certificate.data, zeroCoveredOfBase certificate⟩, activePattern⟩

theorem everyFeasiblePatternCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern) :
    ∃ cover : ActiveCover, activeMatchesProp cover.active pattern ∧
      ∃ stratum ∈ cover.strata, zeroMatchesProp stratum.zero pattern := by
  obtain ⟨certificate, activePattern⟩ :=
    feasibleHasCertifiedCover pattern feasiblePattern
  exact ⟨certificate.data, activePattern,
    certificate.zeroCovered pattern feasiblePattern activePattern⟩

end Krenn.CollapseSupportCoverData

#print axioms Krenn.CollapseSupportCoverData.everyFeasiblePatternCovered
