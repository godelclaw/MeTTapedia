import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitProofDagReduction

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagData

open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Global-color-orbit Kempe proof DAG for classical catalogue configuration
`cf020`. -/
def twentiethCatalogueOrbitProofDagCodeNodeChunk000 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 10, rule := .member 197092339144 },
  { wordCode := 28, rule := .member 111192993224 },
  { wordCode := 40, rule := .member 163684913716 },
  { wordCode := 44, rule := .member 167979881012 },
  { wordCode := 52, rule := .member 237451396962 },
  { wordCode := 82, rule := .member 108173094344 },
  { wordCode := 94, rule := .member 166704812596 },
  { wordCode := 98, rule := .member 170999779892 },
  { wordCode := 106, rule := .member 255637882481 },
  { wordCode := 112, rule := .member 132345074228 },
  { wordCode := 116, rule := .member 119461220916 },
  { wordCode := 128, rule := .member 246740121996 },
  { wordCode := 146, rule := .member 195200514444 },
  { wordCode := 154, rule := .member 245476764891 },
  { wordCode := 244, rule := .member 107903593691 },
  { wordCode := 256, rule := .member 166974296628 },
  { wordCode := 260, rule := .member 171269263924 },
  { wordCode := 266, rule := .member 234900194931 },
  { wordCode := 278, rule := .member 119729656372 },
  { wordCode := 302, rule := .member 131820979825 },
  { wordCode := 374, rule := .member 233826453107 },
  { wordCode := 380, rule := .member 109770930572 },
  { wordCode := 392, rule := .member 165106976371 },
  { wordCode := 404, rule := .member 254014493236 },
  { wordCode := 434, rule := .member 127957432716 },
  { wordCode := 446, rule := .member 198460081777 },
  { wordCode := 458, rule := .member 237841257012 },
  { wordCode := 460, rule := .member 110051077339 },
  { wordCode := 472, rule := .member 164826812980 },
  { wordCode := 476, rule := .member 169121780276 },
  { wordCode := 838, rule := .member 110876323272 },
  { wordCode := 850, rule := .member 164001583671 },
  { wordCode := 854, rule := .member 168296567590 },
  { wordCode := 902, rule := .member 196594071948 },
  { wordCode := 910, rule := .member 247241534920 },
  { wordCode := 946, rule := .member 109802581448 },
  { wordCode := 958, rule := .member 165075325495 },
  { wordCode := 962, rule := .member 169370309414 },
  { wordCode := 982, rule := .member 197042007496 },
  { wordCode := 1000, rule := .member 111142661576 },
  { wordCode := 1012, rule := .member 163735245364 },
  { wordCode := 1016, rule := .member 168030212660 },
  { wordCode := 1024, rule := .member 237468174178 },
  { wordCode := 1028, rule := .member 127539050892 },
  { wordCode := 1048, rule := .member 232385516087 },
  { wordCode := 1052, rule := .member 236680500006 },
  { wordCode := 1054, rule := .member 108122762696 },
  { wordCode := 1066, rule := .member 166755144244 },
  { wordCode := 1070, rule := .member 171050111540 },
  { wordCode := 1078, rule := .member 255654659697 },
  { wordCode := 1084, rule := .member 132395405876 },
  { wordCode := 1118, rule := .member 195184785804 },
  { wordCode := 1126, rule := .member 245429595592 },
  { wordCode := 1136, rule := .member 125523671198 },
  { wordCode := 1156, rule := .member 234400879156 },
  { wordCode := 1160, rule := .member 238695846452 },
  { wordCode := 1172, rule := .member 194178152844 },
  { wordCode := 1180, rule := .member 246434131400 },
  { wordCode := 1192, rule := .member 131321664052 },
  { wordCode := 1198, rule := .member 194894523848 },
  { wordCode := 1226, rule := .member 197128829086 },
  { wordCode := 1234, rule := .member 247776308680 },
  { wordCode := 1270, rule := .member 110337355208 },
  { wordCode := 1282, rule := .member 164540551732 },
  { wordCode := 1286, rule := .member 168835519028 },
  { wordCode := 1294, rule := .member 236662867810 },
  { wordCode := 1312, rule := .member 171030398818 },
  { wordCode := 1330, rule := .member 119490774641 },
  { wordCode := 1334, rule := .member 193907603614 },
  { wordCode := 1342, rule := .member 246702566856 },
  { wordCode := 1360, rule := .member 195162959304 },
  { wordCode := 1378, rule := .member 125503958472 },
  { wordCode := 1390, rule := .member 200913556020 },
  { wordCode := 1402, rule := .member 238676133730 },
  { wordCode := 1438, rule := .member 118417032817 },
  { wordCode := 2200, rule := .member 201386480420 },
  { wordCode := 2212, rule := .member 256469403249 },
  { wordCode := 2218, rule := .member 132667003684 },
  { wordCode := 2222, rule := .member 119782101796 },
  { wordCode := 2276, rule := .member 116762202916 },
  { wordCode := 2354, rule := .member 129834976881 },
  { wordCode := 2390, rule := .member 198487344753 },
  { wordCode := 2402, rule := .member 255073571620 },
  { wordCode := 2416, rule := .member 199238996772 },
  { wordCode := 2678, rule := .member 129298105969 },
  { wordCode := 2680, rule := .member 116480312945 },
  { wordCode := 2816, rule := .member 118372815652 },
  { wordCode := 2866, rule := .member 132264350500 },
  { wordCode := 2972, rule := .member 127542196622 },
  { wordCode := 2992, rule := .member 232342541092 },
  { wordCode := 2996, rule := .member 236637508388 },
  { wordCode := 2998, rule := .member 108167834843 },
  { wordCode := 3010, rule := .member 166710072100 },
  { wordCode := 3014, rule := .member 171005039396 },
  { wordCode := 3032, rule := .member 119465431844 },
  { wordCode := 3062, rule := .member 195187931534 },
  { wordCode := 3070, rule := .member 245472570587 },
  { wordCode := 3080, rule := .member 125528930702 },
  { wordCode := 3092, rule := .member 200888583793 },
  { wordCode := 3100, rule := .member 234355807012 },
  { wordCode := 3104, rule := .member 238650774308 },
  { wordCode := 3140, rule := .member 118391690020 },
  { wordCode := 3160, rule := .member 107899399387 },
  { wordCode := 3172, rule := .member 166978507556 },
  { wordCode := 3176, rule := .member 171273474852 },
  { wordCode := 3184, rule := .member 256452626033 },
  { wordCode := 3190, rule := .member 132616672036 },
  { wordCode := 3194, rule := .member 119731770148 },
  { wordCode := 3218, rule := .member 131833562737 },
  { wordCode := 3248, rule := .member 116711871268 },
  { wordCode := 3308, rule := .member 199479297649 },
  { wordCode := 3320, rule := .member 254018704164 },
  { wordCode := 3326, rule := .member 129818199665 },
  { wordCode := 3350, rule := .member 127944849806 },
  { wordCode := 3362, rule := .member 198470567537 },
  { wordCode := 3370, rule := .member 233550500644 },
  { wordCode := 3374, rule := .member 237845467940 },
  { wordCode := 3376, rule := .member 110046883035 },
  { wordCode := 3392, rule := .member 169125991204 },
  { wordCode := 3416, rule := .member 201423357553 },
  { wordCode := 3428, rule := .member 256365417252 },
  { wordCode := 3460, rule := .member 131811365668 },
  { wordCode := 3464, rule := .member 118926463780 },
  { wordCode := 3490, rule := .member 116731971185 },
  { wordCode := 3536, rule := .member 255291675428 },
  { wordCode := 3550, rule := .member 199457100580 },
  { wordCode := 3656, rule := .member 197083756942 },
  { wordCode := 3664, rule := .member 247871712475 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk001 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 3674, rule := .member 128364280206 },
  { wordCode := 3694, rule := .member 233164624676 },
  { wordCode := 3698, rule := .member 237459591972 },
  { wordCode := 3740, rule := .member 201073133169 },
  { wordCode := 3752, rule := .member 255646094116 },
  { wordCode := 3758, rule := .member 132353656433 },
  { wordCode := 3866, rule := .member 131279914609 },
  { wordCode := 3872, rule := .member 194936273294 },
  { wordCode := 3880, rule := .member 245724228827 },
  { wordCode := 4132, rule := .member 107882622171 },
  { wordCode := 4144, rule := .member 166995284772 },
  { wordCode := 4148, rule := .member 171290252068 },
  { wordCode := 4166, rule := .member 119750644516 },
  { wordCode := 4190, rule := .member 131816785521 },
  { wordCode := 4280, rule := .member 199462520433 },
  { wordCode := 4292, rule := .member 254035481380 },
  { wordCode := 4322, rule := .member 127961627022 },
  { wordCode := 4334, rule := .member 198455887473 },
  { wordCode := 4346, rule := .member 237862245156 },
  { wordCode := 4364, rule := .member 169142768420 },
  { wordCode := 6652, rule := .member 196769672648 },
  { wordCode := 6670, rule := .member 110871375304 },
  { wordCode := 6682, rule := .member 164006531879 },
  { wordCode := 6694, rule := .member 238283147106 },
  { wordCode := 6742, rule := .member 247236586952 },
  { wordCode := 6778, rule := .member 109797633480 },
  { wordCode := 6790, rule := .member 165080273703 },
  { wordCode := 6802, rule := .member 237209405282 },
  { wordCode := 6832, rule := .member 111139810760 },
  { wordCode := 6844, rule := .member 163738096423 },
  { wordCode := 6880, rule := .member 232390464295 },
  { wordCode := 6958, rule := .member 245424647624 },
  { wordCode := 7012, rule := .member 246431280584 },
  { wordCode := 7090, rule := .member 168020166498 },
  { wordCode := 7102, rule := .member 127513325000 },
  { wordCode := 7192, rule := .member 195159059912 },
  { wordCode := 7624, rule := .member 196820004296 },
  { wordCode := 7642, rule := .member 128100527560 },
  { wordCode := 7666, rule := .member 238266369890 },
  { wordCode := 7900, rule := .member 168271824738 },
  { wordCode := 7948, rule := .member 196618677704 },
  { wordCode := 8008, rule := .member 169345566562 },
  { wordCode := 8362, rule := .member 247068814792 },
  { wordCode := 8392, rule := .member 233967522599 },
  { wordCode := 8614, rule := .member 110904929736 },
  { wordCode := 8626, rule := .member 163972977447 },
  { wordCode := 8686, rule := .member 247270141384 },
  { wordCode := 8722, rule := .member 109831187912 },
  { wordCode := 8758, rule := .member 197091552712 },
  { wordCode := 8768, rule := .member 247813618060 },
  { wordCode := 8776, rule := .member 111192206792 },
  { wordCode := 8788, rule := .member 163685700148 },
  { wordCode := 8792, rule := .member 167980667444 },
  { wordCode := 8800, rule := .member 237451626338 },
  { wordCode := 8804, rule := .member 110374664588 },
  { wordCode := 8816, rule := .member 164503242595 },
  { wordCode := 8824, rule := .member 232339116596 },
  { wordCode := 8828, rule := .member 236634083892 },
  { wordCode := 8830, rule := .member 108172307912 },
  { wordCode := 8842, rule := .member 166705599028 },
  { wordCode := 8846, rule := .member 171000566324 },
  { wordCode := 8854, rule := .member 255638161249 },
  { wordCode := 8860, rule := .member 132345860660 },
  { wordCode := 8864, rule := .member 119462007348 },
  { wordCode := 8876, rule := .member 246739876236 },
  { wordCode := 8894, rule := .member 195200268684 },
  { wordCode := 8902, rule := .member 245475995083 },
  { wordCode := 8912, rule := .member 125541267852 },
  { wordCode := 8924, rule := .member 200876279649 },
  { wordCode := 8932, rule := .member 234351333940 },
  { wordCode := 8936, rule := .member 238646301236 },
  { wordCode := 8948, rule := .member 194192554142 },
  { wordCode := 8956, rule := .member 246483676616 },
  { wordCode := 8968, rule := .member 131272118836 },
  { wordCode := 8972, rule := .member 118388265524 },
  { wordCode := 8974, rule := .member 194944069064 },
  { wordCode := 8992, rule := .member 107902823883 },
  { wordCode := 9004, rule := .member 166975083060 },
  { wordCode := 9008, rule := .member 171270050356 },
  { wordCode := 9014, rule := .member 234900440931 },
  { wordCode := 9026, rule := .member 119730442804 },
  { wordCode := 9050, rule := .member 131821258593 },
  { wordCode := 9122, rule := .member 233826699107 },
  { wordCode := 9128, rule := .member 109770684812 },
  { wordCode := 9140, rule := .member 165107222371 },
  { wordCode := 9152, rule := .member 254015279668 },
  { wordCode := 9182, rule := .member 127957186956 },
  { wordCode := 9194, rule := .member 198460360545 },
  { wordCode := 9202, rule := .member 233547076148 },
  { wordCode := 9206, rule := .member 237842043444 },
  { wordCode := 9208, rule := .member 110050307531 },
  { wordCode := 9220, rule := .member 164827599412 },
  { wordCode := 9224, rule := .member 169122566708 },
  { wordCode := 9236, rule := .member 125003315358 },
  { wordCode := 9250, rule := .member 171282286434 },
  { wordCode := 9256, rule := .member 234888204852 },
  { wordCode := 9260, rule := .member 239183172148 },
  { wordCode := 9268, rule := .member 119742711649 },
  { wordCode := 9292, rule := .member 131808989748 },
  { wordCode := 9344, rule := .member 128224540830 },
  { wordCode := 9368, rule := .member 238109430324 },
  { wordCode := 9370, rule := .member 109782920648 },
  { wordCode := 9382, rule := .member 165094986292 },
  { wordCode := 9386, rule := .member 169389953588 },
  { wordCode := 9394, rule := .member 254027548513 },
  { wordCode := 9424, rule := .member 127969422792 },
  { wordCode := 9436, rule := .member 198448091700 },
  { wordCode := 9448, rule := .member 237854279522 },
  { wordCode := 9586, rule := .member 110875536840 },
  { wordCode := 9598, rule := .member 164002337575 },
  { wordCode := 9602, rule := .member 168297304870 },
  { wordCode := 9650, rule := .member 196593826188 },
  { wordCode := 9658, rule := .member 247240748488 },
  { wordCode := 9694, rule := .member 109801795016 },
  { wordCode := 9710, rule := .member 169371046694 },
  { wordCode := 9730, rule := .member 197041221064 },
  { wordCode := 9748, rule := .member 111141875144 },
  { wordCode := 9760, rule := .member 163736031796 },
  { wordCode := 9764, rule := .member 168030999092 },
  { wordCode := 9772, rule := .member 237468403554 },
  { wordCode := 9776, rule := .member 127538805132 },
  { wordCode := 9796, rule := .member 232386269991 },
  { wordCode := 9800, rule := .member 236681237286 },
  { wordCode := 9802, rule := .member 108121976264 },
  { wordCode := 9814, rule := .member 166755930676 },
  { wordCode := 9818, rule := .member 171050897972 },
  { wordCode := 9826, rule := .member 255654938465 },
  { wordCode := 9832, rule := .member 132396192308 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk002 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 9866, rule := .member 195184540044 },
  { wordCode := 9874, rule := .member 245428809160 },
  { wordCode := 9884, rule := .member 125523409054 },
  { wordCode := 9904, rule := .member 234401665588 },
  { wordCode := 9908, rule := .member 238696632884 },
  { wordCode := 9920, rule := .member 194177907084 },
  { wordCode := 9940, rule := .member 131322450484 },
  { wordCode := 9946, rule := .member 194893737416 },
  { wordCode := 9974, rule := .member 197128566942 },
  { wordCode := 9982, rule := .member 247775522248 },
  { wordCode := 10018, rule := .member 110336568776 },
  { wordCode := 10030, rule := .member 164541338164 },
  { wordCode := 10034, rule := .member 168836305460 },
  { wordCode := 10042, rule := .member 236663097186 },
  { wordCode := 10060, rule := .member 171030628194 },
  { wordCode := 10082, rule := .member 193907341470 },
  { wordCode := 10090, rule := .member 246701780424 },
  { wordCode := 10108, rule := .member 195162172872 },
  { wordCode := 10126, rule := .member 125503172040 },
  { wordCode := 10138, rule := .member 200914342452 },
  { wordCode := 10186, rule := .member 118417311585 },
  { wordCode := 10298, rule := .member 196778375564 },
  { wordCode := 10306, rule := .member 247056199112 },
  { wordCode := 10316, rule := .member 128058898828 },
  { wordCode := 10340, rule := .member 238275072806 },
  { wordCode := 10424, rule := .member 126985157004 },
  { wordCode := 10444, rule := .member 232906363687 },
  { wordCode := 10448, rule := .member 237201330982 },
  { wordCode := 10460, rule := .member 197045762444 },
  { wordCode := 10478, rule := .member 111146416524 },
  { wordCode := 10490, rule := .member 163731490659 },
  { wordCode := 10498, rule := .member 233177977396 },
  { wordCode := 10502, rule := .member 237472944692 },
  { wordCode := 10532, rule := .member 108126517644 },
  { wordCode := 10544, rule := .member 166751389539 },
  { wordCode := 10556, rule := .member 255659446836 },
  { wordCode := 10562, rule := .member 132391683937 },
  { wordCode := 10634, rule := .member 234397124451 },
  { wordCode := 10658, rule := .member 246437886348 },
  { wordCode := 10670, rule := .member 131317942113 },
  { wordCode := 10676, rule := .member 194898278796 },
  { wordCode := 10684, rule := .member 245710876107 },
  { wordCode := 10712, rule := .member 247780063628 },
  { wordCode := 10720, rule := .member 111160749512 },
  { wordCode := 10732, rule := .member 163717124903 },
  { wordCode := 10736, rule := .member 168012092198 },
  { wordCode := 10748, rule := .member 110341110156 },
  { wordCode := 10760, rule := .member 164536797027 },
  { wordCode := 10772, rule := .member 236667638324 },
  { wordCode := 10774, rule := .member 108137704907 },
  { wordCode := 10786, rule := .member 166740202036 },
  { wordCode := 10790, rule := .member 171035169332 },
  { wordCode := 10808, rule := .member 119495561780 },
  { wordCode := 10820, rule := .member 246706321804 },
  { wordCode := 10838, rule := .member 195166714252 },
  { wordCode := 10856, rule := .member 125507713420 },
  { wordCode := 10868, rule := .member 200909834081 },
  { wordCode := 10876, rule := .member 234385936948 },
  { wordCode := 10880, rule := .member 238680904244 },
  { wordCode := 10892, rule := .member 194161129868 },
  { wordCode := 10900, rule := .member 246452219336 },
  { wordCode := 10916, rule := .member 118421819956 },
  { wordCode := 10954, rule := .member 247813270984 },
  { wordCode := 10990, rule := .member 110374317512 },
  { wordCode := 11002, rule := .member 164503589431 },
  { wordCode := 11014, rule := .member 236633769826 },
  { wordCode := 11032, rule := .member 171001300834 },
  { wordCode := 11062, rule := .member 246739529160 },
  { wordCode := 11080, rule := .member 195199921608 },
  { wordCode := 11098, rule := .member 125540920776 },
  { wordCode := 11122, rule := .member 238647035746 },
  { wordCode := 11194, rule := .member 171269736290 },
  { wordCode := 11200, rule := .member 234900787767 },
  { wordCode := 11308, rule := .member 233827045943 },
  { wordCode := 11314, rule := .member 109770337736 },
  { wordCode := 11368, rule := .member 127956839880 },
  { wordCode := 11788, rule := .member 168297023330 },
  { wordCode := 11836, rule := .member 196593479112 },
  { wordCode := 11896, rule := .member 169370765154 },
  { wordCode := 11962, rule := .member 127538458056 },
  { wordCode := 11986, rule := .member 236680955746 },
  { wordCode := 12052, rule := .member 195184192968 },
  { wordCode := 12106, rule := .member 194177560008 },
  { wordCode := 12484, rule := .member 196778028488 },
  { wordCode := 12502, rule := .member 128058551752 },
  { wordCode := 12526, rule := .member 238274791266 },
  { wordCode := 12610, rule := .member 126984809928 },
  { wordCode := 12634, rule := .member 237201049442 },
  { wordCode := 12646, rule := .member 197045415368 },
  { wordCode := 12664, rule := .member 111146069448 },
  { wordCode := 12676, rule := .member 163731837495 },
  { wordCode := 12688, rule := .member 237472630626 },
  { wordCode := 12718, rule := .member 108126170568 },
  { wordCode := 12730, rule := .member 166751736375 },
  { wordCode := 12820, rule := .member 234397471287 },
  { wordCode := 12844, rule := .member 246437539272 },
  { wordCode := 12862, rule := .member 194897931720 },
  { wordCode := 12898, rule := .member 247779716552 },
  { wordCode := 12922, rule := .member 168011810658 },
  { wordCode := 12934, rule := .member 110340763080 },
  { wordCode := 12946, rule := .member 164537143863 },
  { wordCode := 12958, rule := .member 236664178530 },
  { wordCode := 12976, rule := .member 171034855266 },
  { wordCode := 13006, rule := .member 246705974728 },
  { wordCode := 13024, rule := .member 195166367176 },
  { wordCode := 13042, rule := .member 125507366344 },
  { wordCode := 13066, rule := .member 238680590178 },
  { wordCode := 13078, rule := .member 194160782792 },
  { wordCode := 19696, rule := .member 201453343261 },
  { wordCode := 19708, rule := .member 256403785544 },
  { wordCode := 19710, rule := .member 111192970011 },
  { wordCode := 19722, rule := .member 163684936932 },
  { wordCode := 19742, rule := .member 131849733708 },
  { wordCode := 19758, rule := .member 232338353380 },
  { wordCode := 19764, rule := .member 108172022555 },
  { wordCode := 19772, rule := .member 116761957145 },
  { wordCode := 19774, rule := .member 196769607112 },
  { wordCode := 19776, rule := .member 166704835812 },
  { wordCode := 19788, rule := .member 255637895601 },
  { wordCode := 19792, rule := .member 110871309768 },
  { wordCode := 19794, rule := .member 132345097444 },
  { wordCode := 19804, rule := .member 164006597175 },
  { wordCode := 19816, rule := .member 238283343714 },
  { wordCode := 19832, rule := .member 199495468620 },
  { wordCode := 19836, rule := .member 245476758299 },
  { wordCode := 19844, rule := .member 254066692889 },
  { wordCode := 19850, rule := .member 129836467788 },
  { wordCode := 19864, rule := .member 247236521416 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk003 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 19866, rule := .member 234350570724 },
  { wordCode := 19890, rule := .member 246484439835 },
  { wordCode := 19900, rule := .member 109797567944 },
  { wordCode := 19902, rule := .member 131271355620 },
  { wordCode := 19912, rule := .member 165080338999 },
  { wordCode := 19924, rule := .member 237209601890 },
  { wordCode := 19926, rule := .member 107903587099 },
  { wordCode := 19930, rule := .member 129311314461 },
  { wordCode := 19934, rule := .member 116493521689 },
  { wordCode := 19938, rule := .member 166974319844 },
  { wordCode := 19954, rule := .member 111139745224 },
  { wordCode := 19966, rule := .member 163738161719 },
  { wordCode := 20002, rule := .member 232390529591 },
  { wordCode := 20038, rule := .member 132532539933 },
  { wordCode := 20080, rule := .member 245424582088 },
  { wordCode := 20120, rule := .member 132252386892 },
  { wordCode := 20134, rule := .member 246431215048 },
  { wordCode := 20136, rule := .member 233546312932 },
  { wordCode := 20142, rule := .member 110051070747 },
  { wordCode := 20154, rule := .member 164826836196 },
  { wordCode := 20190, rule := .member 234887441636 },
  { wordCode := 20202, rule := .member 119742446001 },
  { wordCode := 20212, rule := .member 168020363106 },
  { wordCode := 20224, rule := .member 127513259464 },
  { wordCode := 20226, rule := .member 131808226532 },
  { wordCode := 20298, rule := .member 233813699812 },
  { wordCode := 20304, rule := .member 109783683867 },
  { wordCode := 20314, rule := .member 195158994376 },
  { wordCode := 20316, rule := .member 165094223076 },
  { wordCode := 20328, rule := .member 254027282865 },
  { wordCode := 20368, rule := .member 194152361416 },
  { wordCode := 20370, rule := .member 198447328484 },
  { wordCode := 20382, rule := .member 255033915825 },
  { wordCode := 20422, rule := .member 197153385954 },
  { wordCode := 20432, rule := .member 247800838579 },
  { wordCode := 20468, rule := .member 110361885107 },
  { wordCode := 20480, rule := .member 164516021836 },
  { wordCode := 20528, rule := .member 119466234649 },
  { wordCode := 20530, rule := .member 193932160482 },
  { wordCode := 20540, rule := .member 246727096755 },
  { wordCode := 20588, rule := .member 200889026124 },
  { wordCode := 20600, rule := .member 255831446297 },
  { wordCode := 20636, rule := .member 118392492825 },
  { wordCode := 20656, rule := .member 125011357154 },
  { wordCode := 20680, rule := .member 239208187720 },
  { wordCode := 20682, rule := .member 111142638363 },
  { wordCode := 20690, rule := .member 119734670105 },
  { wordCode := 20694, rule := .member 163735268580 },
  { wordCode := 20714, rule := .member 131834005068 },
  { wordCode := 20736, rule := .member 108122739483 },
  { wordCode := 20746, rule := .member 196819938760 },
  { wordCode := 20748, rule := .member 166755167460 },
  { wordCode := 20760, rule := .member 255654672817 },
  { wordCode := 20764, rule := .member 128100462024 },
  { wordCode := 20766, rule := .member 132395429092 },
  { wordCode := 20788, rule := .member 238134445896 },
  { wordCode := 20792, rule := .member 109757905331 },
  { wordCode := 20804, rule := .member 165120001612 },
  { wordCode := 20816, rule := .member 254019506969 },
  { wordCode := 20838, rule := .member 234400902372 },
  { wordCode := 20858, rule := .member 198473107020 },
  { wordCode := 20862, rule := .member 246434108187 },
  { wordCode := 20870, rule := .member 255026139929 },
  { wordCode := 20872, rule := .member 127026720200 },
  { wordCode := 20874, rule := .member 131321687268 },
  { wordCode := 20896, rule := .member 237192824674 },
  { wordCode := 20916, rule := .member 247776285467 },
  { wordCode := 20952, rule := .member 110337331995 },
  { wordCode := 20964, rule := .member 164540574948 },
  { wordCode := 21012, rule := .member 119490787761 },
  { wordCode := 21070, rule := .member 196618612168 },
  { wordCode := 21084, rule := .member 255855999409 },
  { wordCode := 21120, rule := .member 118417045937 },
  { wordCode := 21170, rule := .member 111183968691 },
  { wordCode := 21182, rule := .member 163693938252 },
  { wordCode := 21224, rule := .member 108164069811 },
  { wordCode := 21236, rule := .member 166713837132 },
  { wordCode := 21248, rule := .member 255646896921 },
  { wordCode := 21254, rule := .member 132354098764 },
  { wordCode := 21326, rule := .member 234359572044 },
  { wordCode := 21328, rule := .member 238654539592 },
  { wordCode := 21350, rule := .member 246475438515 },
  { wordCode := 21362, rule := .member 131280356940 },
  { wordCode := 21398, rule := .member 201340962380 },
  { wordCode := 21402, rule := .member 247859122971 },
  { wordCode := 21410, rule := .member 256449057561 },
  { wordCode := 21416, rule := .member 132621485644 },
  { wordCode := 21432, rule := .member 233177214180 },
  { wordCode := 21484, rule := .member 247068749256 },
  { wordCode := 21514, rule := .member 233967587895 },
  { wordCode := 21598, rule := .member 255028053832 },
  { wordCode := 21614, rule := .member 199193478732 },
  { wordCode := 21618, rule := .member 245711639323 },
  { wordCode := 21622, rule := .member 232893846071 },
  { wordCode := 21626, rule := .member 254301573913 },
  { wordCode := 21628, rule := .member 124994579938 },
  { wordCode := 21640, rule := .member 201419788829 },
  { wordCode := 21650, rule := .member 234896442956 },
  { wordCode := 21652, rule := .member 239191410504 },
  { wordCode := 21662, rule := .member 119751447321 },
  { wordCode := 21686, rule := .member 131816179276 },
  { wordCode := 21688, rule := .member 118931277640 },
  { wordCode := 21702, rule := .member 232371907812 },
  { wordCode := 21708, rule := .member 108138468123 },
  { wordCode := 21716, rule := .member 116728402713 },
  { wordCode := 21720, rule := .member 166739438820 },
  { wordCode := 21736, rule := .member 110904864200 },
  { wordCode := 21748, rule := .member 163973042743 },
  { wordCode := 21758, rule := .member 233822701132 },
  { wordCode := 21760, rule := .member 238117668680 },
  { wordCode := 21764, rule := .member 109774682547 },
  { wordCode := 21776, rule := .member 165103224396 },
  { wordCode := 21778, rule := .member 169398191944 },
  { wordCode := 21780, rule := .member 245443203867 },
  { wordCode := 21788, rule := .member 254033138457 },
  { wordCode := 21794, rule := .member 129802913356 },
  { wordCode := 21810, rule := .member 234385173732 },
  { wordCode := 21830, rule := .member 198456329804 },
  { wordCode := 21842, rule := .member 255042917145 },
  { wordCode := 21844, rule := .member 109831122376 },
  { wordCode := 21856, rule := .member 165046784567 },
  { wordCode := 21880, rule := .member 197091519944 },
  { wordCode := 21882, rule := .member 201386487012 },
  { wordCode := 21890, rule := .member 247813421212 },
  { wordCode := 21894, rule := .member 256403355828 },
  { wordCode := 21898, rule := .member 111192174024 },
  { wordCode := 21900, rule := .member 132667010276 },
  { wordCode := 21910, rule := .member 163685732919 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk004 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 21922, rule := .member 237451822946 },
  { wordCode := 21926, rule := .member 110374467740 },
  { wordCode := 21938, rule := .member 164503439203 },
  { wordCode := 21950, rule := .member 236634116662 },
  { wordCode := 21952, rule := .member 108172275144 },
  { wordCode := 21964, rule := .member 166705631799 },
  { wordCode := 21968, rule := .member 171001647670 },
  { wordCode := 21990, rule := .member 198231322081 },
  { wordCode := 21998, rule := .member 246739679388 },
  { wordCode := 22002, rule := .member 255329614004 },
  { wordCode := 22016, rule := .member 195200071836 },
  { wordCode := 22034, rule := .member 125541071004 },
  { wordCode := 22054, rule := .member 234351366711 },
  { wordCode := 22058, rule := .member 238647382582 },
  { wordCode := 22078, rule := .member 246483643848 },
  { wordCode := 22096, rule := .member 194944036296 },
  { wordCode := 22098, rule := .member 199239003364 },
  { wordCode := 22110, rule := .member 254321932721 },
  { wordCode := 22116, rule := .member 129310518753 },
  { wordCode := 22130, rule := .member 171270083126 },
  { wordCode := 22136, rule := .member 234900637539 },
  { wordCode := 22224, rule := .member 132531744225 },
  { wordCode := 22244, rule := .member 233826895715 },
  { wordCode := 22250, rule := .member 109770487964 },
  { wordCode := 22304, rule := .member 127956990108 },
  { wordCode := 22362, rule := .member 116480326065 },
  { wordCode := 22372, rule := .member 171282483042 },
  { wordCode := 22378, rule := .member 234888237623 },
  { wordCode := 22486, rule := .member 233814495799 },
  { wordCode := 22492, rule := .member 109782887880 },
  { wordCode := 22504, rule := .member 165095019063 },
  { wordCode := 22546, rule := .member 127969390024 },
  { wordCode := 22570, rule := .member 237854476130 },
  { wordCode := 22578, rule := .member 118627809713 },
  { wordCode := 22588, rule := .member 169134999394 },
  { wordCode := 22608, rule := .member 197154181662 },
  { wordCode := 22674, rule := .member 232342547684 },
  { wordCode := 22680, rule := .member 108167828251 },
  { wordCode := 22692, rule := .member 166710078692 },
  { wordCode := 22708, rule := .member 110875504072 },
  { wordCode := 22716, rule := .member 193932956190 },
  { wordCode := 22720, rule := .member 164002402871 },
  { wordCode := 22724, rule := .member 168297370166 },
  { wordCode := 22752, rule := .member 245472563995 },
  { wordCode := 22772, rule := .member 196593629340 },
  { wordCode := 22780, rule := .member 247240715720 },
  { wordCode := 22782, rule := .member 234355813604 },
  { wordCode := 22816, rule := .member 109801762248 },
  { wordCode := 22828, rule := .member 165076144695 },
  { wordCode := 22842, rule := .member 107899392795 },
  { wordCode := 22852, rule := .member 197041188296 },
  { wordCode := 22854, rule := .member 166978514148 },
  { wordCode := 22866, rule := .member 239207758004 },
  { wordCode := 22870, rule := .member 111141842376 },
  { wordCode := 22872, rule := .member 132616678628 },
  { wordCode := 22882, rule := .member 163733967415 },
  { wordCode := 22886, rule := .member 168028934710 },
  { wordCode := 22894, rule := .member 237468600162 },
  { wordCode := 22898, rule := .member 127538608284 },
  { wordCode := 22918, rule := .member 232386335287 },
  { wordCode := 22922, rule := .member 236681302582 },
  { wordCode := 22924, rule := .member 108121943496 },
  { wordCode := 22936, rule := .member 166755963447 },
  { wordCode := 22950, rule := .member 128233378334 },
  { wordCode := 22974, rule := .member 238134016180 },
  { wordCode := 22988, rule := .member 195184343196 },
  { wordCode := 22996, rule := .member 245428776392 },
  { wordCode := 23026, rule := .member 234401698359 },
  { wordCode := 23042, rule := .member 194177710236 },
  { wordCode := 23050, rule := .member 246433312200 },
  { wordCode := 23052, rule := .member 233550507236 },
  { wordCode := 23058, rule := .member 110046876443 },
  { wordCode := 23068, rule := .member 194893704648 },
  { wordCode := 23070, rule := .member 164831030500 },
  { wordCode := 23082, rule := .member 254305155505 },
  { wordCode := 23104, rule := .member 247775489480 },
  { wordCode := 23140, rule := .member 110336536008 },
  { wordCode := 23142, rule := .member 131811372260 },
  { wordCode := 23152, rule := .member 164541370935 },
  { wordCode := 23172, rule := .member 116731984305 },
  { wordCode := 23182, rule := .member 171030824802 },
  { wordCode := 23212, rule := .member 246701747656 },
  { wordCode := 23230, rule := .member 195162140104 },
  { wordCode := 23232, rule := .member 199457107172 },
  { wordCode := 23248, rule := .member 125503139272 },
  { wordCode := 23272, rule := .member 238676559714 },
  { wordCode := 23346, rule := .member 247871705883 },
  { wordCode := 23376, rule := .member 233164631268 },
  { wordCode := 23420, rule := .member 196778178716 },
  { wordCode := 23428, rule := .member 247056166344 },
  { wordCode := 23438, rule := .member 128058701980 },
  { wordCode := 23458, rule := .member 233980170807 },
  { wordCode := 23462, rule := .member 238275138102 },
  { wordCode := 23514, rule := .member 238654109876 },
  { wordCode := 23546, rule := .member 126984960156 },
  { wordCode := 23562, rule := .member 245724222235 },
  { wordCode := 23566, rule := .member 232906428983 },
  { wordCode := 23570, rule := .member 237201396278 },
  { wordCode := 23582, rule := .member 197045565596 },
  { wordCode := 23600, rule := .member 111146219676 },
  { wordCode := 23612, rule := .member 163731687267 },
  { wordCode := 23624, rule := .member 237472977462 },
  { wordCode := 23666, rule := .member 166751586147 },
  { wordCode := 23756, rule := .member 234397321059 },
  { wordCode := 23780, rule := .member 246437689500 },
  { wordCode := 23784, rule := .member 255027624116 },
  { wordCode := 23798, rule := .member 194898081948 },
  { wordCode := 23814, rule := .member 107882615579 },
  { wordCode := 23826, rule := .member 166995291364 },
  { wordCode := 23834, rule := .member 247779866780 },
  { wordCode := 23838, rule := .member 239190980788 },
  { wordCode := 23842, rule := .member 111160716744 },
  { wordCode := 23854, rule := .member 163717190199 },
  { wordCode := 23858, rule := .member 168012157494 },
  { wordCode := 23870, rule := .member 110340913308 },
  { wordCode := 23874, rule := .member 118930847924 },
  { wordCode := 23882, rule := .member 164536993635 },
  { wordCode := 23890, rule := .member 232369558071 },
  { wordCode := 23894, rule := .member 236664525366 },
  { wordCode := 23912, rule := .member 171035202102 },
  { wordCode := 23922, rule := .member 128216601118 },
  { wordCode := 23934, rule := .member 198197767649 },
  { wordCode := 23942, rule := .member 246706124956 },
  { wordCode := 23946, rule := .member 238117238964 },
  { wordCode := 23960, rule := .member 195166517404 },
  { wordCode := 23964, rule := .member 169397762228 },
  { wordCode := 23968, rule := .member 245445553608 },
  { wordCode := 23978, rule := .member 125507516572 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk005 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 24002, rule := .member 238680937014 },
  { wordCode := 24022, rule := .member 246452186568 },
  { wordCode := 24030, rule := .member 110030099227 },
  { wordCode := 24042, rule := .member 164847807716 },
  { wordCode := 26288, rule := .member 167979963160 },
  { wordCode := 26300, rule := .member 127554582962 },
  { wordCode := 26324, rule := .member 236633379608 },
  { wordCode := 26334, rule := .member 196769665816 },
  { wordCode := 26352, rule := .member 110871368472 },
  { wordCode := 26360, rule := .member 119461303064 },
  { wordCode := 26364, rule := .member 164006538471 },
  { wordCode := 26376, rule := .member 238283159986 },
  { wordCode := 26390, rule := .member 195200317874 },
  { wordCode := 26408, rule := .member 125540268466 },
  { wordCode := 26420, rule := .member 200876197453 },
  { wordCode := 26424, rule := .member 247236580120 },
  { wordCode := 26432, rule := .member 238645596952 },
  { wordCode := 26444, rule := .member 194192636338 },
  { wordCode := 26460, rule := .member 109797626648 },
  { wordCode := 26468, rule := .member 118387561240 },
  { wordCode := 26472, rule := .member 165080280295 },
  { wordCode := 26484, rule := .member 237209418162 },
  { wordCode := 26504, rule := .member 171269346072 },
  { wordCode := 26514, rule := .member 111139803928 },
  { wordCode := 26526, rule := .member 163738103015 },
  { wordCode := 26546, rule := .member 131821176397 },
  { wordCode := 26562, rule := .member 232390470887 },
  { wordCode := 26636, rule := .member 199466911309 },
  { wordCode := 26640, rule := .member 245424640792 },
  { wordCode := 26648, rule := .member 254014575384 },
  { wordCode := 26678, rule := .member 127957236146 },
  { wordCode := 26690, rule := .member 198460278349 },
  { wordCode := 26694, rule := .member 246431273752 },
  { wordCode := 26702, rule := .member 237841339160 },
  { wordCode := 26720, rule := .member 169121862424 },
  { wordCode := 26732, rule := .member 125003397554 },
  { wordCode := 26756, rule := .member 239182467864 },
  { wordCode := 26772, rule := .member 168020179378 },
  { wordCode := 26784, rule := .member 127513318168 },
  { wordCode := 26874, rule := .member 195159053080 },
  { wordCode := 26928, rule := .member 194152420120 },
  { wordCode := 27260, rule := .member 168030294808 },
  { wordCode := 27306, rule := .member 196819997464 },
  { wordCode := 27314, rule := .member 171050193688 },
  { wordCode := 27324, rule := .member 128100520728 },
  { wordCode := 27348, rule := .member 238266382770 },
  { wordCode := 27380, rule := .member 125523491250 },
  { wordCode := 27404, rule := .member 238695928600 },
  { wordCode := 27416, rule := .member 194175859122 },
  { wordCode := 27432, rule := .member 127026778904 },
  { wordCode := 27456, rule := .member 237192640946 },
  { wordCode := 27470, rule := .member 197128649138 },
  { wordCode := 27530, rule := .member 168835601176 },
  { wordCode := 27578, rule := .member 193907423666 },
  { wordCode := 27582, rule := .member 168271837618 },
  { wordCode := 27630, rule := .member 196618670872 },
  { wordCode := 27690, rule := .member 169345579442 },
  { wordCode := 27956, rule := .member 197045811634 },
  { wordCode := 27974, rule := .member 128326334898 },
  { wordCode := 27998, rule := .member 237472240408 },
  { wordCode := 28040, rule := .member 201111078477 },
  { wordCode := 28044, rule := .member 247068807960 },
  { wordCode := 28052, rule := .member 255658742552 },
  { wordCode := 28058, rule := .member 132391601741 },
  { wordCode := 28074, rule := .member 233967529191 },
  { wordCode := 28166, rule := .member 131317859917 },
  { wordCode := 28172, rule := .member 194898327986 },
  { wordCode := 28182, rule := .member 232893787367 },
  { wordCode := 28244, rule := .member 127521028530 },
  { wordCode := 28268, rule := .member 236666934040 },
  { wordCode := 28286, rule := .member 171034465048 },
  { wordCode := 28296, rule := .member 110904922904 },
  { wordCode := 28308, rule := .member 163972984039 },
  { wordCode := 28334, rule := .member 195166763442 },
  { wordCode := 28352, rule := .member 125507762610 },
  { wordCode := 28364, rule := .member 200909751885 },
  { wordCode := 28368, rule := .member 247270134552 },
  { wordCode := 28376, rule := .member 238680199960 },
  { wordCode := 28404, rule := .member 109831181080 },
  { wordCode := 28416, rule := .member 165046725863 },
  { wordCode := 28440, rule := .member 197091578648 },
  { wordCode := 28458, rule := .member 111192232728 },
  { wordCode := 28466, rule := .member 119782167320 },
  { wordCode := 28470, rule := .member 163685674215 },
  { wordCode := 28482, rule := .member 237451639218 },
  { wordCode := 28490, rule := .member 131849487948 },
  { wordCode := 28512, rule := .member 108172333848 },
  { wordCode := 28520, rule := .member 116762268440 },
  { wordCode := 28524, rule := .member 166705573095 },
  { wordCode := 28580, rule := .member 199495222860 },
  { wordCode := 28592, rule := .member 254065955609 },
  { wordCode := 28598, rule := .member 129836222028 },
  { wordCode := 28614, rule := .member 234351308007 },
  { wordCode := 28634, rule := .member 198487541325 },
  { wordCode := 28638, rule := .member 246483702552 },
  { wordCode := 28646, rule := .member 255073637144 },
  { wordCode := 28656, rule := .member 194944095000 },
  { wordCode := 28682, rule := .member 116492784409 },
  { wordCode := 28868, rule := .member 132252141132 },
  { wordCode := 28922, rule := .member 129298302541 },
  { wordCode := 28932, rule := .member 171282299314 },
  { wordCode := 28938, rule := .member 234888178919 },
  { wordCode := 29046, rule := .member 233814437095 },
  { wordCode := 29052, rule := .member 109782946584 },
  { wordCode := 29060, rule := .member 118372881176 },
  { wordCode := 29064, rule := .member 165094960359 },
  { wordCode := 29106, rule := .member 127969448728 },
  { wordCode := 29130, rule := .member 237854292402 },
  { wordCode := 29180, rule := .member 247801084339 },
  { wordCode := 29216, rule := .member 110362130867 },
  { wordCode := 29228, rule := .member 164515776076 },
  { wordCode := 29240, rule := .member 236637573912 },
  { wordCode := 29258, rule := .member 171005104920 },
  { wordCode := 29268, rule := .member 110875562776 },
  { wordCode := 29280, rule := .member 164002344167 },
  { wordCode := 29288, rule := .member 246727342515 },
  { wordCode := 29306, rule := .member 195187734962 },
  { wordCode := 29324, rule := .member 125528734130 },
  { wordCode := 29336, rule := .member 200888780364 },
  { wordCode := 29340, rule := .member 247240774424 },
  { wordCode := 29348, rule := .member 238650839832 },
  { wordCode := 29376, rule := .member 109801820952 },
  { wordCode := 29384, rule := .member 118391755544 },
  { wordCode := 29388, rule := .member 165076085991 },
  { wordCode := 29412, rule := .member 197041247000 },
  { wordCode := 29420, rule := .member 171273540376 },
  { wordCode := 29426, rule := .member 234912974412 },
  { wordCode := 29430, rule := .member 111141901080 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk006 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 29442, rule := .member 163733908711 },
  { wordCode := 29454, rule := .member 237468416434 },
  { wordCode := 29462, rule := .member 131833759308 },
  { wordCode := 29478, rule := .member 232386276583 },
  { wordCode := 29484, rule := .member 108122002200 },
  { wordCode := 29492, rule := .member 116711936792 },
  { wordCode := 29496, rule := .member 166755904743 },
  { wordCode := 29534, rule := .member 233839232588 },
  { wordCode := 29540, rule := .member 109758151091 },
  { wordCode := 29552, rule := .member 165119755852 },
  { wordCode := 29556, rule := .member 245428835096 },
  { wordCode := 29564, rule := .member 254018769688 },
  { wordCode := 29570, rule := .member 129818396237 },
  { wordCode := 29586, rule := .member 234401639655 },
  { wordCode := 29594, rule := .member 127944653234 },
  { wordCode := 29606, rule := .member 198472861260 },
  { wordCode := 29618, rule := .member 237845533464 },
  { wordCode := 29628, rule := .member 194893763352 },
  { wordCode := 29660, rule := .member 201423554125 },
  { wordCode := 29672, rule := .member 256365482776 },
  { wordCode := 29700, rule := .member 110336594712 },
  { wordCode := 29708, rule := .member 118926529304 },
  { wordCode := 29712, rule := .member 164541312231 },
  { wordCode := 29724, rule := .member 236663110066 },
  { wordCode := 29742, rule := .member 171030641074 },
  { wordCode := 29772, rule := .member 246701806360 },
  { wordCode := 29780, rule := .member 255291740952 },
  { wordCode := 29790, rule := .member 195162198808 },
  { wordCode := 29832, rule := .member 238676375986 },
  { wordCode := 29900, rule := .member 197083560370 },
  { wordCode := 29918, rule := .member 111184214451 },
  { wordCode := 29930, rule := .member 163693692492 },
  { wordCode := 29942, rule := .member 237459657496 },
  { wordCode := 29972, rule := .member 108164315571 },
  { wordCode := 29984, rule := .member 166713591372 },
  { wordCode := 29988, rule := .member 247056225048 },
  { wordCode := 29996, rule := .member 255646159640 },
  { wordCode := 30018, rule := .member 233980112103 },
  { wordCode := 30074, rule := .member 234359326284 },
  { wordCode := 30098, rule := .member 246475684275 },
  { wordCode := 30110, rule := .member 131280111180 },
  { wordCode := 30116, rule := .member 194936076722 },
  { wordCode := 30126, rule := .member 232906370279 },
  { wordCode := 30146, rule := .member 201340716620 },
  { wordCode := 30158, rule := .member 256448320281 },
  { wordCode := 30164, rule := .member 132621239884 },
  { wordCode := 30362, rule := .member 199193232972 },
  { wordCode := 30374, rule := .member 254300836633 },
  { wordCode := 30392, rule := .member 171290317592 },
  { wordCode := 30402, rule := .member 111160775448 },
  { wordCode := 30410, rule := .member 119750710040 },
  { wordCode := 30414, rule := .member 163717131495 },
  { wordCode := 30450, rule := .member 232369499367 },
  { wordCode := 30464, rule := .member 116727665433 },
  { wordCode := 30506, rule := .member 233822455372 },
  { wordCode := 30512, rule := .member 109774928307 },
  { wordCode := 30524, rule := .member 165102978636 },
  { wordCode := 30528, rule := .member 245445612312 },
  { wordCode := 30536, rule := .member 254035546904 },
  { wordCode := 30542, rule := .member 129802667596 },
  { wordCode := 30566, rule := .member 127961430450 },
  { wordCode := 30578, rule := .member 198456084044 },
  { wordCode := 30582, rule := .member 246452245272 },
  { wordCode := 30590, rule := .member 237862310680 },
  { wordCode := 32834, rule := .member 111192865203 },
  { wordCode := 32846, rule := .member 163685041740 },
  { wordCode := 32882, rule := .member 232338458188 },
  { wordCode := 32888, rule := .member 108171917747 },
  { wordCode := 32900, rule := .member 166704940620 },
  { wordCode := 32912, rule := .member 255638033177 },
  { wordCode := 32918, rule := .member 132345202252 },
  { wordCode := 32960, rule := .member 245476653491 },
  { wordCode := 32990, rule := .member 234350675532 },
  { wordCode := 33014, rule := .member 246484335027 },
  { wordCode := 33026, rule := .member 131271460428 },
  { wordCode := 33050, rule := .member 107903482291 },
  { wordCode := 33062, rule := .member 166974424652 },
  { wordCode := 33260, rule := .member 233546417740 },
  { wordCode := 33266, rule := .member 110050965939 },
  { wordCode := 33314, rule := .member 234887546444 },
  { wordCode := 33326, rule := .member 119742583577 },
  { wordCode := 33350, rule := .member 131808331340 },
  { wordCode := 33422, rule := .member 233813804620 },
  { wordCode := 33428, rule := .member 109783579059 },
  { wordCode := 33440, rule := .member 165094327884 },
  { wordCode := 33452, rule := .member 254027420441 },
  { wordCode := 33494, rule := .member 198447433292 },
  { wordCode := 33506, rule := .member 255034053401 },
  { wordCode := 33806, rule := .member 111142533555 },
  { wordCode := 33818, rule := .member 163735373388 },
  { wordCode := 33860, rule := .member 108122634675 },
  { wordCode := 33872, rule := .member 166755272268 },
  { wordCode := 33884, rule := .member 255654810393 },
  { wordCode := 33890, rule := .member 132395533900 },
  { wordCode := 33962, rule := .member 234401007180 },
  { wordCode := 33986, rule := .member 246434003379 },
  { wordCode := 33998, rule := .member 131321792076 },
  { wordCode := 34040, rule := .member 247776180659 },
  { wordCode := 34076, rule := .member 110337227187 },
  { wordCode := 34088, rule := .member 164540679756 },
  { wordCode := 34136, rule := .member 119490925337 },
  { wordCode := 34148, rule := .member 246702438835 },
  { wordCode := 34196, rule := .member 200913684044 },
  { wordCode := 34208, rule := .member 255856136985 },
  { wordCode := 34244, rule := .member 118417183513 },
  { wordCode := 34526, rule := .member 247859018163 },
  { wordCode := 34556, rule := .member 233177318988 },
  { wordCode := 34742, rule := .member 245711534515 },
  { wordCode := 34826, rule := .member 232372012620 },
  { wordCode := 34832, rule := .member 108138363315 },
  { wordCode := 34844, rule := .member 166739543628 },
  { wordCode := 34904, rule := .member 245443099059 },
  { wordCode := 34934, rule := .member 234385278540 },
  { wordCode := 35006, rule := .member 201386575436 },
  { wordCode := 35018, rule := .member 256469504793 },
  { wordCode := 35024, rule := .member 132667098700 },
  { wordCode := 35026, rule := .member 119782197064 },
  { wordCode := 35034, rule := .member 167980611764 },
  { wordCode := 35046, rule := .member 127554425374 },
  { wordCode := 35070, rule := .member 236634028212 },
  { wordCode := 35080, rule := .member 116762298184 },
  { wordCode := 35084, rule := .member 196770314396 },
  { wordCode := 35088, rule := .member 171000510644 },
  { wordCode := 35102, rule := .member 110872017052 },
  { wordCode := 35114, rule := .member 164005889891 },
  { wordCode := 35126, rule := .member 238283002422 },
  { wordCode := 35136, rule := .member 195200160286 },
  { wordCode := 35154, rule := .member 125540110878 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk007 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 35158, rule := .member 129835078173 },
  { wordCode := 35166, rule := .member 200876355041 },
  { wordCode := 35178, rule := .member 238646245556 },
  { wordCode := 35190, rule := .member 194192478750 },
  { wordCode := 35194, rule := .member 198487446045 },
  { wordCode := 35206, rule := .member 255073666888 },
  { wordCode := 35210, rule := .member 109798275228 },
  { wordCode := 35250, rule := .member 171269994676 },
  { wordCode := 35264, rule := .member 111140452508 },
  { wordCode := 35292, rule := .member 131821333985 },
  { wordCode := 35312, rule := .member 232389822307 },
  { wordCode := 35382, rule := .member 199467068897 },
  { wordCode := 35390, rule := .member 245425289372 },
  { wordCode := 35424, rule := .member 127957078558 },
  { wordCode := 35436, rule := .member 198460435937 },
  { wordCode := 35448, rule := .member 237841987764 },
  { wordCode := 35482, rule := .member 129298207261 },
  { wordCode := 35486, rule := .member 116480414489 },
  { wordCode := 35502, rule := .member 239183116468 },
  { wordCode := 35522, rule := .member 168020021814 },
  { wordCode := 35534, rule := .member 127513966748 },
  { wordCode := 35586, rule := .member 128224465438 },
  { wordCode := 35610, rule := .member 238109374644 },
  { wordCode := 35620, rule := .member 118372910920 },
  { wordCode := 35702, rule := .member 118627898137 },
  { wordCode := 35776, rule := .member 127542095330 },
  { wordCode := 35798, rule := .member 232342636108 },
  { wordCode := 35800, rule := .member 236637603656 },
  { wordCode := 35804, rule := .member 108167739827 },
  { wordCode := 35816, rule := .member 166710167116 },
  { wordCode := 35818, rule := .member 171005134664 },
  { wordCode := 35836, rule := .member 119465527112 },
  { wordCode := 35866, rule := .member 195187830242 },
  { wordCode := 35876, rule := .member 245472475571 },
  { wordCode := 35884, rule := .member 125528829410 },
  { wordCode := 35896, rule := .member 200888685085 },
  { wordCode := 35906, rule := .member 234355902028 },
  { wordCode := 35908, rule := .member 238650869576 },
  { wordCode := 35966, rule := .member 107899304371 },
  { wordCode := 35978, rule := .member 166978602572 },
  { wordCode := 35980, rule := .member 171273570120 },
  { wordCode := 35990, rule := .member 256452727577 },
  { wordCode := 35996, rule := .member 132616767052 },
  { wordCode := 35998, rule := .member 119731865416 },
  { wordCode := 36006, rule := .member 168030943412 },
  { wordCode := 36022, rule := .member 131833664029 },
  { wordCode := 36056, rule := .member 196820646044 },
  { wordCode := 36060, rule := .member 171050842292 },
  { wordCode := 36074, rule := .member 128101169308 },
  { wordCode := 36098, rule := .member 238266225206 },
  { wordCode := 36112, rule := .member 199479398941 },
  { wordCode := 36124, rule := .member 254018799432 },
  { wordCode := 36126, rule := .member 125523333662 },
  { wordCode := 36130, rule := .member 129818300957 },
  { wordCode := 36150, rule := .member 238696577204 },
  { wordCode := 36154, rule := .member 127944748514 },
  { wordCode := 36162, rule := .member 194175701534 },
  { wordCode := 36166, rule := .member 198470668829 },
  { wordCode := 36176, rule := .member 233550595660 },
  { wordCode := 36178, rule := .member 237845563208 },
  { wordCode := 36196, rule := .member 169126086472 },
  { wordCode := 36216, rule := .member 197128491550 },
  { wordCode := 36220, rule := .member 201423458845 },
  { wordCode := 36232, rule := .member 256365512520 },
  { wordCode := 36276, rule := .member 168836249780 },
  { wordCode := 36296, rule := .member 116732072729 },
  { wordCode := 36324, rule := .member 193907266078 },
  { wordCode := 36332, rule := .member 168271680054 },
  { wordCode := 36340, rule := .member 255291770696 },
  { wordCode := 36356, rule := .member 199457195596 },
  { wordCode := 36368, rule := .member 254036808473 },
  { wordCode := 36440, rule := .member 169345421878 },
  { wordCode := 36460, rule := .member 197083655650 },
  { wordCode := 36470, rule := .member 247871617459 },
  { wordCode := 36478, rule := .member 128364178914 },
  { wordCode := 36500, rule := .member 233164719692 },
  { wordCode := 36502, rule := .member 237459687240 },
  { wordCode := 36544, rule := .member 201073234461 },
  { wordCode := 36556, rule := .member 255646189384 },
  { wordCode := 36562, rule := .member 132353757725 },
  { wordCode := 36676, rule := .member 194936172002 },
  { wordCode := 36686, rule := .member 245724133811 },
  { wordCode := 36720, rule := .member 128326177310 },
  { wordCode := 36744, rule := .member 237472889012 },
  { wordCode := 36786, rule := .member 201111236065 },
  { wordCode := 36794, rule := .member 247069456540 },
  { wordCode := 36798, rule := .member 255659391156 },
  { wordCode := 36918, rule := .member 194898170398 },
  { wordCode := 36932, rule := .member 232893138787 },
  { wordCode := 36938, rule := .member 107882527155 },
  { wordCode := 36950, rule := .member 166995379788 },
  { wordCode := 36952, rule := .member 171290347336 },
  { wordCode := 36990, rule := .member 127520870942 },
  { wordCode := 36994, rule := .member 131816886813 },
  { wordCode := 37014, rule := .member 236667582644 },
  { wordCode := 37032, rule := .member 171035113652 },
  { wordCode := 37046, rule := .member 110905571484 },
  { wordCode := 37058, rule := .member 163972335459 },
  { wordCode := 37080, rule := .member 195166605854 },
  { wordCode := 37084, rule := .member 199462621725 },
  { wordCode := 37096, rule := .member 254035576648 },
  { wordCode := 37098, rule := .member 125507605022 },
  { wordCode := 37110, rule := .member 200909909473 },
  { wordCode := 37118, rule := .member 247270783132 },
  { wordCode := 37122, rule := .member 238680848564 },
  { wordCode := 37126, rule := .member 127961525730 },
  { wordCode := 37138, rule := .member 198455988765 },
  { wordCode := 37148, rule := .member 233567372876 },
  { wordCode := 37150, rule := .member 237862340424 },
  { wordCode := 37188, rule := .member 197091840792 },
  { wordCode := 37192, rule := .member 201452818973 },
  { wordCode := 37204, rule := .member 256403261256 },
  { wordCode := 37206, rule := .member 111192494872 },
  { wordCode := 37214, rule := .member 119782429464 },
  { wordCode := 37218, rule := .member 163685461220 },
  { wordCode := 37230, rule := .member 237451901362 },
  { wordCode := 37238, rule := .member 131849209420 },
  { wordCode := 37254, rule := .member 232338877668 },
  { wordCode := 37260, rule := .member 108172595992 },
  { wordCode := 37268, rule := .member 116762530584 },
  { wordCode := 37270, rule := .member 196770131400 },
  { wordCode := 37272, rule := .member 166705360100 },
  { wordCode := 37284, rule := .member 255638419889 },
  { wordCode := 37290, rule := .member 132345621732 },
  { wordCode := 37300, rule := .member 164006072887 },
  { wordCode := 37328, rule := .member 199494944332 },
  { wordCode := 37332, rule := .member 245476234011 },
  { wordCode := 37340, rule := .member 254066168601 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk008 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 37346, rule := .member 129835943500 },
  { wordCode := 37360, rule := .member 247237045704 },
  { wordCode := 37362, rule := .member 234351095012 },
  { wordCode := 37382, rule := .member 198487279181 },
  { wordCode := 37386, rule := .member 246483964696 },
  { wordCode := 37394, rule := .member 255073899288 },
  { wordCode := 37396, rule := .member 109798092232 },
  { wordCode := 37398, rule := .member 131271879908 },
  { wordCode := 37404, rule := .member 194944357144 },
  { wordCode := 37408, rule := .member 165079814711 },
  { wordCode := 37420, rule := .member 237209077602 },
  { wordCode := 37422, rule := .member 107903062811 },
  { wordCode := 37430, rule := .member 116492997401 },
  { wordCode := 37434, rule := .member 166974844132 },
  { wordCode := 37450, rule := .member 111140269512 },
  { wordCode := 37462, rule := .member 163737637431 },
  { wordCode := 37498, rule := .member 232390005303 },
  { wordCode := 37534, rule := .member 132532015645 },
  { wordCode := 37564, rule := .member 118360328008 },
  { wordCode := 37576, rule := .member 245425106376 },
  { wordCode := 37616, rule := .member 132251862604 },
  { wordCode := 37650, rule := .member 164827360484 },
  { wordCode := 37670, rule := .member 129298040397 },
  { wordCode := 37680, rule := .member 171282561458 },
  { wordCode := 37686, rule := .member 234887965924 },
  { wordCode := 37698, rule := .member 119742970289 },
  { wordCode := 37708, rule := .member 168019838818 },
  { wordCode := 37720, rule := .member 127513783752 },
  { wordCode := 37722, rule := .member 131808750820 },
  { wordCode := 37794, rule := .member 233814224100 },
  { wordCode := 37800, rule := .member 109783208728 },
  { wordCode := 37808, rule := .member 118373143320 },
  { wordCode := 37810, rule := .member 195159518664 },
  { wordCode := 37812, rule := .member 165094747364 },
  { wordCode := 37824, rule := .member 254027807153 },
  { wordCode := 37854, rule := .member 127969710872 },
  { wordCode := 37866, rule := .member 198447852772 },
  { wordCode := 37918, rule := .member 197153910242 },
  { wordCode := 37928, rule := .member 247801346483 },
  { wordCode := 37964, rule := .member 110362393011 },
  { wordCode := 37976, rule := .member 164515497548 },
  { wordCode := 37988, rule := .member 236637836056 },
  { wordCode := 38006, rule := .member 171005367064 },
  { wordCode := 38016, rule := .member 110875824920 },
  { wordCode := 38026, rule := .member 193932684770 },
  { wordCode := 38028, rule := .member 164002082023 },
  { wordCode := 38054, rule := .member 195187997106 },
  { wordCode := 38072, rule := .member 125528996274 },
  { wordCode := 38088, rule := .member 247241036568 },
  { wordCode := 38136, rule := .member 165075823847 },
  { wordCode := 38160, rule := .member 197041509144 },
  { wordCode := 38176, rule := .member 239207663432 },
  { wordCode := 38178, rule := .member 111142163224 },
  { wordCode := 38186, rule := .member 119732097816 },
  { wordCode := 38190, rule := .member 163735792868 },
  { wordCode := 38202, rule := .member 237468678578 },
  { wordCode := 38226, rule := .member 232386014439 },
  { wordCode := 38232, rule := .member 108122264344 },
  { wordCode := 38240, rule := .member 116712198936 },
  { wordCode := 38242, rule := .member 196820463048 },
  { wordCode := 38244, rule := .member 166755691748 },
  { wordCode := 38256, rule := .member 255655197105 },
  { wordCode := 38288, rule := .member 109758413235 },
  { wordCode := 38300, rule := .member 165119477324 },
  { wordCode := 38304, rule := .member 245429097240 },
  { wordCode := 38312, rule := .member 254019031832 },
  { wordCode := 38334, rule := .member 234401426660 },
  { wordCode := 38342, rule := .member 127944915378 },
  { wordCode := 38354, rule := .member 198472582732 },
  { wordCode := 38366, rule := .member 237845795608 },
  { wordCode := 38368, rule := .member 127027244488 },
  { wordCode := 38370, rule := .member 131322211556 },
  { wordCode := 38376, rule := .member 194894025496 },
  { wordCode := 38384, rule := .member 169126318872 },
  { wordCode := 38412, rule := .member 247775810328 },
  { wordCode := 38448, rule := .member 110336856856 },
  { wordCode := 38460, rule := .member 164541099236 },
  { wordCode := 38472, rule := .member 236663372210 },
  { wordCode := 38490, rule := .member 171030903218 },
  { wordCode := 38518, rule := .member 168271497058 },
  { wordCode := 38520, rule := .member 246702068504 },
  { wordCode := 38528, rule := .member 255292003096 },
  { wordCode := 38556, rule := .member 125503460120 },
  { wordCode := 38568, rule := .member 200914103524 },
  { wordCode := 38648, rule := .member 197083822514 },
  { wordCode := 38678, rule := .member 163693413964 },
  { wordCode := 38690, rule := .member 237459919640 },
  { wordCode := 38720, rule := .member 108164577715 },
  { wordCode := 38736, rule := .member 247056487192 },
  { wordCode := 38750, rule := .member 132353574476 },
  { wordCode := 38766, rule := .member 233979849959 },
  { wordCode := 38836, rule := .member 194184343010 },
  { wordCode := 38864, rule := .member 194936338866 },
  { wordCode := 38874, rule := .member 232906108135 },
  { wordCode := 38894, rule := .member 201340438092 },
  { wordCode := 38898, rule := .member 247858598683 },
  { wordCode := 38912, rule := .member 132620961356 },
  { wordCode := 38928, rule := .member 233177738468 },
  { wordCode := 38980, rule := .member 247069273544 },
  { wordCode := 39082, rule := .member 198466474525 },
  { wordCode := 39094, rule := .member 255027529544 },
  { wordCode := 39114, rule := .member 245711115035 },
  { wordCode := 39124, rule := .member 124995104226 },
  { wordCode := 39136, rule := .member 201419264541 },
  { wordCode := 39148, rule := .member 239190886216 },
  { wordCode := 39150, rule := .member 111161037592 },
  { wordCode := 39162, rule := .member 163716869351 },
  { wordCode := 39184, rule := .member 118930753352 },
  { wordCode := 39198, rule := .member 232372432100 },
  { wordCode := 39204, rule := .member 108137943835 },
  { wordCode := 39216, rule := .member 166739963108 },
  { wordCode := 39254, rule := .member 233822176844 },
  { wordCode := 39256, rule := .member 238117144392 },
  { wordCode := 39260, rule := .member 109775190451 },
  { wordCode := 39272, rule := .member 165102700108 },
  { wordCode := 39284, rule := .member 254035809048 },
  { wordCode := 39290, rule := .member 129802389068 },
  { wordCode := 39306, rule := .member 234385698020 },
  { wordCode := 39314, rule := .member 127961692594 },
  { wordCode := 39326, rule := .member 198455805516 },
  { wordCode := 39330, rule := .member 246452507416 },
  { wordCode := 39338, rule := .member 237862572824 },
  { wordCode := 39340, rule := .member 109831646664 },
  { wordCode := 39356, rule := .member 169143096088 },
  { wordCode := 59058, rule := .member 197092332236 },
  { wordCode := 59062, rule := .member 201387299532 },
  { wordCode := 59074, rule := .member 256403785608 },
  { wordCode := 59076, rule := .member 111192986316 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk009 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 59080, rule := .member 132667822796 },
  { wordCode := 59088, rule := .member 163684920627 },
  { wordCode := 59100, rule := .member 237451409510 },
  { wordCode := 59110, rule := .member 118964832136 },
  { wordCode := 59130, rule := .member 108173087436 },
  { wordCode := 59142, rule := .member 166704819507 },
  { wordCode := 59170, rule := .member 198232117981 },
  { wordCode := 59182, rule := .member 255330043784 },
  { wordCode := 59232, rule := .member 234350554419 },
  { wordCode := 59256, rule := .member 246484456140 },
  { wordCode := 59274, rule := .member 194944848588 },
  { wordCode := 59278, rule := .member 199239815884 },
  { wordCode := 59290, rule := .member 254322345881 },
  { wordCode := 59296, rule := .member 129311314653 },
  { wordCode := 59404, rule := .member 132532540125 },
  { wordCode := 59542, rule := .member 116480739225 },
  { wordCode := 59550, rule := .member 171282069606 },
  { wordCode := 59556, rule := .member 234887425331 },
  { wordCode := 59664, rule := .member 233813683507 },
  { wordCode := 59670, rule := .member 109783700172 },
  { wordCode := 59682, rule := .member 165094206771 },
  { wordCode := 59758, rule := .member 118628222873 },
  { wordCode := 59766, rule := .member 169134585958 },
  { wordCode := 59788, rule := .member 197153385762 },
  { wordCode := 59854, rule := .member 232343360204 },
  { wordCode := 59860, rule := .member 108167015731 },
  { wordCode := 59872, rule := .member 166710891212 },
  { wordCode := 59886, rule := .member 110876316364 },
  { wordCode := 59896, rule := .member 193932160290 },
  { wordCode := 59898, rule := .member 164001590579 },
  { wordCode := 59932, rule := .member 245471751475 },
  { wordCode := 59958, rule := .member 247241528012 },
  { wordCode := 59962, rule := .member 234356626124 },
  { wordCode := 59994, rule := .member 109802574540 },
  { wordCode := 60006, rule := .member 165075332403 },
  { wordCode := 60022, rule := .member 107898580275 },
  { wordCode := 60030, rule := .member 197042000588 },
  { wordCode := 60034, rule := .member 166979326668 },
  { wordCode := 60046, rule := .member 239208187784 },
  { wordCode := 60048, rule := .member 111142654668 },
  { wordCode := 60052, rule := .member 132617491148 },
  { wordCode := 60060, rule := .member 163733155123 },
  { wordCode := 60072, rule := .member 237468186726 },
  { wordCode := 60096, rule := .member 232385522995 },
  { wordCode := 60102, rule := .member 108122755788 },
  { wordCode := 60114, rule := .member 166755151155 },
  { wordCode := 60130, rule := .member 128232582434 },
  { wordCode := 60154, rule := .member 238134445960 },
  { wordCode := 60174, rule := .member 245429588684 },
  { wordCode := 60204, rule := .member 234400886067 },
  { wordCode := 60228, rule := .member 246434124492 },
  { wordCode := 60238, rule := .member 110046063923 },
  { wordCode := 60246, rule := .member 194894516940 },
  { wordCode := 60250, rule := .member 164831843020 },
  { wordCode := 60262, rule := .member 254305568665 },
  { wordCode := 60282, rule := .member 247776301772 },
  { wordCode := 60318, rule := .member 110337348300 },
  { wordCode := 60322, rule := .member 131812184780 },
  { wordCode := 60330, rule := .member 164540558643 },
  { wordCode := 60342, rule := .member 236662880358 },
  { wordCode := 60352, rule := .member 116732397465 },
  { wordCode := 60360, rule := .member 171030411366 },
  { wordCode := 60412, rule := .member 199457919692 },
  { wordCode := 60426, rule := .member 125503951564 },
  { wordCode := 60450, rule := .member 238676146278 },
  { wordCode := 60526, rule := .member 247870893363 },
  { wordCode := 60556, rule := .member 233165443788 },
  { wordCode := 60606, rule := .member 247056978636 },
  { wordCode := 60636, rule := .member 233979358515 },
  { wordCode := 60694, rule := .member 238654539656 },
  { wordCode := 60742, rule := .member 245723409715 },
  { wordCode := 60744, rule := .member 232905616691 },
  { wordCode := 60964, rule := .member 255028053896 },
  { wordCode := 60994, rule := .member 107881803059 },
  { wordCode := 61006, rule := .member 166996103884 },
  { wordCode := 61018, rule := .member 239191410568 },
  { wordCode := 61020, rule := .member 111161529036 },
  { wordCode := 61032, rule := .member 163716377907 },
  { wordCode := 61054, rule := .member 118931277704 },
  { wordCode := 61102, rule := .member 128215805218 },
  { wordCode := 61114, rule := .member 198198563549 },
  { wordCode := 61126, rule := .member 238117668744 },
  { wordCode := 61146, rule := .member 245446365900 },
  { wordCode := 61200, rule := .member 246452998860 },
  { wordCode := 61204, rule := .member 233568096972 },
  { wordCode := 61210, rule := .member 110029286707 },
  { wordCode := 61222, rule := .member 164848620236 },
  { wordCode := 61248, rule := .member 201452547361 },
  { wordCode := 61260, rule := .member 256403355764 },
  { wordCode := 61356, rule := .member 198231321889 },
  { wordCode := 61368, rule := .member 255329613940 },
  { wordCode := 61482, rule := .member 129310518561 },
  { wordCode := 61590, rule := .member 132531744033 },
  { wordCode := 61974, rule := .member 197154181854 },
  { wordCode := 62082, rule := .member 193932956382 },
  { wordCode := 62208, rule := .member 125012153054 },
  { wordCode := 62232, rule := .member 239207757940 },
  { wordCode := 62316, rule := .member 128233378526 },
  { wordCode := 62340, rule := .member 238134016116 },
  { wordCode := 62880, rule := .member 238654109812 },
  { wordCode := 63150, rule := .member 255027624052 },
  { wordCode := 63180, rule := .member 124995375838 },
  { wordCode := 63192, rule := .member 201418992929 },
  { wordCode := 63204, rule := .member 239190980724 },
  { wordCode := 63240, rule := .member 118930847860 },
  { wordCode := 63288, rule := .member 128216601310 },
  { wordCode := 63300, rule := .member 198197767457 },
  { wordCode := 63312, rule := .member 238117238900 },
  { wordCode := 63330, rule := .member 169397762164 },
  { wordCode := 63456, rule := .member 119782307940 },
  { wordCode := 63510, rule := .member 116762409060 },
  { wordCode := 63588, rule := .member 129834790193 },
  { wordCode := 63624, rule := .member 198487158065 },
  { wordCode := 63636, rule := .member 255073777764 },
  { wordCode := 63912, rule := .member 129297919281 },
  { wordCode := 64020, rule := .member 132519144753 },
  { wordCode := 64050, rule := .member 118373021796 },
  { wordCode := 64206, rule := .member 127542383310 },
  { wordCode := 64230, rule := .member 236637714532 },
  { wordCode := 64248, rule := .member 171005245540 },
  { wordCode := 64266, rule := .member 119465637988 },
  { wordCode := 64296, rule := .member 195188118222 },
  { wordCode := 64314, rule := .member 125529117390 },
  { wordCode := 64326, rule := .member 200888397105 },
  { wordCode := 64338, rule := .member 238650980452 },
  { wordCode := 64374, rule := .member 118391896164 },
  { wordCode := 64410, rule := .member 171273680996 },
  { wordCode := 64428, rule := .member 119731976292 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk010 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 64452, rule := .member 131833376049 },
  { wordCode := 64482, rule := .member 116712077412 },
  { wordCode := 64542, rule := .member 199479110961 },
  { wordCode := 64554, rule := .member 254018910308 },
  { wordCode := 64560, rule := .member 129818012977 },
  { wordCode := 64584, rule := .member 127945036494 },
  { wordCode := 64596, rule := .member 198470380849 },
  { wordCode := 64608, rule := .member 237845674084 },
  { wordCode := 64626, rule := .member 169126197348 },
  { wordCode := 64650, rule := .member 201423170865 },
  { wordCode := 64698, rule := .member 118926669924 },
  { wordCode := 64758, rule := .member 198201945393 },
  { wordCode := 64770, rule := .member 255291881572 },
  { wordCode := 64890, rule := .member 197083943630 },
  { wordCode := 64932, rule := .member 237459798116 },
  { wordCode := 64974, rule := .member 201072946481 },
  { wordCode := 64986, rule := .member 255646300260 },
  { wordCode := 64992, rule := .member 132353469745 },
  { wordCode := 65100, rule := .member 131279727921 },
  { wordCode := 65106, rule := .member 194936459982 },
  { wordCode := 65424, rule := .member 131816598833 },
  { wordCode := 65514, rule := .member 199462333745 },
  { wordCode := 65526, rule := .member 254035687524 },
  { wordCode := 65556, rule := .member 127961813710 },
  { wordCode := 65568, rule := .member 198455700785 },
  { wordCode := 65580, rule := .member 237862451300 },
  { wordCode := 65630, rule := .member 247813666924 },
  { wordCode := 65638, rule := .member 111192911163 },
  { wordCode := 65650, rule := .member 163684995780 },
  { wordCode := 65654, rule := .member 167979963076 },
  { wordCode := 65666, rule := .member 110374713452 },
  { wordCode := 65678, rule := .member 164503193491 },
  { wordCode := 65686, rule := .member 232338412228 },
  { wordCode := 65690, rule := .member 236633379524 },
  { wordCode := 65692, rule := .member 108171963707 },
  { wordCode := 65704, rule := .member 166704894660 },
  { wordCode := 65708, rule := .member 170999861956 },
  { wordCode := 65716, rule := .member 255638079377 },
  { wordCode := 65722, rule := .member 132345156292 },
  { wordCode := 65726, rule := .member 119461302980 },
  { wordCode := 65738, rule := .member 246739925100 },
  { wordCode := 65756, rule := .member 195200317548 },
  { wordCode := 65764, rule := .member 245476699451 },
  { wordCode := 65774, rule := .member 125541316716 },
  { wordCode := 65786, rule := .member 200876197777 },
  { wordCode := 65794, rule := .member 234350629572 },
  { wordCode := 65798, rule := .member 238645596868 },
  { wordCode := 65810, rule := .member 194192636014 },
  { wordCode := 65818, rule := .member 246484380987 },
  { wordCode := 65830, rule := .member 131271414468 },
  { wordCode := 65834, rule := .member 118387561156 },
  { wordCode := 65854, rule := .member 107903528251 },
  { wordCode := 65866, rule := .member 166974378692 },
  { wordCode := 65870, rule := .member 171269345988 },
  { wordCode := 65876, rule := .member 234900391827 },
  { wordCode := 65888, rule := .member 119729738436 },
  { wordCode := 65912, rule := .member 131821176721 },
  { wordCode := 65984, rule := .member 233826650003 },
  { wordCode := 65990, rule := .member 109770733676 },
  { wordCode := 66014, rule := .member 254014575300 },
  { wordCode := 66044, rule := .member 127957235820 },
  { wordCode := 66056, rule := .member 198460278673 },
  { wordCode := 66064, rule := .member 233546371780 },
  { wordCode := 66068, rule := .member 237841339076 },
  { wordCode := 66070, rule := .member 110051011899 },
  { wordCode := 66082, rule := .member 164826895044 },
  { wordCode := 66086, rule := .member 169121862340 },
  { wordCode := 66098, rule := .member 125003397230 },
  { wordCode := 66118, rule := .member 234887500484 },
  { wordCode := 66122, rule := .member 239182467780 },
  { wordCode := 66130, rule := .member 119742629777 },
  { wordCode := 66154, rule := .member 131808285380 },
  { wordCode := 66226, rule := .member 233813758660 },
  { wordCode := 66230, rule := .member 238108725956 },
  { wordCode := 66232, rule := .member 109783625019 },
  { wordCode := 66244, rule := .member 165094281924 },
  { wordCode := 66248, rule := .member 169389249220 },
  { wordCode := 66256, rule := .member 254027466641 },
  { wordCode := 66464, rule := .member 168296633030 },
  { wordCode := 66512, rule := .member 196593875052 },
  { wordCode := 66610, rule := .member 111142579515 },
  { wordCode := 66622, rule := .member 163735327428 },
  { wordCode := 66626, rule := .member 168030294724 },
  { wordCode := 66638, rule := .member 127538853996 },
  { wordCode := 66662, rule := .member 236680565446 },
  { wordCode := 66664, rule := .member 108122680635 },
  { wordCode := 66676, rule := .member 166755226308 },
  { wordCode := 66680, rule := .member 171050193604 },
  { wordCode := 66688, rule := .member 255654856593 },
  { wordCode := 66694, rule := .member 132395487940 },
  { wordCode := 66728, rule := .member 195184588908 },
  { wordCode := 66746, rule := .member 125523490926 },
  { wordCode := 66766, rule := .member 234400961220 },
  { wordCode := 66770, rule := .member 238695928516 },
  { wordCode := 66782, rule := .member 194177955948 },
  { wordCode := 66790, rule := .member 246434049339 },
  { wordCode := 66802, rule := .member 131321746116 },
  { wordCode := 66836, rule := .member 197128648814 },
  { wordCode := 66844, rule := .member 247776226619 },
  { wordCode := 66880, rule := .member 110337273147 },
  { wordCode := 66892, rule := .member 164540633796 },
  { wordCode := 66896, rule := .member 168835601092 },
  { wordCode := 66940, rule := .member 119490971537 },
  { wordCode := 66944, rule := .member 193907423342 },
  { wordCode := 66952, rule := .member 246702484795 },
  { wordCode := 67000, rule := .member 200913638084 },
  { wordCode := 67012, rule := .member 255856183185 },
  { wordCode := 67048, rule := .member 118417229713 },
  { wordCode := 67160, rule := .member 196778424428 },
  { wordCode := 67178, rule := .member 128058947692 },
  { wordCode := 67202, rule := .member 238274400966 },
  { wordCode := 67286, rule := .member 126985205868 },
  { wordCode := 67310, rule := .member 237200659142 },
  { wordCode := 67322, rule := .member 197045811308 },
  { wordCode := 67330, rule := .member 247859064123 },
  { wordCode := 67340, rule := .member 111146465388 },
  { wordCode := 67352, rule := .member 163731441555 },
  { wordCode := 67360, rule := .member 233177273028 },
  { wordCode := 67364, rule := .member 237472240324 },
  { wordCode := 67394, rule := .member 108126566508 },
  { wordCode := 67406, rule := .member 166751340435 },
  { wordCode := 67418, rule := .member 255658742468 },
  { wordCode := 67424, rule := .member 132391602065 },
  { wordCode := 67496, rule := .member 234397075347 },
  { wordCode := 67520, rule := .member 246437935212 },
  { wordCode := 67532, rule := .member 131317860241 },
  { wordCode := 67538, rule := .member 194898327660 },
  { wordCode := 67546, rule := .member 245711580475 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk011 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 67574, rule := .member 247780112492 },
  { wordCode := 67598, rule := .member 168011420358 },
  { wordCode := 67610, rule := .member 110341159020 },
  { wordCode := 67622, rule := .member 164536747923 },
  { wordCode := 67634, rule := .member 236666933956 },
  { wordCode := 67636, rule := .member 108138409275 },
  { wordCode := 67648, rule := .member 166739497668 },
  { wordCode := 67652, rule := .member 171034464964 },
  { wordCode := 67682, rule := .member 246706370668 },
  { wordCode := 67708, rule := .member 245443145019 },
  { wordCode := 67718, rule := .member 125507762284 },
  { wordCode := 67730, rule := .member 200909752209 },
  { wordCode := 67738, rule := .member 234385232580 },
  { wordCode := 67742, rule := .member 238680199876 },
  { wordCode := 67754, rule := .member 194161178732 },
  { wordCode := 67810, rule := .member 201386545860 },
  { wordCode := 67822, rule := .member 256469600145 },
  { wordCode := 67824, rule := .member 111192199884 },
  { wordCode := 67832, rule := .member 119782167236 },
  { wordCode := 67836, rule := .member 163685707059 },
  { wordCode := 67848, rule := .member 237451671654 },
  { wordCode := 67878, rule := .member 108172301004 },
  { wordCode := 67886, rule := .member 116762268356 },
  { wordCode := 67890, rule := .member 166705605939 },
  { wordCode := 67964, rule := .member 129835173777 },
  { wordCode := 67980, rule := .member 234351340851 },
  { wordCode := 68000, rule := .member 198487541649 },
  { wordCode := 68012, rule := .member 255073637060 },
  { wordCode := 68022, rule := .member 194944062156 },
  { wordCode := 68026, rule := .member 199239062212 },
  { wordCode := 68288, rule := .member 129298302865 },
  { wordCode := 68298, rule := .member 171282331750 },
  { wordCode := 68304, rule := .member 234888211763 },
  { wordCode := 68396, rule := .member 132519528337 },
  { wordCode := 68412, rule := .member 233814469939 },
  { wordCode := 68418, rule := .member 109782913740 },
  { wordCode := 68426, rule := .member 118372881092 },
  { wordCode := 68430, rule := .member 165094993203 },
  { wordCode := 68476, rule := .member 132264415940 },
  { wordCode := 68506, rule := .member 118627993489 },
  { wordCode := 68514, rule := .member 169134848102 },
  { wordCode := 68582, rule := .member 127541999726 },
  { wordCode := 68602, rule := .member 232342606532 },
  { wordCode := 68606, rule := .member 236637573828 },
  { wordCode := 68608, rule := .member 108167802163 },
  { wordCode := 68620, rule := .member 166710137540 },
  { wordCode := 68624, rule := .member 171005104836 },
  { wordCode := 68634, rule := .member 110875529932 },
  { wordCode := 68642, rule := .member 119465497284 },
  { wordCode := 68646, rule := .member 164002377011 },
  { wordCode := 68672, rule := .member 195187734638 },
  { wordCode := 68680, rule := .member 245472537907 },
  { wordCode := 68690, rule := .member 125528733806 },
  { wordCode := 68702, rule := .member 200888780689 },
  { wordCode := 68706, rule := .member 247240741580 },
  { wordCode := 68710, rule := .member 234355872452 },
  { wordCode := 68714, rule := .member 238650839748 },
  { wordCode := 68742, rule := .member 109801788108 },
  { wordCode := 68750, rule := .member 118391755460 },
  { wordCode := 68754, rule := .member 165076118835 },
  { wordCode := 68770, rule := .member 107899366707 },
  { wordCode := 68778, rule := .member 197041214156 },
  { wordCode := 68786, rule := .member 171273540292 },
  { wordCode := 68794, rule := .member 256452822929 },
  { wordCode := 68796, rule := .member 111141868236 },
  { wordCode := 68804, rule := .member 119731835588 },
  { wordCode := 68808, rule := .member 163733941555 },
  { wordCode := 68820, rule := .member 237468448870 },
  { wordCode := 68828, rule := .member 131833759633 },
  { wordCode := 68844, rule := .member 232386309427 },
  { wordCode := 68850, rule := .member 108121969356 },
  { wordCode := 68858, rule := .member 116711936708 },
  { wordCode := 68862, rule := .member 166755937587 },
  { wordCode := 68918, rule := .member 199479494545 },
  { wordCode := 68922, rule := .member 245428802252 },
  { wordCode := 68930, rule := .member 254018769604 },
  { wordCode := 68936, rule := .member 129818396561 },
  { wordCode := 68952, rule := .member 234401672499 },
  { wordCode := 68960, rule := .member 127944652910 },
  { wordCode := 68972, rule := .member 198470764433 },
  { wordCode := 68976, rule := .member 246433338060 },
  { wordCode := 68980, rule := .member 233550566084 },
  { wordCode := 68984, rule := .member 237845533380 },
  { wordCode := 68986, rule := .member 110046850355 },
  { wordCode := 68998, rule := .member 164831089348 },
  { wordCode := 69002, rule := .member 169126056644 },
  { wordCode := 69010, rule := .member 254305339281 },
  { wordCode := 69026, rule := .member 201423554449 },
  { wordCode := 69038, rule := .member 256365482692 },
  { wordCode := 69066, rule := .member 110336561868 },
  { wordCode := 69074, rule := .member 118926529220 },
  { wordCode := 69078, rule := .member 164541345075 },
  { wordCode := 69090, rule := .member 236663142502 },
  { wordCode := 69108, rule := .member 171030673510 },
  { wordCode := 69134, rule := .member 198202328977 },
  { wordCode := 69138, rule := .member 246701773516 },
  { wordCode := 69146, rule := .member 255291740868 },
  { wordCode := 69156, rule := .member 195162165964 },
  { wordCode := 69198, rule := .member 238676408422 },
  { wordCode := 69266, rule := .member 197083560046 },
  { wordCode := 69274, rule := .member 247871679795 },
  { wordCode := 69284, rule := .member 128364083310 },
  { wordCode := 69304, rule := .member 233164690116 },
  { wordCode := 69308, rule := .member 237459657412 },
  { wordCode := 69350, rule := .member 201073330065 },
  { wordCode := 69354, rule := .member 247056192204 },
  { wordCode := 69362, rule := .member 255646159556 },
  { wordCode := 69368, rule := .member 132353853329 },
  { wordCode := 69476, rule := .member 131280111505 },
  { wordCode := 69482, rule := .member 194936076398 },
  { wordCode := 69490, rule := .member 245724196147 },
  { wordCode := 69492, rule := .member 232906403123 },
  { wordCode := 69742, rule := .member 107882589491 },
  { wordCode := 69754, rule := .member 166995350212 },
  { wordCode := 69768, rule := .member 111160742604 },
  { wordCode := 69780, rule := .member 163717164339 },
  { wordCode := 69800, rule := .member 131816982417 },
  { wordCode := 69816, rule := .member 232369532211 },
  { wordCode := 69890, rule := .member 199462717329 },
  { wordCode := 69894, rule := .member 245445579468 },
  { wordCode := 69902, rule := .member 254035546820 },
  { wordCode := 69932, rule := .member 127961430126 },
  { wordCode := 69944, rule := .member 198456084369 },
  { wordCode := 69948, rule := .member 246452212428 },
  { wordCode := 69952, rule := .member 233567343300 },
  { wordCode := 69956, rule := .member 237862310596 },
  { wordCode := 69970, rule := .member 164847866564 },
  { wordCode := 69974, rule := .member 169142833860 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk012 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 70002, rule := .member 247813264076 },
  { wordCode := 70026, rule := .member 167980365924 },
  { wordCode := 70038, rule := .member 110374310604 },
  { wordCode := 70042, rule := .member 131849147084 },
  { wordCode := 70050, rule := .member 164503596339 },
  { wordCode := 70062, rule := .member 236633782372 },
  { wordCode := 70072, rule := .member 116761495449 },
  { wordCode := 70080, rule := .member 171000264804 },
  { wordCode := 70128, rule := .member 195199914700 },
  { wordCode := 70132, rule := .member 199494881996 },
  { wordCode := 70144, rule := .member 254066231193 },
  { wordCode := 70146, rule := .member 125540913868 },
  { wordCode := 70150, rule := .member 129835881164 },
  { wordCode := 70158, rule := .member 200876600625 },
  { wordCode := 70170, rule := .member 238645999716 },
  { wordCode := 70182, rule := .member 194192233166 },
  { wordCode := 70206, rule := .member 118387964004 },
  { wordCode := 70234, rule := .member 116493059993 },
  { wordCode := 70242, rule := .member 171269748836 },
  { wordCode := 70248, rule := .member 234900794675 },
  { wordCode := 70260, rule := .member 119730141284 },
  { wordCode := 70284, rule := .member 131821579569 },
  { wordCode := 70356, rule := .member 233827052851 },
  { wordCode := 70362, rule := .member 109770330828 },
  { wordCode := 70386, rule := .member 254014978148 },
  { wordCode := 70416, rule := .member 127956832972 },
  { wordCode := 70420, rule := .member 132251800268 },
  { wordCode := 70428, rule := .member 198460681521 },
  { wordCode := 70440, rule := .member 237841741924 },
  { wordCode := 70450, rule := .member 118640543641 },
  { wordCode := 70458, rule := .member 169122265188 },
  { wordCode := 70470, rule := .member 125002994382 },
  { wordCode := 70494, rule := .member 239182870628 },
  { wordCode := 70578, rule := .member 128224219854 },
  { wordCode := 70620, rule := .member 169389652068 },
  { wordCode := 70732, rule := .member 247801425203 },
  { wordCode := 70768, rule := .member 110362471731 },
  { wordCode := 70780, rule := .member 164515435212 },
  { wordCode := 70828, rule := .member 119465772953 },
  { wordCode := 70836, rule := .member 168297035878 },
  { wordCode := 70840, rule := .member 246727683379 },
  { wordCode := 70884, rule := .member 196593472204 },
  { wordCode := 70888, rule := .member 200888439500 },
  { wordCode := 70900, rule := .member 255830984601 },
  { wordCode := 70978, rule := .member 234912633548 },
  { wordCode := 70998, rule := .member 168030697572 },
  { wordCode := 71010, rule := .member 127538451148 },
  { wordCode := 71014, rule := .member 131833418444 },
  { wordCode := 71034, rule := .member 236680968294 },
  { wordCode := 71052, rule := .member 171050596452 },
  { wordCode := 71086, rule := .member 233838891724 },
  { wordCode := 71092, rule := .member 109758491955 },
  { wordCode := 71100, rule := .member 195184186060 },
  { wordCode := 71104, rule := .member 165119414988 },
  { wordCode := 71116, rule := .member 254019045273 },
  { wordCode := 71118, rule := .member 125523088078 },
  { wordCode := 71142, rule := .member 238696331364 },
  { wordCode := 71154, rule := .member 194177553100 },
  { wordCode := 71158, rule := .member 198472520396 },
  { wordCode := 71170, rule := .member 255025678233 },
  { wordCode := 71208, rule := .member 197128245966 },
  { wordCode := 71268, rule := .member 168836003940 },
  { wordCode := 71316, rule := .member 193907020494 },
  { wordCode := 71482, rule := .member 163693351628 },
  { wordCode := 71524, rule := .member 108164656435 },
  { wordCode := 71532, rule := .member 196778021580 },
  { wordCode := 71536, rule := .member 166713250508 },
  { wordCode := 71548, rule := .member 255646435225 },
  { wordCode := 71554, rule := .member 132353512140 },
  { wordCode := 71574, rule := .member 238274803814 },
  { wordCode := 71626, rule := .member 234358985420 },
  { wordCode := 71650, rule := .member 246476025139 },
  { wordCode := 71658, rule := .member 126984803020 },
  { wordCode := 71694, rule := .member 197045408460 },
  { wordCode := 71712, rule := .member 111146062540 },
  { wordCode := 71724, rule := .member 163731844403 },
  { wordCode := 71736, rule := .member 237472643172 },
  { wordCode := 71766, rule := .member 108126163660 },
  { wordCode := 71778, rule := .member 166751743283 },
  { wordCode := 71790, rule := .member 255659145316 },
  { wordCode := 71796, rule := .member 132392004913 },
  { wordCode := 71868, rule := .member 234397478195 },
  { wordCode := 71892, rule := .member 246437532364 },
  { wordCode := 71904, rule := .member 131318263089 },
  { wordCode := 71914, rule := .member 199192892108 },
  { wordCode := 71926, rule := .member 254301112217 },
  { wordCode := 71946, rule := .member 247779709644 },
  { wordCode := 71950, rule := .member 234895856332 },
  { wordCode := 71970, rule := .member 168011823206 },
  { wordCode := 71982, rule := .member 110340756172 },
  { wordCode := 71986, rule := .member 131815592652 },
  { wordCode := 71994, rule := .member 164537150771 },
  { wordCode := 72006, rule := .member 236667336804 },
  { wordCode := 72058, rule := .member 233822114508 },
  { wordCode := 72064, rule := .member 109775269171 },
  { wordCode := 72072, rule := .member 195166360268 },
  { wordCode := 72076, rule := .member 165102637772 },
  { wordCode := 72088, rule := .member 254032676761 },
  { wordCode := 72090, rule := .member 125507359436 },
  { wordCode := 72102, rule := .member 200910155057 },
  { wordCode := 72114, rule := .member 238680602724 },
  { wordCode := 72130, rule := .member 198455743180 },
  { wordCode := 72142, rule := .member 255042455449 },
  { wordCode := 72150, rule := .member 118421518436 },
  { wordCode := 72182, rule := .member 197092210796 },
  { wordCode := 72200, rule := .member 111192864876 },
  { wordCode := 72212, rule := .member 163685042067 },
  { wordCode := 72224, rule := .member 237451530950 },
  { wordCode := 72254, rule := .member 108172965996 },
  { wordCode := 72266, rule := .member 166704940947 },
  { wordCode := 72380, rule := .member 246484334700 },
  { wordCode := 72674, rule := .member 171282191046 },
  { wordCode := 72680, rule := .member 234887546771 },
  { wordCode := 72788, rule := .member 233813804947 },
  { wordCode := 72794, rule := .member 109783578732 },
  { wordCode := 72806, rule := .member 165094328211 },
  { wordCode := 72890, rule := .member 169134707398 },
  { wordCode := 73010, rule := .member 110876194924 },
  { wordCode := 73022, rule := .member 164001712019 },
  { wordCode := 73082, rule := .member 247241406572 },
  { wordCode := 73130, rule := .member 165075453843 },
  { wordCode := 73154, rule := .member 197041879148 },
  { wordCode := 73172, rule := .member 111142533228 },
  { wordCode := 73184, rule := .member 163733276563 },
  { wordCode := 73196, rule := .member 237468308166 },
  { wordCode := 73220, rule := .member 232385644435 },
  { wordCode := 73226, rule := .member 108122634348 },
  { wordCode := 73238, rule := .member 166755272595 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk013 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 73298, rule := .member 245429467244 },
  { wordCode := 73328, rule := .member 234401007507 },
  { wordCode := 73352, rule := .member 246434003052 },
  { wordCode := 73370, rule := .member 194894395500 },
  { wordCode := 73406, rule := .member 247776180332 },
  { wordCode := 73454, rule := .member 164540680083 },
  { wordCode := 73466, rule := .member 236663001798 },
  { wordCode := 73484, rule := .member 171030532806 },
  { wordCode := 73514, rule := .member 246702438508 },
  { wordCode := 73730, rule := .member 247056857196 },
  { wordCode := 73760, rule := .member 233979479955 },
  { wordCode := 73868, rule := .member 232905738131 },
  { wordCode := 74144, rule := .member 111161407596 },
  { wordCode := 74156, rule := .member 163716499347 },
  { wordCode := 74192, rule := .member 232368867219 },
  { wordCode := 74270, rule := .member 245446244460 },
  { wordCode := 74324, rule := .member 246452877420 },
  { wordCode := 74392, rule := .member 119782197128 },
  { wordCode := 74400, rule := .member 167980611700 },
  { wordCode := 74412, rule := .member 127554425566 },
  { wordCode := 74436, rule := .member 236634028148 },
  { wordCode := 74446, rule := .member 116762298248 },
  { wordCode := 74454, rule := .member 171000510580 },
  { wordCode := 74502, rule := .member 195200160478 },
  { wordCode := 74520, rule := .member 125540111070 },
  { wordCode := 74524, rule := .member 129835078365 },
  { wordCode := 74532, rule := .member 200876354849 },
  { wordCode := 74544, rule := .member 238646245492 },
  { wordCode := 74556, rule := .member 194192478942 },
  { wordCode := 74560, rule := .member 198487446237 },
  { wordCode := 74572, rule := .member 255073666952 },
  { wordCode := 74616, rule := .member 171269994612 },
  { wordCode := 74658, rule := .member 131821333793 },
  { wordCode := 74748, rule := .member 199467068705 },
  { wordCode := 74790, rule := .member 127957078750 },
  { wordCode := 74802, rule := .member 198460435745 },
  { wordCode := 74814, rule := .member 237841987700 },
  { wordCode := 74848, rule := .member 129298207453 },
  { wordCode := 74868, rule := .member 239183116404 },
  { wordCode := 74952, rule := .member 128224465630 },
  { wordCode := 74956, rule := .member 132519432925 },
  { wordCode := 74976, rule := .member 238109374580 },
  { wordCode := 74986, rule := .member 118372910984 },
  { wordCode := 75142, rule := .member 127542095138 },
  { wordCode := 75166, rule := .member 236637603720 },
  { wordCode := 75184, rule := .member 171005134728 },
  { wordCode := 75202, rule := .member 119465527176 },
  { wordCode := 75232, rule := .member 195187830050 },
  { wordCode := 75250, rule := .member 125528829218 },
  { wordCode := 75262, rule := .member 200888685277 },
  { wordCode := 75274, rule := .member 238650869640 },
  { wordCode := 75310, rule := .member 118391785352 },
  { wordCode := 75346, rule := .member 171273570184 },
  { wordCode := 75364, rule := .member 119731865480 },
  { wordCode := 75372, rule := .member 168030943348 },
  { wordCode := 75388, rule := .member 131833664221 },
  { wordCode := 75418, rule := .member 116711966600 },
  { wordCode := 75426, rule := .member 171050842228 },
  { wordCode := 75478, rule := .member 199479399133 },
  { wordCode := 75490, rule := .member 254018799496 },
  { wordCode := 75492, rule := .member 125523333854 },
  { wordCode := 75496, rule := .member 129818301149 },
  { wordCode := 75516, rule := .member 238696577140 },
  { wordCode := 75520, rule := .member 127944748322 },
  { wordCode := 75528, rule := .member 194175701726 },
  { wordCode := 75532, rule := .member 198470669021 },
  { wordCode := 75544, rule := .member 237845563272 },
  { wordCode := 75562, rule := .member 169126086536 },
  { wordCode := 75586, rule := .member 201423459037 },
  { wordCode := 75598, rule := .member 256365512584 },
  { wordCode := 75634, rule := .member 118926559112 },
  { wordCode := 75642, rule := .member 168836249716 },
  { wordCode := 75694, rule := .member 198202233565 },
  { wordCode := 75706, rule := .member 255291770760 },
  { wordCode := 75826, rule := .member 197083655458 },
  { wordCode := 75844, rule := .member 128364178722 },
  { wordCode := 75868, rule := .member 237459687304 },
  { wordCode := 75922, rule := .member 255646189448 },
  { wordCode := 75928, rule := .member 132353757917 },
  { wordCode := 76036, rule := .member 131280016093 },
  { wordCode := 76042, rule := .member 194936171810 },
  { wordCode := 76110, rule := .member 237472888948 },
  { wordCode := 76152, rule := .member 201111235873 },
  { wordCode := 76164, rule := .member 255659391092 },
  { wordCode := 76284, rule := .member 194898170590 },
  { wordCode := 76336, rule := .member 119750739848 },
  { wordCode := 76356, rule := .member 127520871134 },
  { wordCode := 76360, rule := .member 131816887005 },
  { wordCode := 76380, rule := .member 236667582580 },
  { wordCode := 76398, rule := .member 171035113588 },
  { wordCode := 76446, rule := .member 195166606046 },
  { wordCode := 76450, rule := .member 199462621917 },
  { wordCode := 76462, rule := .member 254035576712 },
  { wordCode := 76464, rule := .member 125507605214 },
  { wordCode := 76476, rule := .member 200909909281 },
  { wordCode := 76488, rule := .member 238680848500 },
  { wordCode := 76492, rule := .member 127961525538 },
  { wordCode := 76504, rule := .member 198455988957 },
  { wordCode := 76516, rule := .member 237862340488 },
  { wordCode := 76534, rule := .member 169142863752 },
  { wordCode := 76558, rule := .member 201386808004 },
  { wordCode := 76570, rule := .member 256403261320 },
  { wordCode := 76576, rule := .member 132667331268 },
  { wordCode := 76580, rule := .member 119782429380 },
  { wordCode := 76606, rule := .member 118964307848 },
  { wordCode := 76634, rule := .member 116762530500 },
  { wordCode := 76666, rule := .member 198231593693 },
  { wordCode := 76678, rule := .member 255329519496 },
  { wordCode := 76748, rule := .member 198487279505 },
  { wordCode := 76760, rule := .member 255073899204 },
  { wordCode := 76774, rule := .member 199239324356 },
  { wordCode := 76786, rule := .member 254321854353 },
  { wordCode := 76792, rule := .member 129310790365 },
  { wordCode := 76900, rule := .member 132532015837 },
  { wordCode := 76930, rule := .member 118360328072 },
  { wordCode := 77036, rule := .member 129298040721 },
  { wordCode := 77038, rule := .member 116480247697 },
  { wordCode := 77144, rule := .member 132519266193 },
  { wordCode := 77174, rule := .member 118373143236 },
  { wordCode := 77224, rule := .member 132264678084 },
  { wordCode := 77254, rule := .member 118627731345 },
  { wordCode := 77284, rule := .member 197153910050 },
  { wordCode := 77350, rule := .member 232342868676 },
  { wordCode := 77356, rule := .member 108167507259 },
  { wordCode := 77368, rule := .member 166710399684 },
  { wordCode := 77372, rule := .member 171005366980 },
  { wordCode := 77390, rule := .member 119465759428 },
  { wordCode := 77392, rule := .member 193932684578 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk014 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 77420, rule := .member 195187996782 },
  { wordCode := 77428, rule := .member 245472243003 },
  { wordCode := 77458, rule := .member 234356134596 },
  { wordCode := 77498, rule := .member 118392017604 },
  { wordCode := 77518, rule := .member 107899071803 },
  { wordCode := 77530, rule := .member 166978835140 },
  { wordCode := 77542, rule := .member 239207663496 },
  { wordCode := 77548, rule := .member 132616999620 },
  { wordCode := 77576, rule := .member 131833497489 },
  { wordCode := 77626, rule := .member 128233106722 },
  { wordCode := 77650, rule := .member 238133921672 },
  { wordCode := 77666, rule := .member 199479232401 },
  { wordCode := 77678, rule := .member 254019031748 },
  { wordCode := 77708, rule := .member 127944915054 },
  { wordCode := 77720, rule := .member 198470502289 },
  { wordCode := 77728, rule := .member 233550828228 },
  { wordCode := 77732, rule := .member 237845795524 },
  { wordCode := 77734, rule := .member 110046555451 },
  { wordCode := 77746, rule := .member 164831351492 },
  { wordCode := 77750, rule := .member 169126318788 },
  { wordCode := 77758, rule := .member 254305077137 },
  { wordCode := 77818, rule := .member 131811693252 },
  { wordCode := 77848, rule := .member 116731905937 },
  { wordCode := 77882, rule := .member 198202066833 },
  { wordCode := 77894, rule := .member 255292003012 },
  { wordCode := 77908, rule := .member 199457428164 },
  { wordCode := 77920, rule := .member 254036641681 },
  { wordCode := 78014, rule := .member 197083822190 },
  { wordCode := 78022, rule := .member 247871384891 },
  { wordCode := 78052, rule := .member 233164952260 },
  { wordCode := 78110, rule := .member 255646421700 },
  { wordCode := 78116, rule := .member 132353591185 },
  { wordCode := 78166, rule := .member 125531974946 },
  { wordCode := 78190, rule := .member 238654015368 },
  { wordCode := 78202, rule := .member 194184342818 },
  { wordCode := 78334, rule := .member 116716160904 },
  { wordCode := 78412, rule := .member 129814106845 },
  { wordCode := 78448, rule := .member 198466474717 },
  { wordCode := 78460, rule := .member 255027529608 },
  { wordCode := 78490, rule := .member 107882294587 },
  { wordCode := 78502, rule := .member 166995612356 },
  { wordCode := 78514, rule := .member 239190886280 },
  { wordCode := 78550, rule := .member 118930753416 },
  { wordCode := 78598, rule := .member 128216329506 },
  { wordCode := 78610, rule := .member 198198039261 },
  { wordCode := 78622, rule := .member 238117144456 },
  { wordCode := 78638, rule := .member 199462455185 },
  { wordCode := 78650, rule := .member 254035808964 },
  { wordCode := 78680, rule := .member 127961692270 },
  { wordCode := 78692, rule := .member 198455822225 },
  { wordCode := 78704, rule := .member 237862572740 },
  { wordCode := 78706, rule := .member 110029778235 },
  { wordCode := 78718, rule := .member 164848128708 },
  { wordCode := 78742, rule := .member 197092339000 },
  { wordCode := 78752, rule := .member 247813863532 },
  { wordCode := 78760, rule := .member 111192993080 },
  { wordCode := 78772, rule := .member 163684913860 },
  { wordCode := 78784, rule := .member 237451397010 },
  { wordCode := 78788, rule := .member 110374910060 },
  { wordCode := 78800, rule := .member 164502996883 },
  { wordCode := 78808, rule := .member 232338330308 },
  { wordCode := 78812, rule := .member 236633297604 },
  { wordCode := 78814, rule := .member 108173094200 },
  { wordCode := 78822, rule := .member 196769583820 },
  { wordCode := 78826, rule := .member 166704812740 },
  { wordCode := 78838, rule := .member 255637882769 },
  { wordCode := 78840, rule := .member 110871286476 },
  { wordCode := 78844, rule := .member 132345074372 },
  { wordCode := 78852, rule := .member 164006620467 },
  { wordCode := 78860, rule := .member 246740121708 },
  { wordCode := 78864, rule := .member 238283339878 },
  { wordCode := 78878, rule := .member 195200514156 },
  { wordCode := 78886, rule := .member 245476781363 },
  { wordCode := 78896, rule := .member 125541513324 },
  { wordCode := 78908, rule := .member 200876001169 },
  { wordCode := 78912, rule := .member 247236498124 },
  { wordCode := 78920, rule := .member 238645514948 },
  { wordCode := 78940, rule := .member 246484462904 },
  { wordCode := 78948, rule := .member 109797544652 },
  { wordCode := 78972, rule := .member 237209598054 },
  { wordCode := 78988, rule := .member 166974296772 },
  { wordCode := 78998, rule := .member 234900195219 },
  { wordCode := 79002, rule := .member 111139721932 },
  { wordCode := 79014, rule := .member 163738185011 },
  { wordCode := 79034, rule := .member 131820980113 },
  { wordCode := 79106, rule := .member 233826453395 },
  { wordCode := 79112, rule := .member 109770930284 },
  { wordCode := 79124, rule := .member 165106976659 },
  { wordCode := 79136, rule := .member 254014493380 },
  { wordCode := 79178, rule := .member 198460082065 },
  { wordCode := 79186, rule := .member 233546289860 },
  { wordCode := 79190, rule := .member 237841257156 },
  { wordCode := 79204, rule := .member 164826813124 },
  { wordCode := 79208, rule := .member 169121780420 },
  { wordCode := 79220, rule := .member 125003577454 },
  { wordCode := 79240, rule := .member 234887418564 },
  { wordCode := 79244, rule := .member 239182385860 },
  { wordCode := 79252, rule := .member 119742433169 },
  { wordCode := 79260, rule := .member 168020359270 },
  { wordCode := 79272, rule := .member 127513236172 },
  { wordCode := 79276, rule := .member 131808203460 },
  { wordCode := 79296, rule := .member 236672727142 },
  { wordCode := 79362, rule := .member 195158971084 },
  { wordCode := 79370, rule := .member 169389167300 },
  { wordCode := 79378, rule := .member 254027270033 },
  { wordCode := 79408, rule := .member 127970209080 },
  { wordCode := 79432, rule := .member 237854050194 },
  { wordCode := 79570, rule := .member 110876323128 },
  { wordCode := 79582, rule := .member 164001583815 },
  { wordCode := 79586, rule := .member 168296567494 },
  { wordCode := 79634, rule := .member 196594071660 },
  { wordCode := 79642, rule := .member 247241534776 },
  { wordCode := 79678, rule := .member 109802581304 },
  { wordCode := 79714, rule := .member 197042007352 },
  { wordCode := 79732, rule := .member 111142661432 },
  { wordCode := 79744, rule := .member 163735245508 },
  { wordCode := 79748, rule := .member 168030212804 },
  { wordCode := 79756, rule := .member 237468174226 },
  { wordCode := 79760, rule := .member 127539050604 },
  { wordCode := 79780, rule := .member 232385516231 },
  { wordCode := 79784, rule := .member 236680499910 },
  { wordCode := 79786, rule := .member 108122762552 },
  { wordCode := 79794, rule := .member 196819915468 },
  { wordCode := 79798, rule := .member 166755144388 },
  { wordCode := 79802, rule := .member 171050111684 },
  { wordCode := 79810, rule := .member 255654659985 },
  { wordCode := 79812, rule := .member 128100438732 },
  { wordCode := 79836, rule := .member 238266562662 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk015 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 79850, rule := .member 195184785516 },
  { wordCode := 79858, rule := .member 245429595448 },
  { wordCode := 79868, rule := .member 125523671150 },
  { wordCode := 79888, rule := .member 234400879300 },
  { wordCode := 79892, rule := .member 238695846596 },
  { wordCode := 79912, rule := .member 246434131256 },
  { wordCode := 79958, rule := .member 197128829038 },
  { wordCode := 79966, rule := .member 247776308536 },
  { wordCode := 80002, rule := .member 110337355064 },
  { wordCode := 80014, rule := .member 164540551876 },
  { wordCode := 80018, rule := .member 168835519172 },
  { wordCode := 80026, rule := .member 236662867858 },
  { wordCode := 80044, rule := .member 171030398866 },
  { wordCode := 80066, rule := .member 193907603566 },
  { wordCode := 80070, rule := .member 168272017510 },
  { wordCode := 80074, rule := .member 246702566712 },
  { wordCode := 80092, rule := .member 195162959160 },
  { wordCode := 80110, rule := .member 125503958328 },
  { wordCode := 80122, rule := .member 200913556164 },
  { wordCode := 80134, rule := .member 238676133778 },
  { wordCode := 80170, rule := .member 118417033105 },
  { wordCode := 80282, rule := .member 196778621036 },
  { wordCode := 80290, rule := .member 247056985400 },
  { wordCode := 80324, rule := .member 238274335430 },
  { wordCode := 80408, rule := .member 126985402476 },
  { wordCode := 80428, rule := .member 232905609927 },
  { wordCode := 80432, rule := .member 237200593606 },
  { wordCode := 80474, rule := .member 163731244947 },
  { wordCode := 80482, rule := .member 233177191108 },
  { wordCode := 80486, rule := .member 237472158404 },
  { wordCode := 80516, rule := .member 108126763116 },
  { wordCode := 80528, rule := .member 166751143827 },
  { wordCode := 80532, rule := .member 247068725964 },
  { wordCode := 80540, rule := .member 255658660548 },
  { wordCode := 80562, rule := .member 233967611187 },
  { wordCode := 80618, rule := .member 234396878739 },
  { wordCode := 80642, rule := .member 246438131820 },
  { wordCode := 80660, rule := .member 194898524268 },
  { wordCode := 80668, rule := .member 245711662387 },
  { wordCode := 80670, rule := .member 232893869363 },
  { wordCode := 80696, rule := .member 247780309100 },
  { wordCode := 80704, rule := .member 111161535800 },
  { wordCode := 80716, rule := .member 163716371143 },
  { wordCode := 80720, rule := .member 168011354822 },
  { wordCode := 80732, rule := .member 110341355628 },
  { wordCode := 80744, rule := .member 164536551315 },
  { wordCode := 80756, rule := .member 236666852036 },
  { wordCode := 80758, rule := .member 108138491187 },
  { wordCode := 80770, rule := .member 166739415748 },
  { wordCode := 80784, rule := .member 110904840908 },
  { wordCode := 80796, rule := .member 163973066035 },
  { wordCode := 80840, rule := .member 125507958892 },
  { wordCode := 80852, rule := .member 200909555601 },
  { wordCode := 80860, rule := .member 234385150660 },
  { wordCode := 80864, rule := .member 238680117956 },
  { wordCode := 80876, rule := .member 194161375340 },
  { wordCode := 80884, rule := .member 246453005624 },
  { wordCode := 80950, rule := .member 132667003588 },
  { wordCode := 81008, rule := .member 116762202820 },
  { wordCode := 81086, rule := .member 129834977169 },
  { wordCode := 81122, rule := .member 198487345041 },
  { wordCode := 81134, rule := .member 255073571524 },
  { wordCode := 81148, rule := .member 199238996676 },
  { wordCode := 81160, rule := .member 254321919889 },
  { wordCode := 81518, rule := .member 132519331729 },
  { wordCode := 81548, rule := .member 118372815556 },
  { wordCode := 81598, rule := .member 132264350404 },
  { wordCode := 81628, rule := .member 118627796881 },
  { wordCode := 81724, rule := .member 232342540996 },
  { wordCode := 81730, rule := .member 108167834939 },
  { wordCode := 81742, rule := .member 166710072004 },
  { wordCode := 81794, rule := .member 195187931246 },
  { wordCode := 81802, rule := .member 245472570683 },
  { wordCode := 81832, rule := .member 234355806916 },
  { wordCode := 81922, rule := .member 132616671940 },
  { wordCode := 82040, rule := .member 199479297937 },
  { wordCode := 82052, rule := .member 254018704068 },
  { wordCode := 82082, rule := .member 127944849518 },
  { wordCode := 82094, rule := .member 198470567825 },
  { wordCode := 82102, rule := .member 233550500548 },
  { wordCode := 82106, rule := .member 237845467844 },
  { wordCode := 82108, rule := .member 110046883131 },
  { wordCode := 82120, rule := .member 164831023812 },
  { wordCode := 82124, rule := .member 169125991108 },
  { wordCode := 82132, rule := .member 254305142673 },
  { wordCode := 82396, rule := .member 247871712571 },
  { wordCode := 82426, rule := .member 233164624580 },
  { wordCode := 82472, rule := .member 201073133457 },
  { wordCode := 82604, rule := .member 194936273006 },
  { wordCode := 82612, rule := .member 245724228923 },
  { wordCode := 83012, rule := .member 199462520721 },
  { wordCode := 83024, rule := .member 254035481284 },
  { wordCode := 83054, rule := .member 127961626734 },
  { wordCode := 83066, rule := .member 198455887761 },
  { wordCode := 83074, rule := .member 233567277764 },
  { wordCode := 83078, rule := .member 237862245060 },
  { wordCode := 83080, rule := .member 110030105915 },
  { wordCode := 83092, rule := .member 164847801028 },
  { wordCode := 83120, rule := .member 201452734353 },
  { wordCode := 83124, rule := .member 247813214924 },
  { wordCode := 83132, rule := .member 256403149508 },
  { wordCode := 83140, rule := .member 119782295448 },
  { wordCode := 83160, rule := .member 110374261452 },
  { wordCode := 83164, rule := .member 131849097924 },
  { wordCode := 83172, rule := .member 164503645491 },
  { wordCode := 83184, rule := .member 236633929830 },
  { wordCode := 83194, rule := .member 116762396568 },
  { wordCode := 83202, rule := .member 171001460838 },
  { wordCode := 83250, rule := .member 195199865548 },
  { wordCode := 83254, rule := .member 199494832836 },
  { wordCode := 83266, rule := .member 254066083729 },
  { wordCode := 83268, rule := .member 125540864716 },
  { wordCode := 83292, rule := .member 238647195750 },
  { wordCode := 83308, rule := .member 198487151309 },
  { wordCode := 83320, rule := .member 255073765272 },
  { wordCode := 83354, rule := .member 129310705553 },
  { wordCode := 83364, rule := .member 171269896294 },
  { wordCode := 83370, rule := .member 234900843827 },
  { wordCode := 83462, rule := .member 132531931025 },
  { wordCode := 83484, rule := .member 109770281676 },
  { wordCode := 83496, rule := .member 165107625267 },
  { wordCode := 83538, rule := .member 127956783820 },
  { wordCode := 83542, rule := .member 132251751108 },
  { wordCode := 83562, rule := .member 237841889382 },
  { wordCode := 83596, rule := .member 129297912525 },
  { wordCode := 83734, rule := .member 118373009304 },
  { wordCode := 83854, rule := .member 247801474355 },
  { wordCode := 83914, rule := .member 236637702040 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk016 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 83932, rule := .member 171005233048 },
  { wordCode := 83954, rule := .member 193932769390 },
  { wordCode := 83980, rule := .member 195188124978 },
  { wordCode := 83998, rule := .member 125529124146 },
  { wordCode := 84006, rule := .member 196593423052 },
  { wordCode := 84010, rule := .member 200888390340 },
  { wordCode := 84058, rule := .member 118391883672 },
  { wordCode := 84080, rule := .member 125011966062 },
  { wordCode := 84104, rule := .member 239207551684 },
  { wordCode := 84112, rule := .member 119731963800 },
  { wordCode := 84120, rule := .member 168028747878 },
  { wordCode := 84132, rule := .member 127538401996 },
  { wordCode := 84156, rule := .member 236681115750 },
  { wordCode := 84214, rule := .member 109758541107 },
  { wordCode := 84226, rule := .member 165119365828 },
  { wordCode := 84238, rule := .member 254018897816 },
  { wordCode := 84244, rule := .member 129818006221 },
  { wordCode := 84268, rule := .member 127945043250 },
  { wordCode := 84276, rule := .member 194177503948 },
  { wordCode := 84280, rule := .member 198472471236 },
  { wordCode := 84292, rule := .member 237845661592 },
  { wordCode := 84310, rule := .member 169126184856 },
  { wordCode := 84334, rule := .member 201423164109 },
  { wordCode := 84574, rule := .member 197083950386 },
  { wordCode := 84616, rule := .member 237459785624 },
  { wordCode := 84646, rule := .member 108164705587 },
  { wordCode := 84654, rule := .member 196777972428 },
  { wordCode := 84658, rule := .member 166713201348 },
  { wordCode := 84662, rule := .member 171008168644 },
  { wordCode := 84670, rule := .member 255646287768 },
  { wordCode := 84728, rule := .member 125532059758 },
  { wordCode := 84748, rule := .member 234358936260 },
  { wordCode := 84752, rule := .member 238653903556 },
  { wordCode := 84764, rule := .member 194184427630 },
  { wordCode := 84772, rule := .member 246476074291 },
  { wordCode := 84780, rule := .member 126984753868 },
  { wordCode := 84834, rule := .member 111146013388 },
  { wordCode := 84858, rule := .member 237472790630 },
  { wordCode := 84888, rule := .member 108126114508 },
  { wordCode := 84900, rule := .member 166751792435 },
  { wordCode := 84974, rule := .member 129814022033 },
  { wordCode := 84990, rule := .member 234397527347 },
  { wordCode := 85036, rule := .member 199192842948 },
  { wordCode := 85064, rule := .member 201419179921 },
  { wordCode := 85068, rule := .member 247779660492 },
  { wordCode := 85076, rule := .member 239190774468 },
  { wordCode := 85104, rule := .member 110340707020 },
  { wordCode := 85116, rule := .member 164537199923 },
  { wordCode := 85128, rule := .member 236664338534 },
  { wordCode := 85146, rule := .member 171035015270 },
  { wordCode := 85186, rule := .member 109775318323 },
  { wordCode := 85198, rule := .member 165102588612 },
  { wordCode := 85210, rule := .member 254035675032 },
  { wordCode := 85212, rule := .member 125507310284 },
  { wordCode := 85236, rule := .member 238680750182 },
  { wordCode := 85240, rule := .member 127961820466 },
  { wordCode := 85252, rule := .member 198455694020 },
  { wordCode := 85264, rule := .member 237862438808 },
  { wordCode := 87508, rule := .member 111192206648 },
  { wordCode := 87520, rule := .member 163685700292 },
  { wordCode := 87524, rule := .member 167980667588 },
  { wordCode := 87532, rule := .member 237451659154 },
  { wordCode := 87536, rule := .member 127554500718 },
  { wordCode := 87556, rule := .member 232339116740 },
  { wordCode := 87560, rule := .member 236634084036 },
  { wordCode := 87562, rule := .member 108172307768 },
  { wordCode := 87570, rule := .member 196770370252 },
  { wordCode := 87574, rule := .member 166705599172 },
  { wordCode := 87578, rule := .member 171000566468 },
  { wordCode := 87586, rule := .member 255638161297 },
  { wordCode := 87588, rule := .member 110872072908 },
  { wordCode := 87592, rule := .member 132345860804 },
  { wordCode := 87600, rule := .member 164005834035 },
  { wordCode := 87612, rule := .member 238283077734 },
  { wordCode := 87626, rule := .member 195200235630 },
  { wordCode := 87644, rule := .member 125540186222 },
  { wordCode := 87656, rule := .member 200876279697 },
  { wordCode := 87660, rule := .member 247237284556 },
  { wordCode := 87668, rule := .member 238646301380 },
  { wordCode := 87688, rule := .member 246483676472 },
  { wordCode := 87736, rule := .member 166975083204 },
  { wordCode := 87782, rule := .member 131821258641 },
  { wordCode := 87872, rule := .member 199466993553 },
  { wordCode := 87884, rule := .member 254015279812 },
  { wordCode := 87914, rule := .member 127957153902 },
  { wordCode := 87926, rule := .member 198460360593 },
  { wordCode := 87934, rule := .member 233547076292 },
  { wordCode := 87956, rule := .member 169122566852 },
  { wordCode := 87968, rule := .member 125003315310 },
  { wordCode := 87982, rule := .member 171282319250 },
  { wordCode := 87988, rule := .member 234888204996 },
  { wordCode := 87992, rule := .member 239183172292 },
  { wordCode := 88000, rule := .member 119742711697 },
  { wordCode := 88020, rule := .member 127514022604 },
  { wordCode := 88096, rule := .member 233814463172 },
  { wordCode := 88100, rule := .member 238109430468 },
  { wordCode := 88118, rule := .member 169389953732 },
  { wordCode := 88126, rule := .member 254027548561 },
  { wordCode := 88156, rule := .member 127969422648 },
  { wordCode := 88168, rule := .member 198448091844 },
  { wordCode := 88198, rule := .member 169134835602 },
  { wordCode := 88318, rule := .member 110875536696 },
  { wordCode := 88462, rule := .member 197041220920 },
  { wordCode := 88480, rule := .member 111141875000 },
  { wordCode := 88492, rule := .member 163736031940 },
  { wordCode := 88496, rule := .member 168030999236 },
  { wordCode := 88504, rule := .member 237468436370 },
  { wordCode := 88528, rule := .member 232386302663 },
  { wordCode := 88534, rule := .member 108121976120 },
  { wordCode := 88542, rule := .member 196820701900 },
  { wordCode := 88546, rule := .member 166755930820 },
  { wordCode := 88550, rule := .member 171050898116 },
  { wordCode := 88558, rule := .member 255654938513 },
  { wordCode := 88560, rule := .member 128101225164 },
  { wordCode := 88584, rule := .member 238266300518 },
  { wordCode := 88606, rule := .member 245428809016 },
  { wordCode := 88616, rule := .member 125523409006 },
  { wordCode := 88636, rule := .member 234401665732 },
  { wordCode := 88640, rule := .member 238696633028 },
  { wordCode := 88706, rule := .member 197128566894 },
  { wordCode := 88750, rule := .member 110336568632 },
  { wordCode := 88762, rule := .member 164541338308 },
  { wordCode := 88766, rule := .member 168836305604 },
  { wordCode := 88774, rule := .member 236663130002 },
  { wordCode := 88792, rule := .member 171030661010 },
  { wordCode := 88814, rule := .member 193907341422 },
  { wordCode := 88822, rule := .member 246701780280 },
  { wordCode := 88840, rule := .member 195162172728 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk017 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 88870, rule := .member 200914342596 },
  { wordCode := 89176, rule := .member 232906396359 },
  { wordCode := 89210, rule := .member 128326252654 },
  { wordCode := 89230, rule := .member 233177977540 },
  { wordCode := 89234, rule := .member 237472944836 },
  { wordCode := 89280, rule := .member 247069512396 },
  { wordCode := 89288, rule := .member 255659446980 },
  { wordCode := 89310, rule := .member 233966824755 },
  { wordCode := 89408, rule := .member 194898245742 },
  { wordCode := 89416, rule := .member 245710875955 },
  { wordCode := 89452, rule := .member 111160749368 },
  { wordCode := 89464, rule := .member 163717157575 },
  { wordCode := 89480, rule := .member 127520946286 },
  { wordCode := 89500, rule := .member 232372671172 },
  { wordCode := 89504, rule := .member 236667638468 },
  { wordCode := 89506, rule := .member 108137704755 },
  { wordCode := 89518, rule := .member 166740202180 },
  { wordCode := 89522, rule := .member 171035169476 },
  { wordCode := 89532, rule := .member 110905627340 },
  { wordCode := 89544, rule := .member 163972279603 },
  { wordCode := 89570, rule := .member 195166681198 },
  { wordCode := 89588, rule := .member 125507680366 },
  { wordCode := 89600, rule := .member 200909834129 },
  { wordCode := 89608, rule := .member 234385937092 },
  { wordCode := 89612, rule := .member 238680904388 },
  { wordCode := 89632, rule := .member 246452219192 },
  { wordCode := 89722, rule := .member 110374317368 },
  { wordCode := 89734, rule := .member 164503589575 },
  { wordCode := 89746, rule := .member 236633769880 },
  { wordCode := 89794, rule := .member 246739529016 },
  { wordCode := 89812, rule := .member 195199921464 },
  { wordCode := 89830, rule := .member 125540920632 },
  { wordCode := 89842, rule := .member 200876593869 },
  { wordCode := 89854, rule := .member 238645987224 },
  { wordCode := 89866, rule := .member 194192239922 },
  { wordCode := 89890, rule := .member 118387951512 },
  { wordCode := 89932, rule := .member 234900787911 },
  { wordCode := 89968, rule := .member 131821572813 },
  { wordCode := 90040, rule := .member 233827046087 },
  { wordCode := 90070, rule := .member 254014965656 },
  { wordCode := 90112, rule := .member 198460674765 },
  { wordCode := 90142, rule := .member 169122252696 },
  { wordCode := 90154, rule := .member 125003001138 },
  { wordCode := 90178, rule := .member 239182858136 },
  { wordCode := 90568, rule := .member 196593478968 },
  { wordCode := 90682, rule := .member 168030685080 },
  { wordCode := 90694, rule := .member 127538457912 },
  { wordCode := 90718, rule := .member 236680955794 },
  { wordCode := 90736, rule := .member 171050583960 },
  { wordCode := 90784, rule := .member 195184192824 },
  { wordCode := 90802, rule := .member 125523094834 },
  { wordCode := 90826, rule := .member 238696318872 },
  { wordCode := 90892, rule := .member 197128252722 },
  { wordCode := 90952, rule := .member 168835991448 },
  { wordCode := 91378, rule := .member 197045415224 },
  { wordCode := 91396, rule := .member 111146069304 },
  { wordCode := 91408, rule := .member 163731837639 },
  { wordCode := 91420, rule := .member 237472630680 },
  { wordCode := 91462, rule := .member 166751736519 },
  { wordCode := 91474, rule := .member 255659132824 },
  { wordCode := 91480, rule := .member 132391998157 },
  { wordCode := 91552, rule := .member 234397471431 },
  { wordCode := 91630, rule := .member 247779716408 },
  { wordCode := 91654, rule := .member 168011810706 },
  { wordCode := 91666, rule := .member 110340762936 },
  { wordCode := 91678, rule := .member 164537144007 },
  { wordCode := 91690, rule := .member 236667324312 },
  { wordCode := 91708, rule := .member 171034855320 },
  { wordCode := 91738, rule := .member 246705974584 },
  { wordCode := 91774, rule := .member 125507366200 },
  { wordCode := 91786, rule := .member 200910148301 },
  { wordCode := 91798, rule := .member 238680590232 },
  { wordCode := 91810, rule := .member 194160782648 },
  { wordCode := 94052, rule := .member 197091620972 },
  { wordCode := 94070, rule := .member 111192275052 },
  { wordCode := 94082, rule := .member 163685631891 },
  { wordCode := 94094, rule := .member 237451727558 },
  { wordCode := 94124, rule := .member 108172376172 },
  { wordCode := 94136, rule := .member 166705530771 },
  { wordCode := 94544, rule := .member 171282387654 },
  { wordCode := 94658, rule := .member 233814394771 },
  { wordCode := 94760, rule := .member 169134904006 },
  { wordCode := 94880, rule := .member 110875605100 },
  { wordCode := 94892, rule := .member 164002301843 },
  { wordCode := 95024, rule := .member 197041289324 },
  { wordCode := 95042, rule := .member 111141943404 },
  { wordCode := 95054, rule := .member 163733866387 },
  { wordCode := 95066, rule := .member 237468504774 },
  { wordCode := 95090, rule := .member 232386234259 },
  { wordCode := 95096, rule := .member 108122044524 },
  { wordCode := 95108, rule := .member 166755862419 },
  { wordCode := 95168, rule := .member 245428877420 },
  { wordCode := 95198, rule := .member 234401597331 },
  { wordCode := 95312, rule := .member 110336637036 },
  { wordCode := 95324, rule := .member 164541269907 },
  { wordCode := 95336, rule := .member 236663198406 },
  { wordCode := 95354, rule := .member 171030729414 },
  { wordCode := 95444, rule := .member 238676464326 },
  { wordCode := 95600, rule := .member 247056267372 },
  { wordCode := 95630, rule := .member 233980069779 },
  { wordCode := 95738, rule := .member 232906327955 },
  { wordCode := 96014, rule := .member 111160817772 },
  { wordCode := 96026, rule := .member 163717089171 },
  { wordCode := 96194, rule := .member 246452287596 },
  { wordCode := 96248, rule := .member 247813339244 },
  { wordCode := 96256, rule := .member 111192452411 },
  { wordCode := 96268, rule := .member 163685454532 },
  { wordCode := 96284, rule := .member 110374385772 },
  { wordCode := 96296, rule := .member 164503521171 },
  { wordCode := 96304, rule := .member 232338870980 },
  { wordCode := 96308, rule := .member 236633838276 },
  { wordCode := 96310, rule := .member 108171504955 },
  { wordCode := 96322, rule := .member 166705353412 },
  { wordCode := 96326, rule := .member 171000320708 },
  { wordCode := 96334, rule := .member 255638407057 },
  { wordCode := 96340, rule := .member 132345615044 },
  { wordCode := 96374, rule := .member 195199989868 },
  { wordCode := 96382, rule := .member 245476240699 },
  { wordCode := 96392, rule := .member 125540989036 },
  { wordCode := 96404, rule := .member 200876525457 },
  { wordCode := 96412, rule := .member 234351088324 },
  { wordCode := 96416, rule := .member 238646055620 },
  { wordCode := 96436, rule := .member 246483922235 },
  { wordCode := 96448, rule := .member 131271873220 },
  { wordCode := 96452, rule := .member 118388019908 },
  { wordCode := 96472, rule := .member 107903069499 },
  { wordCode := 96484, rule := .member 166974837444 },
  { wordCode := 96530, rule := .member 131821504401 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk018 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 96602, rule := .member 233826977683 },
  { wordCode := 96608, rule := .member 109770405996 },
  { wordCode := 96620, rule := .member 165107500947 },
  { wordCode := 96632, rule := .member 254015034052 },
  { wordCode := 96662, rule := .member 127956908140 },
  { wordCode := 96674, rule := .member 198460606353 },
  { wordCode := 96682, rule := .member 233546830532 },
  { wordCode := 96686, rule := .member 237841797828 },
  { wordCode := 96688, rule := .member 110050553147 },
  { wordCode := 96700, rule := .member 164827353796 },
  { wordCode := 96716, rule := .member 125003069550 },
  { wordCode := 96736, rule := .member 234887959236 },
  { wordCode := 96740, rule := .member 239182926532 },
  { wordCode := 96748, rule := .member 119742957457 },
  { wordCode := 96844, rule := .member 233814217412 },
  { wordCode := 96850, rule := .member 109783166267 },
  { wordCode := 96862, rule := .member 165094740676 },
  { wordCode := 96874, rule := .member 254027794321 },
  { wordCode := 96916, rule := .member 198447846084 },
  { wordCode := 97082, rule := .member 168297091782 },
  { wordCode := 97228, rule := .member 111142120763 },
  { wordCode := 97240, rule := .member 163735786180 },
  { wordCode := 97244, rule := .member 168030753476 },
  { wordCode := 97256, rule := .member 127538526316 },
  { wordCode := 97280, rule := .member 236681024198 },
  { wordCode := 97282, rule := .member 108122221883 },
  { wordCode := 97294, rule := .member 166755685060 },
  { wordCode := 97298, rule := .member 171050652356 },
  { wordCode := 97306, rule := .member 255655184273 },
  { wordCode := 97364, rule := .member 125523163246 },
  { wordCode := 97384, rule := .member 234401419972 },
  { wordCode := 97388, rule := .member 238696387268 },
  { wordCode := 97462, rule := .member 247775767867 },
  { wordCode := 97498, rule := .member 110336814395 },
  { wordCode := 97510, rule := .member 164541092548 },
  { wordCode := 97514, rule := .member 168836059844 },
  { wordCode := 97562, rule := .member 193907095662 },
  { wordCode := 97570, rule := .member 246702026043 },
  { wordCode := 97618, rule := .member 200914096836 },
  { wordCode := 97630, rule := .member 255856510865 },
  { wordCode := 97666, rule := .member 118417557393 },
  { wordCode := 97904, rule := .member 126984878188 },
  { wordCode := 97928, rule := .member 237201117894 },
  { wordCode := 97948, rule := .member 247858605371 },
  { wordCode := 97958, rule := .member 111146137708 },
  { wordCode := 97970, rule := .member 163731769235 },
  { wordCode := 97978, rule := .member 233177731780 },
  { wordCode := 97982, rule := .member 237472699076 },
  { wordCode := 98012, rule := .member 108126238828 },
  { wordCode := 98024, rule := .member 166751668115 },
  { wordCode := 98036, rule := .member 255659201220 },
  { wordCode := 98114, rule := .member 234397403027 },
  { wordCode := 98192, rule := .member 247779784812 },
  { wordCode := 98216, rule := .member 168011879110 },
  { wordCode := 98228, rule := .member 110340831340 },
  { wordCode := 98240, rule := .member 164537075603 },
  { wordCode := 98252, rule := .member 236667392708 },
  { wordCode := 98254, rule := .member 108137950523 },
  { wordCode := 98266, rule := .member 166739956420 },
  { wordCode := 98270, rule := .member 171034923716 },
  { wordCode := 98336, rule := .member 125507434604 },
  { wordCode := 98348, rule := .member 200910079889 },
  { wordCode := 98360, rule := .member 238680658628 },
  { wordCode := 98458, rule := .member 167979894664 },
  { wordCode := 98470, rule := .member 127554776354 },
  { wordCode := 98494, rule := .member 236633311112 },
  { wordCode := 98512, rule := .member 170999793544 },
  { wordCode := 98530, rule := .member 119461234568 },
  { wordCode := 98560, rule := .member 195200511266 },
  { wordCode := 98578, rule := .member 125540461858 },
  { wordCode := 98590, rule := .member 200876004061 },
  { wordCode := 98602, rule := .member 238645528456 },
  { wordCode := 98614, rule := .member 194192829730 },
  { wordCode := 98638, rule := .member 118387492744 },
  { wordCode := 98674, rule := .member 171269277576 },
  { wordCode := 98692, rule := .member 119729670024 },
  { wordCode := 98716, rule := .member 131820983005 },
  { wordCode := 98806, rule := .member 199466717917 },
  { wordCode := 98818, rule := .member 254014506888 },
  { wordCode := 98848, rule := .member 127957429538 },
  { wordCode := 98860, rule := .member 198460084957 },
  { wordCode := 98872, rule := .member 237841270664 },
  { wordCode := 98902, rule := .member 125003590946 },
  { wordCode := 98926, rule := .member 239182399368 },
  { wordCode := 99010, rule := .member 128224816418 },
  { wordCode := 99430, rule := .member 168030226312 },
  { wordCode := 99484, rule := .member 171050125192 },
  { wordCode := 99550, rule := .member 125523684642 },
  { wordCode := 99574, rule := .member 238695860104 },
  { wordCode := 99586, rule := .member 194176052514 },
  { wordCode := 99640, rule := .member 197128842530 },
  { wordCode := 99700, rule := .member 168835532680 },
  { wordCode := 100126, rule := .member 197046005026 },
  { wordCode := 100144, rule := .member 128326528290 },
  { wordCode := 100168, rule := .member 237472171912 },
  { wordCode := 100228, rule := .member 132391408349 },
  { wordCode := 100414, rule := .member 127521221922 },
  { wordCode := 100438, rule := .member 236666865544 },
  { wordCode := 100504, rule := .member 195166956834 },
  { wordCode := 100522, rule := .member 125507956002 },
  { wordCode := 100534, rule := .member 200909558493 },
  { wordCode := 100546, rule := .member 238680131464 },
  { wordCode := 100620, rule := .member 247813411548 },
  { wordCode := 100636, rule := .member 119782098824 },
  { wordCode := 100656, rule := .member 110374458076 },
  { wordCode := 100660, rule := .member 131849294556 },
  { wordCode := 100668, rule := .member 164503448867 },
  { wordCode := 100680, rule := .member 236634126454 },
  { wordCode := 100690, rule := .member 116762199944 },
  { wordCode := 100698, rule := .member 171001657462 },
  { wordCode := 100746, rule := .member 195200062172 },
  { wordCode := 100750, rule := .member 199495029468 },
  { wordCode := 100762, rule := .member 254065887113 },
  { wordCode := 100764, rule := .member 125541061340 },
  { wordCode := 100768, rule := .member 129836028636 },
  { wordCode := 100788, rule := .member 238647392374 },
  { wordCode := 100804, rule := .member 198487347933 },
  { wordCode := 100816, rule := .member 255073568648 },
  { wordCode := 100852, rule := .member 116492715913 },
  { wordCode := 100860, rule := .member 171270092918 },
  { wordCode := 100866, rule := .member 234900647203 },
  { wordCode := 100980, rule := .member 109770478300 },
  { wordCode := 100992, rule := .member 165107428643 },
  { wordCode := 101034, rule := .member 127956980444 },
  { wordCode := 101038, rule := .member 132251947740 },
  { wordCode := 101058, rule := .member 237842086006 },
  { wordCode := 101092, rule := .member 129298109149 },
  { wordCode := 101230, rule := .member 118372812680 }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk019 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 101350, rule := .member 247801277731 },
  { wordCode := 101398, rule := .member 164515582684 },
  { wordCode := 101410, rule := .member 236637505416 },
  { wordCode := 101428, rule := .member 171005036424 },
  { wordCode := 101454, rule := .member 168297379958 },
  { wordCode := 101458, rule := .member 246727535907 },
  { wordCode := 101476, rule := .member 195187928354 },
  { wordCode := 101494, rule := .member 125528927522 },
  { wordCode := 101502, rule := .member 196593619676 },
  { wordCode := 101506, rule := .member 200888586972 },
  { wordCode := 101554, rule := .member 118391687048 },
  { wordCode := 101608, rule := .member 119731767176 },
  { wordCode := 101616, rule := .member 168028944502 },
  { wordCode := 101628, rule := .member 127538598620 },
  { wordCode := 101652, rule := .member 236681312374 },
  { wordCode := 101704, rule := .member 233839039196 },
  { wordCode := 101710, rule := .member 109758344483 },
  { wordCode := 101722, rule := .member 165119562460 },
  { wordCode := 101734, rule := .member 254018701192 },
  { wordCode := 101740, rule := .member 129818202845 },
  { wordCode := 101764, rule := .member 127944846626 },
  { wordCode := 101772, rule := .member 194177700572 },
  { wordCode := 101776, rule := .member 198472667868 },
  { wordCode := 101788, rule := .member 237845464968 },
  { wordCode := 101830, rule := .member 201423360733 },
  { wordCode := 102070, rule := .member 197083753762 },
  { wordCode := 102088, rule := .member 111184407843 },
  { wordCode := 102100, rule := .member 163693499100 },
  { wordCode := 102112, rule := .member 237459589000 },
  { wordCode := 102142, rule := .member 108164508963 },
  { wordCode := 102150, rule := .member 196778169052 },
  { wordCode := 102166, rule := .member 255646091144 },
  { wordCode := 102244, rule := .member 234359132892 },
  { wordCode := 102268, rule := .member 246475877667 },
  { wordCode := 102276, rule := .member 126984950492 },
  { wordCode := 102316, rule := .member 201340523228 },
  { wordCode := 102330, rule := .member 111146210012 },
  { wordCode := 102384, rule := .member 108126311132 },
  { wordCode := 102396, rule := .member 166751595811 },
  { wordCode := 102486, rule := .member 234397330723 },
  { wordCode := 102532, rule := .member 199193039580 },
  { wordCode := 102564, rule := .member 247779857116 },
  { wordCode := 102568, rule := .member 234896003804 },
  { wordCode := 102600, rule := .member 110340903644 },
  { wordCode := 102604, rule := .member 131815740124 },
  { wordCode := 102612, rule := .member 164537003299 },
  { wordCode := 102624, rule := .member 236664535158 },
  { wordCode := 102634, rule := .member 116727596937 },
  { wordCode := 102642, rule := .member 171035211894 },
  { wordCode := 102672, rule := .member 246706115292 },
  { wordCode := 102676, rule := .member 233822261980 },
  { wordCode := 102682, rule := .member 109775121699 },
  { wordCode := 102694, rule := .member 165102785244 },
  { wordCode := 102706, rule := .member 254035478408 },
  { wordCode := 102708, rule := .member 125507506908 },
  { wordCode := 102712, rule := .member 129802474204 },
  { wordCode := 102732, rule := .member 238680946806 },
  { wordCode := 102736, rule := .member 127961623842 },
  { wordCode := 102748, rule := .member 198455890652 },
  { wordCode := 102760, rule := .member 237862242184 },
  { wordCode := 102778, rule := .member 169142765448 },
  { wordCode := 113752, rule := .member 111192272163 },
  { wordCode := 113764, rule := .member 163685634780 },
  { wordCode := 113800, rule := .member 232339051228 },
  { wordCode := 113806, rule := .member 108171324707 },
  { wordCode := 113814, rule := .member 196770304732 },
  { wordCode := 113818, rule := .member 166705533660 },
  { wordCode := 113830, rule := .member 255638226825 },
  { wordCode := 113832, rule := .member 110872007388 },
  { wordCode := 113836, rule := .member 132345795292 },
  { wordCode := 113844, rule := .member 164005899555 },
  { wordCode := 113856, rule := .member 238283012214 },
  { wordCode := 113878, rule := .member 245476060451 },
  { wordCode := 113904, rule := .member 247237219036 },
  { wordCode := 113908, rule := .member 234351268572 },
  { wordCode := 113932, rule := .member 246483741987 },
  { wordCode := 113980, rule := .member 166975017692 },
  { wordCode := 114178, rule := .member 233547010780 },
  { wordCode := 114244, rule := .member 119742777225 },
  { wordCode := 114264, rule := .member 127513957084 },
  { wordCode := 114424, rule := .member 255034247049 },
  { wordCode := 114724, rule := .member 111141940515 },
  { wordCode := 114736, rule := .member 163735966428 },
  { wordCode := 114778, rule := .member 108122041635 },
  { wordCode := 114786, rule := .member 196820636380 },
  { wordCode := 114790, rule := .member 166755865308 },
  { wordCode := 114802, rule := .member 255655004041 },
  { wordCode := 114804, rule := .member 128101159644 },
  { wordCode := 114828, rule := .member 238266234998 },
  { wordCode := 114880, rule := .member 234401600220 },
  { wordCode := 115474, rule := .member 233177912028 },
  { wordCode := 115744, rule := .member 232372605660 },
  { wordCode := 115750, rule := .member 108137770275 },
  { wordCode := 115762, rule := .member 166740136668 },
  { wordCode := 115776, rule := .member 110905561820 },
  { wordCode := 115788, rule := .member 163972345123 },
  { wordCode := 115822, rule := .member 245442506019 },
  { wordCode := 115966, rule := .member 127554252066 },
  { wordCode := 115990, rule := .member 236633835400 },
  { wordCode := 116026, rule := .member 119461758856 },
  { wordCode := 116056, rule := .member 195199986978 },
  { wordCode := 116074, rule := .member 125539937570 },
  { wordCode := 116086, rule := .member 200876528349 },
  { wordCode := 116098, rule := .member 238646052744 },
  { wordCode := 116110, rule := .member 194192305442 },
  { wordCode := 116134, rule := .member 118388017032 },
  { wordCode := 116212, rule := .member 131821507293 },
  { wordCode := 116302, rule := .member 199467242205 },
  { wordCode := 116926, rule := .member 168030750600 },
  { wordCode := 117046, rule := .member 125523160354 },
  { wordCode := 117070, rule := .member 238696384392 },
  { wordCode := 117082, rule := .member 194175528226 },
  { wordCode := 117196, rule := .member 168836056968 },
  { wordCode := 117664, rule := .member 237472696200 },
  { wordCode := 117910, rule := .member 127520697634 },
  { wordCode := 117934, rule := .member 236667389832 },
  { wordCode := 118018, rule := .member 125507431714 },
  { wordCode := 118030, rule := .member 200910082781 },
  { wordCode := 118042, rule := .member 238680655752 },
  { wordCode := 265776, rule := .chromograms #[2212, 2212, 118, 25, 76, 652, 118, 25, 76, 118, 25, 76, 25, 76, 652, 118, 25, 76, 118, 25, 76, 25, 76, 118, 25, 76, 25, 76, 652, 118, 25, 76, 118, 25, 76, 25, 76, 118, 25, 76, 25, 76] },
  { wordCode := 268, rule := .chromograms #[90, 102] },
  { wordCode := 265460, rule := .chromograms #[982, 424, 145, 109, 2716, 424, 145, 109, 4744, 145, 109, 424, 109, 145, 424, 145, 109, 982, 145, 109, 424, 109, 145, 145, 109, 424, 109, 145, 424, 145, 109, 982, 145, 109, 424, 109, 145, 145, 109, 424, 109, 145] },
  { wordCode := 266454, rule := .chromograms #[1240, 100, 292, 196, 4336, 100, 292, 196, 472, 22, 100, 100, 196, 292, 100, 292, 196, 472, 22, 100, 100, 196, 292, 22, 100, 100, 196, 292, 100, 292, 196, 472, 22, 100, 100, 196, 292, 22, 100, 100, 196, 292] },
  { wordCode := 266514, rule := .chromograms #[1276, 136, 2278, 2212, 2278, 136, 4378, 4354, 4378, 118, 118, 130, 262, 262, 136, 1258, 1258, 1270, 118, 118, 130, 262, 262, 118, 118, 130, 262, 262, 136, 1258, 1258, 1270, 118, 118, 130, 262, 262, 118, 118, 130, 262, 262] },
  { wordCode := 992, rule := .chromograms #[360, 228] },
  { wordCode := 1022, rule := .chromograms #[384, 246, 252, 246, 252] },
  { wordCode := 1150, rule := .chromograms #[294, 324, 396, 288, 294] },
  { wordCode := 266640, rule := .chromograms #[4390, 2296, 2296, 2398, 340, 484, 484, 4432, 340, 49, 49, 79, 202, 202, 484, 484, 1180, 340, 49, 49, 79, 202, 202, 49, 49, 79, 202, 202, 484, 484, 1180, 340, 49, 49, 79, 202, 202, 49, 49, 79, 202, 202] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk020 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 1244, rule := .chromograms #[258, 372] },
  { wordCode := 1268, rule := .chromograms #[384, 270, 264, 378, 378] },
  { wordCode := 1310, rule := .chromograms #[288, 330, 396, 432, 396] },
  { wordCode := 1442, rule := .chromograms #[408, 306, 306, 414, 408] },
  { wordCode := 268028, rule := .chromograms #[16, 190, 190, 190, 184, 190, 556, 454, 904, 898, 904, 454, 904, 898, 904, 904, 454, 454, 898, 904, 58, 58, 16, 10, 16, 190, 190, 184, 190, 190, 184, 190, 184, 190, 454, 550, 550, 556, 616, 454, 454, 4360, 4360, 6952, 454, 454, 4360, 4360, 58, 58, 16, 10, 16, 190, 190, 184, 190, 190, 184, 190, 184, 190, 454, 550, 550, 556, 616, 454, 454, 898, 904, 904, 454, 454, 898, 904, 454, 550, 550, 58, 616, 454, 58, 10, 16, 190, 184, 190, 184, 190, 58, 58, 16, 10, 16, 190, 190, 184, 190, 190, 184, 190, 184, 190, 454, 550, 550, 556, 616, 454, 454, 898, 904, 904, 454, 454, 898, 904, 454, 550, 550, 58, 616, 454, 58, 10, 16, 190, 184, 190, 184, 190] },
  { wordCode := 268004, rule := .chromograms #[1000, 910, 910, 460, 910, 28, 256, 460, 7198, 634, 460, 6958, 460, 6958, 28, 256, 460, 1000, 634, 460, 910, 460, 910, 634, 460, 28, 460, 256, 28, 256, 460, 1000, 634, 460, 910, 460, 910, 634, 460, 28, 460, 256] },
  { wordCode := 268056, rule := .chromograms #[4126, 334, 604, 496, 334, 604, 496, 160, 334, 334, 604, 496, 160, 334] },
  { wordCode := 268988, rule := .chromograms #[10, 10, 88, 892, 898, 898, 994, 616, 892, 898, 898, 616, 988, 994, 994, 622, 616, 616, 994, 988, 4, 4, 4, 10, 10, 4, 4, 10, 10, 94, 88, 88, 4636, 4648, 454, 454, 454, 7192, 454, 454, 616, 4360, 4372, 622, 616, 616, 4636, 4648, 4, 4, 4, 10, 10, 4, 4, 10, 10, 94, 88, 88, 898, 892, 454, 454, 454, 994, 454, 454, 616, 898, 892, 622, 616, 616, 994, 988, 454, 454, 454, 4, 454, 454, 4, 10, 4, 94, 88, 4, 10, 4, 4, 4, 4, 10, 10, 4, 4, 10, 10, 94, 88, 88, 898, 892, 454, 454, 454, 994, 454, 454, 616, 898, 892, 622, 616, 616, 994, 988, 454, 454, 454, 4, 454, 454, 4, 10, 4, 94, 88, 4, 10, 4] },
  { wordCode := 3914, rule := .chromograms #[714, 714, 720, 828, 828] },
  { wordCode := 267044, rule := .chromograms #[259, 826, 1036, 1036, 1036, 826, 259, 259, 259, 832, 826, 826, 7390, 7390, 826, 259, 259, 259, 832, 826, 826, 1036, 1036, 832, 826, 826, 259, 259, 826, 259, 259, 259, 832, 826, 826, 1036, 1036, 832, 826, 826, 259, 259] },
  { wordCode := 272294, rule := .chromograms #[16, 16, 94, 94, 88, 94, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 1534, 904, 1126, 1120, 1126, 904, 1516, 1510, 1516, 892, 898, 904, 2188, 2188, 904, 988, 994, 2188, 892, 898, 904, 2188, 2188, 892, 898, 904, 2188, 2188, 4, 4, 4, 10, 16, 4, 4, 10, 16, 94, 88, 94, 88, 94, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 904, 988, 994, 1534, 892, 898, 904, 1120, 1126, 892, 898, 904, 1510, 1516, 4, 4, 4, 10, 16, 4, 4, 10, 16, 94, 88, 94, 88, 94, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 904, 988, 994, 1534, 892, 898, 904, 1120, 1126, 892, 898, 904, 1510, 1516] },
  { wordCode := 272304, rule := .chromograms #[112, 472, 472, 472, 472, 1150, 8878, 2230, 8002, 8560, 2230, 2584, 2230, 8560, 478, 658, 112, 100, 472, 472, 472, 472, 472, 1084, 1084, 1132, 1480, 1522, 478, 658, 112, 100, 472, 472, 472, 472, 472, 1084, 1084, 1132, 1480, 1522] },
  { wordCode := 272358, rule := .chromograms #[658, 478, 478, 472, 478, 2230, 2230, 2230, 1432, 2230, 2230, 2230, 2230, 2230, 64, 64, 112, 658, 478, 472, 478, 472, 478, 1132, 1084, 1084, 1480, 1432, 64, 64, 112, 658, 478, 472, 478, 472, 478, 1132, 1084, 1084, 1480, 1432] },
  { wordCode := 272238, rule := .chromograms #[154, 490, 490, 484, 490, 1180, 8908, 2296, 8044, 8608, 2296, 2668, 2296, 8608, 484, 676, 154, 148, 490, 484, 490, 484, 490, 1198, 1174, 1174, 1552, 1552, 484, 676, 154, 148, 490, 484, 490, 484, 490, 1198, 1174, 1174, 1552, 1552] },
  { wordCode := 272214, rule := .chromograms #[496, 8062, 2680, 8614, 160, 496, 496, 1192, 1564, 160, 496, 496, 1192, 1564] },
  { wordCode := 272088, rule := .chromograms #[520, 8992, 8668, 8668, 736, 520, 520, 1390, 1612, 736, 520, 520, 1390, 1612] },
  { wordCode := 273254, rule := .chromograms #[10, 184, 184, 1228, 454, 1228, 550, 616, 616, 454, 616, 616, 550, 550, 550, 616, 616, 616, 616, 616, 898, 898, 1120, 1120, 1120, 994, 1120, 1120, 1120, 1228, 994, 994, 1228, 1228, 904, 904, 898, 898, 904, 898, 898, 2188, 2206, 2566, 994, 994, 2566, 2536, 58, 58, 16, 10, 10, 190, 190, 184, 184, 190, 184, 184, 454, 1228, 454, 550, 550, 550, 616, 454, 616, 454, 616, 616, 616, 616, 550, 550, 904, 904, 898, 898, 904, 898, 898, 1120, 1120, 1228, 994, 994, 1120, 1120, 58, 58, 16, 10, 10, 190, 190, 184, 184, 190, 184, 184, 454, 1228, 454, 550, 550, 550, 616, 454, 616, 454, 616, 616, 616, 616, 550, 550, 904, 904, 898, 898, 904, 898, 898, 1120, 1120, 1228, 994, 994, 1120, 1120] },
  { wordCode := 273266, rule := .chromograms #[16, 190, 190, 454, 454, 454, 556, 454, 454, 454, 454, 622, 556, 550, 556, 622, 616, 622, 616, 622, 904, 904, 1126, 1120, 1126, 1144, 1126, 1120, 1126, 988, 994, 1234, 1228, 1234, 898, 892, 898, 904, 892, 898, 904, 2188, 2188, 988, 994, 8734, 2566, 2578, 232, 4, 4, 10, 16, 184, 184, 184, 190, 184, 184, 190, 454, 454, 622, 556, 550, 556, 454, 454, 454, 454, 454, 622, 616, 622, 550, 556, 898, 892, 898, 904, 892, 898, 904, 1120, 1126, 988, 994, 1144, 1120, 1126, 232, 4, 4, 10, 16, 184, 184, 184, 190, 184, 184, 190, 454, 454, 622, 556, 550, 556, 454, 454, 454, 454, 454, 622, 616, 622, 550, 556, 898, 892, 898, 904, 892, 898, 904, 1120, 1126, 988, 994, 1144, 1120, 1126] },
  { wordCode := 273242, rule := .chromograms #[460, 460, 634, 634, 634, 1138, 1138, 1000, 2572, 910, 910, 2194, 1000, 2572, 28, 256, 460, 460, 634, 460, 460, 634, 634, 910, 910, 1138, 1000, 1138, 28, 256, 460, 460, 634, 460, 460, 634, 634, 910, 910, 1138, 1000, 1138] },
  { wordCode := 273276, rule := .chromograms #[472, 472, 568, 646, 628, 1150, 1150, 1252, 1240, 2230, 2230, 2584, 2584, 2530, 478, 478, 472, 472, 478, 472, 472, 562, 562, 1132, 1084, 1132, 1084, 1132, 478, 478, 472, 472, 478, 472, 472, 562, 562, 1132, 1084, 1132, 1084, 1132] },
  { wordCode := 273198, rule := .chromograms #[1288, 682, 586, 682, 682, 1174, 1174, 1288, 1288, 8764, 8920, 2668, 2548, 2548, 79, 202, 202, 490, 586, 682, 490, 592, 586, 1180, 1180, 1174, 1180, 1174, 79, 202, 202, 490, 586, 682, 490, 592, 586, 1180, 1180, 1174, 1180, 1174] },
  { wordCode := 273194, rule := .chromograms #[1300, 694, 598, 694, 694, 1186, 1186, 1300, 1300, 916, 916, 2314, 8776, 2674, 73, 208, 208, 1300, 598, 694, 694, 694, 598, 916, 916, 1186, 1300, 1186, 73, 208, 208, 1300, 598, 694, 694, 694, 598, 916, 916, 1186, 1300, 1186] },
  { wordCode := 273186, rule := .chromograms #[700, 1306, 2680, 2554, 496, 496, 604, 1192, 1192, 496, 496, 604, 1192, 1192] },
  { wordCode := 273150, rule := .chromograms #[712, 1324, 8962, 2560, 226, 712, 610, 1216, 1216, 226, 712, 610, 1216, 1216] },
  { wordCode := 272834, rule := .chromograms #[382, 754, 730, 754, 754, 1360, 1360, 1378, 1384, 976, 976, 9034, 2710, 2710, 424, 376, 376, 382, 730, 754, 754, 754, 730, 976, 976, 1360, 1378, 1360, 424, 376, 376, 382, 730, 754, 754, 754, 730, 976, 976, 1360, 1378, 1360] },
  { wordCode := 271578, rule := .chromograms #[211, 772, 772, 760, 772, 1738, 1714, 1708, 1714, 2746, 2746, 2746, 2746, 2746, 760, 205, 205, 211, 772, 760, 772, 760, 772, 1720, 1744, 1738, 1708, 1714, 760, 205, 205, 211, 772, 760, 772, 760, 772, 1720, 1744, 1738, 1708, 1714] },
  { wordCode := 271566, rule := .chromograms #[784, 1732, 9070, 2770, 217, 784, 784, 1750, 1732, 217, 784, 784, 1750, 1732] },
  { wordCode := 271620, rule := .chromograms #[796, 1750, 2770, 2770, 1750, 796, 784, 1684, 1732, 1750, 796, 784, 1684, 1732] },
  { wordCode := 271452, rule := .chromograms #[814, 1780, 9106, 2800, 181, 814, 808, 1774, 1774, 181, 814, 808, 1774, 1774] },
  { wordCode := 271322, rule := .chromograms #[271, 832, 832, 826, 832, 1042, 1840, 1834, 1840, 1036, 1036, 1042, 2878, 2884, 826, 259, 259, 271, 832, 826, 832, 826, 832, 1036, 1036, 1042, 1834, 1840, 826, 259, 259, 271, 832, 826, 832, 826, 832, 1036, 1036, 1042, 1834, 1840] },
  { wordCode := 271332, rule := .chromograms #[844, 1852, 2902, 2902, 1852, 844, 838, 1810, 1846, 1852, 844, 838, 1810, 1846] },
  { wordCode := 271374, rule := .chromograms #[856, 1822, 2908, 2968, 850, 850, 856, 1816, 1816, 850, 850, 856, 1816, 1816] },
  { wordCode := 271350, rule := .chromograms #[2992, 862, 1828, 862, 1828] },
  { wordCode := 271254, rule := .chromograms #[868, 1870, 9178, 3010, 313, 868, 868, 1876, 1870, 313, 868, 868, 1876, 1870] },
  { wordCode := 271206, rule := .chromograms #[9214, 886, 1906, 886, 1906] },
  { wordCode := 274480, rule := .chromograms #[2260, 2632, 2632, 2614, 2602, 232, 2632, 2260, 2242, 2224, 4, 2632, 2614, 2602, 4, 4522, 4522, 4, 10, 4, 2632, 2260, 2242, 2224, 892, 2632, 2614, 2602, 988, 3040, 3040, 1060, 1072, 1060, 3040, 3040, 3040, 1060, 3040, 3040, 1060, 1072, 1060, 1234, 1228, 1060, 1072, 1060, 11512, 11152, 11134, 11152, 892, 11512, 11488, 11512, 988, 11488, 11512, 232, 238, 232, 11164, 11488, 11512, 4, 11134, 11152, 4, 10, 4, 94, 88, 4, 10, 4, 904, 988, 994, 994, 892, 898, 898, 898, 892, 988, 994, 994, 994, 988, 2626, 2254, 2236, 2254, 892, 2506, 2506, 2626, 988, 2608, 2566, 232, 238, 232, 2188, 2188, 2188, 4, 2188, 2188, 4, 10, 4, 94, 88, 4, 10, 4, 904, 988, 994, 994, 892, 898, 898, 898, 892, 988, 994, 994, 994, 988] },
  { wordCode := 274588, rule := .chromograms #[6892, 3184, 2632, 2590, 2578, 2590, 2260, 2260, 2206, 2200, 2206, 2632, 2590, 2578, 2536, 4528, 4522, 4, 34, 34, 2260, 2260, 2206, 2200, 2206, 2632, 2590, 2578, 2536, 3118, 3040, 1060, 1120, 1120, 3040, 3118, 3118, 1462, 3118, 3040, 1060, 1120, 1120, 1228, 1228, 1060, 1120, 1120, 11152, 11152, 12724, 12712, 4, 11512, 12724, 12712, 232, 12724, 11512, 232, 280, 280, 11164, 11164, 11152, 232, 11164, 11152, 4, 34, 34, 88, 88, 4, 34, 34, 904, 904, 898, 898, 904, 898, 898, 1120, 1120, 1228, 994, 994, 1120, 1120, 2254, 2254, 2566, 2188, 4, 2506, 2536, 2566, 232, 2566, 2566, 232, 280, 280, 2188, 2266, 2254, 232, 2266, 2188, 4, 34, 34, 88, 88, 4, 34, 34, 904, 904, 898, 898, 904, 898, 898, 1120, 1120, 1228, 994, 994, 1120, 1120] },
  { wordCode := 256712, rule := .chromograms #[1765, 1285, 1249, 6604, 1285, 1249, 1765, 1249, 1285, 1285, 1249, 1765, 1249, 1285] },
  { wordCode := 9230, rule := .chromograms #[1260, 1290, 1320, 1392, 1278, 1260, 1260, 1296, 1290, 1278, 1260, 1260, 1296, 1290] },
  { wordCode := 275202, rule := .chromograms #[100, 100, 292, 196, 4336, 1240, 1522, 1432, 8002, 1084, 1240, 1240, 1432, 1522, 196, 22, 100, 100, 22, 100, 100, 196, 292, 1084, 1240, 1240, 1432, 1522, 196, 22, 100, 100, 22, 100, 100, 196, 292, 1084, 1240, 1240, 1432, 1522] },
  { wordCode := 275278, rule := .chromograms #[3316, 3316, 3886, 2344, 2344, 2344, 4588, 11254, 2344, 2344, 2344, 2200, 2224, 2224, 2224, 2206, 2200, 2200, 184, 190, 3298, 3298, 2344, 2344, 2344, 2200, 2224, 2224, 2224, 2206, 2200, 2200, 898, 904, 3064, 3118, 3118, 1144, 3184, 3298, 3298, 1420, 1426, 1474, 1468, 1474, 1420, 1426, 11164, 11254, 11254, 11248, 11248, 11254, 11164, 11152, 58, 11254, 11248, 640, 898, 904, 11254, 11164, 11152, 58, 11254, 11248, 11248, 184, 190, 244, 238, 244, 184, 190, 946, 904, 898, 904, 946, 940, 946, 940, 946, 946, 940, 946, 898, 904, 2266, 2374, 2350, 2368, 2374, 2374, 2266, 2254, 58, 2350, 2368, 640, 898, 904, 2374, 2266, 2254, 58, 2350, 2368, 2374, 184, 190, 244, 238, 244, 184, 190, 946, 904, 898, 904, 946, 940, 946, 940, 946, 946, 940, 946, 898, 904] },
  { wordCode := 275274, rule := .chromograms #[658, 2356, 2230, 2230, 196, 2356, 2230, 2230, 1432, 1150, 1252, 1432, 1480, 1432, 112, 64, 112, 658, 64, 112, 196, 250, 196, 1150, 1252, 1432, 1480, 1432, 112, 64, 112, 658, 64, 112, 196, 250, 196, 1150, 1252, 1432, 1480, 1432] },
  { wordCode := 275290, rule := .chromograms #[3202, 2260, 3400, 2362, 2344, 892, 2260, 11248, 2362, 2344, 2362, 2206, 2242, 2224, 232, 2200, 2200, 2206, 184, 184, 2260, 3304, 2362, 2344, 2362, 2206, 2242, 2224, 892, 2200, 2200, 892, 898, 892, 3304, 3304, 3118, 1462, 3202, 3298, 3304, 1420, 1420, 1462, 1468, 1468, 1420, 1420, 11152, 11248, 11248, 11248, 11254, 11134, 11134, 11152, 892, 11248, 11248, 892, 898, 892, 11134, 11134, 11152, 232, 11248, 11248, 11254, 184, 184, 232, 238, 238, 184, 184, 892, 892, 898, 898, 940, 940, 940, 940, 940, 940, 940, 892, 898, 892, 2254, 2368, 2368, 2368, 2368, 2236, 2236, 2254, 892, 2368, 2368, 892, 898, 892, 2236, 2236, 2254, 232, 2368, 2368, 2368, 184, 184, 232, 238, 238, 184, 184, 892, 892, 898, 898, 940, 940, 940, 940, 940, 940, 940, 892, 898, 892] },
  { wordCode := 275262, rule := .chromograms #[136, 136, 2278, 2212, 2278, 1276, 2278, 2212, 2278, 1258, 1258, 1270, 1492, 1492, 118, 118, 118, 130, 118, 118, 130, 262, 262, 1258, 1258, 1270, 1492, 1492, 118, 118, 118, 130, 118, 118, 130, 262, 262, 1258, 1258, 1270, 1492, 1492] },
  { wordCode := 275452, rule := .chromograms #[2260, 2260, 2260, 2242, 2224, 4, 2260, 2260, 2242, 2224, 4, 2260, 2242, 2224, 232, 2362, 2344, 232, 238, 232, 2260, 2260, 2242, 2224, 892, 2260, 2242, 2224, 892, 2362, 2344, 1462, 940, 940, 3382, 3304, 3118, 1462, 3040, 3040, 1060, 1072, 1060, 1420, 1420, 1420, 1420, 1420, 11152, 11152, 11134, 11152, 892, 11152, 11134, 11152, 892, 11134, 11152, 4, 10, 4, 11152, 11134, 11152, 232, 11134, 11152, 4, 10, 4, 184, 184, 184, 184, 184, 898, 892, 898, 898, 892, 898, 898, 898, 892, 892, 898, 898, 898, 892, 2254, 2254, 2236, 2254, 892, 2254, 2236, 2254, 892, 2188, 2188, 4, 10, 4, 2254, 2236, 2254, 232, 2188, 2188, 4, 10, 4, 184, 184, 184, 184, 184, 898, 892, 898, 898, 892, 898, 898, 898, 892, 892, 898, 898, 898, 892] },
  { wordCode := 9740, rule := .chromograms #[1788, 1584, 1458, 1584, 1458] },
  { wordCode := 275470, rule := .chromograms #[2242, 2242, 2206, 2242, 2260, 10, 2242, 2206, 2242, 2260, 10, 2206, 2242, 2260, 184, 2362, 11134, 238, 232, 232, 2242, 2206, 2242, 2260, 898, 2206, 2242, 2260, 898, 2362, 3400, 940, 1462, 940, 3304, 3304, 3184, 1120, 3040, 3064, 1072, 1060, 1060, 1420, 3400, 1468, 1462, 1420, 11134, 11134, 11134, 11134, 34, 11134, 11134, 11134, 34, 11134, 11134, 10, 4, 4, 11134, 11134, 11134, 34, 11134, 11134, 10, 4, 4, 184, 11488, 238, 232, 184, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 2236, 2236, 2236, 2236, 34, 2236, 2236, 2236, 34, 2188, 2236, 10, 4, 4, 2236, 2236, 2236, 34, 2188, 2236, 10, 4, 4, 184, 2236, 238, 232, 184, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892, 892] },
  { wordCode := 9770, rule := .chromograms #[1716, 1818, 1476, 1482, 1608, 1476, 1482, 1476, 1482, 1608, 1476, 1482, 1476, 1482] },
  { wordCode := 9898, rule := .chromograms #[1620, 1524, 1554, 1872, 1524, 1554, 1620, 1518, 1524, 1524, 1554, 1620, 1518, 1524] },
  { wordCode := 275344, rule := .chromograms #[2326, 2326, 2326, 2416, 358, 2326, 2326, 2416, 1582, 3514, 3172, 1222, 1450, 1450, 11224, 11224, 11224, 67, 11224, 11224, 67, 214, 214, 922, 922, 922, 922, 922, 2320, 2320, 2320, 67, 2320, 2320, 67, 214, 214, 922, 922, 922, 922, 922] },
  { wordCode := 10016, rule := .chromograms #[1500, 1608, 1716, 1722, 1608, 1500, 1494, 1602, 1602, 1608, 1500, 1494, 1602, 1602] },
  { wordCode := 275032, rule := .chromograms #[2434, 2434, 2434, 11344, 400, 2434, 2434, 3550, 1624, 3550, 3226, 1336, 3550, 1624, 11344, 11344, 11344, 103, 11344, 11344, 103, 11608, 400, 970, 970, 970, 970, 970, 2440, 2440, 2440, 103, 2440, 2440, 103, 2440, 400, 970, 970, 970, 970, 970] },
  { wordCode := 10058, rule := .chromograms #[1758, 1740, 1740, 1620, 1518, 1560, 1620, 1650, 1620, 1518, 1560, 1620, 1650, 1620] },
  { wordCode := 275020, rule := .chromograms #[2452, 2452, 2452, 2464, 424, 2452, 2452, 2464, 982, 3538, 3574, 1642, 1600, 1600, 11350, 11350, 11350, 982, 11350, 11350, 424, 376, 376, 976, 976, 976, 976, 976, 2446, 2446, 2446, 982, 2446, 2446, 424, 376, 376, 976, 976, 976, 976, 976] },
  { wordCode := 257706, rule := .chromograms #[1339, 1879, 1693, 6058, 1105, 1339, 1339, 1693, 1879, 1105, 1339, 1339, 1693, 1879] },
  { wordCode := 257766, rule := .chromograms #[1411, 6130, 6076, 6130, 1351, 1351, 1399, 1795, 1795, 1351, 1351, 1399, 1795, 1795] },
  { wordCode := 273984, rule := .chromograms #[2776, 2776, 445, 391, 367, 2776, 1756, 1720, 1708, 1756, 1720, 1666, 1720, 1708, 391, 1756, 1720, 205, 445, 391, 205, 391, 367, 1756, 1720, 1666, 1720, 1708, 391, 1756, 1720, 205, 445, 391, 205, 391, 367, 1756, 1720, 1666, 1720, 1708] },
  { wordCode := 10516, rule := .chromograms #[1494, 1602, 1602, 1602, 1722, 1800, 1800, 1716, 1722, 1608, 1500, 1494, 1602, 1602] },
  { wordCode := 10576, rule := .chromograms #[1542, 1632, 1632, 1626, 1782, 1896, 1890, 1764, 1776, 1626, 1536, 1536, 1632, 1626] },
  { wordCode := 273508, rule := .chromograms #[11818, 11818, 2938, 2926, 2938, 3724, 2938, 2926, 2938, 3724, 3718, 3724, 1798, 1798, 11818, 11818, 11818, 11824, 11818, 11818, 11824, 259, 259, 1036, 1036, 1036, 1036, 1036, 2878, 2944, 2944, 2944, 2884, 2878, 2878, 259, 259, 1036, 1036, 1036, 1036, 1036] },
  { wordCode := 10762, rule := .chromograms #[1482, 1482, 1494, 1818, 1722, 1722, 1716, 1806, 1818, 1608, 1476, 1482, 1476, 1482] },
  { wordCode := 10796, rule := .chromograms #[1758, 1872, 1518, 1524, 1746, 1758, 1758, 1842, 1872, 1524, 1554, 1620, 1518, 1524] },
  { wordCode := 273616, rule := .chromograms #[13168, 11818, 4918, 4906, 4918, 3724, 3802, 3796, 3802, 3718, 3718, 3724, 1834, 1834, 11818, 13174, 13168, 13174, 11824, 11818, 11824, 319, 319, 1042, 1036, 1036, 1834, 1834, 2878, 2878, 2878, 2878, 2878, 2878, 2878, 319, 319, 1042, 1036, 1036, 1834, 1834] },
  { wordCode := 10964, rule := .chromograms #[1092, 1914] },
  { wordCode := 10988, rule := .chromograms #[1098, 1098, 1104, 1920, 1920] },
  { wordCode := 11018, rule := .chromograms #[1170, 1950] },
  { wordCode := 11144, rule := .chromograms #[1158, 1152, 1152, 1938, 1944] },
  { wordCode := 11162, rule := .chromograms #[1152, 1152, 1158, 1938, 1938] },
  { wordCode := 11444, rule := .chromograms #[1236, 1236, 1242, 1962, 1962] },
  { wordCode := 261480, rule := .chromograms #[1033, 2041, 1939, 5080, 2041, 1033, 1033, 1939, 2041, 2041, 1033, 1033, 1939, 2041] },
  { wordCode := 11558, rule := .chromograms #[1284, 1266, 1266, 1980, 1986] },
  { wordCode := 11612, rule := .chromograms #[1266, 1266, 1284, 1980, 1980] },
  { wordCode := 11654, rule := .chromograms #[1260, 1260, 1260, 1404, 1260, 1260, 1314, 1296, 1296, 1974, 1974, 1974, 1974, 1974] },
  { wordCode := 11846, rule := .chromograms #[1434, 1662, 1998, 2034, 1998] },
  { wordCode := 11918, rule := .chromograms #[1788, 1704, 1704, 2064, 2118] },
  { wordCode := 11936, rule := .chromograms #[1488, 1710, 1710, 2070, 2010] },
  { wordCode := 11960, rule := .chromograms #[1716, 1818, 1500, 1494, 1728, 1716, 1722, 1716, 1722, 2082, 2076, 2076, 2016, 2136] },
  { wordCode := 12116, rule := .chromograms #[1566, 1536, 1536, 1854, 1764, 1764, 1764, 1764, 1764, 2106, 2106, 2028, 2022, 2022] },
  { wordCode := 12178, rule := .chromograms #[1596, 1794, 1794, 2010, 2070] },
  { wordCode := 12230, rule := .chromograms #[1716, 1716, 1716, 1722, 1716, 1716, 1722, 1800, 1800, 2076, 2076, 2076, 2076, 2076] },
  { wordCode := 12314, rule := .chromograms #[1734, 1734, 1830, 2088, 2088] },
  { wordCode := 12494, rule := .chromograms #[1434, 1434, 2034, 1998, 1998] },
  { wordCode := 12632, rule := .chromograms #[1428, 1428, 1428, 2058, 1428, 1428, 2046, 1452, 2058, 1992, 1992, 1992, 1992, 1992] },
  { wordCode := 12692, rule := .chromograms #[1710, 1488, 1464, 2010, 2070] },
  { wordCode := 12908, rule := .chromograms #[1488, 1488, 1596, 2010, 2010] },
  { wordCode := 13034, rule := .chromograms #[1566, 1536, 1566, 1578, 1536, 1566, 1578, 1626, 1638, 2022, 2028, 2028, 2028, 2022] },
  { wordCode := 13088, rule := .chromograms #[1536, 1536, 1536, 1854, 1536, 1536, 2178, 1632, 1638, 2022, 2022, 2022, 2022, 2022] },
  { wordCode := 285418, rule := .chromograms #[4618, 4348, 4348, 2248, 2194, 3130, 3460, 2248, 2194, 2620, 2248, 2194, 2248, 2194, 3130, 3460, 2248, 2194, 2620, 2248, 2194, 2248, 2194, 2620, 2248, 2194, 2248, 2194, 28, 28, 28, 52, 28, 28, 52, 256, 298, 1090, 1090, 1138, 1486, 1528] },
  { wordCode := 19886, rule := .chromograms #[2286, 2274, 2274, 2328, 2334] },
  { wordCode := 19898, rule := .chromograms #[2274, 2274, 2286, 2328, 2328] },
  { wordCode := 285304, rule := .chromograms #[4714, 4420, 2416, 2326, 220, 3502, 2416, 2326, 928, 2416, 2326, 928, 2326, 928, 3502, 2416, 2326, 2332, 2416, 2326, 2332, 2326, 2332, 2416, 2326, 2332, 2326, 2332, 67, 67, 61, 61, 67, 61, 61, 352, 220, 1222, 1210, 928, 1576, 928] },
  { wordCode := 246188, rule := .chromograms #[5017, 2761, 2275, 2473, 2761, 2275, 2473, 2275, 2473, 2761, 2275, 2473, 2275, 2473] },
  { wordCode := 286390, rule := .chromograms #[4348, 4348, 4618, 2620, 2572, 3130, 3130, 2620, 2572, 2248, 2248, 2194, 2620, 2572, 3130, 3130, 2620, 2572, 2248, 2248, 2194, 2620, 2572, 2248, 2248, 2194, 2620, 2572, 28, 256, 256, 298, 52, 28, 52, 28, 52, 1138, 1090, 1138, 1090, 1138] },
  { wordCode := 20846, rule := .chromograms #[2964, 2640, 2682, 2640, 2682] },
  { wordCode := 284458, rule := .chromograms #[3796, 2926, 4906, 4906, 4906, 2926, 3796, 3796, 3796, 2938, 2926, 2926, 2878, 2884, 2926, 3796, 3796, 3796, 2938, 2926, 2926, 2878, 2884, 2938, 2926, 2926, 2878, 2884, 259, 259, 259, 271, 259, 259, 271, 319, 331, 1798, 1798, 1804, 1834, 1840] },
  { wordCode := 284470, rule := .chromograms #[3802, 2938, 4918, 4906, 4918, 2938, 3802, 3796, 3802, 2926, 2926, 2938, 2878, 2878, 2938, 3802, 3796, 3802, 2926, 2926, 2938, 2878, 2878, 2926, 2926, 2938, 2878, 2878, 271, 271, 259, 259, 271, 259, 259, 319, 319, 1804, 1798, 1798, 1834, 1834] },
  { wordCode := 21818, rule := .chromograms #[2640, 2640, 2682, 2964, 3018] },
  { wordCode := 287660, rule := .chromograms #[460, 460, 634, 3076, 3130, 1138, 1138, 1090, 1138, 1138, 1090, 1138, 1090, 1138, 2194, 2572, 3076, 3130, 3418, 3076, 3130, 3076, 3130, 2248, 2248, 2194, 2620, 2572, 2194, 2572, 3076, 460, 3418, 3076, 460, 3076, 634, 1138, 1090, 1138, 1090, 1138] },
  { wordCode := 243920, rule := .chromograms #[5287, 5917, 3085, 3169, 3769, 3085, 3169, 3085, 3169, 3769, 3085, 3169, 3085, 3169] },
  { wordCode := 288632, rule := .chromograms #[634, 460, 460, 3418, 3460, 1138, 1528, 1486, 1528, 1090, 1090, 1138, 1486, 1528, 2194, 2194, 3418, 3460, 3076, 3076, 3130, 3418, 3460, 2620, 2248, 2194, 2248, 2194, 2194, 2194, 3418, 634, 3076, 3076, 460, 3418, 460, 1090, 1090, 1138, 1486, 1528] },
  { wordCode := 242960, rule := .chromograms #[3421, 5605, 5605, 5605, 3433, 3421, 3421, 3499, 3517, 3433, 3421, 3421, 3499, 3517] },
  { wordCode := 242972, rule := .chromograms #[3433, 5623, 5605, 5623, 3421, 3421, 3433, 3499, 3499, 3421, 3421, 3433, 3499, 3499] },
  { wordCode := 23114, rule := .chromograms #[3666, 3420, 3528, 3420, 3528] },
  { wordCode := 286700, rule := .chromograms #[2878, 3742, 826, 826, 826, 1798, 1834, 1834, 1834, 1804, 1798, 1798, 1834, 1834, 3742, 2878, 2878, 2878, 3748, 3742, 3742, 3796, 3802, 2926, 2926, 2938, 2878, 2878, 3742, 2878, 2878, 2878, 3748, 3742, 3742, 826, 826, 1804, 1798, 1798, 1834, 1834] },
  { wordCode := 286712, rule := .chromograms #[2884, 3748, 832, 826, 832, 1804, 1840, 1834, 1840, 1798, 1798, 1804, 1834, 1840, 3748, 2884, 2878, 2884, 3742, 3742, 3748, 3796, 3796, 2938, 2926, 2926, 2878, 2884, 3748, 2884, 2878, 2884, 3742, 3742, 3748, 826, 832, 1798, 1798, 1804, 1834, 1840] },
  { wordCode := 244892, rule := .chromograms #[5287, 5287, 3769, 3859, 3085, 3085, 3169, 3769, 3859, 3085, 3085, 3169, 3769, 3859] },
  { wordCode := 284230, rule := .chromograms #[7624, 9250, 9250, 2020, 7702, 7624, 7702, 7624, 7702, 487, 871, 1930, 1930, 1930] },
  { wordCode := 284146, rule := .chromograms #[7714, 7648, 7648, 7648, 7654, 9286, 9286, 9286, 2032, 9286, 9286, 2002, 9370, 2032, 7582, 7582, 7588, 7588, 7648, 7648, 7654, 7714, 7708, 7648, 7648, 7582, 7588, 7582, 475, 475, 859, 1954, 859, 793, 1954, 793, 1954, 1954, 1954, 1954, 1954, 1954] },
  { wordCode := 284122, rule := .chromograms #[7660, 9304, 9304, 9388, 7594, 7660, 7726, 7660, 7594, 853, 787, 787, 1960, 1960] },
  { wordCode := 282556, rule := .chromograms #[7768, 9634, 9676, 2050, 7780, 7768, 7780, 7768, 7780, 589, 589, 2086, 2086, 2050] },
  { wordCode := 282382, rule := .chromograms #[7798, 9652, 9718, 2056, 7792, 7792, 7792, 7792, 7792, 565, 565, 2116, 2116, 2056] },
  { wordCode := 282202, rule := .chromograms #[7822, 9808, 9808, 2182, 7828, 7822, 7828, 7822, 7828, 655, 667, 2170, 2170, 2170] },
  { wordCode := 282178, rule := .chromograms #[9820, 7834, 7834, 661, 2176] },
  { wordCode := 291954, rule := .chromograms #[4492, 3046, 3046, 3046, 3046, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3124, 4492, 4492, 4492, 3046, 3046, 3046, 3046, 3046, 4654, 4600, 4654, 4492, 4492, 3124, 124, 106, 124, 3046, 3046, 3046, 3046, 3046, 1, 1, 1, 1, 1] },
  { wordCode := 291948, rule := .chromograms #[136, 664, 664, 3088, 532, 25, 25, 25, 7, 25, 25, 7, 25, 7, 2212, 2212, 4504, 3424, 3088, 3088, 3082, 3088, 3082, 4006, 4660, 3874, 4504, 3874, 7, 7, 130, 130, 532, 3088, 664, 3088, 532, 25, 25, 7, 25, 7] },
  { wordCode := 292020, rule := .chromograms #[118, 652, 652, 3088, 574, 652, 118, 25, 76, 118, 25, 76, 25, 76, 2278, 2278, 4504, 3466, 3994, 3088, 3136, 3088, 3136, 3994, 4660, 3916, 4504, 3916, 76, 76, 130, 118, 574, 3088, 652, 3088, 574, 118, 25, 76, 25, 76] },
  { wordCode := 292010, rule := .chromograms #[2392, 3472, 580, 538, 580, 82, 82, 19, 82, 82, 19, 82, 19, 82, 3430, 2380, 2380, 2392, 3430, 3430, 3472, 4000, 4000, 4630, 4630, 4630, 4000, 4000, 3430, 2380, 2380, 2392, 3430, 3430, 3472, 538, 580, 82, 19, 82, 19, 82] },
  { wordCode := 291902, rule := .chromograms #[916, 916, 3160, 598, 3160, 73, 73, 43, 73, 73, 43, 73, 43, 73, 3148, 3478, 2404, 2404, 3160, 3148, 3160, 3148, 3160, 4408, 4396, 4396, 4036, 4690, 3148, 3478, 2404, 916, 3160, 3148, 916, 598, 3160, 73, 43, 73, 43, 73] },
  { wordCode := 292220, rule := .chromograms #[2374, 58, 58, 40, 34, 40, 640, 3322, 556, 550, 556, 622, 556, 550, 556, 622, 616, 622, 616, 622, 40, 94, 94, 88, 94, 58, 40, 34, 40, 94, 88, 94, 88, 94, 58, 40, 34, 40, 94, 88, 94, 88, 94, 94, 88, 58, 34, 40, 2236, 2506, 2368, 2368, 2374, 2254, 2236, 2254, 2266, 2188, 2188, 2188, 2188, 2188, 3310, 3106, 3100, 3106, 3310, 3310, 3286, 3982, 3286, 3040, 3040, 3892, 3100, 3106, 4522, 4372, 4360, 3886, 4522, 4522, 4522, 3982, 3982, 3886, 3892, 3892, 3892, 3886, 2236, 2506, 2368, 2368, 2374, 2254, 2236, 2254, 58, 2188, 2188, 58, 34, 40, 3310, 3106, 3100, 640, 3310, 3310, 3286, 550, 556, 622, 616, 622, 550, 556, 58, 40, 34, 40, 94, 88, 94, 88, 94, 94, 88, 58, 34, 40] },
  { wordCode := 292200, rule := .chromograms #[4600, 3196, 3196, 3196, 3196, 106, 106, 106, 106, 106, 106, 106, 1, 70, 3208, 4600, 4600, 4600, 3196, 3196, 3196, 3046, 3124, 4534, 4492, 4534, 4492, 4534, 3208, 70, 1, 70, 3196, 3196, 3196, 3046, 3124, 106, 106, 106, 1, 70] },
  { wordCode := 292308, rule := .chromograms #[4654, 3208, 3208, 3196, 3208, 124, 124, 106, 124, 124, 106, 124, 1, 1, 3196, 4654, 4600, 4654, 3208, 3196, 3208, 3046, 3046, 4492, 4492, 4492, 4492, 4492, 3196, 1, 1, 1, 3208, 3196, 3208, 3046, 3046, 124, 106, 124, 1, 1] },
  { wordCode := 292100, rule := .chromograms #[67, 3358, 706, 706, 706, 166, 67, 166, 166, 67, 166, 166, 166, 67, 3364, 2332, 2320, 2320, 3166, 3358, 3358, 3172, 3166, 4420, 4570, 4582, 3952, 3964, 3364, 2332, 2320, 67, 3166, 3358, 3358, 706, 706, 67, 166, 166, 166, 67] },
  { wordCode := 291746, rule := .chromograms #[742, 514, 742, 3232, 4066, 115, 115, 103, 115, 115, 103, 115, 103, 115, 2440, 2440, 3556, 4066, 3556, 3232, 4066, 3232, 4066, 4756, 4444, 4066, 4756, 4066, 2440, 2440, 3556, 742, 3556, 3232, 514, 3232, 742, 115, 103, 115, 103, 115] },
  { wordCode := 291698, rule := .chromograms #[157, 754, 730, 730, 730, 109, 109, 109, 109, 109, 109, 109, 109, 109, 2446, 2446, 2470, 2464, 3256, 3568, 4072, 4078, 3256, 4474, 4774, 4072, 4078, 4072, 2446, 2446, 2470, 157, 3256, 3568, 754, 730, 730, 109, 109, 109, 109, 109] },
  { wordCode := 291656, rule := .chromograms #[3268, 133, 133, 133, 3586, 3268, 3268, 4486, 4780, 3586, 3268, 3268, 133, 133] },
  { wordCode := 292964, rule := .chromograms #[4, 232, 988, 184, 184, 184, 892, 892, 892, 898, 898, 892, 892, 898, 898, 940, 940, 940, 940, 940, 34, 10, 4, 10, 10, 238, 184, 184, 184, 232, 238, 238, 238, 232, 16, 40, 34, 34, 4, 10, 10, 10, 4, 232, 238, 238, 184, 184, 2350, 3070, 2188, 2188, 2566, 3070, 3106, 2566, 2566, 2506, 3058, 3058, 3040, 2506, 3070, 3106, 3100, 3100, 3034, 3058, 3058, 3040, 3034, 3286, 3298, 3304, 3298, 3304, 4342, 4372, 4360, 4372, 4324, 4330, 4342, 4360, 4372, 4324, 4330, 4342, 4360, 4372, 2350, 3070, 2188, 2188, 4, 3070, 3106, 2566, 232, 2506, 3058, 988, 184, 184, 3070, 3106, 3100, 892, 3034, 3058, 892, 898, 892, 940, 940, 892, 898, 892, 16, 40, 34, 34, 4, 10, 10, 10, 4, 232, 238, 238, 184, 184] },
  { wordCode := 292976, rule := .chromograms #[1144, 1144, 466, 190, 184, 190, 640, 466, 904, 898, 904, 466, 904, 898, 904, 946, 940, 946, 940, 946, 40, 16, 16, 10, 16, 244, 190, 184, 190, 244, 238, 244, 238, 244, 10, 34, 34, 40, 16, 10, 16, 10, 16, 244, 238, 244, 184, 190, 2236, 2236, 2566, 2188, 2188, 2608, 2536, 2566, 3106, 2536, 3058, 3070, 3040, 3070, 3058, 3100, 3100, 3106, 3070, 3058, 3070, 3040, 3070, 3298, 3298, 3298, 3298, 3298, 4330, 4360, 4360, 3886, 4342, 4330, 3886, 4360, 4360, 4342, 4330, 4096, 4360, 4360, 2236, 2236, 2566, 2188, 1144, 2608, 2536, 2566, 1144, 2536, 3058, 466, 184, 190, 3058, 3100, 3100, 640, 3070, 3058, 466, 898, 904, 946, 940, 466, 898, 904, 10, 34, 34, 40, 16, 10, 16, 10, 16, 244, 238, 244, 184, 190] },
  { wordCode := 292908, rule := .chromograms #[1270, 3082, 3424, 3424, 3424, 7, 262, 262, 262, 76, 7, 7, 262, 262, 3136, 3136, 2518, 2518, 3136, 3082, 3082, 3424, 3424, 3916, 3874, 3874, 4354, 4378, 25, 1258, 1258, 1270, 652, 652, 664, 3424, 3424, 76, 7, 7, 262, 262] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk021 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 292896, rule := .chromograms #[3436, 274, 13, 274, 3094, 3094, 3436, 3880, 4384, 1282, 670, 3436, 13, 274] },
  { wordCode := 293030, rule := .chromograms #[58, 304, 466, 454, 454, 454, 466, 466, 454, 454, 454, 466, 454, 454, 454, 940, 940, 946, 3442, 3448, 16, 16, 40, 34, 40, 244, 286, 280, 286, 232, 238, 244, 280, 286, 10, 4, 10, 16, 4, 10, 16, 34, 40, 232, 238, 244, 280, 286, 2506, 2236, 2236, 2254, 2266, 2608, 2506, 2626, 3070, 2506, 3058, 3070, 3100, 3106, 3058, 3034, 3058, 3070, 3034, 3058, 3070, 3100, 3106, 3286, 3298, 3298, 3442, 3286, 4330, 4324, 4330, 4096, 4324, 4330, 3886, 3892, 3886, 4324, 4330, 4096, 4108, 4096, 2506, 2236, 2236, 2254, 58, 2608, 2506, 2626, 304, 2506, 3058, 466, 454, 454, 3058, 3034, 3058, 466, 3034, 3058, 466, 454, 454, 940, 940, 466, 454, 454, 10, 4, 10, 16, 4, 10, 16, 34, 40, 232, 238, 244, 280, 286] },
  { wordCode := 293006, rule := .chromograms #[460, 460, 460, 3418, 3460, 52, 298, 256, 298, 28, 28, 52, 256, 298, 2272, 2638, 3076, 3130, 3076, 3076, 3130, 3418, 3460, 4348, 4348, 3910, 4348, 4114, 2272, 2638, 3076, 460, 3076, 3076, 460, 3418, 460, 28, 28, 52, 256, 298] },
  { wordCode := 292998, rule := .chromograms #[3136, 3136, 3466, 3424, 3466, 76, 310, 262, 310, 7, 7, 76, 262, 310, 2644, 2518, 2518, 3136, 3082, 3082, 3136, 3424, 3466, 3874, 3874, 3916, 4354, 4354, 652, 1102, 1258, 1258, 664, 652, 652, 3424, 3466, 7, 7, 76, 262, 310] },
  { wordCode := 292874, rule := .chromograms #[208, 916, 916, 964, 964, 73, 208, 328, 346, 43, 43, 73, 328, 208, 3148, 3148, 3148, 3160, 3148, 3148, 3160, 3352, 3346, 4396, 4396, 4396, 4396, 4396, 3148, 3148, 3148, 208, 3148, 3148, 916, 964, 916, 43, 43, 73, 328, 208] },
  { wordCode := 292436, rule := .chromograms #[1360, 730, 3544, 976, 3544, 157, 382, 376, 382, 145, 145, 157, 376, 382, 2470, 3250, 3250, 3256, 3250, 3250, 3256, 3532, 3544, 4462, 4462, 4078, 4462, 4462, 2470, 3250, 3250, 1360, 3250, 3250, 730, 976, 3544, 145, 145, 157, 376, 382] },
  { wordCode := 292550, rule := .chromograms #[370, 3562, 3526, 3562, 3562, 418, 370, 418, 418, 97, 97, 418, 418, 370, 3238, 3238, 3238, 4456, 3238, 3238, 3562, 3562, 3526, 4450, 4450, 4450, 4450, 4450, 3238, 3238, 3238, 370, 3238, 3238, 3562, 3562, 3526, 97, 97, 418, 418, 370] },
  { wordCode := 292382, rule := .chromograms #[526, 526, 526, 3580, 4174, 139, 436, 430, 436, 127, 127, 139, 430, 436, 2488, 2728, 3262, 4174, 3262, 3262, 4084, 3580, 4174, 4480, 4480, 4084, 4480, 4174, 2488, 2728, 3262, 526, 3262, 3262, 526, 3580, 526, 127, 127, 139, 430, 436] },
  { wordCode := 291324, rule := .chromograms #[3664, 3604, 3604, 3604, 3604, 205, 205, 205, 205, 205, 205, 205, 205, 205, 2758, 2746, 2746, 3664, 3604, 3604, 3604, 3604, 3604, 4192, 4186, 4186, 4870, 4882, 802, 1720, 1744, 1756, 790, 790, 802, 3604, 3604, 205, 205, 205, 205, 205] },
  { wordCode := 291126, rule := .chromograms #[3640, 181, 181, 181, 3712, 3640, 3640, 4240, 4888, 1774, 808, 3640, 181, 181] },
  { wordCode := 291138, rule := .chromograms #[8434, 4888, 403, 181, 2800, 4234, 3640, 4234, 4888, 181, 814, 3640, 403, 181] },
  { wordCode := 291114, rule := .chromograms #[187, 3658, 4894, 3658, 187] },
  { wordCode := 291516, rule := .chromograms #[439, 790, 790, 3676, 772, 391, 391, 391, 373, 391, 391, 211, 391, 373, 2776, 2824, 4798, 3616, 3676, 3676, 3616, 3676, 3670, 4204, 4810, 4192, 4798, 4192, 211, 373, 427, 427, 772, 3676, 790, 3676, 772, 391, 391, 211, 391, 373] },
  { wordCode := 291500, rule := .chromograms #[2842, 3622, 778, 766, 778, 223, 385, 361, 385, 199, 199, 223, 361, 385, 3610, 2836, 2836, 2842, 3610, 3610, 3622, 4210, 4210, 4822, 4822, 4822, 4210, 4210, 3610, 2836, 2836, 2842, 3610, 3610, 3622, 766, 778, 199, 199, 223, 361, 385] },
  { wordCode := 291390, rule := .chromograms #[3694, 397, 397, 397, 4840, 3694, 3694, 4846, 4840, 421, 3694, 3694, 397, 397] },
  { wordCode := 291414, rule := .chromograms #[3700, 421, 421, 397, 4846, 3700, 3694, 4840, 4840, 397, 3700, 3694, 421, 397] },
  { wordCode := 291362, rule := .chromograms #[820, 409, 193, 409, 2866, 3652, 4246, 4864, 4246, 2866, 3652, 820, 193, 409] },
  { wordCode := 291024, rule := .chromograms #[3754, 265, 265, 265, 3790, 3754, 3754, 4264, 4930, 1852, 844, 3754, 265, 265] },
  { wordCode := 290976, rule := .chromograms #[856, 253, 253, 235, 2908, 3772, 3760, 4942, 4252, 235, 3772, 856, 253, 235] },
  { wordCode := 290960, rule := .chromograms #[3778, 247, 247, 247, 3832, 3778, 3778, 4924, 4954, 3832, 3778, 3778, 247, 247] },
  { wordCode := 291086, rule := .chromograms #[2950, 3748, 832, 826, 832, 271, 331, 319, 331, 259, 259, 271, 319, 331, 3742, 2944, 2944, 2950, 3742, 3742, 3748, 3796, 3796, 4906, 4906, 4906, 4270, 4270, 3742, 2944, 2944, 2950, 3742, 3742, 3748, 826, 832, 259, 259, 271, 319, 331] },
  { wordCode := 291038, rule := .chromograms #[3832, 337, 247, 337, 3778, 3778, 3832, 4924, 4924, 3778, 3778, 3832, 247, 337] },
  { wordCode := 294498, rule := .chromograms #[472, 112, 4336, 2356, 292, 112, 472, 4426, 292, 472, 568, 562, 4426, 472, 2356, 4336, 2530, 2530, 4336, 2356, 2530, 2356, 4336, 3868, 3976, 3976, 4426, 4102, 100, 292, 196, 472, 22, 100, 100, 196, 292, 22, 100, 100, 196, 292] },
  { wordCode := 237464, rule := .chromograms #[4381, 4465, 4807, 4819, 4465, 4381, 4381, 4459, 4459, 4465, 4381, 4381, 4459, 4459] },
  { wordCode := 237638, rule := .chromograms #[4351, 4435, 4837, 4849, 4435, 4351, 4351, 4447, 4435, 4435, 4351, 4351, 4447, 4435] },
  { wordCode := 294926, rule := .chromograms #[2392, 2392, 82, 19, 82, 580, 82, 19, 82, 580, 538, 580, 538, 580, 2380, 2380, 2380, 2392, 2380, 2380, 2392, 4630, 4630, 4000, 4000, 4000, 4000, 4000, 2380, 2380, 2380, 2392, 2380, 2380, 2392, 19, 82, 580, 538, 580, 19, 82] },
  { wordCode := 236678, rule := .chromograms #[4489, 4543, 4573, 4747, 4507, 4489, 4489, 4555, 4543, 4507, 4489, 4489, 4555, 4543] },
  { wordCode := 295104, rule := .chromograms #[76, 76, 76, 130, 118, 76, 76, 130, 118, 574, 4660, 652, 4504, 574, 2644, 3424, 4660, 2212, 4540, 2644, 2212, 2524, 2596, 3994, 4660, 3916, 4504, 3916, 652, 118, 25, 76, 118, 25, 76, 25, 76, 118, 25, 76, 25, 76] },
  { wordCode := 29678, rule := .chromograms #[4878, 4620, 4734, 5628, 4620, 4734, 4878, 4734, 4620, 4620, 4734, 4878, 4734, 4620] },
  { wordCode := 293538, rule := .chromograms #[367, 205, 367, 427, 445, 205, 367, 427, 445, 760, 4810, 802, 4798, 760, 2758, 3616, 4810, 2824, 4786, 2758, 2776, 2752, 2776, 4222, 4810, 4186, 4798, 4186, 802, 445, 391, 367, 445, 391, 205, 391, 367, 445, 391, 205, 391, 367] },
  { wordCode := 238244, rule := .chromograms #[4843, 4969, 4333, 4345, 4801, 4843, 4843, 4909, 4969, 4345, 4405, 4843, 4333, 4345] },
  { wordCode := 30766, rule := .chromograms #[5406, 5406, 5400, 5400, 5406, 5400, 5400, 5352, 5358, 4374, 4374, 4380, 4398, 4410] },
  { wordCode := 30778, rule := .chromograms #[5400, 5400, 5400, 5406, 5400, 5400, 5406, 5352, 5352, 4380, 4374, 4374, 4398, 4398] },
  { wordCode := 30820, rule := .chromograms #[5406, 6204, 6198, 6198, 5400, 5400, 5400, 5400, 5400, 4380, 4374, 4380, 4374, 4380] },
  { wordCode := 30832, rule := .chromograms #[5400, 6198, 6198, 6204, 5406, 5400, 5406, 5400, 5406, 4374, 4374, 4374, 4374, 4374] },
  { wordCode := 31402, rule := .chromograms #[5820, 5526, 5526, 4494, 4788] },
  { wordCode := 31522, rule := .chromograms #[5598, 5844, 5838, 5838, 5586, 5586, 5586, 5550, 5586, 4548, 4548, 4560, 4812, 4824] },
  { wordCode := 31534, rule := .chromograms #[5586, 5838, 5838, 4836, 5556, 5586, 5592, 5550, 5550, 4512, 4548, 4548, 4812, 4812] },
  { wordCode := 31726, rule := .chromograms #[5706, 6006, 6006, 5952, 6006, 5706, 5664, 5706, 5664, 4656, 4656, 4692, 4938, 4968] },
  { wordCode := 31780, rule := .chromograms #[6564, 6564, 6006, 6006, 5706, 5706, 5706, 5706, 5706, 4692, 4656, 4656, 4938, 4938] },
  { wordCode := 31846, rule := .chromograms #[5754, 5922, 6450, 4896, 5748, 5748, 5748, 5610, 5622, 4596, 4716, 4722, 4866, 4872] },
  { wordCode := 32698, rule := .chromograms #[5706, 5706, 5706, 5664, 5706, 5706, 5664, 6006, 5952, 4692, 4656, 4692, 4656, 4692] },
  { wordCode := 278856, rule := .chromograms #[2137, 1921, 1921, 1921, 5362, 5674, 5026, 5164, 5026, 5362, 5674, 2137, 1921, 1921] },
  { wordCode := 278742, rule := .chromograms #[2155, 1939, 1939, 1939, 5416, 5080, 5056, 5080, 5056, 907, 907, 2155, 1939, 1939] },
  { wordCode := 278604, rule := .chromograms #[2101, 1969, 1969, 1969, 5494, 5782, 5092, 5212, 5092, 5494, 5782, 2101, 1969, 1969] },
  { wordCode := 278580, rule := .chromograms #[961, 2107, 1987, 5098, 5500, 5110, 5098, 5110, 5098, 5500, 2083, 961, 1987, 2107] },
  { wordCode := 278496, rule := .chromograms #[1975, 5806, 5236, 5806, 1975] },
  { wordCode := 279822, rule := .chromograms #[5338, 5338, 1909, 1909, 1909, 2119, 1909, 1909, 1909, 2053, 2053, 2119, 2119, 2119, 5350, 5350, 4996, 5338, 5350, 5140, 5338, 5140, 5170, 5032, 5020, 5032, 4996, 5032, 931, 931, 1957, 5338, 5350, 1957, 5338, 1909, 1909, 2053, 1957, 2119, 1909, 1909] },
  { wordCode := 279828, rule := .chromograms #[1921, 1921, 2137, 2137, 5362, 5362, 5164, 5026, 5026, 5362, 5362, 1921, 2137, 1921] },
  { wordCode := 279780, rule := .chromograms #[5440, 2125, 2125, 2125, 5008, 5440, 5440, 5038, 5008, 2179, 5440, 5440, 2125, 2125] },
  { wordCode := 251560, rule := .chromograms #[14932, 6505, 5155, 2647, 5155] },
  { wordCode := 279858, rule := .chromograms #[5452, 2179, 2179, 2125, 5038, 5452, 5440, 5008, 5008, 2125, 5452, 5440, 2179, 2125] },
  { wordCode := 279714, rule := .chromograms #[1939, 1939, 2041, 2155, 5416, 5416, 5188, 5056, 5056, 907, 5416, 1939, 2041, 1939] },
  { wordCode := 279414, rule := .chromograms #[1969, 1969, 2101, 2101, 5494, 5494, 5212, 5092, 5092, 5494, 5494, 1969, 2101, 1969] },
  { wordCode := 253234, rule := .chromograms #[2935, 14578, 14518, 14518, 6343, 6103, 6103, 5017, 5113, 2761, 2761, 2935, 5017, 5113] },
  { wordCode := 278184, rule := .chromograms #[5890, 1999, 1999, 1999, 5242, 5890, 5890, 5248, 5242, 2005, 5890, 5890, 1999, 1999] },
  { wordCode := 277998, rule := .chromograms #[1993, 5908, 5254, 5908, 1993] },
  { wordCode := 277896, rule := .chromograms #[5956, 2011, 2011, 2011, 5266, 5956, 5956, 5272, 5266, 2017, 5956, 5956, 2011, 2011] },
  { wordCode := 277908, rule := .chromograms #[5962, 2017, 2017, 2011, 5272, 5962, 5956, 5266, 5266, 2011, 5962, 5956, 2017, 2011] },
  { wordCode := 277806, rule := .chromograms #[2023, 5998, 5284, 5998, 2023] },
  { wordCode := 250426, rule := .chromograms #[3169, 3859, 5383, 5287, 5989, 5383, 5287, 5383, 5287, 3085, 3085, 3169, 3769, 3859] },
  { wordCode := 35094, rule := .chromograms #[4368, 5382, 5340, 5382, 5340] },
  { wordCode := 35140, rule := .chromograms #[5400, 6198, 6198, 6198, 5406, 5400, 5400, 5352, 5358, 5406, 5400, 5400, 5352, 5358] },
  { wordCode := 35152, rule := .chromograms #[5406, 6204, 6198, 6204, 5400, 5400, 5406, 5352, 5352, 5400, 5400, 5406, 5352, 5352] },
  { wordCode := 35986, rule := .chromograms #[6762, 5748, 5616, 4722, 5748, 5616, 5622, 5616, 5622, 5748, 5616, 5622, 5616, 5622] },
  { wordCode := 249420, rule := .chromograms #[3487, 5707, 5635, 3415, 3487] },
  { wordCode := 249466, rule := .chromograms #[5689, 3499, 3499, 3499, 5701, 5689, 5689, 5605, 5623, 3421, 3421, 3433, 3499, 3499] },
  { wordCode := 249478, rule := .chromograms #[5701, 3517, 3499, 3517, 5689, 5689, 5701, 5605, 5605, 3433, 3421, 3421, 3499, 3517] },
  { wordCode := 36100, rule := .chromograms #[6564, 6876, 5706, 5664, 6006, 5706, 5664, 5706, 5664, 6006, 5706, 5664, 5706, 5664] },
  { wordCode := 251398, rule := .chromograms #[3169, 3169, 5989, 5917, 5383, 5383, 5287, 5989, 5917, 3769, 3085, 3169, 3085, 3169] },
  { wordCode := 37072, rule := .chromograms #[6564, 6564, 6006, 5952, 5706, 5706, 5664, 6006, 5952, 5706, 5706, 5664, 6006, 5952] },
  { wordCode := 37248, rule := .chromograms #[4344, 4344, 6078, 6066, 5310] },
  { wordCode := 276582, rule := .chromograms #[1165, 1669, 1669, 1669, 6430, 6550, 6148, 6268, 6148, 1135, 1135, 1165, 1669, 1669] },
  { wordCode := 37446, rule := .chromograms #[4440, 4440, 6222, 6282, 5484] },
  { wordCode := 276870, rule := .chromograms #[1399, 1795, 1795, 1795, 6424, 6382, 6382, 6076, 6130, 1351, 1351, 1399, 1795, 1795] },
  { wordCode := 276828, rule := .chromograms #[1393, 6166, 6268, 1831, 6166, 6268, 6430, 6268, 6166, 1165, 1375, 1375, 1669, 1831] },
  { wordCode := 276410, rule := .chromograms #[1255, 1771, 6304, 6286, 6622, 6304, 6286, 6304, 6286, 6622, 6304, 1255, 6304, 1771] },
  { wordCode := 254960, rule := .chromograms #[5119, 2929, 2767, 2755, 2767, 2287, 2767, 2755, 2767, 6331, 2287, 2281, 2461, 2461, 5035, 5107, 5107, 5119, 6331, 5263, 6133, 5263, 6325, 6331, 6139, 6133, 6325, 6325, 2281, 2461, 2461, 2461, 6331, 2923, 2923, 2755, 2767, 6331, 2287, 2281, 2461, 2461] },
  { wordCode := 255134, rule := .chromograms #[5095, 2995, 2797, 2779, 2797, 2209, 2797, 2779, 2797, 6277, 2209, 2209, 2425, 2425, 5005, 5083, 5083, 5095, 6277, 5281, 6073, 5281, 6277, 6277, 6073, 6073, 6289, 6277, 2215, 2425, 2425, 2425, 6277, 3001, 2995, 2779, 2797, 6277, 2209, 2209, 2425, 2425] },
  { wordCode := 277352, rule := .chromograms #[6244, 1081, 1081, 1081, 6262, 6244, 6244, 6484, 6532, 6262, 6244, 6244, 1081, 1081] },
  { wordCode := 277430, rule := .chromograms #[6262, 1195, 1081, 1195, 6244, 6244, 6262, 6484, 6484, 6244, 6244, 6262, 1081, 1195] },
  { wordCode := 254174, rule := .chromograms #[5191, 5191, 6427, 5233, 14380, 2509, 6427, 2557, 6607, 6391, 2509, 2509, 2557, 6427, 5233, 6427, 5191, 5191, 6391, 5191, 5191, 5233, 6427, 6391, 6373, 6373, 6433, 6427, 2737, 6427, 2701, 5191, 6391, 2701, 2737, 2701, 6427, 6391, 2509, 2509, 2557, 6427] },
  { wordCode := 277608, rule := .chromograms #[1201, 1201, 1399, 1351, 6424, 6520, 6076, 6388, 6424, 1351, 1087, 1201, 1087, 1201] },
  { wordCode := 38328, rule := .chromograms #[5658, 5946, 5892, 6540, 4752, 6510, 4686, 6510, 4686, 6612, 5988, 5658, 5892, 5946] },
  { wordCode := 255520, rule := .chromograms #[6289, 2215, 2425, 2425, 2425, 2215, 2425, 2425, 2425, 6703, 3001, 2995, 2779, 2797, 6079, 6289, 6289, 6277, 6703, 6847, 6841, 5041, 5053, 6277, 6073, 6073, 6289, 6277, 2209, 2797, 2779, 2797, 6703, 2209, 2209, 2425, 2425, 6277, 2209, 2209, 2425, 2425] },
  { wordCode := 276042, rule := .chromograms #[1441, 1591, 1645, 1657, 6652, 6670, 6682, 6658, 6652, 1657, 1615, 1441, 1615, 1591] },
  { wordCode := 255460, rule := .chromograms #[6325, 2281, 2461, 2461, 2461, 2281, 2461, 2461, 2461, 6673, 2923, 2923, 2755, 2767, 6133, 6325, 6325, 6325, 6673, 6799, 6799, 5011, 5023, 6331, 6139, 6133, 6325, 6325, 2287, 2767, 2755, 2767, 6673, 2287, 2281, 2461, 2461, 6331, 2287, 2281, 2461, 2461] },
  { wordCode := 255592, rule := .chromograms #[2449, 2323, 2449, 6703, 5041, 2323, 2449, 6703, 2779, 2917, 2917, 2779, 6703, 2779, 6187, 6313, 6703, 5083, 6793, 6703, 5041, 5005, 5005, 6073, 6145, 6187, 6277, 6313, 2779, 2779, 6703, 2449, 2209, 2293, 2323, 5005, 2449, 2209, 2293, 2323, 6277, 2449] },
  { wordCode := 38934, rule := .chromograms #[4728, 4728, 4902, 5868, 6774] },
  { wordCode := 38946, rule := .chromograms #[6600, 4626, 4740, 4740, 4626, 4740, 4740, 6726, 4914, 6480, 5760, 5874, 5760, 6780] },
  { wordCode := 39006, rule := .chromograms #[6624, 4668, 4758, 4758, 4668, 4758, 4758, 6750, 4980, 6528, 5772, 5898, 5772, 6864] },
  { wordCode := 39066, rule := .chromograms #[4752, 4752, 4752, 4776, 4752, 4752, 4776, 6804, 6804, 6612, 5880, 5880, 5658, 5700] },
  { wordCode := 39132, rule := .chromograms #[4584, 4584, 6714, 6444, 5742] },
  { wordCode := 255740, rule := .chromograms #[5047, 5047, 6853, 5089, 14236, 2791, 6853, 2899, 6067, 6661, 2791, 2791, 2899, 6853, 5089, 6853, 5047, 5047, 6661, 5047, 5047, 5089, 6853, 6067, 6169, 6295, 6055, 6067, 2431, 6853, 2311, 5047, 6661, 2311, 2431, 2311, 6853, 6067, 2311, 2431, 2311, 6067] },
  { wordCode := 39192, rule := .chromograms #[4614, 4614, 4614, 4626, 4614, 4614, 4626, 6726, 4920, 6474, 6474, 5640, 5760, 5640] },
  { wordCode := 324846, rule := .chromograms #[64, 64, 64, 112, 4642, 64, 64, 112, 658, 478, 472, 478, 472, 478, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 2230, 7918, 7918, 8014, 8878, 8584, 8560, 8584, 8560, 8584, 12700, 12652, 12652, 12922, 12922] },
  { wordCode := 324838, rule := .chromograms #[4618, 4348, 4618, 2620, 2620, 3910, 3910, 4618, 6958, 4618, 4348, 6958, 4348, 6958, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 7444, 7492, 6928, 6958, 7168, 6928, 6958, 6928, 6958, 7168, 6928, 6958, 6928, 6958] },
  { wordCode := 325428, rule := .chromograms #[484, 2398, 2296, 2398, 322, 4432, 484, 4432, 322, 484, 592, 586, 592, 586, 2548, 2548, 2548, 2548, 2296, 2398, 2548, 2548, 2548, 2296, 2398, 2548, 2548, 2548, 11416, 8596, 11416, 8230, 8596, 8770, 8764, 8770, 8764, 12742, 12796, 12796, 12748, 12742] },
  { wordCode := 325716, rule := .chromograms #[1102, 25, 2278, 2212, 2212, 25, 4378, 4354, 4354, 652, 652, 652, 532, 574, 2212, 2596, 2596, 2596, 2278, 2212, 2212, 2518, 2596, 2278, 2212, 2212, 2518, 2596, 7870, 11464, 11464, 11524, 8860, 8860, 8860, 8698, 8752, 12736, 12664, 12736, 12664, 12736] },
  { wordCode := 325810, rule := .chromograms #[4348, 4348, 4348, 2248, 2248, 3910, 4114, 4348, 7198, 4348, 4348, 6958, 4618, 7198, 2248, 2620, 2620, 2620, 2620, 2248, 2248, 2620, 2620, 2620, 2248, 2248, 2620, 2620, 7444, 7444, 7168, 7198, 6928, 6928, 6958, 7168, 7198, 6928, 6928, 6958, 7168, 7198] },
  { wordCode := 324108, rule := .chromograms #[2818, 4876, 796, 784, 2770, 2770, 2770, 2770, 2770, 11662, 9088, 9070, 13084, 13084] },
  { wordCode := 323772, rule := .chromograms #[253, 253, 850, 850, 2908, 2908, 2908, 2908, 2908, 8470, 9148, 9148, 13132, 13180] },
  { wordCode := 323878, rule := .chromograms #[2938, 2938, 4918, 4906, 4906, 4918, 4276, 4270, 4270, 4918, 4906, 4906, 7390, 7396, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 2926, 7372, 7522, 7522, 7522, 7378, 7372, 7372, 7390, 7396, 7378, 7372, 7372, 7390, 7396] },
  { wordCode := 323890, rule := .chromograms #[2926, 2926, 4906, 4906, 4918, 4906, 4270, 4270, 4276, 4906, 4906, 4918, 7390, 7390, 2938, 2938, 2926, 2938, 2938, 2926, 2938, 2926, 2938, 2938, 2926, 2938, 2926, 2938, 7378, 7528, 7522, 7528, 7372, 7372, 7378, 7390, 7390, 7372, 7372, 7378, 7390, 7390] },
  { wordCode := 323838, rule := .chromograms #[862, 2992, 2992, 9172, 13144] },
  { wordCode := 323754, rule := .chromograms #[2998, 4966, 874, 868, 3010, 2998, 3010, 2998, 3010, 11854, 9184, 9178, 13186, 13186] },
  { wordCode := 326996, rule := .chromograms #[892, 988, 988, 1228, 454, 454, 988, 892, 616, 454, 454, 892, 3442, 454, 454, 946, 940, 946, 940, 946, 10, 10, 34, 34, 40, 238, 280, 280, 286, 244, 238, 244, 238, 244, 16, 16, 10, 16, 16, 10, 16, 10, 16, 16, 10, 16, 10, 16, 2386, 3070, 2266, 2254, 2266, 3070, 3070, 2626, 3070, 2536, 3058, 3070, 3040, 3070, 3070, 3070, 3058, 3070, 3070, 3058, 3070, 3040, 3070, 3070, 3058, 3070, 3040, 3070, 2206, 2206, 2200, 2200, 2206, 2200, 2200, 2224, 2224, 2536, 2578, 2578, 2602, 2602, 6916, 6916, 6952, 6952, 6952, 7072, 8194, 7192, 8200, 7066, 7066, 7072, 7438, 8170, 7852, 7852, 7846, 7474, 7852, 7846, 7852, 7438, 7486, 7462, 7846, 7852, 7438, 7852, 6922, 6922, 6910, 6910, 6922, 6910, 6910, 6940, 6940, 7066, 7066, 7072, 7180, 7180] },
  { wordCode := 326972, rule := .chromograms #[460, 460, 460, 3418, 3388, 52, 298, 256, 256, 28, 28, 28, 28, 28, 2272, 2638, 3076, 3052, 3076, 3076, 3052, 3076, 3052, 2620, 2248, 2248, 2620, 2620, 6958, 7198, 8212, 7444, 8212, 7906, 7444, 7906, 7444, 6928, 6928, 6958, 7168, 7198] },
  { wordCode := 326924, rule := .chromograms #[7060, 3472, 958, 952, 952, 82, 316, 268, 268, 19, 19, 19, 19, 19, 3430, 7060, 7060, 7060, 3472, 3430, 3430, 4000, 4012, 2218, 2218, 2284, 7060, 7060, 7936, 7060, 7060, 7060, 7876, 7876, 7876, 7876, 7876, 7204, 7174, 7204, 7060, 7060] },
  { wordCode := 327046, rule := .chromograms #[6892, 3184, 3064, 3040, 3064, 190, 3184, 3064, 3040, 3064, 904, 3304, 3304, 3316, 904, 3382, 3400, 946, 4096, 3448, 4372, 4342, 4372, 6892, 16, 4342, 4372, 7132, 190, 4096, 4096, 244, 304, 286, 3886, 3886, 3886, 40, 3886, 3886, 16, 58, 40, 94, 3886, 16, 58, 40, 2224, 2200, 2200, 6892, 2188, 2578, 2578, 3184, 3106, 3040, 3064, 3070, 2536, 3106, 3304, 3304, 3184, 3106, 3040, 3064, 3070, 3886, 3106, 3040, 3064, 3070, 3184, 3106, 2236, 2236, 2236, 2224, 2188, 2236, 2200, 6892, 2188, 2608, 2608, 2578, 2536, 2578, 6940, 6910, 6892, 6892, 6892, 7150, 7078, 7132, 7072, 7078, 11866, 7072, 7084, 7072, 11944, 11944, 7462, 7480, 7438, 11866, 7852, 7912, 7498, 7438, 11968, 7852, 7462, 7894, 7072, 7072, 6994, 6940, 6898, 6916, 6910, 6892, 6892, 7078, 7156, 7072, 7084, 7072] },
  { wordCode := 327026, rule := .chromograms #[1000, 910, 910, 3418, 3460, 28, 256, 256, 298, 52, 28, 52, 28, 52, 2194, 2572, 3076, 3130, 3418, 3076, 3130, 3076, 3130, 2248, 2248, 2194, 2620, 2572, 6904, 7144, 8212, 7456, 7906, 7906, 7456, 7906, 7456, 7168, 6928, 6904, 7168, 7144] },
  { wordCode := 327068, rule := .chromograms #[10, 184, 184, 184, 988, 7078, 550, 616, 892, 892, 3370, 898, 892, 892, 3298, 940, 3376, 3370, 4096, 3448, 232, 4, 4, 4, 4360, 184, 184, 232, 4360, 232, 232, 304, 304, 286, 58, 40, 58, 58, 4, 4, 58, 58, 40, 4, 4, 58, 58, 40, 2266, 2188, 2188, 6916, 2200, 7138, 3106, 2536, 2578, 2506, 2506, 4108, 2536, 3106, 3310, 3106, 3376, 3298, 3034, 3034, 3370, 3886, 3106, 3034, 3034, 3892, 3184, 3106, 2260, 2242, 2260, 2266, 2200, 2260, 2188, 6892, 2188, 2506, 2506, 7078, 2536, 2578, 6952, 6898, 6898, 6916, 6910, 7138, 7072, 7084, 7078, 7054, 7054, 7078, 7084, 7072, 7912, 7894, 7912, 7486, 7846, 7912, 7486, 7912, 7498, 7468, 7462, 7912, 7462, 7894, 7078, 6946, 7132, 6952, 6892, 6892, 6892, 6892, 6892, 7054, 7054, 7078, 7084, 7072] },
  { wordCode := 327002, rule := .chromograms #[7096, 3430, 952, 952, 958, 19, 268, 268, 316, 82, 19, 82, 19, 82, 3472, 7096, 7060, 7096, 3430, 3430, 3472, 4000, 4000, 2284, 2218, 2218, 7060, 7096, 7876, 7096, 7060, 7096, 7936, 7876, 7936, 7876, 7936, 7174, 7174, 7174, 7060, 7096] },
  { wordCode := 326894, rule := .chromograms #[1300, 694, 3478, 964, 964, 43, 328, 328, 346, 73, 43, 73, 43, 73, 2302, 3160, 3148, 3160, 3160, 3148, 3160, 3148, 3160, 2314, 2308, 2302, 2662, 2662, 7954, 8236, 7108, 8254, 7972, 7954, 7972, 7954, 7972, 6970, 6964, 6964, 7108, 7210] },
  { wordCode := 326848, rule := .chromograms #[3172, 3172, 3514, 3502, 3502, 3964, 7114, 4138, 352, 3952, 3952, 61, 166, 61, 3502, 7114, 3172, 4138, 3514, 3172, 3502, 3172, 3952, 2320, 2320, 2332, 2686, 7114, 6976, 7114, 7114, 7114, 12016, 11896, 7978, 8068, 7978, 7234, 6982, 6976, 7114, 7114] },
  { wordCode := 326852, rule := .chromograms #[214, 706, 922, 3508, 3502, 67, 214, 352, 352, 61, 61, 61, 61, 61, 2332, 7234, 3166, 4138, 3358, 3166, 3502, 3166, 3952, 2326, 2326, 2332, 2692, 7114, 6982, 7234, 8260, 7114, 7978, 7978, 7978, 7978, 7978, 7114, 6976, 6976, 7228, 7114] },
  { wordCode := 326858, rule := .chromograms #[220, 502, 502, 3508, 3508, 61, 220, 352, 358, 67, 61, 67, 61, 67, 2320, 2686, 3166, 3166, 3166, 3166, 3166, 3166, 3166, 2416, 2326, 2320, 2692, 2686, 7222, 7222, 8260, 7120, 8068, 7978, 12010, 7978, 8068, 6976, 6976, 7222, 7228, 7120] },
  { wordCode := 326860, rule := .chromograms #[4138, 3502, 3502, 3502, 3508, 3952, 4138, 4138, 358, 3964, 3952, 67, 166, 67, 2326, 2692, 3172, 3166, 3172, 3172, 3166, 3172, 3166, 2332, 2320, 2320, 2686, 2686, 8620, 7120, 7114, 7120, 11896, 11896, 12010, 8068, 8068, 6982, 6982, 7222, 7114, 7120] },
  { wordCode := 326836, rule := .chromograms #[3520, 4144, 3970, 3970, 3178, 3178, 3178, 2338, 2698, 11902, 11902, 12028, 6988, 7240] },
  { wordCode := 327212, rule := .chromograms #[7072, 232, 232, 232, 238, 244, 892, 3310, 940, 940, 946, 898, 892, 898, 904, 454, 454, 454, 454, 454, 34, 88, 184, 184, 190, 184, 184, 184, 190, 184, 184, 190, 454, 454, 58, 40, 34, 40, 94, 88, 94, 88, 94, 94, 88, 58, 34, 40, 2350, 2350, 2386, 7066, 3286, 7138, 3106, 2566, 3106, 2608, 2566, 4324, 2566, 2578, 3310, 3106, 3100, 3106, 3310, 3310, 3286, 3982, 3286, 3040, 3040, 3892, 3100, 3106, 2260, 2242, 2224, 2224, 2362, 2344, 2344, 7066, 2386, 2608, 2566, 7078, 2566, 2578, 6994, 6994, 7000, 7066, 7072, 7138, 7072, 7066, 7072, 7138, 7126, 7132, 7126, 7132, 7912, 7894, 7888, 7480, 7996, 7990, 7474, 7990, 7474, 7438, 7438, 7912, 7450, 7894, 7078, 6946, 6940, 6940, 7078, 7078, 6994, 7066, 7000, 7078, 7078, 7078, 7066, 7072] },
  { wordCode := 327226, rule := .chromograms #[7078, 2590, 2590, 2614, 2602, 2602, 3118, 3304, 3202, 3298, 3298, 3304, 3304, 3298, 3298, 3286, 3298, 466, 454, 454, 3904, 3988, 7078, 7078, 7000, 4342, 4372, 4360, 4360, 4324, 4330, 466, 454, 454, 3886, 3886, 3892, 58, 3982, 3982, 3982, 88, 94, 4, 10, 16, 34, 40, 3298, 3298, 3286, 7078, 2386, 2578, 2578, 2578, 2578, 2578, 2578, 2578, 2566, 2578, 3304, 3304, 3118, 3298, 3202, 3298, 3298, 3982, 3286, 3034, 3058, 3070, 3100, 3106, 2236, 2236, 2254, 2266, 2368, 2368, 2374, 7066, 2386, 2506, 2578, 2578, 2566, 2578, 7132, 11938, 7078, 7078, 7000, 7150, 7078, 7078, 7078, 7132, 7150, 7150, 7126, 7132, 11944, 11944, 7450, 7486, 7468, 11938, 11944, 7990, 7474, 7468, 7846, 7852, 7450, 7894, 7072, 7072, 6952, 6952, 7000, 7066, 7072, 7066, 7000, 7054, 7066, 7072, 7066, 7072] },
  { wordCode := 326738, rule := .chromograms #[1006, 970, 970, 3556, 4168, 103, 400, 400, 406, 115, 103, 115, 103, 115, 7006, 7276, 3232, 4168, 3556, 3232, 4066, 3232, 4066, 2434, 2434, 7006, 2722, 7276, 7006, 7276, 8296, 8296, 8104, 8104, 8104, 8104, 8104, 7282, 7012, 7006, 7282, 7276] },
  { wordCode := 326768, rule := .chromograms #[1360, 730, 3544, 976, 976, 157, 382, 376, 376, 145, 145, 145, 145, 145, 2470, 3250, 3250, 3250, 3250, 3250, 3250, 3250, 3250, 2464, 2464, 2470, 2710, 2716, 8134, 8284, 7288, 8278, 8128, 8128, 8128, 8128, 8128, 7030, 7030, 7036, 7252, 7264] },
  { wordCode := 327960, rule := .chromograms #[100, 628, 562, 562, 3868, 46, 46, 22, 22, 46, 22, 22, 250, 196, 3412, 3328, 3412, 2356, 3112, 3112, 3412, 3412, 3328, 2230, 2230, 2230, 2230, 2230, 7900, 7900, 7858, 7858, 7900, 7858, 7858, 8176, 8152, 12700, 12652, 12652, 12922, 12922] },
  { wordCode := 327944, rule := .chromograms #[634, 460, 634, 3076, 3052, 52, 52, 28, 28, 52, 28, 28, 256, 256, 2272, 2272, 3418, 3388, 3418, 3076, 3052, 3418, 3388, 2248, 2248, 2248, 2248, 2248, 6958, 6958, 7906, 7492, 7906, 7906, 7444, 8212, 7492, 7168, 6928, 6958, 6928, 6958] },
  { wordCode := 203418, rule := .chromograms #[15103, 10333] },
  { wordCode := 327998, rule := .chromograms #[910, 910, 1000, 3076, 3130, 28, 28, 28, 52, 28, 28, 52, 256, 298, 2194, 2194, 3418, 3460, 3076, 3076, 3130, 3418, 3460, 2620, 2248, 2194, 2248, 2194, 6904, 6904, 7906, 7504, 8212, 7906, 7456, 8212, 7504, 6928, 6928, 6904, 6928, 6904] },
  { wordCode := 327820, rule := .chromograms #[2422, 3172, 3172, 3172, 3952, 3964, 3964, 3952, 61, 3964, 3952, 61, 214, 220, 3502, 2416, 2416, 2416, 3172, 3172, 3502, 3358, 3364, 2332, 2320, 2332, 2320, 2332, 6976, 6976, 8794, 7978, 11896, 11896, 7978, 11896, 8260, 6982, 6982, 6976, 6982, 6976] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk022 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 327808, rule := .chromograms #[3178, 3970, 3970, 4144, 3520, 3178, 3520, 2338, 2338, 12028, 11902, 11902, 6988, 6988] },
  { wordCode := 327434, rule := .chromograms #[97, 3244, 3238, 3244, 8272, 175, 97, 175, 7018, 97, 175, 370, 370, 370, 3526, 3526, 3526, 2428, 3238, 3244, 3526, 3526, 3526, 2428, 2458, 2458, 2458, 2428, 8116, 8092, 8116, 7018, 8092, 8116, 8272, 8272, 8272, 7018, 7024, 7024, 7024, 7018] },
  { wordCode := 327428, rule := .chromograms #[982, 982, 3250, 754, 754, 145, 145, 145, 157, 145, 145, 157, 376, 382, 3256, 3544, 2446, 3544, 3250, 3250, 3256, 3532, 3544, 2464, 2464, 2464, 2446, 2464, 7258, 8128, 8128, 8134, 8128, 8128, 8134, 8278, 8284, 7030, 7030, 7030, 7030, 7030] },
  { wordCode := 327332, rule := .chromograms #[1018, 121, 121, 448, 7042, 3280, 4180, 2740, 7042, 7042, 8326, 8326, 7048, 7042] },
  { wordCode := 326492, rule := .chromograms #[7312, 3610, 1024, 1024, 1030, 199, 199, 199, 223, 199, 199, 223, 361, 385, 3622, 7312, 7306, 7312, 3610, 3610, 3622, 4210, 4210, 2830, 2812, 2812, 7306, 7312, 8368, 7312, 7306, 7312, 8386, 8368, 8386, 8368, 8386, 7318, 7318, 7318, 7306, 7312] },
  { wordCode := 326484, rule := .chromograms #[3628, 217, 217, 379, 3682, 3628, 3682, 2770, 2770, 8344, 8344, 8392, 13084, 13084] },
  { wordCode := 326012, rule := .chromograms #[2950, 3748, 832, 826, 826, 271, 331, 319, 319, 259, 259, 259, 259, 259, 3742, 2944, 2944, 2944, 3742, 3742, 3742, 3718, 3724, 2938, 2926, 2938, 2926, 2938, 8488, 7390, 7390, 7390, 8488, 8482, 8482, 7522, 7528, 7372, 7372, 7378, 7390, 7390] },
  { wordCode := 326024, rule := .chromograms #[2944, 3742, 826, 826, 832, 259, 319, 319, 331, 271, 259, 271, 259, 271, 3748, 2950, 2944, 2950, 3748, 3742, 3748, 3718, 3718, 2926, 2926, 2926, 2926, 2926, 8482, 7396, 7390, 7396, 8482, 8482, 8488, 7522, 7522, 7378, 7372, 7372, 7390, 7396] },
  { wordCode := 205488, rule := .chromograms #[14845, 14785, 14785, 10207, 15037, 14971, 14971, 15139, 15139, 10135, 10135, 10135, 10135, 10135] },
  { wordCode := 326066, rule := .chromograms #[2884, 3748, 1042, 1036, 1036, 271, 271, 259, 259, 271, 259, 259, 319, 319, 3742, 2878, 2878, 2878, 3748, 3742, 3742, 3796, 3802, 2926, 2926, 2938, 2878, 2878, 8488, 7354, 7354, 7354, 8482, 8482, 8482, 7546, 7552, 7378, 7372, 7378, 7354, 7354] },
  { wordCode := 326078, rule := .chromograms #[2878, 3742, 1036, 1036, 1042, 259, 259, 259, 271, 259, 259, 271, 319, 331, 3748, 2884, 2878, 2884, 3742, 3742, 3748, 3796, 3796, 2938, 2926, 2926, 2878, 2884, 8482, 7360, 7354, 7360, 8488, 8482, 8488, 7546, 7546, 7372, 7372, 7372, 7354, 7360] },
  { wordCode := 325898, rule := .chromograms #[1048, 307, 289, 289, 7420, 3850, 4300, 3004, 7414, 7420, 8524, 8524, 7414, 7414] },
  { wordCode := 325876, rule := .chromograms #[3862, 4318, 4312, 4312, 3856, 3856, 3856, 3022, 3028, 12100, 12100, 12106, 7426, 7432] },
  { wordCode := 322556, rule := .chromograms #[469, 469, 469, 493, 9436, 469, 469, 493, 865, 769, 769, 769, 769, 769, 9238, 9238, 9274, 7684, 9436, 9436, 9436, 9436, 9436, 7618, 7618, 7696, 7696, 7684, 9238, 9238, 9274, 7684, 9436, 9436, 9436, 9436, 9436, 7618, 7618, 7696, 7696, 7684] },
  { wordCode := 322490, rule := .chromograms #[9478, 853, 787, 787, 9574, 9478, 7594, 7660, 7594, 9574, 9478, 7594, 7660, 7594] },
  { wordCode := 64416, rule := .chromograms #[7524, 7524, 7668, 7734, 7668] },
  { wordCode := 323588, rule := .chromograms #[847, 805, 847, 9322, 7678, 481, 481, 481, 7570, 481, 481, 7636, 505, 7678, 9256, 9256, 9256, 7570, 9256, 9256, 7636, 7690, 7678, 7570, 7576, 7576, 7576, 7570, 9256, 9256, 9256, 7570, 9256, 9256, 7636, 7690, 7678, 7570, 7576, 7576, 7576, 7570] },
  { wordCode := 331386, rule := .chromograms #[136, 664, 8020, 7870, 3466, 1102, 2278, 7870, 1540, 1258, 1102, 1162, 1102, 1162, 2278, 2278, 4504, 3466, 3994, 3088, 3136, 3088, 3136, 3994, 4660, 3916, 4504, 3916, 8860, 8020, 7870, 7930, 8020, 7870, 7930, 7870, 7930, 8020, 7870, 7930, 7870, 7930] },
  { wordCode := 331240, rule := .chromograms #[2410, 3496, 3352, 3496, 3478, 2308, 2308, 2410, 1558, 3352, 3496, 1186, 1300, 1186, 2308, 2308, 2410, 3478, 3352, 3496, 3148, 3934, 3148, 3934, 3934, 3934, 3934, 3934, 6964, 6964, 8776, 7954, 11962, 11998, 7954, 8056, 7954, 8782, 8938, 7954, 8056, 7954] },
  { wordCode := 331222, rule := .chromograms #[2422, 3172, 3514, 3502, 3502, 2326, 2326, 2416, 1576, 3514, 3172, 1210, 1312, 1210, 2326, 2326, 2416, 2416, 3514, 3172, 3502, 3172, 3952, 3952, 3952, 3952, 3952, 3952, 8620, 8794, 8794, 7978, 12016, 11896, 7978, 8068, 7978, 8956, 8626, 7978, 8068, 7978] },
  { wordCode := 331232, rule := .chromograms #[172, 502, 502, 3508, 3508, 928, 928, 1576, 1582, 1222, 1210, 1222, 1210, 1222, 2332, 2332, 3508, 2422, 3166, 3166, 3166, 3166, 3166, 4420, 4420, 3964, 4714, 3964, 6982, 6982, 7978, 8806, 8068, 7978, 12010, 7978, 8068, 8068, 7978, 8950, 7978, 8068] },
  { wordCode := 199850, rule := .chromograms #[8425, 8041, 8011, 9673, 8041, 8011, 8425, 8011, 8041, 8041, 8011, 8425, 8011, 8041] },
  { wordCode := 331540, rule := .chromograms #[2284, 3334, 3334, 3292, 3292, 3334, 2284, 2218, 2218, 3334, 3292, 3292, 1108, 1168, 3334, 2284, 2218, 2218, 3334, 3292, 3292, 4000, 4000, 4000, 4000, 4000, 4000, 4000, 11956, 8866, 8866, 8866, 11956, 11932, 11956, 7876, 7936, 8758, 8704, 8758, 7876, 7936] },
  { wordCode := 66092, rule := .chromograms #[8022, 8046, 8076, 8142, 8034, 8022, 8022, 8052, 8046, 8034, 8022, 8022, 8052, 8046] },
  { wordCode := 332064, rule := .chromograms #[250, 3328, 3868, 628, 628, 1432, 1084, 1240, 1240, 1084, 1240, 1240, 1432, 1522, 3328, 4102, 3190, 2584, 3868, 3190, 3190, 3328, 4102, 3868, 3976, 3976, 4426, 4102, 8002, 8206, 8152, 8560, 7858, 8002, 8002, 8152, 8206, 7858, 8002, 8002, 8152, 8206] },
  { wordCode := 66854, rule := .chromograms #[8370, 8178, 8274, 8178, 8274] },
  { wordCode := 66878, rule := .chromograms #[8184, 8286, 8376, 8382, 8286, 8184, 8184, 8280, 8280, 8286, 8184, 8184, 8280, 8280] },
  { wordCode := 67052, rule := .chromograms #[8220, 8298, 8424, 8436, 8298, 8220, 8220, 8304, 8298, 8298, 8220, 8220, 8304, 8298] },
  { wordCode := 331714, rule := .chromograms #[3274, 2740, 3274, 1660, 2740, 3274, 4180, 4180, 4180, 8692, 11926, 8326, 8686, 8326] },
  { wordCode := 330846, rule := .chromograms #[439, 790, 8416, 8380, 3604, 1720, 2806, 8380, 1666, 1756, 1720, 1666, 1720, 1708, 2764, 2806, 4798, 3604, 4222, 3676, 3604, 3676, 3664, 4222, 4810, 4186, 4798, 4186, 9094, 8416, 8380, 8362, 8416, 8380, 8332, 8380, 8362, 8416, 8380, 8332, 8380, 8362] },
  { wordCode := 330730, rule := .chromograms #[3646, 2860, 3646, 1786, 2860, 3646, 4246, 4246, 4246, 9118, 12058, 8446, 9112, 8446] },
  { wordCode := 67658, rule := .chromograms #[8418, 8514, 8202, 8208, 8406, 8418, 8418, 8490, 8514, 8208, 8232, 8418, 8202, 8208] },
  { wordCode := 333492, rule := .chromograms #[1102, 25, 25, 118, 118, 1102, 1102, 1258, 1258, 2212, 2212, 2212, 2212, 2212, 2278, 2524, 2596, 2596, 2212, 2212, 2212, 2212, 2212, 3874, 3874, 3916, 4354, 4354, 8860, 11524, 11464, 11524, 8890, 8860, 8860, 11464, 11524, 7864, 7864, 7930, 8182, 8224] },
  { wordCode := 333630, rule := .chromograms #[292, 46, 46, 100, 4642, 1132, 1132, 1240, 8152, 8728, 8824, 2230, 2356, 2230, 3112, 3112, 3190, 4366, 4516, 4594, 2230, 2356, 2230, 3898, 3898, 3868, 4426, 4090, 7858, 8152, 8152, 8152, 8728, 8824, 8584, 11410, 8584, 7918, 7918, 7858, 8152, 8152] },
  { wordCode := 333582, rule := .chromograms #[2596, 2212, 118, 118, 130, 2212, 1258, 1258, 1270, 2278, 2212, 2278, 2212, 2278, 2212, 2596, 2596, 2644, 2278, 2212, 2278, 2212, 2278, 3916, 3874, 3874, 4354, 4378, 7870, 11464, 11464, 11464, 8860, 8860, 8890, 11464, 11464, 7930, 7864, 7864, 8182, 8182] },
  { wordCode := 333558, rule := .chromograms #[142, 1282, 2290, 2290, 2656, 2290, 2290, 3880, 4384, 11476, 8902, 11476, 7882, 8188] },
  { wordCode := 333444, rule := .chromograms #[322, 31, 31, 148, 4684, 1174, 1174, 1288, 8158, 8764, 8920, 2296, 2398, 2296, 3142, 3142, 3220, 4390, 4546, 4696, 2296, 2398, 2296, 3928, 3928, 3946, 4432, 4132, 7966, 8158, 8158, 8158, 8764, 8920, 8596, 11416, 8596, 7948, 7948, 7966, 8158, 8158] },
  { wordCode := 333732, rule := .chromograms #[3136, 4540, 76, 7, 7, 8032, 1162, 1096, 1096, 8752, 2518, 2518, 2212, 2278, 4498, 3136, 2518, 2518, 4540, 2518, 2518, 2212, 2278, 3994, 3994, 4006, 4354, 4378, 8032, 8182, 8182, 8182, 8752, 8698, 8698, 11464, 11464, 8020, 8020, 8032, 8182, 8182] },
  { wordCode := 333864, rule := .chromograms #[478, 2356, 4642, 64, 46, 2356, 8560, 1150, 1132, 8560, 2356, 2530, 2356, 8560, 2356, 4336, 2530, 2530, 4336, 2356, 2530, 2356, 4336, 3868, 3976, 3976, 4426, 4102, 8014, 8560, 11410, 8206, 8560, 8740, 8728, 11410, 8560, 7858, 8002, 8002, 8152, 8206] },
  { wordCode := 333690, rule := .chromograms #[484, 2398, 4684, 49, 31, 2398, 8608, 1180, 1174, 8608, 2398, 2548, 2398, 8608, 2398, 4402, 2548, 2548, 4402, 2398, 2548, 2398, 4402, 3946, 4024, 4024, 4432, 4120, 8050, 8608, 11416, 8230, 8608, 8770, 8764, 11416, 8608, 7966, 8044, 8044, 8158, 8230] },
  { wordCode := 333666, rule := .chromograms #[37, 1192, 2554, 8614, 2554, 2554, 4414, 4042, 4126, 8242, 8788, 8614, 8062, 8242] },
  { wordCode := 333708, rule := .chromograms #[490, 154, 49, 49, 79, 1294, 1180, 1180, 1198, 2296, 2398, 2398, 2398, 2296, 2548, 2548, 2548, 4132, 2296, 2398, 2398, 2398, 2296, 3922, 4024, 4432, 4432, 4132, 11416, 8596, 11416, 8248, 8596, 8770, 11416, 11416, 8596, 7942, 8044, 8158, 8158, 8158] },
  { wordCode := 333652, rule := .chromograms #[3172, 2422, 2692, 4570, 61, 2422, 2692, 3172, 1210, 2416, 2416, 2416, 922, 928, 2422, 2692, 3172, 4138, 2416, 2416, 2416, 2320, 2332, 4420, 4570, 4570, 4138, 4138, 7120, 7120, 7114, 7114, 6976, 7114, 7114, 6982, 6976, 8068, 8068, 8074, 8626, 8260] },
  { wordCode := 334236, rule := .chromograms #[4534, 2542, 11080, 11080, 11080, 2542, 7840, 7840, 7840, 2512, 2512, 2512, 2512, 2512, 2542, 4492, 4492, 4492, 2512, 2512, 2512, 2512, 2512, 4492, 4492, 4492, 4492, 4492, 11266, 7840, 7840, 7840, 11266, 11242, 11266, 11080, 11080, 8026, 8008, 8026, 7840, 7840] },
  { wordCode := 334344, rule := .chromograms #[4492, 2512, 11170, 11080, 11170, 2512, 7924, 7840, 7924, 2542, 2512, 2542, 2512, 2542, 2512, 4534, 4492, 4534, 2542, 2512, 2542, 2512, 2542, 4534, 4492, 4534, 4492, 4534, 11242, 7924, 7840, 7924, 11242, 11242, 11242, 11080, 11170, 8008, 8008, 8008, 7840, 7924] },
  { wordCode := 196934, rule := .chromograms #[8917, 8839, 8851, 8839, 8851] },
  { wordCode := 334470, rule := .chromograms #[7, 7, 262, 11272, 2212, 1096, 1492, 8032, 2212, 8752, 2644, 2212, 2524, 2596, 2644, 3424, 4660, 2212, 4540, 2644, 2212, 2524, 2596, 3994, 4660, 3916, 4504, 3916, 7930, 7930, 8032, 8020, 8752, 11110, 8860, 11110, 8752, 8020, 7870, 7930, 7870, 7930] },
  { wordCode := 334542, rule := .chromograms #[76, 76, 310, 11272, 2278, 1162, 1540, 8032, 2278, 2518, 2644, 2278, 2524, 2518, 3136, 3466, 4660, 2278, 2518, 2644, 2278, 2524, 2518, 4006, 4660, 3874, 4504, 3874, 7864, 7864, 8032, 8032, 8698, 11110, 8890, 11110, 8698, 7870, 7870, 7864, 7870, 7864] },
  { wordCode := 197008, rule := .chromograms #[8851, 8929, 8917, 8839, 8851] },
  { wordCode := 332868, rule := .chromograms #[367, 205, 205, 11704, 2806, 1666, 1666, 8398, 2806, 2746, 2758, 2758, 2752, 2746, 3604, 3604, 4810, 2806, 2746, 2758, 2758, 2752, 2746, 4204, 4810, 4192, 4798, 4192, 8338, 8374, 8398, 8398, 9058, 11686, 9076, 11686, 9058, 8380, 8380, 8338, 8380, 8374] },
  { wordCode := 332904, rule := .chromograms #[373, 211, 211, 11704, 2824, 1678, 1678, 8398, 2824, 9046, 2758, 2776, 2752, 2776, 2758, 3616, 4810, 2824, 4786, 2758, 2776, 2752, 2776, 4222, 4810, 4186, 4798, 4186, 8332, 8362, 8398, 8416, 9046, 11686, 9094, 11686, 9046, 8416, 8380, 8332, 8380, 8362] },
  { wordCode := 332724, rule := .chromograms #[11740, 8428, 2794, 2782, 4846, 2794, 2782, 4846, 4840, 8428, 11734, 11734, 8422, 8422] },
  { wordCode := 332922, rule := .chromograms #[415, 1780, 9106, 2854, 3712, 4858, 2854, 4234, 4888, 8350, 9106, 11668, 8434, 8350] },
  { wordCode := 332934, rule := .chromograms #[403, 1774, 2800, 2854, 2800, 2800, 2854, 4240, 4888, 11668, 9100, 11668, 8350, 8350] },
  { wordCode := 332910, rule := .chromograms #[2872, 2872, 4894, 11680, 8356] },
  { wordCode := 332598, rule := .chromograms #[343, 1864, 2968, 2968, 3820, 2968, 2968, 4942, 4252, 8464, 11794, 9160, 8470, 8464] },
  { wordCode := 70086, rule := .chromograms #[8598, 9294, 9258, 9294, 8598] },
  { wordCode := 70464, rule := .chromograms #[8652, 8652, 9378, 8688, 9348, 9378, 9396, 9360, 9348, 8688, 9378, 8652, 9360, 8652] },
  { wordCode := 202450, rule := .chromograms #[9607, 9265, 9421, 8491, 9265, 9421, 9607, 9421, 9265, 7927, 8137, 8137, 8329, 8491] },
  { wordCode := 202446, rule := .chromograms #[8485, 9613, 9271, 8131, 8485] },
  { wordCode := 329878, rule := .chromograms #[7630, 9514, 9454, 7570, 481, 9226, 9328, 9328, 9322, 9454, 9514, 9514, 1936, 9448, 7570, 7636, 7630, 7630, 9454, 7570, 9514, 7570, 9448, 9322, 9514, 9226, 9328, 9322, 7570, 7636, 7630, 7630, 9454, 7570, 9514, 7570, 9448, 9322, 9514, 9226, 9328, 9322] },
  { wordCode := 71226, rule := .chromograms #[9132, 9660, 9492, 8982, 9132] },
  { wordCode := 71250, rule := .chromograms #[9000, 9504, 9582, 9138, 9504, 9582, 9666, 9582, 9504, 8862, 8994, 8994, 9582, 9138] },
  { wordCode := 71424, rule := .chromograms #[9030, 9528, 9588, 9186, 9528, 9588, 9708, 9588, 9528, 8892, 9018, 9018, 9588, 9186] },
  { wordCode := 328660, rule := .chromograms #[7786, 7786, 9670, 7762, 529, 9700, 9670, 9610, 2044, 9670, 9658, 2044, 9658, 9670, 7762, 9670, 7786, 7786, 9670, 7762, 7786, 7762, 9670, 9598, 9628, 9700, 9610, 9604, 7762, 9670, 7786, 7786, 9670, 7762, 7786, 7762, 9670, 9598, 9628, 9700, 9610, 9604] },
  { wordCode := 202840, rule := .chromograms #[9337, 9673, 9709, 8041, 9367, 9337, 9337, 9709, 9673, 8041, 8011, 8425, 8011, 8041] },
  { wordCode := 328154, rule := .chromograms #[697, 2140, 2164, 2164, 9784, 9760, 7810, 9760, 9766, 9784, 9760, 7810, 9760, 9766] },
  { wordCode := 72030, rule := .chromograms #[8910, 8910, 9810, 9006, 9702, 9810, 9510, 9690, 9702, 9006, 9810, 8910, 9690, 8910] },
  { wordCode := 328228, rule := .chromograms #[7804, 9766, 9790, 2134, 9766, 7804, 7804, 9760, 9766, 9766, 7804, 7804, 9760, 9766] },
  { wordCode := 72226, rule := .chromograms #[7842, 9846] },
  { wordCode := 318174, rule := .chromograms #[13588, 9970, 5536, 5536, 5008, 5008, 5008, 5008, 5008, 9970, 13606, 13588, 9988, 9970] },
  { wordCode := 318276, rule := .chromograms #[5626, 5296, 5626, 9862, 5026, 5026, 5026, 5026, 5026, 13516, 13582, 9862, 9964, 9862] },
  { wordCode := 318318, rule := .chromograms #[931, 931, 931, 5068, 5632, 931, 931, 5290, 5302, 5614, 5554, 5632, 5554, 9844, 5032, 5032, 5020, 5032, 5032, 5020, 5032, 4996, 5032, 5032, 5020, 5032, 4996, 5032, 13564, 13498, 9874, 13498, 13552, 9874, 13564, 9844, 9844, 9922, 9874, 9946, 9844, 9844] },
  { wordCode := 318324, rule := .chromograms #[919, 919, 919, 5062, 5632, 919, 919, 5608, 5302, 1051, 5548, 5632, 5548, 9844, 5350, 5350, 5014, 5032, 5062, 5014, 5032, 5002, 5032, 5062, 5014, 5032, 5002, 5032, 9946, 9844, 9868, 13498, 9844, 9868, 13564, 9856, 9844, 9844, 9868, 9946, 9856, 9844] },
  { wordCode := 318252, rule := .chromograms #[13606, 9988, 5578, 5536, 5038, 5038, 5008, 5038, 5008, 9988, 13588, 13588, 9970, 9970] },
  { wordCode := 72334, rule := .chromograms #[7884, 9864] },
  { wordCode := 318462, rule := .chromograms #[13558, 5032, 5032, 2173, 2167, 5632, 9928, 5554, 5548, 5614, 5554, 5548, 1045, 1051, 5020, 5068, 5068, 5062, 5032, 5020, 5014, 5068, 5062, 5032, 5020, 5014, 5068, 5062, 9874, 9928, 13552, 13552, 13552, 9874, 9868, 13552, 13552, 9922, 9874, 9868, 9922, 9922] },
  { wordCode := 318558, rule := .chromograms #[9922, 5656, 2119, 973, 973, 1045, 9922, 973, 973, 1051, 1045, 1051, 1045, 1051, 4996, 5062, 5428, 5428, 5062, 4996, 4996, 5068, 5062, 5062, 4996, 4996, 5068, 5062, 9850, 9922, 9922, 9922, 9844, 9844, 9850, 13552, 13552, 9844, 9844, 9850, 9922, 9922] },
  { wordCode := 317988, rule := .chromograms #[5770, 5482, 5770, 9886, 5092, 5092, 5092, 5092, 5092, 13534, 13636, 9886, 10030, 9886] },
  { wordCode := 318006, rule := .chromograms #[5800, 5122, 5122, 13630, 10024] },
  { wordCode := 319248, rule := .chromograms #[5296, 5296, 5296, 9964, 5026, 5164, 5164, 5164, 5026, 13516, 13516, 9964, 9862, 9862] },
  { wordCode := 73342, rule := .chromograms #[8250, 8250, 8502, 8496, 8502, 8442, 8424, 8442, 8424, 10074, 10074, 9996, 9984, 9984] },
  { wordCode := 318582, rule := .chromograms #[5524, 5236, 5236, 13546, 9916] },
  { wordCode := 317742, rule := .chromograms #[13654, 10048, 5830, 5818, 5248, 5248, 5242, 5248, 5242, 10048, 13648, 13648, 10042, 10042] },
  { wordCode := 317604, rule := .chromograms #[5866, 5254, 5254, 13660, 10054] },
  { wordCode := 74170, rule := .chromograms #[8160, 8160, 8274, 9948, 9948] },
  { wordCode := 317316, rule := .chromograms #[13666, 10060, 5914, 5914, 5266, 5266, 5266, 5266, 5266, 10060, 13672, 13666, 10066, 10060] },
  { wordCode := 317328, rule := .chromograms #[13672, 10066, 5920, 5914, 5272, 5272, 5266, 5272, 5266, 10066, 13666, 13666, 10060, 10060] },
  { wordCode := 317148, rule := .chromograms #[6022, 5284, 5284, 13678, 10084] },
  { wordCode := 74416, rule := .chromograms #[10596, 9234, 9234, 10086, 10596] },
  { wordCode := 74460, rule := .chromograms #[8586, 9294, 9258, 10140, 10116] },
  { wordCode := 74506, rule := .chromograms #[9276, 10644, 10644, 10644, 9270, 9270, 9270, 9270, 9270, 10164, 10158, 10158, 10632, 10638] },
  { wordCode := 74518, rule := .chromograms #[9270, 10650, 10644, 10650, 9276, 9270, 9276, 9270, 9276, 10158, 10158, 10164, 10632, 10632] },
  { wordCode := 74608, rule := .chromograms #[10680, 9318, 9318, 10206, 10674] },
  { wordCode := 320546, rule := .chromograms #[5410, 10288, 10168, 10204, 5602, 5410, 5470, 5410, 5470, 10288, 10168, 10204, 10168, 10204] },
  { wordCode := 74794, rule := .chromograms #[9390, 10698, 10698, 10698, 9372, 9372, 9372, 9372, 9372, 10236, 10224, 10224, 10686, 10692] },
  { wordCode := 75106, rule := .chromograms #[10920, 9426, 9426, 10428, 10914] },
  { wordCode := 75154, rule := .chromograms #[10716, 10926, 9594, 9594, 9438, 9438, 9438, 9438, 9438, 10440, 10248, 10716, 10248, 10926] },
  { wordCode := 75352, rule := .chromograms #[8826, 8826, 9738, 8976, 9480, 9480, 9480, 9480, 9480, 10392, 10296, 10782, 10296, 10392] },
  { wordCode := 210054, rule := .chromograms #[14713, 10363, 10303, 10363, 10303] },
  { wordCode := 75466, rule := .chromograms #[10854, 11058, 9780, 9780, 9522, 9522, 9522, 9522, 9522, 10560, 10362, 10830, 10362, 11040] },
  { wordCode := 75814, rule := .chromograms #[9192, 9720, 10908, 10902, 10908, 8952, 9822, 9822, 9828, 8964, 8952, 8964, 8922, 8922, 9720, 9540, 9534, 9540, 9726, 9720, 9726, 9720, 9726, 10416, 10416, 10386, 9534, 9540, 10386, 10338, 10332, 10338, 10416, 10416, 10422, 10890, 10890, 10416, 10416, 10386, 10332, 10338] },
  { wordCode := 75856, rule := .chromograms #[10716, 10716, 9438, 9438, 9594, 9438, 9438, 9594, 9594, 10248, 10248, 10716, 10440, 10716] },
  { wordCode := 75898, rule := .chromograms #[10722, 9600, 9600, 10272, 10722] },
  { wordCode := 75994, rule := .chromograms #[8718, 9468, 10764, 9072, 9468, 9636, 10254, 9636, 9618, 10278, 10254, 10254, 10734, 10446] },
  { wordCode := 76432, rule := .chromograms #[8964, 8964, 9570, 10842, 8898, 10860, 9570, 10842, 9168, 9516, 9516, 9516, 9516, 9516, 9720, 9570, 9774, 9774, 9516, 9516, 9516, 9516, 9516, 9774, 9774, 9720, 9774, 9720, 10386, 10380, 10386, 10860, 10332, 10386, 10860, 10842, 10332, 10530, 10578, 10860, 10842, 10530] },
  { wordCode := 76438, rule := .chromograms #[10854, 10854, 9522, 9522, 9780, 9522, 9522, 9780, 9780, 10362, 10362, 10830, 10560, 10830] },
  { wordCode := 76540, rule := .chromograms #[11064, 8964, 8964, 8934, 8934, 10860, 9540, 9192, 9192, 9540, 9516, 9516, 10578, 9564, 9720, 9540, 9516, 9516, 9540, 9516, 9516, 10386, 9564, 9798, 9774, 9720, 10578, 9822, 10386, 10338, 10578, 11064, 10338, 10386, 10860, 10386, 10374, 10536, 10578, 10860, 10578, 10566] },
  { wordCode := 316060, rule := .chromograms #[6052, 6052, 6088, 6088, 1063, 6460, 6490, 6490, 1063, 6472, 6460, 6472, 1327, 1327, 6064, 6064, 6052, 6064, 6064, 6052, 6064, 6040, 6064, 6064, 6052, 6064, 6040, 6064, 13696, 13696, 13690, 10714, 13696, 13690, 13690, 10588, 10780, 10660, 13948, 13948, 10588, 13978] },
  { wordCode := 316036, rule := .chromograms #[6112, 6514, 6478, 6454, 6070, 6070, 6046, 6070, 6046, 13996, 13744, 10594, 13996, 10594] },
  { wordCode := 76604, rule := .chromograms #[8556, 8556, 10608, 10086, 10086] },
  { wordCode := 76626, rule := .chromograms #[8574, 10128] },
  { wordCode := 76638, rule := .chromograms #[8598, 8586, 8586, 10116, 10140] },
  { wordCode := 316090, rule := .chromograms #[6070, 6478, 6478, 6514, 6112, 6070, 6112, 6070, 6112, 13744, 13744, 10630, 13996, 10630] },
  { wordCode := 76694, rule := .chromograms #[8610, 8610, 8604, 8604, 8610, 8604, 8604, 10620, 10626, 10164, 10158, 10164, 10158, 10164] },
  { wordCode := 76706, rule := .chromograms #[8604, 8604, 8604, 8610, 8604, 8604, 8610, 10620, 10620, 10158, 10158, 10158, 10158, 10158] },
  { wordCode := 316358, rule := .chromograms #[1063, 6232, 1687, 1687, 1699, 1093, 1063, 1093, 1111, 1063, 1093, 1111, 1171, 1189, 6238, 6040, 6040, 6034, 6232, 6232, 6238, 6406, 6250, 6034, 6052, 6052, 6040, 6034, 10600, 10588, 10588, 10588, 10666, 10726, 10732, 10726, 10666, 10666, 13948, 10600, 10588, 10588] },
  { wordCode := 316372, rule := .chromograms #[6064, 6226, 6226, 6214, 6214, 6418, 6508, 6490, 6490, 6406, 6406, 1213, 1171, 1189, 6034, 6034, 6052, 6052, 6226, 6214, 6214, 6406, 6250, 6040, 6040, 6034, 6040, 6034, 13810, 13690, 13690, 10600, 13816, 13810, 10660, 10726, 10666, 10588, 10588, 10588, 10588, 10588] },
  { wordCode := 316368, rule := .chromograms #[6220, 6496, 1207, 1183, 6058, 6220, 6400, 6220, 6058, 10606, 10744, 10738, 13942, 10606] },
  { wordCode := 315772, rule := .chromograms #[6628, 6592, 6628, 14020, 6292, 6292, 6292, 6292, 6292, 13894, 13894, 14050, 14050, 14020] },
  { wordCode := 315832, rule := .chromograms #[6346, 6604, 6598, 1249, 6328, 6328, 6328, 6310, 6328, 13918, 13918, 10882, 14026, 14032] },
  { wordCode := 315724, rule := .chromograms #[6364, 6646, 6640, 6640, 6358, 6358, 6358, 6358, 6358, 14056, 13936, 10702, 14056, 10702] },
  { wordCode := 317002, rule := .chromograms #[6118, 6118, 6106, 6118, 1111, 6118, 6106, 6118, 1699, 6034, 6034, 1699, 6034, 6034, 6118, 6106, 6118, 6124, 6034, 6034, 6034, 6034, 6034, 6370, 6370, 6406, 6412, 6406, 13750, 13732, 13750, 10624, 13690, 13750, 10588, 10600, 10588, 10714, 10714, 10786, 10750, 10732] },
  { wordCode := 317030, rule := .chromograms #[1189, 1111, 1111, 1063, 1063, 1825, 1699, 1789, 1789, 1699, 6100, 6064, 6034, 6064, 6238, 6124, 6100, 6100, 6124, 6100, 6064, 6034, 6064, 6418, 6502, 6472, 6412, 6412, 10600, 10624, 10660, 10750, 10624, 10600, 13690, 10600, 10780, 10780, 10798, 10726, 10750, 10726] },
  { wordCode := 317008, rule := .chromograms #[6112, 6112, 6070, 6046, 6112, 6070, 6046, 6478, 6454, 13744, 13744, 10594, 13744, 10792] },
  { wordCode := 316974, rule := .chromograms #[1069, 1795, 13834, 6076, 6424, 6520, 6076, 6388, 6424, 10756, 13708, 10804, 13708, 10756] },
  { wordCode := 316960, rule := .chromograms #[6136, 6136, 6082, 6082, 6136, 6082, 6082, 6484, 6484, 13762, 13714, 13762, 10720, 10762] },
  { wordCode := 317074, rule := .chromograms #[6064, 6064, 6064, 6052, 1213, 6064, 6064, 6052, 1903, 6064, 6052, 6052, 1687, 1699, 6064, 6064, 6052, 6052, 6064, 6052, 6052, 6088, 6088, 6412, 6460, 6460, 6490, 6490, 13696, 13696, 13690, 10600, 13696, 13690, 10600, 10624, 10624, 10726, 10726, 10732, 10810, 13696] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk023 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 77610, rule := .chromograms #[8910, 10476, 10476, 10476, 8880, 8880, 8880, 8880, 8880, 10326, 10326, 10356, 10476, 10476] },
  { wordCode := 317062, rule := .chromograms #[6070, 6070, 6070, 6112, 6070, 6070, 6112, 6478, 6514, 13996, 13744, 10630, 13744, 10816] },
  { wordCode := 77654, rule := .chromograms #[8916, 9174, 9174, 10806, 9174, 8916, 10806, 8916, 10806, 10560, 10362, 10362, 10560, 10560] },
  { wordCode := 316906, rule := .chromograms #[6172, 6172, 6160, 1663, 6172, 6160, 6154, 6544, 6544, 13792, 13780, 13792, 10768, 13792] },
  { wordCode := 77724, rule := .chromograms #[8892, 9162, 9162, 9186, 8928, 8892, 8928, 8892, 8928, 10368, 10368, 10524, 10524, 10488] },
  { wordCode := 316888, rule := .chromograms #[6196, 6196, 6190, 1675, 6196, 6190, 6184, 6574, 6442, 13876, 13798, 10858, 13798, 10858] },
  { wordCode := 316498, rule := .chromograms #[6322, 6292, 6322, 13894, 6292, 6322, 6592, 6592, 6592, 13894, 13912, 13912, 13912, 13894] },
  { wordCode := 316492, rule := .chromograms #[6328, 6328, 6328, 1765, 6328, 6328, 6340, 6598, 6604, 13918, 13918, 13918, 10906, 13918] },
  { wordCode := 316594, rule := .chromograms #[6298, 6298, 6286, 6286, 6298, 6286, 6286, 6616, 6616, 13906, 13906, 10684, 13906, 10888] },
  { wordCode := 77990, rule := .chromograms #[8898, 9024, 9024, 9012, 9012, 9210, 9198, 9180, 9180, 10896, 10890, 10578, 9564, 9570, 9012, 8886, 8886, 8886, 9024, 9012, 9012, 10974, 10980, 8934, 8952, 8964, 8886, 8886, 10416, 10332, 10332, 10338, 10422, 10416, 10422, 10416, 10422, 10812, 10812, 10578, 10566, 10572] },
  { wordCode := 78086, rule := .chromograms #[8760, 8760, 10944, 10272, 10272] },
  { wordCode := 315364, rule := .chromograms #[6688, 6730, 6718, 6718, 6676, 6676, 6676, 6676, 6676, 14104, 14086, 14104, 10924, 10930] },
  { wordCode := 315408, rule := .chromograms #[1447, 1447, 14116, 6724, 6652, 6670, 6682, 6658, 6652, 10918, 14098, 10942, 14098, 10918] },
  { wordCode := 78212, rule := .chromograms #[8748, 8748, 8748, 10956, 8748, 8748, 10746, 9102, 10956, 10266, 10266, 10266, 10266, 10266] },
  { wordCode := 315076, rule := .chromograms #[6784, 6808, 6802, 6802, 6778, 6778, 6778, 6760, 6766, 14176, 14170, 14176, 10990, 10996] },
  { wordCode := 315088, rule := .chromograms #[6778, 6802, 6802, 6808, 6784, 6778, 6784, 6760, 6760, 14170, 14170, 14170, 10990, 10990] },
  { wordCode := 315130, rule := .chromograms #[6784, 6784, 6778, 6778, 6784, 6778, 6778, 6802, 6802, 14170, 14170, 14176, 11014, 11020] },
  { wordCode := 78578, rule := .chromograms #[8904, 8904, 8874, 8874, 8904, 8874, 8874, 10962, 10968, 10350, 10320, 10350, 10320, 10350] },
  { wordCode := 315142, rule := .chromograms #[6778, 6778, 6778, 6784, 6778, 6778, 6784, 6802, 6808, 14176, 14170, 14170, 11014, 11014] },
  { wordCode := 78626, rule := .chromograms #[8916, 8916, 8916, 11010, 8916, 8916, 10806, 9174, 11010, 10362, 10362, 10362, 10362, 10362] },
  { wordCode := 78642, rule := .chromograms #[8928, 8928, 8892, 8892, 8928, 8892, 8892, 9162, 9162, 10368, 10368, 10368, 10368, 10368] },
  { wordCode := 344464, rule := .chromograms #[12724, 3286, 3286, 2200, 2200, 2206, 4324, 4324, 2200, 2200, 2206, 2344, 2200, 2200, 2206, 2362, 2344, 232, 238, 232, 3454, 3370, 2200, 2200, 2206, 2344, 2200, 2200, 2206, 2362, 2344, 1462, 940, 940, 3040, 3040, 3040, 1060, 3040, 3040, 1060, 1072, 1060, 1234, 1228, 1060, 1072, 1060, 12970, 11164, 12688, 12712, 4, 11164, 12946, 12970, 4, 11134, 11152, 4, 10, 4, 11164, 11488, 11512, 4, 11134, 11152, 4, 10, 4, 94, 88, 4, 10, 4, 454, 454, 454, 4, 454, 454, 4, 10, 4, 94, 88, 4, 10, 4, 6898, 6898, 6898, 6898, 7126, 6898, 6898, 6898, 7846, 6898, 6898, 7990, 6940, 6946, 6898, 6898, 6898, 7192, 6898, 6898, 7126, 6940, 6946, 7078, 7078, 7054, 7180, 7054, 8542, 8542, 8542, 11074, 8542, 8542, 8812, 7846, 7846, 7996, 7990, 7990, 7846, 7846] },
  { wordCode := 344508, rule := .chromograms #[25, 25, 2278, 11110, 310, 1102, 2278, 7870, 1540, 1258, 1102, 1162, 1102, 1162, 652, 118, 25, 76, 118, 25, 76, 25, 76, 118, 25, 76, 25, 76, 7930, 7930, 8032, 8020, 8752, 11110, 8860, 11110, 8752, 8020, 7870, 7930, 7870, 7930] },
  { wordCode := 187044, rule := .chromograms #[12127, 11335, 11095, 11215, 11335, 11095, 11215, 11095, 11215, 11335, 11095, 11215, 11095, 11215] },
  { wordCode := 79214, rule := .chromograms #[11262, 11286, 11310, 11376, 11280, 11262, 11262, 11292, 11286, 11280, 11262, 11262, 11292, 11286] },
  { wordCode := 187142, rule := .chromograms #[11647, 11179, 11371, 12583, 11179, 11371, 11647, 11131, 11179, 11179, 11371, 11647, 11131, 11179] },
  { wordCode := 345424, rule := .chromograms #[6892, 3184, 2632, 2590, 2578, 304, 2260, 2260, 2206, 2200, 58, 2632, 2590, 2578, 58, 4528, 4522, 58, 10, 16, 2260, 2260, 2206, 2200, 1144, 2632, 2590, 2578, 1144, 3118, 3040, 1144, 1072, 1078, 3040, 3118, 3118, 1144, 3118, 3040, 1144, 1072, 1078, 1426, 1420, 1426, 1420, 1426, 11152, 11152, 12724, 12712, 1144, 11512, 12724, 12712, 1144, 12724, 11512, 304, 238, 244, 11164, 11164, 11152, 58, 11164, 11152, 58, 10, 16, 190, 184, 190, 184, 190, 454, 550, 550, 58, 616, 454, 58, 10, 16, 190, 184, 190, 184, 190, 7066, 7126, 7126, 6898, 6892, 7054, 7066, 7066, 7072, 7126, 7126, 7132, 7180, 7180, 6898, 6952, 6952, 6952, 6952, 6898, 6892, 6940, 6940, 6952, 6898, 6892, 6940, 6940, 8542, 8716, 8716, 7912, 8812, 8542, 7912, 7846, 7852, 11404, 8542, 8218, 8164, 8170] },
  { wordCode := 79724, rule := .chromograms #[11760, 11556, 11430, 11556, 11430] },
  { wordCode := 345412, rule := .chromograms #[4348, 4348, 4618, 11518, 28, 3130, 3130, 3052, 1090, 3130, 3052, 1090, 3388, 1486, 12730, 12730, 11518, 256, 11176, 11176, 28, 11518, 256, 634, 460, 28, 460, 256, 6904, 7144, 7144, 7198, 6958, 6904, 6958, 6904, 6958, 8830, 8548, 11098, 8548, 11458] },
  { wordCode := 79882, rule := .chromograms #[11592, 11502, 11538, 11832, 11502, 11538, 11592, 11496, 11502, 11502, 11538, 11592, 11496, 11502] },
  { wordCode := 80000, rule := .chromograms #[11472, 11580, 11682, 11688, 11580, 11472, 11466, 11574, 11574, 11580, 11472, 11466, 11574, 11574] },
  { wordCode := 187722, rule := .chromograms #[11323, 11839, 11671, 12139, 11113, 11323, 11323, 11671, 11839, 11113, 11323, 11323, 11671, 11839] },
  { wordCode := 187782, rule := .chromograms #[11389, 12205, 12127, 12205, 11335, 11335, 11383, 11767, 11767, 11335, 11335, 11383, 11767, 11767] },
  { wordCode := 343626, rule := .chromograms #[403, 1774, 1774, 1690, 1774, 403, 181, 403, 181, 8350, 9106, 11668, 8434, 8350] },
  { wordCode := 343968, rule := .chromograms #[391, 391, 2806, 11686, 205, 1720, 2806, 8380, 1666, 1756, 1720, 1666, 1720, 1708, 802, 445, 391, 367, 445, 391, 205, 391, 367, 445, 391, 205, 391, 367, 8332, 8362, 8398, 8416, 9046, 11686, 9094, 11686, 9046, 8416, 8380, 8332, 8380, 8362] },
  { wordCode := 80500, rule := .chromograms #[11466, 11574, 11574, 11574, 11688, 11772, 11772, 11682, 11688, 11580, 11472, 11466, 11574, 11574] },
  { wordCode := 80560, rule := .chromograms #[11526, 11610, 11610, 11598, 11748, 11856, 11850, 11736, 11742, 11598, 11520, 11520, 11610, 11598] },
  { wordCode := 80620, rule := .chromograms #[11592, 11592, 11628, 11634, 11808, 11808, 11730, 11706, 11706, 11496, 11544, 11592, 11628, 11592] },
  { wordCode := 343492, rule := .chromograms #[13174, 11824, 4906, 4906, 4918, 3718, 3796, 3796, 3802, 3724, 3718, 3724, 1798, 1798, 11824, 13168, 13168, 13174, 11818, 11818, 11824, 259, 259, 832, 826, 826, 259, 259, 7360, 7360, 7354, 7354, 7360, 7354, 7354, 7390, 7390, 9130, 9124, 9124, 11770, 11770] },
  { wordCode := 80746, rule := .chromograms #[11454, 11454, 11466, 11790, 11688, 11688, 11682, 11778, 11790, 11580, 11448, 11454, 11448, 11454] },
  { wordCode := 346760, rule := .chromograms #[10, 184, 184, 1228, 454, 454, 550, 616, 616, 454, 454, 616, 550, 550, 556, 616, 616, 622, 994, 7480, 898, 898, 1120, 1120, 1126, 994, 1120, 1120, 1126, 1228, 994, 1234, 994, 2602, 904, 904, 898, 904, 904, 898, 904, 898, 904, 904, 898, 904, 898, 904, 58, 58, 16, 10, 16, 190, 190, 184, 190, 190, 184, 190, 184, 190, 454, 550, 550, 556, 616, 454, 454, 898, 904, 904, 454, 454, 898, 904, 454, 550, 550, 58, 616, 454, 58, 10, 16, 190, 184, 190, 184, 190, 7450, 7438, 6922, 6910, 6910, 7090, 7090, 7078, 7078, 7090, 7078, 7078, 7438, 8170, 7438, 7450, 7450, 7486, 7450, 7438, 7486, 7438, 7486, 7486, 7486, 7474, 7486, 7480, 8542, 8716, 8716, 7912, 8812, 8542, 7912, 7846, 7852, 11404, 8542, 8218, 8164, 8170] },
  { wordCode := 346736, rule := .chromograms #[460, 460, 634, 634, 1000, 1138, 1138, 1000, 1000, 910, 910, 910, 910, 910, 28, 256, 460, 1000, 634, 460, 910, 460, 910, 634, 460, 28, 460, 256, 6928, 7168, 7444, 7444, 7456, 7444, 7444, 7492, 7492, 8830, 8548, 11098, 8548, 11458] },
  { wordCode := 347720, rule := .chromograms #[16, 16, 94, 94, 88, 88, 454, 454, 454, 454, 616, 454, 454, 454, 3442, 454, 454, 898, 898, 892, 1534, 904, 1126, 1120, 1120, 904, 1516, 1510, 1510, 892, 898, 898, 898, 892, 904, 988, 994, 994, 892, 898, 898, 898, 892, 988, 994, 994, 994, 988, 4, 4, 4, 10, 10, 4, 4, 10, 10, 94, 88, 88, 898, 892, 454, 454, 454, 994, 454, 454, 616, 898, 892, 622, 616, 616, 994, 988, 454, 454, 454, 4, 454, 454, 4, 10, 4, 94, 88, 4, 10, 4, 6892, 6892, 6892, 6910, 6922, 6892, 6892, 6910, 6922, 7498, 7486, 8746, 7486, 7846, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 7438, 8542, 8542, 8542, 11074, 8542, 8542, 8812, 7846, 7846, 7996, 7990, 7990, 7846, 7846] },
  { wordCode := 345776, rule := .chromograms #[271, 832, 832, 826, 826, 1042, 1840, 1834, 1834, 1036, 1036, 1036, 1036, 1036, 826, 259, 259, 259, 832, 826, 826, 1036, 1036, 832, 826, 826, 259, 259, 7522, 7372, 7372, 7378, 7528, 7522, 7528, 7522, 7528, 9130, 9124, 9124, 11770, 11770] },
  { wordCode := 189102, rule := .chromograms #[11185, 11653, 11653, 11653, 12439, 12589, 12157, 12271, 12157, 11143, 11143, 11185, 11653, 11653] },
  { wordCode := 342614, rule := .chromograms #[1966, 12130, 1996, 9448, 9448, 12130, 1966, 1966, 9448, 1996, 12130, 9226, 9328, 9322, 12130, 505, 805, 805, 505, 12130, 12130, 12220, 505, 505, 12130, 12130, 805, 505, 7570, 7636, 7630, 7630, 9454, 7570, 9514, 7570, 9448, 9322, 9514, 9226, 9328, 9322] },
  { wordCode := 342440, rule := .chromograms #[1990, 12202, 2002, 9472, 9466, 12202, 1990, 1990, 9466, 2002, 12202, 9310, 9370, 9370, 12202, 517, 793, 793, 517, 12202, 12202, 12250, 517, 517, 12202, 12202, 793, 517, 7588, 7654, 7648, 7648, 9466, 7588, 9550, 7588, 9466, 9376, 9550, 9310, 9370, 9370] },
  { wordCode := 189522, rule := .chromograms #[11353, 12139, 12265, 11839, 12139, 12265, 12475, 12265, 12139, 11113, 11323, 11323, 11671, 11839] },
  { wordCode := 188562, rule := .chromograms #[11419, 11563, 11623, 11641, 12277, 12307, 12325, 12283, 12277, 11641, 11587, 11419, 11587, 11563] },
  { wordCode := 188184, rule := .chromograms #[11551, 12391, 12343, 11455, 11551] },
  { wordCode := 84348, rule := .chromograms #[14808, 12504, 12354, 12504, 12354] },
  { wordCode := 341654, rule := .chromograms #[607, 607, 541, 2068, 2068, 12430, 2080, 2038, 2038, 2080, 2068, 2068, 9610, 2092, 12430, 583, 607, 2038, 541, 607, 2068, 607, 583, 541, 607, 12430, 607, 583, 7762, 9670, 7786, 7786, 9670, 7762, 7786, 7762, 9670, 9598, 9628, 9700, 9610, 9604] },
  { wordCode := 190128, rule := .chromograms #[11215, 11215, 11383, 11335, 12493, 12619, 12127, 12433, 12493, 11335, 11095, 11215, 11095, 11215] },
  { wordCode := 353212, rule := .chromograms #[3886, 4096, 4324, 2578, 2578, 2590, 4324, 4324, 2200, 2200, 2206, 2344, 2200, 2200, 2206, 2362, 2344, 232, 238, 232, 4108, 3892, 3886, 3892, 3904, 4108, 4096, 4108, 4342, 4096, 4108, 232, 238, 232, 3904, 4096, 4108, 4, 3886, 3892, 4, 10, 4, 94, 88, 4, 10, 4, 11512, 11152, 11134, 11152, 892, 11512, 11488, 11512, 988, 11488, 11512, 232, 238, 232, 11164, 11488, 11512, 4, 11134, 11152, 4, 10, 4, 94, 88, 4, 10, 4, 904, 988, 994, 994, 892, 898, 898, 898, 892, 988, 994, 994, 994, 988, 7192, 7126, 7192, 6952, 7192, 7054, 7054, 7192, 7192, 7138, 7126, 7126, 7180, 7186, 6898, 6898, 6898, 7192, 6898, 6898, 7126, 6940, 6946, 7078, 7078, 7054, 7180, 7054, 6898, 6898, 6898, 7192, 6898, 6898, 7126, 6940, 6946, 7078, 7078, 7054, 7180, 7054] },
  { wordCode := 178296, rule := .chromograms #[12841, 12655, 12763, 12655, 12763] },
  { wordCode := 354172, rule := .chromograms #[2260, 2260, 2260, 2206, 2200, 58, 2260, 2260, 2206, 2200, 58, 2632, 2590, 2578, 58, 4528, 4522, 58, 10, 16, 3904, 3904, 3904, 3892, 58, 3904, 3904, 3892, 58, 3904, 3892, 58, 10, 16, 3904, 3904, 3892, 58, 3904, 3892, 58, 10, 16, 190, 184, 190, 184, 190, 11164, 11164, 11164, 11152, 58, 11164, 11164, 11152, 58, 11164, 11152, 58, 10, 16, 11164, 11164, 11152, 58, 11164, 11152, 58, 10, 16, 190, 184, 190, 184, 190, 904, 904, 898, 904, 904, 898, 904, 898, 904, 904, 898, 904, 898, 904, 6952, 6898, 6952, 6952, 6952, 6898, 6952, 6952, 6952, 6952, 6898, 6892, 6940, 6940, 6898, 6952, 6952, 6952, 6952, 6898, 6892, 6940, 6940, 6952, 6898, 6892, 6940, 6940, 6898, 6952, 6952, 6952, 6952, 6898, 6892, 6940, 6940, 6952, 6898, 6892, 6940, 6940] },
  { wordCode := 354184, rule := .chromograms #[3886, 3316, 3286, 2200, 2200, 2206, 4588, 4324, 2200, 2200, 2206, 4522, 2578, 2578, 2536, 4522, 4522, 4, 10, 4, 3892, 3892, 3886, 3892, 3904, 3892, 3886, 3892, 3904, 3886, 3892, 4, 10, 4, 3892, 3886, 3892, 232, 3886, 3892, 4, 10, 4, 184, 184, 184, 184, 184, 11152, 11152, 11134, 11152, 892, 11152, 11134, 11152, 892, 11134, 11152, 4, 10, 4, 11152, 11134, 11152, 232, 11134, 11152, 4, 10, 4, 184, 184, 184, 184, 184, 898, 892, 898, 898, 892, 898, 898, 898, 892, 892, 898, 898, 898, 892, 7066, 7126, 7192, 6952, 7192, 7912, 7894, 6952, 7888, 6898, 6898, 7990, 6940, 6946, 7138, 7072, 6952, 7066, 6898, 6898, 7126, 6940, 6946, 6898, 6898, 11398, 6940, 6946, 7138, 7072, 6952, 7066, 6898, 6898, 7126, 6940, 6946, 6898, 6898, 12898, 6940, 6946] },
  { wordCode := 354160, rule := .chromograms #[4618, 4348, 4618, 11518, 28, 3910, 3910, 3910, 28, 3910, 3910, 28, 4114, 256, 11176, 11176, 11176, 28, 11176, 11176, 28, 11518, 256, 910, 910, 910, 910, 910, 6958, 6958, 6904, 6958, 6958, 6904, 6958, 6904, 6958, 6958, 6904, 6958, 6904, 6958] },
  { wordCode := 88630, rule := .chromograms #[13344, 13032, 12960, 12990, 14190, 13032, 12960, 12990, 13188, 12960, 12990, 13032, 12954, 12960, 13032, 12960, 12990, 13188, 12960, 12990, 13032, 12954, 12960, 12960, 12990, 13032, 12954, 12960, 13032, 12960, 12990, 13188, 12960, 12990, 13032, 12954, 12960, 12960, 12990, 13032, 12954, 12960] },
  { wordCode := 353752, rule := .chromograms #[4078, 4774, 2710, 2710, 2716, 4072, 4072, 4072, 4744, 4072, 4072, 424, 376, 376, 11350, 11350, 11350, 982, 11350, 11350, 424, 376, 376, 976, 976, 976, 976, 976, 8110, 8110, 8128, 8128, 7258, 7288, 11620, 7030, 7036, 7258, 7288, 13054, 7030, 7036] },
  { wordCode := 178974, rule := .chromograms #[12667, 12829, 12829, 13063, 13195] },
  { wordCode := 179034, rule := .chromograms #[12841, 12841, 12877, 13117, 13117] },
  { wordCode := 89308, rule := .chromograms #[13044, 13206, 13110, 13350, 14040, 12978, 13044, 13044, 13038, 13110, 13206, 13206, 13104, 13104, 12978, 13044, 13044, 13038, 13110, 13206, 13206, 13104, 13104, 13038, 13206, 12978, 13044, 13038, 12978, 13044, 13044, 13038, 13110, 13206, 13206, 13104, 13104, 13038, 13206, 12978, 13044, 13038] },
  { wordCode := 352240, rule := .chromograms #[11824, 11824, 4906, 4906, 4918, 4270, 4270, 4270, 4276, 4270, 4270, 4276, 259, 259, 11818, 11818, 11818, 11824, 11818, 11818, 11824, 259, 259, 1036, 1036, 1036, 1036, 1036, 7354, 7390, 7390, 7390, 7360, 7354, 7354, 7390, 7390, 7360, 7354, 7354, 7390, 7390] },
  { wordCode := 89494, rule := .chromograms #[13326, 13326, 13374, 13134, 13374, 12924, 12924, 12930, 14154, 13074, 13074, 14094, 13134, 14154, 12924, 12924, 12930, 13326, 13074, 13074, 13326, 13134, 13374, 13020, 12918, 12924, 12918, 12924, 12924, 12924, 12930, 13326, 13074, 13074, 13326, 13134, 13374, 13020, 12918, 12924, 12918, 12924] },
  { wordCode := 348884, rule := .chromograms #[1948, 1948, 865, 841, 841, 13282, 865, 469, 469, 781, 841, 841, 13240, 781, 12304, 865, 469, 469, 781, 841, 841, 1948, 781, 1924, 1948, 13282, 1948, 1924, 7642, 9244, 7684, 9268, 9244, 7642, 7642, 7684, 9358, 13222, 7642, 7642, 7684, 13222] },
  { wordCode := 90148, rule := .chromograms #[12804, 12852, 12882, 12888, 13842, 13284, 13296, 13302, 15054, 13290, 13284, 13284, 13302, 13296, 12888, 12870, 12804, 12804, 12870, 12852, 12852, 12888, 12882, 13290, 13284, 13284, 13302, 13296, 12888, 12870, 12804, 12804, 12870, 12852, 12852, 12888, 12882, 13290, 13284, 13284, 13302, 13296] },
  { wordCode := 90166, rule := .chromograms #[12768, 13272, 13314, 13530, 12822, 12768, 12768, 13314, 13272, 12822, 12768, 12768, 13314, 13272] },
  { wordCode := 90910, rule := .chromograms #[13116, 13386, 13332, 13614, 13008, 13116, 13116, 13332, 13386, 13008, 13116, 13116, 13332, 13386] },
  { wordCode := 90976, rule := .chromograms #[13056, 13152, 13152, 13152, 13152, 13422, 13404, 13404, 13404, 13344, 13362, 13632, 13638, 13632, 13032, 13032, 13056, 13056, 13152, 13152, 13152, 13152, 13152, 13344, 13362, 13422, 13404, 13404, 13032, 13032, 13056, 13056, 13152, 13152, 13152, 13152, 13152, 13344, 13362, 13422, 13404, 13404] },
  { wordCode := 348344, rule := .chromograms #[2038, 2068, 583, 607, 607, 13420, 583, 607, 607, 541, 607, 607, 13384, 541, 12430, 583, 607, 607, 541, 607, 607, 2068, 541, 2080, 2068, 13420, 2038, 2080, 7762, 9670, 7786, 9610, 9670, 7762, 7762, 7786, 9682, 13396, 7762, 7762, 7786, 13396] },
  { wordCode := 91714, rule := .chromograms #[12990, 12990, 13056, 13032, 14124, 13422, 13476, 13344, 15126, 13410, 13422, 13422, 13458, 13476, 13032, 12960, 12990, 12990, 12960, 12990, 12990, 13032, 13056, 13410, 13422, 13422, 13344, 13476, 13032, 12960, 12990, 12990, 12960, 12990, 12990, 13032, 13056, 13410, 13422, 13422, 13344, 13476] },
  { wordCode := 193576, rule := .chromograms #[12151, 12151, 12193, 12187, 12187, 11359, 12613, 12607, 12607, 11347, 11347, 11347, 11317, 11329, 12133, 12115, 12133, 12133, 12115, 12133, 12133, 12121, 12115, 12115, 12133, 12133, 12121, 12115, 13699, 13681, 13699, 13717, 13681, 13699, 13717, 13765, 13783, 14137, 14149, 14161, 14185, 14197] },
  { wordCode := 193486, rule := .chromograms #[12163, 12583, 11365, 11365, 12169, 12163, 12169, 12163, 12169, 13753, 13735, 13735, 14179, 14179] },
  { wordCode := 193630, rule := .chromograms #[12193, 12151, 11227, 11221, 11221, 11359, 11227, 11221, 11221, 11359, 11347, 11347, 12607, 12607, 12133, 12187, 12187, 12187, 12151, 12133, 12133, 12187, 12187, 12151, 12133, 12133, 12187, 12187, 13699, 13765, 13765, 13783, 13717, 13699, 13717, 13699, 13717, 14161, 14149, 14161, 14071, 14077] },
  { wordCode := 193642, rule := .chromograms #[11203, 11203, 11203, 11221, 11227, 11203, 11203, 11221, 11227, 11347, 11347, 11359, 12607, 12613, 12151, 12193, 12187, 12193, 12115, 12133, 12151, 12187, 12193, 12115, 12133, 12151, 12187, 12193, 13717, 13783, 13765, 13765, 13681, 13699, 13699, 13699, 13681, 14137, 14149, 14149, 14071, 14071] },
  { wordCode := 193240, rule := .chromograms #[12523, 12241, 12241, 13837, 14119] },
  { wordCode := 193360, rule := .chromograms #[12259, 12511, 11245, 11245, 12247, 12247, 12247, 12247, 12247, 13849, 13849, 13867, 14089, 14107] },
  { wordCode := 193698, rule := .chromograms #[11137, 12451, 12175, 13921, 14173] },
  { wordCode := 192828, rule := .chromograms #[11623, 11425, 11419, 11419, 12277, 12277, 12277, 12277, 12277, 14065, 14059, 14065, 14017, 14017] },
  { wordCode := 192522, rule := .chromograms #[11527, 12367, 12367, 13993, 13975] },
  { wordCode := 192622, rule := .chromograms #[12349, 12349, 12397, 13957, 13957] },
  { wordCode := 194196, rule := .chromograms #[11653, 11653, 11803, 11803, 12439, 12439, 12439, 12439, 12439, 13741, 13927, 13915, 13723, 13723] },
  { wordCode := 194548, rule := .chromograms #[12193, 12151, 12193, 12187, 12187, 12151, 12193, 12187, 12187, 12115, 12133, 12133, 12121, 12115, 12151, 12193, 12187, 12187, 12115, 12133, 12133, 12121, 12115, 12481, 12469, 12481, 12469, 12481, 13717, 13783, 13765, 13783, 13681, 13699, 13717, 13765, 13783, 13681, 13699, 13717, 13765, 13783] },
  { wordCode := 194458, rule := .chromograms #[12163, 12163, 12163, 12169, 12163, 12163, 12169, 12457, 12445, 13735, 13735, 13735, 13735, 13735] },
  { wordCode := 335720, rule := .chromograms #[1177, 1873, 1819, 1819, 1099, 1099, 1099, 1099, 1099, 13996, 13744, 10630, 13744, 10816] },
  { wordCode := 96710, rule := .chromograms #[12798, 13536, 13854, 12864, 12870, 13824, 12798, 12810, 12870, 12786, 12810, 13824, 12804, 12798, 13542, 13854, 13536, 13536, 13842, 13536, 13536, 13542, 13854, 13842, 13824, 13824, 13860, 13854, 12888, 12870, 12804, 12798, 12870, 12852, 12888, 12852, 12870, 12786, 12810, 12888, 12804, 12798] },
  { wordCode := 336692, rule := .chromograms #[1177, 1177, 1099, 1099, 1177, 1099, 1099, 1819, 1819, 13744, 13744, 10630, 13996, 10630] },
  { wordCode := 97496, rule := .chromograms #[13020, 13968, 13080, 13080, 13074, 13968, 13020, 13080, 13074, 13020, 13968, 12930, 13014, 13014, 13584, 13620, 13620, 13626, 14034, 13668, 13968, 13668, 14028, 14034, 13968, 13968, 14028, 14028, 12930, 13014, 13014, 13014, 13074, 13122, 13122, 13080, 13074, 13020, 13122, 12930, 13014, 13014] },
  { wordCode := 335220, rule := .chromograms #[1615, 6712, 14098, 1441, 1657, 1615, 1441, 1615, 1591, 10918, 14098, 10942, 14098, 10918] },
  { wordCode := 334760, rule := .chromograms #[1501, 1561, 1549, 1549, 1489, 1489, 1489, 1489, 1489, 14176, 14170, 14170, 11014, 11014] },
  { wordCode := 334772, rule := .chromograms #[1489, 1549, 1549, 1561, 1501, 1489, 1501, 1489, 1501, 14170, 14170, 14176, 11014, 11020] },
  { wordCode := 98276, rule := .chromograms #[13188, 13608, 14190, 12954, 12960, 14130, 13188, 12954, 12960, 13092, 13158, 14130, 13158, 13188, 13632, 14190, 13608, 13608, 14124, 13608, 13608, 13632, 14190, 13992, 14004, 14130, 13986, 13992, 13032, 12960, 12990, 13188, 12960, 12990, 13032, 12954, 12960, 12960, 12990, 13032, 12954, 12960] },
  { wordCode := 226368, rule := .chromograms #[6979, 6979, 7429, 14245, 10645, 11065, 14245, 14425, 14245, 15205, 15295, 14245, 14425, 14245] },
  { wordCode := 226254, rule := .chromograms #[11011, 7387, 7387, 14227, 11011, 11011, 14227, 14329, 14227, 15187, 14329, 14227, 14329, 14227] },
  { wordCode := 99050, rule := .chromograms #[11280, 11298, 11286, 11286, 11262, 11274, 11274, 11274, 11262, 14286, 14286, 14292, 14304, 14310] },
  { wordCode := 306082, rule := .chromograms #[2215, 2917, 2917, 3001, 6187, 2305, 2215, 2305, 2323, 2215, 2305, 2323, 2425, 2449, 6157, 6079, 6157, 5005, 6079, 6157, 5257, 5281, 5257, 5005, 5041, 5041, 5041, 5005, 14482, 14482, 14482, 14206, 14482, 14482, 14338, 14344, 14338, 14206, 14224, 14224, 14224, 14206] },
  { wordCode := 225408, rule := .chromograms #[15247, 14347, 7219, 7219, 14347, 10855, 10855, 14353, 14347, 14347, 15253, 15247, 14353, 14347] },
  { wordCode := 225420, rule := .chromograms #[15253, 14353, 7237, 7219, 14353, 10873, 10855, 14347, 14347, 14353, 15247, 15247, 14347, 14347] },
  { wordCode := 306124, rule := .chromograms #[2311, 6049, 6049, 6049, 6067, 2197, 2197, 2197, 6067, 2197, 2197, 2497, 2497, 2431, 6049, 6049, 6049, 5047, 6049, 6049, 6067, 6355, 6295, 4993, 4993, 4993, 4993, 4993, 14452, 14452, 14452, 14236, 14452, 14452, 14464, 14554, 14560, 14212, 14212, 14212, 14212, 14212] },
  { wordCode := 99698, rule := .chromograms #[11448, 11580, 11682, 11682, 11694, 11682, 11682, 11772, 11790, 14388, 14388, 14334, 14388, 14370] },
  { wordCode := 227340, rule := .chromograms #[7429, 6979, 6979, 14425, 10645, 10645, 14425, 14245, 14245, 15205, 15205, 14425, 14245, 14245] },
  { wordCode := 100442, rule := .chromograms #[11532, 11532, 11622, 14346, 14346] },
  { wordCode := 304180, rule := .chromograms #[2671, 2575, 2575, 6475, 6457, 6457, 5179, 5137, 5137, 14854, 14854, 14416, 14404, 14404] },
  { wordCode := 307622, rule := .chromograms #[5083, 5281, 2887, 2887, 2905, 5005, 5083, 5083, 5095, 14536, 5281, 14446, 5281, 14536, 5005, 5083, 5083, 5095, 6277, 5281, 6073, 5281, 6277, 6277, 6073, 6073, 6289, 6277, 14206, 14272, 14272, 14278, 14536, 14344, 14446, 14344, 14536, 14536, 14446, 14446, 14542, 14536] },
  { wordCode := 224340, rule := .chromograms #[10237, 14497, 10447, 10447, 14497, 10237, 10447, 10237, 14497, 14497, 14587, 14767, 14587, 14497] },
  { wordCode := 224514, rule := .chromograms #[10207, 14455, 10459, 10459, 14455, 10207, 10459, 10207, 14455, 14455, 14581, 14785, 14581, 14455] },
  { wordCode := 223554, rule := .chromograms #[10273, 14593, 14635, 10405, 14593, 10273, 10291, 10249, 10291, 14593, 14635, 14653, 14605, 14593] },
  { wordCode := 223176, rule := .chromograms #[10363, 10363, 10303, 14713, 14659] },
  { wordCode := 101844, rule := .chromograms #[12504, 12504, 12354, 14808, 14670] },
  { wordCode := 306662, rule := .chromograms #[2551, 5233, 6391, 5191, 2731, 5233, 14770, 5191, 5191, 14758, 5191, 5191, 5233, 14770, 5233, 6427, 5191, 5191, 6391, 5191, 5191, 5233, 6427, 6391, 6373, 6373, 6433, 6427, 14398, 14770, 14380, 14380, 14758, 14380, 14380, 14398, 14770, 14758, 14746, 14746, 14776, 14770] },
  { wordCode := 102238, rule := .chromograms #[11940, 12318, 12288, 12042, 12318, 12288, 12288, 12456, 12462, 14646, 14610, 14610, 14784, 14778] },
  { wordCode := 225120, rule := .chromograms #[10561, 14791, 14935, 10087, 14791, 10561, 10087, 10441, 10495, 14791, 14935, 14443, 14761, 14791] },
  { wordCode := 306284, rule := .chromograms #[2677, 14902, 5179, 5179, 6547, 5179, 5179, 6463, 6475, 14902, 14416, 14416, 14860, 14866] },
  { wordCode := 102878, rule := .chromograms #[11874, 11868, 11868, 14472, 14508] },
  { wordCode := 103910, rule := .chromograms #[11976, 11976, 12000, 11988, 11988, 12066, 12090, 12078, 12078, 12060, 12060, 12060, 12060, 12060, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 11970, 14694, 14682, 14694, 14700, 14682, 14694, 14700, 14724, 14730, 14892, 14904, 14910, 14940, 14946] },
  { wordCode := 103922, rule := .chromograms #[11970, 11970, 11988, 11988, 11994, 12060, 12078, 12078, 12084, 12066, 12060, 12066, 12060, 12066, 11976, 11976, 11970, 11976, 11976, 11970, 11976, 11970, 11976, 11976, 11970, 11976, 11970, 11976, 14700, 14700, 14694, 14694, 14700, 14694, 14694, 14724, 14724, 14910, 14904, 14904, 14940, 14940] },
  { wordCode := 103976, rule := .chromograms #[11988, 11970, 11970, 11970, 11976, 12060, 12060, 12060, 12066, 12060, 12060, 12066, 12078, 12084, 11976, 12000, 11988, 11994, 11970, 11970, 11976, 11988, 11994, 11970, 11970, 11976, 11988, 11994, 14700, 14730, 14724, 14724, 14682, 14694, 14694, 14694, 14682, 14892, 14904, 14904, 14832, 14832] },
  { wordCode := 104882, rule := .chromograms #[12000, 11976, 12000, 11988, 11988, 11976, 12000, 11988, 11988, 11970, 11970, 11970, 11970, 11970, 11976, 12000, 11988, 11988, 11970, 11970, 11970, 11970, 11970, 12060, 12060, 12060, 12060, 12060, 14700, 14730, 14724, 14730, 14682, 14694, 14700, 14724, 14730, 14682, 14694, 14700, 14724, 14730] },
  { wordCode := 311726, rule := .chromograms #[5041, 5041, 5005, 5005, 2425, 5041, 5005, 5005, 14476, 5257, 5257, 14476, 14476, 14446, 2293, 2209, 2293, 2293, 2209, 2293, 2293, 2215, 2209, 2209, 2293, 2293, 2215, 2209, 14482, 14482, 14668, 14230, 14668, 14620, 14230, 14668, 14278, 14446, 14476, 14476, 14476, 14446] },
  { wordCode := 310718, rule := .chromograms #[5143, 2665, 2587, 14872, 14872] },
  { wordCode := 235116, rule := .chromograms #[7429, 6979, 7429, 14245, 6979, 7429, 15205, 15295, 15205, 14245, 14425, 14425, 14425, 14245] },
  { wordCode := 234156, rule := .chromograms #[14347, 14347, 7219, 7219, 15247, 7219, 7219, 15253, 15247, 14353, 14353, 14347, 14353, 14347] },
  { wordCode := 234168, rule := .chromograms #[14353, 14353, 7237, 7219, 15253, 7237, 7219, 15247, 15247, 14347, 14347, 14347, 14347, 14347] },
  { wordCode := 236088, rule := .chromograms #[6979, 6979, 6979, 14425, 6979, 6979, 15295, 15205, 15205, 14245, 14245, 14245, 14245, 14245] },
  { wordCode := 142, rule := .chromograms #[54, 15311] },
  { wordCode := 265010, rule := .chromograms #[7312, 2836, 199, 15326, 2830, 766, 199, 15326, 7324, 199, 15326, 4228, 15326, 199, 766, 199, 15326, 13102, 199, 15326, 11728, 15326, 199, 199, 15326, 766, 15326, 199, 766, 199, 15326, 15712, 199, 15326, 2836, 15326, 199, 199, 15326, 766, 15326, 199] },
  { wordCode := 264768, rule := .chromograms #[2956, 4936, 15349, 229, 15730, 15349, 229, 15349, 229, 3808, 15349, 229, 15349, 229] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk024 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 266274, rule := .chromograms #[8980, 12838, 91, 15370, 1348, 91, 15370, 91, 15370, 1348, 91, 15370, 91, 15370] },
  { wordCode := 2336, rule := .chromograms #[492, 486, 486, 15389, 15395] },
  { wordCode := 2348, rule := .chromograms #[486, 486, 492, 15389, 15389] },
  { wordCode := 3296, rule := .chromograms #[864, 678, 15407, 678, 15407] },
  { wordCode := 4268, rule := .chromograms #[678, 678, 15407, 864, 15419] },
  { wordCode := 6710, rule := .chromograms #[15449, 15443, 15443, 900, 906] },
  { wordCode := 8642, rule := .chromograms #[15485, 15485, 990, 15563, 1032] },
  { wordCode := 275268, rule := .chromograms #[4492, 2512, 11170, 17168, 11266, 2512, 7924, 17024, 8026, 1156, 15584, 1264, 15646, 15634, 15320, 70, 15320, 124, 70, 15320, 124, 15346, 15340, 1156, 15584, 1264, 15646, 15634, 3208, 70, 15320, 124, 70, 15320, 124, 15346, 15340, 1156, 15584, 1264, 15646, 15634] },
  { wordCode := 256020, rule := .chromograms #[6814, 15649, 1459, 15649, 1459] },
  { wordCode := 275022, rule := .chromograms #[8980, 8098, 1348, 15664, 91, 91, 15370, 1348, 15664, 91, 91, 15370, 1348, 15664] },
  { wordCode := 257492, rule := .chromograms #[15589, 1759, 6304, 6298, 1255, 15589, 15589, 15698, 1759, 1255, 15589, 15589, 6304, 1759] },
  { wordCode := 274058, rule := .chromograms #[7306, 2842, 385, 15379, 4822, 1030, 1726, 15712, 17852, 1672, 15686, 3592, 15712, 1726, 766, 199, 15326, 13090, 199, 15326, 11716, 15379, 385, 1672, 15686, 1030, 15712, 1726, 766, 199, 15326, 15326, 199, 15326, 2842, 15379, 385, 1672, 15686, 1030, 15712, 1726] },
  { wordCode := 270160, rule := .chromograms #[9268, 7642, 7618, 7618, 1948, 9268, 9232, 9232, 1948, 9496, 9496, 1948, 1918, 1918, 12172, 12136, 12136, 1948, 12358, 12358, 1948, 769, 769, 2014, 2014, 1948, 1918, 1918, 16318, 16318, 16318, 1948, 16318, 16318, 1948, 769, 769, 2014, 2014, 1948, 1918, 1918] },
  { wordCode := 270136, rule := .chromograms #[7624, 9250, 9508, 1930, 12154, 12364, 1930, 2020, 1930, 16324, 16324, 1930, 2020, 1930] },
  { wordCode := 261414, rule := .chromograms #[5164, 5026, 5026, 1921, 15422, 15536, 1921, 2137, 1921, 5362, 5362, 1921, 2137, 1921] },
  { wordCode := 11396, rule := .chromograms #[1284, 1362, 1398, 15775, 1986] },
  { wordCode := 271134, rule := .chromograms #[12124, 12124, 12124, 15820, 451, 451, 15820, 15748, 15748, 451, 451, 15820, 15748, 15748] },
  { wordCode := 260454, rule := .chromograms #[5956, 2011, 5266, 5266, 2011, 15458, 15458, 2017, 2011, 2011, 5962, 5956, 2017, 2011] },
  { wordCode := 260466, rule := .chromograms #[5962, 2017, 5272, 5266, 2017, 15470, 15458, 2011, 2011, 2017, 5956, 5956, 2011, 2011] },
  { wordCode := 269176, rule := .chromograms #[7804, 9766, 9754, 9754, 12574, 12568, 643, 2134, 2140, 16378, 16378, 643, 2134, 2140] },
  { wordCode := 262386, rule := .chromograms #[5026, 5026, 5164, 2137, 15422, 15422, 2137, 1921, 1921, 5362, 5674, 2137, 1921, 1921] },
  { wordCode := 285330, rule := .chromograms #[79, 79, 202, 202, 202, 1198, 1438, 1438, 1438, 8764, 8920, 2296, 2398, 2296, 3484, 3340, 3340, 2296, 4546, 4696, 2296, 2398, 2296, 15922, 15922, 2296, 2398, 2296, 49, 49, 49, 79, 49, 49, 79, 202, 202, 1180, 1180, 1198, 1438, 1438] },
  { wordCode := 246094, rule := .chromograms #[6067, 2431, 15884, 2311, 6853, 2431, 6067, 2311, 6853, 6067, 2311, 2431, 2311, 6067, 2431, 15884, 2311, 15937, 15884, 2311, 2431, 2311, 15884, 15884, 2311, 2431, 2311, 15884, 2431, 6853, 2311, 5047, 6661, 2311, 2431, 2311, 6853, 6067, 2311, 2431, 2311, 6067] },
  { wordCode := 285576, rule := .chromograms #[154, 154, 4402, 2398, 322, 1294, 8908, 2398, 1552, 8608, 2398, 2548, 2398, 8608, 2548, 4684, 2398, 3922, 4402, 2398, 2548, 2398, 4402, 15892, 2398, 2548, 2398, 15892, 202, 79, 148, 148, 79, 148, 148, 202, 322, 1198, 1288, 1288, 1438, 1552] },
  { wordCode := 246254, rule := .chromograms #[2743, 5047, 4993, 4993, 2431, 2791, 2743, 2743, 2431, 6055, 6175, 2431, 2497, 2431, 2791, 2743, 2743, 2431, 15895, 15895, 2431, 2497, 2431, 15895, 15895, 2431, 2497, 2431, 2791, 2743, 2743, 2431, 6775, 6775, 2431, 2497, 2431, 6055, 6175, 2431, 2497, 2431] },
  { wordCode := 246832, rule := .chromograms #[2497, 6295, 6295, 6355, 2791, 2431, 2431, 2497, 2497, 6775, 6775, 2791, 2743, 2743, 2431, 2431, 2497, 2497, 15926, 15926, 2791, 2743, 2743, 15895, 15895, 2431, 2497, 2431, 2431, 2431, 2497, 2497, 6055, 6175, 2791, 2743, 2743, 6055, 6175, 2431, 2497, 2431] },
  { wordCode := 21450, rule := .chromograms #[15935, 2712, 2712, 2826, 15935] },
  { wordCode := 246992, rule := .chromograms #[4993, 2791, 15937, 2899, 6067, 2791, 6853, 2899, 6067, 6661, 2791, 2791, 2899, 6853, 2791, 15937, 2899, 15884, 15937, 2791, 2791, 2899, 15937, 15884, 2311, 2431, 2311, 15884, 2791, 6067, 2899, 4993, 6067, 2791, 2791, 2899, 6067, 6067, 2311, 2431, 2311, 6067] },
  { wordCode := 21696, rule := .chromograms #[15917, 15917, 2916, 2826, 2826] },
  { wordCode := 288264, rule := .chromograms #[31, 586, 4120, 3340, 490, 1288, 1552, 1438, 8044, 1198, 1288, 1288, 1438, 1552, 3220, 3946, 3340, 4024, 3946, 3220, 3220, 3340, 4120, 15892, 2398, 2548, 2398, 15892, 1294, 676, 49, 31, 490, 592, 586, 3340, 490, 1198, 1288, 1288, 1438, 1552] },
  { wordCode := 23020, rule := .chromograms #[3552, 15959, 3474, 15991, 15959, 3474, 3552, 3474, 15959, 15959, 3474, 3552, 3474, 15959] },
  { wordCode := 288510, rule := .chromograms #[676, 484, 484, 7948, 3484, 2296, 2296, 2398, 1570, 1180, 1180, 1198, 1438, 1438, 2296, 2296, 2398, 2398, 3928, 3928, 3484, 3340, 3340, 15922, 15922, 2296, 2398, 2296, 31, 31, 148, 676, 586, 682, 484, 3340, 484, 1180, 1180, 1198, 1438, 1438] },
  { wordCode := 23180, rule := .chromograms #[3690, 3684, 3684, 3552, 15967, 15967, 3552, 3582, 3552, 15967, 15967, 3552, 3582, 3552] },
  { wordCode := 244524, rule := .chromograms #[3247, 15980, 3607, 16507, 15980, 3247, 3247, 3607, 15980, 15980, 3247, 3247, 3607, 15980] },
  { wordCode := 23758, rule := .chromograms #[3552, 3552, 3582, 3582, 15989, 15989, 3690, 3684, 3684, 15967, 15967, 3552, 3582, 3552] },
  { wordCode := 23918, rule := .chromograms #[3690, 15991, 3786, 15959, 15991, 3690, 3690, 3786, 15991, 15959, 3474, 3552, 3474, 15959] },
  { wordCode := 244770, rule := .chromograms #[5329, 5329, 5515, 3829, 15944, 15944, 3829, 3607, 3607, 15944, 15944, 3829, 3607, 3607] },
  { wordCode := 239488, rule := .chromograms #[15118, 3967, 14986, 15004, 15016, 3967, 15100, 15118, 16040, 3931, 3949, 3967, 3871, 3871, 3967, 4297, 4309, 16040, 3931, 3949, 3967, 3871, 3871, 3931, 3949, 3967, 3871, 3871, 3967, 4297, 4309, 16040, 3931, 3949, 3967, 3871, 3871, 3931, 3949, 3967, 3871, 3871] },
  { wordCode := 26438, rule := .chromograms #[16055, 3954, 5028, 3954, 16055] },
  { wordCode := 238516, rule := .chromograms #[4141, 15160, 15160, 15166, 4135, 4135, 4141, 16124, 16124, 4135, 4135, 4141, 16124, 16124] },
  { wordCode := 27512, rule := .chromograms #[16133, 4152, 4194, 4194, 4152, 16133, 16133, 16163, 4152, 4152, 16133, 16133, 4194, 4152] },
  { wordCode := 240028, rule := .chromograms #[15070, 15070, 15070, 16220, 3979, 3979, 16220, 4189, 4189, 3979, 3979, 16220, 4189, 4189] },
  { wordCode := 240448, rule := .chromograms #[3949, 3949, 15016, 15004, 15004, 4309, 15016, 15004, 15004, 15016, 4309, 4309, 4249, 4255, 3967, 3967, 3949, 3949, 3967, 3949, 3949, 3871, 3877, 16196, 4309, 4309, 4249, 4255, 3967, 3967, 3949, 3949, 3967, 3949, 3949, 3871, 3877, 16196, 4309, 4309, 4249, 4255] },
  { wordCode := 240436, rule := .chromograms #[15022, 15022, 4315, 16238, 3961, 3961, 16046, 4315, 16190, 3961, 3961, 16046, 4315, 16190] },
  { wordCode := 240460, rule := .chromograms #[3967, 3967, 14986, 15004, 15016, 15004, 14986, 15004, 15016, 4297, 4309, 15016, 4249, 4249, 3949, 3931, 3949, 3967, 3931, 3949, 3967, 3871, 3871, 4297, 4309, 16184, 4249, 4249, 3949, 3931, 3949, 3967, 3931, 3949, 3967, 3871, 3871, 4297, 4309, 16184, 4249, 4249] },
  { wordCode := 240388, rule := .chromograms #[15034, 15034, 15034, 4279, 3883, 3883, 3913, 16178, 4279, 3883, 3883, 3913, 16178, 4279] },
  { wordCode := 28814, rule := .chromograms #[5520, 4428, 16265, 16597, 4428, 16265, 6252, 16265, 4428, 4428, 16265, 16273, 16265, 4428] },
  { wordCode := 293922, rule := .chromograms #[9028, 12862, 748, 16268, 17056, 4768, 16268, 4060, 16268, 1348, 91, 15370, 91, 15370] },
  { wordCode := 29360, rule := .chromograms #[16307, 4536, 5574, 16643, 4536, 16285, 16307, 6408, 4536, 4536, 16285, 16307, 16283, 4536] },
  { wordCode := 30044, rule := .chromograms #[16285, 4842, 5862, 5856, 4536, 16285, 16285, 6690, 4842, 4536, 16285, 16285, 16307, 4842] },
  { wordCode := 30684, rule := .chromograms #[4338, 16489, 5322, 4344, 4338] },
  { wordCode := 31108, rule := .chromograms #[16589, 5472, 5472, 4422, 4422] },
  { wordCode := 31426, rule := .chromograms #[16607, 16607, 5832, 5826, 5538, 5538, 5532, 5538, 5532, 4506, 4500, 4500, 4794, 4794] },
  { wordCode := 31492, rule := .chromograms #[16613, 16613, 5856, 5856, 5568, 5568, 5568, 5568, 5568, 4536, 4530, 4530, 4842, 4842] },
  { wordCode := 31644, rule := .chromograms #[5928, 5928, 16525, 4602, 4902] },
  { wordCode := 31860, rule := .chromograms #[4902, 5868, 16525, 4728, 4902] },
  { wordCode := 32628, rule := .chromograms #[4608, 4608, 4740, 4740, 16543, 16543, 5940, 5874, 5874, 4614, 4614, 4608, 4614, 4608] },
  { wordCode := 32950, rule := .chromograms #[16061, 16067, 5034, 5046, 5034] },
  { wordCode := 33074, rule := .chromograms #[16079, 4056, 4056, 5064, 16397] },
  { wordCode := 33106, rule := .chromograms #[16097, 16097, 16103, 5088, 5088] },
  { wordCode := 33316, rule := .chromograms #[16073, 16073, 5082, 5064, 5064] },
  { wordCode := 33400, rule := .chromograms #[16091, 16091, 5106, 5076, 5076] },
  { wordCode := 33416, rule := .chromograms #[16085, 4026, 4044, 4044, 4014, 4044, 4044, 5100, 4014, 5118, 5100, 16409, 5070, 5118] },
  { wordCode := 33956, rule := .chromograms #[16217, 4290, 4098, 4098, 4212, 4260, 4260, 5172, 4212, 5160, 5172, 16451, 5172, 5160] },
  { wordCode := 251680, rule := .chromograms #[2671, 14866, 14854, 14854, 6475, 6457, 6457, 5137, 16418, 6475, 2677, 2671, 5137, 16418] },
  { wordCode := 34138, rule := .chromograms #[16157, 16169, 16229, 5214, 16229, 16229, 5178, 16259, 5214, 5250, 5250, 5178, 5250, 5214] },
  { wordCode := 253334, rule := .chromograms #[5083, 5281, 2887, 2887, 2887, 5005, 5083, 5083, 5083, 14536, 5281, 5281, 14446, 16022, 5005, 5083, 5083, 5083, 6277, 5281, 5281, 6073, 6187, 16466, 5281, 5005, 5083, 5083, 2215, 2425, 2425, 2449, 6277, 3001, 5281, 2887, 2887, 16466, 5281, 5005, 5083, 5083] },
  { wordCode := 253394, rule := .chromograms #[5131, 2899, 2899, 3013, 3013, 5089, 5089, 5131, 5131, 14458, 14494, 14488, 14452, 14452, 5089, 5089, 5131, 5131, 6055, 6175, 6169, 6049, 6049, 16472, 16472, 5089, 5131, 5089, 2431, 2431, 2497, 5131, 6055, 6175, 2899, 3013, 2899, 16472, 16472, 5089, 5131, 5089] },
  { wordCode := 34562, rule := .chromograms #[4188, 16127, 16115, 16475, 5196] },
  { wordCode := 34574, rule := .chromograms #[16133, 4152, 4194, 5202, 4152, 16133, 16481, 16121, 5244, 5244, 16481, 16427, 5202, 5202] },
  { wordCode := 34634, rule := .chromograms #[16151, 4158, 4236, 5214, 4158, 16151, 16487, 16151, 5250, 5250, 16487, 16439, 5214, 5214] },
  { wordCode := 34694, rule := .chromograms #[16217, 4200, 4200, 4212, 4098, 4122, 4122, 4122, 4098, 5268, 5268, 16451, 5220, 5226] },
  { wordCode := 34820, rule := .chromograms #[16205, 16241, 4086, 4086, 4152, 4086, 4086, 4152, 4152, 5244, 5244, 16421, 5256, 16421] },
  { wordCode := 253624, rule := .chromograms #[2311, 6049, 6355, 6355, 6355, 14464, 14464, 14452, 14452, 14464, 14452, 14452, 14554, 14554, 6067, 6067, 6049, 6049, 6067, 6049, 6049, 6355, 6355, 16382, 4993, 5131, 4993, 16382, 2743, 6067, 3013, 2311, 6067, 2743, 3013, 2743, 6355, 16382, 4993, 5131, 4993, 16382] },
  { wordCode := 35040, rule := .chromograms #[4338, 16489, 5310, 6066, 5310] },
  { wordCode := 250338, rule := .chromograms #[3829, 3607, 3607, 3607, 16549, 16549, 5329, 5515, 5329, 15944, 15944, 3829, 3607, 3607] },
  { wordCode := 281246, rule := .chromograms #[5530, 15757, 15512, 15512, 5434, 5572, 5530, 5530, 5434, 15428, 15446, 5434, 5446, 5434, 5572, 5530, 5530, 5434, 16504, 16504, 5434, 5446, 5434, 16504, 16504, 5434, 5446, 5434, 5572, 5530, 5530, 5434, 16504, 16504, 5434, 5446, 5434, 15428, 15446, 5434, 5446, 5434] },
  { wordCode := 250560, rule := .chromograms #[15986, 5839, 16501, 3253, 15986] },
  { wordCode := 250584, rule := .chromograms #[5845, 16507, 5515, 15980, 16507, 5515, 5845, 5515, 16507, 15980, 3247, 3247, 3607, 15980] },
  { wordCode := 281824, rule := .chromograms #[5446, 18104, 18098, 18098, 5572, 5434, 5434, 5446, 5446, 16526, 16526, 5572, 5530, 5530, 5434, 5434, 5446, 5446, 16526, 16526, 5572, 5530, 5530, 16504, 16504, 5434, 5446, 5434, 5434, 5434, 5446, 5446, 15428, 15446, 5572, 5530, 5530, 15428, 15446, 5434, 5446, 5434] },
  { wordCode := 36258, rule := .chromograms #[5874, 16531, 4614, 4608, 16531, 5760, 5874, 5760, 16531, 6480, 5760, 5874, 5760, 6780] },
  { wordCode := 276426, rule := .chromograms #[10900, 6634, 16592, 1231, 15703] },
  { wordCode := 253834, rule := .chromograms #[14842, 16627, 6445, 16622, 16627, 6445, 16442, 6445, 16622, 16627, 6445, 16442, 6445, 16622] },
  { wordCode := 38792, rule := .chromograms #[16307, 4536, 5574, 5568, 4536, 16285, 16285, 6690, 4842, 5568, 16615, 16615, 5574, 5568] },
  { wordCode := 38826, rule := .chromograms #[4518, 4518, 16645, 6402, 16645] },
  { wordCode := 276244, rule := .chromograms #[16634, 6730, 16672, 1435, 6676, 16634, 6736, 16672, 6730, 1435, 15596, 6736, 15596, 1435] },
  { wordCode := 60198, rule := .chromograms #[7278, 16727, 7206, 16727, 7206] },
  { wordCode := 207346, rule := .chromograms #[7027, 16742, 7315, 17618, 10693, 16742, 7027, 7027, 7027, 7315, 16742, 16742, 10933, 7315, 16742, 7027, 7027, 7027, 7315, 16742, 16742, 16730, 7315, 7315, 16742, 16742, 7027, 7027, 16742, 7027, 7027, 7027, 7315, 16742, 16742, 16730, 7315, 7315, 16742, 16742, 7027, 7027] },
  { wordCode := 60936, rule := .chromograms #[7278, 7278, 7296, 16751, 16751] },
  { wordCode := 207592, rule := .chromograms #[7573, 7573, 7609, 7405, 7609, 16706, 16706, 7405, 17779, 7315, 7315, 17725, 7405, 17779, 16706, 16706, 7405, 7573, 7315, 7315, 7573, 7405, 7609, 7315, 7315, 16706, 7405, 16706, 16706, 16706, 7405, 7573, 7315, 7315, 7573, 7405, 7609, 7315, 7315, 16706, 7405, 16706] },
  { wordCode := 323742, rule := .chromograms #[313, 313, 868, 868, 3838, 4972, 3010, 15940, 3010, 8536, 9178, 9178, 13192, 13186] },
  { wordCode := 204540, rule := .chromograms #[10087, 10495, 10441, 16808, 15061, 16772, 15043, 16772, 15043, 16856, 10561, 10087, 10441, 10495] },
  { wordCode := 205278, rule := .chromograms #[10441, 10165, 10087, 10165, 15061, 15061, 15073, 16934, 16934, 16856, 10435, 10435, 10087, 10165] },
  { wordCode := 63004, rule := .chromograms #[16943, 16913, 16913, 16913, 16925, 16943, 16943, 16931, 16925, 16925, 16943, 16943, 16913, 16913] },
  { wordCode := 325914, rule := .chromograms #[8518, 4966, 295, 277, 3010, 4294, 3838, 15940, 3010, 11854, 8518, 8512, 13192, 13186] },
  { wordCode := 63570, rule := .chromograms #[7584, 16835, 16835, 7590, 7584] },
  { wordCode := 63582, rule := .chromograms #[7590, 16841, 16835, 7584, 7584] },
  { wordCode := 64530, rule := .chromograms #[16895, 16973, 7710, 7818, 7710] },
  { wordCode := 207974, rule := .chromograms #[9967, 9967, 9991, 7705, 16718, 16718, 7705, 7681, 7681, 16718, 16718, 7705, 7681, 7681] },
  { wordCode := 208388, rule := .chromograms #[9937, 9937, 10015, 7735, 16712, 16712, 7735, 7651, 7651, 16712, 16712, 7735, 7651, 7651] },
  { wordCode := 65502, rule := .chromograms #[16895, 16895, 7818, 7710, 7710] },
  { wordCode := 65804, rule := .chromograms #[17003, 7980, 17333, 7908, 17003] },
  { wordCode := 66110, rule := .chromograms #[8004, 8094, 17357, 7992, 8004] },
  { wordCode := 199400, rule := .chromograms #[17059, 8155, 17042, 9583, 8155, 17042, 17059, 17042, 8155, 8155, 17042, 17059, 17042, 8155] },
  { wordCode := 66920, rule := .chromograms #[8418, 8400, 8400, 8400, 8202, 8238, 17423, 8310, 8316, 8202, 8238, 8418, 8310, 8316] },
  { wordCode := 331884, rule := .chromograms #[724, 1348, 1348, 15664, 16268, 4060, 17056, 4060, 16268, 12862, 8098, 17056, 8098, 17056] },
  { wordCode := 200630, rule := .chromograms #[17035, 8419, 17072, 9343, 8017, 17035, 17035, 17072, 8419, 8017, 17035, 17035, 17072, 8419] },
  { wordCode := 201094, rule := .chromograms #[9313, 9313, 9301, 9283, 7837, 9313, 9301, 9283, 8449, 9409, 9403, 8449, 8461, 8449, 17012, 17006, 17012, 8449, 17006, 17012, 7837, 7861, 7837, 8347, 8347, 8347, 8347, 8347, 17012, 17006, 17012, 8449, 17006, 17012, 7837, 7861, 7837, 8347, 8347, 8347, 8347, 8347] },
  { wordCode := 67902, rule := .chromograms #[9300, 17579, 8586, 9294, 8586] },
  { wordCode := 68180, rule := .chromograms #[17609, 10692, 17129, 10704, 8664, 17129, 8682, 17129, 10668, 8664, 17129, 8682, 17129, 17147] },
  { wordCode := 198074, rule := .chromograms #[9073, 17102, 8671, 17102, 8671] },
  { wordCode := 198098, rule := .chromograms #[17108, 8665, 9085, 9079, 8665, 17108, 17108, 8659, 8659, 8665, 17108, 17108, 8659, 8659] },
  { wordCode := 198272, rule := .chromograms #[17090, 8629, 9097, 9097, 8629, 17090, 17090, 8641, 8629, 8629, 17090, 17090, 8641, 8629] },
  { wordCode := 68726, rule := .chromograms #[17201, 8748, 17741, 9642, 8748, 17201, 17201, 8754, 8748, 8748, 17201, 17201, 8754, 8748] },
  { wordCode := 197312, rule := .chromograms #[17156, 8761, 8797, 9001, 8707, 8797, 17156, 8773, 8761, 8707, 8797, 17156, 8773, 8761] },
  { wordCode := 68874, rule := .chromograms #[9552, 9036, 9690, 8880, 9036, 17675, 8880, 17675, 8880, 9036, 9810, 8880, 9690, 8880] },
  { wordCode := 68946, rule := .chromograms #[9510, 9006, 9690, 8910, 9006, 17675, 8910, 17675, 8910, 9006, 9810, 8910, 9690, 8910] },
  { wordCode := 69684, rule := .chromograms #[9036, 9552, 9510, 9552, 9006, 9006, 9036, 17777, 17777, 9006, 9006, 9036, 9510, 9552] },
  { wordCode := 69822, rule := .chromograms #[17663, 8868, 17765, 8868, 9546] },
  { wordCode := 69834, rule := .chromograms #[8880, 17687, 10476, 10476, 8910, 8880, 8880, 17777, 17777, 8910, 8880, 8880, 9510, 9552] },
  { wordCode := 70186, rule := .chromograms #[9270, 10650, 10644, 10644, 9276, 9270, 9270, 10158, 10158, 8604, 8604, 8610, 17105, 17099] },
  { wordCode := 70198, rule := .chromograms #[9276, 10644, 10644, 10650, 9270, 9270, 9276, 10158, 10164, 8610, 8604, 8604, 17105, 17105] },
  { wordCode := 202132, rule := .chromograms #[17282, 9343, 17078, 8419, 9343, 17239, 17282, 17239, 9343, 8017, 17035, 17035, 17072, 8419] },
  { wordCode := 70482, rule := .chromograms #[17615, 9330, 9408, 8634, 9408] },
  { wordCode := 70612, rule := .chromograms #[9390, 10698, 10698, 10704, 9372, 9372, 9390, 10224, 10236, 8664, 8646, 8646, 17147, 17147] },
  { wordCode := 70858, rule := .chromograms #[10758, 10758, 9456, 10464, 9642, 9456, 10266, 9456, 10266, 8748, 8748, 17165, 9102, 17207] },
  { wordCode := 70876, rule := .chromograms #[10722, 9600, 10272, 8760, 17195] },
  { wordCode := 70974, rule := .chromograms #[17705, 9732, 9576, 8814, 9576] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk025 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 71004, rule := .chromograms #[8862, 9150, 17711, 9486, 9666, 9762, 9486, 9582, 9486, 8850, 8850, 8862, 9582, 9150] },
  { wordCode := 71146, rule := .chromograms #[10854, 10854, 9522, 10560, 9780, 9522, 10362, 9522, 10362, 8916, 8916, 17183, 9174, 17213] },
  { wordCode := 71292, rule := .chromograms #[9684, 17687, 10476, 10476, 9702, 9684, 9684, 9510, 9552, 9006, 9006, 9036, 9510, 9552] },
  { wordCode := 71320, rule := .chromograms #[8934, 9720, 10908, 10902, 10902, 9204, 9564, 9564, 9564, 10872, 9204, 9204, 9156, 9168, 9516, 9564, 9564, 9564, 9726, 9720, 9720, 10416, 10416, 10416, 10416, 9516, 9564, 9564, 9012, 8922, 8922, 8934, 9012, 9012, 9024, 17219, 17225, 17225, 9204, 9204, 9156, 9168] },
  { wordCode := 201886, rule := .chromograms #[17066, 9583, 17275, 8155, 9463, 17258, 17258, 17275, 9583, 8155, 17042, 17059, 17042, 8155] },
  { wordCode := 202816, rule := .chromograms #[17239, 9703, 17030, 8017, 9343, 17239, 17239, 17282, 9703, 8017, 17035, 17072, 17030, 8017] },
  { wordCode := 72118, rule := .chromograms #[10854, 11058, 9780, 10362, 9522, 9522, 10362, 9780, 10560, 9174, 8916, 17183, 8916, 17183] },
  { wordCode := 72120, rule := .chromograms #[17699, 9696, 17309, 9834, 9696, 17309, 9834, 17287, 9696, 9696, 17185, 9834, 17185, 9696] },
  { wordCode := 72316, rule := .chromograms #[7932, 7968, 17021, 9876, 9876] },
  { wordCode := 72370, rule := .chromograms #[7932, 7932, 7920, 17339, 9876] },
  { wordCode := 213274, rule := .chromograms #[7825, 7585, 7585, 7585, 17546, 17756, 9853, 10063, 9853, 16760, 17756, 7825, 7585, 7585] },
  { wordCode := 72394, rule := .chromograms #[7908, 7908, 17003, 17333, 17333] },
  { wordCode := 72766, rule := .chromograms #[8064, 8064, 8028, 17363, 9900] },
  { wordCode := 72782, rule := .chromograms #[8022, 8046, 8076, 8070, 8034, 8022, 8070, 8022, 8034, 17375, 9894, 9912, 9894, 17375] },
  { wordCode := 73306, rule := .chromograms #[8190, 8478, 8394, 17417, 9972] },
  { wordCode := 212750, rule := .chromograms #[10771, 10771, 10021, 10009, 7291, 17390, 10021, 9931, 7645, 10021, 10009, 17390, 7741, 10021, 17390, 10021, 9931, 10771, 10021, 10009, 10771, 10009, 10021, 10021, 10009, 17390, 9931, 10021, 17390, 7267, 7099, 7099, 7267, 7243, 7243, 7663, 7291, 7621, 7663, 17390, 7663, 7645] },
  { wordCode := 73504, rule := .chromograms #[8250, 8304, 8442, 8424, 8442, 8442, 8424, 8502, 8496, 17405, 10074, 9996, 17405, 10032] },
  { wordCode := 213968, rule := .chromograms #[9889, 17426, 10051, 16736, 7597, 17318, 9889, 9889, 7597, 10051, 17426, 17426, 7789, 7789, 17318, 9889, 9889, 9889, 10051, 17426, 17426, 17557, 10051, 10051, 17426, 17318, 9889, 9889, 17318, 7015, 7015, 7789, 7339, 17426, 17426, 16736, 7597, 7597, 17426, 17318, 7789, 7597] },
  { wordCode := 74000, rule := .chromograms #[8220, 8298, 8424, 8424, 8298, 8220, 10080, 8220, 17405, 17405, 10080, 9984, 10032, 10032] },
  { wordCode := 74186, rule := .chromograms #[8376, 8466, 8172, 8166, 8286, 8172, 8166, 8286, 8280, 17399, 10068, 9960, 9966, 9960] },
  { wordCode := 211050, rule := .chromograms #[14971, 14971, 14845, 14845, 17539, 14845, 10507, 10207, 14455, 17539, 16820, 10507, 10207, 16964] },
  { wordCode := 74406, rule := .chromograms #[8562, 9240, 9222, 17555, 10092] },
  { wordCode := 74424, rule := .chromograms #[17549, 9240, 9240, 17555, 10104] },
  { wordCode := 210972, rule := .chromograms #[14899, 14767, 14899, 10111, 14767, 14899, 10111, 10237, 10111, 16790, 16790, 10111, 10237, 10111] },
  { wordCode := 320324, rule := .chromograms #[5380, 5380, 15524, 10138, 5464, 10276, 10366, 10138, 10144, 15847, 10138, 10144, 10138, 10144, 5584, 5710, 5380, 5386, 17470, 5380, 5386, 5380, 5386, 17470, 5380, 5386, 5380, 5386, 10276, 10366, 10138, 10144, 17470, 10138, 10144, 10138, 10144, 17470, 10138, 10144, 10138, 10144] },
  { wordCode := 320612, rule := .chromograms #[10246, 15542, 15542, 15560, 10180, 10270, 10246, 10246, 10180, 15865, 15865, 10180, 10186, 10180, 5572, 5530, 5530, 5434, 16504, 16504, 5434, 5446, 5434, 16504, 16504, 5434, 5446, 5434, 10270, 10246, 10246, 10180, 17434, 17446, 10180, 10186, 10180, 17434, 17446, 10180, 10186, 10180] },
  { wordCode := 320744, rule := .chromograms #[5560, 10090, 15769, 5308, 5308, 10090, 10264, 10258, 10264, 15853, 10090, 10090, 10174, 10174, 5308, 5566, 5560, 5566, 17458, 5308, 5308, 5422, 5422, 17458, 5308, 5308, 5422, 5422, 10090, 10264, 10258, 10264, 17458, 10090, 10090, 10174, 10174, 17458, 10090, 10090, 10174, 10174] },
  { wordCode := 74736, rule := .chromograms #[17153, 9354, 9354, 17603, 10188] },
  { wordCode := 320570, rule := .chromograms #[5584, 10162, 15781, 5404, 5398, 10162, 10282, 10276, 10282, 15847, 10162, 10156, 10192, 10192, 5404, 5590, 5584, 5590, 17470, 5404, 5398, 5458, 5458, 17470, 5404, 5398, 5458, 5458, 10162, 10282, 10276, 10282, 17470, 10162, 10156, 10192, 10192, 17470, 10162, 10156, 10192, 10192] },
  { wordCode := 211260, rule := .chromograms #[10435, 14791, 14749, 14749, 14791, 10435, 10435, 10087, 10165, 16856, 10435, 10435, 10087, 10165] },
  { wordCode := 211218, rule := .chromograms #[10447, 14875, 10237, 14767, 14497, 10237, 10447, 10237, 14497, 16802, 10237, 10447, 10237, 16952] },
  { wordCode := 211392, rule := .chromograms #[10459, 14923, 10207, 14785, 14455, 10207, 10459, 10207, 14455, 16778, 10207, 10459, 10207, 16964] },
  { wordCode := 210432, rule := .chromograms #[14635, 16904, 10273, 10291, 14593, 10273, 10291, 10249, 10291, 16916, 10273, 10291, 10249, 10291] },
  { wordCode := 75384, rule := .chromograms #[8982, 9492, 9492, 10500, 17753] },
  { wordCode := 321350, rule := .chromograms #[5650, 5650, 17500, 5572, 5572, 10270, 15745, 10318, 15757, 15745, 10270, 10270, 10318, 15787, 5572, 16540, 5650, 16430, 16540, 5572, 5572, 5650, 16540, 16490, 5368, 5434, 5368, 16490, 10270, 17500, 10318, 18146, 17482, 10270, 10270, 10318, 17500, 17482, 10126, 10180, 10126, 17500] },
  { wordCode := 75408, rule := .chromograms #[9486, 9744, 9000, 8994, 9504, 9486, 9504, 9486, 9504, 17657, 10308, 10512, 10308, 17759] },
  { wordCode := 210558, rule := .chromograms #[10273, 14593, 14635, 10399, 14593, 10273, 10273, 17503, 10399, 16916, 10273, 10273, 17503, 10399] },
  { wordCode := 75624, rule := .chromograms #[9582, 9744, 8850, 8844, 9504, 9582, 9666, 9582, 9504, 17657, 10410, 10470, 10410, 17759] },
  { wordCode := 319784, rule := .chromograms #[5854, 5854, 17518, 5812, 5812, 10432, 15835, 10456, 15799, 15835, 10432, 10432, 10456, 15841, 5812, 17518, 5854, 16454, 17512, 5812, 5812, 5854, 17518, 17512, 5812, 5812, 5854, 17518, 10432, 17518, 10456, 18158, 17512, 10432, 10432, 10456, 17518, 17512, 10432, 10432, 10456, 17518] },
  { wordCode := 211998, rule := .chromograms #[14935, 16808, 10561, 10495, 14791, 10561, 10087, 10441, 10495, 16856, 10561, 10087, 10441, 10495] },
  { wordCode := 76368, rule := .chromograms #[8862, 9150, 17711, 9504, 9666, 9762, 9504, 9672, 9666, 17645, 17645, 10512, 10470, 10470] },
  { wordCode := 315792, rule := .chromograms #[1315, 6634, 16592, 10900, 18196] },
  { wordCode := 77694, rule := .chromograms #[9552, 9552, 10482, 17687, 9006, 17675, 8910, 17675, 8910, 17717, 10548, 10326, 10482, 10518] },
  { wordCode := 78432, rule := .chromograms #[9006, 9006, 9006, 9036, 9006, 9006, 9036, 17777, 17777, 17717, 10476, 10476, 10326, 10356] },
  { wordCode := 315120, rule := .chromograms #[1579, 16688, 6814, 18220, 14140] },
  { wordCode := 216340, rule := .chromograms #[7813, 7777, 7777, 17785, 9901, 16706, 16706, 7405, 17779, 7315, 7315, 17725, 7405, 17779, 17576, 17576, 17785, 9865, 17732, 17732, 9865, 17767, 9901, 10693, 10615, 17576, 10615, 17576, 17576, 17576, 16700, 7813, 17732, 16700, 7777, 16700, 7777, 7315, 7315, 16706, 7405, 16706] },
  { wordCode := 78874, rule := .chromograms #[17803, 11154, 14262, 11154, 17801] },
  { wordCode := 186036, rule := .chromograms #[12415, 17839, 11431, 17839, 11431] },
  { wordCode := 345006, rule := .chromograms #[91, 1348, 1348, 15664, 1348, 91, 15370, 91, 15370, 12838, 9028, 17848, 8098, 17056] },
  { wordCode := 343742, rule := .chromograms #[7306, 2842, 385, 15379, 4834, 1030, 1726, 15712, 15712, 1672, 15686, 3598, 15686, 1672, 766, 199, 15326, 13102, 199, 15326, 11728, 15326, 199, 199, 15326, 766, 15326, 199, 12034, 7318, 17852, 7306, 7318, 17852, 7306, 17852, 11656, 8386, 17852, 9052, 17852, 11656] },
  { wordCode := 187508, rule := .chromograms #[17809, 11731, 12211, 18181, 11257, 17809, 17809, 11755, 11731, 11257, 17809, 17809, 11755, 11731] },
  { wordCode := 344042, rule := .chromograms #[2836, 2836, 199, 15326, 2812, 1024, 1024, 15686, 2812, 1672, 15686, 3592, 15712, 1726, 778, 385, 15379, 11716, 199, 15326, 11716, 15379, 385, 199, 15326, 778, 15379, 385, 12040, 9082, 17884, 8386, 7318, 17852, 7312, 17884, 7312, 8386, 17852, 9064, 17884, 8386] },
  { wordCode := 188946, rule := .chromograms #[13879, 12541, 17942, 11233, 17875] },
  { wordCode := 83788, rule := .chromograms #[11922, 12270, 17947, 18293, 12252, 17939, 12228, 17947, 12270, 11910, 17939, 11922, 17947, 12270] },
  { wordCode := 84034, rule := .chromograms #[17975, 12300, 12054, 18329, 12300, 17953, 17975, 12294, 12300, 11946, 17953, 17975, 12054, 12300] },
  { wordCode := 84718, rule := .chromograms #[17953, 11952, 11952, 11946, 12300, 17953, 17953, 12486, 12486, 11946, 17953, 17953, 11952, 11946] },
  { wordCode := 178256, rule := .chromograms #[13189, 12745, 17984, 12745, 17984] },
  { wordCode := 177296, rule := .chromograms #[12997, 12985, 12985, 17996, 18008] },
  { wordCode := 177288, rule := .chromograms #[18013, 12901] },
  { wordCode := 177308, rule := .chromograms #[12985, 12985, 12997, 17996, 17996] },
  { wordCode := 352790, rule := .chromograms #[7312, 2836, 199, 15326, 2812, 766, 199, 15326, 7318, 199, 15326, 4210, 15379, 385, 766, 199, 15326, 13090, 199, 15326, 11716, 15379, 385, 1672, 15686, 1030, 15712, 1726, 12034, 7318, 17852, 7312, 7318, 17852, 7312, 17884, 7312, 7318, 18026, 7312, 18040, 7312] },
  { wordCode := 179228, rule := .chromograms #[12745, 12745, 17984, 13189, 18044] },
  { wordCode := 89860, rule := .chromograms #[12714, 18059, 13266, 15006, 17989, 12714, 12714, 13266, 18059, 17989, 12714, 12714, 13266, 18059] },
  { wordCode := 90934, rule := .chromograms #[13026, 13338, 13374, 13122, 18191, 13338, 13374, 13392, 13398, 13374, 13338, 13338, 13620, 13374, 12930, 13014, 13014, 13026, 13074, 13122, 13338, 13122, 13374, 13374, 13338, 13338, 13392, 13374, 12930, 13014, 13014, 13026, 13074, 13122, 13338, 13122, 13374, 13374, 13338, 13338, 13392, 13374] },
  { wordCode := 183132, rule := .chromograms #[18061, 13423, 18086, 13279, 18061] },
  { wordCode := 193564, rule := .chromograms #[17792, 17792, 12571, 12547, 12145, 12145, 12109, 12145, 12109, 13705, 13705, 13771, 14155, 14191] },
  { wordCode := 192604, rule := .chromograms #[12361, 17834, 17822, 17822, 12355, 12355, 12355, 12331, 12337, 13963, 13963, 13969, 13999, 14011] },
  { wordCode := 194536, rule := .chromograms #[17792, 17894, 12145, 12109, 12571, 12145, 12109, 12571, 12547, 13771, 13705, 13771, 13705, 13771] },
  { wordCode := 340146, rule := .chromograms #[5296, 5296, 5626, 9862, 15422, 15536, 1921, 2137, 1921, 9862, 9964, 9964, 9964, 9862] },
  { wordCode := 95068, rule := .chromograms #[13008, 13332, 13332, 13332, 13944, 18209, 13566, 13662, 13566, 13128, 18209, 13008, 13332, 13332] },
  { wordCode := 341118, rule := .chromograms #[5626, 5296, 5296, 9964, 15422, 15422, 2137, 1921, 1921, 9862, 9862, 9862, 9862, 9862] },
  { wordCode := 341116, rule := .chromograms #[5368, 18122, 16526, 16526, 10270, 5320, 5320, 5320, 16490, 5320, 5320, 5446, 5446, 5434, 18098, 18098, 18098, 15757, 18098, 18098, 15877, 15865, 15865, 15739, 15739, 15739, 15739, 15739, 10336, 10318, 10336, 17314, 10246, 10246, 10246, 10246, 10246, 17314, 17314, 17314, 17314, 17314] },
  { wordCode := 339186, rule := .chromograms #[10060, 10060, 5914, 5914, 2011, 15458, 15458, 2017, 2011, 10066, 10066, 10060, 10066, 10060] },
  { wordCode := 339198, rule := .chromograms #[10066, 10066, 5920, 5914, 2017, 15470, 15458, 2011, 2011, 10060, 10060, 10060, 10060, 10060] },
  { wordCode := 339172, rule := .chromograms #[5968, 5932, 5932, 16544, 18164, 18164, 15823, 15811, 15811, 10510, 10534, 17410, 17410, 17410] },
  { wordCode := 335692, rule := .chromograms #[6070, 6070, 15716, 1819, 15572, 15572, 1099, 15572, 1099, 10594, 10594, 10630, 10792, 10816] },
  { wordCode := 335584, rule := .chromograms #[15734, 15578, 15578, 10654, 10876] },
  { wordCode := 336258, rule := .chromograms #[1231, 1231, 15703, 10900, 18196] },
  { wordCode := 334882, rule := .chromograms #[15680, 15614, 15614, 10954, 10984] },
  { wordCode := 97996, rule := .chromograms #[13074, 12930, 13014, 13014, 13014, 12930, 13014, 13014, 13014, 13074, 13122, 13122, 13080, 13074, 18215, 14028, 14028, 14028, 14100, 18215, 14142, 13572, 13578, 14034, 13968, 13968, 14028, 14028, 18215, 13020, 13080, 13074, 13020, 18215, 12930, 13014, 13014, 13020, 13122, 12930, 13014, 13014] },
  { wordCode := 196256, rule := .chromograms #[17870, 11257, 12529, 17809, 11257, 17809, 17809, 11755, 11731, 13819, 18181, 18181, 18200, 14131] },
  { wordCode := 334720, rule := .chromograms #[15656, 15626, 15626, 11002, 11026] },
  { wordCode := 305152, rule := .chromograms #[2311, 2311, 2197, 2197, 14236, 2311, 2197, 2197, 6067, 6775, 6775, 2791, 2743, 2743, 6169, 6049, 6049, 5047, 6775, 6775, 5047, 4993, 4993, 16472, 16472, 5047, 4993, 4993, 14488, 14452, 14452, 14236, 14674, 14674, 14236, 14212, 14212, 18248, 18248, 14236, 14212, 14212] },
  { wordCode := 305128, rule := .chromograms #[2203, 2203, 6781, 2749, 6061, 6781, 4999, 16478, 4999, 14470, 14680, 14218, 18254, 14218] },
  { wordCode := 305882, rule := .chromograms #[2791, 2791, 2743, 2743, 14488, 2791, 2743, 2743, 6661, 6055, 6175, 2311, 2197, 2197, 5089, 5089, 5131, 5131, 6055, 6175, 6169, 6049, 6049, 16472, 16472, 5089, 5131, 5089, 14284, 14284, 14290, 14290, 14458, 14494, 14488, 14452, 14452, 18248, 18248, 14284, 14290, 14284] },
  { wordCode := 99436, rule := .chromograms #[11454, 11454, 11466, 11466, 11688, 11688, 11688, 11688, 11688, 14370, 14334, 18271, 14334, 18271] },
  { wordCode := 99440, rule := .chromograms #[11682, 11790, 11472, 11466, 11694, 11682, 11688, 11682, 11688, 14388, 14388, 18271, 14406, 18271] },
  { wordCode := 306112, rule := .chromograms #[6067, 6067, 6067, 6049, 2899, 2497, 6067, 2197, 2197, 6067, 2197, 2197, 2497, 6355, 6067, 6067, 6049, 6049, 6067, 6049, 6049, 6355, 6355, 16382, 4993, 5131, 4993, 16382, 14464, 14464, 14452, 14452, 14464, 14452, 14452, 14554, 14554, 18224, 14212, 14290, 14212, 18224] },
  { wordCode := 306100, rule := .chromograms #[6061, 2203, 2203, 2491, 6061, 6061, 6361, 4999, 4999, 14470, 14470, 18254, 14218, 14218] },
  { wordCode := 99658, rule := .chromograms #[11568, 11766, 11766, 18247, 14382] },
  { wordCode := 99682, rule := .chromograms #[11466, 11574, 11574, 11586, 11688, 11772, 18253, 11772, 11790, 14370, 18253, 18253, 14388, 14370] },
  { wordCode := 100388, rule := .chromograms #[11460, 11460, 11568, 18247, 14400] },
  { wordCode := 304168, rule := .chromograms #[6475, 6475, 2575, 2575, 6475, 6457, 6457, 5137, 16418, 14866, 14854, 14854, 14404, 18272] },
  { wordCode := 224094, rule := .chromograms #[15025, 15169, 16862, 14473, 14767, 14899, 10111, 10237, 10111, 14767, 14899, 14473, 14587, 14473] },
  { wordCode := 101284, rule := .chromograms #[11916, 11916, 17939, 11904, 12252, 17939, 12228, 17947, 12270, 14568, 18293, 18293, 18301, 14586] },
  { wordCode := 102214, rule := .chromograms #[17975, 12300, 12054, 12048, 12300, 17953, 17953, 12486, 12486, 14628, 18307, 18307, 18329, 14790] },
  { wordCode := 225210, rule := .chromograms #[16826, 14743, 18344, 14953, 10429, 18344, 10579, 17521, 10429, 14743, 18344, 14953, 18331, 14743] },
  { wordCode := 102938, rule := .chromograms #[11886, 11886, 11880, 11880, 11886, 11880, 11880, 17909, 17915, 14490, 14490, 14496, 14520, 14526] },
  { wordCode := 227476, rule := .chromograms #[7693, 17665, 10819, 18260, 18355] },
  { wordCode := 103898, rule := .chromograms #[11982, 12072, 12072, 17927, 12072, 11982, 17921, 11982, 17921, 14688, 14688, 14712, 14898, 14934] },
  { wordCode := 311690, rule := .chromograms #[4999, 4999, 14500, 14470, 3007, 15889, 2203, 15889, 2203, 14470, 14680, 14296, 14500, 14470] },
  { wordCode := 310730, rule := .chromograms #[2677, 14902, 5137, 5137, 15919, 2677, 15919, 2575, 15914, 14866, 14854, 14416, 14854, 14866] },
  { wordCode := 312824, rule := .chromograms #[2665, 2665, 16004, 14872, 14410] },
  { wordCode := 230712, rule := .chromograms #[10087, 10087, 14761, 14749, 15073, 16772, 14959, 16772, 14959, 14749, 14935, 14527, 14761, 14749] },
  { wordCode := 230784, rule := .chromograms #[10165, 10165, 14761, 14791, 15061, 16772, 15043, 16772, 15043, 14791, 14935, 14443, 14761, 14791] },
  { wordCode := 229740, rule := .chromograms #[10303, 16874, 15079, 14713, 14713] },
  { wordCode := 231672, rule := .chromograms #[14935, 16808, 10435, 10435, 15043, 14959, 14959, 16934, 16934, 14527, 14443, 14527, 14443, 14527] },
  { wordCode := 231660, rule := .chromograms #[16766, 14965, 16940, 14521, 14521] },
  { wordCode := 296396, rule := .chromograms #[4843, 4969, 4333, 4327, 4801, 4843, 4903, 4843, 4801, 18392, 15196, 15232, 15196, 18392] },
  { wordCode := 297134, rule := .chromograms #[4843, 4789, 4789, 4801, 4333, 4411, 4405, 4327, 4327, 18398, 18398, 15232, 15238, 15232] },
  { wordCode := 234442, rule := .chromograms #[7261, 7117, 7261, 17719, 7117, 7261, 7651, 7651, 7651, 18265, 18265, 18265, 18265, 18265] },
  { wordCode := 116932, rule := .chromograms #[13326, 13326, 13374, 13134, 13134, 12924, 12924, 12930, 12930, 13074, 13074, 13074, 13074, 13074, 12924, 12924, 12930, 12930, 13074, 13074, 13074, 13074, 13074, 13374, 13326, 13392, 13326, 13446, 18409, 18409, 15138, 15138, 15132, 15132, 15132, 15132, 15132, 15264, 15240, 18409, 15240, 18409] },
  { wordCode := 1040, rule := .chromograms #[384, 270, 18427, 240, 252] },
  { wordCode := 1148, rule := .chromograms #[18437, 330, 396, 282, 294] },
  { wordCode := 263518, rule := .chromograms #[9268, 9532, 12238, 12238, 12244, 7618, 18736, 7696, 7696, 18736, 7618, 7696, 493, 18736, 12148, 12148, 12136, 1948, 12148, 12136, 2026, 493, 12148, 781, 769, 769, 493, 865, 16342, 16360, 16318, 1948, 16360, 16342, 2026, 493, 16360, 781, 769, 769, 493, 865] },
  { wordCode := 268122, rule := .chromograms #[262, 532, 3424, 3424, 3424, 130, 262, 262, 262, 574, 532, 532, 4354, 4378, 130, 262, 262, 262, 574, 532, 532, 18442, 18442, 118, 118, 130, 262, 262, 130, 262, 262, 262, 574, 532, 532, 3424, 3424, 118, 118, 130, 262, 262] },
  { wordCode := 263708, rule := .chromograms #[793, 13360, 517, 9568, 9562, 13264, 517, 793, 793, 517, 13360, 16330, 7714, 517, 12202, 517, 793, 793, 517, 12202, 12202, 12250, 517, 517, 12202, 12202, 793, 517, 18445, 517, 793, 793, 517, 18445, 18445, 16348, 517, 517, 16330, 16330, 793, 517] },
  { wordCode := 262546, rule := .chromograms #[9790, 18772, 7810, 7810, 12574, 12568, 2164, 679, 679, 16378, 16378, 2164, 679, 679] },
  { wordCode := 268860, rule := .chromograms #[3466, 3136, 574, 3214, 652, 76, 76, 130, 118, 574, 4660, 652, 4504, 574, 76, 76, 130, 118, 574, 18454, 652, 18454, 574, 118, 25, 76, 25, 76, 76, 76, 130, 118, 574, 3088, 652, 3088, 574, 118, 25, 76, 25, 76] },
  { wordCode := 264478, rule := .chromograms #[7684, 7684, 7684, 7696, 841, 7684, 7684, 7696, 469, 18760, 18760, 841, 865, 841, 12172, 12136, 12136, 469, 12358, 12358, 841, 865, 841, 469, 493, 493, 493, 469, 16318, 16318, 16318, 469, 16318, 16318, 841, 865, 841, 469, 493, 493, 493, 469] },
  { wordCode := 264466, rule := .chromograms #[7702, 7702, 19012, 871, 12154, 12364, 871, 487, 487, 16324, 16324, 871, 487, 487] },
  { wordCode := 259088, rule := .chromograms #[5710, 5584, 5710, 5698, 15847, 5584, 5710, 5380, 5386, 15452, 5380, 5386, 5380, 5386, 18469, 18469, 15434, 15871, 15452, 15434, 15847, 15434, 15847, 15452, 15434, 18469, 15434, 18469, 5386, 5386, 5398, 5710, 15452, 5716, 5584, 5698, 5710, 15452, 5380, 5386, 5380, 5386] },
  { wordCode := 272496, rule := .chromograms #[7, 532, 3424, 3424, 3424, 1270, 1492, 1492, 1492, 8752, 2518, 2518, 2212, 2278, 574, 76, 7, 7, 574, 532, 532, 18442, 18442, 1258, 1258, 1270, 1492, 1492, 574, 76, 7, 7, 574, 532, 532, 3424, 3424, 1258, 1258, 1270, 1492, 1492] },
  { wordCode := 273234, rule := .chromograms #[3136, 3136, 574, 3214, 652, 1162, 1162, 1270, 1258, 8752, 2644, 2212, 2524, 2596, 7, 262, 1270, 1258, 574, 18454, 652, 18454, 574, 1258, 1102, 1162, 1102, 1162, 7, 262, 1270, 1258, 574, 3088, 652, 3088, 574, 1258, 1102, 1162, 1102, 1162] },
  { wordCode := 9788, rule := .chromograms #[18493, 1818, 1500, 1818, 1608, 1500, 2124, 1470, 1482, 1608, 1500, 18481, 1470, 1482] },
  { wordCode := 9896, rule := .chromograms #[1758, 1872, 1560, 1872, 18491, 1560, 1620, 1512, 1524, 18491, 1560, 1620, 1512, 1524] },
  { wordCode := 10744, rule := .chromograms #[18481, 1482, 1470, 1482, 1722, 1800, 2016, 1800, 1818, 1608, 1500, 18481, 1470, 1482] },
  { wordCode := 10798, rule := .chromograms #[1620, 1524, 1512, 1524, 18503, 1836, 1758, 1836, 1872, 18491, 1560, 1620, 1512, 1524] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk026 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 11136, rule := .chromograms #[18509, 15581, 15581, 18515, 18509] },
  { wordCode := 260356, rule := .chromograms #[5932, 19444, 10528, 10528, 19604, 18170, 15494, 15823, 15817, 16552, 5938, 5932, 15823, 15817] },
  { wordCode := 12086, rule := .chromograms #[1758, 1872, 1518, 1512, 1746, 1758, 1836, 1758, 1746, 18533, 2100, 2100, 2148, 18533] },
  { wordCode := 260428, rule := .chromograms #[5968, 19444, 10504, 10504, 19604, 18164, 15476, 15811, 15817, 16552, 5974, 5968, 15811, 15817] },
  { wordCode := 271016, rule := .chromograms #[475, 475, 517, 517, 517, 12310, 12394, 2032, 9286, 2002, 2002, 9286, 2032, 9370, 12310, 12394, 475, 475, 517, 475, 475, 517, 517, 2002, 2002, 13252, 2032, 13252, 18457, 18457, 475, 475, 517, 475, 475, 517, 517, 2002, 2002, 18518, 2032, 18518] },
  { wordCode := 12232, rule := .chromograms #[1644, 1830, 1830, 18535, 2088] },
  { wordCode := 12244, rule := .chromograms #[1620, 1620, 1650, 1650, 1836, 1836, 1836, 1836, 1836, 18541, 18541, 2100, 2094, 2094] },
  { wordCode := 19784, rule := .chromograms #[18563, 2232] },
  { wordCode := 19824, rule := .chromograms #[18565, 2256] },
  { wordCode := 246592, rule := .chromograms #[6223, 2359, 16663, 2851, 2359, 18589, 2851, 18572, 2359, 2359, 16580, 2851, 16580, 2359] },
  { wordCode := 284502, rule := .chromograms #[229, 1792, 18596, 2956, 3730, 16310, 2956, 18596, 2956, 3730, 15349, 229, 15730, 1792] },
  { wordCode := 242858, rule := .chromograms #[5725, 18620, 3397, 18620, 3397] },
  { wordCode := 242898, rule := .chromograms #[5737, 18613, 3373, 18613, 3373] },
  { wordCode := 23518, rule := .chromograms #[3306, 18631, 3636, 18611, 3306] },
  { wordCode := 286638, rule := .chromograms #[17086, 2956, 15730, 1792, 2956, 17086, 3730, 18596, 2956, 355, 18646, 3730, 15730, 1792] },
  { wordCode := 283258, rule := .chromograms #[9508, 9250, 9508, 1930, 7702, 9508, 18748, 19012, 7702, 487, 487, 2020, 2020, 1930] },
  { wordCode := 283174, rule := .chromograms #[7714, 9550, 9550, 9550, 2032, 9310, 9286, 9286, 2032, 9550, 9550, 19528, 1954, 1954, 7588, 7582, 7588, 7588, 7582, 7588, 7588, 7588, 7582, 7582, 7588, 7588, 7588, 7582, 18445, 475, 859, 1954, 475, 18445, 18536, 16348, 2032, 2032, 18536, 18536, 1954, 1954] },
  { wordCode := 283150, rule := .chromograms #[9556, 9304, 9556, 1960, 7594, 7594, 7594, 7594, 7594, 853, 18439, 16354, 18542, 1960] },
  { wordCode := 284242, rule := .chromograms #[7696, 7696, 9244, 7618, 7618, 9244, 9244, 9232, 9232, 9244, 9232, 9232, 2014, 9358, 7618, 9244, 7696, 9232, 9244, 7618, 7618, 7696, 9358, 19018, 7618, 7618, 7696, 19018, 769, 865, 493, 493, 781, 769, 781, 769, 781, 1924, 1918, 1924, 1918, 1924] },
  { wordCode := 284134, rule := .chromograms #[7588, 7654, 7654, 7648, 7648, 9298, 9298, 9286, 9286, 9298, 9286, 9286, 9370, 9370, 7648, 7714, 7588, 7714, 7654, 7648, 7648, 7714, 7714, 7654, 7648, 7648, 7588, 7714, 18457, 18457, 859, 859, 793, 793, 793, 793, 793, 1990, 1954, 18518, 1954, 18518] },
  { wordCode := 282226, rule := .chromograms #[7804, 9766, 9790, 2140, 9766, 7804, 9790, 7804, 19036, 679, 643, 643, 2164, 2140] },
  { wordCode := 282190, rule := .chromograms #[7828, 9814, 9808, 9808, 7822, 7822, 7822, 7822, 7822, 18451, 667, 667, 2170, 18554] },
  { wordCode := 292952, rule := .chromograms #[1000, 910, 910, 3418, 3388, 28, 256, 256, 256, 52, 28, 28, 256, 256, 2194, 2572, 3076, 3052, 3418, 3076, 3052, 3418, 3388, 4618, 4348, 18656, 4348, 18668, 2194, 2572, 3076, 1000, 3418, 3076, 910, 3418, 910, 52, 28, 28, 256, 256] },
  { wordCode := 292866, rule := .chromograms #[490, 490, 490, 7948, 4120, 49, 490, 4432, 322, 18415, 49, 31, 202, 322, 2296, 4402, 2548, 2548, 18664, 3928, 3142, 3340, 4120, 18664, 3928, 3922, 4432, 4120, 31, 322, 202, 490, 18664, 682, 490, 3340, 490, 18415, 49, 31, 202, 322] },
  { wordCode := 291386, rule := .chromograms #[18640, 7348, 15332, 7516, 2848, 18640, 3706, 19138, 18680, 2848, 18640, 3706, 15332, 15373] },
  { wordCode := 291020, rule := .chromograms #[2878, 3742, 1036, 1036, 1036, 259, 259, 259, 259, 259, 259, 259, 259, 259, 3748, 2884, 2878, 2878, 3742, 3742, 3742, 3718, 3724, 4906, 4906, 4918, 18686, 18692, 3748, 2884, 2878, 2878, 3742, 3742, 3742, 1036, 1036, 259, 259, 259, 259, 259] },
  { wordCode := 291012, rule := .chromograms #[17086, 4936, 15349, 229, 2890, 17086, 3730, 16310, 4936, 229, 18646, 3730, 15349, 229] },
  { wordCode := 294220, rule := .chromograms #[2620, 2248, 2248, 2248, 2248, 6928, 7168, 4348, 7198, 4618, 4348, 6958, 4348, 6958, 3130, 3130, 2620, 2620, 2248, 2248, 2248, 2248, 2248, 4618, 4348, 18656, 4348, 18668, 28, 256, 256, 256, 52, 28, 28, 256, 256, 52, 28, 28, 256, 256] },
  { wordCode := 237236, rule := .chromograms #[18727, 4939, 4381, 4939, 4465, 4381, 15250, 4357, 19862, 4465, 4381, 18727, 4357, 4939] },
  { wordCode := 237344, rule := .chromograms #[4843, 4969, 4411, 4969, 18716, 4411, 18398, 4327, 4345, 18716, 4411, 4843, 4327, 4345] },
  { wordCode := 295192, rule := .chromograms #[2248, 2248, 2620, 2620, 2620, 6928, 6928, 4618, 6958, 4348, 4348, 6958, 4618, 7198, 3130, 3460, 2248, 2248, 2620, 2248, 2248, 2620, 2620, 4348, 4348, 18656, 4618, 18656, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28] },
  { wordCode := 293356, rule := .chromograms #[18584, 7510, 18964, 7330, 3634, 18584, 2788, 19138, 18680, 3634, 15332, 2788, 15332, 15373] },
  { wordCode := 293260, rule := .chromograms #[3796, 2926, 2926, 2926, 2926, 4906, 7378, 7372, 7372, 4918, 4906, 4906, 7390, 7396, 2938, 3802, 3796, 3796, 2926, 2926, 2926, 2926, 2926, 4918, 4906, 4906, 18686, 18686, 271, 271, 259, 271, 271, 259, 271, 259, 271, 271, 259, 271, 259, 271] },
  { wordCode := 293272, rule := .chromograms #[3802, 2938, 2938, 2926, 2938, 4918, 7372, 7372, 7378, 4906, 4906, 4918, 7390, 7390, 2926, 3796, 3796, 3802, 2938, 2926, 2938, 2926, 2938, 4906, 4906, 4918, 18686, 18692, 259, 259, 259, 259, 259, 259, 259, 259, 259, 259, 259, 259, 259, 259] },
  { wordCode := 251648, rule := .chromograms #[6583, 18338, 14896, 14890, 16622, 6583, 6577, 16412, 18811, 16622, 6583, 6577, 16412, 18811] },
  { wordCode := 33912, rule := .chromograms #[4134, 4308, 18817, 18871, 18817] },
  { wordCode := 278430, rule := .chromograms #[13654, 18830, 5248, 18856, 5830, 5248, 18856, 5248, 18830, 1009, 1009, 18856, 1999, 18830] },
  { wordCode := 35506, rule := .chromograms #[6228, 18893, 5496, 16577, 5496] },
  { wordCode := 280802, rule := .chromograms #[19382, 5788, 18902, 5488, 5788, 18902, 5488, 18902, 5488, 5788, 18902, 5488, 18902, 5488] },
  { wordCode := 249832, rule := .chromograms #[3301, 18908, 5791, 18625, 3301] },
  { wordCode := 281584, rule := .chromograms #[19426, 5488, 18916, 5788, 5488, 18916, 5788, 18902, 5488, 5488, 18916, 5788, 18902, 5488] },
  { wordCode := 254732, rule := .chromograms #[5011, 5263, 2965, 2965, 2965, 18931, 2965, 2287, 2965, 6331, 2287, 14350, 2221, 2245, 18931, 5023, 5011, 5011, 6331, 5263, 5263, 6085, 6109, 6331, 6139, 18931, 6085, 6109, 18931, 2245, 2221, 2245, 6331, 2923, 5263, 2923, 2965, 6331, 2287, 18931, 2221, 2245] },
  { wordCode := 254840, rule := .chromograms #[4993, 2791, 15937, 3013, 15937, 2791, 6853, 3013, 6853, 18920, 6175, 2431, 2197, 6067, 5089, 6853, 4993, 4993, 18920, 6175, 6295, 6049, 6067, 18920, 6175, 6295, 6049, 6067, 2431, 6853, 2197, 4993, 18920, 6175, 2791, 3013, 6067, 18920, 6175, 2431, 2197, 6067] },
  { wordCode := 275854, rule := .chromograms #[15602, 18940, 15668, 10978, 18940, 16652, 6742, 6694, 18940, 18476, 15608, 6742, 6694, 18488] },
  { wordCode := 39174, rule := .chromograms #[5940, 16531, 4614, 4608, 18925, 4614, 4608, 6726, 4914, 18925, 6474, 5940, 5760, 6780] },
  { wordCode := 205720, rule := .chromograms #[7729, 18949, 7129, 17648, 18949, 7129, 7729, 7129, 18949, 17648, 7129, 7729, 7129, 17648] },
  { wordCode := 60696, rule := .chromograms #[7074, 18955] },
  { wordCode := 205038, rule := .chromograms #[14803, 15049, 18991, 16844, 18991] },
  { wordCode := 63250, rule := .chromograms #[16877, 16877, 16945, 16997, 16925, 16925, 16997, 16945, 19027, 16925, 16871, 16877, 16871, 16877] },
  { wordCode := 208786, rule := .chromograms #[7405, 7315, 7315, 7315, 7315, 19033, 19033, 7573, 17324, 7609, 7573, 17324, 7573, 17324, 16706, 16706, 7405, 7405, 7315, 7315, 7315, 7315, 7315, 7609, 7573, 19033, 7573, 19033, 16706, 16706, 7405, 7405, 7315, 7315, 7315, 7315, 7315, 7609, 7573, 17324, 7573, 17324] },
  { wordCode := 322640, rule := .chromograms #[865, 2014, 9442, 469, 469, 13282, 865, 469, 469, 781, 841, 841, 13240, 781, 18754, 9526, 9238, 9232, 9442, 9502, 9496, 18754, 9442, 19018, 7642, 7642, 7684, 19018, 19186, 9526, 9238, 9232, 9442, 9502, 9496, 13354, 9442, 13222, 7642, 7642, 7684, 13222] },
  { wordCode := 208968, rule := .chromograms #[6931, 7381, 10681, 7327, 7333, 19267, 19267, 16982, 19267, 19267, 16982, 19267, 16976, 19267, 6985, 6901, 6901, 6931, 7363, 7327, 7333, 7303, 7303, 15223, 15211, 15223, 15175, 15223, 6985, 6901, 6901, 6931, 7363, 7327, 7333, 7303, 7303, 19267, 16982, 19267, 16976, 19267] },
  { wordCode := 322798, rule := .chromograms #[7618, 9496, 9496, 9496, 9496, 7642, 7618, 7618, 7618, 18760, 18760, 841, 865, 841, 7642, 7618, 7618, 7618, 9496, 9496, 9496, 9496, 9496, 19006, 19006, 7642, 7618, 7618, 7642, 7618, 7618, 7618, 9496, 9496, 9496, 9496, 9496, 13336, 13336, 7642, 7618, 7618] },
  { wordCode := 209008, rule := .chromograms #[16748, 7771, 19003, 9907, 7033, 16748, 16748, 19003, 7771, 7033, 16748, 16748, 17420, 7771] },
  { wordCode := 209032, rule := .chromograms #[7777, 19009, 7609, 16742, 10039, 19009, 7609, 7777, 7777, 7609, 19009, 17342, 9901, 7609, 16742, 7027, 7027, 7777, 7315, 16742, 19009, 16742, 7609, 7609, 19009, 19009, 7777, 7609, 16742, 7027, 7027, 7777, 7315, 16742, 17414, 16742, 7609, 7609, 17414, 17342, 7777, 7609] },
  { wordCode := 331346, rule := .chromograms #[634, 460, 460, 3418, 3388, 1138, 1528, 1486, 1486, 1090, 1090, 1090, 1090, 1090, 2194, 2194, 3418, 3388, 3076, 3076, 3052, 3076, 3052, 4348, 4348, 18656, 4618, 18656, 6904, 6904, 7906, 7492, 8212, 7906, 7444, 7906, 7444, 8212, 7906, 11098, 7906, 11098] },
  { wordCode := 332318, rule := .chromograms #[460, 460, 634, 3076, 3052, 1138, 1138, 1090, 1090, 1138, 1090, 1090, 1486, 1486, 2194, 2572, 3076, 3052, 3418, 3076, 3052, 3418, 3388, 4618, 4348, 18656, 4348, 18668, 6904, 7144, 8212, 7444, 7906, 7906, 7444, 8212, 7492, 7906, 7906, 11098, 8212, 11458] },
  { wordCode := 66650, rule := .chromograms #[19069, 8466, 8184, 8466, 8286, 8184, 10062, 8166, 17399, 8286, 8184, 19069, 8166, 8466] },
  { wordCode := 66758, rule := .chromograms #[8418, 8514, 8238, 8514, 19067, 8238, 17423, 8196, 8208, 19067, 8238, 8418, 8196, 8208] },
  { wordCode := 330386, rule := .chromograms #[2884, 3748, 832, 826, 826, 1804, 1840, 1834, 1834, 1798, 1798, 1798, 1798, 1798, 3748, 2884, 2878, 2878, 3742, 3742, 3742, 3718, 3724, 4906, 4906, 4918, 18686, 18692, 8482, 7360, 7354, 7354, 8488, 8482, 8482, 7522, 7528, 8488, 8482, 8482, 11770, 11770] },
  { wordCode := 330398, rule := .chromograms #[2878, 3742, 826, 826, 832, 1798, 1834, 1834, 1840, 1804, 1798, 1804, 1798, 1804, 3742, 2878, 2878, 2884, 3748, 3742, 3748, 3718, 3718, 4918, 4906, 4906, 18686, 18686, 8488, 7354, 7354, 7360, 8482, 8482, 8488, 7522, 7522, 8482, 8482, 8488, 11770, 11776] },
  { wordCode := 333570, rule := .chromograms #[310, 76, 76, 130, 130, 1162, 1162, 1270, 1270, 8752, 2644, 2278, 19090, 2278, 3136, 3136, 2644, 2644, 4540, 2644, 2278, 18712, 2278, 3994, 4660, 3874, 18712, 4378, 7864, 8182, 19052, 11464, 8752, 11110, 8890, 19090, 11464, 8020, 7870, 7864, 19052, 8182] },
  { wordCode := 333462, rule := .chromograms #[340, 79, 79, 148, 148, 1198, 1198, 1288, 1288, 19114, 8920, 2668, 2398, 8608, 3484, 4120, 3220, 2668, 18724, 4696, 2668, 2398, 4402, 18664, 3928, 3922, 4432, 4120, 7942, 8230, 8158, 8608, 19114, 8920, 8608, 11416, 8608, 19042, 7948, 7942, 8158, 8230] },
  { wordCode := 196972, rule := .chromograms #[19129, 8815, 17174, 8815, 17174] },
  { wordCode := 198844, rule := .chromograms #[19081, 19081, 9163, 17228, 9079, 9079, 17192, 9163, 17228, 8665, 8581, 17192, 8581, 17228] },
  { wordCode := 70084, rule := .chromograms #[19349, 19339, 19339, 17117, 17117] },
  { wordCode := 70366, rule := .chromograms #[8676, 8676, 19387, 8664, 9372, 19361, 19387, 19361, 9372, 8664, 17129, 8676, 19105, 8664] },
  { wordCode := 70402, rule := .chromograms #[17251, 19381, 17597, 17597, 19373, 17251, 17251, 17465, 19373, 17135, 17135, 17141, 19093, 19099] },
  { wordCode := 70498, rule := .chromograms #[19355, 19355, 19375, 17123, 17123] },
  { wordCode := 70912, rule := .chromograms #[19393, 10758, 9108, 10746, 9642, 19393, 19433, 19393, 10266, 8748, 17201, 19117, 9108, 17207] },
  { wordCode := 71022, rule := .chromograms #[8844, 9138, 17711, 9504, 19231, 9762, 9504, 9582, 9504, 19231, 8850, 8844, 9582, 9138] },
  { wordCode := 71130, rule := .chromograms #[8880, 17687, 10548, 9552, 9702, 9810, 9552, 19225, 9552, 9006, 9810, 8880, 19225, 9552] },
  { wordCode := 71596, rule := .chromograms #[19433, 8754, 8754, 8748, 9642, 19393, 19393, 19433, 9642, 8748, 17201, 17201, 8754, 8748] },
  { wordCode := 71974, rule := .chromograms #[17639, 19409, 17297, 17491, 19409, 17297, 17491, 17297, 19435, 17177, 17167, 17177, 17167, 17177] },
  { wordCode := 318726, rule := .chromograms #[1969, 19282, 949, 949, 18808, 5494, 5482, 5092, 18808, 19282, 10030, 19292, 10030, 19282] },
  { wordCode := 317496, rule := .chromograms #[5890, 1009, 1009, 19304, 5818, 5890, 18830, 5248, 18830, 19312, 10042, 19304, 10042, 19304] },
  { wordCode := 317796, rule := .chromograms #[1015, 1015, 5830, 19312, 5830, 5248, 18856, 5248, 18830, 19304, 13648, 19312, 10042, 19304] },
  { wordCode := 214154, rule := .chromograms #[10615, 10615, 10693, 10075, 10693, 17324, 17324, 10075, 18349, 10039, 10039, 18349, 10075, 19033, 17324, 17324, 10075, 10615, 10039, 10039, 10615, 10075, 10693, 10039, 10039, 17324, 10075, 17324, 16706, 16706, 7405, 7405, 7315, 7315, 7315, 7315, 7315, 7609, 7573, 17324, 7573, 17324] },
  { wordCode := 320414, rule := .chromograms #[15566, 15566, 19340, 15530, 15530, 15793, 17492, 15763, 15763, 19340, 19322, 19330, 17440, 17440, 17476, 16520, 16516, 16520, 18884, 19322, 18880, 16498, 16498, 18884, 19322, 17476, 16498, 16498, 17476, 17492, 17488, 17492, 19340, 19322, 18140, 17440, 17440, 19340, 19322, 17476, 17440, 17440] },
  { wordCode := 320234, rule := .chromograms #[5752, 18896, 5476, 18523, 18523, 19376, 19418, 10396, 15859, 10210, 15859, 15859, 10222, 18826, 19376, 19418, 5752, 18802, 5476, 18896, 19376, 5506, 18826, 5476, 18896, 19376, 5506, 19418, 19376, 19418, 10396, 19276, 10210, 19376, 19376, 10222, 19300, 10210, 18134, 19376, 10222, 19418] },
  { wordCode := 320950, rule := .chromograms #[18916, 10216, 19426, 10426, 5488, 18916, 5788, 18902, 5488, 10216, 19426, 10426, 19382, 10216] },
  { wordCode := 215366, rule := .chromograms #[9865, 17414, 10039, 16754, 7609, 19466, 17779, 11035, 17779, 10693, 17587, 18277, 6937, 16706, 19466, 17324, 9865, 9865, 10039, 17414, 17414, 17563, 10039, 10693, 17587, 19466, 11035, 17576, 19466, 16706, 6937, 7813, 7315, 16742, 17414, 16742, 7609, 7315, 16742, 19466, 6937, 16706] },
  { wordCode := 215474, rule := .chromograms #[9847, 10057, 18974, 10639, 18974, 17743, 11041, 10639, 11041, 19448, 10639, 19747, 6907, 6925, 17366, 9859, 9847, 9847, 19448, 10057, 10057, 10639, 17552, 19448, 10639, 17743, 10639, 11041, 17366, 6925, 6907, 6925, 19448, 7369, 7591, 7369, 17552, 19448, 7369, 17743, 6907, 6925] },
  { wordCode := 214468, rule := .chromograms #[7669, 18949, 7129, 17648, 19453, 17630, 10003, 10867, 17648, 19453, 17630, 7669, 7129, 17648] },
  { wordCode := 315028, rule := .chromograms #[15638, 16696, 6790, 19472, 11008] },
  { wordCode := 79772, rule := .chromograms #[19501, 11790, 11472, 11790, 11580, 11472, 19483, 11442, 11454, 11580, 11472, 19483, 11442, 11454] },
  { wordCode := 79880, rule := .chromograms #[11730, 11832, 11544, 11832, 19493, 11544, 11592, 11490, 11502, 19493, 11544, 11592, 11490, 11502] },
  { wordCode := 80728, rule := .chromograms #[19483, 11454, 11442, 11454, 11688, 11772, 18253, 11772, 11790, 11580, 11472, 19483, 11442, 11454] },
  { wordCode := 80782, rule := .chromograms #[11592, 11502, 11490, 11502, 19511, 11808, 11730, 11808, 11832, 19493, 11544, 11592, 11490, 11502] },
  { wordCode := 346704, rule := .chromograms #[1258, 652, 652, 652, 664, 2212, 1258, 1258, 1270, 2278, 2212, 2278, 2212, 2278, 25, 1258, 1258, 1270, 652, 652, 664, 18442, 18442, 76, 7, 7, 262, 262, 7864, 8182, 8182, 8182, 7930, 7864, 7864, 8182, 8182, 7930, 7864, 7864, 8182, 8182] },
  { wordCode := 346680, rule := .chromograms #[670, 1282, 2290, 2290, 1282, 670, 18448, 13, 274, 8188, 7882, 8188, 7882, 8188] },
  { wordCode := 347592, rule := .chromograms #[130, 3082, 3424, 8032, 8020, 1096, 1492, 8032, 2212, 8752, 2644, 2212, 2524, 2596, 76, 76, 130, 118, 574, 18454, 652, 18454, 574, 118, 25, 76, 25, 76, 8860, 8020, 7870, 7930, 8020, 7870, 7930, 7870, 7930, 8020, 7870, 7930, 7870, 7930] },
  { wordCode := 183736, rule := .chromograms #[19628, 11971] },
  { wordCode := 347664, rule := .chromograms #[3466, 3136, 3466, 8032, 8032, 1162, 1540, 8032, 2278, 2518, 2644, 2278, 2524, 2518, 7, 7, 130, 130, 532, 18454, 664, 18454, 532, 25, 25, 7, 25, 7, 7870, 7870, 7870, 7864, 7870, 7870, 7864, 7870, 7864, 7870, 7870, 7864, 7870, 7864] },
  { wordCode := 345720, rule := .chromograms #[3820, 1864, 2968, 2968, 235, 18460, 856, 253, 235, 8470, 8470, 8464, 8470, 8464] },
  { wordCode := 189120, rule := .chromograms #[11125, 11803, 11653, 12181, 19531, 12589, 12181, 12271, 12181, 19477, 11143, 11125, 11653, 11803] },
  { wordCode := 189228, rule := .chromograms #[11083, 11767, 19496, 12205, 12493, 12619, 12205, 19519, 12205, 11335, 11095, 11083, 19496, 11767] },
  { wordCode := 353994, rule := .chromograms #[118, 118, 118, 118, 130, 118, 118, 118, 130, 118, 118, 130, 262, 262, 118, 118, 118, 130, 118, 118, 130, 262, 262, 1258, 1258, 1270, 1492, 1492, 8752, 7930, 7864, 7864, 8752, 8698, 8698, 11464, 11464, 12778, 12778, 12784, 19544, 19544] },
  { wordCode := 88724, rule := .chromograms #[13566, 13068, 13962, 13008, 13068, 19543, 13008, 13116, 13008, 13068, 18209, 13008, 13116, 13008] },
  { wordCode := 88748, rule := .chromograms #[13080, 14142, 13020, 13572, 13578, 13968, 13020, 13080, 13074, 13020, 13968, 12930, 13014, 13014, 19555, 13020, 13080, 13074, 13020, 19555, 12930, 13014, 13014, 13020, 13122, 12930, 13014, 13014, 18215, 13020, 13080, 13074, 13020, 18215, 12930, 13014, 13014, 13020, 13122, 12930, 13014, 13014] },
  { wordCode := 89476, rule := .chromograms #[12924, 13338, 13374, 13122, 18191, 19549, 12924, 12912, 12924, 13074, 13122, 18403, 13122, 14154, 19549, 12924, 12912, 12924, 13074, 13122, 13338, 13122, 13374, 13020, 13122, 19549, 12912, 12924, 19549, 12924, 12912, 12924, 13074, 13122, 13338, 13122, 13374, 13020, 13122, 19549, 12912, 12924] },
  { wordCode := 89530, rule := .chromograms #[12960, 13362, 13992, 13152, 13992, 13032, 12960, 12948, 12960, 19565, 13152, 14130, 13152, 13188, 13032, 12960, 12948, 12960, 19565, 13152, 13362, 13152, 13188, 19565, 12996, 13032, 12948, 12960, 13032, 12960, 12948, 12960, 19565, 13152, 13362, 13152, 13188, 19565, 12996, 13032, 12948, 12960] },
  { wordCode := 90706, rule := .chromograms #[12912, 13122, 13074, 13338, 14028, 19585, 13446, 13338, 13446, 13374, 13338, 19843, 13338, 13578, 19549, 12924, 12912, 12912, 13074, 13122, 13122, 13080, 13074, 13374, 13338, 19585, 13338, 13446, 19549, 12924, 12912, 12912, 13074, 13122, 13122, 13080, 13074, 13374, 13338, 19585, 13338, 13446] },
  { wordCode := 349730, rule := .chromograms #[1954, 12202, 2002, 9472, 9466, 19576, 13252, 859, 859, 517, 13360, 16330, 7714, 517, 19528, 12394, 859, 859, 517, 12202, 12202, 12250, 517, 2002, 13360, 19576, 1954, 13252, 19166, 7714, 7588, 7714, 9466, 7588, 9550, 7588, 9466, 13324, 7588, 19576, 7588, 7714] },
  { wordCode := 337822, rule := .chromograms #[5398, 5716, 18548, 10348, 15871, 10144, 10144, 10132, 10144, 10144, 10132, 10144, 10132, 10144, 18548, 18548, 18110, 15871, 18128, 18110, 15847, 18110, 15847, 15524, 15524, 18469, 15554, 18469, 10276, 10366, 10162, 10366, 10282, 10276, 10276, 10348, 10366, 10144, 10132, 10144, 10132, 10144] },
  { wordCode := 193320, rule := .chromograms #[11305, 12541, 17942, 13813, 19675] },
  { wordCode := 338770, rule := .chromograms #[5470, 10150, 10360, 10360, 18116, 18506, 15548, 18463, 15548, 10168, 10168, 10150, 10168, 10150] },
  { wordCode := 194534, rule := .chromograms #[11761, 11077, 11077, 11101, 11119, 11665, 11665, 11665, 11677, 11665, 11665, 11677, 12121, 12115, 12559, 12481, 12469, 12481, 12121, 12121, 12115, 12121, 12115, 12499, 12499, 12499, 12469, 12481, 19688, 19670, 19658, 13801, 19652, 19652, 13801, 13765, 13783, 13897, 13885, 13801, 13765, 13783] },
  { wordCode := 340144, rule := .chromograms #[5368, 5368, 5320, 5320, 10186, 5368, 5320, 5320, 16490, 16526, 16526, 5572, 5530, 5530, 18104, 18098, 18098, 15757, 19598, 19598, 15757, 15512, 15512, 15865, 15865, 15757, 15739, 15739, 10318, 10318, 10336, 17314, 17434, 17446, 10180, 10186, 10180, 19618, 19618, 19252, 17314, 17314] },
  { wordCode := 340036, rule := .chromograms #[5398, 5398, 5374, 5374, 5386, 5398, 5374, 5374, 5386, 5692, 5692, 19258, 5584, 5584, 18512, 18110, 18110, 15871, 18152, 18512, 18512, 15524, 15751, 15871, 18512, 18512, 15751, 15751, 10162, 10138, 10162, 10366, 10138, 10162, 19288, 10192, 10198, 17386, 19262, 19258, 17350, 17350] },
  { wordCode := 95192, rule := .chromograms #[12996, 12996, 14124, 13608, 13056, 13632, 19625, 13608, 13476, 19625, 13608, 13632, 13344, 19625, 13632, 14190, 13608, 13980, 14124, 13608, 13632, 13608, 14124, 19625, 13608, 13632, 13608, 19625, 13032, 12960, 12990, 12990, 12960, 12990, 12990, 13032, 13056, 13410, 13422, 13422, 13344, 13476] },
  { wordCode := 97268, rule := .chromograms #[13572, 13668, 19567, 13140, 13374, 19681, 14154, 13140, 14154, 13020, 13968, 19549, 12912, 12924, 19681, 13578, 13572, 13572, 14034, 13668, 13668, 13950, 18191, 14034, 13968, 19681, 13950, 14154, 19549, 12924, 12912, 12924, 13074, 13122, 13338, 13122, 13374, 13020, 13122, 19549, 12912, 12924] },
  { wordCode := 97376, rule := .chromograms #[13596, 19643, 13188, 13188, 13188, 14130, 13188, 12996, 13188, 19667, 12996, 13032, 12948, 12960, 13632, 14190, 13596, 13596, 19667, 14010, 19643, 13980, 13992, 19667, 14010, 14130, 13980, 13992, 13032, 12960, 12948, 12960, 19565, 13152, 13362, 13152, 13188, 19565, 12996, 13032, 12948, 12960] },
  { wordCode := 196290, rule := .chromograms #[11233, 11233, 17875, 13813, 19675] },
  { wordCode := 335126, rule := .chromograms #[6748, 15620, 15673, 19462, 10954] },
  { wordCode := 98616, rule := .chromograms #[19697, 11160, 11160, 19703, 19697] },
  { wordCode := 99576, rule := .chromograms #[11508, 11814, 19727, 19757, 19727] },
  { wordCode := 225432, rule := .chromograms #[7153, 10795, 19711, 19867, 19711] },
  { wordCode := 225774, rule := .chromograms #[7069, 10729, 19706, 19856, 19706] },
  { wordCode := 305642, rule := .chromograms #[2851, 2851, 16580, 2419, 5065, 16580, 6271, 18847, 5065, 14326, 18296, 18296, 19744, 14326] },
  { wordCode := 100548, rule := .chromograms #[11508, 11508, 19757, 19727, 19727] },
  { wordCode := 224112, rule := .chromograms #[14899, 15145, 16862, 10537, 19771, 14899, 10537, 10237, 14497, 19771, 14899, 14497, 14587, 14497] },
  { wordCode := 224220, rule := .chromograms #[14935, 16808, 10561, 10561, 14791, 10561, 10165, 19765, 10165, 14791, 14935, 14527, 19765, 14527] },
  { wordCode := 227500, rule := .chromograms #[7201, 19015, 7699, 7699, 17672, 17660, 9985, 10825, 17672, 19724, 19724, 19730, 18361, 19795] },
  { wordCode := 229420, rule := .chromograms #[7033, 7807, 19003, 9907, 17569, 17774, 9907, 17581, 11029, 18284, 19694, 18235, 19783, 18373] },
  { wordCode := 222870, rule := .chromograms #[7933, 7933, 7885, 7885, 7933, 7885, 7885, 8479, 8479, 19802, 18380, 18386, 18380, 19802] },
  { wordCode := 113866, rule := .chromograms #[12714, 18059, 13266, 13266, 17989, 12714, 13266, 12714, 17989, 19825, 15006, 15222, 15006, 19825] },
  { wordCode := 301672, rule := .chromograms #[3961, 3961, 3961, 16046, 3961, 3961, 16046, 4315, 16190, 15022, 15022, 19820, 15124, 19832] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk027 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 299752, rule := .chromograms #[4135, 4135, 4135, 4141, 4135, 4135, 4141, 16124, 16124, 15160, 15160, 15166, 19838, 19838] },
  { wordCode := 116104, rule := .chromograms #[13266, 17989, 12714, 12714, 17989, 12714, 12714, 13266, 18059, 19825, 15006, 15006, 15222, 19853] },
  { wordCode := 234180, rule := .chromograms #[7153, 7153, 19867, 19711, 19711] },
  { wordCode := 267678, rule := .chromograms #[8122, 12862, 748, 16268, 1372, 748, 19898, 91, 15370, 1372, 748, 18676, 91, 15370] },
  { wordCode := 268948, rule := .chromograms #[3388, 3052, 3052, 19904, 1000, 6928, 6928, 4618, 6958, 4348, 4348, 6958, 4618, 7198, 12730, 12976, 19904, 910, 19886, 19886, 910, 19904, 1000, 28, 28, 28, 28, 28, 2194, 2194, 3418, 910, 3076, 3076, 910, 3076, 1000, 28, 28, 28, 28, 28] },
  { wordCode := 262634, rule := .chromograms #[2122, 18094, 709, 13432, 17978, 709, 2122, 709, 17978, 19910, 709, 2122, 709, 19910] },
  { wordCode := 6734, rule := .chromograms #[19927, 912] },
  { wordCode := 7076, rule := .chromograms #[19937, 972] },
  { wordCode := 272052, rule := .chromograms #[8122, 8122, 9028, 19100, 169, 748, 19898, 1348, 15664, 169, 748, 18676, 1348, 15664] },
  { wordCode := 260550, rule := .chromograms #[18836, 15506, 20005, 15506, 18836] },
  { wordCode := 260352, rule := .chromograms #[18868, 15488, 19994, 15488, 18868] },
  { wordCode := 260396, rule := .chromograms #[15500, 19436, 15805, 17530, 19940, 15500, 15500, 15805, 19981, 19940, 15500, 15500, 15805, 19981] },
  { wordCode := 245984, rule := .chromograms #[2965, 5035, 5107, 2287, 5107, 18931, 2965, 2287, 2965, 6331, 2287, 14350, 2221, 2245, 20030, 2965, 2287, 2965, 20011, 2287, 20017, 2221, 2245, 20011, 2287, 20017, 2221, 2245, 20030, 2965, 2287, 2965, 6673, 2287, 5035, 2221, 2245, 6331, 2287, 18931, 2221, 2245] },
  { wordCode := 22910, rule := .chromograms #[20057, 3768, 3432, 3768, 20035, 3432, 20041, 3402, 3414, 20035, 3432, 20041, 3402, 3414] },
  { wordCode := 27284, rule := .chromograms #[20129, 16241, 4254, 5142, 4152, 16133, 16481, 16121, 5244, 4152, 16133, 20129, 4254, 16241] },
  { wordCode := 240270, rule := .chromograms #[16106, 16333, 16333, 16333, 16094, 16094, 16106, 20120, 20120, 16094, 16094, 16106, 16333, 16333] },
  { wordCode := 28258, rule := .chromograms #[20105, 20105, 16247, 5142, 16211, 16211, 5142, 16235, 5202, 4152, 4086, 16205, 4086, 16241] },
  { wordCode := 29580, rule := .chromograms #[5700, 4752, 20153, 4686, 4752, 6510, 4686, 6510, 4686, 4752, 20153, 4686, 20153, 4686] },
  { wordCode := 237964, rule := .chromograms #[20162, 4459, 4459, 4459, 4819, 20162, 4927, 4807, 4819, 4465, 4381, 4381, 4459, 4459] },
  { wordCode := 30318, rule := .chromograms #[4776, 5946, 5946, 5988, 4752, 4752, 4776, 6804, 6804, 4752, 4752, 4776, 20171, 20171] },
  { wordCode := 293158, rule := .chromograms #[18604, 7540, 18968, 7384, 3766, 18604, 2914, 20354, 18704, 3766, 15343, 2914, 15343, 15356] },
  { wordCode := 238210, rule := .chromograms #[20132, 20132, 4951, 4939, 4819, 4819, 4807, 4927, 4939, 4465, 4363, 4807, 4363, 4939] },
  { wordCode := 31926, rule := .chromograms #[18947, 6540, 5880, 5880, 20203, 5880, 5880, 5658, 5700, 4752, 4752, 4776, 20171, 20171] },
  { wordCode := 252772, rule := .chromograms #[6349, 20017, 2245, 2221, 2245, 20060, 14566, 14566, 16016, 14644, 20060, 5035, 5107, 5107, 6133, 6325, 6325, 6349, 6673, 6799, 5035, 5107, 5107, 16460, 5263, 5035, 5107, 5107, 2287, 2767, 2755, 2755, 6673, 2287, 5035, 2221, 2245, 16460, 5263, 5035, 5107, 5107] },
  { wordCode := 279796, rule := .chromograms #[5368, 5368, 19336, 5434, 10126, 10180, 19336, 10126, 10126, 19336, 10126, 10126, 10180, 19366, 5434, 16490, 5368, 5368, 16490, 5368, 5368, 5434, 19366, 20182, 18778, 18790, 18778, 20182, 5434, 15560, 5368, 5368, 15518, 5368, 5368, 5434, 15518, 15745, 15757, 18790, 15757, 15745] },
  { wordCode := 34802, rule := .chromograms #[20129, 16241, 4254, 4254, 4152, 16133, 16133, 16163, 4152, 5244, 16481, 20173, 5142, 16421] },
  { wordCode := 34856, rule := .chromograms #[16217, 4290, 4122, 4122, 20111, 4122, 4122, 5268, 16175, 20189, 5268, 16451, 5154, 5160] },
  { wordCode := 250464, rule := .chromograms #[3055, 3739, 19798, 5407, 20191, 6007, 5407, 20198, 5407, 20191, 3073, 3055, 20047, 3739] },
  { wordCode := 36138, rule := .chromograms #[4686, 4686, 18947, 4776, 20203, 5988, 5700, 20213, 5700, 6612, 5988, 5700, 18947, 5700] },
  { wordCode := 39228, rule := .chromograms #[5700, 4752, 20153, 4644, 4752, 6510, 4644, 18947, 6804, 6612, 5988, 5700, 18947, 5700] },
  { wordCode := 63594, rule := .chromograms #[16787, 20263] },
  { wordCode := 63616, rule := .chromograms #[18979, 16799, 16799, 20275, 20273] },
  { wordCode := 63936, rule := .chromograms #[16853, 20285] },
  { wordCode := 322354, rule := .chromograms #[17272, 7756, 20294, 13318, 7756, 17272, 17272, 20294, 7756, 7756, 17272, 17272, 19582, 7756] },
  { wordCode := 67378, rule := .chromograms #[20333, 8280, 8280, 8280, 8382, 20333, 8454, 8376, 8382, 8286, 8184, 8184, 8280, 8280] },
  { wordCode := 69792, rule := .chromograms #[8850, 9504, 9582, 9138, 20347, 8850, 8844, 20477, 9138, 19231, 8850, 8844, 9582, 9138] },
  { wordCode := 202242, rule := .chromograms #[7885, 8479, 19808, 9277, 20401, 9781, 9277, 19177, 9277, 20401, 7903, 7885, 19177, 8479] },
  { wordCode := 329090, rule := .chromograms #[475, 13264, 793, 793, 1954, 19528, 12394, 1954, 1954, 2002, 12202, 18536, 9286, 2002, 20386, 16366, 9568, 7582, 9376, 16330, 7708, 7648, 7654, 9376, 9550, 19166, 9286, 9298, 20386, 19210, 9568, 7582, 9376, 19156, 7708, 7648, 7654, 9376, 9550, 19166, 9286, 9298] },
  { wordCode := 74168, rule := .chromograms #[19069, 8466, 8184, 8184, 8286, 8184, 8184, 8280, 8280, 17399, 10062, 20417, 9954, 9960] },
  { wordCode := 74222, rule := .chromograms #[8418, 8514, 8238, 8232, 19067, 8238, 8232, 8310, 8310, 20429, 17423, 10026, 9978, 17381] },
  { wordCode := 210990, rule := .chromograms #[15025, 15025, 14899, 14899, 19771, 14899, 10537, 10237, 14497, 20444, 16790, 10537, 10237, 16952] },
  { wordCode := 211098, rule := .chromograms #[10561, 14791, 14935, 10165, 14791, 10561, 10165, 19765, 10165, 16856, 10561, 10165, 20438, 10165] },
  { wordCode := 75396, rule := .chromograms #[8862, 8862, 8994, 8994, 19231, 9762, 9504, 9582, 9504, 20467, 17645, 10512, 10410, 17759] },
  { wordCode := 75504, rule := .chromograms #[8910, 8910, 9810, 9036, 9702, 9810, 9552, 19225, 9552, 17717, 10548, 10356, 20453, 10356] },
  { wordCode := 78540, rule := .chromograms #[9486, 9744, 8850, 8844, 20347, 8850, 8844, 20477, 9138, 20467, 17645, 10512, 10410, 17759] },
  { wordCode := 347680, rule := .chromograms #[3460, 3130, 3460, 19886, 910, 3130, 3460, 2248, 910, 2620, 2248, 910, 2620, 1000, 12730, 12976, 19904, 910, 19886, 19886, 910, 19904, 1000, 28, 28, 28, 28, 28, 6904, 6904, 7906, 7492, 8212, 7906, 7444, 7906, 7444, 8212, 7906, 11098, 7906, 11098] },
  { wordCode := 185734, rule := .chromograms #[20624, 20624, 12079, 11881, 11881] },
  { wordCode := 345748, rule := .chromograms #[13168, 19922, 3802, 3796, 3796, 2938, 3802, 3796, 3796, 2926, 2926, 2926, 1036, 1042, 19916, 13174, 13168, 13168, 19922, 19916, 19916, 1036, 1042, 271, 259, 271, 259, 271, 8488, 7354, 7354, 7360, 8482, 8482, 8488, 7522, 7522, 8482, 8482, 8488, 11770, 11776] },
  { wordCode := 185680, rule := .chromograms #[19646, 20618, 12061, 20504, 12061] },
  { wordCode := 189244, rule := .chromograms #[17792, 17894, 12145, 17864, 12571, 12145, 20594, 12145, 20594, 11197, 11107, 11107, 11791, 11791] },
  { wordCode := 342940, rule := .chromograms #[9466, 9310, 7714, 7714, 7714, 9310, 9370, 9370, 9370, 9466, 9550, 9550, 1954, 9466, 19972, 12250, 12250, 517, 12316, 19972, 12388, 793, 793, 517, 12202, 12202, 793, 517, 19156, 9376, 9472, 9466, 9376, 19156, 9310, 7714, 7714, 9376, 9550, 9310, 9370, 9370] },
  { wordCode := 343156, rule := .chromograms #[9310, 9310, 7648, 7648, 7648, 9310, 9286, 9286, 9286, 9550, 9550, 9550, 1990, 9550, 19972, 12190, 12190, 475, 12400, 19972, 12388, 859, 859, 475, 12202, 12202, 859, 475, 19156, 9292, 9568, 9310, 9292, 19156, 9310, 7648, 7648, 9292, 9550, 9310, 9286, 9286] },
  { wordCode := 188296, rule := .chromograms #[12361, 17834, 17822, 17827, 12355, 12355, 12361, 20606, 20606, 11461, 11461, 11461, 11461, 11461] },
  { wordCode := 177662, rule := .chromograms #[20552, 18020] },
  { wordCode := 353754, rule := .chromograms #[91, 91, 91, 15370, 91, 91, 15370, 1348, 15664, 8122, 9028, 17848, 12838, 20566] },
  { wordCode := 190412, rule := .chromograms #[20516, 12019, 12019, 13561, 20629] },
  { wordCode := 339084, rule := .chromograms #[15488, 15488, 19994, 20432, 19318] },
  { wordCode := 98278, rule := .chromograms #[13344, 13032, 12960, 12948, 12960, 13032, 12960, 12948, 12960, 19565, 13152, 14130, 13152, 13188, 20657, 13992, 13980, 13608, 20647, 14172, 13608, 13638, 14190, 19667, 14010, 14130, 13980, 13992, 20657, 13188, 12996, 13188, 20647, 12996, 13032, 12948, 12960, 19565, 12996, 13032, 12948, 12960] },
  { wordCode := 305014, rule := .chromograms #[2245, 2245, 2245, 2281, 2281, 2245, 2245, 2281, 2281, 6673, 2983, 2767, 6673, 2767, 6109, 6109, 6133, 5023, 6673, 6673, 5023, 5035, 5023, 16460, 5275, 5023, 5035, 5023, 20668, 20668, 14722, 14248, 14644, 14644, 14248, 14260, 14248, 20672, 14362, 14248, 14260, 14248] },
  { wordCode := 225364, rule := .chromograms #[7165, 7165, 7213, 7213, 17642, 17689, 9961, 9997, 9961, 20665, 18242, 18367, 18242, 19717] },
  { wordCode := 99562, rule := .chromograms #[11592, 11502, 11490, 11490, 19511, 11808, 11808, 11706, 11718, 20687, 14352, 20677, 14352, 14424] },
  { wordCode := 224236, rule := .chromograms #[16832, 16832, 10549, 10549, 10141, 10141, 10141, 10141, 10141, 14863, 14461, 20738, 14461, 20738] },
  { wordCode := 307948, rule := .chromograms #[6349, 20017, 2245, 2221, 2221, 20060, 14566, 14566, 14566, 14644, 20060, 14710, 5011, 5023, 6133, 6325, 6325, 6325, 6673, 6799, 6799, 5011, 5023, 6331, 6139, 6133, 6325, 6325, 20662, 14566, 14566, 14566, 14644, 20662, 14710, 14242, 14248, 14572, 14524, 14524, 14566, 14566] },
  { wordCode := 308164, rule := .chromograms #[6109, 20017, 2479, 2461, 2461, 20060, 14506, 14506, 14506, 14722, 20060, 14710, 5107, 5119, 6133, 6085, 6085, 6085, 6799, 6799, 6799, 5107, 5119, 6091, 6139, 6133, 6085, 6085, 20662, 14506, 14506, 14506, 14722, 20662, 14710, 14302, 14308, 14512, 14524, 14524, 14506, 14506] },
  { wordCode := 223288, rule := .chromograms #[10345, 16892, 16892, 16898, 10357, 10345, 10357, 10345, 10357, 14671, 14671, 14677, 20732, 20732] },
  { wordCode := 306232, rule := .chromograms #[6487, 20078, 14920, 15998, 6511, 6487, 6511, 6487, 6511, 20692, 14920, 19778, 14920, 14938] },
  { wordCode := 301966, rule := .chromograms #[5689, 3367, 3367, 3385, 5689, 5689, 5701, 5605, 5605, 20720, 20714, 20714, 20720, 20720] },
  { wordCode := 311822, rule := .chromograms #[2755, 5035, 5107, 2287, 2281, 5035, 5107, 5107, 5119, 14572, 5263, 14524, 5263, 14566, 2287, 2767, 2755, 2767, 20011, 2287, 2281, 2461, 2461, 20011, 2287, 2281, 2461, 2461, 20662, 14566, 14566, 14566, 14644, 20662, 14710, 14242, 14248, 14572, 14524, 14524, 14566, 14566] },
  { wordCode := 314768, rule := .chromograms #[5125, 3007, 6163, 2491, 3007, 15889, 2491, 20066, 16028, 14470, 14680, 14218, 18254, 14218] },
  { wordCode := 312848, rule := .chromograms #[5179, 6547, 2677, 2671, 15919, 2677, 2671, 16010, 20084, 14866, 14854, 14854, 14404, 18272] },
  { wordCode := 296266, rule := .chromograms #[20132, 20132, 4951, 4381, 4819, 4819, 4819, 4819, 4819, 20750, 15262, 15208, 15220, 15208] },
  { wordCode := 296554, rule := .chromograms #[20156, 4483, 4477, 4477, 4903, 4903, 4903, 4903, 4903, 18398, 18398, 15232, 15238, 15232] },
  { wordCode := 297242, rule := .chromograms #[18727, 4939, 4381, 4381, 4465, 4381, 4381, 4459, 4459, 20750, 15250, 20746, 15202, 15208] },
  { wordCode := 263588, rule := .chromograms #[865, 2014, 9442, 493, 9436, 13282, 865, 493, 865, 20584, 493, 7684, 493, 18736, 12304, 865, 493, 865, 19514, 493, 2014, 493, 12148, 19514, 493, 12304, 493, 865, 20792, 865, 493, 865, 20756, 493, 2014, 493, 16360, 20756, 493, 18754, 493, 865] },
  { wordCode := 259214, rule := .chromograms #[10318, 5572, 16540, 5680, 10246, 5572, 15560, 5680, 15560, 20786, 15446, 5434, 5320, 16490, 20779, 15560, 15446, 15560, 20600, 15446, 15865, 15446, 19592, 20600, 15446, 20779, 15446, 15560, 5434, 15560, 5320, 15560, 20786, 15446, 5572, 5680, 16540, 20786, 15446, 5434, 5320, 15560] },
  { wordCode := 11974, rule := .chromograms #[18481, 1482, 1470, 1470, 1722, 1800, 1800, 1716, 1722, 20797, 2016, 20803, 2016, 2136] },
  { wordCode := 19874, rule := .chromograms #[20809, 2316] },
  { wordCode := 284824, rule := .chromograms #[20854, 3634, 18584, 2848, 3634, 18584, 2848, 18584, 2848, 3634, 15332, 2848, 15692, 2848] },
  { wordCode := 242948, rule := .chromograms #[5611, 20815, 3511, 20815, 3511] },
  { wordCode := 286598, rule := .chromograms #[20836, 2980, 15724, 3766, 2980, 18650, 3766, 18604, 2980, 2980, 18650, 3766, 15724, 2980] },
  { wordCode := 283144, rule := .chromograms #[7582, 7582, 19988, 9562, 9562, 9298, 9298, 9310, 9310, 9466, 9466, 9466, 9466, 9466, 7648, 7714, 7582, 9310, 9466, 7582, 9466, 7582, 9466, 20920, 7582, 7648, 7582, 7714, 18457, 18457, 475, 475, 517, 475, 475, 517, 517, 2002, 2002, 18518, 2032, 18518] },
  { wordCode := 283000, rule := .chromograms #[7750, 18766, 7606, 18766, 12268, 19216, 19174, 9406, 9406, 9580, 17266, 17266, 12424, 9580, 19216, 19174, 7750, 9406, 7606, 17266, 17266, 16372, 9580, 7606, 20288, 20932, 7750, 20932, 19892, 19892, 19892, 18742, 15398, 15398, 15398, 15398, 15398, 15832, 15832, 20008, 20002, 20008] },
  { wordCode := 236338, rule := .chromograms #[20839, 4585, 16292, 4585, 16292] },
  { wordCode := 30078, rule := .chromograms #[6402, 4518, 16645, 4518, 20845] },
  { wordCode := 30808, rule := .chromograms #[6180, 20899, 5412, 20137, 20137] },
  { wordCode := 279398, rule := .chromograms #[18902, 10426, 19382, 10234, 5788, 18902, 5512, 20876, 18796, 5788, 18902, 5512, 20876, 18796] },
  { wordCode := 35128, rule := .chromograms #[6180, 20899, 5346, 20215, 5346] },
  { wordCode := 249454, rule := .chromograms #[3511, 20905, 5611, 20815, 3511] },
  { wordCode := 323776, rule := .chromograms #[20864, 7564, 18968, 7384, 3826, 18604, 2914, 18604, 2914, 7564, 17902, 7384, 18052, 7384] },
  { wordCode := 327534, rule := .chromograms #[8974, 508, 19060, 718, 718, 508, 16300, 718, 85, 15376, 15313, 85, 364, 15364, 4438, 15908, 4720, 4054, 18628, 18628, 4054, 4150, 15976, 18578, 18578, 18578, 15908, 15908, 8632, 17816, 8974, 8086, 19060, 19048, 8086, 8266, 17050, 21056, 21056, 12820, 13006, 20560] },
  { wordCode := 326378, rule := .chromograms #[20828, 7330, 15332, 7516, 2788, 18640, 3706, 18584, 2788, 7330, 18986, 7516, 18032, 7330] },
  { wordCode := 326036, rule := .chromograms #[20836, 7384, 15343, 7564, 2914, 18650, 3826, 18604, 2914, 7384, 20260, 7564, 18052, 7384] },
  { wordCode := 208912, rule := .chromograms #[6907, 7369, 17624, 7591, 17624, 20929, 7819, 7591, 7819, 20936, 7591, 17366, 7591, 9859, 20929, 6925, 6907, 6907, 20245, 7369, 7369, 7591, 20245, 20936, 7591, 20929, 7591, 7819, 17366, 6925, 6907, 6907, 19448, 7369, 7369, 7591, 17624, 20420, 7591, 17366, 7591, 7819] },
  { wordCode := 200664, rule := .chromograms #[20371, 7993, 20941, 7993, 20371] },
  { wordCode := 330752, rule := .chromograms #[20828, 2848, 15692, 3706, 2848, 18640, 3706, 19138, 18680, 7348, 18986, 7516, 17858, 17890] },
  { wordCode := 315118, rule := .chromograms #[15656, 20236, 6820, 21004, 11026] },
  { wordCode := 346584, rule := .chromograms #[202, 3484, 3946, 682, 682, 1198, 1198, 1288, 1288, 19114, 8920, 2668, 2398, 8608, 31, 322, 202, 490, 20768, 682, 490, 20776, 490, 18415, 49, 31, 202, 322, 7948, 8608, 11416, 8230, 19042, 7948, 7942, 8158, 8230, 19042, 7948, 7942, 8158, 8230] },
  { wordCode := 83970, rule := .chromograms #[14796, 12498, 21041, 12498, 21041] },
  { wordCode := 84402, rule := .chromograms #[14814, 12516, 21047, 12516, 21023] },
  { wordCode := 84414, rule := .chromograms #[12522, 14826, 14820, 14820, 12534, 12522, 12522, 21049, 21049, 12534, 12522, 12522, 21025, 21025] },
  { wordCode := 341224, rule := .chromograms #[19246, 9814, 9808, 2182, 20762, 12610, 2182, 667, 12622, 19240, 9826, 13492, 9808, 9814] },
  { wordCode := 88628, rule := .chromograms #[13188, 13608, 14190, 12996, 14190, 14130, 13188, 12996, 13188, 19667, 12996, 13032, 12948, 12960, 21055, 13188, 12996, 13188, 21065, 12996, 13032, 12948, 12960, 19565, 12996, 13032, 12948, 12960, 20657, 13188, 12996, 13188, 20647, 12996, 13032, 12948, 12960, 19565, 12996, 13032, 12948, 12960] },
  { wordCode := 348754, rule := .chromograms #[7714, 7648, 7714, 7708, 859, 7648, 7714, 7582, 859, 20920, 7582, 793, 7582, 793, 19988, 19988, 12400, 859, 12316, 12316, 793, 12316, 793, 2002, 2002, 13252, 2032, 13252, 19192, 19210, 9292, 7714, 9376, 9292, 7648, 7708, 7714, 13324, 7582, 7648, 7582, 7714] },
  { wordCode := 96038, rule := .chromograms #[12918, 13968, 13080, 13080, 13074, 21067, 13578, 13572, 13578, 21077, 13668, 19585, 13446, 13446, 19681, 13578, 13572, 13578, 14034, 13668, 13968, 13668, 14028, 21077, 13668, 21067, 13572, 13578, 19549, 12924, 12912, 12912, 13074, 13122, 13122, 13080, 13074, 13374, 13338, 19585, 13338, 13446] },
  { wordCode := 334748, rule := .chromograms #[6772, 19945, 15626, 21004, 11026] },
  { wordCode := 98514, rule := .chromograms #[11202, 21089] },
  { wordCode := 225396, rule := .chromograms #[7231, 10861, 21097, 21170, 21097] },
  { wordCode := 101466, rule := .chromograms #[12498, 12498, 21041, 14796, 21113] },
  { wordCode := 101898, rule := .chromograms #[12516, 12516, 21047, 14814, 21119] },
  { wordCode := 101910, rule := .chromograms #[12534, 12534, 12522, 12522, 12534, 12522, 12522, 21049, 21049, 14826, 14820, 14820, 20713, 20713] },
  { wordCode := 102648, rule := .chromograms #[20521, 14826, 21131, 14880, 12534, 21131, 12582, 21131, 12534, 14826, 20707, 14880, 20707, 14826] },
  { wordCode := 222480, rule := .chromograms #[8071, 8071, 20941, 21140, 21140] },
  { wordCode := 234144, rule := .chromograms #[7231, 7231, 21170, 21097, 21097] },
  { wordCode := 6698, rule := .chromograms #[21181, 894] },
  { wordCode := 260442, rule := .chromograms #[20612, 15464, 21187, 15464, 20890] },
  { wordCode := 21732, rule := .chromograms #[21203, 2616, 2610, 20023, 2934] },
  { wordCode := 23866, rule := .chromograms #[20041, 3414, 3402, 3414, 21215, 3744, 20057, 3744, 3768, 20035, 3432, 20041, 3402, 3414] },
  { wordCode := 28294, rule := .chromograms #[20117, 16145, 16139, 5172, 21251, 16253, 5172, 4290, 4290, 20111, 4122, 16217, 4122, 4290] },
  { wordCode := 30426, rule := .chromograms #[4614, 18925, 5874, 4914, 18925, 4614, 4608, 6726, 4914, 21229, 4614, 4608, 20861, 4914] },
  { wordCode := 31656, rule := .chromograms #[4608, 4914, 6600, 5940, 21259, 16543, 5940, 5760, 16531, 21229, 4614, 4608, 20861, 4914] },
  { wordCode := 61044, rule := .chromograms #[20239, 7164, 7158, 21269, 7374] },
  { wordCode := 63286, rule := .chromograms #[21281, 16889, 16879, 16889, 20251, 16961, 19021, 16961, 19001, 20251, 16961, 21275, 16879, 16889] },
  { wordCode := 63558, rule := .chromograms #[16817, 21289] },
  { wordCode := 67660, rule := .chromograms #[21305, 8208, 8196, 8208, 21295, 8484, 8418, 8484, 8514, 19067, 8238, 8418, 8196, 8208] },
  { wordCode := 69846, rule := .chromograms #[9552, 9552, 10482, 10476, 9006, 17675, 8880, 21311, 17777, 9006, 9810, 8880, 19225, 9552] },
  { wordCode := 85152, rule := .chromograms #[19789, 12534, 21341, 12582, 12534, 21131, 12582, 21131, 12534, 12534, 21011, 12582, 21011, 12534] },
  { wordCode := 177284, rule := .chromograms #[21343, 18002] },
  { wordCode := 89766, rule := .chromograms #[15030, 12750, 21161, 12750, 21353] }]

def twentiethCatalogueOrbitProofDagCodeNodeChunk028 : Array ClassicalCertificateOrbitProofDagReduction.NodeCode :=
  #[{ wordCode := 348610, rule := .chromograms #[9592, 17246, 9418, 7750, 9418, 20872, 20872, 7750, 18742, 7606, 18766, 18766, 13312, 15409, 21334, 21334, 21328, 12268, 17968, 17968, 17968, 12424, 12424, 13372, 15832, 18082, 13312, 18070, 20380, 20380, 19222, 9592, 17252, 17252, 17246, 7750, 9418, 7606, 18076, 18082, 7750, 18070] },
  { wordCode := 339174, rule := .chromograms #[15464, 15464, 21187, 20612, 20968] },
  { wordCode := 304870, rule := .chromograms #[16567, 16675, 16675, 2341, 2341, 16675, 16567, 2341, 2341, 2809, 16657, 16657, 2815, 2809, 16675, 16567, 6211, 6211, 6715, 16657, 16657, 5059, 6715, 5239, 18841, 18859, 5059, 18781, 21394, 21394, 21388, 14584, 18322, 18322, 18322, 14320, 14740, 14368, 19738, 20678, 14320, 20678] },
  { wordCode := 308266, rule := .chromograms #[6031, 15902, 20090, 20228, 6697, 14548, 20090, 14440, 16388, 21218, 21218, 14626, 14686, 16400, 6283, 16555, 6031, 16388, 16693, 16681, 6697, 6883, 16400, 16562, 16562, 6283, 6031, 16555, 14548, 21092, 14440, 18230, 21370, 21370, 14626, 14686, 18314, 19760, 19760, 14548, 14440, 18314] },
  { wordCode := 306322, rule := .chromograms #[6445, 20882, 14842, 16442, 16627, 6445, 16442, 6445, 16622, 21400, 14842, 18338, 14842, 18338] },
  { wordCode := 231630, rule := .chromograms #[10111, 14497, 10447, 10447, 20725, 14995, 14977, 21284, 15145, 19771, 14899, 14497, 14587, 14497] },
  { wordCode := 296392, rule := .chromograms #[20156, 4345, 4327, 4327, 21235, 4903, 4903, 4789, 4801, 21410, 18398, 15232, 15178, 18392] },
  { wordCode := 263480, rule := .chromograms #[1954, 12202, 2002, 9472, 7582, 19576, 13252, 859, 7582, 517, 13360, 7708, 7648, 7654, 19528, 12394, 859, 1954, 517, 12202, 13360, 12190, 2002, 517, 12202, 19528, 859, 12394, 21422, 18457, 859, 1954, 517, 18445, 18536, 16366, 2002, 517, 16330, 21244, 859, 16366] },
  { wordCode := 284446, rule := .chromograms #[21448, 3814, 20950, 2896, 3814, 20950, 2896, 21430, 2896, 3814, 19873, 2896, 19960, 2896] },
  { wordCode := 286688, rule := .chromograms #[21442, 2896, 19960, 3814, 2896, 21436, 3814, 21430, 2896, 2896, 21436, 3814, 19960, 2896] },
  { wordCode := 283162, rule := .chromograms #[7588, 7588, 19988, 9550, 517, 19166, 9298, 9286, 9286, 9466, 9550, 9550, 1954, 9466, 19166, 7714, 7588, 7714, 9466, 7588, 9550, 7588, 9466, 20920, 7588, 20926, 7588, 7714, 21422, 18457, 859, 859, 517, 18445, 18445, 16348, 517, 2002, 18536, 21422, 1954, 18518] },
  { wordCode := 293248, rule := .chromograms #[20950, 7558, 21448, 7402, 3814, 20950, 2962, 20950, 18698, 3814, 19873, 2962, 19873, 18698] },
  { wordCode := 323866, rule := .chromograms #[21448, 7534, 21448, 7402, 3736, 20950, 2962, 21430, 2962, 7534, 20494, 7402, 20572, 7402] },
  { wordCode := 326000, rule := .chromograms #[21442, 7402, 19873, 7534, 2962, 21436, 3736, 21430, 2962, 7402, 21466, 7534, 20572, 7402] },
  { wordCode := 330374, rule := .chromograms #[21442, 2896, 19960, 3736, 2896, 21436, 3736, 20950, 18698, 7366, 21466, 7534, 20494, 19076] },
  { wordCode := 346692, rule := .chromograms #[3136, 3136, 574, 3214, 664, 1162, 1162, 1270, 1270, 8752, 2644, 2278, 19090, 2278, 7, 262, 1270, 1270, 574, 18454, 664, 21418, 18442, 118, 25, 7, 18422, 262, 7870, 11464, 19090, 8182, 8020, 7870, 7864, 19052, 8182, 8020, 7870, 7864, 19052, 8182] },
  { wordCode := 343258, rule := .chromograms #[16990, 9334, 17236, 9220, 811, 9334, 17236, 9220, 1942, 19204, 19198, 1942, 1978, 17960, 12226, 19976, 12118, 1942, 21502, 21502, 811, 883, 17960, 17930, 17930, 811, 883, 17930, 9460, 20362, 9520, 13234, 20362, 20362, 9334, 9220, 17236, 17930, 17930, 9334, 9220, 17236] },
  { wordCode := 341314, rule := .chromograms #[17302, 17302, 9736, 2158, 21490, 12556, 2158, 709, 17978, 20410, 9778, 13468, 9736, 17302] },
  { wordCode := 89964, rule := .chromograms #[15066, 12846, 21167, 12846, 21509] },
  { wordCode := 98712, rule := .chromograms #[11346, 21521] },
  { wordCode := 101640, rule := .chromograms #[14862, 21137, 12570, 12570, 21533, 12570, 12360, 21527, 12360, 21533, 14862, 14676, 21527, 14676] },
  { wordCode := 84144, rule := .chromograms #[12570, 21013, 14862, 12360, 21533, 12570, 12360, 21527, 12360, 21611, 12570, 12360, 21605, 12360] },
  { wordCode := 348880, rule := .chromograms #[9268, 7642, 9358, 7696, 841, 7642, 18736, 7696, 469, 21454, 18760, 841, 769, 781, 21616, 12148, 12136, 469, 21322, 12358, 841, 769, 781, 20584, 2014, 13282, 1918, 1924, 19186, 9526, 9274, 9268, 20368, 9274, 7642, 7696, 9358, 20584, 13336, 7642, 7696, 13222] },
  { wordCode := 314792, rule := .chromograms #[5047, 5047, 6853, 5131, 2311, 2791, 6853, 3013, 2311, 18920, 6175, 2311, 2497, 6355, 2791, 15937, 3013, 2311, 21193, 15895, 2311, 2497, 20096, 21566, 20072, 21224, 16034, 20096, 21622, 14464, 14452, 14452, 21382, 14674, 14284, 14212, 14602, 21374, 18248, 14284, 14212, 18224] },
  { wordCode := 231684, rule := .chromograms #[10087, 10495, 10441, 10435, 15061, 16772, 14959, 21584, 16934, 14791, 14935, 14527, 19765, 14527] },
  { wordCode := 89856, rule := .chromograms #[15000, 12708, 21545, 12708, 21641] },
  { wordCode := 114764, rule := .chromograms #[13140, 14142, 13020, 13572, 13434, 21067, 13578, 13572, 13326, 21077, 13668, 13434, 13392, 13398, 21493, 19567, 13140, 13326, 13020, 19555, 13434, 12912, 12924, 13020, 13122, 19549, 12912, 12924, 21647, 21155, 19817, 15240, 21403, 21149, 21149, 15084, 15270, 15132, 19843, 21649, 15084, 19831] },
  { wordCode := 343168, rule := .chromograms #[7582, 7708, 7654, 7648, 7654, 19166, 9298, 9286, 2032, 9466, 9550, 19528, 1990, 1990, 21658, 19988, 12190, 2032, 12316, 19972, 13264, 859, 1990, 517, 12202, 19528, 859, 12394, 20386, 19210, 9568, 7582, 9376, 19156, 7708, 7648, 7654, 9376, 9550, 19166, 9286, 9298] },
  { wordCode := 223264, rule := .chromograms #[20989, 20989, 20995, 21625, 21661] }]

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix000 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 4)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 5)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 6)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 8)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 39)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 40)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 42)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 43))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3312))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 45)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 46)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 47)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 49)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 53))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3313))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 55))))
            (.empty)
            (.empty)))
        (.empty))
      (.empty))
    (.node
      (.node
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3591))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3073))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3074)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3529))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 81))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 82))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3075))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 110))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 111)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 113))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 114))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 116))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3076))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 142))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 143)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 144))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 145))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 146))))
            (.empty)))))
    (.empty)

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix001 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.empty)
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 178)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 179)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 181)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 182))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 183))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 185)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 186)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 187)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 189)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 195))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 196))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 198))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 244)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 245)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 247)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 248))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3324))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 250)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 251)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 252)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 254)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 258))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3325))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 260))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 299)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 300)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3326)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 302))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 303))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 304)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 305)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 306)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3327)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 311))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 312))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 314))))
            (.empty)
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 319)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 320)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 321)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 325)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3086)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 326)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 335)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3531)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 336)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3089)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3570)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3090)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 355)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 356)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 357)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 361)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3092)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 362)
                  (.empty))))
            (.empty)
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix003 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 366)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 367)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2647)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 370)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 373)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 374)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3468))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 379))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 381)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3532))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2648))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2649))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 429)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 431)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2652)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 433)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 435)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 436)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 440))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 441))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 442)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2653))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 444))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 446))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2654)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2655)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3592)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 487)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 489)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3571)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 494))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 495))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 498)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2656))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 501))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 502))))
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 509)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 511)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 512)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 513))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 514))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 515)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 516)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 517)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2657)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 523))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2658))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 525))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 565)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 567)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 569)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 570))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3469))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 572)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 573)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 574)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2659)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2660))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3534))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2661))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 623)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 624)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3572)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 626))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 628))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 630)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2663)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2664)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3593)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 639))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2665))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 640))))
            (.empty)
            (.empty)))))
    (.empty)

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix004 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 645))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2674))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 646)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 653))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 654))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 656))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2687))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3470))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2688)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 686))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3351))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 687))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 708))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2706))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 709)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 714))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 715))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 717))))
            (.empty)
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 721)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 723)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 724)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 726)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 728)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3355)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3356))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 729))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 730)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3357))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 733))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 735))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 767)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 768)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 769)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 772)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 774)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3358)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 776))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 777))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 779)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 782))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 783))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 784))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 817)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 819)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3574)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 3360)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3361)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3595)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 823))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 824))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 826)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 828))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 829))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 831))))
            (.empty)))))
    (.empty)

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix005 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 832))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 833))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2730))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 835))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 836))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 837))))
            (.empty)
            (.empty))
          (.empty))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 856))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 857))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2736))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 858))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 859))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 860))))
            (.empty)
            (.empty))
          (.empty))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2745))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2746))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3481))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 877))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 878))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3482))))
            (.empty)
            (.empty))
          (.empty))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 886)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2748)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 887)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3542)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2750)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2751)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 895)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 897)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 898)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3483)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 900)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 901)
                  (.empty))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2754)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3543)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2755)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2756)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 946)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 947)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 948)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3484)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 950)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 951)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 953)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 955)
                  (.empty))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 988)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2757)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 990)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2758)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 995)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 996)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 997)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 998)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1000)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1001)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1002)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1004)
                  (.empty))))
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1008)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1010)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1011)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1014)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1017)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1018)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3369))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1021))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1023)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3370))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1027))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1029))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1076)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1078)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1079)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1081)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1084)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1085)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1086))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1087))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1089)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1091))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1092))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1093))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1129)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1130)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3372)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1133)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1134)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3485)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1137))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1138))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1139)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1142))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1143))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1145))))
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix009 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1151)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1153)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1154)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1156)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1157)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2784)
                  (.empty)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1191)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1193)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1194)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1196)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1197)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2787)
                  (.empty)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1228)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1229)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3576)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 2790)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2791)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3596)
                  (.empty)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))))
    (.empty)
    (.node
      (.node
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 3578)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3167)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3168)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 3548)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1264)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1265)
                  (.empty)
                  (.empty))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 3169)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1282)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1283)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1285)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1286)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1287)
                  (.empty)
                  (.empty))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 3172)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1301)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1302)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1303)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1304)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1305)
                  (.empty)
                  (.empty))))
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix010 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1307)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1308)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3383)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1310))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1311))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1313)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1314)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1315)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1317)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1323))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1324))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1326))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1360)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1361)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3384)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1363))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3385))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1364)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1365)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1366)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1368)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1371))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3386))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1373))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3387)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3388)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3598)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1410))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1411))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1412)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1413)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1414)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3579)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1418))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1419))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1421))))
            (.empty)
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1425)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1427)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1428)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1429)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1431)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3180)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3389))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2850))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2851)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3390))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1434))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1435))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1472)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1474)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1475)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1478)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1480)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3187)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2863))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1481))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1483)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1486))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1487))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1490))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1522)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1523)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3491)
                  (.empty)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 3190)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3191)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3580)
                  (.empty)
                  (.empty))))
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2871))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1526))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1528)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1529))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1530))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1533))))
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1538)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1540)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1541)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3492)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1545)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1546)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1547)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1549)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1550)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3493)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3192)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3193)
                  (.empty))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1582)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3398)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1584)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1587)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1589)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1590)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1591)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3399)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1592)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3201)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1594)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1595)
                  (.empty))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1625)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1627)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1628)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1630)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1632)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1633)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1634)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1635)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1636)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3206)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1637)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1638)
                  (.empty))))
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix011 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1641))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1642))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1643))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1644))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1645))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2887))))
            (.empty)
            (.empty))
          (.empty))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1658))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1659))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1660))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1662))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1663))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2896))))
            (.empty)
            (.empty))
          (.empty))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1676))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1677))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3494))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2902))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2903))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3495))))
            (.empty)
            (.empty))
          (.empty))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1683)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3222)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1684)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3496)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2907)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2908)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1688)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1690)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1691)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3497)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1693)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1694)
                  (.empty))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 3233)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3498)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3235)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2916)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1722)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1723)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1724)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3499)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1726)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1727)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1729)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1730)
                  (.empty))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 1750)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3240)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1752)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2922)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1755)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1756)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 1757)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 1758)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 1759)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1760)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1761)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1762)
                  (.empty))))
            (.empty)))))
    (.node
      (.node
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3409))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2930))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2931)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3410))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1772))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1773))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2946))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1803))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1804)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1805))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1806))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1808))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2963))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1838))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1839)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1840))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1841))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1842))))
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix012 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1847)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1848)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1849)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1850))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1851))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1853)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1854)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1856)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1857)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1865))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1866))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1868))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1906)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1907)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1909)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1910))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3413))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1912)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1913)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1915)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1917)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1922))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3414))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1924))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1961)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1962)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3415)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1964))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1965))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1966)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 1967)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 1968)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3416)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1971))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1972))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1974))))
            (.empty)
            (.empty)))))
    (.node
      (.node
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3599))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3417))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3418)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3552))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1980))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1981))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3421))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1995))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1996)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1997))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 1998))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2000))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.empty)
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3422))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2010))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2011)))))
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2012))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2013))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2015))))
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2022)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2024)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2025)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3423)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2029)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2030)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 2031)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3505)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2032)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3424)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2033)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2034)
                  (.empty))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2059)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3605)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2060)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2061)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2062)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2063)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 3507)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3611)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3508)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2065)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2067)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2068)
                  (.empty))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2094)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2095)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2096)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2098)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2099)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2100)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 2101)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3556)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2102)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2103)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2104)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2105)
                  (.empty))))
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix013 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.empty)
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2106)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2107)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2109)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2110))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3256))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2112)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2113)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2115)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2117)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2123))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2124))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2126))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2151)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2152)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2154)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3257))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3582))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3259)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2156)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2158)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2160)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2164))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3557))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2166))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2186)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2187)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3428)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2188))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3261))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2190)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2191)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2192)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3429)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2197))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2198))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2200))))
            (.empty)
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2202)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2203)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2204)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2207)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2208)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2209)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2222)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3430)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2223)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2226)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3431)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2227)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2240)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2241)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2242)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2245)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2246)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2247)
                  (.empty))))
            (.empty)
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix014 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.empty)
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2250))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2251))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2252))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2253))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2254))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3268))))
            (.empty)
            (.empty))
          (.empty))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2261))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2262))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2263))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2265))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2266))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3270))))
            (.empty)
            (.empty))
          (.empty))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2277))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2278))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3559))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3272))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3273))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3585))))
            (.empty)
            (.empty))
          (.empty))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2281)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2282)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3029)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2283))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2284))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2286)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2287)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2288)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2290)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2294))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2295))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2297))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2324)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2325)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3031)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2327))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3439))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2328)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2329)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2330)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2332)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2333))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 3440))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2335))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3034)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3035)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3560)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2358))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2359))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2360)))))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2361)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2362)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3513)
                  (.empty))))
            (.empty)
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2364))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2365))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.empty)
                  (.leaf 2366))))
            (.empty)
            (.empty)))))

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix015 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2368)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3037)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2369)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2373)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2374)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2375)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3041)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3562)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3042)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2391)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3516)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2392)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2400)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3045)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2401)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2403)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2404)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2405)
                  (.empty))))
            (.empty)
            (.empty)))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2408)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2410)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2411)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3449)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2415)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2416)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 2417)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3517)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2419)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3450)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2420)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2421)
                  (.empty))))
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2445)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3604)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2446)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2448)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2449)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2450)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 3519)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3612)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 3520)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2452)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2454)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2455)
                  (.empty))))
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.leaf 2475)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 2477)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2478)
                  (.empty)
                  (.empty)))))
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2483)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2484)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2485)
                  (.empty)))))
          (.node
            (.node
              (.node
                (.node
                  (.leaf 2486)
                  (.empty)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.leaf 3521)
                  (.empty)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.leaf 2488)
                  (.empty)
                  (.empty))))
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2489)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2490)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2491)
                  (.empty))))
            (.empty)))))
    (.empty)

def twentiethCatalogueOrbitProofDagCodeContractTargetPrefix017 : ClassicalCertificateProofDagReduction.TargetTreeCode :=
  .node
    (.empty)
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2493)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2494)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3303)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2496)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2498)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2499)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2513)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2514)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3305)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2515)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2517)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2518)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3306)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3307)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3608)
                  (.empty))))
            (.empty))
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2524)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2525)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3589)
                  (.empty))))
            (.empty)
            (.empty))
          (.empty))))
    (.node
      (.node
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2529)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3065)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2530)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2533)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2534)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2535)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty)
        (.empty))
      (.node
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 3066)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3568)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3067)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2541)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3528)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2542)
                  (.empty))))
            (.empty)
            (.empty)))
        (.empty))
      (.node
        (.empty)
        (.empty)
        (.node
          (.node
            (.empty)
            (.empty)
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2546)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 3068)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2547)
                  (.empty)))))
          (.empty)
          (.node
            (.node
              (.node
                (.node
                  (.empty)
                  (.leaf 2548)
                  (.empty))
                (.empty)
                (.empty))
              (.node
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2549)
                  (.empty))
                (.empty))
              (.node
                (.empty)
                (.empty)
                (.node
                  (.empty)
                  (.leaf 2550)
                  (.empty))))
            (.empty)
            (.empty)))))

def twentiethCatalogueOrbitProofDagCode : ClassicalCertificateOrbitProofDagReduction.Code where
  nodeCount := 3613
  nodeChunks := #[twentiethCatalogueOrbitProofDagCodeNodeChunk000,
  twentiethCatalogueOrbitProofDagCodeNodeChunk001,
  twentiethCatalogueOrbitProofDagCodeNodeChunk002,
  twentiethCatalogueOrbitProofDagCodeNodeChunk003,
  twentiethCatalogueOrbitProofDagCodeNodeChunk004,
  twentiethCatalogueOrbitProofDagCodeNodeChunk005,
  twentiethCatalogueOrbitProofDagCodeNodeChunk006,
  twentiethCatalogueOrbitProofDagCodeNodeChunk007,
  twentiethCatalogueOrbitProofDagCodeNodeChunk008,
  twentiethCatalogueOrbitProofDagCodeNodeChunk009,
  twentiethCatalogueOrbitProofDagCodeNodeChunk010,
  twentiethCatalogueOrbitProofDagCodeNodeChunk011,
  twentiethCatalogueOrbitProofDagCodeNodeChunk012,
  twentiethCatalogueOrbitProofDagCodeNodeChunk013,
  twentiethCatalogueOrbitProofDagCodeNodeChunk014,
  twentiethCatalogueOrbitProofDagCodeNodeChunk015,
  twentiethCatalogueOrbitProofDagCodeNodeChunk016,
  twentiethCatalogueOrbitProofDagCodeNodeChunk017,
  twentiethCatalogueOrbitProofDagCodeNodeChunk018,
  twentiethCatalogueOrbitProofDagCodeNodeChunk019,
  twentiethCatalogueOrbitProofDagCodeNodeChunk020,
  twentiethCatalogueOrbitProofDagCodeNodeChunk021,
  twentiethCatalogueOrbitProofDagCodeNodeChunk022,
  twentiethCatalogueOrbitProofDagCodeNodeChunk023,
  twentiethCatalogueOrbitProofDagCodeNodeChunk024,
  twentiethCatalogueOrbitProofDagCodeNodeChunk025,
  twentiethCatalogueOrbitProofDagCodeNodeChunk026,
  twentiethCatalogueOrbitProofDagCodeNodeChunk027,
  twentiethCatalogueOrbitProofDagCodeNodeChunk028]
  contractTargets := .node
    (.node
      (.node
        (.node
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix000)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix001)
          (.empty))
        (.node
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix003)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix004)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix005))
        (.empty))
      (.node
        (.node
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix009)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix010)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix011))
        (.node
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix012)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix013)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix014))
        (.node
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix015)
          (.empty)
          (twentiethCatalogueOrbitProofDagCodeContractTargetPrefix017)))
      (.empty))
    (.empty)
    (.empty)

end ClassicalCertificateCatalogueTwentyOrbitProofDagData

end Mettapedia.GraphTheory.FourColor
