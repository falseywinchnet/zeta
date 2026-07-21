set_option linter.style.header false
namespace PF4.RobustThreeModeClosure.Generated
open Finset PF4.CERT12Inequalities

def c4BandACoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (571597930000000 / 19683 : ℚ)
  | 0, 1 => (5557313882800000 / 216513 : ℚ)
  | 0, 2 => (53734106516306560 / 2381643 : ℚ)
  | 0, 3 => (2583469179049841024 / 130990365 : ℚ)
  | 0, 4 => (15443566539252696447104 / 900558759375 : ℚ)
  | 1, 0 => (4162038242000000 / 137781 : ℚ)
  | 1, 1 => (40318510999280000 / 1515591 : ℚ)
  | 1, 2 => (388118290974283904 / 16671501 : ℚ)
  | 1, 3 => (92794586763349250432 / 4584662775 : ℚ)
  | 1, 4 => (550999130074247941109888 / 31519556578125 : ℚ)
  | 2, 0 => (18760844854000000 / 597051 : ℚ)
  | 2, 1 => (181067812040272000 / 6567561 : ℚ)
  | 2, 2 => (4943231599084160 / 205821 : ℚ)
  | 2, 3 => (2062466234139771081344 / 99334360125 : ℚ)
  | 2, 4 => (2432057526338258629873024 / 136584745171875 : ℚ)
  | 3, 0 => (8363834802400000 / 255879 : ℚ)
  | 3, 1 => (562922015985568000 / 19702683 : ℚ)
  | 3, 2 => (26844333619739763968 / 1083647565 : ℚ)
  | 3, 3 => (906344040312806842112 / 42571868625 : ℚ)
  | 3, 4 => (37128668155294127764050176 / 2048771177578125 : ℚ)
  | 4, 0 => (95704503470560000 / 2814669 : ℚ)
  | 4, 1 => (916637365079142400 / 30961359 : ℚ)
  | 4, 2 => (1522528737297195279616 / 59600616075 : ℚ)
  | 4, 3 => (51090395172054959017984 / 2341452774375 : ℚ)
  | 4, 4 => (2076518014718031476442418432 / 112682414766796875 : ℚ)
  | 5, 0 => (232298618698374400 / 6567561 : ℚ)
  | 5, 1 => (2216133205140841984 / 72243171 : ℚ)
  | 5, 2 => (13080870174192137173888 / 496671800625 : ℚ)
  | 5, 3 => (3053014921275936184084096 / 136584745171875 : ℚ)
  | 5, 4 => (17579690852824486127665232896 / 939020123056640625 : ℚ)
  | 6, 0 => (3835708731650560 / 104247 : ℚ)
  | 6, 1 => (1275585580026000944 / 40135095 : ℚ)
  | 6, 2 => (7490552785445814889472 / 275928778125 : ℚ)
  | 6, 3 => (248089767699964876002128 / 10840059140625 : ℚ)
  | 6, 4 => (9911968907586766357530809984 / 521677846142578125 : ℚ)
  | 7, 0 => (3990121499191040 / 104247 : ℚ)
  | 7, 1 => (943909618990834649 / 28667925 : ℚ)
  | 7, 2 => (1102701348741973587562 / 39418396875 : ℚ)
  | 7, 3 => (1269387968867447657978531 / 54200295703125 : ℚ)
  | 7, 4 => (287108469348124416366777476 / 14905081318359375 : ℚ)
  | 8, 0 => (9685081276622720 / 243243 : ℚ)
  | 8, 1 => (2281479178949809922 / 66891825 : ℚ)
  | 8, 2 => (2650720299800298944068 / 91976259375 : ℚ)
  | 8, 3 => (3029272479957142080789734 / 126467356640625 : ℚ)
  | 8, 4 => (308356017168740259235060952 / 15808419580078125 : ℚ)
  | 9, 0 => (3358313094648704 / 81081 : ℚ)
  | 9, 1 => (7877037020341360561 / 222972750 : ℚ)
  | 9, 2 => (910025570857606370437 / 30658753125 : ℚ)
  | 9, 3 => (10320995458628612928898939 / 421557855468750 : ℚ)
  | 9, 4 => (5717497743066805104428079506 / 289821025634765625 : ℚ)
  | 10, 0 => (3493478878652032 / 81081 : ℚ)
  | 10, 1 => (4079027942081374252 / 111486375 : ℚ)
  | 10, 2 => (1874004600516915756343 / 61317506250 : ℚ)
  | 10, 3 => (10542607807672316714241119 / 421557855468750 : ℚ)
  | 10, 4 => (5774778800592589221353299417 / 289821025634765625 : ℚ)
  | 11, 0 => (110122962996224 / 2457 : ℚ)
  | 11, 1 => (39385571310614633 / 1039500 : ℚ)
  | 11, 2 => (116907946482590083081 / 3716212500 : ℚ)
  | 11, 3 => (29646493785898028426459 / 1161316406250 : ℚ)
  | 11, 4 => (352980303505694726385204523 / 17564910644531250 : ℚ)
  | 12, 0 => (12728138023936 / 273 : ℚ)
  | 12, 1 => (14726771771955016 / 375375 : ℚ)
  | 12, 2 => (3037877983114116169 / 93843750 : ℚ)
  | 12, 3 => (36960946323801064891223 / 1419386718750 : ℚ)
  | 12, 4 => (19746655315298524118663881 / 975828369140625 : ℚ)
  | 13, 0 => (1018464428032 / 21 : ℚ)
  | 13, 1 => (1172852312963281 / 28875 : ℚ)
  | 13, 2 => (120192186329956742 / 3609375 : ℚ)
  | 13, 3 => (1448964482790663574741 / 54591796875 : ℚ)
  | 13, 4 => (1526941586557473539035612 / 75063720703125 : ℚ)
  | 14, 0 => 50448102400
  | 14, 1 => (57816325760608 / 1375 : ℚ)
  | 14, 2 => (64741086186884743 / 1890625 : ℚ)
  | 14, 3 => (70270666557816949627 / 2599609375 : ℚ)
  | 14, 4 => (72956550199729163943274 / 3574462890625 : ℚ)
  | _, _ => 0

theorem c4BandACoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (15443566539252696447104 / 900558759375 : ℚ) ≤ c4BandACoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandACoeff]

theorem c4BandA_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial (((10 : ℝ) / 3)+((1 : ℝ) / 6)*u) (((1 : ℝ) / 22000)*v) = bernsteinBoxEval 14 4 c4BandACoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandACoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandA_box_pos {x y : ℝ} (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ ((7 : ℝ) / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-((10 : ℝ) / 3))/((1 : ℝ) / 6)
  let v := y/((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 6))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 22000))]; exact hy1
  rw [show x=((10 : ℝ) / 3)+((1 : ℝ) / 6)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 22000)*v by dsimp [v]; field_simp; ring, c4BandA_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(15443566539252696447104 / 900558759375 : ℚ)) hu0 hu1 hv0 hv1 c4BandACoeff_floor

def c4BandBCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 50448102400
  | 0, 1 => (16993069226768 / 375 : ℚ)
  | 0, 2 => (68181328222649581 / 1687500 : ℚ)
  | 0, 3 => (67801529729964316667 / 1898437500 : ℚ)
  | 0, 4 => (33367070195457063574751 / 1067871093750 : ℚ)
  | 1, 0 => (394082439168 / 7 : ℚ)
  | 1, 1 => (87869660289527 / 1750 : ℚ)
  | 1, 2 => (43690670713202747 / 984375 : ℚ)
  | 1, 3 => (34388404177558940591 / 885937500 : ℚ)
  | 1, 4 => (8348624510834627774623 / 249169921875 : ℚ)
  | 2, 0 => (5716550650880 / 91 : ℚ)
  | 2, 1 => (1897704482441512 / 34125 : ℚ)
  | 2, 2 => (14958206681048310499 / 307125000 : ℚ)
  | 2, 3 => (2909203001480313304033 / 69103125000 : ℚ)
  | 2, 4 => (6957094628612342171021297 / 194352539062500 : ℚ)
  | 3, 0 => (490611627008 / 7 : ℚ)
  | 3, 1 => (16805096305056889 / 273000 : ℚ)
  | 3, 2 => (32788528783032307423 / 614250000 : ℚ)
  | 3, 3 => (2421517109280746383763 / 53156250000 : ℚ)
  | 3, 4 => (2960477319800540357728801 / 77741015625000 : ℚ)
  | 4, 0 => (78261798364800 / 1001 : ℚ)
  | 4, 1 => (8520894482392648 / 125125 : ℚ)
  | 4, 2 => (65795309509747962979 / 1126125000 : ℚ)
  | 4, 3 => (62286188050664138826989 / 1266890625000 : ℚ)
  | 4, 4 => (28728309958402741702307009 / 712625976562500 : ℚ)
  | 5, 0 => (87285288748928 / 1001 : ℚ)
  | 5, 1 => (113042664924995807 / 1501500 : ℚ)
  | 5, 2 => (53931899914367310527 / 844593750 : ℚ)
  | 5, 3 => (25133893743073410859313 / 475083984375 : ℚ)
  | 5, 4 => (22678446639760684105881826 / 534469482421875 : ℚ)
  | 6, 0 => (97327402324608 / 1001 : ℚ)
  | 6, 1 => (6244164388896019 / 75075 : ℚ)
  | 6, 2 => (29423672704612101922 / 422296875 : ℚ)
  | 6, 3 => (26955391922861238902774 / 475083984375 : ℚ)
  | 6, 4 => (2155366069941161599133576 / 48588134765625 : ℚ)
  | 7, 0 => (15499676699904 / 143 : ℚ)
  | 7, 1 => (3282278196371633 / 35750 : ℚ)
  | 7, 2 => (1526081912068914812 / 20109375 : ℚ)
  | 7, 3 => (1371399590100362698576 / 22623046875 : ℚ)
  | 7, 4 => (1170804205284730128721586 / 25450927734375 : ℚ)
  | 8, 0 => (120916983418368 / 1001 : ℚ)
  | 8, 1 => (2923963873098232 / 28875 : ℚ)
  | 8, 2 => (34836651527524805912 / 422296875 : ℚ)
  | 8, 3 => (6127284621012302159576 / 95016796875 : ℚ)
  | 8, 4 => (3606964249033001967095888 / 76352783203125 : ℚ)
  | 9, 0 => (19245424957184 / 143 : ℚ)
  | 9, 1 => (5983694603510336 / 53625 : ℚ)
  | 9, 2 => (37785516031982142016 / 422296875 : ℚ)
  | 9, 3 => (32428482738662610420032 / 475083984375 : ℚ)
  | 9, 4 => (25616769191847809522448256 / 534469482421875 : ℚ)
  | 10, 0 => (150046825830144 / 1001 : ℚ)
  | 10, 1 => (1182296729868544 / 9625 : ℚ)
  | 10, 2 => (13628314491136540928 / 140765625 : ℚ)
  | 10, 3 => (11375756932373938369792 / 158361328125 : ℚ)
  | 10, 4 => (1706384636111825769727744 / 35631298828125 : ℚ)
  | 11, 0 => 166897276160
  | 11, 1 => (4609590519869696 / 34125 : ℚ)
  | 11, 2 => (4010914337261970688 / 38390625 : ℚ)
  | 11, 3 => (3242919810604628433152 / 43189453125 : ℚ)
  | 11, 4 => (2279089564109529468767488 / 48588134765625 : ℚ)
  | 12, 0 => (2414889890432 / 13 : ℚ)
  | 12, 1 => (202532023268992 / 1365 : ℚ)
  | 12, 2 => (4315380233405844608 / 38390625 : ℚ)
  | 12, 3 => (480357709001219784064 / 6169921875 : ℚ)
  | 12, 4 => (434531880825949767196288 / 9717626953125 : ℚ)
  | 13, 0 => (1446767149440 / 7 : ℚ)
  | 13, 1 => (28486755476864 / 175 : ℚ)
  | 13, 2 => (118653391753361792 / 984375 : ℚ)
  | 13, 3 => (88532374257174392704 / 1107421875 : ℚ)
  | 13, 4 => (51082893681460986887552 / 1245849609375 : ℚ)
  | 14, 0 => 229870589824
  | 14, 1 => (66882928487552 / 375 : ℚ)
  | 14, 2 => (54324930330431104 / 421875 : ℚ)
  | 14, 3 => (38497953898498013312 / 474609375 : ℚ)
  | 14, 4 => (755758098378452266624 / 21357421875 : ℚ)
  | _, _ => 0

theorem c4BandBCoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (33367070195457063574751 / 1067871093750 : ℚ) ≤ c4BandBCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandBCoeff]

theorem c4BandB_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial (((7 : ℝ) / 2)+((1 : ℝ) / 2)*u) (((1 : ℝ) / 36000)*v) = bernsteinBoxEval 14 4 c4BandBCoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandBCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandB_box_pos {x y : ℝ} (hx0 : ((7 : ℝ) / 2) ≤ x) (hx1 : x ≤ (4 : ℝ)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 36000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-((7 : ℝ) / 2))/((1 : ℝ) / 2)
  let v := y/((1 : ℝ) / 36000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 2))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 36000))]; exact hy1
  rw [show x=((7 : ℝ) / 2)+((1 : ℝ) / 2)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 36000)*v by dsimp [v]; field_simp; ring, c4BandB_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(33367070195457063574751 / 1067871093750 : ℚ)) hu0 hu1 hv0 hv1 c4BandBCoeff_floor

def c4BandCCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 229870589824
  | 0, 1 => (136424665128832 / 625 : ℚ)
  | 0, 2 => (80775835213326208 / 390625 : ℚ)
  | 0, 3 => (47702778406241427328 / 244140625 : ℚ)
  | 0, 4 => (1123613034252505850752 / 6103515625 : ℚ)
  | 1, 0 => (1771421108096 / 7 : ℚ)
  | 1, 1 => (1048929474236288 / 4375 : ℚ)
  | 1, 2 => (123901246482792832 / 546875 : ℚ)
  | 1, 3 => (364835754402331336064 / 1708984375 : ℚ)
  | 1, 4 => (214169433176782319748992 / 1068115234375 : ℚ)
  | 2, 0 => (25345232158080 / 91 : ℚ)
  | 2, 1 => (1151729100483456 / 4375 : ℚ)
  | 2, 2 => (8819661416351101824 / 35546875 : ℚ)
  | 2, 3 => (5178792078756519354048 / 22216796875 : ℚ)
  | 2, 4 => (432869155128765172025472 / 1983642578125 : ℚ)
  | 3, 0 => (27887837346816 / 91 : ℚ)
  | 3, 1 => (657356504997888 / 2275 : ℚ)
  | 3, 2 => (742607766941590464 / 2734375 : ℚ)
  | 3, 3 => (226045040358503155392 / 888671875 : ℚ)
  | 3, 4 => (3294881146365394198747488 / 13885498046875 : ℚ)
  | 4, 0 => (337450846642944 / 1001 : ℚ)
  | 4, 1 => (39668779294763328 / 125125 : ℚ)
  | 4, 2 => (23235699278250858936 / 78203125 : ℚ)
  | 4, 3 => (9683696480830091093259 / 34912109375 : ℚ)
  | 4, 4 => (7875127203784024720557432 / 30548095703125 : ℚ)
  | 5, 0 => (53014802123520 / 143 : ℚ)
  | 5, 1 => (217538790106080312 / 625625 : ℚ)
  | 5, 2 => (18147982604562650277 / 55859375 : ℚ)
  | 5, 3 => (590923653291024000309459 / 1955078125000 : ℚ)
  | 5, 4 => (42737608964856362951692512 / 152740478515625 : ℚ)
  | 6, 0 => (407998873681408 / 1001 : ℚ)
  | 6, 1 => (47699313940296677 / 125125 : ℚ)
  | 6, 2 => (44426117392945569143 / 125125000 : ℚ)
  | 6, 3 => (5147532698802361925782057 / 15640625000000 : ℚ)
  | 6, 4 => (28516931005906714767794639 / 93994140625000 : ℚ)
  | 7, 0 => (64062146583296 / 143 : ℚ)
  | 7, 1 => (597409335786795239 / 1430000 : ℚ)
  | 7, 2 => (1386386549420195576009 / 3575000000 : ℚ)
  | 7, 3 => (2560286075716524486128833 / 7150000000000 : ℚ)
  | 7, 4 => (367122671312184596454075049 / 1117187500000000 : ℚ)
  | 8, 0 => (492736501736064 / 1001 : ℚ)
  | 8, 1 => (2290474424846317221 / 5005000 : ℚ)
  | 8, 2 => (2648371067480483216721 / 6256250000 : ℚ)
  | 8, 3 => (48708734793854730046338591 / 125125000000000 : ℚ)
  | 8, 4 => (6950904819600673208480258079 / 19550781250000000 : ℚ)
  | 9, 0 => (541255890400640 / 1001 : ℚ)
  | 9, 1 => (771684792004255639 / 1540000 : ℚ)
  | 9, 2 => (1155653791993502684147 / 2502500000 : ℚ)
  | 9, 3 => (211627502682268703815460659 / 500500000000000 : ℚ)
  | 9, 4 => (4292137159427323341266742277 / 11171875000000000 : ℚ)
  | 10, 0 => (594376237339264 / 1001 : ℚ)
  | 10, 1 => (2744913025211747387 / 5005000 : ℚ)
  | 10, 2 => (14398946590334877942317 / 28600000000 : ℚ)
  | 10, 3 => (2050525498920688450837799 / 4468750000000 : ℚ)
  | 10, 4 => (16212743980207561717038124567 / 39101562500000000 : ℚ)
  | 11, 0 => (59319410163456 / 91 : ℚ)
  | 11, 1 => (2183903964132671181 / 3640000 : ℚ)
  | 11, 2 => (3993174998361412015119 / 7280000000 : ℚ)
  | 11, 3 => (4527066481182602377835817 / 9100000000000 : ℚ)
  | 11, 4 => (4538562569203739451668457 / 10156250000000 : ℚ)
  | 12, 0 => (65101750935552 / 91 : ℚ)
  | 12, 1 => (298502808346301823 / 455000 : ℚ)
  | 12, 2 => (10868771900186180737317 / 18200000000 : ℚ)
  | 12, 3 => (3064477039827047507515383 / 5687500000000 : ℚ)
  | 12, 4 => (1709526143941261822223629389 / 3554687500000000 : ℚ)
  | 13, 0 => (5494289909760 / 7 : ℚ)
  | 13, 1 => (50191702934982759 / 70000 : ℚ)
  | 13, 2 => (454796441074900492731 / 700000000 : ℚ)
  | 13, 3 => (291476517196212193335129 / 500000000000 : ℚ)
  | 13, 4 => (282600762713444305166316219 / 546875000000000 : ℚ)
  | 14, 0 => 860876688384
  | 14, 1 => (1958201629726779 / 2500 : ℚ)
  | 14, 2 => (14126481218295015957 / 20000000 : ℚ)
  | 14, 3 => (78750843923368596153987 / 125000000000 : ℚ)
  | 14, 4 => (676670604539715374409441 / 1220703125000 : ℚ)
  | _, _ => 0

theorem c4BandCCoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (1123613034252505850752 / 6103515625 : ℚ) ≤ c4BandCCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandCCoeff]

theorem c4BandC_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial ((4 : ℝ)+((1 : ℝ) / 2)*u) (((1 : ℝ) / 160000)*v) = bernsteinBoxEval 14 4 c4BandCCoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandCCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandC_box_pos {x y : ℝ} (hx0 : (4 : ℝ) ≤ x) (hx1 : x ≤ ((9 : ℝ) / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 160000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-(4 : ℝ))/((1 : ℝ) / 2)
  let v := y/((1 : ℝ) / 160000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 2))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 160000))]; exact hy1
  rw [show x=(4 : ℝ)+((1 : ℝ) / 2)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 160000)*v by dsimp [v]; field_simp; ring, c4BandC_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(1123613034252505850752 / 6103515625 : ℚ)) hu0 hu1 hv0 hv1 c4BandCCoeff_floor

def c4BandDCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 860876688384
  | 0, 1 => (18443697375933558 / 21875 : ℚ)
  | 0, 2 => (315987839796021081957 / 382812500 : ℚ)
  | 0, 3 => (33821349151791355526856573 / 41870117187500 : ℚ)
  | 0, 4 => (361844513503516987641290934459 / 457954406738281250 : ℚ)
  | 1, 0 => (6557983727616 / 7 : ℚ)
  | 1, 1 => (56159907827351373 / 61250 : ℚ)
  | 1, 2 => (12018072796199239011759 / 13398437500 : ℚ)
  | 1, 3 => (2623140530439290369316153 / 2990722656250 : ℚ)
  | 1, 4 => (2748060240624450598710926468547 / 3205680847167968750 : ℚ)
  | 2, 0 => (92757790199808 / 91 : ℚ)
  | 2, 1 => (1984377028099605201 / 1990625 : ℚ)
  | 2, 2 => (339458290450946191846773 / 348359375000 : ℚ)
  | 2, 3 => (1451035890353244660406238097 / 1524072265625000 : ℚ)
  | 2, 4 => (11070361463616296237635080254001 / 11906814575195312500 : ℚ)
  | 3, 0 => (100900098670848 / 91 : ℚ)
  | 3, 1 => (17255254108682576499 / 15925000 : ℚ)
  | 3, 2 => (147470310577017469464897 / 139343750000 : ℚ)
  | 3, 3 => (629841568533315945584552247 / 609628906250000 : ℚ)
  | 3, 4 => (168035430386791793336731494555639 / 166695404052734375000 : ℚ)
  | 4, 0 => (1207060804037248 / 1001 : ℚ)
  | 4, 1 => (1983258475344018308 / 1684375 : ℚ)
  | 4, 2 => (880650393121354864840147 / 766390625000 : ℚ)
  | 4, 3 => (93948671941444975630508177263 / 83823974609375000 : ℚ)
  | 4, 4 => (1001663937893331266769685788783637 / 916824722290039062500 : ℚ)
  | 5, 0 => (187490335574144 / 143 : ℚ)
  | 5, 1 => (112039569215852322817 / 87587500 : ℚ)
  | 5, 2 => (95590772018837750024939 / 76639062500 : ℚ)
  | 5, 3 => (50942252994279554784792414157 / 41911987304687500 : ℚ)
  | 5, 4 => (542618485810981102096123586251459 / 458412361145019531250 : ℚ)
  | 6, 0 => (1426681041720960 / 1001 : ℚ)
  | 6, 1 => (6084418815132993516 / 4379375 : ℚ)
  | 6, 2 => (259324001656506415718409 / 191597656250 : ℚ)
  | 6, 3 => (44181848010829600674027057 / 33529589843750 : ℚ)
  | 6, 4 => (58767562919572734968478053619243 / 45841236114501953125 : ℚ)
  | 7, 0 => (221503359810560 / 143 : ℚ)
  | 7, 1 => (1887627875425631203 / 1251250 : ℚ)
  | 7, 2 => (20094343255262579938018 / 13685546875 : ℚ)
  | 7, 3 => (427520707670437167183375974 / 299371337890625 : ℚ)
  | 7, 4 => (699159599430579875822572754902 / 503749847412109375 : ℚ)
  | 8, 0 => (1684731463390720 / 1001 : ℚ)
  | 8, 1 => (1434386477050045856 / 875875 : ℚ)
  | 8, 2 => (152546228316035767392908 / 95798828125 : ℚ)
  | 8, 3 => (8421289066061149721675548 / 5443115234375 : ℚ)
  | 8, 4 => (68854282356903990098857184863304 / 45841236114501953125 : ℚ)
  | 9, 0 => (261447941433600 / 143 : ℚ)
  | 9, 1 => (62267746720728672 / 35035 : ℚ)
  | 9, 2 => (33077266977731690811096 / 19159765625 : ℚ)
  | 9, 3 => (2160827166395118821242248 / 1289599609375 : ℚ)
  | 9, 4 => (2128165884967522407182379874224 / 1309749603271484375 : ℚ)
  | 10, 0 => (1987629894240000 / 1001 : ℚ)
  | 10, 1 => (13511828534268096 / 7007 : ℚ)
  | 10, 2 => (1434017023535582109168 / 766390625 : ℚ)
  | 10, 3 => (6082393914963886193922096 / 3352958984375 : ℚ)
  | 10, 4 => (644364149640585424662919998624 / 366729888916015625 : ℚ)
  | 11, 0 => (196197835200000 / 91 : ℚ)
  | 11, 1 => (102490085540880 / 49 : ℚ)
  | 11, 2 => (2173088866936961136 / 1071875 : ℚ)
  | 11, 3 => (119684271925957581085392 / 60962890625 : ℚ)
  | 11, 4 => (12663613217281608079391724384 / 6667816162109375 : ℚ)
  | 12, 0 => (30426090000000 / 13 : ℚ)
  | 12, 1 => (1444809352525440 / 637 : ℚ)
  | 12, 2 => (6119874412158788448 / 2786875 : ℚ)
  | 12, 3 => (129480170510339821715808 / 60962890625 : ℚ)
  | 12, 4 => (210498956764405464116677056 / 102581787109375 : ℚ)
  | 13, 0 => (17780702000000 / 7 : ℚ)
  | 13, 1 => (120484968468800 / 49 : ℚ)
  | 13, 2 => (509742871041548096 / 214375 : ℚ)
  | 13, 3 => (2154238620949728439232 / 937890625 : ℚ)
  | 13, 4 => (227335748589636294333064448 / 102581787109375 : ℚ)
  | 14, 0 => 2756110000000
  | 14, 1 => (18654327760000 / 7 : ℚ)
  | 14, 2 => (15764974070110976 / 6125 : ℚ)
  | 14, 3 => (13307424845808652288 / 5359375 : ℚ)
  | 14, 4 => (7011723495493292005793408 / 2930908203125 : ℚ)
  | _, _ => 0

theorem c4BandDCoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (361844513503516987641290934459 / 457954406738281250 : ℚ) ≤ c4BandDCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandDCoeff]

theorem c4BandD_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial (((9 : ℝ) / 2)+((1 : ℝ) / 2)*u) (((1 : ℝ) / 700000)*v) = bernsteinBoxEval 14 4 c4BandDCoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandDCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandD_box_pos {x y : ℝ} (hx0 : ((9 : ℝ) / 2) ≤ x) (hx1 : x ≤ (5 : ℝ)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 700000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-((9 : ℝ) / 2))/((1 : ℝ) / 2)
  let v := y/((1 : ℝ) / 700000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 2))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 700000))]; exact hy1
  rw [show x=((9 : ℝ) / 2)+((1 : ℝ) / 2)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 700000)*v by dsimp [v]; field_simp; ring, c4BandD_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(361844513503516987641290934459 / 457954406738281250 : ℚ)) hu0 hu1 hv0 hv1 c4BandDCoeff_floor

noncomputable def baseOuter0UpperPolynomial (x y : ℝ) : ℝ := -32*x*y + 6*x + 12*y - 9

def baseOuter0UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => 21
  | 0, 1 => 6
  | 1, 0 => (15749963 / 750000 : ℚ)
  | 1, 1 => (562499 / 93750 : ℚ)
  | _, _ => 0

theorem baseOuter0UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (15749963 / 750000 : ℚ) ≤ baseOuter0UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter0UpperCoeff]

theorem baseOuter0UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (1+1), 0 ≤ baseOuter0UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter0UpperCoeff]

theorem baseOuter0Upper_representation (v z : ℝ) : baseOuter0UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 1 baseOuter0UpperCoeff v z := by
  norm_num [baseOuter0UpperPolynomial, bernsteinHalfstripEval, baseOuter0UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter0Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter0UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(15749963 / 750000 : ℚ)) hv0 hv1 hz baseOuter0UpperCoeff_const_floor baseOuter0UpperCoeff_nonneg
  rw [← baseOuter0Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter0LowerPolynomial (x y : ℝ) : ℝ := 32*x*y + 10*x - 12*y - 15

def baseOuter0LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => 35
  | 0, 1 => 10
  | 1, 0 => (26250037 / 750000 : ℚ)
  | 1, 1 => (937501 / 93750 : ℚ)
  | _, _ => 0

theorem baseOuter0LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), 35 ≤ baseOuter0LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter0LowerCoeff]

theorem baseOuter0LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (1+1), 0 ≤ baseOuter0LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter0LowerCoeff]

theorem baseOuter0Lower_representation (v z : ℝ) : baseOuter0LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 1 baseOuter0LowerCoeff v z := by
  norm_num [baseOuter0LowerPolynomial, bernsteinHalfstripEval, baseOuter0LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter0Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter0LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<35) hv0 hv1 hz baseOuter0LowerCoeff_const_floor baseOuter0LowerCoeff_nonneg
  rw [← baseOuter0Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter1UpperPolynomial (x y : ℝ) : ℝ := 256*x^2*y + 4*x^2 - 240*x*y + 40*x*(2*x - 3) - 15*x + 30*y + 15/2

def baseOuter1UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2865 / 2 : ℚ)
  | 0, 1 => 705
  | 0, 2 => 84
  | 1, 0 => (429750523 / 300000 : ℚ)
  | 1, 1 => (26437529 / 37500 : ℚ)
  | 1, 2 => (3937504 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter1UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (2865 / 2 : ℚ) ≤ baseOuter1UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter1UpperCoeff]

theorem baseOuter1UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (2+1), 0 ≤ baseOuter1UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter1UpperCoeff]

theorem baseOuter1Upper_representation (v z : ℝ) : baseOuter1UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 2 baseOuter1UpperCoeff v z := by
  norm_num [baseOuter1UpperPolynomial, bernsteinHalfstripEval, baseOuter1UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter1Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter1UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(2865 / 2 : ℚ)) hv0 hv1 hz baseOuter1UpperCoeff_const_floor baseOuter1UpperCoeff_nonneg
  rw [← baseOuter1Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter1LowerPolynomial (x y : ℝ) : ℝ := -256*x^2*y - 4*x^2 + 240*x*y + 40*x*(2*x - 3) + 15*x - 30*y - 15/2

def baseOuter1LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2735 / 2 : ℚ)
  | 0, 1 => 655
  | 0, 2 => 76
  | 1, 0 => (410249477 / 300000 : ℚ)
  | 1, 1 => (24562471 / 37500 : ℚ)
  | 1, 2 => (3562496 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter1LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (410249477 / 300000 : ℚ) ≤ baseOuter1LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter1LowerCoeff]

theorem baseOuter1LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (2+1), 0 ≤ baseOuter1LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter1LowerCoeff]

theorem baseOuter1Lower_representation (v z : ℝ) : baseOuter1LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 2 baseOuter1LowerCoeff v z := by
  norm_num [baseOuter1LowerPolynomial, bernsteinHalfstripEval, baseOuter1LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter1Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter1LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(410249477 / 300000 : ℚ)) hv0 hv1 hz baseOuter1LowerCoeff_const_floor baseOuter1LowerCoeff_nonneg
  rw [← baseOuter1Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter2UpperPolynomial (x y : ℝ) : ℝ := -2048*x^3*y - 8*x^3 + 3584*x^2*y + 400*x^2*(2*x - 3) + 56*x^2 - 1320*x*y - 165*x/2 + 75*y + 75/4

def baseOuter2UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (280025 / 4 : ℚ)
  | 0, 1 => (95755 / 2 : ℚ)
  | 0, 2 => 10736
  | 0, 3 => 792
  | 1, 0 => (8400743083 / 120000 : ℚ)
  | 1, 1 => (3590809523 / 75000 : ℚ)
  | 1, 2 => (503249576 / 46875 : ℚ)
  | 1, 3 => (37124968 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter2UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (8400743083 / 120000 : ℚ) ≤ baseOuter2UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter2UpperCoeff]

theorem baseOuter2UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (3+1), 0 ≤ baseOuter2UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter2UpperCoeff]

theorem baseOuter2Upper_representation (v z : ℝ) : baseOuter2UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 3 baseOuter2UpperCoeff v z := by
  norm_num [baseOuter2UpperPolynomial, bernsteinHalfstripEval, baseOuter2UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter2Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter2UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(8400743083 / 120000 : ℚ)) hv0 hv1 hz baseOuter2UpperCoeff_const_floor baseOuter2UpperCoeff_nonneg
  rw [← baseOuter2Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter2LowerPolynomial (x y : ℝ) : ℝ := 2048*x^3*y + 8*x^3 - 3584*x^2*y + 400*x^2*(2*x - 3) - 56*x^2 + 1320*x*y + 165*x/2 - 75*y - 75/4

def baseOuter2LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (279975 / 4 : ℚ)
  | 0, 1 => (96245 / 2 : ℚ)
  | 0, 2 => 10864
  | 0, 3 => 808
  | 1, 0 => (8399256917 / 120000 : ℚ)
  | 1, 1 => (3609190477 / 75000 : ℚ)
  | 1, 2 => (509250424 / 46875 : ℚ)
  | 1, 3 => (37875032 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter2LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (279975 / 4 : ℚ) ≤ baseOuter2LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter2LowerCoeff]

theorem baseOuter2LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (3+1), 0 ≤ baseOuter2LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter2LowerCoeff]

theorem baseOuter2Lower_representation (v z : ℝ) : baseOuter2LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 3 baseOuter2LowerCoeff v z := by
  norm_num [baseOuter2LowerPolynomial, bernsteinHalfstripEval, baseOuter2LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter2Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter2LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(279975 / 4 : ℚ)) hv0 hv1 hz baseOuter2LowerCoeff_const_floor baseOuter2LowerCoeff_nonneg
  rw [← baseOuter2Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter3UpperPolynomial (x y : ℝ) : ℝ := 16384*x^4*y + 16*x^4 - 46080*x^3*y + 4000*x^3*(2*x - 3) - 180*x^3 + 33856*x^2*y + 529*x^2 - 6540*x*y - 1635*x/4 + 375*y/2 + 375/8

def baseOuter3UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (27989825 / 8 : ℚ)
  | 0, 1 => (12397525 / 4 : ℚ)
  | 0, 2 => 1020229
  | 0, 3 => 148140
  | 0, 4 => 8016
  | 1, 0 => (839695173511 / 240000 : ℚ)
  | 1, 1 => (154969146967 / 50000 : ℚ)
  | 1, 2 => (47823262504 / 46875 : ℚ)
  | 1, 3 => (277762676 / 1875 : ℚ)
  | 1, 4 => (375750256 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter3UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (27989825 / 8 : ℚ) ≤ baseOuter3UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter3UpperCoeff]

theorem baseOuter3UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (4+1), 0 ≤ baseOuter3UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter3UpperCoeff]

theorem baseOuter3Upper_representation (v z : ℝ) : baseOuter3UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 4 baseOuter3UpperCoeff v z := by
  norm_num [baseOuter3UpperPolynomial, bernsteinHalfstripEval, baseOuter3UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter3Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter3UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(27989825 / 8 : ℚ)) hv0 hv1 hz baseOuter3UpperCoeff_const_floor baseOuter3UpperCoeff_nonneg
  rw [← baseOuter3Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter3LowerPolynomial (x y : ℝ) : ℝ := -16384*x^4*y - 16*x^4 + 46080*x^3*y + 4000*x^3*(2*x - 3) + 180*x^3 - 33856*x^2*y - 529*x^2 + 6540*x*y + 1635*x/4 - 375*y/2 - 375/8

def baseOuter3LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (28010175 / 8 : ℚ)
  | 0, 1 => (12402475 / 4 : ℚ)
  | 0, 2 => 1019771
  | 0, 3 => 147860
  | 0, 4 => 7984
  | 1, 0 => (840304826489 / 240000 : ℚ)
  | 1, 1 => (155030853033 / 50000 : ℚ)
  | 1, 2 => (47801737496 / 46875 : ℚ)
  | 1, 3 => (277237324 / 1875 : ℚ)
  | 1, 4 => (374249744 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter3LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (840304826489 / 240000 : ℚ) ≤ baseOuter3LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter3LowerCoeff]

theorem baseOuter3LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (4+1), 0 ≤ baseOuter3LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter3LowerCoeff]

theorem baseOuter3Lower_representation (v z : ℝ) : baseOuter3LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 4 baseOuter3LowerCoeff v z := by
  norm_num [baseOuter3LowerPolynomial, bernsteinHalfstripEval, baseOuter3LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter3Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter3LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(840304826489 / 240000 : ℚ)) hv0 hv1 hz baseOuter3LowerCoeff_const_floor baseOuter3LowerCoeff_nonneg
  rw [← baseOuter3Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter4UpperPolynomial (x y : ℝ) : ℝ := -131072*x^5*y - 32*x^5 + 540672*x^4*y + 40000*x^4*(2*x - 3) + 528*x^4 - 662528*x^3*y - 2588*x^3 + 272384*x^2*y + 4256*x^2 - 30930*x*y - 15465*x/8 + 1875*y/4 + 1875/16

def baseOuter4UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2800053625 / 16 : ℚ)
  | 0, 1 => (1520084215 / 8 : ℚ)
  | 0, 2 => 82004636
  | 0, 3 => 17599972
  | 0, 4 => 1879728
  | 0, 5 => 79968
  | 1, 0 => (28000528365169 / 160000 : ℚ)
  | 1, 1 => (57003139436431 / 300000 : ℚ)
  | 1, 2 => (3843965868676 / 46875 : ℚ)
  | 1, 3 => (824998334108 / 46875 : ℚ)
  | 1, 4 => (88112207248 / 46875 : ℚ)
  | 1, 5 => (3748497952 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter4UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (28000528365169 / 160000 : ℚ) ≤ baseOuter4UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter4UpperCoeff]

theorem baseOuter4UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (5+1), 0 ≤ baseOuter4UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter4UpperCoeff]

theorem baseOuter4Upper_representation (v z : ℝ) : baseOuter4UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 5 baseOuter4UpperCoeff v z := by
  norm_num [baseOuter4UpperPolynomial, bernsteinHalfstripEval, baseOuter4UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter4Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter4UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(28000528365169 / 160000 : ℚ)) hv0 hv1 hz baseOuter4UpperCoeff_const_floor baseOuter4UpperCoeff_nonneg
  rw [← baseOuter4Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter4LowerPolynomial (x y : ℝ) : ℝ := 131072*x^5*y + 32*x^5 - 540672*x^4*y + 40000*x^4*(2*x - 3) - 528*x^4 + 662528*x^3*y + 2588*x^3 - 272384*x^2*y - 4256*x^2 + 30930*x*y + 15465*x/8 - 1875*y/4 - 1875/16

def baseOuter4LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2799946375 / 16 : ℚ)
  | 0, 1 => (1519915785 / 8 : ℚ)
  | 0, 2 => 81995364
  | 0, 3 => 17600028
  | 0, 4 => 1880272
  | 0, 5 => 80032
  | 1, 0 => (27999471634831 / 160000 : ℚ)
  | 1, 1 => (56996860563569 / 300000 : ℚ)
  | 1, 2 => (3843534131324 / 46875 : ℚ)
  | 1, 3 => (825001665892 / 46875 : ℚ)
  | 1, 4 => (88137792752 / 46875 : ℚ)
  | 1, 5 => (3751502048 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter4LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (2799946375 / 16 : ℚ) ≤ baseOuter4LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter4LowerCoeff]

theorem baseOuter4LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (5+1), 0 ≤ baseOuter4LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter4LowerCoeff]

theorem baseOuter4Lower_representation (v z : ℝ) : baseOuter4LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 5 baseOuter4LowerCoeff v z := by
  norm_num [baseOuter4LowerPolynomial, bernsteinHalfstripEval, baseOuter4LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter4Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter4LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(2799946375 / 16 : ℚ)) hv0 hv1 hz baseOuter4LowerCoeff_const_floor baseOuter4LowerCoeff_nonneg
  rw [← baseOuter4Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter5UpperPolynomial (x y : ℝ) : ℝ := 1048576*x^6*y + 64*x^6 - 5963776*x^5*y + 400000*x^5*(2*x - 3) - 1456*x^5 + 10977280*x^4*y + 10720*x^4 - 7810560*x^3*y - 30510*x^3 + 2017936*x^2*y + 126121*x^2/4 - 142935*x*y - 142935*x/16 + 9375*y/8 + 9375/32

def baseOuter5UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (280002564225 / 32 : ℚ)
  | 0, 1 => (180000449905 / 16 : ℚ)
  | 0, 2 => (23999847521 / 4 : ℚ)
  | 0, 3 => 1699979890
  | 0, 4 => 269998320
  | 0, 5 => 22800464
  | 0, 6 => 800064
  | 1, 0 => (8400078104802767 / 960000 : ℚ)
  | 1, 1 => (1350003612162877 / 120000 : ℚ)
  | 1, 2 => (281248274185649 / 46875 : ℚ)
  | 1, 3 => (15937315663222 / 9375 : ℚ)
  | 1, 4 => (843745015728 / 3125 : ℚ)
  | 1, 5 => (1068772148336 / 46875 : ℚ)
  | 1, 6 => (37503016384 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter5UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (280002564225 / 32 : ℚ) ≤ baseOuter5UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter5UpperCoeff]

theorem baseOuter5UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (6+1), 0 ≤ baseOuter5UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter5UpperCoeff]

theorem baseOuter5Upper_representation (v z : ℝ) : baseOuter5UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 6 baseOuter5UpperCoeff v z := by
  norm_num [baseOuter5UpperPolynomial, bernsteinHalfstripEval, baseOuter5UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter5Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter5UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(280002564225 / 32 : ℚ)) hv0 hv1 hz baseOuter5UpperCoeff_const_floor baseOuter5UpperCoeff_nonneg
  rw [← baseOuter5Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter5LowerPolynomial (x y : ℝ) : ℝ := -1048576*x^6*y - 64*x^6 + 5963776*x^5*y + 400000*x^5*(2*x - 3) + 1456*x^5 - 10977280*x^4*y - 10720*x^4 + 7810560*x^3*y + 30510*x^3 - 2017936*x^2*y - 126121*x^2/4 + 142935*x*y + 142935*x/16 - 9375*y/8 - 9375/32

def baseOuter5LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (279997435775 / 32 : ℚ)
  | 0, 1 => (179999550095 / 16 : ℚ)
  | 0, 2 => (24000152479 / 4 : ℚ)
  | 0, 3 => 1700020110
  | 0, 4 => 270001680
  | 0, 5 => 22799536
  | 0, 6 => 799936
  | 1, 0 => (8399921895197233 / 960000 : ℚ)
  | 1, 1 => (1349996387837123 / 120000 : ℚ)
  | 1, 2 => (281251725814351 / 46875 : ℚ)
  | 1, 3 => (15937684336778 / 9375 : ℚ)
  | 1, 4 => (843754984272 / 3125 : ℚ)
  | 1, 5 => (1068727851664 / 46875 : ℚ)
  | 1, 6 => (37496983616 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter5LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (8399921895197233 / 960000 : ℚ) ≤ baseOuter5LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter5LowerCoeff]

theorem baseOuter5LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (6+1), 0 ≤ baseOuter5LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter5LowerCoeff]

theorem baseOuter5Lower_representation (v z : ℝ) : baseOuter5LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 6 baseOuter5LowerCoeff v z := by
  norm_num [baseOuter5LowerPolynomial, bernsteinHalfstripEval, baseOuter5LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter5Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter5LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(8399921895197233 / 960000 : ℚ)) hv0 hv1 hz baseOuter5LowerCoeff_const_floor baseOuter5LowerCoeff_nonneg
  rw [← baseOuter5Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter6UpperPolynomial (x y : ℝ) : ℝ := -8388608*x^7*y - 128*x^7 + 62914560*x^6*y + 4000000*x^6*(2*x - 3) + 3840*x^6 - 162365440*x^5*y - 39640*x^5 + 177745920*x^4*y + 173580*x^4 - 82533248*x^3*y - 644791*x^3/2 + 14260064*x^2*y + 445627*x^2/2 - 1305165*x*y/2 - 1305165*x/32 + 46875*y/16 + 46875/64

def baseOuter6UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (27999979532825 / 64 : ℚ)
  | 0, 1 => (20799965525955 / 32 : ℚ)
  | 0, 2 => 412499473881
  | 0, 3 => (290000078409 / 2 : ℚ)
  | 0, 4 => 30500062580
  | 0, 5 => 3840008360
  | 0, 6 => 267999360
  | 0, 7 => 7999872
  | 1, 0 => (167999867138170559 / 384000 : ℚ)
  | 1, 1 => (779998642254078283 / 1200000 : ℚ)
  | 1, 2 => (12890607119228639 / 31250 : ℚ)
  | 1, 3 => (13593751696253911 / 93750 : ℚ)
  | 1, 4 => (95312677866052 / 3125 : ℚ)
  | 1, 5 => (36000070003288 / 9375 : ℚ)
  | 1, 6 => (2512493279104 / 9375 : ℚ)
  | 1, 7 => (374993868928 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter6UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (167999867138170559 / 384000 : ℚ) ≤ baseOuter6UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter6UpperCoeff]

theorem baseOuter6UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (7+1), 0 ≤ baseOuter6UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter6UpperCoeff]

theorem baseOuter6Upper_representation (v z : ℝ) : baseOuter6UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 7 baseOuter6UpperCoeff v z := by
  norm_num [baseOuter6UpperPolynomial, bernsteinHalfstripEval, baseOuter6UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter6Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter6UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(167999867138170559 / 384000 : ℚ)) hv0 hv1 hz baseOuter6UpperCoeff_const_floor baseOuter6UpperCoeff_nonneg
  rw [← baseOuter6Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter6LowerPolynomial (x y : ℝ) : ℝ := 8388608*x^7*y + 128*x^7 - 62914560*x^6*y + 4000000*x^6*(2*x - 3) - 3840*x^6 + 162365440*x^5*y + 39640*x^5 - 177745920*x^4*y - 173580*x^4 + 82533248*x^3*y + 644791*x^3/2 - 14260064*x^2*y - 445627*x^2/2 + 1305165*x*y/2 + 1305165*x/32 - 46875*y/16 - 46875/64

def baseOuter6LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (28000020467175 / 64 : ℚ)
  | 0, 1 => (20800034474045 / 32 : ℚ)
  | 0, 2 => 412500526119
  | 0, 3 => (289999921591 / 2 : ℚ)
  | 0, 4 => 30499937420
  | 0, 5 => 3839991640
  | 0, 6 => 268000640
  | 0, 7 => 8000128
  | 1, 0 => (168000132861829441 / 384000 : ℚ)
  | 1, 1 => (780001357745921717 / 1200000 : ℚ)
  | 1, 2 => (12890642880771361 / 31250 : ℚ)
  | 1, 3 => (13593748303746089 / 93750 : ℚ)
  | 1, 4 => (95312322133948 / 3125 : ℚ)
  | 1, 5 => (35999929996712 / 9375 : ℚ)
  | 1, 6 => (2512506720896 / 9375 : ℚ)
  | 1, 7 => (375006131072 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter6LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (28000020467175 / 64 : ℚ) ≤ baseOuter6LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter6LowerCoeff]

theorem baseOuter6LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (7+1), 0 ≤ baseOuter6LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter6LowerCoeff]

theorem baseOuter6Lower_representation (v z : ℝ) : baseOuter6LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 7 baseOuter6LowerCoeff v z := by
  norm_num [baseOuter6LowerPolynomial, bernsteinHalfstripEval, baseOuter6LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter6Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter6LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(28000020467175 / 64 : ℚ)) hv0 hv1 hz baseOuter6LowerCoeff_const_floor baseOuter6LowerCoeff_nonneg
  rw [← baseOuter6Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

end PF4.RobustThreeModeClosure.Generated
