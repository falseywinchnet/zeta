set_option linter.style.header false
namespace PF4.UnscaledOuterClosure.C4Data

noncomputable def c4MarginBase (x : ℝ) : ℝ :=
  ((-4050000000 : ℝ) + ((-10800000000 : ℝ) * (x ^ 2)) + ((-800000000 : ℝ) * (x ^ 4)) + ((-41287680 : ℝ) * (x ^ 7)) + ((-4718592 : ℝ) * (x ^ 9)) + ((786432 : ℝ) * (x ^ 10)) + ((17694720 : ℝ) * (x ^ 8)) + ((46448640 : ℝ) * (x ^ 6)) + ((4800000000 : ℝ) * (x ^ 3)) + ((10800000000 : ℝ) * x))

theorem c4MarginBase_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginBase x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginBase]
  positivity

noncomputable def c4MarginNeg1 (x : ℝ) : ℝ :=
  (((-312563957760 : ℝ) * (x ^ 8)) + ((-173237403648 : ℝ) * (x ^ 10)) + ((-15792537600 : ℝ) * (x ^ 6)) + ((-14077919232 : ℝ) * (x ^ 12)) + ((1528823808 : ℝ) * (x ^ 13)) + ((61970448384 : ℝ) * (x ^ 11)) + ((141059358720 : ℝ) * (x ^ 7)) + ((308900560896 : ℝ) * (x ^ 9)))

theorem c4MarginNeg1_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginNeg1 x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginNeg1]
  positivity

noncomputable def c4MarginPos2 (x : ℝ) : ℝ :=
  (((-58482889850880 : ℝ) * (x ^ 9)) + ((-35786792632320 : ℝ) * (x ^ 11)) + ((-9225319219200 : ℝ) * (x ^ 7)) + ((-3608024186880 : ℝ) * (x ^ 13)) + ((440301256704 : ℝ) * (x ^ 14)) + ((1061258526720 : ℝ) * (x ^ 6)) + ((14404832722944 : ℝ) * (x ^ 12)) + ((33577217556480 : ℝ) * (x ^ 8)) + ((57854526750720 : ℝ) * (x ^ 10)))

theorem c4MarginPos2_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginPos2 x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginPos2]
  positivity

noncomputable def c4MarginNeg3 (x : ℝ) : ℝ :=
  (((-519124442677248 : ℝ) * (x ^ 10)) + ((-305687754178560 : ℝ) * (x ^ 8)) + ((-124197569298432 : ℝ) * (x ^ 12)) + ((-16171558502400 : ℝ) * (x ^ 6)) + ((25048249270272 : ℝ) * (x ^ 13)) + ((103223163617280 : ℝ) * (x ^ 7)) + ((319756557090816 : ℝ) * (x ^ 11)) + ((522657825030144 : ℝ) * (x ^ 9)))

theorem c4MarginNeg3_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginNeg3 x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginNeg3]
  positivity

noncomputable def c4MarginPos4 (x : ℝ) : ℝ :=
  (((-316659348799488 : ℝ) * (x ^ 9)) + ((-173173081374720 : ℝ) * (x ^ 7)) + ((48704929136640 : ℝ) * (x ^ 6)) + ((211106232532992 : ℝ) * (x ^ 10)) + ((296868139499520 : ℝ) * (x ^ 8)))

theorem c4MarginPos4_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginPos4 x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginPos4]
  positivity

noncomputable def c4MarginDecay1 (x : ℝ) : ℝ :=
  (((-75370825329868800000000 : ℝ) * (x ^ 9)) + ((-53454922245734400000000 : ℝ) * (x ^ 11)) + ((-22175505727488000000000 : ℝ) * (x ^ 7)) + ((-10598188266464005324800 : ℝ) * (x ^ 13)) + ((-418683242213088952320 : ℝ) * (x ^ 15)) + ((-383758663680000000000 : ℝ) * (x ^ 5)) + ((-53726119667139870720 : ℝ) * (x ^ 16)) + ((-31211330995602063360 : ℝ) * (x ^ 18)) + ((-2605917341799677952 : ℝ) * (x ^ 20)) + ((-58462613796814848 : ℝ) * (x ^ 22)) + ((3606947894919168 : ℝ) * (x ^ 23)) + ((477645065334816768 : ℝ) * (x ^ 21)) + ((10387491577764249600 : ℝ) * (x ^ 19)) + ((67375995901213409280 : ℝ) * (x ^ 17)) + ((2835533191273387130880 : ℝ) * (x ^ 14)) + ((5043709181952000000000 : ℝ) * (x ^ 6)) + ((27814858063552394035200 : ℝ) * (x ^ 12)) + ((51613532091187200000000 : ℝ) * (x ^ 8)) + ((75101860675584000000000 : ℝ) * (x ^ 10)))

theorem c4MarginDecay1_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginDecay1 x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginDecay1]
  positivity

noncomputable def c4MarginDecay3 (x : ℝ) : ℝ :=
  (((-228318088740942643200000000 : ℝ) * (x ^ 11)) + ((-147494131976267366400000000 : ℝ) * (x ^ 9)) + ((-101607716127821716153958400 : ℝ) * (x ^ 13)) + ((-22626115365371904000000000 : ℝ) * (x ^ 7)) + ((-11611662036470203164917760 : ℝ) * (x ^ 15)) + ((-392968871608320000000000 : ℝ) * (x ^ 5)) + ((-330564548351884598968320 : ℝ) * (x ^ 18)) + ((-50565627624164023074816 : ℝ) * (x ^ 20)) + ((-2001884937263297593344 : ℝ) * (x ^ 22)) + ((177288702931066945536 : ℝ) * (x ^ 23)) + ((12194651586622503518208 : ℝ) * (x ^ 21)) + ((151302016660187664875520 : ℝ) * (x ^ 19)) + ((348482406683805524951040 : ℝ) * (x ^ 17)) + ((1546123124613958336512000 : ℝ) * (x ^ 16)) + ((4389094155091968000000000 : ℝ) * (x ^ 6)) + ((41937459608130227294699520 : ℝ) * (x ^ 14)) + ((70715278845856972800000000 : ℝ) * (x ^ 8)) + ((177522128718282462383308800 : ℝ) * (x ^ 12)) + ((215814175836025651200000000 : ℝ) * (x ^ 10)))

theorem c4MarginDecay3_pos {x : ℝ} (hx : 5 ≤ x) : 0 < c4MarginDecay3 x := by
  let z:=x-5
  have hz : 0≤z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [c4MarginDecay3]
  positivity

theorem decomposition (x y : ℝ) :
  PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y =
    c4MarginBase x-c4MarginNeg1 x*y+c4MarginPos2 x*y^2-
    c4MarginNeg3 x*y^3+c4MarginPos4 x*y^4 := by
  simp [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, c4MarginBase, c4MarginNeg1, c4MarginPos2, c4MarginNeg3, c4MarginPos4]
  ring

end PF4.UnscaledOuterClosure.C4Data
