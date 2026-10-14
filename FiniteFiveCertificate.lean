import FiniteArrivalCertificate

/-!
# A 21-test below-five certificate for finite atomic exposure

Generated from exact rational data by generate_arrival_certificate.py.
The conclusion is for exposure data satisfying the displayed arrival bounds;
the separate probabilistic connection to replica PS remains necessary.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open Finset
open scoped BigOperators

namespace ProbabilisticSerial.FiniteFiveCertificate

open FiniteAtomicExposure FiniteArrivalCertificate FiniteExposure

def grid (j : ℕ) : ℝ := if j ≤ 20 then 1 - (1 / 2 : ℝ) ^ j else 1
def horizon (i : Fin 21) : ℝ := grid (i.val + 1)
def parameter (i : Fin 21) : ℝ :=
  match i.val with
  | 0 => (1567089 / 1000000)
  | 1 => (1955847 / 1000000)
  | 2 => (36688 / 15625)
  | 3 => (1399107 / 500000)
  | 4 => (1663837 / 500000)
  | 5 => (1975359 / 500000)
  | 6 => (4678649 / 1000000)
  | 7 => (2759709 / 500000)
  | 8 => (6477031 / 1000000)
  | 9 => (7552067 / 1000000)
  | 10 => (4371511 / 500000)
  | 11 => (10047541 / 1000000)
  | 12 => (5731513 / 500000)
  | 13 => (12986789 / 1000000)
  | 14 => (7308021 / 500000)
  | 15 => (16347911 / 1000000)
  | 16 => (454487 / 25000)
  | 17 => (20107839 / 1000000)
  | 18 => (5532533 / 250000)
  | 19 => (4848713 / 200000)
  | 20 => 1600
  | _ => 0
def mass (i : Fin 21) : ℝ :=
  match i.val with
  | 0 => (532173605091 / 1000000000000)
  | 1 => (18999280421 / 62500000000)
  | 2 => (37868468153 / 200000000000)
  | 3 => (54747937651 / 500000000000)
  | 4 => (13997066237 / 250000000000)
  | 5 => (26138646661 / 1000000000000)
  | 6 => (11675292139 / 1000000000000)
  | 7 => (7370461003 / 1000000000000)
  | 8 => (10246989 / 625000000)
  | 9 => (28882108813 / 1000000000000)
  | 10 => (7006303691 / 250000000000)
  | 11 => (9359747377 / 500000000000)
  | 12 => (639031969 / 62500000000)
  | 13 => (5044633677 / 1000000000000)
  | 14 => (2370401391 / 1000000000000)
  | 15 => (544920101 / 500000000000)
  | 16 => (795131 / 1600000000)
  | 17 => (113116583 / 500000000000)
  | 18 => (103141199 / 1000000000000)
  | 19 => (982693 / 15625000000)
  | 20 => (625477059 / 1000000000000)
  | _ => 0
def price (i : Fin 21) : ℝ :=
  match i.val with
  | 0 => (811019 / 1000000)
  | 1 => (1671327 / 1000000)
  | 2 => (1286951 / 500000)
  | 3 => (55341 / 15625)
  | 4 => (573893 / 125000)
  | 5 => (1433937 / 250000)
  | 6 => (6987849 / 1000000)
  | 7 => (1044621 / 125000)
  | 8 => (9849011 / 1000000)
  | 9 => (11466517 / 1000000)
  | 10 => (3302493 / 250000)
  | 11 => (15079011 / 1000000)
  | 12 => (4268299 / 250000)
  | 13 => (19192179 / 1000000)
  | 14 => (5358943 / 250000)
  | 15 => (23803881 / 1000000)
  | 16 => (2629651 / 100000)
  | 17 => (28913809 / 1000000)
  | 18 => (15828041 / 500000)
  | 19 => (6904751 / 200000)
  | 20 => (11151293 / 6250)
  | _ => 0
def allowance (i : Fin 20) : ℝ :=
  match i.val with
  | 0 => (24393 / 100000)
  | 1 => (17887 / 25000)
  | 2 => (122587 / 100000)
  | 3 => (174361 / 100000)
  | 4 => (226347 / 100000)
  | 5 => (278503 / 100000)
  | 6 => (8273 / 2500)
  | 7 => (76751 / 20000)
  | 8 => (218599 / 50000)
  | 9 => (98289 / 20000)
  | 10 => (109339 / 20000)
  | 11 => (603147 / 100000)
  | 12 => (661017 / 100000)
  | 13 => (720539 / 100000)
  | 14 => (781973 / 100000)
  | 15 => (845597 / 100000)
  | 16 => (911703 / 100000)
  | 17 => (980597 / 100000)
  | 18 => (210519 / 20000)
  | 19 => (1128019 / 100000)
  | _ => 0
def lowerCost (i : Fin 21) (j : Fin 22) : ℝ :=
  match i.val, j.val with
  | 0, 0 => (67901982901 / 125000000000)
  | 1, 0 => (153870369841 / 200000000000)
  | 1, 1 => (96684303603 / 250000000000)
  | 2, 0 => (435904866537 / 500000000000)
  | 2, 1 => (14635730943 / 25000000000)
  | 2, 2 => (254353759701 / 1000000000000)
  | 3, 0 => (185464820693 / 200000000000)
  | 3, 1 => (44125687601 / 62500000000)
  | 3, 2 => (40824650229 / 100000000000)
  | 3, 3 => (16044926961 / 100000000000)
  | 4, 0 => (959952302823 / 1000000000000)
  | 4, 1 => (394911976667 / 500000000000)
  | 4, 2 => (517091751553 / 1000000000000)
  | 4, 3 => (267996100201 / 1000000000000)
  | 4, 4 => (98765521299 / 1000000000000)
  | 5, 0 => (979153747231 / 1000000000000)
  | 5, 1 => (170486122623 / 200000000000)
  | 5, 2 => (120768936587 / 200000000000)
  | 5, 3 => (175430944891 / 500000000000)
  | 5, 4 => (169053533059 / 1000000000000)
  | 5, 5 => (14965820297 / 250000000000)
  | 6, 0 => (494942509017 / 500000000000)
  | 6, 1 => (56247125949 / 62500000000)
  | 6, 2 => (338984461747 / 500000000000)
  | 6, 3 => (211028251789 / 500000000000)
  | 6, 4 => (11287622217 / 50000000000)
  | 6, 5 => (51928748863 / 500000000000)
  | 6, 6 => (4486498537 / 125000000000)
  | 7, 0 => (248855405313 / 250000000000)
  | 7, 1 => (935173869319 / 1000000000000)
  | 7, 2 => (92862218259 / 125000000000)
  | 7, 3 => (60931888853 / 125000000000)
  | 7, 4 => (276318136597 / 1000000000000)
  | 7, 5 => (28016974909 / 200000000000)
  | 7, 6 => (7829158021 / 125000000000)
  | 7, 7 => (21329466267 / 1000000000000)
  | 8, 0 => (998042246529 / 1000000000000)
  | 8, 1 => (192007706981 / 200000000000)
  | 8, 2 => (799423685137 / 1000000000000)
  | 8, 3 => (274655611053 / 500000000000)
  | 8, 4 => (324406682903 / 1000000000000)
  | 8, 5 => (86419849159 / 500000000000)
  | 8, 6 => (84745543839 / 1000000000000)
  | 8, 7 => (37240225369 / 1000000000000)
  | 8, 8 => (6285385283 / 500000000000)
  | 9, 0 => (499596757073 / 500000000000)
  | 9, 1 => (976559726169 / 1000000000000)
  | 9, 2 => (847484652777 / 1000000000000)
  | 9, 3 => (304027283231 / 500000000000)
  | 9, 4 => (185815944503 / 500000000000)
  | 9, 5 => (204374776147 / 1000000000000)
  | 9, 6 => (104726464769 / 1000000000000)
  | 9, 7 => (50315503037 / 1000000000000)
  | 9, 8 => (21882229329 / 1000000000000)
  | 9, 9 => (459246023 / 62500000000)
  | 10, 0 => (249918327587 / 250000000000)
  | 10, 1 => (493430795021 / 500000000000)
  | 10, 2 => (887076431521 / 1000000000000)
  | 10, 3 => (663314649817 / 1000000000000)
  | 10, 4 => (418514832369 / 1000000000000)
  | 10, 5 => (117909414753 / 500000000000)
  | 10, 6 => (61978746407 / 500000000000)
  | 10, 7 => (62028585759 / 1000000000000)
  | 10, 8 => (7360320647 / 250000000000)
  | 10, 9 => (6362749219 / 500000000000)
  | 10, 10 => (2129977127 / 500000000000)
  | 11, 0 => (249966898313 / 250000000000)
  | 11, 1 => (496455782239 / 500000000000)
  | 11, 2 => (459295184383 / 500000000000)
  | 11, 3 => (714491292689 / 1000000000000)
  | 11, 4 => (465015913031 / 1000000000000)
  | 11, 5 => (16729768457 / 62500000000)
  | 11, 6 => (143190622561 / 1000000000000)
  | 11, 7 => (73224017431 / 1000000000000)
  | 11, 8 => (2257904867 / 62500000000)
  | 11, 9 => (4256126899 / 250000000000)
  | 11, 10 => (7160183 / 976562500)
  | 11, 11 => (2450006761 / 1000000000000)
  | 12, 0 => (999945616039 / 1000000000000)
  | 12, 1 => (62267778279 / 62500000000)
  | 12, 2 => (188563772409 / 200000000000)
  | 12, 3 => (76104011947 / 100000000000)
  | 12, 4 => (127706834393 / 250000000000)
  | 12, 5 => (150050859427 / 500000000000)
  | 12, 6 => (162815234953 / 1000000000000)
  | 12, 7 => (3375264017 / 40000000000)
  | 12, 8 => (5306346973 / 125000000000)
  | 12, 9 => (20770682573 / 1000000000000)
  | 12, 10 => (9747250747 / 1000000000000)
  | 12, 11 => (4189086693 / 1000000000000)
  | 12, 12 => (1398316609 / 1000000000000)
  | 13, 0 => (499988584639 / 500000000000)
  | 13, 1 => (499044355711 / 500000000000)
  | 13, 2 => (960822113203 / 1000000000000)
  | 13, 3 => (802596519793 / 1000000000000)
  | 13, 4 => (277766942779 / 500000000000)
  | 13, 5 => (166526436139 / 500000000000)
  | 13, 6 => (91503980121 / 500000000000)
  | 13, 7 => (95765580289 / 1000000000000)
  | 13, 8 => (48710640293 / 1000000000000)
  | 13, 9 => (24272733391 / 1000000000000)
  | 13, 10 => (590967827 / 50000000000)
  | 13, 11 => (553319007 / 100000000000)
  | 13, 12 => (2375126999 / 1000000000000)
  | 13, 13 => (792336631 / 1000000000000)
  | 14, 0 => (124998769087 / 125000000000)
  | 14, 1 => (999025805879 / 1000000000000)
  | 14, 2 => (194753485113 / 200000000000)
  | 14, 3 => (104876730201 / 125000000000)
  | 14, 4 => (299352014681 / 500000000000)
  | 14, 5 => (366379614381 / 1000000000000)
  | 14, 6 => (203819699039 / 1000000000000)
  | 14, 7 => (107511617233 / 1000000000000)
  | 14, 8 => (55073250131 / 1000000000000)
  | 14, 9 => (13854876381 / 500000000000)
  | 14, 10 => (85826703 / 6250000000)
  | 14, 11 => (3334180101 / 500000000000)
  | 14, 12 => (1558727021 / 500000000000)
  | 14, 13 => (668621851 / 500000000000)
  | 14, 14 => (445946739 / 1000000000000)
  | 15, 0 => (199999124779 / 200000000000)
  | 15, 1 => (999503847537 / 1000000000000)
  | 15, 2 => (7862335223 / 8000000000)
  | 15, 3 => (870355902351 / 1000000000000)
  | 15, 4 => (639943260943 / 1000000000000)
  | 15, 5 => (399878272581 / 1000000000000)
  | 15, 6 => (225228134483 / 1000000000000)
  | 15, 7 => (59839473619 / 500000000000)
  | 15, 8 => (61628711199 / 1000000000000)
  | 15, 9 => (31183508561 / 1000000000000)
  | 15, 10 => (7796233201 / 500000000000)
  | 15, 11 => (1925776729 / 250000000000)
  | 15, 12 => (3734748297 / 1000000000000)
  | 15, 13 => (872310827 / 500000000000)
  | 15, 14 => (374034017 / 500000000000)
  | 15, 15 => (49883643 / 200000000000)
  | 16, 0 => (999997993949 / 1000000000000)
  | 16, 1 => (499872909207 / 500000000000)
  | 16, 2 => (494453504539 / 500000000000)
  | 16, 3 => (56053999377 / 62500000000)
  | 16, 4 => (339461716703 / 500000000000)
  | 16, 5 => (433325402091 / 1000000000000)
  | 16, 6 => (965507331 / 3906250000)
  | 16, 7 => (13228198887 / 100000000000)
  | 16, 8 => (13684314069 / 200000000000)
  | 16, 9 => (34749956189 / 1000000000000)
  | 16, 10 => (8730234047 / 500000000000)
  | 16, 11 => (1087491927 / 125000000000)
  | 16, 12 => (4290420917 / 1000000000000)
  | 16, 13 => (259789211 / 125000000000)
  | 16, 14 => (121302227 / 125000000000)
  | 16, 15 => (5200109 / 12500000000)
  | 16, 16 => (138688807 / 1000000000000)
  | 17, 0 => (999999051321 / 1000000000000)
  | 17, 1 => (15622943053 / 15625000000)
  | 17, 2 => (248237028199 / 250000000000)
  | 17, 3 => (918911973107 / 1000000000000)
  | 17, 4 => (715395913269 / 1000000000000)
  | 17, 5 => (233249208089 / 500000000000)
  | 17, 6 => (8423752107 / 31250000000)
  | 17, 7 => (2270459909 / 15625000000)
  | 17, 8 => (75469780023 / 1000000000000)
  | 17, 9 => (4804772149 / 125000000000)
  | 17, 10 => (1936980337 / 100000000000)
  | 17, 11 => (9694279999 / 1000000000000)
  | 17, 12 => (4820777633 / 1000000000000)
  | 17, 13 => (237503999 / 100000000000)
  | 17, 14 => (1149918113 / 1000000000000)
  | 17, 15 => (33549569 / 62500000000)
  | 17, 16 => (5752237 / 25000000000)
  | 17, 17 => (9587797 / 125000000000)
  | 18, 0 => (999999537453 / 1000000000000)
  | 18, 1 => (999930831483 / 1000000000000)
  | 18, 2 => (99556278939 / 100000000000)
  | 18, 3 => (187391869509 / 200000000000)
  | 18, 4 => (749194168239 / 1000000000000)
  | 18, 5 => (15599622867 / 31250000000)
  | 18, 6 => (292304315951 / 1000000000000)
  | 18, 7 => (158735739303 / 1000000000000)
  | 18, 8 => (5173503239 / 62500000000)
  | 18, 9 => (42261692891 / 1000000000000)
  | 18, 10 => (4267658883 / 200000000000)
  | 18, 11 => (2141159849 / 200000000000)
  | 18, 12 => (5346311713 / 1000000000000)
  | 18, 13 => (663922413 / 250000000000)
  | 18, 14 => (653825233 / 500000000000)
  | 18, 15 => (632947759 / 1000000000000)
  | 18, 16 => (73856373 / 250000000000)
  | 18, 17 => (126621613 / 1000000000000)
  | 18, 18 => (21104493 / 500000000000)
  | 19, 0 => (249999941931 / 250000000000)
  | 19, 1 => (999963047143 / 1000000000000)
  | 19, 2 => (99722629857 / 100000000000)
  | 19, 3 => (237877024653 / 250000000000)
  | 19, 4 => (780229119529 / 1000000000000)
  | 19, 5 => (66400535029 / 125000000000)
  | 19, 6 => (315305538851 / 1000000000000)
  | 19, 7 => (172527769909 / 1000000000000)
  | 19, 8 => (90334478033 / 1000000000000)
  | 19, 9 => (2889068939 / 62500000000)
  | 19, 10 => (5843678539 / 250000000000)
  | 19, 11 => (11745039913 / 1000000000000)
  | 19, 12 => (5878373001 / 1000000000000)
  | 19, 13 => (146599619 / 50000000000)
  | 19, 14 => (1455529001 / 1000000000000)
  | 19, 15 => (71647763 / 100000000000)
  | 19, 16 => (10835839 / 31250000000)
  | 19, 17 => (161830161 / 1000000000000)
  | 19, 18 => (6935899 / 100000000000)
  | 19, 19 => (11560099 / 500000000000)
  | 20, 0 => (999999999999 / 1000000000000)
  | 20, 1 => (999999999999 / 1000000000000)
  | 20, 2 => (999999999999 / 1000000000000)
  | 20, 3 => (999999999999 / 1000000000000)
  | 20, 4 => (249999999999 / 250000000000)
  | 20, 5 => (999999999129 / 1000000000000)
  | 20, 6 => (999999816011 / 1000000000000)
  | 20, 7 => (999970166773 / 1000000000000)
  | 20, 8 => (249411718911 / 250000000000)
  | 20, 9 => (477922776101 / 500000000000)
  | 20, 10 => (395190334967 / 500000000000)
  | 20, 11 => (542166570337 / 1000000000000)
  | 20, 12 => (8084153839 / 25000000000)
  | 20, 13 => (221778047 / 1250000000)
  | 20, 14 => (2907480691 / 31250000000)
  | 20, 15 => (5956900013 / 125000000000)
  | 20, 16 => (3014806233 / 125000000000)
  | 20, 17 => (2426565537 / 200000000000)
  | 20, 18 => (6084927011 / 1000000000000)
  | 20, 19 => (761776483 / 250000000000)
  | 20, 20 => (95294709 / 62500000000)
  | _, _ => 0

lemma parameter_pos (i : Fin 21) : 0 < parameter i := by
  fin_cases i <;> norm_num [parameter]

lemma mass_nonneg (i : Fin 21) : 0 ≤ mass i := by
  fin_cases i <;> norm_num [mass]

lemma kernel_lower_0 (j : Fin 22) :
    lowerCost (⟨0, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨0, by decide⟩ : Fin 21)) (horizon (⟨0, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨0, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨0, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨0, by decide⟩ : Fin 21) * max (horizon (⟨0, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨0, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_1 (j : Fin 22) :
    lowerCost (⟨1, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨1, by decide⟩ : Fin 21)) (horizon (⟨1, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨1, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨1, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨1, by decide⟩ : Fin 21) * max (horizon (⟨1, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨1, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_2 (j : Fin 22) :
    lowerCost (⟨2, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨2, by decide⟩ : Fin 21)) (horizon (⟨2, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨2, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨2, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨2, by decide⟩ : Fin 21) * max (horizon (⟨2, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨2, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_3 (j : Fin 22) :
    lowerCost (⟨3, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨3, by decide⟩ : Fin 21)) (horizon (⟨3, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨3, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨3, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨3, by decide⟩ : Fin 21) * max (horizon (⟨3, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨3, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_4 (j : Fin 22) :
    lowerCost (⟨4, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨4, by decide⟩ : Fin 21)) (horizon (⟨4, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨4, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨4, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨4, by decide⟩ : Fin 21) * max (horizon (⟨4, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨4, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_5 (j : Fin 22) :
    lowerCost (⟨5, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨5, by decide⟩ : Fin 21)) (horizon (⟨5, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨5, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨5, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨5, by decide⟩ : Fin 21) * max (horizon (⟨5, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨5, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_6 (j : Fin 22) :
    lowerCost (⟨6, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨6, by decide⟩ : Fin 21)) (horizon (⟨6, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨6, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨6, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨6, by decide⟩ : Fin 21) * max (horizon (⟨6, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨6, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_7 (j : Fin 22) :
    lowerCost (⟨7, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨7, by decide⟩ : Fin 21)) (horizon (⟨7, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨7, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨7, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨7, by decide⟩ : Fin 21) * max (horizon (⟨7, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨7, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_8 (j : Fin 22) :
    lowerCost (⟨8, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨8, by decide⟩ : Fin 21)) (horizon (⟨8, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨8, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨8, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨8, by decide⟩ : Fin 21) * max (horizon (⟨8, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨8, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_9 (j : Fin 22) :
    lowerCost (⟨9, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨9, by decide⟩ : Fin 21)) (horizon (⟨9, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨9, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨9, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨9, by decide⟩ : Fin 21) * max (horizon (⟨9, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨9, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_10 (j : Fin 22) :
    lowerCost (⟨10, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨10, by decide⟩ : Fin 21)) (horizon (⟨10, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨10, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨10, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨10, by decide⟩ : Fin 21) * max (horizon (⟨10, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨10, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_11 (j : Fin 22) :
    lowerCost (⟨11, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨11, by decide⟩ : Fin 21)) (horizon (⟨11, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨11, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨11, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨11, by decide⟩ : Fin 21) * max (horizon (⟨11, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨11, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_12 (j : Fin 22) :
    lowerCost (⟨12, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨12, by decide⟩ : Fin 21)) (horizon (⟨12, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨12, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨12, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨12, by decide⟩ : Fin 21) * max (horizon (⟨12, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨12, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_13 (j : Fin 22) :
    lowerCost (⟨13, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨13, by decide⟩ : Fin 21)) (horizon (⟨13, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨13, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨13, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨13, by decide⟩ : Fin 21) * max (horizon (⟨13, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨13, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_14 (j : Fin 22) :
    lowerCost (⟨14, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨14, by decide⟩ : Fin 21)) (horizon (⟨14, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨14, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨14, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨14, by decide⟩ : Fin 21) * max (horizon (⟨14, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨14, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_15 (j : Fin 22) :
    lowerCost (⟨15, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨15, by decide⟩ : Fin 21)) (horizon (⟨15, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨15, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨15, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨15, by decide⟩ : Fin 21) * max (horizon (⟨15, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨15, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_16 (j : Fin 22) :
    lowerCost (⟨16, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨16, by decide⟩ : Fin 21)) (horizon (⟨16, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨16, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨16, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨16, by decide⟩ : Fin 21) * max (horizon (⟨16, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨16, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_17 (j : Fin 22) :
    lowerCost (⟨17, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨17, by decide⟩ : Fin 21)) (horizon (⟨17, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨17, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨17, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨17, by decide⟩ : Fin 21) * max (horizon (⟨17, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨17, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_18 (j : Fin 22) :
    lowerCost (⟨18, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨18, by decide⟩ : Fin 21)) (horizon (⟨18, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨18, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨18, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨18, by decide⟩ : Fin 21) * max (horizon (⟨18, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨18, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_19 (j : Fin 22) :
    lowerCost (⟨19, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨19, by decide⟩ : Fin 21)) (horizon (⟨19, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨19, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨19, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨19, by decide⟩ : Fin 21) * max (horizon (⟨19, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨19, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower_20 (j : Fin 22) :
    lowerCost (⟨20, by decide⟩ : Fin 21) j ≤ kernel (parameter (⟨20, by decide⟩ : Fin 21)) (horizon (⟨20, by decide⟩ : Fin 21)) (grid j.val) := by
  have hb : 0 < 1 - lowerCost (⟨20, by decide⟩ : Fin 21) j := by
    fin_cases j <;> norm_num [lowerCost]
  have hp : 1 ≤ (1 - lowerCost (⟨20, by decide⟩ : Fin 21) j) *
      ∑ k ∈ Finset.range 9,
        (parameter (⟨20, by decide⟩ : Fin 21) * max (horizon (⟨20, by decide⟩ : Fin 21) - grid j.val) 0) ^ k / (k.factorial : ℝ) := by
    fin_cases j <;>
      norm_num [lowerCost, parameter, horizon, grid, Finset.sum_range_succ, Nat.factorial]
  have h := exp_neg_le_of_taylor
    (mul_nonneg (parameter_pos (⟨20, by decide⟩ : Fin 21)).le (le_max_right _ _)) hb 9 hp
  unfold kernel arrivalCost
  rw [neg_mul]
  linarith

lemma kernel_lower (i : Fin 21) (j : Fin 22) :
    lowerCost i j ≤ kernel (parameter i) (horizon i) (grid j.val) := by
  fin_cases i
  · exact kernel_lower_0 j
  · exact kernel_lower_1 j
  · exact kernel_lower_2 j
  · exact kernel_lower_3 j
  · exact kernel_lower_4 j
  · exact kernel_lower_5 j
  · exact kernel_lower_6 j
  · exact kernel_lower_7 j
  · exact kernel_lower_8 j
  · exact kernel_lower_9 j
  · exact kernel_lower_10 j
  · exact kernel_lower_11 j
  · exact kernel_lower_12 j
  · exact kernel_lower_13 j
  · exact kernel_lower_14 j
  · exact kernel_lower_15 j
  · exact kernel_lower_16 j
  · exact kernel_lower_17 j
  · exact kernel_lower_18 j
  · exact kernel_lower_19 j
  · exact kernel_lower_20 j

lemma endpoint_check (j : Fin 22) :
    1 - grid j.val ≤ ∑ i : Fin 21, mass i * lowerCost i j := by
  fin_cases j <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [grid, mass, lowerCost]

theorem domination (r : ℝ) (hr : 0 ≤ r) :
    max (1 - r) 0 ≤ combination mass parameter horizon r := by
  apply grid_domination mass parameter horizon mass_nonneg
    (fun i => (parameter_pos i).le) grid 20 _ _ _ _ _ r hr
  · norm_num [grid]
  · norm_num [grid]
  · intro j hj
    interval_cases j <;> norm_num [grid]
  · intro j hj i
    interval_cases j <;> fin_cases i <;> norm_num [horizon, grid]
  · intro j hj
    let k : Fin 22 := ⟨j, by omega⟩
    exact (endpoint_check k).trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (kernel_lower i k) (mass_nonneg i))

lemma allowance_log_bound (i : Fin 20) :
    -Real.log (parameter i.castSucc * (1 - horizon i.castSucc)) ≤ allowance i := by
  have hx : 0 ≤ allowance i := by fin_cases i <;> norm_num [allowance]
  have hb : 0 < parameter i.castSucc * (1 - horizon i.castSucc) := by
    fin_cases i <;> norm_num [parameter, horizon, grid]
  have hp : 1 ≤ (parameter i.castSucc * (1 - horizon i.castSucc)) *
      ∑ k ∈ Finset.range 12, allowance i ^ k / (k.factorial : ℝ) := by
    fin_cases i <;>
      norm_num [parameter, horizon, grid, allowance, Finset.sum_range_succ, Nat.factorial]
  have h := (Real.le_log_iff_exp_le hb).2 (exp_neg_le_of_taylor hx hb 12 hp)
  linarith

lemma interior_horizon_bounds (i : Fin 20) :
    0 < horizon i.castSucc ∧ horizon i.castSucc < 1 := by
  fin_cases i <;> norm_num [horizon, grid]

lemma phi_le_price (i : Fin 20) :
    phi (parameter i.castSucc) (1 - horizon i.castSucc) ≤ price i.castSucc := by
  have hs : ¬parameter i.castSucc ≤ 1 := by fin_cases i <;> norm_num [parameter]
  have hm : parameter i.castSucc ≤ 1 / (1 - horizon i.castSucc) := by
    fin_cases i <;> norm_num [parameter, horizon, grid]
  have hu : 0 < 1 - horizon i.castSucc := by fin_cases i <;> norm_num [horizon, grid]
  have hp : price i.castSucc = parameter i.castSucc - 1 + allowance i := by
    fin_cases i <;> norm_num [price, parameter, allowance]
  rw [phi, if_neg hs, if_pos hm, hp]
  have h := allowance_log_bound i
  rw [Real.log_mul (parameter_pos _).ne' hu.ne'] at h
  linarith

lemma log_ten_upper : Real.log 10 ≤ (2302586 / 1000000 : ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)).2
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 2302586 / 1000000) 16
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem weighted_price_lt_five : (∑ i : Fin 21, mass i * price i) < 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [mass, price]

/-- The analytic below-five certificate. Its hypotheses are the arrival
inequalities; it is not an unconditional theorem about the PS mechanism. -/
theorem value_lt_five {ι : Type*} [Fintype ι] (D : Data ι)
    (hinterior : ∀ t, 0 < t → t < 1 → ∀ θ, 0 < θ → cost D θ t ≤ phi θ (1 - t))
    (hendpoint : cost D 1600 1 ≤ 1600 + 80 * Real.log 10) :
    value D 1 < 5 := by
  apply lt_of_le_of_lt (value_le_certificate D mass parameter horizon price
    mass_nonneg domination ?_) weighted_price_lt_five
  intro i
  by_cases hi : i.val < 20
  · let j : Fin 20 := ⟨i.val, hi⟩
    have hij : j.castSucc = i := Fin.ext rfl
    have ht := interior_horizon_bounds j
    rw [← hij]
    exact (hinterior _ ht.1 ht.2 _ (parameter_pos _)).trans (phi_le_price j)
  · have hi20 : i = 20 := Fin.ext (by omega)
    subst i
    change cost D 1600 1 ≤ (11151293 / 6250 : ℝ)
    linarith [log_ten_upper]

end ProbabilisticSerial.FiniteFiveCertificate
