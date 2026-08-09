/-
# Q565 : the next term in the asymptotic expansion of the Bell numbers

Formalization of the answer to Q565.
-/
import Mathlib

open Real Filter Asymptotics
open scoped BigOperators Nat Topology

set_option maxHeartbeats 1000000

namespace Q565

/-! ## Elementary real-analysis preliminaries -/

/-- `exp (-t) ≤ 1 - t + t²/2` for `t ≥ 0`. -/
theorem exp_neg_le_quad (t : ℝ) (ht : 0 ≤ t) : exp (-t) ≤ 1 - t + t^2/2 := by
  have h1 : 1 + t + t^2/2 ≤ exp t := by
    have := Real.sum_le_exp_of_nonneg ht 3
    simp [Finset.sum_range_succ] at this
    linarith
  have h2 : (0:ℝ) < exp t := exp_pos t
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ h2]
  nlinarith [sq_nonneg t, sq_nonneg (t^2), sq_nonneg (t*t)]

theorem log_le_two_sqrt {L : ℝ} (hL : 0 < L) : Real.log L ≤ 2 * Real.sqrt L := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hL)
  rw [Real.log_sqrt hL.le] at h
  linarith [Real.sqrt_nonneg L]

/-- The heart of the expansion of the saddle parameter: if `exp (-d) = 1 - (l-d)/L`
with `0 ≤ d`, then `d = l/L + O(l²/L²)`. -/
theorem delta_bound {L l d : ℝ} (hL : 64 ≤ L) (hl1 : 4 ≤ l) (hl4 : l ≤ L/4)
    (hd0 : 0 ≤ d) (heq : exp (-d) = 1 - (l - d)/L) :
    |d - l/L| ≤ l^2/L^2 := by
  have hL0 : (0:ℝ) < L := by linarith
  have hA : l ≤ d * L + d := by
    have h := Real.add_one_le_exp (-d)
    rw [heq] at h
    have h2 : (l - d)/L ≤ d := by linarith
    rw [div_le_iff₀ hL0] at h2
    linarith
  have hC : d ≤ 1/3 := by
    have h1 : exp (-d) ≤ 1/(1+d) := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by linarith)
      linarith [Real.add_one_le_exp d]
    have h2 : (3:ℝ)/4 ≤ exp (-d) := by
      rw [heq]
      have h4 : (l - d)/L ≤ l/L := by gcongr; linarith
      have h3 : l/L ≤ 1/4 := by rw [div_le_iff₀ hL0]; linarith
      linarith
    have h5 := h2.trans h1
    rw [le_div_iff₀ (by linarith)] at h5
    linarith
  have hB : d * L + d ≤ l + d^2 * L/2 := by
    have hq := exp_neg_le_quad d hd0
    rw [heq] at hq
    have h6 : (d - d^2/2) * L ≤ l - d := by
      have h : d - d^2/2 ≤ (l - d)/L := by linarith
      calc (d - d^2/2) * L ≤ ((l-d)/L) * L := by nlinarith
        _ = l - d := by field_simp
    linarith
  have hd6 : d * (5 * L) ≤ 6 * l := by nlinarith
  have hrw : d - l/L = (d*L - l)/L := by field_simp
  have key : |d*L - l| ≤ l^2/L := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h : l - d*L ≤ l^2/L := by rw [le_div_iff₀ hL0]; nlinarith
      linarith
    · rw [le_div_iff₀ hL0]; nlinarith
  calc |d - l/L| = |d*L - l|/L := by rw [hrw, abs_div, abs_of_pos hL0]
    _ ≤ (l^2/L)/L := by gcongr
    _ = l^2/L^2 := by field_simp

/-- Second-order Taylor expansion of `(1+u)^{-1/2}`. -/
theorem inv_sqrt_taylor {u : ℝ} (hu : |u| ≤ 1/8) :
    |1/Real.sqrt (1+u) - (1 - u/2 + 3*u^2/8)| ≤ |u|^3 := by
  obtain ⟨hu1, hu2⟩ := abs_le.1 hu
  set a := |u| with ha
  have ha0 : 0 ≤ a := abs_nonneg u
  have hua : u^2 = a^2 := (sq_abs u).symm
  have hu3 : |u^3| = a^3 := by rw [ha, abs_pow]
  set s := Real.sqrt (1+u) with hs
  have h1u : (0:ℝ) < 1 + u := by linarith
  have hs2 : s^2 = 1 + u := Real.sq_sqrt h1u.le
  have hspos : 0 < s := Real.sqrt_pos.2 h1u
  have hslb : (9:ℝ)/10 ≤ s := by nlinarith
  have hsub : s ≤ (11:ℝ)/10 := by nlinarith
  set P := 1 - u/2 + 3*u^2/8 with hP
  have hPlb : (9:ℝ)/10 ≤ P := by rw [hP]; nlinarith
  have hPub : P ≤ (11:ℝ)/10 := by rw [hP]; nlinarith
  have key : (1 - P*s)*(1 + P*s) = -(5/8)*u^3 + (15/64)*u^4 - (9/64)*u^5 := by
    have h : (1 - P*s)*(1+P*s) = 1 - P^2*(s^2) := by ring
    rw [h, hs2, hP]; ring
  have hden : (18:ℝ)/10 ≤ 1 + P*s := by nlinarith
  have hnum : |(1 - P*s)*(1 + P*s)| ≤ (7/10)*a^3 := by
    rw [key]
    have e1 : |u^3| = a^3 := hu3
    have e2 : |u^4| = a^4 := by rw [ha, abs_pow]
    have e3 : |u^5| = a^5 := by rw [ha, abs_pow]
    have b1 := abs_le.1 (le_of_eq e1)
    have b4 := abs_le.1 (le_of_eq e2)
    have b5 := abs_le.1 (le_of_eq e3)
    have haa : a ≤ 1/8 := hu
    rw [abs_le]
    constructor <;>
      nlinarith [b1.1, b1.2, b4.1, b4.2, b5.1, b5.2, pow_nonneg ha0 3, pow_nonneg ha0 4,
        pow_nonneg ha0 5]
  have hPs : |1 - P*s| ≤ (4/10)*a^3 := by
    have habs : |1 - P*s| * |1 + P*s| ≤ (7/10)*a^3 := by
      rw [← abs_mul]; exact hnum
    have h2 : |1 + P*s| = 1 + P*s := abs_of_nonneg (by linarith)
    rw [h2] at habs
    nlinarith [abs_nonneg (1 - P*s), pow_nonneg ha0 3]
  have hfin : 1/s - P = (1 - P*s)/s := by field_simp
  rw [hfin, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
  nlinarith [pow_nonneg ha0 3]

/-- The polynomial bookkeeping behind the second-order expansion of `√(L/(r+1))`. -/
theorem expansion_algebra {l v e : ℝ} (hl : 4 ≤ l) (hv : 0 < v) (hlv : l * v ≤ 1/32)
    (he : |e| ≤ l^2 * v^2) :
    |(1 - ((1-l)*v + l*v^2 + e*v)/2 + 3*((1-l)*v + l*v^2 + e*v)^2/8)
       - (1 + (l-1)*v/2 + (3*l^2-10*l+3)*v^2/8)| ≤ 2*l^3*v^3 := by
  have hid : (1 - ((1-l)*v + l*v^2 + e*v)/2 + 3*((1-l)*v + l*v^2 + e*v)^2/8)
       - (1 + (l-1)*v/2 + (3*l^2-10*l+3)*v^2/8)
      = (3*(1-l)*l/4)*v^3 + (3/8)*l^2*v^4 - e*v/2 + (3/4)*((1-l)*v + l*v^2)*(e*v)
        + (3/8)*(e*v)^2 := by ring
  rw [hid]
  have hl0 : (0:ℝ) < l := by linarith
  have hv3 : (0:ℝ) < v^3 := by positivity
  have hvsmall : v ≤ 1/32 := by nlinarith
  have hbase : (0:ℝ) < l^3*v^3 := by positivity
  have hev : |e * v| ≤ l^2*v^3 := by
    rw [abs_mul, abs_of_pos hv]; nlinarith [abs_nonneg e]
  have h1 : |(3*(1-l)*l/4)*v^3| ≤ (3/4)*(l^3*v^3) := by
    rw [abs_mul, abs_of_pos hv3, abs_of_nonpos (by nlinarith : 3*(1-l)*l/4 ≤ 0)]
    have h : -(3*(1-l)*l/4) ≤ (3/4)*l^3 := by nlinarith
    nlinarith
  have h2 : |(3/8)*l^2*v^4| ≤ (1/64)*(l^3*v^3) := by
    rw [abs_of_nonneg (by positivity)]
    have h : (3/8)*l^2*v^4 = ((3/8)*v)*(l^2*v^3) := by ring
    rw [h]
    have h9 : (l^2*v^3) ≤ l^3*v^3 := by nlinarith
    nlinarith [mul_pos (by positivity : (0:ℝ) < l^2) hv3]
  have h3 : |e*v/2| ≤ (1/2)*(l^3*v^3) := by
    have h10 : |e*v/2| = |e * v| / 2 := by rw [abs_div]; norm_num
    rw [h10]
    nlinarith
  have h4 : |(3/4)*((1-l)*v + l*v^2)*(e*v)| ≤ (1/8)*(l^3*v^3) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (3:ℝ)/4)]
    have hA : |(1-l)*v + l*v^2| ≤ 2*(l*v) := by
      rw [abs_le]
      constructor <;> nlinarith [mul_pos hl0 hv, mul_pos (mul_pos hl0 hv) hv]
    calc 3/4 * |(1-l)*v + l*v^2| * |e * v| ≤ 3/4 * (2*(l*v)) * (l^2*v^3) := by
          apply mul_le_mul (by nlinarith [abs_nonneg ((1-l)*v + l*v^2)]) hev (abs_nonneg _)
            (by positivity)
      _ ≤ (1/8)*(l^3*v^3) := by
          nlinarith [mul_pos (by positivity : (0:ℝ) < l^2*v^3) (mul_pos hl0 hv)]
  have h5 : |(3/8)*(e*v)^2| ≤ (1/8)*(l^3*v^3) := by
    rw [abs_of_nonneg (by positivity)]
    have hB : (e*v)^2 ≤ (l^2*v^3)^2 := by
      nlinarith [abs_nonneg (e*v), sq_abs (e*v)]
    have hC : (l^2*v^3)^2 = (l*v)*((l^3*v^3)*(v^2)) := by ring
    have hx1 : (l*v)*((l^3*v^3)*(v^2)) ≤ (1/32)*((l^3*v^3)*(v^2)) :=
      mul_le_mul_of_nonneg_right hlv (by positivity)
    have hx2 : (l^3*v^3)*(v^2) ≤ (l^3*v^3)*(1/1024) := by
      apply mul_le_mul_of_nonneg_left _ hbase.le
      nlinarith
    nlinarith
  rw [abs_le] at h1 h2 h3 h4 h5 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-! ## The saddle parameter `r` (the Lambert `W` function on `[0,∞)`) -/

theorem exists_lambert (x : ℝ) (hx : 0 ≤ x) : ∃ r, 0 ≤ r ∧ r * exp r = x := by
  have hcont : ContinuousOn (fun r : ℝ => r * exp r) (Set.Icc 0 x) := by fun_prop
  have hmem : x ∈ Set.Icc ((0:ℝ) * exp 0) (x * exp x) := by
    constructor
    · simpa using hx
    · nlinarith [Real.add_one_le_exp x, hx]
  obtain ⟨r, hr, hrx⟩ := intermediate_value_Icc hx hcont hmem
  exact ⟨r, hr.1, hrx⟩

theorem lambert_strictMono : StrictMonoOn (fun r : ℝ => r * exp r) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have : exp a ≤ exp b := by gcongr
  nlinarith [Real.exp_pos a, Real.exp_pos b]

/-- The saddle parameter: for `x ≥ 0`, `lamW x` is the unique `r ≥ 0` with `r * exp r = x`. -/
noncomputable def lamW (x : ℝ) : ℝ :=
  if h : 0 ≤ x then (exists_lambert x h).choose else 0

theorem lamW_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lamW x := by
  rw [lamW, dif_pos hx]; exact (exists_lambert x hx).choose_spec.1

theorem lamW_spec {x : ℝ} (hx : 0 ≤ x) : lamW x * exp (lamW x) = x := by
  rw [lamW, dif_pos hx]; exact (exists_lambert x hx).choose_spec.2

theorem lamW_eq {x r : ℝ} (hr : 0 ≤ r) (h : r * exp r = x) : lamW x = r := by
  have hx : 0 ≤ x := by rw [← h]; positivity
  exact lambert_strictMono.injOn (Set.mem_Ici.2 (lamW_nonneg hx)) (Set.mem_Ici.2 hr)
    (by simpa [lamW_spec hx] using h.symm)

theorem lamW_pos {x : ℝ} (hx : 0 < x) : 0 < lamW x := by
  rcases (lamW_nonneg hx.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have hs := lamW_spec hx.le
    rw [← h] at hs
    simp at hs
    linarith [hs ▸ hx]

/-- The saddle equation in logarithmic form: `r + log r = log x`. -/
theorem lamW_add_log {x : ℝ} (hx : 0 < x) : lamW x + Real.log (lamW x) = Real.log x := by
  have hr := lamW_pos hx
  have h := lamW_spec hx.le
  calc lamW x + Real.log (lamW x)
      = Real.log (lamW x * Real.exp (lamW x)) := by
        rw [Real.log_mul (ne_of_gt hr) (Real.exp_ne_zero _), Real.log_exp]; ring
    _ = Real.log x := by rw [h]

theorem lamW_le_log {x : ℝ} (hx : 0 < x) (hL : 1 ≤ Real.log x) : lamW x ≤ Real.log x := by
  have hr := lamW_pos hx
  have h := lamW_add_log hx
  by_cases h1 : lamW x ≤ 1
  · linarith
  · have : 0 < Real.log (lamW x) := Real.log_pos (by linarith [not_le.1 h1])
    linarith

/-! ## Expansion of the saddle parameter -/

section Expansion

variable {x : ℝ}

/-- With `L = log x` and `l = log L`, the saddle parameter satisfies
`r = L - l + l/L + O(l²/L²)`. -/
theorem lamW_expansion (hx : Real.exp 64 ≤ x) :
    |lamW x - (Real.log x - Real.log (Real.log x) + Real.log (Real.log x) / Real.log x)|
      ≤ (Real.log (Real.log x))^2 / (Real.log x)^2 := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos 64) hx
  set L := Real.log x with hLdef
  have hL64 : 64 ≤ L := by
    rw [hLdef, ← Real.log_exp 64]
    exact Real.log_le_log (Real.exp_pos 64) hx
  have hL0 : (0:ℝ) < L := by linarith
  set l := Real.log L with hldef
  have hl4 : 4 ≤ l := by
    have h : Real.log 64 ≤ l := Real.log_le_log (by norm_num) hL64
    have h64 : (4:ℝ) ≤ Real.log 64 := by
      rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hlL : l ≤ L/4 := by
    have h1 : l ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
    have h2 : (8:ℝ) ≤ Real.sqrt L := by
      rw [show (8:ℝ) = Real.sqrt 64 by
        rw [show (64:ℝ) = 8^2 by norm_num, Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt hL64
    have h3 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
    nlinarith [Real.sqrt_nonneg L]
  have hr := lamW_pos hx0
  set r := lamW x with hrdef
  have hsum : r + Real.log r = L := lamW_add_log hx0
  have hrL : r ≤ L := lamW_le_log hx0 (by linarith)
  set d := r - L + l with hddef
  have hlogr : Real.log r = l - d := by rw [hddef]; linarith
  have hd0 : 0 ≤ d := by
    have hle : Real.log r ≤ l := by rw [hldef]; exact Real.log_le_log hr hrL
    linarith [hlogr]
  have heq : Real.exp (-d) = 1 - (l - d)/L := by
    have h1 : Real.exp (-d) = Real.exp (Real.log r) / Real.exp l := by
      rw [← Real.exp_sub, hlogr]; ring_nf
    rw [h1, Real.exp_log hr, hldef, Real.exp_log hL0]
    field_simp
    linarith
  have hfin := delta_bound hL64 hl4 hlL hd0 heq
  have hrewrite : d - l/L = r - (L - l + l/L) := by rw [hddef]; ring
  rw [hrewrite] at hfin
  exact hfin

/-- **The conversion factor of Q565.**  With `L = log x`, `l = log L` and `r` the saddle
parameter (`r * exp r = x`), the normalization factor relating the two shapes of the
asymptotic formula has the expansion
`√(L/(r+1)) = 1 + (l-1)/(2L) + (3l²-10l+3)/(8L²) + O(l³/L³)`. -/
theorem sqrt_ratio_expansion (hx : Real.exp 4096 ≤ x) :
    |Real.sqrt (Real.log x / (lamW x + 1))
        - (1 + (Real.log (Real.log x) - 1)/(2 * Real.log x)
            + (3*(Real.log (Real.log x))^2 - 10*Real.log (Real.log x) + 3)
                / (8 * (Real.log x)^2))|
      ≤ 10 * (Real.log (Real.log x))^3 / (Real.log x)^3 := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (Real.exp_pos 4096) hx
  have hx64 : Real.exp 64 ≤ x :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) hx
  set L := Real.log x with hLdef
  have hL : 4096 ≤ L := by
    rw [hLdef, ← Real.log_exp 4096]
    exact Real.log_le_log (Real.exp_pos 4096) hx
  have hL0 : (0:ℝ) < L := by linarith
  set l := Real.log L with hldef
  have hl4 : 4 ≤ l := by
    have h : Real.log 4096 ≤ l := Real.log_le_log (by norm_num) hL
    have h64 : (4:ℝ) ≤ Real.log 4096 := by
      rw [show (4096:ℝ) = 2^12 by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hsqrt : (64:ℝ) ≤ Real.sqrt L := by
    rw [show (64:ℝ) = Real.sqrt 4096 by
      rw [show (4096:ℝ) = 64^2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hL
  have hlL : l * (1/L) ≤ 1/32 := by
    have h1 : l ≤ 2 * Real.sqrt L := log_le_two_sqrt hL0
    have h3 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
    rw [mul_one_div, div_le_iff₀ hL0]
    nlinarith [Real.sqrt_nonneg L]
  set v : ℝ := 1/L with hvdef
  have hv : (0:ℝ) < v := by rw [hvdef]; positivity
  set r := lamW x with hrdef
  have hrpos : 0 < r := lamW_pos hx0
  set e : ℝ := r - (L - l + l/L) with hedef
  have he : |e| ≤ l^2 * v^2 := by
    have h := lamW_expansion hx64
    rw [← hLdef, ← hldef, ← hrdef, ← hedef] at h
    rw [hvdef]
    calc |e| ≤ l^2/L^2 := h
      _ = l^2 * (1/L)^2 := by field_simp
  set u : ℝ := (1-l)*v + l*v^2 + e*v with hudef
  -- `(r+1)/L = 1 + u`
  have hru : L / (r + 1) = 1/(1+u) := by
    have hr1 : r + 1 = L * (1 + u) := by
      rw [hudef, hvdef, hedef]; field_simp; ring
    rw [hr1]
    have h1u : (0:ℝ) < 1 + u := by
      nlinarith [hrpos]
    field_simp
  -- `|u|` is small
  have hlv : l * v ≤ 1/32 := by rw [hvdef]; exact hlL
  have hvsmall : v ≤ 1/4096 := by
    rw [hvdef, div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hl0 : (0:ℝ) < l := by linarith
  have hu2lv : |u| ≤ 2 * (l * v) := by
    have h1 : |(1-l)*v| ≤ l * v := by
      rw [abs_mul, abs_of_pos hv, abs_of_nonpos (by linarith : (1:ℝ)-l ≤ 0)]
      nlinarith
    have h2 : |l*v^2| ≤ (l*v) * v := by
      rw [abs_of_nonneg (by positivity)]; nlinarith
    have h3 : |e*v| ≤ (l*v)^2 * v := by
      rw [abs_mul, abs_of_pos hv]
      have := he
      nlinarith [abs_nonneg e]
    have h4 : |u| ≤ |(1-l)*v| + |l*v^2| + |e*v| := by
      rw [hudef]
      exact (abs_add_three _ _ _)
    nlinarith [mul_pos hl0 hv]
  have huabs : |u| ≤ 1/8 := by nlinarith
  -- Taylor expansion of the inverse square root
  have hT := inv_sqrt_taylor huabs
  have hA := expansion_algebra hl4 hv hlv he
  rw [← hudef] at hA
  -- rewrite the target
  have hgoal : Real.sqrt (L / (r + 1)) = 1 / Real.sqrt (1 + u) := by
    rw [hru, one_div, one_div, Real.sqrt_inv]
  have htarget : (1 + (l - 1)/(2 * L) + (3*l^2 - 10*l + 3)/(8 * L^2))
      = 1 + (l-1)*v/2 + (3*l^2-10*l+3)*v^2/8 := by
    rw [hvdef]; field_simp
  rw [hgoal, htarget]
  have hcube : |u|^3 ≤ 8 * (l^3 * v^3) := by
    calc |u|^3 ≤ (2*(l*v))^3 := by
          exact pow_le_pow_left₀ (abs_nonneg u) hu2lv 3
      _ = 8 * (l^3*v^3) := by ring
  have hfinal : 10 * l^3 / L^3 = 10 * (l^3 * v^3) := by
    rw [hvdef]; field_simp
  rw [hfinal]
  calc |1 / Real.sqrt (1 + u) - (1 + (l-1)*v/2 + (3*l^2-10*l+3)*v^2/8)|
      ≤ |1 / Real.sqrt (1 + u) - (1 - u/2 + 3*u^2/8)|
        + |(1 - u/2 + 3*u^2/8) - (1 + (l-1)*v/2 + (3*l^2-10*l+3)*v^2/8)| := by
        exact abs_sub_le _ _ _
    _ ≤ |u|^3 + 2*l^3*v^3 := by
        have : |(1 - u/2 + 3*u^2/8) - (1 + (l-1)*v/2 + (3*l^2-10*l+3)*v^2/8)| ≤ 2*l^3*v^3 := by
          rw [hudef] at hA ⊢
          exact hA
        linarith
    _ ≤ 10 * (l^3 * v^3) := by linarith

end Expansion

/-! ## Dobinski's formula

The Bell numbers, as defined in Mathlib by the recurrence `B_{n+1} = ∑ C(n,k) B_k`, are
exactly the quantities `T(n) = e⁻¹ ∑_{k≥0} kⁿ/k!` appearing in the statement of Q565. -/

theorem summable_pow_div_fact (n : ℕ) : Summable (fun k : ℕ => (k:ℝ)^n / k !) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using (Real.summable_pow_div_factorial (1:ℝ))
    | (m+1) =>
      rw [← summable_nat_add_iff 1]
      have hrw : ∀ k : ℕ, ((k+1:ℕ):ℝ)^(m+1) / (k+1)! =
          ∑ j ∈ Finset.range (m+1), ((k:ℝ)^j / k !) * (m.choose j) := by
        intro k
        have hfac : ((k+1)! : ℝ) = (k+1) * k ! := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hk : ((k:ℝ)+1) ≠ 0 := by positivity
        rw [hfac]
        push_cast
        rw [show ((k:ℝ)+1)^(m+1) = ((k:ℝ)+1) * ((k:ℝ)+1)^m by ring, add_pow,
          mul_div_mul_left _ _ hk, Finset.sum_div]
        exact Finset.sum_congr rfl (fun j _ => by simp; ring)
      simp only [hrw]
      exact summable_sum (fun j hj => (ih j (by simp at hj; omega)).mul_right _)

theorem tsum_pow_div_fact_succ (m : ℕ) :
    ∑' k : ℕ, (k:ℝ)^(m+1) / k ! =
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * ∑' k : ℕ, (k:ℝ)^j / k ! := by
  have h0 : ∑' k : ℕ, (k:ℝ)^(m+1) / k ! = ∑' k : ℕ, ((k+1:ℕ):ℝ)^(m+1) / (k+1)! := by
    rw [Summable.tsum_eq_zero_add (summable_pow_div_fact (m+1))]
    simp
  rw [h0]
  have hrw : ∀ k : ℕ, ((k+1:ℕ):ℝ)^(m+1) / (k+1)! =
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * ((k:ℝ)^j / k !) := by
    intro k
    have hfac : ((k+1)! : ℝ) = (k+1) * k ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hk : ((k:ℝ)+1) ≠ 0 := by positivity
    rw [hfac]
    push_cast
    rw [show ((k:ℝ)+1)^(m+1) = ((k:ℝ)+1) * ((k:ℝ)+1)^m by ring, add_pow,
      mul_div_mul_left _ _ hk, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by simp; ring)
  simp only [hrw]
  rw [Summable.tsum_finsetSum (fun j _ => (summable_pow_div_fact j).mul_left ((m.choose j : ℝ)))]
  exact Finset.sum_congr rfl (fun j _ => tsum_mul_left)

/-- **Dobinski's formula**: `e * B n = ∑_{k≥0} kⁿ/k!`, i.e. the `n`-th Bell number equals
`T(n) = e⁻¹ ∑_{k≥0} kⁿ/k!`. -/
theorem dobinski (n : ℕ) : (Nat.bell n : ℝ) * Real.exp 1 = ∑' k : ℕ, (k:ℝ)^n / k ! := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [Nat.bell_zero, Nat.cast_one, one_mul, pow_zero]
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      simp
    | (m+1) =>
      rw [tsum_pow_div_fact_succ m]
      have hbell : (Nat.bell (m+1) : ℝ)
          = ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * Nat.bell j := by
        rw [Nat.bell_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        push_cast
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        simp only [Finset.mem_range] at hk
        have h1 : m + 1 - 1 - k = m - k := by omega
        have h2 : m - (m - k) = k := by omega
        rw [h1, h2, Nat.choose_symm (by omega)]
      rw [hbell, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      rw [← ih j (by omega)]
      ring

/-! ## The functions `w`, `f` and the saddle-point normalization -/

/-- `w(x)`, the inverse of `y ↦ y log y`: `W x = exp (lamW x)`. -/
noncomputable def W (x : ℝ) : ℝ := Real.exp (lamW x)

theorem W_pos (x : ℝ) : 0 < W x := Real.exp_pos _

/-- `w(x) log w(x) = x`. -/
theorem W_mul_log {x : ℝ} (hx : 0 ≤ x) : W x * Real.log (W x) = x := by
  rw [W, Real.log_exp, mul_comm]
  exact lamW_spec hx

/-- The function `f` of Q565: `f(x) = w(x)^x e^{w(x)-x-1} / √(log x)`. -/
noncomputable def fQ (x : ℝ) : ℝ := (W x) ^ x * Real.exp (W x - x - 1) / Real.sqrt (Real.log x)

/-- The saddle-point normalization: `g(x) = w(x)^x e^{w(x)-x-1} / √(r+1)`, where `r = lamW x`. -/
noncomputable def gQ (x : ℝ) : ℝ :=
  (W x) ^ x * Real.exp (W x - x - 1) / Real.sqrt (lamW x + 1)

theorem fQ_pos {x : ℝ} (hx : 1 < x) : 0 < fQ x :=
  div_pos (mul_pos (Real.rpow_pos_of_pos (W_pos x) x) (Real.exp_pos _))
    (Real.sqrt_pos.2 (Real.log_pos hx))

theorem gQ_pos {x : ℝ} (hx : 0 < x) : 0 < gQ x :=
  div_pos (mul_pos (Real.rpow_pos_of_pos (W_pos x) x) (Real.exp_pos _))
    (Real.sqrt_pos.2 (by linarith [lamW_nonneg hx.le]))

/-- The two normalizations differ exactly by the factor `√(log x/(r+1))`. -/
theorem gQ_eq {x : ℝ} (hx : 1 < x) : gQ x = fQ x * Real.sqrt (Real.log x / (lamW x + 1)) := by
  have h1 : 0 < Real.log x := Real.log_pos hx
  have h2 : (0:ℝ) < lamW x + 1 := by linarith [lamW_nonneg (by linarith : (0:ℝ) ≤ x)]
  have h3 : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h1)
  have h4 : Real.sqrt (lamW x + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h2)
  rw [Real.sqrt_div h1.le, fQ, gQ]
  field_simp

/-! ## Asymptotic bookkeeping -/

noncomputable def tq (n : ℕ) : ℝ := Real.log (Real.log n) / Real.log n

noncomputable def sq' (n : ℕ) : ℝ := 1 / Real.log n

theorem tendsto_log_nat : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_tq : Tendsto tq atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  exact h.comp tendsto_log_nat

theorem tendsto_sq' : Tendsto sq' atTop (𝓝 0) := by
  have h := tendsto_log_nat.inv_tendsto_atTop
  have he : sq' = (fun n : ℕ => Real.log n)⁻¹ := by funext n; simp [sq', one_div]
  rw [he]; exact h

theorem eventually_big : ∀ᶠ n : ℕ in atTop, Real.exp 4096 ≤ (n:ℝ) :=
  tendsto_natCast_atTop_atTop.eventually_ge_atTop _

/-- Basic size information available for all large `n`. -/
theorem eventually_log_facts : ∀ᶠ n : ℕ in atTop,
    (4096:ℝ) ≤ Real.log n ∧ 4 ≤ Real.log (Real.log n)
      ∧ Real.log (Real.log n) ≤ Real.log n / 4 := by
  filter_upwards [eventually_big] with n hn
  have hL : (4096:ℝ) ≤ Real.log n := by
    rw [← Real.log_exp 4096]
    exact Real.log_le_log (Real.exp_pos 4096) hn
  have hL0 : (0:ℝ) < Real.log n := by linarith
  refine ⟨hL, ?_, ?_⟩
  · have h : Real.log 4096 ≤ Real.log (Real.log n) := Real.log_le_log (by norm_num) hL
    have h64 : (4:ℝ) ≤ Real.log 4096 := by
      rw [show (4096:ℝ) = 2^12 by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_gt_d9]
    linarith
  · have h1 : Real.log (Real.log n) ≤ 2 * Real.sqrt (Real.log n) := log_le_two_sqrt hL0
    have h2 : (64:ℝ) ≤ Real.sqrt (Real.log n) := by
      rw [show (64:ℝ) = Real.sqrt 4096 by
        rw [show (4096:ℝ) = 64^2 by norm_num, Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt hL
    have h3 : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt hL0.le
    nlinarith [Real.sqrt_nonneg (Real.log n)]

/-- Second-order form of the conversion factor, with remainder `O(l³/L³)`. -/
theorem Sfac_bound_three : ∀ᶠ n : ℕ in atTop,
    |Real.sqrt (Real.log n / (lamW n + 1))
      - (1 + ((Real.log (Real.log n) - 1)/(2 * Real.log n)
          + (3*(Real.log (Real.log n))^2 - 10*Real.log (Real.log n) + 3)
              / (8 * (Real.log n)^2)))|
      ≤ 10 * ((Real.log (Real.log n))^3 / (Real.log n)^3) := by
  filter_upwards [eventually_big] with n hn
  have h := sqrt_ratio_expansion hn
  have hgroup : (1 + ((Real.log (Real.log n) - 1)/(2 * Real.log n)
          + (3*(Real.log (Real.log n))^2 - 10*Real.log (Real.log n) + 3)
              / (8 * (Real.log n)^2)))
      = (1 + (Real.log (Real.log n) - 1)/(2 * Real.log n)
          + (3*(Real.log (Real.log n))^2 - 10*Real.log (Real.log n) + 3)
              / (8 * (Real.log n)^2)) := by ring
  rw [hgroup]
  calc |Real.sqrt (Real.log n / (lamW n + 1))
      - (1 + (Real.log (Real.log n) - 1)/(2 * Real.log n)
          + (3*(Real.log (Real.log n))^2 - 10*Real.log (Real.log n) + 3)
              / (8 * (Real.log n)^2))|
      ≤ 10 * (Real.log (Real.log n))^3 / (Real.log n)^3 := h
    _ = 10 * ((Real.log (Real.log n))^3 / (Real.log n)^3) := by ring

/-- First-order form of the conversion factor, with remainder `O(l²/L²)`. -/
theorem Sfac_bound_two : ∀ᶠ n : ℕ in atTop,
    |Real.sqrt (Real.log n / (lamW n + 1))
      - (1 + (Real.log (Real.log n) - 1)/(2 * Real.log n))|
      ≤ 12 * ((Real.log (Real.log n))^2 / (Real.log n)^2) := by
  filter_upwards [Sfac_bound_three, eventually_log_facts] with n h3 hfacts
  obtain ⟨hL, hl4, hlL⟩ := hfacts
  set L := Real.log (n:ℝ)
  set l := Real.log L
  have hL0 : (0:ℝ) < L := by linarith
  have hl0 : (0:ℝ) < l := by linarith
  have hlLle : l ≤ L := by linarith
  have hcube : 10 * (l^3/L^3) ≤ 10 * (l^2/L^2) := by
    have : l^3/L^3 ≤ l^2/L^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg l) (sq_nonneg L)) (sub_nonneg.2 hlLle)]
    linarith
  have hquad : |(3*l^2 - 10*l + 3)/(8*L^2)| ≤ 2 * (l^2/L^2) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 8*L^2)]
    rw [div_le_iff₀ (by positivity)]
    have habs : |3*l^2 - 10*l + 3| ≤ 3*l^2 + 10*l + 3 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg l]
    have hlin : 3*l^2 + 10*l + 3 ≤ 16 * l^2 := by nlinarith
    have : 2 * (l^2/L^2) * (8*L^2) = 16 * l^2 := by field_simp; ring
    rw [this]
    linarith
  have htri := abs_add_le (Real.sqrt (L / (lamW n + 1))
      - (1 + ((l - 1)/(2 * L) + (3*l^2 - 10*l + 3)/(8 * L^2))))
      ((3*l^2 - 10*l + 3)/(8 * L^2))
  have heq : Real.sqrt (L / (lamW n + 1))
      - (1 + ((l - 1)/(2 * L) + (3*l^2 - 10*l + 3)/(8 * L^2)))
      + (3*l^2 - 10*l + 3)/(8 * L^2)
      = Real.sqrt (L / (lamW n + 1)) - (1 + (l - 1)/(2 * L)) := by ring
  rw [heq] at htri
  linarith

/-- The conversion factor tends to `1`. -/
theorem tendsto_Sfac :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log n / (lamW n + 1))) atTop (𝓝 1) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      |Real.sqrt (Real.log n / (lamW n + 1)) - 1|
        ≤ 12 * (tq n)^2 + |(tq n - sq' n)/2| := by
    filter_upwards [Sfac_bound_two, eventually_log_facts] with n hn hfacts
    obtain ⟨hL, _, _⟩ := hfacts
    have hL0 : (0:ℝ) < Real.log (n:ℝ) := by linarith
    have h1 : (Real.log (Real.log n) - 1)/(2*Real.log n) = (tq n - sq' n)/2 := by
      simp only [tq, sq']; field_simp
    have h2 : (Real.log (Real.log n))^2 / (Real.log n)^2 = (tq n)^2 := by
      simp only [tq]; field_simp
    rw [h1, h2] at hn
    have htri := abs_add_le
      (Real.sqrt (Real.log n / (lamW n + 1)) - (1 + (tq n - sq' n)/2)) ((tq n - sq' n)/2)
    have heq : Real.sqrt (Real.log n / (lamW n + 1)) - (1 + (tq n - sq' n)/2)
        + (tq n - sq' n)/2 = Real.sqrt (Real.log n / (lamW n + 1)) - 1 := by ring
    rw [heq] at htri
    linarith
  have hlim : Tendsto (fun n : ℕ => 12 * (tq n)^2 + |(tq n - sq' n)/2|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 12 * (tq n)^2) atTop (𝓝 0) := by
      simpa using (tendsto_tq.pow 2).const_mul 12
    have h2 : Tendsto (fun n : ℕ => |(tq n - sq' n)/2|) atTop (𝓝 0) := by
      simpa using ((tendsto_tq.sub tendsto_sq').div_const 2).abs
    simpa using h1.add h2
  have hsq := squeeze_zero' (Eventually.of_forall (fun n : ℕ => abs_nonneg _)) hbound hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using hsq

/-! ## The main results -/

/-- For all large `n` the two normalized ratios are related by the conversion factor. -/
theorem eventually_ratio_eq : ∀ᶠ n : ℕ in atTop,
    0 < Real.sqrt (Real.log n / (lamW n + 1)) ∧
    (Nat.bell n : ℝ) / fQ n
      = ((Nat.bell n : ℝ) / gQ n) * Real.sqrt (Real.log n / (lamW n + 1)) := by
  filter_upwards [eventually_big] with n hn
  have hx1 : (1:ℝ) < (n:ℝ) := lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (4096:ℝ)]) hn
  have hL : (0:ℝ) < Real.log n := Real.log_pos hx1
  have hr : (0:ℝ) < lamW n + 1 := by linarith [lamW_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ))]
  have hS : 0 < Real.sqrt (Real.log n / (lamW n + 1)) := Real.sqrt_pos.2 (by positivity)
  refine ⟨hS, ?_⟩
  rw [gQ_eq hx1]
  have hf : fQ (n:ℝ) ≠ 0 := ne_of_gt (fQ_pos hx1)
  field_simp

/-- **Transfer lemma.**  Passing from the saddle-point normalization `g` to the
normalization `f` used in Q565 changes the expansion exactly by the conversion factor
`√(log n/(r+1))`. -/
theorem ratio_transfer {cc bb : ℕ → ℝ}
    (hSc : (fun n : ℕ => Real.sqrt (Real.log n / (lamW n + 1)) - (1 + cc n)) =O[atTop] bb) :
    ((fun n : ℕ => (Nat.bell n : ℝ) / gQ n - 1) =O[atTop] bb)
      ↔ ((fun n : ℕ => (Nat.bell n : ℝ) / fQ n - (1 + cc n)) =O[atTop] bb) := by
  set S : ℕ → ℝ := fun n => Real.sqrt (Real.log n / (lamW n + 1)) with hSdef
  set rho : ℕ → ℝ := fun n => (Nat.bell n : ℝ) / gQ n with hrho
  have hSO : S =O[atTop] (fun _ : ℕ => (1:ℝ)) := Tendsto.isBigO_one ℝ tendsto_Sfac
  have hSinv : (fun n : ℕ => (S n)⁻¹) =O[atTop] (fun _ : ℕ => (1:ℝ)) :=
    Tendsto.isBigO_one ℝ (tendsto_Sfac.inv₀ one_ne_zero)
  constructor
  · intro hr
    have h1 : (fun n : ℕ => (rho n - 1) * S n) =O[atTop] bb := by
      simpa using hr.mul hSO
    refine (h1.add hSc).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ratio_eq] with n hn
    rw [hSdef, hrho]
    simp only
    rw [hn.2]
    ring
  · intro hD
    have h1 : (fun n : ℕ => (rho n - 1) * S n) =O[atTop] bb := by
      refine (hD.sub hSc).congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_ratio_eq] with n hn
      rw [hSdef, hrho]
      simp only
      rw [hn.2]
      ring
    have h3 : (fun n : ℕ => ((rho n - 1) * S n) * (S n)⁻¹) =O[atTop] bb := by
      simpa using h1.mul hSinv
    refine h3.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ratio_eq] with n hn
    have hS0 : S n ≠ 0 := ne_of_gt hn.1
    rw [mul_assoc, mul_inv_cancel₀ hS0, mul_one]

theorem Sfac_isBigO_two :
    (fun n : ℕ => Real.sqrt (Real.log n / (lamW n + 1))
        - (1 + (Real.log (Real.log n) - 1)/(2 * Real.log n)))
      =O[atTop] (fun n : ℕ => (Real.log (Real.log n))^2 / (Real.log n)^2) := by
  refine Asymptotics.IsBigO.of_bound 12 ?_
  filter_upwards [Sfac_bound_two, eventually_log_facts] with n hn hfacts
  obtain ⟨hL, hl4, _⟩ := hfacts
  have hpos : (0:ℝ) ≤ (Real.log (Real.log n))^2 / (Real.log n)^2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  exact hn

theorem Sfac_isBigO_three :
    (fun n : ℕ => Real.sqrt (Real.log n / (lamW n + 1))
        - (1 + ((Real.log (Real.log n) - 1)/(2 * Real.log n)
            + (3*(Real.log (Real.log n))^2 - 10*Real.log (Real.log n) + 3)
                / (8 * (Real.log n)^2))))
      =O[atTop] (fun n : ℕ => (Real.log (Real.log n))^3 / (Real.log n)^3) := by
  refine Asymptotics.IsBigO.of_bound 10 ?_
  filter_upwards [Sfac_bound_three, eventually_log_facts] with n hn hfacts
  obtain ⟨hL, hl4, _⟩ := hfacts
  have hl0 : (0:ℝ) ≤ Real.log (Real.log n) := by linarith
  have hL0 : (0:ℝ) < Real.log (n:ℝ) := by linarith
  have hpos : (0:ℝ) ≤ (Real.log (Real.log n))^3 / (Real.log n)^3 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  exact hn

/-- **Q565, first correction term.**

With `L = log n`, `l = log log n`, `T(n)` the `n`-th Bell number (equivalently, by
`Q565.dobinski`, `T(n) = e⁻¹ ∑_k kⁿ/k!`), `f` the function of the question and `g` the
saddle-point normalization `w(n)^n e^{w(n)-n-1}/√(r+1)`, the statement

  `T(n) = f(n) (1 + (l-1)/(2L) + O(l²/L²))`

is *equivalent* to the saddle-point statement `T(n) = g(n)(1 + O(l²/L²))`.
The whole content of Q565 — the extraction of the next term `(log log n - 1)/(2 log n)` —
is the conversion factor `√(L/(r+1))`, which is what this equivalence isolates. -/
theorem Q565_first_correction :
    ((fun n : ℕ => (Nat.bell n : ℝ) / gQ n - 1) =O[atTop]
        (fun n : ℕ => (Real.log (Real.log n))^2 / (Real.log n)^2))
      ↔ ((fun n : ℕ => (Nat.bell n : ℝ) / fQ n
            - (1 + (Real.log (Real.log n) - 1)/(2 * Real.log n))) =O[atTop]
        (fun n : ℕ => (Real.log (Real.log n))^2 / (Real.log n)^2)) :=
  ratio_transfer Sfac_isBigO_two

/-- **Q565, two correction terms.**  Same statement one order further:

  `T(n) = f(n) (1 + (l-1)/(2L) + (3l²-10l+3)/(8L²) + O(l³/L³))`

is equivalent to the saddle-point statement `T(n) = g(n)(1 + O(l³/L³))`. -/
theorem Q565_second_correction :
    ((fun n : ℕ => (Nat.bell n : ℝ) / gQ n - 1) =O[atTop]
        (fun n : ℕ => (Real.log (Real.log n))^3 / (Real.log n)^3))
      ↔ ((fun n : ℕ => (Nat.bell n : ℝ) / fQ n
            - (1 + ((Real.log (Real.log n) - 1)/(2 * Real.log n)
                + (3*(Real.log (Real.log n))^2 - 10*Real.log (Real.log n) + 3)
                    / (8 * (Real.log n)^2)))) =O[atTop]
        (fun n : ℕ => (Real.log (Real.log n))^3 / (Real.log n)^3)) :=
  ratio_transfer Sfac_isBigO_three

/-! ## The asymptotic-equivalence form of the answer -/

theorem tendsto_loglog : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat

theorem tq_isLittleO_one : tq =o[atTop] (fun _ : ℕ => (1:ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).2 tendsto_tq

theorem inv_loglog_isLittleO_one :
    (fun n : ℕ => 1/(2 * Real.log (Real.log n))) =o[atTop] (fun _ : ℕ => (1:ℝ)) := by
  refine (Asymptotics.isLittleO_one_iff ℝ).2 ?_
  have h : Tendsto (fun n : ℕ => 2 * Real.log (Real.log n)) atTop atTop :=
    tendsto_loglog.const_mul_atTop (by norm_num)
  have he : (fun n : ℕ => 1/(2 * Real.log (Real.log n)))
      = (fun n : ℕ => 2 * Real.log (Real.log n))⁻¹ := by funext n; simp [one_div]
  rw [he]; exact h.inv_tendsto_atTop

theorem sq_isLittleO :
    (fun n : ℕ => (Real.log (Real.log n))^2/(Real.log n)^2) =o[atTop]
      (fun n : ℕ => Real.log (Real.log n)/Real.log n) := by
  have h := (Asymptotics.isBigO_refl tq atTop).mul_isLittleO tq_isLittleO_one
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_log_facts] with n hf
    obtain ⟨hL, _, _⟩ := hf
    have hL0 : (0:ℝ) < Real.log (n:ℝ) := by linarith
    simp only [tq]; field_simp
  · filter_upwards with n
    simp [tq]

theorem invL_isLittleO :
    (fun n : ℕ => 1/(2 * Real.log n)) =o[atTop]
      (fun n : ℕ => Real.log (Real.log n)/Real.log n) := by
  have h := (Asymptotics.isBigO_refl tq atTop).mul_isLittleO inv_loglog_isLittleO_one
  refine h.congr' ?_ ?_
  · filter_upwards [eventually_log_facts] with n hf
    obtain ⟨hL, hl4, _⟩ := hf
    have hL0 : (0:ℝ) < Real.log (n:ℝ) := by linarith
    have hl0 : (0:ℝ) < Real.log (Real.log (n:ℝ)) := by linarith
    simp only [tq]; field_simp
  · filter_upwards with n
    simp [tq]

/-- Little-o version of the transfer lemma. -/
theorem ratio_transfer_littleO {cc bb : ℕ → ℝ}
    (hSc : (fun n : ℕ => Real.sqrt (Real.log n / (lamW n + 1)) - (1 + cc n)) =o[atTop] bb) :
    ((fun n : ℕ => (Nat.bell n : ℝ) / gQ n - 1) =o[atTop] bb)
      ↔ ((fun n : ℕ => (Nat.bell n : ℝ) / fQ n - (1 + cc n)) =o[atTop] bb) := by
  set S : ℕ → ℝ := fun n => Real.sqrt (Real.log n / (lamW n + 1)) with hSdef
  set rho : ℕ → ℝ := fun n => (Nat.bell n : ℝ) / gQ n with hrho
  have hSO : S =O[atTop] (fun _ : ℕ => (1:ℝ)) := Tendsto.isBigO_one ℝ tendsto_Sfac
  have hSinv : (fun n : ℕ => (S n)⁻¹) =O[atTop] (fun _ : ℕ => (1:ℝ)) :=
    Tendsto.isBigO_one ℝ (tendsto_Sfac.inv₀ one_ne_zero)
  constructor
  · intro hr
    have h1 : (fun n : ℕ => (rho n - 1) * S n) =o[atTop] bb := by
      simpa using hr.mul_isBigO hSO
    refine (h1.add hSc).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ratio_eq] with n hn
    rw [hSdef, hrho]
    simp only
    rw [hn.2]
    ring
  · intro hD
    have h1 : (fun n : ℕ => (rho n - 1) * S n) =o[atTop] bb := by
      refine (hD.sub hSc).congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_ratio_eq] with n hn
      rw [hSdef, hrho]
      simp only
      rw [hn.2]
      ring
    have h3 : (fun n : ℕ => ((rho n - 1) * S n) * (S n)⁻¹) =o[atTop] bb := by
      simpa using h1.mul_isBigO hSinv
    refine h3.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ratio_eq] with n hn
    have hS0 : S n ≠ 0 := ne_of_gt hn.1
    rw [mul_assoc, mul_inv_cancel₀ hS0, mul_one]

theorem Sfac_isLittleO :
    (fun n : ℕ => Real.sqrt (Real.log n / (lamW n + 1))
        - (1 + Real.log (Real.log n)/(2 * Real.log n))) =o[atTop]
      (fun n : ℕ => Real.log (Real.log n)/Real.log n) := by
  have h := (Sfac_isBigO_two.trans_isLittleO sq_isLittleO).sub invL_isLittleO
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards with n
  ring

/-- **Q565, asymptotic-equivalence form.**

`T(n) - f(n) ∼ (log log n)/(2 log n) · f(n)` is *equivalent* to the saddle-point statement
`T(n) = g(n)(1 + o(log log n/log n))`. -/
theorem Q565_asymptotic_form :
    ((fun n : ℕ => (Nat.bell n : ℝ)/gQ n - 1) =o[atTop]
        (fun n : ℕ => Real.log (Real.log n)/Real.log n))
      ↔ ((fun n : ℕ => (Nat.bell n : ℝ)/fQ n - 1)
            ~[atTop] (fun n : ℕ => Real.log (Real.log n)/(2 * Real.log n))) := by
  rw [Asymptotics.IsEquivalent]
  have hhalf : ((fun n : ℕ => ((Nat.bell n : ℝ)/fQ n - 1)
        - Real.log (Real.log n)/(2 * Real.log n)) =o[atTop]
        (fun n : ℕ => Real.log (Real.log n)/(2 * Real.log n)))
      ↔ ((fun n : ℕ => ((Nat.bell n : ℝ)/fQ n - 1)
        - Real.log (Real.log n)/(2 * Real.log n)) =o[atTop]
        (fun n : ℕ => Real.log (Real.log n)/Real.log n)) := by
    have he : (fun n : ℕ => Real.log (Real.log n)/(2 * Real.log n))
        = (fun n : ℕ => (2:ℝ)⁻¹ * (Real.log (Real.log n)/Real.log n)) := by
      funext n; field_simp
    rw [he]
    exact isLittleO_const_mul_right_iff (by norm_num)
  rw [show ((fun n : ℕ => (Nat.bell n : ℝ)/fQ n - 1)
      - fun n : ℕ => Real.log (Real.log n)/(2 * Real.log n))
      = (fun n : ℕ => ((Nat.bell n : ℝ)/fQ n - 1)
        - Real.log (Real.log n)/(2 * Real.log n)) from rfl, hhalf]
  rw [ratio_transfer_littleO (cc := fun n : ℕ => Real.log (Real.log n)/(2 * Real.log n))
    (bb := fun n : ℕ => Real.log (Real.log n)/Real.log n) Sfac_isLittleO]
  constructor
  · intro h
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards with n; ring
  · intro h
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards with n; ring

end Q565
