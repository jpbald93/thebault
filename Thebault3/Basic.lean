import Mathlib

/-!
# Thébault's problem III (Sawayama–Thébault theorem)

Let `ABC` be a triangle and `D` a point strictly inside segment `BC`. Let `P` and `Q` be the
centres of the two circles each tangent to line `AD`, tangent to line `BC`, and internally
tangent to the circumcircle of `ABC`, lying in the angles `∠ADB` and `∠ADC` respectively.
Then `P`, `Q` and the incentre `I` of `ABC` are collinear.

The proof is a coordinate certificate: in the frame with `D` at the origin and `BC` on the
x-axis, the centres and the incentre are pinned down by polynomial equations, and the
collinearity is an explicit `linear_combination` of them (`core`).
-/

open EuclideanGeometry

namespace Thebault3

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The triangle `ABC` as a Mathlib `Affine.Triangle`. -/
noncomputable def tri (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Affine.Triangle ℝ Pt :=
  ⟨![A, B, C], h⟩

/-- `P` is the centre of a Thébault circle of triangle `ABC` for the cevian `AD`, lying in the
angle `∠ADX` (`X = B` or `X = C`): the circle of radius `r > 0` centred at `P` is tangent to
lines `AD` and `BC` (`P` is at distance `r` from both), is internally tangent to the
circumcircle (`dist P O = R - r`), and lies on the same side of `AD` as `X` and on the same side
of `BC` as `A`. -/
def IsThebaultCircle (A B C D X P : Pt) (h : AffineIndependent ℝ ![A, B, C]) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.infDist P (line[ℝ, A, D] : Set Pt) = r ∧
    Metric.infDist P (line[ℝ, B, C] : Set Pt) = r ∧
    dist P (tri A B C h).circumcenter = (tri A B C h).circumradius - r ∧
    (line[ℝ, A, D]).SSameSide P X ∧
    (line[ℝ, B, C]).SSameSide P A

/-! ### Real-algebra core -/

/-- Uniqueness of the positive root: `al > 0`, `ga < 0`. -/
theorem pos_root_unique (al be ga Y N u : ℝ) (hal : 0 < al) (hga : ga < 0) (hY : 0 < Y)
    (hN : 0 < N) (h1 : al * Y ^ 2 + be * Y * u + ga * u ^ 2 = 0)
    (h2 : al * N ^ 2 + be * N * u + ga * u ^ 2 = 0) : Y = N := by
  by_contra hne
  have h3 : al * (Y + N) + be * u = 0 := by
    have : (Y - N) * (al * (Y + N) + be * u) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have h4 : ga * u ^ 2 = al * N * Y := by linear_combination h1 - Y * h3
  have h5 : ga * u ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hga.le (sq_nonneg u)
  have h6 : 0 < al * N * Y := by positivity
  linarith

/-- Positivity facts in the coordinate configuration. -/
theorem core_pos (p q m n L b c : ℝ) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n) (hL0 : 0 < L)
    (hb0 : 0 < b) (hc0 : 0 < c) (hL : L ^ 2 = p ^ 2 + q ^ 2) (hb : b ^ 2 = (p - n) ^ 2 + q ^ 2)
    (hc : c ^ 2 = (p + m) ^ 2 + q ^ 2) :
    0 < L - p ∧ 0 < L + p ∧ 0 < (m + n) * L + b * m - c * n ∧
      0 < (m + n) * L + c * n - b * m := by
  have hpL : p ^ 2 < L ^ 2 := by linarith [pow_pos hq 2]
  have hLp : p < L := (abs_lt_of_sq_lt_sq' hpL hL0.le).2
  have hLm : -p < L := by linarith [(abs_lt_of_sq_lt_sq' hpL hL0.le).1]
  have hcL : c < L + m := by
    have : c ^ 2 < (L + m) ^ 2 := by
      have : (L + m) ^ 2 - c ^ 2 = 2 * m * (L - p) := by linear_combination hL - hc
      have : 0 < 2 * m * (L - p) := by have := sub_pos.2 hLp; positivity
      linarith
    exact (abs_lt_of_sq_lt_sq' this (by positivity)).2
  have hbL : n - L < b := by
    have : (n - L) ^ 2 < b ^ 2 := by
      have : b ^ 2 - (n - L) ^ 2 = 2 * n * (L - p) := by linear_combination hb - hL
      have : 0 < 2 * n * (L - p) := by have := sub_pos.2 hLp; positivity
      linarith
    exact (abs_lt_of_sq_lt_sq' this hb0.le).2
  have hbL' : b < L + n := by
    have : b ^ 2 < (L + n) ^ 2 := by
      have : (L + n) ^ 2 - b ^ 2 = 2 * n * (L + p) := by linear_combination hL - hb
      have : 0 < 2 * n * (L + p) := by have : 0 < L + p := (by linarith); positivity
      linarith
    exact (abs_lt_of_sq_lt_sq' this (by positivity)).2
  have hcL' : m - L < c := by
    have : (m - L) ^ 2 < c ^ 2 := by
      have : c ^ 2 - (m - L) ^ 2 = 2 * m * (L + p) := by linear_combination hc - hL
      have : 0 < 2 * m * (L + p) := by have : 0 < L + p := (by linarith); positivity
      linarith
    exact (abs_lt_of_sq_lt_sq' this hc0.le).2
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_left hcL hn, mul_lt_mul_of_pos_left hbL hm]
  · nlinarith [mul_lt_mul_of_pos_left hbL' hm, mul_lt_mul_of_pos_left hcL' hn]

/-- The algebraic core of the Sawayama–Thébault theorem, in coordinates with `D = (0,0)`,
`B = (-m,0)`, `C = (n,0)`, `A = (p,q)`, `L = AD`, `b = AC`, `c = AB`, circumcentre `(o1,o2)`,
circumradius `R`, Thébault centres `(x1,y1)`, `(x2,y2)` and incentre `(i1,i2)`. -/
theorem core (p q m n L b c o1 o2 R x1 y1 x2 y2 i1 i2 : ℝ) (hq : 0 < q) (hm : 0 < m)
    (hn : 0 < n) (hL0 : 0 < L) (hb0 : 0 < b) (hc0 : 0 < c) (hR0 : 0 ≤ R)
    (hL : L ^ 2 = p ^ 2 + q ^ 2) (hb : b ^ 2 = (p - n) ^ 2 + q ^ 2)
    (hc : c ^ 2 = (p + m) ^ 2 + q ^ 2)
    (hO1 : (o1 - p) ^ 2 + (o2 - q) ^ 2 = R ^ 2) (hO2 : (o1 + m) ^ 2 + o2 ^ 2 = R ^ 2)
    (hO3 : (o1 - n) ^ 2 + o2 ^ 2 = R ^ 2)
    (hy1 : 0 < y1) (hx1 : q * x1 = (p - L) * y1)
    (hP1 : (x1 - o1) ^ 2 + (y1 - o2) ^ 2 = (R - y1) ^ 2)
    (hy2 : 0 < y2) (hx2 : q * x2 = (p + L) * y2)
    (hP2 : (x2 - o1) ^ 2 + (y2 - o2) ^ 2 = (R - y2) ^ 2)
    (hi1 : (m + n + b + c) * i1 = (m + n) * p - b * m + c * n) (hi2 : (m + n + b + c) * i2 = (m + n) * q) :
    (x2 - x1) * (i2 - y1) - (y2 - y1) * (i1 - x1) = 0 := by
  obtain ⟨hLp, hLm, hM1, hM2⟩ := core_pos p q m n L b c hq hm hn hL0 hb0 hc0 hL hb hc
  have hmn : m + n ≠ 0 := by positivity
  have ho1 : 2 * o1 = n - m := by
    have : (m + n) * (2 * o1) = (m + n) * (n - m) := by linear_combination hO2 - hO3
    exact mul_left_cancel₀ hmn this
  have ho2 : 2 * q * o2 = (p ^ 2 + q ^ 2 - m * n - n * p + m * p) := by
    linear_combination hO2 - hO1 - (m + p) * ho1
  have hRsq : (2 * q * R) ^ 2 = (b * c) ^ 2 := by linear_combination (-4*q^2) * hO2 + (3*m*q^2 + n*q^2 + 2*o1*q^2) * ho1 + (-m*n + m*p - n*p + 2*o2*q + p^2 + q^2) * ho2 + (-c^2) * hb + (-n^2 + 2*n*p - p^2 - q^2) * hc
  have hR : 2 * q * R = b * c :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 hRsq
  have hu : 0 < (q * (m + n + b + c)) := by positivity
  have hN1 : 0 < ((L + p) * ((m + n) * L + b * m - c * n)) := mul_pos hLm hM1
  have hN2 : 0 < ((L - p) * ((m + n) * L + c * n - b * m)) := mul_pos hLp hM2
  have hq1 : (L - p) ^ 2 * y1 ^ 2 + (q * (b * c - (p ^ 2 + q ^ 2 - m * n - n * p + m * p) - (n - m) * (p - L))) * y1 + (-(m * n * q ^ 2)) = 0 := by
    linear_combination (q^2) * hP1 + (L*y1 + 2*o1*q - p*y1 - q*x1) * hx1 + (-L*q*y1 + m*q^2/4 - n*q^2/4 - o1*q^2/2 + p*q*y1) * ho1 + (m*n/4 - m*p/4 + n*p/4 - o2*q/2 - p^2/4 - q^2/4 + q*y1) * ho2 + (R*q/2 + b*c/4 - q*y1) * hR + (c^2/4) * hb + (n^2/4 - n*p/2 + p^2/4 + q^2/4) * hc
  have hq2 : (L + p) ^ 2 * y2 ^ 2 + (q * (b * c - (p ^ 2 + q ^ 2 - m * n - n * p + m * p) - (n - m) * (p + L))) * y2 + (-(m * n * q ^ 2)) = 0 := by
    linear_combination (q^2) * hP2 + (-L*y2 + 2*o1*q - p*y2 - q*x2) * hx2 + (L*q*y2 + m*q^2/4 - n*q^2/4 - o1*q^2/2 + p*q*y2) * ho1 + (m*n/4 - m*p/4 + n*p/4 - o2*q/2 - p^2/4 - q^2/4 + q*y2) * ho2 + (R*q/2 + b*c/4 - q*y2) * hR + (c^2/4) * hb + (n^2/4 - n*p/2 + p^2/4 + q^2/4) * hc
  have hH1 : (L - p) ^ 2 * ((L + p) * ((m + n) * L + b * m - c * n)) ^ 2 + (q * (b * c - (p ^ 2 + q ^ 2 - m * n - n * p + m * p) - (n - m) * (p - L))) * ((L + p) * ((m + n) * L + b * m - c * n)) * (q * (m + n + b + c)) + (-(m * n * q ^ 2)) * (q * (m + n + b + c)) ^ 2 = 0 := by
    linear_combination (L^4*m^2 + 2*L^4*m*n + L^4*n^2 + 2*L^3*b*m^2 + 2*L^3*b*m*n - 2*L^3*c*m*n - 2*L^3*c*n^2 + L^2*b^2*m^2 - 2*L^2*b*c*m*n + L^2*c^2*n^2 - L^2*m^2*p^2 + L^2*m^2*q^2 - 2*L^2*m*n*p^2 + 2*L^2*m*n*q^2 - L^2*n^2*p^2 + L^2*n^2*q^2 - 2*L*b*m^2*p^2 + L*b*m^2*q^2 - 2*L*b*m*n*p^2 + 2*L*b*m*n*q^2 + L*b*n^2*q^2 - L*c*m^2*q^2 + 2*L*c*m*n*p^2 - 2*L*c*m*n*q^2 + 2*L*c*n^2*p^2 - L*c*n^2*q^2 - L*m^3*q^2 - L*m^2*n*q^2 + L*m*n^2*q^2 + L*n^3*q^2 + b^2*c*m*q^2 + b^2*c*n*q^2 - b^2*m^2*p^2 + b^2*m*n*q^2 + b*c^2*m*q^2 + b*c^2*n*q^2 + 2*b*c*m*n*p^2 + 2*b*c*m*n*q^2 - b*m^3*q^2 + b*m^2*n*q^2 - b*m^2*p*q^2 + 2*b*m*n^2*q^2 - b*m*p^2*q^2 - b*m*q^4 + b*n^2*p*q^2 - b*n*p^2*q^2 - b*n*q^4 + c^2*m*n*q^2 - c^2*n^2*p^2 + 2*c*m^2*n*q^2 - c*m^2*p*q^2 + c*m*n^2*q^2 - c*m*p^2*q^2 - c*m*q^4 - c*n^3*q^2 + c*n^2*p*q^2 - c*n*p^2*q^2 - c*n*q^4 + m^3*n*q^2 - m^3*p*q^2 + 2*m^2*n^2*q^2 - m^2*n*p*q^2 - m^2*p^2*q^2 + m*n^3*q^2 + m*n^2*p*q^2 - 2*m*n*p^2*q^2 + n^3*p*q^2 - n^2*p^2*q^2) * hL + (L*b*c*m*q^2 + L*c^2*m*q^2 - L*c^2*n*q^2 + L*c*m^2*q^2 + L*c*m*n*q^2 + L*c*m*p*q^2 + L*c*n*p*q^2 + L*m^2*n*q^2 - L*m^2*p*q^2 + L*m*n*p*q^2 - L*m*p^2*q^2 - L*m*q^4 + b*c*m*p*q^2 + c^2*m*p*q^2 - c^2*n*p*q^2 + c*m^2*p*q^2 + c*m*n*p*q^2 + c*m*p^2*q^2 + c*m*q^4 + c*n*p^2*q^2 + c*n*q^4 + m^2*n*p*q^2 - m^2*p^2*q^2 + m*n*p^2*q^2 - m*p^3*q^2 - m*p*q^4) * hb + (-L*b*c*n*q^2 - L*b*m*n*q^2 + L*b*m*p*q^2 - L*b*n^2*q^2 + L*b*n*p*q^2 - L*m*n*p*q^2 + L*m*p^2*q^2 + L*m*q^4 - L*n^3*q^2 + L*n^2*p*q^2 - b*c*n*p*q^2 - b*m*n*p*q^2 + b*m*p^2*q^2 + b*m*q^4 - b*n^2*p*q^2 + b*n*p^2*q^2 + b*n*q^4 - m*n*p^2*q^2 + m*p^3*q^2 + m*p*q^4 - n^3*p*q^2 + n^2*p^2*q^2) * hc
  have hH2 : (L + p) ^ 2 * ((L - p) * ((m + n) * L + c * n - b * m)) ^ 2 + (q * (b * c - (p ^ 2 + q ^ 2 - m * n - n * p + m * p) - (n - m) * (p + L))) * ((L - p) * ((m + n) * L + c * n - b * m)) * (q * (m + n + b + c)) + (-(m * n * q ^ 2)) * (q * (m + n + b + c)) ^ 2 = 0 := by
    linear_combination (L^4*m^2 + 2*L^4*m*n + L^4*n^2 - 2*L^3*b*m^2 - 2*L^3*b*m*n + 2*L^3*c*m*n + 2*L^3*c*n^2 + L^2*b^2*m^2 - 2*L^2*b*c*m*n + L^2*c^2*n^2 - L^2*m^2*p^2 + L^2*m^2*q^2 - 2*L^2*m*n*p^2 + 2*L^2*m*n*q^2 - L^2*n^2*p^2 + L^2*n^2*q^2 + 2*L*b*m^2*p^2 - L*b*m^2*q^2 + 2*L*b*m*n*p^2 - 2*L*b*m*n*q^2 - L*b*n^2*q^2 + L*c*m^2*q^2 - 2*L*c*m*n*p^2 + 2*L*c*m*n*q^2 - 2*L*c*n^2*p^2 + L*c*n^2*q^2 + L*m^3*q^2 + L*m^2*n*q^2 - L*m*n^2*q^2 - L*n^3*q^2 + b^2*c*m*q^2 + b^2*c*n*q^2 - b^2*m^2*p^2 + b^2*m*n*q^2 + b*c^2*m*q^2 + b*c^2*n*q^2 + 2*b*c*m*n*p^2 + 2*b*c*m*n*q^2 - b*m^3*q^2 + b*m^2*n*q^2 - b*m^2*p*q^2 + 2*b*m*n^2*q^2 - b*m*p^2*q^2 - b*m*q^4 + b*n^2*p*q^2 - b*n*p^2*q^2 - b*n*q^4 + c^2*m*n*q^2 - c^2*n^2*p^2 + 2*c*m^2*n*q^2 - c*m^2*p*q^2 + c*m*n^2*q^2 - c*m*p^2*q^2 - c*m*q^4 - c*n^3*q^2 + c*n^2*p*q^2 - c*n*p^2*q^2 - c*n*q^4 + m^3*n*q^2 - m^3*p*q^2 + 2*m^2*n^2*q^2 - m^2*n*p*q^2 - m^2*p^2*q^2 + m*n^3*q^2 + m*n^2*p*q^2 - 2*m*n*p^2*q^2 + n^3*p*q^2 - n^2*p^2*q^2) * hL + (-L*b*c*m*q^2 - L*c^2*m*q^2 + L*c^2*n*q^2 - L*c*m^2*q^2 - L*c*m*n*q^2 - L*c*m*p*q^2 - L*c*n*p*q^2 - L*m^2*n*q^2 + L*m^2*p*q^2 - L*m*n*p*q^2 + L*m*p^2*q^2 + L*m*q^4 + b*c*m*p*q^2 + c^2*m*p*q^2 - c^2*n*p*q^2 + c*m^2*p*q^2 + c*m*n*p*q^2 + c*m*p^2*q^2 + c*m*q^4 + c*n*p^2*q^2 + c*n*q^4 + m^2*n*p*q^2 - m^2*p^2*q^2 + m*n*p^2*q^2 - m*p^3*q^2 - m*p*q^4) * hb + (L*b*c*n*q^2 + L*b*m*n*q^2 - L*b*m*p*q^2 + L*b*n^2*q^2 - L*b*n*p*q^2 + L*m*n*p*q^2 - L*m*p^2*q^2 - L*m*q^4 + L*n^3*q^2 - L*n^2*p*q^2 - b*c*n*p*q^2 - b*m*n*p*q^2 + b*m*p^2*q^2 + b*m*q^4 - b*n^2*p*q^2 + b*n*p^2*q^2 + b*n*q^4 - m*n*p^2*q^2 + m*p^3*q^2 + m*p*q^4 - n^3*p*q^2 + n^2*p^2*q^2) * hc
  have hga : (-(m * n * q ^ 2)) < 0 := by
    have : 0 < m * n * q ^ 2 := by positivity
    linarith
  have hY1 : (q * (m + n + b + c)) * y1 = ((L + p) * ((m + n) * L + b * m - c * n)) := by
    refine pos_root_unique _ _ _ _ _ (q * (m + n + b + c)) (pow_pos hLp 2) hga (by positivity) hN1 ?_ hH1
    linear_combination (q * (m + n + b + c)) ^ 2 * hq1
  have hY2 : (q * (m + n + b + c)) * y2 = ((L - p) * ((m + n) * L + c * n - b * m)) := by
    refine pos_root_unique _ _ _ _ _ (q * (m + n + b + c)) (pow_pos hLm 2) hga (by positivity) hN2 ?_ hH2
    linear_combination (q * (m + n + b + c)) ^ 2 * hq2
  have hfin : q * (q * (m + n + b + c)) ^ 2 * (m + n + b + c) * ((x2 - x1) * (i2 - y1) - (y2 - y1) * (i1 - x1)) = 0 := by
    linear_combination (b^2*q^3*y1 - b^2*q^3*y2 + 2*b*c*q^3*y1 - 2*b*c*q^3*y2 + 2*b*m*q^3*y1 - 2*b*m*q^3*y2 + 2*b*n*q^3*y1 - 2*b*n*q^3*y2 + c^2*q^3*y1 - c^2*q^3*y2 + 2*c*m*q^3*y1 - 2*c*m*q^3*y2 + 2*c*n*q^3*y1 - 2*c*n*q^3*y2 + m^2*q^3*y1 - m^2*q^3*y2 + 2*m*n*q^3*y1 - 2*m*n*q^3*y2 + n^2*q^3*y1 - n^2*q^3*y2) * hi1 + (-b^2*q^3*x1 + b^2*q^3*x2 - 2*b*c*q^3*x1 + 2*b*c*q^3*x2 - 2*b*m*q^3*x1 + 2*b*m*q^3*x2 - 2*b*n*q^3*x1 + 2*b*n*q^3*x2 - c^2*q^3*x1 + c^2*q^3*x2 - 2*c*m*q^3*x1 + 2*c*m*q^3*x2 - 2*c*n*q^3*x1 + 2*c*n*q^3*x2 - m^2*q^3*x1 + m^2*q^3*x2 - 2*m*n*q^3*x1 + 2*m*n*q^3*x2 - n^2*q^3*x1 + n^2*q^3*x2) * hi2 + (b^3*q^2*y2 + 3*b^2*c*q^2*y2 - b^2*m*q^3 + 3*b^2*m*q^2*y2 - b^2*n*q^3 + 3*b^2*n*q^2*y2 + 3*b*c^2*q^2*y2 - 2*b*c*m*q^3 + 6*b*c*m*q^2*y2 - 2*b*c*n*q^3 + 6*b*c*n*q^2*y2 - 2*b*m^2*q^3 + 3*b*m^2*q^2*y2 - 4*b*m*n*q^3 + 6*b*m*n*q^2*y2 - 2*b*n^2*q^3 + 3*b*n^2*q^2*y2 + c^3*q^2*y2 - c^2*m*q^3 + 3*c^2*m*q^2*y2 - c^2*n*q^3 + 3*c^2*n*q^2*y2 - 2*c*m^2*q^3 + 3*c*m^2*q^2*y2 - 4*c*m*n*q^3 + 6*c*m*n*q^2*y2 - 2*c*n^2*q^3 + 3*c*n^2*q^2*y2 - m^3*q^3 + m^3*q^2*y2 - 3*m^2*n*q^3 + 3*m^2*n*q^2*y2 - 3*m*n^2*q^3 + 3*m*n^2*q^2*y2 - n^3*q^3 + n^3*q^2*y2) * hx1 + (-b^3*q^2*y1 - 3*b^2*c*q^2*y1 + b^2*m*q^3 - 3*b^2*m*q^2*y1 + b^2*n*q^3 - 3*b^2*n*q^2*y1 - 3*b*c^2*q^2*y1 + 2*b*c*m*q^3 - 6*b*c*m*q^2*y1 + 2*b*c*n*q^3 - 6*b*c*n*q^2*y1 + 2*b*m^2*q^3 - 3*b*m^2*q^2*y1 + 4*b*m*n*q^3 - 6*b*m*n*q^2*y1 + 2*b*n^2*q^3 - 3*b*n^2*q^2*y1 - c^3*q^2*y1 + c^2*m*q^3 - 3*c^2*m*q^2*y1 + c^2*n*q^3 - 3*c^2*n*q^2*y1 + 2*c*m^2*q^3 - 3*c*m^2*q^2*y1 + 4*c*m*n*q^3 - 6*c*m*n*q^2*y1 + 2*c*n^2*q^3 - 3*c*n^2*q^2*y1 + m^3*q^3 - m^3*q^2*y1 + 3*m^2*n*q^3 - 3*m^2*n*q^2*y1 + 3*m*n^2*q^3 - 3*m*n^2*q^2*y1 + n^3*q^3 - n^3*q^2*y1) * hx2 + (-2*L*b^2*q*y2 - 4*L*b*c*q*y2 + L*b*m*q^2 - 4*L*b*m*q*y2 + L*b*n*q^2 - 4*L*b*n*q*y2 - 2*L*c^2*q*y2 + L*c*m*q^2 - 4*L*c*m*q*y2 + L*c*n*q^2 - 4*L*c*n*q*y2 + L*m^2*q^2 - 2*L*m^2*q*y2 + 2*L*m*n*q^2 - 4*L*m*n*q*y2 + L*n^2*q^2 - 2*L*n^2*q*y2 - b^2*m*q^2 - b*c*m*q^2 + b*c*n*q^2 - b*m^2*q^2 - b*m*n*q^2 + c^2*n*q^2 + c*m*n*q^2 + c*n^2*q^2) * hY1 + (-2*L^3*b*m - 2*L^3*b*n - 2*L^3*c*m - 2*L^3*c*n - 2*L^3*m^2 - 4*L^3*m*n - 2*L^3*n^2 - 2*L^2*b^2*m - 2*L^2*b*c*m + 2*L^2*b*c*n - 2*L^2*b*m^2 - 2*L^2*b*m*n - 2*L^2*b*m*p - 2*L^2*b*n*p + 2*L^2*c^2*n + 2*L^2*c*m*n - 2*L^2*c*m*p + 2*L^2*c*n^2 - 2*L^2*c*n*p - 2*L^2*m^2*p - 4*L^2*m*n*p - 2*L^2*n^2*p - 2*L*b^2*m*p - 2*L*b*c*m*p + 2*L*b*c*n*p - 2*L*b*m^2*p - 2*L*b*m*n*p + L*b*m*q^2 + L*b*n*q^2 + 2*L*c^2*n*p + 2*L*c*m*n*p + L*c*m*q^2 + 2*L*c*n^2*p + L*c*n*q^2 + L*m^2*q^2 + 2*L*m*n*q^2 + L*n^2*q^2 + b^2*m*q^2 + b*c*m*q^2 - b*c*n*q^2 + b*m^2*q^2 + b*m*n*q^2 - c^2*n*q^2 - c*m*n*q^2 - c*n^2*q^2) * hY2 + (-2*L^3*b*m^2 - 4*L^3*b*m*n - 2*L^3*b*n^2 - 2*L^3*c*m^2 - 4*L^3*c*m*n - 2*L^3*c*n^2 - 2*L^3*m^3 - 6*L^3*m^2*n - 6*L^3*m*n^2 - 2*L^3*n^3 + 2*L*b^3*m^2 + 2*L*b^2*c*m^2 - 4*L*b^2*c*m*n + 2*L*b^2*m^3 + 2*L*b^2*m^2*n - 4*L*b*c^2*m*n + 2*L*b*c^2*n^2 - 4*L*b*c*m^2*n - 4*L*b*c*m*n^2 + 2*L*c^3*n^2 + 2*L*c^2*m*n^2 + 2*L*c^2*n^3) * hL
  have hne : q * (q * (m + n + b + c)) ^ 2 * (m + n + b + c) ≠ 0 := by positivity
  exact (mul_eq_zero.1 hfin).resolve_left hne


/-! ### Change of frame -/

def cr (u0 u1 v0 v1 x0 x1 : ℝ) : ℝ := (v0 - u0) * (x1 - u1) - (v1 - u1) * (x0 - u0)
def fr0 (w0 w1 xd yd x y : ℝ) : ℝ := (x - xd) * w0 + (y - yd) * w1
def fr1 (w0 w1 σ xd yd x y : ℝ) : ℝ := σ * (-(x - xd) * w1 + (y - yd) * w0)

theorem tr_cross (w0 w1 σ xd yd u0 u1 v0 v1 x0 x1 : ℝ) (hw : w0 ^ 2 + w1 ^ 2 = 1) :
    cr (fr0 w0 w1 xd yd u0 u1) (fr1 w0 w1 σ xd yd u0 u1) (fr0 w0 w1 xd yd v0 v1)
      (fr1 w0 w1 σ xd yd v0 v1) (fr0 w0 w1 xd yd x0 x1) (fr1 w0 w1 σ xd yd x0 x1) =
      σ * cr u0 u1 v0 v1 x0 x1 := by
  unfold cr fr0 fr1
  linear_combination σ * ((v0 - u0) * (x1 - u1) - (v1 - u1) * (x0 - u0)) * hw

theorem tr_dist (w0 w1 σ xd yd x0 x1 y0 y1 : ℝ) (hw : w0 ^ 2 + w1 ^ 2 = 1) (hσ : σ ^ 2 = 1) :
    (fr0 w0 w1 xd yd x0 x1 - fr0 w0 w1 xd yd y0 y1) ^ 2 +
      (fr1 w0 w1 σ xd yd x0 x1 - fr1 w0 w1 σ xd yd y0 y1) ^ 2 = (x0 - y0) ^ 2 + (x1 - y1) ^ 2 := by
  unfold fr0 fr1
  linear_combination (-(x0 - y0) * w1 + (x1 - y1) * w0) ^ 2 * hσ + ((x0 - y0) ^ 2 + (x1 - y1) ^ 2) * hw

theorem abs_sigma (σ : ℝ) (hσ : σ ^ 2 = 1) : |σ| = 1 :=
  (pow_left_inj₀ (abs_nonneg σ) zero_le_one two_ne_zero).1 (by rw [sq_abs, hσ, one_pow])

theorem sign_pos (σ X Y : ℝ) (hσ : σ ^ 2 = 1) (hY : 0 < σ * Y) (hXY : 0 < X * Y) :
    |X| = σ * X ∧ 0 < σ * X := by
  have h2 : 0 < σ * X := by
    have h : 0 < (σ * X) * (σ * Y) := by
      have : (σ * X) * (σ * Y) = σ ^ 2 * (X * Y) := by ring
      rw [this, hσ, one_mul]; exact hXY
    exact pos_of_mul_pos_left h hY.le
  refine ⟨?_, h2⟩
  rw [← abs_of_pos h2, abs_mul, abs_sigma σ hσ, one_mul]

theorem sign_neg (σ X Y : ℝ) (hσ : σ ^ 2 = 1) (hY : σ * Y < 0) (hXY : 0 < X * Y) :
    |X| = -(σ * X) ∧ σ * X < 0 := by
  have := sign_pos (-σ) X Y (by linear_combination hσ) (by linarith) hXY
  refine ⟨by linarith [this.1], by linarith [this.2]⟩

theorem pos_of_prod (X Y : ℝ) (hY : 0 < Y) (h : 0 < X * Y) : 0 < X := pos_of_mul_pos_left h hY.le
theorem neg_of_prod (X Y : ℝ) (hY : Y < 0) (h : 0 < X * Y) : X < 0 := by
  by_contra hX; have := mul_nonpos_of_nonneg_of_nonpos (not_lt.1 hX) hY.le; linarith

theorem main_frame (p q m n o0 o1 x1 y1 x2 y2 i1 i2 L b c R r s ρ : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hA : 0 < cr (-m) 0 n 0 p q)
    (hL0 : 0 < L) (hL : L ^ 2 = (p - 0) ^ 2 + (q - 0) ^ 2)
    (hb0 : 0 < b) (hb : b ^ 2 = (p - n) ^ 2 + (q - 0) ^ 2)
    (hc0 : 0 < c) (hc : c ^ 2 = (p - -m) ^ 2 + (q - 0) ^ 2)
    (hR0 : 0 ≤ R) (hOA : (p - o0) ^ 2 + (q - o1) ^ 2 = R ^ 2)
    (hOB : (-m - o0) ^ 2 + (0 - o1) ^ 2 = R ^ 2) (hOC : (n - o0) ^ 2 + (0 - o1) ^ 2 = R ^ 2)
    (hPAD : |cr p q 0 0 x1 y1| = r * L) (hPBC : |cr (-m) 0 n 0 x1 y1| = r * (m + n))
    (hPO : (x1 - o0) ^ 2 + (y1 - o1) ^ 2 = (R - r) ^ 2)
    (hPs1 : 0 < cr p q 0 0 x1 y1 * cr p q 0 0 (-m) 0)
    (hPs2 : 0 < cr (-m) 0 n 0 x1 y1 * cr (-m) 0 n 0 p q)
    (hQAD : |cr p q 0 0 x2 y2| = s * L) (hQBC : |cr (-m) 0 n 0 x2 y2| = s * (m + n))
    (hQO : (x2 - o0) ^ 2 + (y2 - o1) ^ 2 = (R - s) ^ 2)
    (hQs1 : 0 < cr p q 0 0 x2 y2 * cr p q 0 0 n 0)
    (hQs2 : 0 < cr (-m) 0 n 0 x2 y2 * cr (-m) 0 n 0 p q)
    (hIa : |cr (-m) 0 n 0 i1 i2| = ρ * (m + n)) (hIb : |cr n 0 p q i1 i2| = ρ * b)
    (hIc : |cr p q (-m) 0 i1 i2| = ρ * c)
    (hIsa : 0 < cr (-m) 0 n 0 i1 i2 * cr (-m) 0 n 0 p q)
    (hIsb : 0 < cr n 0 p q i1 i2 * cr n 0 p q (-m) 0)
    (hIsc : 0 < cr p q (-m) 0 i1 i2 * cr p q (-m) 0 n 0) :
    cr x1 y1 x2 y2 i1 i2 = 0 := by
  have eBC : ∀ x y, cr (-m) 0 n 0 x y = (m + n) * y := by intro x y; unfold cr; ring
  have eAD : ∀ x y, cr p q 0 0 x y = q * x - p * y := by intro x y; unfold cr; ring
  have eCA : ∀ x y, cr n 0 p q x y = (p - n) * y - q * (x - n) := by intro x y; unfold cr; ring
  have eAB : ∀ x y, cr p q (-m) 0 x y = (-m - p) * (y - q) + q * (x - p) := by
    intro x y; unfold cr; ring
  simp only [eBC] at hA hPBC hPs2 hQBC hQs2 hIa hIsa
  simp only [eAD] at hPs1 hQs1 hPAD hQAD
  simp only [eCA] at hIsb hIb
  simp only [eAB] at hIsc hIc
  have hmn : 0 < m + n := by linarith
  have hq : 0 < q := pos_of_mul_pos_right hA hmn.le
  have hqm : q * -m - p * 0 < 0 := by have := mul_pos hq hm; linarith
  have hqn : 0 < q * n - p * 0 := by have := mul_pos hq hn; linarith
  have hCAB : 0 < (p - n) * 0 - q * (-m - n) := by have := mul_pos hq hmn; linarith
  have hABC : 0 < (-m - p) * (0 - q) + q * (n - p) := by have := mul_pos hq hmn; linarith
  -- P
  have hP2 := pos_of_prod _ _ hA hPs2
  have hy1 : y1 = r := by
    rw [abs_of_pos hP2] at hPBC
    exact mul_left_cancel₀ hmn.ne' (by linarith)
  have hP1 := neg_of_prod _ _ hqm hPs1
  rw [abs_of_neg hP1] at hPAD
  -- Q
  have hQ2 := pos_of_prod _ _ hA hQs2
  have hy2 : y2 = s := by
    rw [abs_of_pos hQ2] at hQBC
    exact mul_left_cancel₀ hmn.ne' (by linarith)
  have hQ1 := pos_of_prod _ _ hqn hQs1
  rw [abs_of_pos hQ1] at hQAD
  -- I
  have hI2 := pos_of_prod _ _ hA hIsa
  have hρ : i2 = ρ := by
    rw [abs_of_pos hI2] at hIa
    exact mul_left_cancel₀ hmn.ne' (by linarith)
  have hIb' := pos_of_prod _ _ hCAB hIsb
  rw [abs_of_pos hIb'] at hIb
  have hIc' := pos_of_prod _ _ hABC hIsc
  rw [abs_of_pos hIc'] at hIc
  subst hy1 hy2 hρ
  have hi2 : (m + n + b + c) * i2 = (m + n) * q := by linear_combination -hIb - hIc
  have hi1 : (m + n + b + c) * i1 = (m + n) * p - b * m + c * n := by
    have : q * ((m + n + b + c) * i1) = q * ((m + n) * p - b * m + c * n) := by
      linear_combination (-(m + n + b + c)) * hIb + (p - n - b) * hi2
    exact mul_left_cancel₀ hq.ne' this
  have := core p q m n L b c o0 o1 R x1 y1 x2 y2 i1 i2 hq hm hn hL0 hb0 hc0 hR0
    (by linear_combination hL) (by linear_combination hb) (by linear_combination hc)
    (by linear_combination hOA) (by linear_combination hOB) (by linear_combination hOC)
    hr (by linear_combination -hPAD) (by linear_combination hPO)
    (by exact hs) (by linear_combination hQAD) (by linear_combination hQO) hi1 hi2
  unfold cr; linear_combination this


theorem main_real (a0 a1 b0 b1 c0 c1 d0 d1 o0 o1 P0 P1 Q0 Q1 I0 I1 t ℓ L b c R r s ρ : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hd0 : d0 = b0 + t * (c0 - b0)) (hd1 : d1 = b1 + t * (c1 - b1))
    (hℓ : 0 < ℓ) (hℓ2 : ℓ ^ 2 = (b0 - c0) ^ 2 + (b1 - c1) ^ 2)
    (hL0 : 0 < L) (hL : L ^ 2 = (a0 - d0) ^ 2 + (a1 - d1) ^ 2)
    (hb0 : 0 < b) (hb : b ^ 2 = (a0 - c0) ^ 2 + (a1 - c1) ^ 2)
    (hc0 : 0 < c) (hc : c ^ 2 = (a0 - b0) ^ 2 + (a1 - b1) ^ 2)
    (hA : cr b0 b1 c0 c1 a0 a1 ≠ 0)
    (hR0 : 0 ≤ R) (hOA : (a0 - o0) ^ 2 + (a1 - o1) ^ 2 = R ^ 2)
    (hOB : (b0 - o0) ^ 2 + (b1 - o1) ^ 2 = R ^ 2) (hOC : (c0 - o0) ^ 2 + (c1 - o1) ^ 2 = R ^ 2)
    (hr : 0 < r) (hPAD : |cr a0 a1 d0 d1 P0 P1| = r * L) (hPBC : |cr b0 b1 c0 c1 P0 P1| = r * ℓ)
    (hPO : (P0 - o0) ^ 2 + (P1 - o1) ^ 2 = (R - r) ^ 2)
    (hPs1 : 0 < cr a0 a1 d0 d1 P0 P1 * cr a0 a1 d0 d1 b0 b1)
    (hPs2 : 0 < cr b0 b1 c0 c1 P0 P1 * cr b0 b1 c0 c1 a0 a1)
    (hs : 0 < s) (hQAD : |cr a0 a1 d0 d1 Q0 Q1| = s * L) (hQBC : |cr b0 b1 c0 c1 Q0 Q1| = s * ℓ)
    (hQO : (Q0 - o0) ^ 2 + (Q1 - o1) ^ 2 = (R - s) ^ 2)
    (hQs1 : 0 < cr a0 a1 d0 d1 Q0 Q1 * cr a0 a1 d0 d1 c0 c1)
    (hQs2 : 0 < cr b0 b1 c0 c1 Q0 Q1 * cr b0 b1 c0 c1 a0 a1)
    (hIa : |cr b0 b1 c0 c1 I0 I1| = ρ * ℓ) (hIb : |cr c0 c1 a0 a1 I0 I1| = ρ * b)
    (hIc : |cr a0 a1 b0 b1 I0 I1| = ρ * c)
    (hIsa : 0 < cr b0 b1 c0 c1 I0 I1 * cr b0 b1 c0 c1 a0 a1)
    (hIsb : 0 < cr c0 c1 a0 a1 I0 I1 * cr c0 c1 a0 a1 b0 b1)
    (hIsc : 0 < cr a0 a1 b0 b1 I0 I1 * cr a0 a1 b0 b1 c0 c1) :
    cr P0 P1 Q0 Q1 I0 I1 = 0 := by
  obtain ⟨w0, w1, hw, hcw0, hcw1⟩ : ∃ w0 w1 : ℝ, w0 ^ 2 + w1 ^ 2 = 1 ∧
      c0 = b0 + ℓ * w0 ∧ c1 = b1 + ℓ * w1 := by
    refine ⟨(c0 - b0) / ℓ, (c1 - b1) / ℓ, ?_, by field_simp; ring, by field_simp; ring⟩
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    linear_combination -hℓ2
  obtain ⟨σ, hσ, hσA⟩ : ∃ σ : ℝ, σ ^ 2 = 1 ∧ 0 < σ * cr b0 b1 c0 c1 a0 a1 := by
    rcases lt_or_gt_of_ne hA with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by linarith⟩
  -- frame coordinates
  set F0 := fun x y => fr0 w0 w1 d0 d1 x y with hF0
  set F1 := fun x y => fr1 w0 w1 σ d0 d1 x y with hF1
  have kB0 : F0 b0 b1 = -(t * ℓ) := by
    simp only [F0, fr0]; rw [hd0, hd1, hcw0, hcw1]; linear_combination (-(t * ℓ)) * hw
  have kB1 : F1 b0 b1 = 0 := by
    simp only [F1, fr1]; rw [hd0, hd1, hcw0, hcw1]; ring
  have kC0 : F0 c0 c1 = (1 - t) * ℓ := by
    simp only [F0, fr0]; rw [hd0, hd1, hcw0, hcw1]; linear_combination ((1 - t) * ℓ) * hw
  have kC1 : F1 c0 c1 = 0 := by
    simp only [F1, fr1]; rw [hd0, hd1, hcw0, hcw1]; ring
  have kD0 : F0 d0 d1 = 0 := by simp only [F0, fr0]; ring
  have kD1 : F1 d0 d1 = 0 := by simp only [F1, fr1]; ring
  -- crosses transform by σ
  have TC : ∀ u0 u1 v0 v1 x0 x1 : ℝ,
      cr (F0 u0 u1) (F1 u0 u1) (F0 v0 v1) (F1 v0 v1) (F0 x0 x1) (F1 x0 x1) =
        σ * cr u0 u1 v0 v1 x0 x1 := fun u0 u1 v0 v1 x0 x1 =>
    tr_cross w0 w1 σ d0 d1 u0 u1 v0 v1 x0 x1 hw
  have TD : ∀ x0 x1 y0 y1 : ℝ, (F0 x0 x1 - F0 y0 y1) ^ 2 + (F1 x0 x1 - F1 y0 y1) ^ 2 =
      (x0 - y0) ^ 2 + (x1 - y1) ^ 2 := fun x0 x1 y0 y1 =>
    tr_dist w0 w1 σ d0 d1 x0 x1 y0 y1 hw hσ
  have hσa : |σ| = 1 := abs_sigma σ hσ
  have AB : ∀ X : ℝ, |σ * X| = |X| := fun X => by rw [abs_mul, hσa, one_mul]
  have PP : ∀ X Y : ℝ, (σ * X) * (σ * Y) = X * Y := fun X Y => by
    linear_combination (X * Y) * hσ
  -- abbreviations in the frame
  have hlsum : t * ℓ + (1 - t) * ℓ = ℓ := by ring
  have h1t : 0 < 1 - t := by linarith
  have e := main_frame (F0 a0 a1) (F1 a0 a1) (t * ℓ) ((1 - t) * ℓ) (F0 o0 o1) (F1 o0 o1)
    (F0 P0 P1) (F1 P0 P1) (F0 Q0 Q1) (F1 Q0 Q1) (F0 I0 I1) (F1 I0 I1) L b c R r s ρ
    (by positivity) (by positivity) hr hs
    (by have h1 := TC b0 b1 c0 c1 a0 a1; rw [kB0, kB1, kC0, kC1] at h1; rw [h1]; exact hσA)
    hL0 (by have h1 := TD a0 a1 d0 d1; rw [kD0, kD1] at h1; rw [h1]; exact hL)
    hb0 (by have h1 := TD a0 a1 c0 c1; rw [kC0, kC1] at h1; rw [h1]; exact hb)
    hc0 (by have h1 := TD a0 a1 b0 b1; rw [kB0, kB1] at h1; rw [h1]; exact hc)
    hR0 (by have h1 := TD a0 a1 o0 o1; rw [h1]; exact hOA)
    (by have h1 := TD b0 b1 o0 o1; rw [kB0, kB1] at h1; rw [h1]; exact hOB)
    (by have h1 := TD c0 c1 o0 o1; rw [kC0, kC1] at h1; rw [h1]; exact hOC)
    (by have h1 := TC a0 a1 d0 d1 P0 P1; rw [kD0, kD1] at h1; rw [h1, AB]; exact hPAD)
    (by have h1 := TC b0 b1 c0 c1 P0 P1; rw [kB0, kB1, kC0, kC1] at h1; rw [h1, AB, hlsum]; exact hPBC)
    (by have h1 := TD P0 P1 o0 o1; rw [h1]; exact hPO)
    (by have h1 := TC a0 a1 d0 d1 P0 P1; have h2 := TC a0 a1 d0 d1 b0 b1; rw [kD0, kD1] at h1; rw [kB0, kB1, kD0, kD1] at h2; rw [h1, h2, PP]; exact hPs1)
    (by have h1 := TC b0 b1 c0 c1 P0 P1; have h2 := TC b0 b1 c0 c1 a0 a1; rw [kB0, kB1, kC0, kC1] at h1; rw [kB0, kB1, kC0, kC1] at h2; rw [h1, h2, PP]; exact hPs2)
    (by have h1 := TC a0 a1 d0 d1 Q0 Q1; rw [kD0, kD1] at h1; rw [h1, AB]; exact hQAD)
    (by have h1 := TC b0 b1 c0 c1 Q0 Q1; rw [kB0, kB1, kC0, kC1] at h1; rw [h1, AB, hlsum]; exact hQBC)
    (by have h1 := TD Q0 Q1 o0 o1; rw [h1]; exact hQO)
    (by have h1 := TC a0 a1 d0 d1 Q0 Q1; have h2 := TC a0 a1 d0 d1 c0 c1; rw [kD0, kD1] at h1; rw [kC0, kC1, kD0, kD1] at h2; rw [h1, h2, PP]; exact hQs1)
    (by have h1 := TC b0 b1 c0 c1 Q0 Q1; have h2 := TC b0 b1 c0 c1 a0 a1; rw [kB0, kB1, kC0, kC1] at h1; rw [kB0, kB1, kC0, kC1] at h2; rw [h1, h2, PP]; exact hQs2)
    (by have h1 := TC b0 b1 c0 c1 I0 I1; rw [kB0, kB1, kC0, kC1] at h1; rw [h1, AB, hlsum]; exact hIa)
    (by have h1 := TC c0 c1 a0 a1 I0 I1; rw [kC0, kC1] at h1; rw [h1, AB]; exact hIb)
    (by have h1 := TC a0 a1 b0 b1 I0 I1; rw [kB0, kB1] at h1; rw [h1, AB]; exact hIc)
    (by have h1 := TC b0 b1 c0 c1 I0 I1; have h2 := TC b0 b1 c0 c1 a0 a1; rw [kB0, kB1, kC0, kC1] at h1; rw [kB0, kB1, kC0, kC1] at h2; rw [h1, h2, PP]; exact hIsa)
    (by have h1 := TC c0 c1 a0 a1 I0 I1; have h2 := TC c0 c1 a0 a1 b0 b1; rw [kC0, kC1] at h1; rw [kB0, kB1, kC0, kC1] at h2; rw [h1, h2, PP]; exact hIsb)
    (by have h1 := TC a0 a1 b0 b1 I0 I1; have h2 := TC a0 a1 b0 b1 c0 c1; rw [kB0, kB1] at h1; rw [kB0, kB1, kC0, kC1] at h2; rw [h1, h2, PP]; exact hIsc)
  rw [TC] at e
  rcases mul_eq_zero.1 e with h | h
  · rw [h] at hσ; norm_num at hσ
  · exact h


/-! ### Bridges to Mathlib -/

def cross (U V X : Pt) : ℝ := (V 0 - U 0) * (X 1 - U 1) - (V 1 - U 1) * (X 0 - U 0)

theorem dist_sq_eq (X Y : Pt) : dist X Y ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem lineMap_apply_coord (U V : Pt) (s : ℝ) (i : Fin 2) :
    (AffineMap.lineMap U V s : Pt) i = U i + s * (V i - U i) := by
  rw [AffineMap.lineMap_apply_module']
  simp; ring

theorem pt_ext (X Y : Pt) (h0 : X 0 = Y 0) (h1 : X 1 = Y 1) : X = Y := by
  ext i; fin_cases i <;> simp [h0, h1]

theorem dist_pos_sq (U V : Pt) (h : U ≠ V) : 0 < (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2 := by
  rw [← dist_sq_eq]; have := dist_pos.2 h.symm; positivity

/-- A point with zero signed area lies on the line. -/
theorem mem_line_of_cross_eq_zero (U V X : Pt) (h : U ≠ V) (hc : cross U V X = 0) :
    X ∈ line[ℝ, U, V] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  have hd := dist_pos_sq U V h
  set d := (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2
  set s := ((X 0 - U 0) * (V 0 - U 0) + (X 1 - U 1) * (V 1 - U 1)) / d
  refine ⟨s, ?_⟩
  unfold cross at hc
  have k0 : s * (V 0 - U 0) = X 0 - U 0 := by
    simp only [s]; rw [div_mul_eq_mul_div, div_eq_iff hd.ne']
    linear_combination (V 1 - U 1) * hc
  have k1 : s * (V 1 - U 1) = X 1 - U 1 := by
    simp only [s]; rw [div_mul_eq_mul_div, div_eq_iff hd.ne']
    linear_combination (-(V 0 - U 0)) * hc
  apply pt_ext <;> rw [lineMap_apply_coord] <;> linarith

theorem cross_of_mem_line (U V X Y : Pt) (hY : Y ∈ line[ℝ, U, V]) :
    cross U V X = (V 0 - U 0) * (X 1 - Y 1) - (V 1 - U 1) * (X 0 - Y 0) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hY
  obtain ⟨s, rfl⟩ := hY
  unfold cross; rw [lineMap_apply_coord, lineMap_apply_coord]; ring

/-- Distance from a point to a line in coordinates. -/
theorem infDist_line_eq (U V X : Pt) (h : U ≠ V) :
    Metric.infDist X (line[ℝ, U, V] : Set Pt) = |cross U V X| / dist U V := by
  have hd := dist_pos_sq U V h
  have hUV : 0 < dist U V := dist_pos.2 h
  have hUV2 : dist U V ^ 2 = (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2 := by
    rw [dist_sq_eq]; ring
  apply le_antisymm
  · set d := (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2
    set s := ((X 0 - U 0) * (V 0 - U 0) + (X 1 - U 1) * (V 1 - U 1)) / d
    have hF := AffineMap.lineMap_mem_affineSpan_pair s U V
    refine (Metric.infDist_le_dist_of_mem hF).trans (le_of_eq ?_)
    rw [eq_div_iff hUV.ne', ← abs_of_pos hUV, ← abs_of_nonneg dist_nonneg, ← abs_mul]
    rw [← sq_eq_sq_iff_abs_eq_abs, mul_pow, hUV2, dist_sq_eq, lineMap_apply_coord,
      lineMap_apply_coord]
    unfold cross
    have hs : s * d = (X 0 - U 0) * (V 0 - U 0) + (X 1 - U 1) * (V 1 - U 1) := by
      simp only [s]; rw [div_mul_cancel₀ _ hd.ne']
    have hdd : d = (V 0 - U 0) ^ 2 + (V 1 - U 1) ^ 2 := rfl
    clear_value s d
    linear_combination (s * d - ((X 0 - U 0) * (V 0 - U 0) + (X 1 - U 1) * (V 1 - U 1))) * hs
      + ((X 0 - U 0) ^ 2 + (X 1 - U 1) ^ 2 - s ^ 2 * d) * hdd
  · rw [Metric.le_infDist ⟨U, left_mem_affineSpan_pair ℝ U V⟩]
    intro Y hY
    rw [div_le_iff₀ hUV, cross_of_mem_line U V X Y hY]
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, hUV2, dist_sq_eq]
    nlinarith [sq_nonneg ((V 0 - U 0) * (X 0 - Y 0) + (V 1 - U 1) * (X 1 - Y 1))]

/-- Points strictly on the same side of a line have signed areas of the same sign. -/
theorem cross_mul_pos_of_sSameSide (U V X Y : Pt) (hUV : U ≠ V)
    (h : (line[ℝ, U, V]).SSameSide X Y) : 0 < cross U V X * cross U V Y := by
  have hU : U ∈ line[ℝ, U, V] := left_mem_affineSpan_pair ℝ U V
  rw [AffineSubspace.sSameSide_iff_exists_left hU] at h
  obtain ⟨hX, hY, Z, hZ, hr⟩ := h
  have hXc : cross U V X ≠ 0 := fun hc => hX (mem_line_of_cross_eq_zero U V X hUV hc)
  have hYc : cross U V Y ≠ 0 := fun hc => hY (mem_line_of_cross_eq_zero U V Y hUV hc)
  have hx : X -ᵥ U ≠ 0 := by
    intro h0; rw [vsub_eq_zero_iff_eq] at h0; exact hX (h0 ▸ hU)
  have hy : Y -ᵥ Z ≠ 0 := by
    intro h0; rw [vsub_eq_zero_iff_eq] at h0; exact hY (h0 ▸ hZ)
  obtain ⟨r₁, r₂, h1, h2, he⟩ := hr.exists_pos hx hy
  have e0 := congrArg (fun v : Pt => v 0) he
  have e1 := congrArg (fun v : Pt => v 1) he
  simp only [PiLp.smul_apply, vsub_eq_sub, PiLp.sub_apply, smul_eq_mul] at e0 e1
  have key : r₁ * cross U V X = r₂ * cross U V Y := by
    rw [cross_of_mem_line U V Y Z hZ]; unfold cross
    linear_combination (V 0 - U 0) * e1 - (V 1 - U 1) * e0
  have hpos : 0 < (r₁ * cross U V X) * (r₂ * cross U V Y) := by
    rw [key]; exact mul_self_pos.2 (mul_ne_zero h2.ne' hYc)
  have : (r₁ * cross U V X) * (r₂ * cross U V Y) = (r₁ * r₂) * (cross U V X * cross U V Y) := by
    ring
  rw [this] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- Zero signed area gives collinearity. -/
theorem collinear_of_cross_eq_zero (P Q I : Pt) (h : cross P Q I = 0) :
    Collinear ℝ {P, Q, I} := by
  by_cases hPQ : P = Q
  · subst hPQ; simp [collinear_pair]
  · have hI := mem_line_of_cross_eq_zero P Q I hPQ h
    have := collinear_insert_of_mem_affineSpan_pair hI
    have hs : ({P, Q, I} : Set Pt) = {I, P, Q} := by
      ext x; simp; tauto
    rw [hs]; exact this

theorem infDist_face (t : Affine.Triangle ℝ Pt) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    Metric.infDist t.incenter (line[ℝ, t.points i₂, t.points i₃] : Set Pt) = t.inradius := by
  have hc : ({i₁}ᶜ : Set (Fin 3)) = {i₂, i₃} := by
    ext x; simp; fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> fin_cases x <;> simp_all
  have he : affineSpan ℝ (Set.range (t.faceOpposite i₁).points) = line[ℝ, t.points i₂, t.points i₃] := by
    simp [Affine.Simplex.range_faceOpposite_points, hc, Set.image_insert_eq]
  rw [← he, ← dist_orthogonalProjection_eq_infDist, ← t.dist_incenter i₁]
  rfl

theorem tri_incenter_spec (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    Metric.infDist (tri A B C h).incenter (line[ℝ, B, C] : Set Pt) = (tri A B C h).inradius ∧
    Metric.infDist (tri A B C h).incenter (line[ℝ, C, A] : Set Pt) = (tri A B C h).inradius ∧
    Metric.infDist (tri A B C h).incenter (line[ℝ, A, B] : Set Pt) = (tri A B C h).inradius ∧
    (line[ℝ, B, C]).SSameSide (tri A B C h).incenter A ∧
    (line[ℝ, C, A]).SSameSide (tri A B C h).incenter B ∧
    (line[ℝ, A, B]).SSameSide (tri A B C h).incenter C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact infDist_face (tri A B C h) (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
  · exact infDist_face (tri A B C h) (i₁ := 1) (i₂ := 2) (i₃ := 0) (by decide) (by decide) (by decide)
  · exact infDist_face (tri A B C h) (i₁ := 2) (i₂ := 0) (i₃ := 1) (by decide) (by decide) (by decide)
  · exact (tri A B C h).sSameSide_affineSpan_pair_incenter_point (i₁ := 0) (i₂ := 1) (i₃ := 2)
      (by decide) (by decide) (by decide)
  · exact (tri A B C h).sSameSide_affineSpan_pair_incenter_point (i₁ := 1) (i₂ := 2) (i₃ := 0)
      (by decide) (by decide) (by decide)
  · exact (tri A B C h).sSameSide_affineSpan_pair_incenter_point (i₁ := 2) (i₂ := 0) (i₃ := 1)
      (by decide) (by decide) (by decide)

theorem dist_tri_circumcenter (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    dist A (tri A B C h).circumcenter = (tri A B C h).circumradius ∧
    dist B (tri A B C h).circumcenter = (tri A B C h).circumradius ∧
    dist C (tri A B C h).circumcenter = (tri A B C h).circumradius :=
  ⟨(tri A B C h).dist_circumcenter_eq_circumradius 0,
    (tri A B C h).dist_circumcenter_eq_circumradius 1,
    (tri A B C h).dist_circumcenter_eq_circumradius 2⟩

/-! ### Assembly -/

theorem cross_eq_cr (U V X : Pt) : cross U V X = cr (U 0) (U 1) (V 0) (V 1) (X 0) (X 1) := rfl

theorem abs_cross_eq (U V X : Pt) (h : U ≠ V) {r : ℝ}
    (hr : Metric.infDist X (line[ℝ, U, V] : Set Pt) = r) :
    |cr (U 0) (U 1) (V 0) (V 1) (X 0) (X 1)| = r * dist U V := by
  rw [infDist_line_eq U V X h, div_eq_iff (dist_pos.2 h).ne'] at hr
  exact hr

theorem cross_ne_zero_of_affineIndependent (A B C : Pt) (h : AffineIndependent ℝ ![A, B, C]) :
    cross B C A ≠ 0 := by
  intro hc
  have hcol : Collinear ℝ {B, C, A} := collinear_of_cross_eq_zero B C A hc
  have hs : ({A, B, C} : Set Pt) = {B, C, A} := by ext x; simp; tauto
  exact (affineIndependent_iff_not_collinear_set.1 h) (hs ▸ hcol)

/-- **Sawayama–Thébault theorem.** -/
theorem sawayama_thebault (A B C D P Q : Pt) (h : AffineIndependent ℝ ![A, B, C])
    (hD : Sbtw ℝ B D C) (hP : IsThebaultCircle A B C D B P h)
    (hQ : IsThebaultCircle A B C D C Q h) :
    Collinear ℝ {P, Q, (tri A B C h).incenter} := by
  have hA := cross_ne_zero_of_affineIndependent A B C h
  have hBC : B ≠ C := by rintro rfl; apply hA; unfold cross; ring
  have hAB : A ≠ B := by rintro rfl; apply hA; unfold cross; ring
  have hCA : C ≠ A := by rintro rfl; apply hA; unfold cross; ring
  obtain ⟨⟨t, ⟨ht0, ht1⟩, hDt⟩, hDB, hDC⟩ := hD
  have ht0' : t ≠ 0 := by rintro rfl; simp at hDt; exact hDB hDt.symm
  have ht1' : t ≠ 1 := by rintro rfl; simp at hDt; exact hDC hDt.symm
  have hd0 : D 0 = B 0 + t * (C 0 - B 0) := by rw [← hDt, lineMap_apply_coord]
  have hd1 : D 1 = B 1 + t * (C 1 - B 1) := by rw [← hDt, lineMap_apply_coord]
  have hAD : A ≠ D := by
    rintro rfl; apply hA; unfold cross; rw [hd0, hd1]; ring
  obtain ⟨r, hr, hPAD, hPBC, hPO, hPs1, hPs2⟩ := hP
  obtain ⟨s, hs, hQAD, hQBC, hQO, hQs1, hQs2⟩ := hQ
  obtain ⟨hIa, hIb, hIc, hIsa, hIsb, hIsc⟩ := tri_incenter_spec A B C h
  obtain ⟨hOA, hOB, hOC⟩ := dist_tri_circumcenter A B C h
  generalize (tri A B C h).incenter = I at *
  generalize (tri A B C h).circumcenter = O at *
  generalize (tri A B C h).circumradius = R at *
  generalize (tri A B C h).inradius = ρ at *
  have hR0 : 0 ≤ R := by rw [← hOA]; exact dist_nonneg
  have sq : ∀ X Y : Pt, ∀ x : ℝ, dist X Y = x → x ^ 2 = (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 :=
    fun X Y x hx => hx ▸ dist_sq_eq X Y
  have sq' : ∀ X Y : Pt, ∀ x : ℝ, dist X Y = x → (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 = x ^ 2 :=
    fun X Y x hx => (sq X Y x hx).symm
  have hfin := main_real (A 0) (A 1) (B 0) (B 1) (C 0) (C 1) (D 0) (D 1) (O 0) (O 1)
    (P 0) (P 1) (Q 0) (Q 1) (I 0) (I 1) t (dist B C) (dist A D) (dist A C) (dist A B) R r s ρ
    (lt_of_le_of_ne ht0 (Ne.symm ht0')) (lt_of_le_of_ne ht1 ht1') hd0 hd1
    (dist_pos.2 hBC) (sq B C _ rfl) (dist_pos.2 hAD) (sq A D _ rfl)
    (dist_pos.2 hCA.symm) (sq A C _ rfl) (dist_pos.2 hAB) (sq A B _ rfl)
    hA hR0 (sq' A O _ hOA) (sq' B O _ hOB) (sq' C O _ hOC)
    hr (abs_cross_eq A D P hAD hPAD) (abs_cross_eq B C P hBC hPBC) (sq' P O _ hPO)
    (cross_mul_pos_of_sSameSide A D P B hAD hPs1) (cross_mul_pos_of_sSameSide B C P A hBC hPs2)
    hs (abs_cross_eq A D Q hAD hQAD) (abs_cross_eq B C Q hBC hQBC) (sq' Q O _ hQO)
    (cross_mul_pos_of_sSameSide A D Q C hAD hQs1) (cross_mul_pos_of_sSameSide B C Q A hBC hQs2)
    (abs_cross_eq B C I hBC hIa) (by rw [abs_cross_eq C A I hCA hIb, dist_comm])
    (abs_cross_eq A B I hAB hIc)
    (cross_mul_pos_of_sSameSide B C I A hBC hIsa) (cross_mul_pos_of_sSameSide C A I B hCA hIsb)
    (cross_mul_pos_of_sSameSide A B I C hAB hIsc)
  exact collinear_of_cross_eq_zero P Q I hfin

end Thebault3
