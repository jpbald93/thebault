import Thebault3.Basic

/-!
# Layer 14: Mathlib-only restatement and a witness for the Sawayama–Thébault theorem

`l14_sawayama_thebault` mentions only Mathlib notions. `T` is an `Affine.Triangle` in the
Euclidean plane, `D` lies strictly between `B` and `C` (`Sbtw`), and `I = T.incenter`
(Mathlib's incentre). The two Thébault circles are Mathlib spheres `ωP`, `ωQ` of positive radius.
Each is tangent to the lines `AD` and `BC` (`EuclideanGeometry.Sphere.IsTangent`), internally
tangent to the circumcircle (`EuclideanGeometry.Sphere.IsIntTangent ω T.circumsphere`), and lies
in the angle `∠ADB` resp. `∠ADC` (strict same-side conditions, `AffineSubspace.SSameSide`). The
conclusion is `Collinear ℝ {ωP.center, ωQ.center, T.incenter}`. The plane is written
`EuclideanSpace ℝ (Fin 2)` rather than the library abbreviation `Pt`. The bridge `l14b_isThebaultCircle`
derives the library's `IsThebaultCircle` from these Mathlib conditions.
`l14w_sawayama_thebault` is the non-isosceles triangle `A = (6, 8)`, `B = (-9, 0)`, `C = (6, 0)`
with `D = (0, 0)`. Here `O = (-3/2, 4)`, `R = 17/2`, `ωP = ⟨(-3, 6), 6⟩`, `ωQ = ⟨(9/2, 9/4), 9/4⟩`,
and every tangency point is explicit. The three points `ωP.center`, `ωQ.center`, `T.incenter` are
pairwise distinct.
-/

namespace Thebault3

open EuclideanGeometry

/-! ### Bridges -/

theorem l14b_points (T : Affine.Triangle ℝ Pt) :
    T.points = ![T.points 0, T.points 1, T.points 2] := by
  ext i; fin_cases i <;> rfl

theorem l14b_indep (T : Affine.Triangle ℝ Pt) :
    AffineIndependent ℝ ![T.points 0, T.points 1, T.points 2] := by
  have h := T.independent; rwa [l14b_points T] at h

theorem l14b_tri (T : Affine.Triangle ℝ Pt) :
    tri (T.points 0) (T.points 1) (T.points 2) (l14b_indep T) = T :=
  Affine.Simplex.ext fun i => by fin_cases i <;> rfl

/-- Internal tangency to the circumcircle gives `dist P O = R - r`. -/
theorem l14b_dist_center {ω s : Sphere (EuclideanSpace ℝ (Fin 2))} (h : ω.IsIntTangent s) :
    dist ω.center s.center = s.radius - ω.radius := by
  obtain ⟨p, h1, h2, hw⟩ := h
  have e := hw.dist_add_dist
  rw [mem_sphere] at h1 h2
  rw [dist_comm p ω.center, dist_comm p s.center] at *
  rw [dist_comm s.center ω.center] at e
  linarith

/-- The Mathlib-only description of a Thébault circle gives the library's `IsThebaultCircle`. -/
theorem l14b_isThebaultCircle (T : Affine.Triangle ℝ Pt) (D X : Pt) (ω : Sphere Pt)
    (hr : 0 < ω.radius) (t1 : ω.IsTangent line[ℝ, T.points 0, D])
    (t2 : ω.IsTangent line[ℝ, T.points 1, T.points 2]) (t3 : ω.IsIntTangent T.circumsphere)
    (s1 : line[ℝ, T.points 0, D].SSameSide ω.center X)
    (s2 : line[ℝ, T.points 1, T.points 2].SSameSide ω.center (T.points 0)) :
    IsThebaultCircle (T.points 0) (T.points 1) (T.points 2) D X ω.center (l14b_indep T) := by
  refine ⟨ω.radius, hr, t1.infDist_eq_radius, t2.infDist_eq_radius, ?_, s1, s2⟩
  have := l14b_dist_center t3
  rw [Affine.Simplex.circumsphere_center, Affine.Simplex.circumsphere_radius] at this
  rw [l14b_tri, this]

/-- **Sawayama–Thébault**, Mathlib-only statement. -/
theorem l14_sawayama_thebault (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (D : EuclideanSpace ℝ (Fin 2))
    (hD : Sbtw ℝ (T.points 1) D (T.points 2)) (ωP ωQ : Sphere (EuclideanSpace ℝ (Fin 2)))
    (hrP : 0 < ωP.radius) (tP1 : ωP.IsTangent line[ℝ, T.points 0, D])
    (tP2 : ωP.IsTangent line[ℝ, T.points 1, T.points 2]) (tP3 : ωP.IsIntTangent T.circumsphere)
    (sP1 : line[ℝ, T.points 0, D].SSameSide ωP.center (T.points 1))
    (sP2 : line[ℝ, T.points 1, T.points 2].SSameSide ωP.center (T.points 0))
    (hrQ : 0 < ωQ.radius) (tQ1 : ωQ.IsTangent line[ℝ, T.points 0, D])
    (tQ2 : ωQ.IsTangent line[ℝ, T.points 1, T.points 2]) (tQ3 : ωQ.IsIntTangent T.circumsphere)
    (sQ1 : line[ℝ, T.points 0, D].SSameSide ωQ.center (T.points 2))
    (sQ2 : line[ℝ, T.points 1, T.points 2].SSameSide ωQ.center (T.points 0)) :
    Collinear ℝ ({ωP.center, ωQ.center, T.incenter} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have := sawayama_thebault (T.points 0) (T.points 1) (T.points 2) D ωP.center ωQ.center
    (l14b_indep T) hD (l14b_isThebaultCircle T D _ ωP hrP tP1 tP2 tP3 sP1 sP2)
    (l14b_isThebaultCircle T D _ ωQ hrQ tQ1 tQ2 tQ3 sQ1 sQ2)
  rwa [l14b_tri] at this

/-! ### Witness -/

theorem l14b_dist_eq_of_sq (X Y : Pt) {d : ℝ} (hd : 0 ≤ d)
    (h : (X 0 - Y 0) ^ 2 + (X 1 - Y 1) ^ 2 = d ^ 2) : dist X Y = d := by
  have h2 : dist X Y ^ 2 = d ^ 2 := by rw [dist_sq_eq, h]
  exact (pow_left_inj₀ dist_nonneg hd two_ne_zero).1 h2

theorem l14b_circumcenter (T : Affine.Triangle ℝ Pt) (p : Pt) {d : ℝ}
    (h : ∀ i, dist (T.points i) p = d) : T.circumcenter = p ∧ T.circumradius = d := by
  have hs : p ∈ affineSpan ℝ (Set.range T.points) := by
    rw [T.span_eq_top (by simp)]; exact AffineSubspace.mem_top _ _ _
  exact ⟨(T.eq_circumcenter_of_dist_eq hs h).symm, (T.eq_circumradius_of_dist_eq hs h).symm⟩

theorem l14b_tangentAt (ω : Sphere Pt) (U V p : Pt) (hp : dist p ω.center = ω.radius)
    (hpl : p ∈ line[ℝ, U, V])
    (hU : (U 0 - p 0) * (p 0 - ω.center 0) + (U 1 - p 1) * (p 1 - ω.center 1) = 0)
    (hV : (V 0 - p 0) * (p 0 - ω.center 0) + (V 1 - p 1) * (p 1 - ω.center 1) = 0) :
    ω.IsTangent line[ℝ, U, V] := by
  refine ⟨p, hp, hpl, affineSpan_pair_le_of_mem_of_mem ?_ ?_⟩
  · rw [Sphere.mem_orthRadius_iff_inner_left]
    simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
    linarith
  · rw [Sphere.mem_orthRadius_iff_inner_left]
    simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
    linarith

theorem l14b_eq_lineMap (U V X : Pt) (s : ℝ) (h0 : X 0 = U 0 + s * (V 0 - U 0))
    (h1 : X 1 = U 1 + s * (V 1 - U 1)) : X = AffineMap.lineMap U V s :=
  pt_ext _ _ (by rw [lineMap_apply_coord]; exact h0) (by rw [lineMap_apply_coord]; exact h1)

theorem l14b_sSameSide (U V W X Y : Pt) (u s : ℝ) (hs : 0 < s) (hY : cross U V Y ≠ 0)
    (hW : W = AffineMap.lineMap U V u) (hX : X = AffineMap.lineMap W Y s) :
    line[ℝ, U, V].SSameSide X Y := by
  have hUV : U ≠ V := by rintro rfl; apply hY; unfold cross; ring
  have hYn : Y ∉ line[ℝ, U, V] := fun hm => hY (by
    rw [cross_of_mem_line U V Y Y hm]; ring)
  rw [hX]
  exact AffineSubspace.sSameSide_lineMap_left (hW ▸ AffineMap.lineMap_mem_affineSpan_pair u U V)
    hYn hs

/-- Witness for `l14_sawayama_thebault`. -/
theorem l14w_sawayama_thebault :
    ∃ T : Affine.Triangle ℝ Pt,
      T.points = ![!₂[6, 8], !₂[-9, 0], !₂[6, 0]] ∧
      Sbtw ℝ (T.points 1) !₂[0, 0] (T.points 2) ∧
      T.circumcenter = !₂[-3/2, 4] ∧ T.circumradius = 17/2 ∧
      (0 < (⟨!₂[-3, 6], 6⟩ : Sphere Pt).radius ∧
        (⟨!₂[-3, 6], 6⟩ : Sphere Pt).IsTangent line[ℝ, T.points 0, !₂[0, 0]] ∧
        (⟨!₂[-3, 6], 6⟩ : Sphere Pt).IsTangent line[ℝ, T.points 1, T.points 2] ∧
        (⟨!₂[-3, 6], 6⟩ : Sphere Pt).IsIntTangent T.circumsphere ∧
        line[ℝ, T.points 0, !₂[0, 0]].SSameSide (⟨!₂[-3, 6], 6⟩ : Sphere Pt).center (T.points 1) ∧
        line[ℝ, T.points 1, T.points 2].SSameSide (⟨!₂[-3, 6], 6⟩ : Sphere Pt).center
          (T.points 0)) ∧
      (0 < (⟨!₂[9/2, 9/4], 9/4⟩ : Sphere Pt).radius ∧
        (⟨!₂[9/2, 9/4], 9/4⟩ : Sphere Pt).IsTangent line[ℝ, T.points 0, !₂[0, 0]] ∧
        (⟨!₂[9/2, 9/4], 9/4⟩ : Sphere Pt).IsTangent line[ℝ, T.points 1, T.points 2] ∧
        (⟨!₂[9/2, 9/4], 9/4⟩ : Sphere Pt).IsIntTangent T.circumsphere ∧
        line[ℝ, T.points 0, !₂[0, 0]].SSameSide (⟨!₂[9/2, 9/4], 9/4⟩ : Sphere Pt).center
          (T.points 2) ∧
        line[ℝ, T.points 1, T.points 2].SSameSide (⟨!₂[9/2, 9/4], 9/4⟩ : Sphere Pt).center
          (T.points 0)) ∧
      (!₂[-3, 6] : Pt) ≠ !₂[9/2, 9/4] ∧ T.incenter ≠ !₂[-3, 6] ∧ T.incenter ≠ !₂[9/2, 9/4] := by
  have nT : AffineIndependent ℝ ![(!₂[6, 8] : Pt), !₂[-9, 0], !₂[6, 0]] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hc
    have := cross_of_mem_line (!₂[-9, 0]) (!₂[6, 0]) (!₂[6, 8]) (!₂[6, 8]) (by
      have hne : (!₂[-9, 0] : Pt) ≠ !₂[6, 0] := by
        intro h; have := congrArg (fun X : Pt => X 0) h; norm_num at this
      exact hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne)
    have h2 := cross_ne_zero_of_affineIndependent (!₂[6, 8]) (!₂[-9, 0]) (!₂[6, 0])
    revert h2 this; simp [cross]; norm_num
  let T : Affine.Triangle ℝ Pt := ⟨![!₂[6, 8], !₂[-9, 0], !₂[6, 0]], nT⟩
  have p0 : T.points 0 = !₂[6, 8] := rfl
  have p1 : T.points 1 = !₂[-9, 0] := rfl
  have p2 : T.points 2 = !₂[6, 0] := rfl
  obtain ⟨hO, hR⟩ := l14b_circumcenter T (!₂[-3/2, 4]) (d := 17/2) (fun i => by
    fin_cases i <;> exact l14b_dist_eq_of_sq _ _ (by norm_num) (by simp [T]; norm_num))
  have hcs : T.circumsphere = ⟨!₂[-3/2, 4], 17/2⟩ := by
    ext
    · rw [Affine.Simplex.circumsphere_center, hO]
    · rw [Affine.Simplex.circumsphere_radius, hR]
  have hA : cross (T.points 1) (T.points 2) (T.points 0) ≠ 0 := by simp [T, cross]; norm_num
  have hD : cross (T.points 0) (!₂[0, 0]) (T.points 1) ≠ 0 := by simp [T, cross]; norm_num
  have hD' : cross (T.points 0) (!₂[0, 0]) (T.points 2) ≠ 0 := by simp [T, cross]
  refine ⟨T, rfl, ?_, hO, hR, ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨3/5, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_, ?_⟩
    · exact (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T])).symm
    · intro h; have := congrArg (fun X : Pt => X 0) h; simp [T] at this
    · intro h; have := congrArg (fun X : Pt => X 0) h; simp [T] at this
  -- ωP
  · refine l14b_tangentAt _ _ _ (!₂[9/5, 12/5]) (l14b_dist_eq_of_sq _ _ (by norm_num)
      (by simp; norm_num)) ?_ (by simp [T]; norm_num) (by simp; norm_num)
    exact (l14b_eq_lineMap (T.points 0) (!₂[0, 0]) (!₂[9/5, 12/5]) (7/10) (by simp [T]; norm_num) (by simp [T]; norm_num)) ▸
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · refine l14b_tangentAt _ _ _ (!₂[-3, 0]) (l14b_dist_eq_of_sq _ _ (by norm_num)
      (by simp)) ?_ (by simp [T]) (by simp [T])
    exact (l14b_eq_lineMap (T.points 1) (T.points 2) (!₂[-3, 0]) (2/5) (by simp [T]; norm_num) (by simp [T])) ▸
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · rw [hcs]
    refine ⟨!₂[-33/5, 54/5], l14b_dist_eq_of_sq _ _ (by norm_num) (by simp; norm_num),
      l14b_dist_eq_of_sq _ _ (by norm_num) (by simp; norm_num), ⟨5/17, ⟨by norm_num, by norm_num⟩,
      (l14b_eq_lineMap (!₂[-3/2, 4]) (!₂[-33/5, 54/5]) (!₂[-3, 6]) _ (by simp; norm_num)
        (by simp; norm_num)).symm⟩⟩
  · exact l14b_sSameSide _ _ (!₂[27, 36]) _ _ (-7/2) (5/6) (by norm_num) hD
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]; norm_num))
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]; norm_num))
  · exact l14b_sSameSide _ _ (!₂[-30, 0]) _ _ (-7/5) (3/4) (by norm_num) hA
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]))
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]; norm_num))
  -- ωQ
  · refine l14b_tangentAt _ _ _ (!₂[27/10, 18/5]) (l14b_dist_eq_of_sq _ _ (by norm_num)
      (by simp; norm_num)) ?_ (by simp [T]; norm_num) (by simp; norm_num)
    exact (l14b_eq_lineMap (T.points 0) (!₂[0, 0]) (!₂[27/10, 18/5]) (11/20) (by simp [T]; norm_num) (by simp [T]; norm_num)) ▸
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · refine l14b_tangentAt _ _ _ (!₂[9/2, 0]) (l14b_dist_eq_of_sq _ _ (by norm_num)
      (by simp)) ?_ (by simp [T]) (by simp [T])
    exact (l14b_eq_lineMap (T.points 1) (T.points 2) (!₂[9/2, 0]) (9/10) (by simp [T]; norm_num) (by simp [T])) ▸
      AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · rw [hcs]
    refine ⟨!₂[333/50, 81/50], l14b_dist_eq_of_sq _ _ (by norm_num) (by simp; norm_num),
      l14b_dist_eq_of_sq _ _ (by norm_num) (by simp; norm_num), ⟨25/34, ⟨by norm_num, by norm_num⟩,
      (l14b_eq_lineMap (!₂[-3/2, 4]) (!₂[333/50, 81/50]) (!₂[9/2, 9/4]) _ (by simp; norm_num)
        (by simp; norm_num)).symm⟩⟩
  · exact l14b_sSameSide _ _ (!₂[54/17, 72/17]) _ _ (8/17) (15/32) (by norm_num) hD'
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]; norm_num))
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]; norm_num))
  · exact l14b_sSameSide _ _ (!₂[90/23, 0]) _ _ (99/115) (9/32) (by norm_num) hA
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]))
      (l14b_eq_lineMap _ _ _ _ (by simp [T]; norm_num) (by simp [T]; norm_num))
  -- distinctness
  · intro h; have := congrArg (fun X : Pt => X 0) h; norm_num at this
  all_goals
    intro h
    obtain ⟨hIa, -, hIc, -, -, -⟩ := tri_incenter_spec (T.points 0) (T.points 1) (T.points 2)
      (l14b_indep T)
    rw [l14b_tri, h] at hIa hIc
    have hBC : T.points 1 ≠ T.points 2 := by
      intro e; have := congrArg (fun X : Pt => X 0) e; simp [T] at this; norm_num at this
    have hAB : T.points 0 ≠ T.points 1 := by
      intro e; have := congrArg (fun X : Pt => X 0) e; simp [T] at this; norm_num at this
    have hCA : T.points 2 ≠ T.points 0 := by
      intro e; have := congrArg (fun X : Pt => X 1) e; simp [T] at this
    rw [infDist_line_eq _ _ _ hBC] at hIa
    rw [infDist_line_eq _ _ _ hAB] at hIc
    have dBC : dist (T.points 1) (T.points 2) = 15 :=
      l14b_dist_eq_of_sq _ _ (by norm_num) (by simp [T]; norm_num)
    have dAB : dist (T.points 0) (T.points 1) = 17 :=
      l14b_dist_eq_of_sq _ _ (by norm_num) (by simp [T]; norm_num)
    rw [dBC] at hIa
    rw [dAB] at hIc
    have key := hIa.trans hIc.symm
    simp [T, cross] at key
    norm_num [abs_of_pos, abs_of_neg] at key

end Thebault3
