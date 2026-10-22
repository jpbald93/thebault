import Thebault3.Basic

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/


/-!
# Paper D — classical statements D1–D7 (blind formalisation)

All statements live in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`.
Constructed objects (second intersection points, Clifford points, Fermat points,
Thébault circles, auxiliary circumcentres, bisector feet) are passed in as data
together with their DEFINING property; well-definedness facts that are needed only
to make such data exist are stated separately as `_obligation` theorems.
-/

open EuclideanGeometry

noncomputable section

namespace Thebault3.Classical

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ## D1 — Clifford's circle theorems -/

/-- OWN DEFINITION. General position hypothesis of D1 for `n` circles `c i` through a
common point `M`: genuine circles (positive radius), pairwise distinct, `P i j` is a
second common point of `c i` and `c j` different from `M`, and for any three circles the
three second points are not collinear. (Since distinct circles meet in at most two points,
`P i j` is uniquely determined by these conditions.) -/
structure CliffordGP (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt) (P : Fin n → Fin n → Pt) :
    Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  second_mem : ∀ i j, i ≠ j → P i j ∈ c i ∧ P i j ∈ c j
  second_ne : ∀ i j, i ≠ j → P i j ≠ M
  noncollinear : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i j, P i k, P j k}

/-- OWN DEFINITION. `X` lies on every circle `Γ_ijk` (through the non-collinear points
`P i j, P i k, P j k`) for `i, j, k` pairwise distinct in `S`. For `S` with four elements
this says that `X` is a common point of the four circles of D1(a) (a "Clifford point").
Because `P i j, P i k, P j k` are non-collinear, `Cospherical {P i j, P i k, P j k, X}`
means exactly that `X` lies on their (unique) circumcircle. -/
def OnAllGamma {n : ℕ} (P : Fin n → Fin n → Pt) (S : Finset (Fin n)) (X : Pt) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k →
    Cospherical ({P i j, P i k, P j k, X} : Set Pt)

/-- D1(a), Clifford n = 4: the four circles `Γ_123, Γ_124, Γ_134, Γ_234` have a common
point. -/
def classical_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) : Prop := 
    ∃ X : Pt, OnAllGamma P Finset.univ X


/-- D1(b), Clifford n = 5: the five Clifford points `X l` (of the four circles obtained by
omitting circle `l`) lie on one circle. -/
def classical_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) : Prop := 
    Cospherical (Set.range X)


/-- D1(c), Clifford n = 6: for each `m`, the five Clifford points `X m l` (`l ≠ m`) of the
five circles other than `m` lie on a circle `C m` (part (b)); these six circles have a
common point. `X m l` is the Clifford point of the four circles other than `m, l`. -/
def classical_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) : Prop := 
    ∃ Y : Pt, ∀ m, Y ∈ C m


/-- OWN DEFINITION. Data of Clifford's chain for `n` circles `c i` through `M`, levels
indexed by subsets `S` of the circles: `circ S` (for `|S|` odd) is the circle and `pt S`
(for `|S|` even) the point attached to `S`.
* level 1: `circ {i} = c i`;
* level 2: `pt {i,j}` is the second intersection of `c i, c j` (≠ `M`);
* odd level `|S| = 2k+1 ≥ 3`: `circ S` passes through the `|S|` points `pt (S \ {i})`,
  which are not collinear (general position), so `circ S` is uniquely determined;
* even level `|S| = 2k ≥ 4`: `pt S` lies on the `|S|` circles `circ (S \ {i})` and is their
  unique common point (general position).
All levels strictly below `n` are part of the data/hypotheses (they are the lower
instances of the chain); the theorems below assert the top level `n`. -/
structure CliffordChain (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt) : Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  level_one : ∀ i, circ {i} = c i
  level_two : ∀ S : Finset (Fin n), S.card = 2 →
    pt S ≠ M ∧ ∀ i ∈ S, pt S ∈ circ (S.erase i)
  odd_mem : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt (S.erase i) ∈ circ S
  odd_gp : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ¬ Collinear ℝ ((fun i => pt (S.erase i)) '' (S : Set (Fin n)))
  even_mem : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt S ∈ circ (S.erase i)
  even_gp : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ Y : Pt, (∀ i ∈ S, Y ∈ circ (S.erase i)) → Y = pt S

/-- D1(d), Clifford's chain, even step (all even `n ≥ 4`): the `n` circles of level
`n - 1` pass through one common point.
(The case `n = 2` is the general-position hypothesis `level_two` itself.) -/
def classical_D1_d_even (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ) : Prop := 
    ∃ Y : Pt, ∀ i, Y ∈ circ (Finset.univ.erase i)


/-- D1(d), Clifford's chain, odd step (all odd `n ≥ 3`): the `n` points of level `n - 1`
lie on one circle. -/
def classical_D1_d_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ)
    -- EXTRA HYPOTHESIS: the top-level points are not collinear ("one circle"). For `n = 3`
    -- this is exactly the non-collinearity hypothesis of (a).
    -- AMBIGUOUS: drop it and conclude `Cospherical … ∨ Collinear ℝ …` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range fun i => pt (Finset.univ.erase i))) : Prop := 
    Cospherical (Set.range fun i => pt (Finset.univ.erase i))


/-! ## D2 — Miquel's pentagram (five circles) theorem -/

/-- D2. Five lines `ℓ 0, …, ℓ 4` in general position (no two parallel, no three
concurrent), labelled in the cyclic order of the sides of the inner pentagon: its vertices
are `V i = ℓ i ∩ ℓ (i+1)`, the star points are `T i = ℓ (i-1) ∩ ℓ (i+1)`, and the outer
triangle `i` (bounded by `ℓ (i-1), ℓ i, ℓ (i+1)`) has vertices `V (i-1), V i, T i` and
circumcircle `ω i`.
AMBIGUOUS: the labelling is only required to be cyclic as above; we do not additionally
require the inner pentagon to be convex / the figure to be a "star" (alternative: add a
hypothesis that the `V i` form a convex pentagon with the `T i` outside it).
Consecutive circles `ω i, ω (i+1)` meet in the inner vertex `V i` and in
a second point `Q i`. Then the five points `Q i` lie on one circle. -/
def classical_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) : Prop := 
    Cospherical (Set.range Q)


/-- D2 obligation (well-formedness only): for five lines in general position the
intersection points `V i`, `T i` exist and the three vertices of each outer triangle are
non-collinear, so the circumcircles `ω i` exist (and are unique). -/
def classical_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) : Prop := 
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)


/-! ## D3 — Lester's theorem -/

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected OUTWARDLY on side
`q r` of triangle `p q r` (opposite side of line `q r` from `p`). -/
def IsOuterApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SOppSide p X

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected INWARDLY on side
`q r` of triangle `p q r` (same side of line `q r` as `p`). -/
def IsInnerApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SSameSide p X

/-- OWN DEFINITION. First Fermat point (first isogonic centre): common point of the lines
joining each vertex to the apex of the outward equilateral triangle on the opposite side. -/
def IsFirstFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsOuterApex a b c A' ∧ IsOuterApex b c a B' ∧ IsOuterApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- OWN DEFINITION. Second Fermat point (second isogonic centre): same with the inward
equilateral triangles. -/
def IsSecondFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsInnerApex a b c A' ∧ IsInnerApex b c a B' ∧ IsInnerApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- D3, Lester's theorem: in a scalene triangle the two Fermat points, the circumcentre and
the nine-point centre are concyclic. -/
def classical_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)


/-- D3 obligation (well-formedness only): both Fermat points exist (the second one needs
the triangle not to be equilateral; scalene suffices). -/
def classical_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) : Prop := 
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)


/-! ## D4 — Sawayama–Thébault theorem -/

/-- OWN DEFINITION. The circle `ω` (positive radius) is tangent to the line `p q`. -/
def TangentToLine (ω : Sphere Pt) (p q : Pt) : Prop :=
  0 < ω.radius ∧ Metric.infDist ω.center (line[ℝ, p, q] : Set Pt) = ω.radius

/-- OWN DEFINITION. The circle `ω` (positive radius) is internally tangent to the circle `Ω`
(lies inside `Ω` and touches it). -/
def InternallyTangent (ω Ω : Sphere Pt) : Prop :=
  0 < ω.radius ∧ ω.radius < Ω.radius ∧ dist ω.center Ω.center = Ω.radius - ω.radius

/-- D4, Sawayama–Thébault: `D` on side `BC`; `ω₁, ω₂` are tangent to lines `AD`, `BC`,
internally tangent to the circumcircle, one on each side of `AD`. Then their centres and
the incentre are collinear. -/
def classical_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt)


/-- D4 obligation (well-formedness only): the two Thébault circles exist. -/
def classical_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a


/-! ## D5 — Kosnita's theorem -/

/-- OWN DEFINITION. `o` is equidistant from `p, q, r`, i.e. (for `p, q, r` not collinear) the
circumcentre of triangle `p q r`. -/
def IsCircumcenterOf (o p q r : Pt) : Prop :=
  dist o p = dist o q ∧ dist o p = dist o r

/-- D5, Kosnita: with `O` the circumcentre and `O_a, O_b, O_c` the circumcentres of `OBC`,
`OCA`, `OAB`, the lines `AO_a, BO_b, CO_c` are concurrent.
(If `O` lies on a side — right triangle — the corresponding `O_x` does not exist and the
statement is vacuous; see the obligation.) -/
def classical_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc]))


/-- D5 obligation (well-formedness only): if the circumcentre is not on line `BC`, the
circumcentre of `OBC` exists. -/
def classical_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c


/-! ## D6 — Blundon's fundamental inequality -/

/-- D6, Blundon, lower bound. -/
def classical_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2


/-- D6, Blundon, upper bound. -/
def classical_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)


/-- D6 obligation (well-formedness only): the radicand is non-negative (Euler `R ≥ 2r`),
so `Real.sqrt` is the genuine square root rather than its junk value `0`. -/
def classical_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius


/-! ## D7 — Steiner–Lehmus theorem -/

/-- OWN DEFINITION. `e` is the foot of the internal bisector from vertex `v` of the angle
`p v q`: `e` lies on segment `p q` and bisects the angle at `v`. -/
def IsBisectorFoot (v p q e : Pt) : Prop :=
  Wbtw ℝ p e q ∧ ∠ p v e = ∠ e v q

/-- D7, Steiner–Lehmus: if the internal bisectors from `B` and `C` (vertex to opposite side)
have equal length, then `AB = AC`. -/
def classical_D7 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (e f : Pt)
    (he : IsBisectorFoot b a c e) (hf : IsBisectorFoot c a b f)
    (hlen : dist b e = dist c f) : Prop := 
    dist a b = dist a c


/-- D7 obligation (well-formedness only): the bisector foot exists. -/
def classical_D7_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    ∃ e, IsBisectorFoot b a c e


end Thebault3.Classical

namespace Thebault3.Classical

theorem cov_D4_part (a b c d : Pt) (h : AffineIndependent ℝ ![a,b,c])
    (hd : Sbtw ℝ b d c) (ω₁ ω₂ : Sphere Pt)
    (hside₁ : (line[ℝ,a,d]).SSameSide ω₁.center b)
    (hside₂ : (line[ℝ,a,d]).SSameSide ω₂.center c) :
    classical_D4 a b c d h hd ω₁ ω₂ := by
  intro h1a h1b h1c h2a h2b h2c hop hbase1 hbase2
  exact Thebault3.sawayama_thebault a b c d ω₁.center ω₂.center h hd
    ⟨ω₁.radius,h1a.1,h1a.2,h1b.2,h1c.2.2,hside₁,hbase1⟩
    ⟨ω₂.radius,h2a.1,h2a.2,h2b.2,h2c.2.2,hside₂,hbase2⟩

theorem cov_D4_swapped_part (a b c d : Pt) (h : AffineIndependent ℝ ![a,b,c])
    (hd : Sbtw ℝ b d c) (ω₁ ω₂ : Sphere Pt)
    (hside₁ : (line[ℝ,a,d]).SSameSide ω₂.center b)
    (hside₂ : (line[ℝ,a,d]).SSameSide ω₁.center c) :
    classical_D4 a b c d h hd ω₁ ω₂ := by
  intro h1a h1b h1c h2a h2b h2c hop hbase1 hbase2
  have hh := Thebault3.sawayama_thebault a b c d ω₂.center ω₁.center h hd
    ⟨ω₂.radius,h2a.1,h2a.2,h2b.2,h2c.2.2,hside₁,hbase2⟩
    ⟨ω₁.radius,h1a.1,h1a.2,h1b.2,h1c.2.2,hside₂,hbase1⟩
  simpa only [Set.insert_comm, Thebault3.tri] using hh


open Thebault3
 theorem cov_cross_zero_of_mem (U V Z : Pt) (hz : Z ∈ line[ℝ,U,V]) : cross U V Z = 0 := by
  have hh := cross_of_mem_line U V Z Z hz
  simpa [cross] using hh

 theorem cov_sameSide_of_cross_pos (U V X Y : Pt) (huv : U ≠ V)
    (hp : 0 < cross U V X * cross U V Y) : (line[ℝ,U,V]).SSameSide X Y := by
  have hx : cross U V X ≠ 0 := by intro hh; rw [hh,zero_mul] at hp; linarith
  have hy : cross U V Y ≠ 0 := by intro hh; rw [hh,mul_zero] at hp; linarith
  let r := cross U V Y / cross U V X
  let Z := Y - r • (X - U)
  have hr : 0 < r := by
    dsimp [r]
    exact (div_pos_iff).2 (by rcases mul_pos_iff.1 hp with h|h <;> tauto)
  have hz : Z ∈ line[ℝ,U,V] := by
    apply mem_line_of_cross_eq_zero _ _ _ huv
    have he : r * cross U V X = cross U V Y := div_mul_cancel₀ _ hx
    dsimp [Z]
    simp only [cross,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at *
    linear_combination -he
  apply AffineSubspace.sSameSide_of_vsub_eq_smul
    (p₁ := U) (p₂ := Z) (m := X-U) (c₁ := (1:ℝ)) (c₂ := r)
    (left_mem_affineSpan_pair ℝ U V) hz
  · simp
  · simp [Z,vsub_eq_sub]
  · simpa using hr.le
  · intro hh; exact hx (cov_cross_zero_of_mem U V X hh)
  · intro hh; exact hy (cov_cross_zero_of_mem U V Y hh)

 theorem cov_opp_cross_neg (U V X Y : Pt) (huv : U ≠ V)
    (h : (line[ℝ,U,V]).SOppSide X Y) : cross U V X * cross U V Y < 0 := by
  obtain ⟨Z,hz,ht⟩ := h.exists_sbtw
  obtain ⟨⟨t,⟨ht0,ht1⟩,he⟩,hZX,hZY⟩ := ht
  have ht0' : t ≠ 0 := by intro hh; rw [hh,AffineMap.lineMap_apply_zero] at he; exact hZX he.symm
  have ht1' : t ≠ 1 := by intro hh; rw [hh,AffineMap.lineMap_apply_one] at he; exact hZY he.symm
  have htl : t < 1 := lt_of_le_of_ne ht1 ht1'
  have hec := cov_cross_zero_of_mem U V Z hz
  have hlin : (1-t) * cross U V X + t * cross U V Y = 0 := by
    rw [← he] at hec
    dsimp [cross] at *
    rw [lineMap_apply_coord,lineMap_apply_coord] at hec
    linear_combination hec
  have hx : cross U V X ≠ 0 := fun hh => h.left_notMem (mem_line_of_cross_eq_zero U V X huv hh)
  have heq : t * (cross U V X * cross U V Y) = -(1-t) * (cross U V X)^2 := by
    linear_combination (cross U V X) * hlin
  have hn : t * (cross U V X * cross U V Y) < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_ne_zero hx)
  exact neg_of_mul_neg_right hn ht0

theorem cov_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt) := by
  dsimp only
  intro h1a h1b h1c h2a h2b h2c hop hbase1 hbase2
  have hnc := affineIndependent_iff_not_collinear_set.1 h
  have hb : b ∉ line[ℝ,a,d] := by
    intro hb
    have hc : c ∈ line[ℝ,b,d] := hd.wbtw.collinear.mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hd.left_ne
    have hline : line[ℝ,b,d] ≤ line[ℝ,a,d] := affineSpan_le.2 (by
      intro p hp
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
      rcases hp with hp|hp
      · rw [hp]; exact hb
      · rw [hp]; exact right_mem_affineSpan_pair ℝ a d)
    have hc := hline hc
    have hh := collinear_triple_of_mem_affineSpan_pair
      (left_mem_affineSpan_pair ℝ a d) hb hc
    exact hnc hh
  have had : a ≠ d := by
    intro hh
    have hh' := hd.wbtw.collinear
    rw [← hh] at hh'
    apply hnc
    exact hh'.subset (by intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp ⊢; tauto)
  have hbc : (line[ℝ,a,d]).SOppSide b c := hd.sOppSide_of_notMem_of_mem hb
    (right_mem_affineSpan_pair ℝ a d)
  have hn1 := cov_opp_cross_neg a d b c had hbc
  have hn2 := cov_opp_cross_neg a d ω₁.center ω₂.center had hop
  have hs : (0 < cross a d ω₁.center * cross a d b ∧
      0 < cross a d ω₂.center * cross a d c) ∨
      (0 < cross a d ω₂.center * cross a d b ∧
      0 < cross a d ω₁.center * cross a d c) := by
    rcases mul_neg_iff.1 hn1 with hbc|hbc <;> rcases mul_neg_iff.1 hn2 with hpq|hpq
    · exact Or.inl ⟨mul_pos hpq.1 hbc.1,mul_pos_of_neg_of_neg hpq.2 hbc.2⟩
    · exact Or.inr ⟨mul_pos hpq.2 hbc.1,mul_pos_of_neg_of_neg hpq.1 hbc.2⟩
    · exact Or.inr ⟨mul_pos_of_neg_of_neg hpq.2 hbc.1,mul_pos hpq.1 hbc.2⟩
    · exact Or.inl ⟨mul_pos_of_neg_of_neg hpq.1 hbc.1,mul_pos hpq.2 hbc.2⟩
  rcases hs with hs|hs
  · exact cov_D4_part a b c d h hd ω₁ ω₂
      (cov_sameSide_of_cross_pos a d _ _ had hs.1)
      (cov_sameSide_of_cross_pos a d _ _ had hs.2)
      h1a h1b h1c h2a h2b h2c hop hbase1 hbase2
  · exact cov_D4_swapped_part a b c d h hd ω₁ ω₂
      (cov_sameSide_of_cross_pos a d _ _ had hs.1)
      (cov_sameSide_of_cross_pos a d _ _ had hs.2)
      h1a h1b h1c h2a h2b h2c hop hbase1 hbase2



/-! ## L15 gap 4 (D4 part): existence of the two Thébault circles -/

theorem gap_opp_of_cross_neg (U V X Y : Pt) (huv : U ≠ V)
    (hp : cross U V X * cross U V Y < 0) : (line[ℝ,U,V]).SOppSide X Y := by
  have hx : cross U V X ≠ 0 := by intro hh; rw [hh,zero_mul] at hp; linarith
  have hy : cross U V Y ≠ 0 := by intro hh; rw [hh,mul_zero] at hp; linarith
  let r := cross U V Y / cross U V X
  let Z := Y - r • (X - U)
  have hr : r < 0 := by
    dsimp [r]
    exact div_neg_iff.2 (by rcases mul_neg_iff.1 hp with h|h <;> tauto)
  have hz : Z ∈ line[ℝ,U,V] := by
    apply mem_line_of_cross_eq_zero _ _ _ huv
    have he : r * cross U V X = cross U V Y := div_mul_cancel₀ _ hx
    dsimp [Z]
    simp only [cross,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at *
    linear_combination -he
  apply AffineSubspace.sOppSide_of_vsub_eq_smul
    (p₁ := U) (p₂ := Z) (m := X-U) (c₁ := (1:ℝ)) (c₂ := r)
    (left_mem_affineSpan_pair ℝ U V) hz
  · simp
  · simp [Z,vsub_eq_sub]
  · linarith
  · intro hh; exact hx (cov_cross_zero_of_mem U V X hh)
  · intro hh; exact hy (cov_cross_zero_of_mem U V Y hh)

/-- One Thébault circle, centred on the bisector at `d` between ray `d → X` (`X - d = λ (c - b)`)
and ray `d → a`. -/
theorem gap_thebault_one (a b c d X : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) (tt : ℝ) (hd0 : d 0 = b 0 + tt * (c 0 - b 0)) (hd1 : d 1 = b 1 + tt * (c 1 - b 1))
    (l : ℝ) (hl : l ≠ 0) (hX0 : X 0 = d 0 + l * (c 0 - b 0)) (hX1 : X 1 = d 1 + l * (c 1 - b 1))
    (had : a ≠ d) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω : Sphere Pt, TangentToLine ω a d ∧ TangentToLine ω b c ∧
      InternallyTangent ω t.circumsphere ∧ (line[ℝ, b, c]).SSameSide ω.center a ∧
      ∃ μ : ℝ, 0 < μ ∧ cross a d ω.center = μ * l * cross b c a := by
  intro t
  have hbc : b ≠ c := hd.left_ne_right
  have hg : cross b c a ≠ 0 := cross_ne_zero_of_affineIndependent a b c h
  set g := cross b c a with hgdef
  set L := dist b c with hLdef
  set f := dist d a with hfdef
  set e := dist d X with hedef
  have hL : 0 < L := dist_pos.2 hbc
  have hf : 0 < f := dist_pos.2 (Ne.symm had)
  have hL2 : L ^ 2 = (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 := dist_sq_eq b c
  have he2 : e ^ 2 = (|l| * L) ^ 2 := by
    rw [dist_sq_eq, mul_pow, sq_abs, hL2, hX0, hX1]; ring
  have he : e = |l| * L := (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).1 he2
  have hepos : 0 < e := by rw [he]; exact mul_pos (abs_pos.2 hl) hL
  set v : Pt := (1 / e) • (X - d) + (1 / f) • (a - d) with hv
  let P : ℝ → Pt := fun s => d + s • v
  have P0 : ∀ s, P s 0 = d 0 + s * ((1 / e) * (X 0 - d 0) + (1 / f) * (a 0 - d 0)) := by
    intro s; simp [P, hv]; ring
  have P1 : ∀ s, P s 1 = d 1 + s * ((1 / e) * (X 1 - d 1) + (1 / f) * (a 1 - d 1)) := by
    intro s; simp [P, hv]; ring
  have cBC : ∀ s, cross b c (P s) = s / f * g := by
    intro s; rw [hgdef]; unfold cross; rw [P0, P1, hX0, hX1, hd0, hd1]; ring
  have cAD : ∀ s, cross a d (P s) = s / e * l * g := by
    intro s; rw [hgdef]; unfold cross; rw [P0, P1, hX0, hX1, hd0, hd1]; ring
  set k := |g| / (L * f) with hk
  have hkpos : 0 < k := div_pos (abs_pos.2 hg) (mul_pos hL hf)
  have iBC : ∀ s, 0 ≤ s → Metric.infDist (P s) (line[ℝ, b, c] : Set Pt) = k * s := by
    intro s hs
    rw [infDist_line_eq _ _ _ hbc, cBC, ← hLdef, abs_mul, abs_div, abs_of_nonneg hs, abs_of_pos hf, hk]
    field_simp
  have iAD : ∀ s, 0 ≤ s → Metric.infDist (P s) (line[ℝ, a, d] : Set Pt) = k * s := by
    intro s hs
    rw [infDist_line_eq _ _ _ had, cAD, dist_comm, ← hfdef, abs_mul, abs_mul, abs_div,
      abs_of_nonneg hs, abs_of_pos hepos, he, hk]
    have : |l| ≠ 0 := abs_ne_zero.2 hl
    field_simp
  -- the circumcircle
  set O := t.circumcenter
  set R := t.circumradius
  have hbO : b ∈ t.circumsphere := t.mem_circumsphere 1
  have hcO : c ∈ t.circumsphere := t.mem_circumsphere 2
  have hdO : dist d O < R := by
    have := Sphere.dist_center_lt_radius_of_sbtw hbO hcO hd
    rw [dist_comm]; exact this
  let F : ℝ → ℝ := fun s => dist (P s) O + k * s - R
  have hFc : Continuous F := by
    have : Continuous P := by fun_prop
    fun_prop
  have hF0 : F 0 < 0 := by simp [F, P]; linarith
  set s₁ := (R + 1) / k
  have hs₁ : 0 ≤ s₁ := by
    have hR : 0 ≤ R := le_trans dist_nonneg hdO.le
    positivity
  have hF1 : 0 < F s₁ := by
    have : k * s₁ = R + 1 := by simp only [s₁]; field_simp
    simp only [F, this]
    linarith [dist_nonneg (x := P s₁) (y := O)]
  obtain ⟨s, ⟨hs0, -⟩, hFs⟩ :=
    intermediate_value_Icc hs₁ hFc.continuousOn ⟨hF0.le, hF1.le⟩
  have hspos : 0 < s := by
    rcases hs0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hFs; linarith
  have hrpos : 0 < k * s := mul_pos hkpos hspos
  have hdist : dist (P s) O = R - k * s := by simp only [F] at hFs; linarith
  have hrR : k * s < R := by
    have h1 := Metric.infDist_le_dist_of_mem (x := P s)
      (AffineMap.lineMap_mem_affineSpan_pair tt b c : AffineMap.lineMap b c tt ∈ line[ℝ, b, c])
    have hdeq : AffineMap.lineMap b c tt = d := by
      apply pt_ext <;> rw [lineMap_apply_coord] <;> linarith
    rw [hdeq, iBC s hspos.le] at h1
    have h2 := dist_triangle (P s) O d
    rw [dist_comm O d] at h2
    linarith
  refine ⟨⟨P s, k * s⟩, ⟨hrpos, iAD s hspos.le⟩, ⟨hrpos, iBC s hspos.le⟩,
    ⟨hrpos, hrR, hdist⟩, ?_, s / e, div_pos hspos hepos, ?_⟩
  · apply cov_sameSide_of_cross_pos _ _ _ _ hbc
    show 0 < cross b c (P s) * cross b c a
    rw [cBC, ← hgdef]
    have : 0 < g ^ 2 := by positivity
    have : 0 < s / f := div_pos hspos hf
    nlinarith
  · show cross a d (P s) = _
    rw [cAD]

/-- **D4 obligation, exact writer statement.** -/
theorem cov_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a := by
  intro t
  obtain ⟨⟨tt, ⟨ht0, ht1⟩, hdt⟩, hdb, hdc⟩ := hd
  have hd0 : d 0 = b 0 + tt * (c 0 - b 0) := by rw [← hdt, lineMap_apply_coord]
  have hd1 : d 1 = b 1 + tt * (c 1 - b 1) := by rw [← hdt, lineMap_apply_coord]
  have hsb : Sbtw ℝ b d c := ⟨⟨tt, ⟨ht0, ht1⟩, hdt⟩, hdb, hdc⟩
  have htne0 : tt ≠ 0 := by
    intro h0; apply hdb; rw [← hdt, h0, AffineMap.lineMap_apply_zero]
  have htne1 : tt ≠ 1 := by
    intro h0; apply hdc; rw [← hdt, h0, AffineMap.lineMap_apply_one]
  have hnc := affineIndependent_iff_not_collinear_set.1 h
  have had : a ≠ d := by
    intro hh
    have hh' := hsb.wbtw.collinear
    rw [← hh] at hh'
    apply hnc
    exact hh'.subset (by intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp ⊢; tauto)
  obtain ⟨ω₁, h1a, h1b, h1c, h1s, μ₁, hμ₁, hc₁⟩ := gap_thebault_one a b c d b h hsb tt hd0 hd1
    (-tt) (neg_ne_zero.2 htne0) (by rw [hd0]; ring) (by rw [hd1]; ring) had
  obtain ⟨ω₂, h2a, h2b, h2c, h2s, μ₂, hμ₂, hc₂⟩ := gap_thebault_one a b c d c h hsb tt hd0 hd1
    (1 - tt) (sub_ne_zero.2 (Ne.symm htne1)) (by rw [hd0]; ring) (by rw [hd1]; ring) had
  refine ⟨ω₁, ω₂, h1a, h1b, h1c, h2a, h2b, h2c, ?_, h1s, h2s⟩
  apply gap_opp_of_cross_neg _ _ _ _ had
  rw [hc₁, hc₂]
  have hg := cross_ne_zero_of_affineIndependent a b c h
  have htp : 0 < tt := lt_of_le_of_ne ht0 (Ne.symm htne0)
  have htl : tt < 1 := lt_of_le_of_ne ht1 htne1
  have e : μ₁ * -tt * cross b c a * (μ₂ * (1 - tt) * cross b c a) =
      -((μ₁ * μ₂) * (tt * (1 - tt)) * (cross b c a) ^ 2) := by ring
  rw [e, neg_lt_zero]
  have : 0 < (cross b c a) ^ 2 := by positivity
  have : 0 < tt * (1 - tt) := mul_pos htp (by linarith)
  positivity

theorem cov_D4_obligation_exact (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : classical_D4_obligation a b c d h hd :=
  cov_D4_obligation a b c d h hd

end Thebault3.Classical
