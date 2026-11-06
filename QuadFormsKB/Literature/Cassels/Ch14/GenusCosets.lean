/-
# Cassels, Chapter 14, §3: the genera are the cosets of $\mathcal G^2$ (Corollary to Theorem 3.1)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 339 (Corollary to Theorem 3.1), with §1, pp. 332–333
(14.r3) and the proof of Theorem 5.1, p. 343 (the number of genera).

For a discriminant $D \ne 0$ ($D \equiv 0, 1 \bmod 4$) and the group $\mathcal G$ = `FormClass D` of proper classes
of primitive forms of discriminant $D$:

* `sameGenus_iff_exists_sq`: two primitive forms of discriminant $D$ are in the same genus (equivalent over every
  $\mathbb Z_p$ and over $\mathbb R$, `Siegel.SameGenus`) if and only if their classes differ by a square
  $\mathfrak S^2$, i.e. the genera are the cosets of $\mathcal G$ modulo $\mathcal G^2$;
* `genusClasses`, `genusClasses_eq`: the classes in the genus of $f$ form the coset $\mathfrak C\,\mathcal G^2$ of the
  class $\mathfrak C$ of $f$; `card_genusClasses`: any two genera contain the same number of classes;
* `card_genera`: the number of genera is the order of the group $\mathcal A$ of ambiguous classes (14.r3; Cassels'
  "general property of finite abelian groups", proof of Theorem 5.1, p. 343).

*Proof route.* Cassels deduces the Corollary from Theorem 3.1 through the local groups $\mathcal G_p$ of
$\mathbb Z_p$-classes and the homomorphisms $\mathcal G \to \mathcal G_p$ (3.1), which he obtains "by mimicking the
argument of Section 2". The local groups are not formalized here; the proof uses instead:
* (cosets $\Rightarrow$ genus) Lemma 2.5: $\mathfrak S^2$ contains a form $[w^2, B, *]$ with $w$ prime to $2D$;
  composing with a concordant $[a, B, *] \in \mathfrak C$ gives $[a w^2, B, c] \in \mathfrak C\mathfrak S^2$, which
  is equivalent to $[a, B, c w^2]$ over $\mathbb R$ and over $\mathbb Z_p$ for $p \nmid w$ (substitution
  $x \mapsto w^{-1}x$, $y \mapsto wy$) and over $\mathbb Z_p$ for $p \mid w$ (Lemma 3.1 (i));
* (genus $\Rightarrow$ cosets) the semi-equivalence of forms in one genus (Ch. 9, Thm. 7.1, as in part (i) of the
  proof of Theorem 3.1): $f_1$ represents primitively $a w^2$, where $a$ is the first coefficient of
  $f_2 = [a, b, *]$, $w$ is prime to $2Da$, and the middle coefficient of the resulting form $[a w^2, B, *] \sim f_1$
  satisfies $B \equiv \pm b \pmod{2a}$; then $[a w^2, B, *]$ is the composition of $[a, B, *] \sim f_2^{\pm 1}$ with
  $[w^2, B, *]$, a square by Lemma 2.5.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Genus
import QuadFormsKB.Literature.Cassels.Ch14.Ambiguous

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

variable {D : ℤ} [NonzeroDisc D]

/-! ### Helpers -/

/-- The substitution $x \mapsto w^{-1}x$, $y \mapsto wy$ over a ring in which $w$ is a unit takes
$[a w^2, b, c]$ to $[a, b, c w^2]$ (helper for `sameGenus_of_mk_eq_mul_sq`). -/
private theorem isometricGL_scale_of_isUnit {R : Type*} [CommRing R] {F G : BinQF} {w : ℤ}
    (hu : IsUnit (w : R)) (ha : F.a = G.a * w ^ 2) (hb : F.b = G.b) (hc : G.c = F.c * w ^ 2) :
    IsometricGL (F.map (Int.castRingHom R)) (G.map (Int.castRingHom R)) := by
  obtain ⟨u0, hu0⟩ := hu
  set u : R := ((u0⁻¹ : Rˣ) : R)
  have hwu : (w : R) * u = 1 := by rw [← hu0]; exact u0.mul_inv
  have huw : u * (w : R) = 1 := by rw [mul_comm]; exact hwu
  refine isometricGL_of_mat !![u, 0; 0, (w : R)] !![(w : R), 0; 0, u] ?_ ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hwu, huw]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hwu, huw]
  · intro v
    rw [eval_map_two, eval_map_two]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [ha, hb, hc]
    simp only [map_mul, map_pow, eq_intCast]
    linear_combination (((G.a : R)) * v 0 ^ 2 * ((w : R) * u + 1) + (G.b : R) * v 0 * v 1) * hwu

/-- Forms $[A w^2, b, c]$ and $[A, b, c w^2]$ with $w$ prime to $2D$ are in the same genus
(helper for `sameGenus_of_mk_eq_mul_sq`). -/
private theorem sameGenus_scale {F G : BinQF} {w : ℤ} (hw : IsCoprime w (2 * F.disc))
    (hdisc : F.disc = G.disc) (ha : F.a = G.a * w ^ 2) (hb : F.b = G.b) (hc : G.c = F.c * w ^ 2) :
    SameGenus F G := by
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  refine ⟨fun p _ => ?_, ?_⟩
  · by_cases hp : (p : ℤ) ∣ w
    · have hp1 : ¬ (p : ℤ) ∣ 2 * F.disc := by
        intro hd
        obtain ⟨a, b, hab⟩ := hw
        have : (p : ℤ) ∣ 1 := by
          rw [← hab]; exact dvd_add (dvd_mul_of_dvd_right hp _) (dvd_mul_of_dvd_right hd _)
        have := Int.eq_one_of_dvd_one (by positivity) this
        have hp1 := (Fact.out : p.Prime).one_lt
        omega
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hp1 (dvd_mul_right _ _)
      exact isometricGL_padic_of_not_dvd hp2 hdisc (fun hd => hp1 (dvd_mul_of_dvd_right hd _))
    · have hu : IsUnit ((w : ℤ) : ℤ_[p]) := by
        rw [PadicInt.isUnit_iff]
        have h1 := PadicInt.norm_le_one ((w : ℤ) : ℤ_[p])
        have h2 := PadicInt.norm_int_lt_one_iff_dvd (p := p) w
        exact le_antisymm h1 (not_lt.mp (fun hlt => hp (h2.mp hlt)))
      exact isometricGL_scale_of_isUnit hu ha hb hc
  · have hu : IsUnit ((w : ℤ) : ℝ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hw0)
    exact isometricGL_scale_of_isUnit hu ha hb hc


/-- **Classes of a coset of $\mathcal G^2$ are in one genus** (Cassels, Ch. 14, Corollary to Theorem 3.1, p. 339,
"cosets $\Rightarrow$ genera"): if $\mathfrak C_1 = \mathfrak C_2\,\mathfrak S^2$ then the forms of $\mathfrak C_1$
and $\mathfrak C_2$ are in the same genus. -/
theorem sameGenus_of_mk_eq_mul_sq (f g : PrimForm D) (S : FormClass D) (h : mk f = mk g * S ^ 2) :
    SameGenus f.1 g.1 := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  obtain ⟨m0, hm0, w, x, y, hxy, hw, hev⟩ :=
    (exists_pow_eq_iff (D := D) (n := 2) (by norm_num) (S ^ 2)).mp ⟨S, rfl⟩
  obtain ⟨mm, em, hmma⟩ := exists_sLEquiv_a_of_eval (f := m0.1) hxy
  rw [hev] at hmma
  obtain ⟨m, hmk, hma⟩ : ∃ m : PrimForm D, mk m = S ^ 2 ∧ m.1.a = w ^ 2 :=
    ⟨ofEquiv m0 em, by rw [← hm0]; exact mk_eq_mk.2 em.symm, hmma⟩
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  obtain ⟨g', hg', hga⟩ := exists_rep_coprime (mk g) (M := 2 * D * w)
    (mul_ne_zero (mul_ne_zero two_ne_zero hD0) hw0)
  have ha0 : g'.1.a ≠ 0 := ne_zero_of_coprime_two_mul (N := D * w)
    (by rw [← mul_assoc]; exact hga)
  have haw : IsCoprime g'.1.a w := hga.of_isCoprime_of_dvd_right ⟨2 * D, by ring⟩
  have haw2 : IsCoprime g'.1.a (w ^ 2) := haw.pow_right
  obtain ⟨B, hB1, hB2⟩ := exists_common_b (a := g'.1.a) (a' := m.1.a) (b := g'.1.b) (b' := m.1.b)
    (by rw [hma]; exact haw2) (two_dvd_b_sub_b (g'.2.2.trans m.2.2.symm))
  obtain ⟨k0, ek, hka, hkb⟩ := exists_sLEquiv_b (f := g'.1) (B := B) hB1
  obtain ⟨m1, em1, hm1a, hm1b⟩ := exists_sLEquiv_b (f := m.1) (B := B) hB2
  obtain ⟨K, hKk, hKa, hKb⟩ : ∃ K : PrimForm D, mk K = mk g' ∧ K.1.a = g'.1.a ∧ K.1.b = B :=
    ⟨ofEquiv g' ek, mk_eq_mk.2 ek.symm, hka, hkb⟩
  obtain ⟨M1, hM1k, hM1a, hM1b⟩ : ∃ M1 : PrimForm D, mk M1 = mk m ∧ M1.1.a = m.1.a ∧ M1.1.b = B :=
    ⟨ofEquiv m em1, mk_eq_mk.2 em1.symm, hm1a, hm1b⟩
  have hc : Concordant K.1 M1.1 := concordant_of_coprime
    (by rw [hKa, hM1a, hma]; exact mul_ne_zero ha0 (pow_ne_zero 2 hw0))
    (hKb.trans hM1b.symm) (K.2.2.trans M1.2.2.symm) (by rw [hKa, hM1a, hma]; exact haw2)
  have hprod := mk_mul_mk K M1 hc
  have hfc : mk f = mk (PrimForm.comp K M1 hc) := by
    rw [← hprod, hKk, hM1k, hmk, hg', h]
  have e1 : SLEquiv f.1 (PrimForm.comp K M1 hc).1 := mk_eq_mk.1 hfc
  have e2 : SLEquiv K.1 g.1 := mk_eq_mk.1 (hKk.trans hg')
  have hCa : (PrimForm.comp K M1 hc).1.a = K.1.a * w ^ 2 := by
    rw [primComp_a, hM1a, hma]
  have hCb : (PrimForm.comp K M1 hc).1.b = K.1.b := by rw [primComp_b]
  have hCd : (PrimForm.comp K M1 hc).1.disc = D := (PrimForm.comp K M1 hc).2.2
  have hKd : K.1.disc = D := K.2.2
  have hcc : K.1.c = (PrimForm.comp K M1 hc).1.c * w ^ 2 := by
    have h1 : K.1.b ^ 2 - 4 * K.1.a * K.1.c = D := hKd
    have h2 : (PrimForm.comp K M1 hc).1.b ^ 2 - 4 * (PrimForm.comp K M1 hc).1.a *
        (PrimForm.comp K M1 hc).1.c = D := hCd
    rw [hCa, hCb] at h2
    have h3 : (4 * K.1.a) * (K.1.c - (PrimForm.comp K M1 hc).1.c * w ^ 2) = 0 := by
      linear_combination h2 - h1
    have h4 : 4 * K.1.a ≠ 0 := mul_ne_zero (by norm_num) (by rw [hKa]; exact ha0)
    have := (mul_eq_zero.1 h3).resolve_left h4
    linarith
  have hsg : SameGenus (PrimForm.comp K M1 hc).1 K.1 :=
    sameGenus_scale (by rw [hCd]; exact hw) (hCd.trans hKd.symm) hCa hCb hcc
  exact (e1.intEquiv.sameGenus).trans (hsg.trans (e2.intEquiv.sameGenus))

/-- Arithmetic core of `exists_sq_of_sameGenus`: from an integral description of the $\mathbb Z^{(P)}$-equivalence
$f_1 \circ (S/d) = [a, b, c_2]$ (columns $(X, Y)$, $(X', Y')$ of $dS$, $\det S = \varepsilon = \pm 1$, $a$ prime to
$2Dd$) extract $w$ prime to $2D$ and a form $[a w^2, B, C] \sim f_1$ with $B \equiv \varepsilon^{-1} b \pmod{2a}$. -/
private theorem core {f1 : BinQF} {D : ℤ} (hD : f1.disc = D) {a b c2 d X Y X' Y' ε : ℤ}
    (hdisc2 : b ^ 2 - 4 * a * c2 = D) (hd : d ≠ 0) (hdD : IsCoprime d (2 * D)) (haD : IsCoprime a (2 * D))
    (had : IsCoprime a d) (hε : ε = 1 ∨ ε = -1) (hdet : X * Y' - X' * Y = ε * d ^ 2)
    (hA : f1.eval X Y = d ^ 2 * a) (hC : f1.eval X' Y' = d ^ 2 * c2)
    (hP : f1.eval (X + X') (Y + Y') = d ^ 2 * (a + b + c2)) :
    ∃ w B C : ℤ, IsCoprime w (2 * D) ∧ IsCoprime a w ∧
      SLEquiv f1 (BinQF.mk (a * w ^ 2) B C) ∧ B ^ 2 - 4 * (a * w ^ 2) * C = D ∧ 2 * a ∣ b - ε * B := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hd2 : d ^ 2 = ε * (X * Y' - X' * Y) := by
    rw [hdet]; linear_combination (-(d ^ 2)) * hε2
  have hXY : 0 < Int.gcd X Y := by
    rcases Nat.eq_zero_or_pos (Int.gcd X Y) with h0 | h0
    · exfalso
      obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
      have : d ^ 2 = 0 := by rw [hd2]; ring
      exact hd (pow_eq_zero_iff two_ne_zero |>.1 this)
    · exact h0
  obtain ⟨g, x, y, hg, hxy1, hX, hY⟩ := Int.exists_gcd_one' hXY
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hxy : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.2 hxy1
  have hgd2 : (g : ℤ) ∣ d ^ 2 := ⟨ε * (x * Y' - X' * y), by rw [hd2, hX, hY]; ring⟩
  have hag : IsCoprime a (g : ℤ) := (had.pow_right (n := 2)).of_isCoprime_of_dvd_right hgd2
  have hf : f1.eval X Y = (g : ℤ) ^ 2 * f1.eval x y := by
    rw [hX, hY, eval_eq, eval_eq]; ring
  have hg2 : (g : ℤ) ^ 2 ∣ d ^ 2 := by
    have : (g : ℤ) ^ 2 ∣ d ^ 2 * a := ⟨f1.eval x y, by rw [← hA, hf]⟩
    exact (hag.symm.pow_left (m := 2)).dvd_of_dvd_mul_right this
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hg2
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hd (by rw [hw]; ring)
  have hxyv : f1.eval x y = a * w ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hg0) ?_
    rw [← hf, hA, hw]; ring
  have hwd : IsCoprime w (2 * D) := hdD.of_isCoprime_of_dvd_left ⟨g, by rw [hw]; ring⟩
  have haw : IsCoprime a w := had.of_isCoprime_of_dvd_right ⟨g, by rw [hw]; ring⟩
  obtain ⟨u, v, huv⟩ := hxy
  have e1 : SLEquiv f1 (BinQF.subst x (-v) y u f1) :=
    (sLEquiv_iff _ _).2 ⟨x, -v, y, u, by linear_combination huv, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = 2 * f1.a * x * (-v) + f1.b * (x * u + (-v) * y) + 2 * f1.c * y * u := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℤ, C = f1.a * (-v) ^ 2 + f1.b * (-v) * u + f1.c * u ^ 2 := ⟨_, rfl⟩
  have e2 : BinQF.subst x (-v) y u f1 = BinQF.mk (a * w ^ 2) B C := by
    refine ext_abc ?_ ?_ ?_
    · simp only [subst, a_mk]; rw [← hxyv, eval_eq]
    · simp only [subst, b_mk]; rw [hB]
    · simp only [subst, c_mk]; rw [hCdef]
  rw [e2] at e1
  have hdiscB : B ^ 2 - 4 * (a * w ^ 2) * C = D := by
    have := SLEquiv.disc_eq e1
    rw [hD] at this
    simpa [BinQF.disc] using this.symm
  obtain ⟨A', Bt, hX', hY'⟩ : ∃ A' Bt : ℤ, X' = A' * x + Bt * (-v) ∧ Y' = A' * y + Bt * u :=
    ⟨u * X' + v * Y', x * Y' - y * X', by linear_combination (-X') * huv, by linear_combination (-Y') * huv⟩
  subst hX' hY' hX hY
  have hBt : Bt = ε * g * w ^ 2 := by
    refine mul_left_cancel₀ hg0 ?_
    have h1 : (g : ℤ) * Bt = ε * d ^ 2 := by linear_combination hdet - (g * Bt) * huv
    rw [h1, hw]; ring
  have hPol : f1.eval (x * g + (A' * x + Bt * -v)) (y * g + (A' * y + Bt * u)) - f1.eval (x * g) (y * g) -
      f1.eval (A' * x + Bt * -v) (A' * y + Bt * u) = d ^ 2 * b := by
    linear_combination hP - hA - hC
  rw [eval_eq, eval_eq, eval_eq] at hPol
  have key1 : d ^ 2 * b = 2 * g * A' * (a * w ^ 2) + g * Bt * B := by
    rw [← hxyv, eval_eq, hB]
    linear_combination (-1 : ℤ) * hPol
  subst hw hBt
  have key2 : (g * w ^ 2 : ℤ) * (g * (b - ε * B) - 2 * a * A') = 0 := by linear_combination key1
  have hne : (g * w ^ 2 : ℤ) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero 2 hw0)
  have key3 : (g : ℤ) * (b - ε * B) = 2 * a * A' := by
    have := (mul_eq_zero.1 key2).resolve_left hne
    linarith
  have ha1 : a ∣ b - ε * B := by
    refine hag.dvd_of_dvd_mul_left ?_
    exact ⟨2 * A', by linear_combination key3⟩
  have hpar : (2 : ℤ) ∣ b - ε * B := by
    have h2 := two_dvd_b_sub_b (f := BinQF.mk a b c2) (g := BinQF.mk (a * w ^ 2) B C)
      (by simp only [BinQF.disc, a_mk, b_mk, c_mk]; rw [hdisc2, ← hdiscB])
    simp only [b_mk] at h2
    rcases hε with rfl | rfl <;> omega
  have h2a : IsCoprime (2 : ℤ) a := (haD.of_isCoprime_of_dvd_right ⟨D, rfl⟩).symm
  exact ⟨w, B, C, hwd, haw, e1, hdiscB, IsCoprime.mul_dvd h2a hpar ha1⟩

/-- Final assembly for `exists_sq_of_sameGenus`: if $f_1 \sim [a w^2, B, C]$ with $w$ prime to $2D$, $a$ prime to
$2Dw$ and $B \equiv \pm b \pmod{2a}$ for $g' = [a, b, *]$, then $\mathfrak C_{f_1} = \mathfrak C_{g'}\mathfrak S^2$:
$[a w^2, B, C]$ is the composition of $[a, B, Cw^2] \sim g'^{\pm 1}$ and the square $[w^2, B, aC]$. -/
private theorem finish (f1 g' : PrimForm D) {w B C ε : ℤ} (hw : IsCoprime w (2 * D))
    (haD : IsCoprime g'.1.a (2 * D)) (haw : IsCoprime g'.1.a w) (hε : ε = 1 ∨ ε = -1)
    (hf : SLEquiv f1.1 (BinQF.mk (g'.1.a * w ^ 2) B C)) (hdisc : B ^ 2 - 4 * (g'.1.a * w ^ 2) * C = D)
    (hdvd : 2 * g'.1.a ∣ g'.1.b - ε * B) :
    ∃ S : FormClass D, mk f1 = mk g' * S ^ 2 := by
  have ha0 := ne_zero_of_coprime_two_mul haD
  have hw0 := ne_zero_of_coprime_two_mul hw
  have haDD : IsCoprime g'.1.a D := haD.of_isCoprime_of_dvd_right ⟨2, by ring⟩
  have hwD : IsCoprime w D := hw.of_isCoprime_of_dvd_right ⟨2, by ring⟩
  obtain ⟨K, hK⟩ : ∃ K : PrimForm D, K.1 = BinQF.mk g'.1.a B (C * w ^ 2) :=
    ⟨⟨BinQF.mk g'.1.a B (C * w ^ 2),
      by
        intro d h1 h2 _
        simp only [a_mk, b_mk] at h1 h2
        refine haDD.isUnit_of_dvd' h1 ?_
        rw [← hdisc]
        have h3 : d ∣ 4 * (g'.1.a * w ^ 2) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h1 _) 4
        exact dvd_sub (dvd_pow h2 two_ne_zero) (dvd_mul_of_dvd_left h3 C),
      by
        simp only [BinQF.disc, a_mk, b_mk, c_mk]
        linear_combination hdisc⟩, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : PrimForm D, M.1 = BinQF.mk (w ^ 2) B (g'.1.a * C) :=
    ⟨⟨BinQF.mk (w ^ 2) B (g'.1.a * C),
      by
        intro d h1 h2 _
        simp only [a_mk, b_mk] at h1 h2
        refine hwD.pow_left.isUnit_of_dvd' h1 ?_
        rw [← hdisc]
        have h3 : d ∣ 4 * (g'.1.a * w ^ 2) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h1 _) 4
        exact dvd_sub (dvd_pow h2 two_ne_zero) (dvd_mul_of_dvd_left h3 C),
      by
        simp only [BinQF.disc, a_mk, b_mk, c_mk]
        linear_combination hdisc⟩, rfl⟩
  have hKa : K.1.a = g'.1.a := by rw [hK, a_mk]
  have hKb : K.1.b = B := by rw [hK, b_mk]
  have hMa : M.1.a = w ^ 2 := by rw [hM, a_mk]
  have hMb : M.1.b = B := by rw [hM, b_mk]
  have hc : Concordant K.1 M.1 := concordant_of_coprime
    (by rw [hKa, hMa]; exact mul_ne_zero ha0 (pow_ne_zero 2 hw0)) (hKb.trans hMb.symm)
    (K.2.2.trans M.2.2.symm) (by rw [hKa, hMa]; exact haw.pow_right)
  have hCm : (PrimForm.comp K M hc).1 = BinQF.mk (g'.1.a * w ^ 2) B C := by
    apply eq_of_a_b_disc
    · rw [primComp_a, hKa, hMa]; exact mul_ne_zero ha0 (pow_ne_zero 2 hw0)
    · rw [primComp_a, hKa, hMa, a_mk]
    · rw [primComp_b, hKb, b_mk]
    · rw [(PrimForm.comp K M hc).2.2]
      simp only [BinQF.disc, a_mk, b_mk, c_mk]
      linear_combination -hdisc
  obtain ⟨T, hT⟩ := (exists_pow_eq_iff (D := D) (n := 2) (by norm_num) (mk M)).2
    ⟨M, rfl, w, 1, 0, isCoprime_one_left, hw, by simp [eval_eq, hMa]⟩
  have hfc : mk f1 = mk K * T ^ 2 := by
    rw [hT, mk_mul_mk K M hc]
    exact mk_eq_mk.2 (by rw [hCm]; exact hf)
  have hKcl : mk K = mk g' ∨ mk K = (mk g')⁻¹ := by
    have hKd : K.1.disc = D := K.2.2
    rcases hε with rfl | rfl
    · left
      obtain ⟨k0, ek, hka, hkb⟩ := exists_sLEquiv_b (f := g'.1) (B := B)
        (by obtain ⟨l, hl⟩ := hdvd; exact ⟨-l, by linarith⟩)
      have : k0 = K.1 := by
        apply eq_of_a_b_disc
        · rw [hka]; exact ha0
        · rw [hka, hKa]
        · rw [hkb, hKb]
        · rw [← SLEquiv.disc_eq ek, hKd, g'.2.2]
      exact (mk_eq_mk.2 (by rw [← this]; exact ek)).symm
    · right
      obtain ⟨k0, ek, hka, hkb⟩ := exists_sLEquiv_b (f := conjForm g'.1) (B := B)
        (by
          simp only [conjForm, a_mk, b_mk]
          obtain ⟨l, hl⟩ := hdvd; exact ⟨l, by linarith⟩)
      simp only [conjForm, a_mk] at hka hkb
      have : k0 = K.1 := by
        apply eq_of_a_b_disc
        · rw [hka]; exact ha0
        · rw [hka, hKa]
        · rw [hkb, hKb]
        · rw [← SLEquiv.disc_eq ek, hKd, disc_conjForm, g'.2.2]
      rw [mk_inv]
      exact (mk_eq_mk.2 (by rw [← this]; exact ek)).symm
  rcases hKcl with h | h
  · exact ⟨T, by rw [hfc, h]⟩
  · refine ⟨(mk g')⁻¹ * T, ?_⟩
    rw [hfc, h, mul_pow, inv_pow, ← mul_assoc]
    group

/-- Coprimality from primes (helper). -/
private theorem isCoprime_of_forall_prime {n m : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → ¬ (p : ℤ) ∣ n) : IsCoprime n m := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hqd' : (q : ℤ) ∣ (Int.gcd n m : ℤ) := Int.natCast_dvd_natCast.mpr hqd
  exact h q hq (hqd'.trans (Int.gcd_dvd_right ..)) (hqd'.trans (Int.gcd_dvd_left ..))

/-- A rational times a common multiple of its denominator is an integer (helper). -/
private theorem exists_int_mul {q : ℚ} {N : ℕ} (h : q.den ∣ N) : ∃ X : ℤ, (X : ℚ) = q * N := by
  obtain ⟨r, hr⟩ := h
  refine ⟨q.num * r, ?_⟩
  rw [hr]; push_cast; rw [← Rat.mul_den_eq_num q]; ring

/-- **Integral form of a $\mathbb Z^{(P)}$-equivalence** ($P$ the primes of $2D$): if $f, g$ are in one genus, there
are $d$ prime to $2D$ and integer vectors $(X, Y)$, $(X', Y')$ (the columns of $dS$) with
$f(X, Y) = d^2 a_g$, $f(X', Y') = d^2 c_g$, the polar value $= d^2 b_g$ and determinant $\pm d^2$. -/
private theorem extract (f g : PrimForm D) (h : SameGenus f.1 g.1) :
    ∃ d X Y X' Y' ε : ℤ, d ≠ 0 ∧ IsCoprime d (2 * D) ∧ (ε = 1 ∨ ε = -1) ∧ X * Y' - X' * Y = ε * d ^ 2 ∧
      f.1.eval X Y = d ^ 2 * g.1.a ∧ f.1.eval X' Y' = d ^ 2 * g.1.c ∧
      f.1.eval (X + X') (Y + Y') = d ^ 2 * (g.1.a + g.1.b + g.1.c) := by
  classical
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  set P : Finset Nat.Primes := (2 * D).natAbs.primeFactors.subtype Nat.Prime with hP
  have hn0 : (2 * D).natAbs ≠ 0 := by simpa using hD0
  have hmem : ∀ p : ℕ, ∀ hp : p.Prime, (p : ℤ) ∣ 2 * D → (⟨p, hp⟩ : Nat.Primes) ∈ P := by
    intro p hp hd
    exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hd, hn0⟩)
  have hsg : g.1.b ^ 2 - 4 * g.1.a * g.1.c = D := g.2.2
  have hsf : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := f.2.2
  have hdet : g.1.hessian.det ≠ 0 := by
    rw [Binary.hessian_det_two]
    show 4 * g.1.a * g.1.c - g.1.b ^ 2 ≠ 0
    intro h0; apply hD0; linarith
  obtain ⟨S, hS⟩ := semiEquiv_of_sameGenus g.1 f.1 hdet h.symm P
  have hv : ∀ v0 v1 : ℚ,
      (f.1.a : ℚ) * (((S.val 0 0 : intAway P) : ℚ) * v0 + ((S.val 0 1 : intAway P) : ℚ) * v1) ^ 2 +
        f.1.b * (((S.val 0 0 : intAway P) : ℚ) * v0 + ((S.val 0 1 : intAway P) : ℚ) * v1) *
          (((S.val 1 0 : intAway P) : ℚ) * v0 + ((S.val 1 1 : intAway P) : ℚ) * v1) +
        f.1.c * (((S.val 1 0 : intAway P) : ℚ) * v0 + ((S.val 1 1 : intAway P) : ℚ) * v1) ^ 2 =
      g.1.a * v0 ^ 2 + g.1.b * v0 * v1 + g.1.c * v1 ^ 2 := by
    intro v0 v1
    have := hS ![v0, v1]
    rw [evalIn_map_rat_eq, evalIn_map_rat_eq, Binary.eval_map_two, Binary.eval_map_two] at this
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this
  have hB : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), ‖(q : ℚ_[p])‖ ≤ 1 → ¬ p ∣ q.den := by
    intro p _ q hq hdvd
    have hu := PadicInt.isUnit_den (p := p) q hq
    rw [PadicInt.isUnit_iff] at hu
    have h1 : ‖((q.den : ℤ) : ℤ_[p])‖ < 1 :=
      (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
    have h2 : ((q.den : ℕ) : ℤ_[p]) = ((q.den : ℤ) : ℤ_[p]) := by simp
    rw [h2] at hu
    linarith
  have hB' : ∀ (a : intAway P) (p : ℕ) (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∈ P →
      ¬ p ∣ (a : ℚ).den := by
    intro a p hp hm
    have := Fact.mk hp
    exact hB p (a : ℚ) (a.2 ⟨p, hp⟩ hm)
  have hent : ∀ i j : Fin 2, ∃ q : ℚ, q = ((S.val i j : intAway P) : ℚ) ∧
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * D → ¬ p ∣ q.den := by
    intro i j
    exact ⟨_, rfl, fun p hp hd => hB' (S.val i j) p hp (hmem p hp hd)⟩
  obtain ⟨q00, h00, hd00⟩ := hent 0 0
  obtain ⟨q01, h01, hd01⟩ := hent 0 1
  obtain ⟨q10, h10, hd10⟩ := hent 1 0
  obtain ⟨q11, h11, hd11⟩ := hent 1 1
  rw [← h00, ← h01, ← h10, ← h11] at hv
  have H1 : (f.1.a : ℚ) * q00 ^ 2 + f.1.b * q00 * q10 + f.1.c * q10 ^ 2 = g.1.a := by
    linear_combination hv 1 0
  have H2 : (f.1.a : ℚ) * q01 ^ 2 + f.1.b * q01 * q11 + f.1.c * q11 ^ 2 = g.1.c := by
    linear_combination hv 0 1
  have H3 : (f.1.a : ℚ) * (q00 + q01) ^ 2 + f.1.b * (q00 + q01) * (q10 + q11) + f.1.c * (q10 + q11) ^ 2 =
      g.1.a + g.1.b + g.1.c := by
    linear_combination hv 1 1
  have hb' : (g.1.b : ℚ) = f.1.b * (q00 * q11 + q01 * q10) + 2 * f.1.a * q00 * q01 + 2 * f.1.c * q10 * q11 := by
    linear_combination H1 + H2 - H3
  have hsfq : (f.1.b : ℚ) ^ 2 - 4 * f.1.a * f.1.c = D := by exact_mod_cast hsf
  have hsgq : (g.1.b : ℚ) ^ 2 - 4 * g.1.a * g.1.c = D := by exact_mod_cast hsg
  have hD0q : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
  have hdet2 : (q00 * q11 - q01 * q10) * (q00 * q11 - q01 * q10) = 1 := by
    have h1 : (g.1.b : ℚ) ^ 2 - 4 * g.1.a * g.1.c =
        ((q00 * q11 - q01 * q10) * (q00 * q11 - q01 * q10)) * ((f.1.b : ℚ) ^ 2 - 4 * f.1.a * f.1.c) := by
      rw [hb', ← H1, ← H2]; ring
    rw [hsgq, hsfq] at h1
    refine mul_left_cancel₀ hD0q ?_
    linear_combination (-1 : ℚ) * h1
  obtain ⟨ε, hε, hεq⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (ε : ℚ) = q00 * q11 - q01 * q10 := by
    rcases mul_self_eq_one_iff.1 hdet2 with h1 | h1
    · exact ⟨1, Or.inl rfl, by rw [h1]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h1]; simp⟩
  set N : ℕ := q00.den * q01.den * q10.den * q11.den with hN
  have hN0 : N ≠ 0 := by
    simp only [hN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero q00.den_nz q01.den_nz) q10.den_nz) q11.den_nz
  obtain ⟨X, hX⟩ := exists_int_mul (q := q00) (N := N) ⟨q01.den * q10.den * q11.den, by rw [hN]; ring⟩
  obtain ⟨X', hX'⟩ := exists_int_mul (q := q01) (N := N) ⟨q00.den * q10.den * q11.den, by rw [hN]; ring⟩
  obtain ⟨Y, hY⟩ := exists_int_mul (q := q10) (N := N) ⟨q00.den * q01.den * q11.den, by rw [hN]; ring⟩
  obtain ⟨Y', hY'⟩ := exists_int_mul (q := q11) (N := N) ⟨q00.den * q01.den * q10.den, by rw [hN]; ring⟩
  refine ⟨(N : ℤ), X, Y, X', Y', ε, by exact_mod_cast hN0, ?_, hε, ?_, ?_, ?_, ?_⟩
  · refine isCoprime_of_forall_prime fun p hp hpd hpN => ?_
    have hpN' : p ∣ N := Int.natCast_dvd_natCast.mp hpN
    rw [hN] at hpN'
    rcases (Nat.Prime.dvd_mul hp).mp hpN' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · exact hd00 p hp hpd h3
        · exact hd01 p hp hpd h3
      · exact hd10 p hp hpd h2
    · exact hd11 p hp hpd h1
  · apply Int.cast_injective (α := ℚ)
    push_cast at hX hX' hY hY' ⊢
    rw [hX, hX', hY, hY']
    linear_combination (-(N : ℚ) ^ 2) * hεq
  · apply Int.cast_injective (α := ℚ)
    rw [eval_eq]
    push_cast at hX hY ⊢
    rw [hX, hY]
    linear_combination ((N : ℚ) ^ 2) * H1
  · apply Int.cast_injective (α := ℚ)
    rw [eval_eq]
    push_cast at hX' hY' ⊢
    rw [hX', hY']
    linear_combination ((N : ℚ) ^ 2) * H2
  · apply Int.cast_injective (α := ℚ)
    rw [eval_eq]
    push_cast at hX hX' hY hY' ⊢
    rw [hX, hX', hY, hY']
    linear_combination ((N : ℚ) ^ 2) * H3

/-- **Classes in one genus differ by a square** (Cassels, Ch. 14, Corollary to Theorem 3.1, p. 339,
"genera $\Rightarrow$ cosets"). -/
theorem exists_sq_of_sameGenus (f g : PrimForm D) (h : SameGenus f.1 g.1) :
    ∃ S : FormClass D, mk f = mk g * S ^ 2 := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  obtain ⟨d, X, Y, X', Y', ε, hd, hdD, hε, hdet, hA, hC, hP⟩ := extract f g h
  obtain ⟨g', hg', hga⟩ := exists_rep_coprime (mk g) (M := 2 * D * d)
    (mul_ne_zero (mul_ne_zero two_ne_zero hD0) hd)
  have haD : IsCoprime g'.1.a (2 * D) := hga.of_isCoprime_of_dvd_right ⟨d, by ring⟩
  have had : IsCoprime g'.1.a d := hga.of_isCoprime_of_dvd_right ⟨2 * D, by ring⟩
  obtain ⟨p, q, r, s, hps, hsub⟩ := (sLEquiv_iff _ _).1 (mk_eq_mk.1 hg'.symm)
  have ea : g'.1.a = g.1.a * p ^ 2 + g.1.b * p * r + g.1.c * r ^ 2 := by rw [← hsub]; simp [subst]
  have eb : g'.1.b = 2 * g.1.a * p * q + g.1.b * (p * s + q * r) + 2 * g.1.c * r * s := by
    rw [← hsub]; simp [subst]
  have ec : g'.1.c = g.1.a * q ^ 2 + g.1.b * q * s + g.1.c * s ^ 2 := by rw [← hsub]; simp [subst]
  rw [eval_eq] at hA hC hP
  have hdisc2 : g'.1.b ^ 2 - 4 * g'.1.a * g'.1.c = D := g'.2.2
  obtain ⟨w, B, C, hw, haw, hf, hdisc, hdvd⟩ := core (f1 := f.1) (D := D) f.2.2 (a := g'.1.a) (b := g'.1.b)
    (c2 := g'.1.c) (d := d) (X := p * X + r * X') (Y := p * Y + r * Y') (X' := q * X + s * X')
    (Y' := q * Y + s * Y') (ε := ε) hdisc2 hd hdD haD had hε
    (by linear_combination (X * Y' - X' * Y) * hps + hdet)
    (by rw [eval_eq, ea]; linear_combination (p ^ 2 - p * r) * hA + (r ^ 2 - p * r) * hC + p * r * hP)
    (by rw [eval_eq, ec]; linear_combination (q ^ 2 - q * s) * hA + (s ^ 2 - q * s) * hC + q * s * hP)
    (by
      rw [eval_eq, ea, eb, ec]
      linear_combination ((p + q) ^ 2 - (p + q) * (r + s)) * hA + ((r + s) ^ 2 - (p + q) * (r + s)) * hC +
        (p + q) * (r + s) * hP)
  obtain ⟨T, hT⟩ := finish f g' hw haD haw hε hf hdisc hdvd
  exact ⟨T, by rw [hT, hg']⟩

/-- **Cassels, Ch. 14, Corollary to Theorem 3.1** (p. 339): *the genera are precisely the cosets of $\mathcal G$
modulo $\mathcal G^2$.* Two primitive forms $f, g$ of discriminant $D$ are in the same genus (equivalent over every
$\mathbb Z_p$ and over $\mathbb R$) if and only if their classes satisfy $\mathfrak C_f = \mathfrak C_g\,\mathfrak S^2$
for some class $\mathfrak S$. For every discriminant $D \ne 0$; for $g$ the principal form this is Theorem 3.1. -/
@[kb "cassels1978" "Ch. 14, Cor. to Thm. 3.1, p. 339 (the genera are the cosets of 𝒢 modulo 𝒢²)"]
theorem sameGenus_iff_exists_sq (f g : PrimForm D) :
    SameGenus f.1 g.1 ↔ ∃ S : FormClass D, mk f = mk g * S ^ 2 :=
  ⟨exists_sq_of_sameGenus f g, fun ⟨S, h⟩ => sameGenus_of_mk_eq_mul_sq f g S h⟩

/-- **The classes of a genus**: the set of classes $\mathfrak C \in \mathcal G$ whose forms are in the genus of the
primitive form $f$ (equivalent to $f$ over every $\mathbb Z_p$ and over $\mathbb R$). Being in the genus of $f$ is a
class invariant (`IntEquiv.sameGenus`), so this is the set of classes of the forms in the genus of $f$. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (the classes of a genus)"]
def genusClasses (f : PrimForm D) : Set (FormClass D) := {C | ∃ g : PrimForm D, mk g = C ∧ SameGenus g.1 f.1}

/-- **The genus of $f$ is the coset $\mathfrak C_f\,\mathcal G^2$** (Cassels, Ch. 14, Corollary to Theorem 3.1,
p. 339). -/
@[kb "cassels1978" "Ch. 14, Cor. to Thm. 3.1, p. 339"]
theorem genusClasses_eq (f : PrimForm D) : genusClasses f = {C | ∃ S : FormClass D, C = mk f * S ^ 2} := by
  ext C
  constructor
  · rintro ⟨g, rfl, hg⟩
    exact (sameGenus_iff_exists_sq g f).1 hg
  · rintro ⟨S, rfl⟩
    obtain ⟨g, hg⟩ := mk_surjective (mk f * S ^ 2)
    exact ⟨g, hg, sameGenus_of_mk_eq_mul_sq g f S hg⟩

/-- The coset $x\,\mathcal G^2$ as a subgroup-membership condition (helper). -/
private theorem exists_sq_iff_mem (x C : FormClass D) :
    (∃ S : FormClass D, C = x * S ^ 2) ↔ x⁻¹ * C ∈ (powMonoidHom 2 : FormClass D →* FormClass D).range := by
  constructor
  · rintro ⟨S, rfl⟩
    exact MonoidHom.mem_range.2 ⟨S, by rw [powMonoidHom_apply, inv_mul_cancel_left]⟩
  · intro hS
    obtain ⟨S, hS⟩ := MonoidHom.mem_range.1 hS
    rw [powMonoidHom_apply] at hS
    exact ⟨S, by rw [hS, mul_inv_cancel_left]⟩

/-- **Any two genera contain the same number of classes** (Cassels, Ch. 14, Corollary to Theorem 3.1, p. 339): the
number of classes in the genus of $f$ is the order of the subgroup $\mathcal G^2$ of squares, for every primitive
form $f$ of discriminant $D$. -/
@[kb "cassels1978" "Ch. 14, Cor. to Thm. 3.1, p. 339 (any two genera contain the same number of classes)"]
theorem card_genusClasses (f : PrimForm D) :
    Nat.card (genusClasses f) = Nat.card (powMonoidHom 2 : FormClass D →* FormClass D).range := by
  rw [genusClasses_eq]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun C => C ∈ {C : FormClass D | ∃ S : FormClass D, C = mk f * S ^ 2})
    (q := fun C => C ∈ (powMonoidHom 2 : FormClass D →* FormClass D).range) (Equiv.mulLeft (mk f)⁻¹)
    (fun C => exists_sq_iff_mem (mk f) C))

/-- **Any two genera contain the same number of classes** (Cassels, Ch. 14, Corollary to Theorem 3.1, p. 339). -/
@[kb "cassels1978" "Ch. 14, Cor. to Thm. 3.1, p. 339 (any two genera contain the same number of classes)"]
theorem card_genusClasses_eq (f g : PrimForm D) : Nat.card (genusClasses f) = Nat.card (genusClasses g) := by
  rw [card_genusClasses, card_genusClasses]

/-- **The number of genera is the order of the group $\mathcal A$ of ambiguous classes** (Cassels, Ch. 14, §1,
p. 333 (14.r3), and proof of Theorem 5.1, p. 343: "the order of $\mathcal G/\mathcal G^2$ is equal to the order of the
kernel of the map $\mathfrak C \to \mathfrak C^2$"). The genera are counted as the distinct sets `genusClasses f`. For
every discriminant $D \ne 0$. -/
@[kb "cassels1978" "Ch. 14, §1, p. 333; proof of Thm. 5.1, p. 343 (the number of genera is the order of 𝒜)"]
theorem card_genera :
    Nat.card (Set.range (genusClasses : PrimForm D → Set (FormClass D))) = Nat.card (ambiguousSubgroup (D := D)) := by
  set H : Subgroup (FormClass D) := (powMonoidHom 2 : FormClass D →* FormClass D).range with hH
  let Φ : FormClass D → Set (FormClass D) := fun C => {x | ∃ S : FormClass D, x = C * S ^ 2}
  have hrange : Set.range (genusClasses : PrimForm D → Set (FormClass D)) = Set.range Φ := by
    ext s
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨mk f, (genusClasses_eq f).symm⟩
    · rintro ⟨C, rfl⟩
      obtain ⟨f, rfl⟩ := mk_surjective C
      exact ⟨f, genusClasses_eq f⟩
  have hker : Setoid.ker Φ = QuotientGroup.leftRel H := by
    ext x y
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply]
    constructor
    · intro hxy
      have hy : y ∈ Φ y := ⟨1, by rw [one_pow, mul_one]⟩
      rw [← hxy] at hy
      exact (exists_sq_iff_mem x y).1 hy
    · intro hxy
      ext z
      show (∃ S : FormClass D, z = x * S ^ 2) ↔ (∃ S : FormClass D, z = y * S ^ 2)
      rw [exists_sq_iff_mem, exists_sq_iff_mem]
      constructor
      · intro h
        have := H.mul_mem (H.inv_mem hxy) h
        rwa [show (x⁻¹ * y)⁻¹ * (x⁻¹ * z) = y⁻¹ * z by group] at this
      · intro h
        have := H.mul_mem hxy h
        rwa [show x⁻¹ * y * (y⁻¹ * z) = x⁻¹ * z by group] at this
  have e : Quotient (QuotientGroup.leftRel H) ≃ Set.range Φ := by
    rw [← hker]; exact Setoid.quotientKerEquivRange Φ
  have h1 : Nat.card (Set.range Φ) = H.index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr e).symm
  have hfin : 0 < Nat.card H := Nat.card_pos
  have h2 := Subgroup.card_mul_index H
  have h3 := Subgroup.card_ker_mul_card_range (powMonoidHom 2 : FormClass D →* FormClass D)
  rw [hrange, h1]
  have h4 : Nat.card (ambiguousSubgroup (D := D)) * Nat.card H = Nat.card H * H.index := by
    rw [h2, ← h3]; rfl
  rw [mul_comm] at h4
  exact (Nat.eq_of_mul_eq_mul_left hfin h4).symm

end QuadFormsKB.Composition
