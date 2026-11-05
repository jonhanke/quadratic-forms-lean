/-
# Conway–Sloane, Ch. 15, §3.5: Estes–Pall, the "only if" direction

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.5, p. 366
(`conwaysloane1999`), citing D. R. Estes and G. Pall, *Spinor genera of binary quadratic forms*, J. Number Theory **5**
(1973), 421–432: *two forms are in the same spinor genus if and only if their quotient is a fourth power in the group*.
Read with the proper spinor genus (`SameProperSpinorGenusForm`, `Section3EstesPall.lean`). The "if" direction is
`sameProperSpinorGenusForm_of_fourth` (`Section3EstesPallIf.lean`).

**Proves**
* `exists_reps_of_sq`: representatives for a square quotient (Cassels, Ch. 14, Lemma 2.5 with $n = 2$ and composition);
* `fourth_of_sameProperSpinorGenusForm` (**the "only if" direction, unconditional**): if $g$ is in the proper spinor
  genus of $f$ (primitive, discriminant $D \ne 0$), then $[g] = [f]\,\mathfrak S^4$;
* `estesPallOnlyIfStatement` and `estesPallStatement` (**Estes–Pall, both directions, unconditional**).

**Proof of the "only if" direction** (the idelic argument of Estes–Pall, carried out with lattices; no ideals of the
quadratic order are needed).
1. $M = \gamma\mathbb Z^2 \in \operatorname{spn}^+(L)$, $L = \mathbb Z^2$ in $(\mathbb Q^2, f)$, so $M = \sigma\Sigma L$
   with $\sigma \in O^+(V)$ and $\Sigma$ in the adelic spinor kernel (O'Meara §102A, `sameProperSpinorGenus_iff`).
2. *Square roots.* Every $\Sigma_p$ is a square $\kappa_p^2$ of a rotation (Hilbert's Theorem 90 for the binary space,
   `exists_sq_eq_of_spinorNorm_eq_one`), with $\kappa_p \in O^+(L_p)$ whenever $\Sigma_p \in O^+(L_p)$ and $p \nmid 2D$
   (`exists_sq_eq_stdStab`); so $\kappa$ is adelic and $M = \sigma\kappa^2 L$.
3. *The lattice $K = \kappa L$* is in the genus of $L$; its proper class is $[f]\mathfrak T^2$ (Cassels' genus theorem).
   Representatives (`exists_reps_of_sq`): $f \sim f' = [a, B, Cw^4]$ (via $P$), $[K] \sim [aw^2, B, Cw^2] =
   f'\circ\Gamma$ with $\Gamma = \operatorname{diag}(w, w^{-1})$. Hence $K = \sigma'P\Gamma L$ for a global rotation
   $\sigma'$.
4. *Squaring.* With $\kappa' = \sigma'^{-1}\kappa$: $\kappa' L = P\Gamma L$, so at every $p$ the squaring lemma
   (`sq_integral_of_integral`) gives $\kappa'^2 L = P\Gamma^2 L$; binary rotations commute (`rot_commute`), so
   $\kappa^2 = \sigma'^2\kappa'^2$ and $M = \sigma\sigma'^2 P\Gamma^2 L$.
5. Therefore $g \sim f'\circ\Gamma^2 = [aw^4, B, C] = [a, B, Cw^4]\circ[w^4, B, aC]$, and $[w^4, B, aC]$ is a fourth
   power (Cassels, Lemma 2.5): $[g] = [f]\,\mathfrak S^4$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section3EstesPallOnlyIfLocal
import QuadFormsKB.Binary.SiegelNonPrimitive
import QuadFormsKB.Literature.Cassels.Ch11Sec3Thm
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.Cassels.Ch11Sec6Subst

open NumberField Matrix IsDedekindDomain

noncomputable section

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.RatBridge QuadFormsKB.Composition BinQF Binary FormClass

set_option linter.unusedSectionVars false

/-- **Representatives for a square quotient** (Cassels, Ch. 14, Lemma 2.5 with $n = 2$, p. 338, and the composition of
concordant forms, as in the proof of the Corollary to Theorem 3.1, p. 339): if $[k] = [f]\,\mathfrak T^2$ then there are
integers $a, B, C, w$ with $w$ prime to $2D$, $a$ prime to $2Dw$, $f \sim [a, B, Cw^4]$ and $[aw^2, B, Cw^2] \sim k$
(proper equivalence). -/
@[kb "cassels1978" "Ch. 14, Lemma 2.5, p. 338 (n = 2), and the proof of the Corollary to Thm. 3.1, p. 339"]
theorem exists_reps_of_sq {D : ℤ} [NonzeroDisc D] (f k : PrimForm D) (T : FormClass D)
    (h : mk k = mk f * T ^ 2) :
    ∃ a B C w : ℤ, IsCoprime w (2 * D) ∧ IsCoprime a (2 * D * w) ∧
      SLEquiv f.1 (BinQF.mk a B (C * w ^ 4)) ∧ SLEquiv (BinQF.mk (a * w ^ 2) B (C * w ^ 2)) k.1 := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  obtain ⟨m0, hm0, w, x, y, hxy, hw, hev⟩ :=
    (exists_pow_eq_iff (D := D) (n := 2) (by norm_num) (T ^ 2)).mp ⟨T, rfl⟩
  obtain ⟨mm, em, hmma⟩ := exists_sLEquiv_a_of_eval (f := m0.1) hxy
  rw [hev] at hmma
  set m : PrimForm D := ofEquiv m0 em with hmdef
  have hmk : mk m = T ^ 2 := by rw [← hm0]; exact mk_eq_mk.2 em.symm
  have hma : m.1.a = w ^ 2 := hmma
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  have hmd : m.1.b ^ 2 - 4 * m.1.a * m.1.c = D := m.2.2
  -- `m.b` is prime to `w`
  have hwD : IsCoprime w D := hw.of_isCoprime_of_dvd_right ⟨2, by ring⟩
  have hbw : IsCoprime m.1.b (w ^ 2) := by
    have h1 : IsCoprime w (m.1.b ^ 2) := by
      have e : m.1.b ^ 2 = D + w * (4 * w * m.1.c) := by linear_combination hmd + 4 * m.1.c * hma
      rw [e]; exact hwD.add_mul_left_right _
    have h2 : IsCoprime w m.1.b := IsCoprime.of_mul_right_left (by rw [← sq]; exact h1)
    exact h2.symm.pow_right
  obtain ⟨u0, v0, huv⟩ := hbw
  rw [hma] at hmd
  -- `m ∼ m1 = [w², B0, w²·c1]`
  obtain ⟨m1, em1, hm1a, hm1b⟩ := exists_sLEquiv_b (f := m.1) (B := m.1.b + 2 * w ^ 2 * (-(m.1.c * u0)))
    ⟨-(m.1.c * u0), by rw [hma]; ring⟩
  have hm1d : m1.disc = D := (SLEquiv.disc_eq em1).symm.trans m.2.2
  have hm1d' : (m.1.b + 2 * w ^ 2 * (-(m.1.c * u0))) ^ 2 - 4 * w ^ 2 * m1.c = D := by
    have : m1.b ^ 2 - 4 * m1.a * m1.c = D := hm1d
    rwa [hm1a, hma, hm1b] at this
  have h4w : 4 * w ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hw0)
  have hm1c : m1.c = w ^ 2 * (m.1.c * v0 + (m.1.c * u0) ^ 2) := by
    have h4 : 4 * w ^ 2 * (m1.c - w ^ 2 * (m.1.c * v0 + (m.1.c * u0) ^ 2)) = 0 := by
      linear_combination hmd - hm1d' - 4 * w ^ 2 * m.1.c * huv
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h4w)
  have hm1d'' : m1.b ^ 2 - 4 * w ^ 2 * m1.c = D := by rw [hm1b]; exact hm1d'
  -- a representative of `[f]` and a common middle coefficient
  obtain ⟨g', hg', hga⟩ := exists_rep_coprime (mk f) (M := 2 * D * w)
    (mul_ne_zero (mul_ne_zero two_ne_zero hD0) hw0)
  have ha0 : g'.1.a ≠ 0 := ne_zero_of_coprime_two_mul (N := D * w) (by rw [← mul_assoc]; exact hga)
  have haw : IsCoprime g'.1.a w := hga.of_isCoprime_of_dvd_right ⟨2 * D, by ring⟩
  have haw4 : IsCoprime g'.1.a (w ^ 4) := haw.pow_right
  have haw2 : IsCoprime g'.1.a (w ^ 2) := haw.pow_right
  obtain ⟨B, hB1, hB2⟩ := exists_common_b (a := g'.1.a) (a' := w ^ 4) (b := g'.1.b) (b' := m1.b) haw4
    (two_dvd_b_sub_b (g'.2.2.trans hm1d.symm))
  obtain ⟨k0, ek, hka, hkb⟩ := exists_sLEquiv_b (f := g'.1) (B := B) hB1
  obtain ⟨B1, hB1'⟩ := hB2
  obtain ⟨m2, em2, hm2a, hm2b⟩ := exists_sLEquiv_b (f := m1) (B := B)
    ⟨w ^ 2 * B1, by rw [hm1a, hma]; linear_combination hB1'⟩
  have hm2d : m2.disc = D := (SLEquiv.disc_eq em2).symm.trans hm1d
  have hm2d' : B ^ 2 - 4 * w ^ 2 * m2.c = D := by
    have : m2.b ^ 2 - 4 * m2.a * m2.c = D := hm2d
    rwa [hm2a, hm1a, hma, hm2b] at this
  set c0 := (m.1.c * v0 + (m.1.c * u0) ^ 2) + B1 * (w ^ 4 * B1 + m1.b) with hc0
  have hm2c : m2.c = w ^ 2 * c0 := by
    have h4 : 4 * w ^ 2 * (m2.c - w ^ 2 * c0) = 0 := by
      rw [hc0]
      linear_combination (-1 : ℤ) * hm2d' + hm1d'' + 4 * w ^ 2 * hm1c + (B + m1.b + 2 * w ^ 4 * B1) * hB1'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h4w)
  -- the concordant pair and its composition
  set K : PrimForm D := ofEquiv g' ek with hK
  set M1 : PrimForm D := ofEquiv m (em1.trans em2) with hM1
  have hKa : K.1.a = g'.1.a := hka
  have hKb : K.1.b = B := hkb
  have hM1a : M1.1.a = w ^ 2 := by rw [hM1]; exact hm2a.trans (hm1a.trans hma)
  have hM1b : M1.1.b = B := hm2b
  have hM1c : M1.1.c = w ^ 2 * c0 := hm2c
  have hc : Concordant K.1 M1.1 := concordant_of_coprime
    (by rw [hKa, hM1a]; exact mul_ne_zero ha0 (pow_ne_zero 2 hw0))
    (hKb.trans hM1b.symm) (K.2.2.trans M1.2.2.symm) (by rw [hKa, hM1a]; exact haw2)
  have hprod := mk_mul_mk K M1 hc
  have hKk : mk K = mk f := (mk_ofEquiv g' ek).trans hg'
  have hM1k : mk M1 = T ^ 2 := (mk_ofEquiv m (em1.trans em2)).trans hmk
  have hkc : mk k = mk (PrimForm.comp K M1 hc) := by rw [← hprod, hKk, hM1k, h]
  have e1 : SLEquiv (PrimForm.comp K M1 hc).1 k.1 := (mk_eq_mk.1 hkc).symm
  have e2 : SLEquiv f.1 K.1 := mk_eq_mk.1 hKk.symm
  set C' := (PrimForm.comp K M1 hc).1.c with hC'
  have hCa : (PrimForm.comp K M1 hc).1.a = g'.1.a * w ^ 2 := by rw [primComp_a, hKa, hM1a]
  have hCb : (PrimForm.comp K M1 hc).1.b = B := by rw [primComp_b, hKb]
  have hCd : B ^ 2 - 4 * (g'.1.a * w ^ 2) * C' = D := by
    have : (PrimForm.comp K M1 hc).1.b ^ 2 - 4 * (PrimForm.comp K M1 hc).1.a * C' = D :=
      (PrimForm.comp K M1 hc).2.2
    rwa [hCa, hCb] at this
  have hKd : B ^ 2 - 4 * g'.1.a * K.1.c = D := by
    have : K.1.b ^ 2 - 4 * K.1.a * K.1.c = D := K.2.2
    rwa [hKa, hKb] at this
  -- `w² ∣ C'`
  have haC : g'.1.a * C' = w ^ 2 * c0 := by
    have h4 : 4 * w ^ 2 * (g'.1.a * C' - w ^ 2 * c0) = 0 := by
      rw [hm2c] at hm2d'; linear_combination hm2d' - hCd
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h4w)
  obtain ⟨C, hC⟩ : w ^ 2 ∣ C' := haw2.symm.dvd_of_dvd_mul_left ⟨c0, haC⟩
  have hKc : K.1.c = C * w ^ 4 := by
    have h4 : 4 * g'.1.a * (K.1.c - C * w ^ 4) = 0 := by
      rw [hC] at hCd; linear_combination hCd - hKd
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (mul_ne_zero (by norm_num) ha0))
  refine ⟨g'.1.a, B, C, w, hw, hga, ?_, ?_⟩
  · have hKe : K.1 = BinQF.mk g'.1.a B (C * w ^ 4) := ext_abc (by simp [hKa]) (by simp [hKb]) (by simp [hKc])
    rw [← hKe]; exact e2
  · have hGe : (PrimForm.comp K M1 hc).1 = BinQF.mk (g'.1.a * w ^ 2) B (C * w ^ 2) :=
      ext_abc (by simp [hCa]) (by simp [hCb]) (by simp [← hC', hC]; ring)
    rw [← hGe]; exact e1

/-! ### The Gram form of a lattice in the genus -/

/-- A binary form over $\mathbb Q$ composed with a linear map is determined by three values. -/
theorem bq_comp_eq_of_three {f g : BinQF} {P : Matrix (Fin 2) (Fin 2) ℚ}
    (E1 : bq f (P *ᵥ ![1, 0]) = bq g ![1, 0]) (E2 : bq f (P *ᵥ ![0, 1]) = bq g ![0, 1])
    (E3 : bq f (P *ᵥ ![1, 1]) = bq g ![1, 1]) (y : Fin 2 → ℚ) : bq f (P *ᵥ y) = bq g y := by
  simp only [bq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at E1 E2 E3 ⊢
  simp only [mul_one, mul_zero, add_zero, zero_add, one_pow, zero_pow two_ne_zero] at E1 E2 E3
  linear_combination y 0 ^ 2 * E1 + y 1 ^ 2 * E2 + y 0 * y 1 * (E3 - E1 - E2)

/-- **The Gram form of $\gamma\mathbb Z^2$**: for an integral lattice $\gamma\mathbb Z^2$ in $(\mathbb Q^2, f)$, the form
$g$ = `down (gramZ _ γ h)` satisfies $g(y) = f(\gamma y)$ for all $y \in \mathbb Q^2$. -/
theorem bq_down_gramZ (f : BinQF) (γ : GL (Fin 2) ℚ) (h : IsIntegral (HilbertModular.formF (up f)) (latOf γ))
    (y : Fin 2 → ℚ) : bq f (γ.val *ᵥ y) = bq (down (gramZ (HilbertModular.formF (up f)) γ h)) y := by
  have key : ∀ x : Fin 2 → 𝓞 ℚ, bq f (γ.val *ᵥ intCoe x) =
      bq (down (gramZ (HilbertModular.formF (up f)) γ h)) (intCoe x) := by
    intro x
    rw [← evalIn_rat_eq_bq (down (gramZ (HilbertModular.formF (up f)) γ h)), evalIn_intCoe_rat, up_down,
      algebraMap_eval_gramZ]
    exact (evalIn_formF_up f ℚ _).symm
  have i10 : intCoe (F := ℚ) ![(1 : 𝓞 ℚ), 0] = ![1, 0] := by ext i; fin_cases i <;> simp [intCoe]
  have i01 : intCoe (F := ℚ) ![(0 : 𝓞 ℚ), 1] = ![0, 1] := by ext i; fin_cases i <;> simp [intCoe]
  have i11 : intCoe (F := ℚ) ![(1 : 𝓞 ℚ), 1] = ![1, 1] := by ext i; fin_cases i <;> simp [intCoe]
  have E1 := key ![1, 0]
  have E2 := key ![0, 1]
  have E3 := key ![1, 1]
  rw [i10] at E1; rw [i01] at E2; rw [i11] at E3
  exact bq_comp_eq_of_three E1 E2 E3 y

/-- The coefficients of $g = f \circ P$ and the discriminant: $\operatorname{disc} g = (\det P)^2\operatorname{disc} f$. -/
theorem disc_of_bq_comp {f g : BinQF} {P : Matrix (Fin 2) (Fin 2) ℚ} (h : ∀ y, bq f (P *ᵥ y) = bq g y) :
    (g.disc : ℚ) = P.det ^ 2 * f.disc := by
  have E1 := h ![1, 0]
  have E2 := h ![0, 1]
  have E3 := h ![1, 1]
  simp only [bq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at E1 E2 E3
  simp only [mul_one, mul_zero, add_zero, zero_add, one_pow, zero_pow two_ne_zero] at E1 E2 E3
  simp only [BinQF.disc, det_fin_two]
  push_cast
  set A1 := (f.a : ℚ) * P 0 0 ^ 2 + f.b * P 0 0 * P 1 0 + f.c * P 1 0 ^ 2
  set B' := (f.a : ℚ) * (P 0 0 + P 0 1) ^ 2 + f.b * (P 0 0 + P 0 1) * (P 1 0 + P 1 1) + f.c * (P 1 0 + P 1 1) ^ 2 -
    A1 - ((f.a : ℚ) * P 0 1 ^ 2 + f.b * P 0 1 * P 1 1 + f.c * P 1 1 ^ 2)
  linear_combination (-((g.b : ℚ) + B')) * (E3 - E1 - E2) + 4 * (g.c : ℚ) * E1 + 4 * A1 * E2

/-- **A form in the genus of a primitive form is primitive** (if a common divisor $d$ of the coefficients of $g$
existed, every value of $f$ would be divisible by $d$, `Binary.dvd_eval_of_sameGenus`). -/
theorem isPrimitive_of_sameGenus {f g : BinQF} (hf : f.IsPrimitive) (hg0 : g.disc ≠ 0) (h : Siegel.SameGenus f g) :
    g.IsPrimitive := by
  intro d ha hb hc
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hg0
    simp only [zero_mul] at ha' hb' hc'
    simp [BinQF.disc, ha', hb', hc']
  have hg : g = d • BinQF.mk a' b' c' := by
    rw [Binary.smul_mk, ← ha', ← hb', ← hc']; exact Binary.binQF_eq_mk g
  have hsg : Siegel.SameGenus (d • BinQF.mk a' b' c') f := by rw [← hg]; exact h.symm
  have hv : ∀ x : Fin 2 → ℤ, d ∣ QuadForm.eval f x := fun x => Binary.dvd_eval_of_sameGenus hd0 hsg x
  have e1 := hv ![1, 0]
  have e2 := hv ![0, 1]
  have e3 := hv ![1, 1]
  simp only [eval_int_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e1 e2 e3
  norm_num at e1 e2 e3
  refine hf d e1 ?_ e2
  have := dvd_sub (dvd_sub e3 e1) e2
  rwa [show f.a + f.b + f.c - f.a - f.c = f.b by ring] at this

/-- **An oriented basis of $\kappa\mathbb Z^2$**: for an adelic isometry $\kappa$ of $(\mathbb Q^2, f)$, the lattice
$K = \kappa\mathbb Z^2$ is $\gamma\mathbb Z^2$ with $\det\gamma = 1$, and its Gram form $g$ ($g(y) = f(\gamma y)$) is a
primitive form of discriminant $D$ in the genus of $f$. -/
theorem exists_oriented_basis {D : ℤ} [NonzeroDisc D] (f : PrimForm D)
    (κ : OAf (HilbertModular.formF (up f.1))) :
    ∃ (γ : GL (Fin 2) ℚ) (g : PrimForm D), γ.val.det = 1 ∧
      (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat).1 = latOf γ ∧
      (∀ y, bq f.1 (γ.val *ᵥ y) = bq g.1 y) ∧ Siegel.SameGenus f.1 g.1 := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  have hK : Lattices.SameGenus (HilbertModular.formF (up f.1)) intVec (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat).1 :=
    Lattices.sameGenus_latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat
  obtain ⟨γ0, hγ0, hint0⟩ := exists_free_of_sameGenus f.1 (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat) hK
  have facts : ∀ γ : GL (Fin 2) ℚ, (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat).1 = latOf γ → ∃ h : IsIntegral (HilbertModular.formF (up f.1)) (latOf γ),
      (∀ y, bq f.1 (γ.val *ᵥ y) = bq (down (gramZ (HilbertModular.formF (up f.1)) γ h)) y) ∧ Siegel.SameGenus f.1 (down (gramZ (HilbertModular.formF (up f.1)) γ h)) ∧
        (BinQF.disc (down (gramZ (HilbertModular.formF (up f.1)) γ h)) : ℚ) = γ.val.det ^ 2 * D := by
    intro γ hγ
    have h : IsIntegral (HilbertModular.formF (up f.1)) (latOf γ) := by rw [← hγ, hγ0]; exact hint0
    have hbq := bq_down_gramZ f.1 γ h
    refine ⟨h, hbq, sameGenus_down_gramZ f.1 γ (by rw [← hγ]; exact hK) h, ?_⟩
    rw [disc_of_bq_comp hbq, f.2.2]
  obtain ⟨h0, -, hsg0, hd0⟩ := facts γ0 hγ0
  have hdisc : BinQF.disc (down (gramZ (HilbertModular.formF (up f.1)) γ0 h0)) = D := by
    have e := Siegel.SameGenus.hessian_det_eq hsg0
    rw [hessian_det_binQF, hessian_det_binQF, f.2.2] at e
    linarith
  have hdet2 : γ0.val.det ^ 2 = 1 := by
    rw [hdisc] at hd0
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    have : (γ0.val.det ^ 2 - 1) * D = 0 := by linear_combination -hd0
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hDq)
  -- choose the orientation
  obtain ⟨γ, hγdet, hγK⟩ : ∃ γ : GL (Fin 2) ℚ, γ.val.det = 1 ∧ (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat).1 = latOf γ := by
    have : (γ0.val.det - 1) * (γ0.val.det + 1) = 0 := by linear_combination hdet2
    rcases mul_eq_zero.mp this with h1 | h1
    · exact ⟨γ0, sub_eq_zero.mp h1, hγ0⟩
    · let T : GL (Fin 2) ℚ := ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by simp [Matrix.one_fin_two], by
        simp [Matrix.one_fin_two]⟩
      have hT : glImage T intVec = intVec := by
        have hint : ∀ i j, T.val i j ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
          intro i j
          fin_cases i <;> fin_cases j
          · exact ⟨1, by simp [T]⟩
          · exact ⟨0, by simp [T]⟩
          · exact ⟨0, by simp [T]⟩
          · exact ⟨-1, by simp [T]⟩
        exact Tamagawa.BinaryNormOne.glImage_intVec_eq hint hint
      refine ⟨γ0 * T, ?_, ?_⟩
      · rw [Units.val_mul, det_mul, show γ0.val.det = -1 by linear_combination h1]
        simp [T, det_fin_two]
      · rw [hγ0, latOf, latOf, glImage_mul, hT]
  obtain ⟨h, hbq, hsg, hd⟩ := facts γ hγK
  have hdisc' : BinQF.disc (down (gramZ (HilbertModular.formF (up f.1)) γ h)) = D := by
    rw [hγdet, one_pow, one_mul] at hd; exact_mod_cast hd
  refine ⟨γ, ⟨down (gramZ (HilbertModular.formF (up f.1)) γ h), isPrimitive_of_sameGenus f.2.1 (by rw [hdisc']; exact hD0) hsg, hdisc'⟩,
    hγdet, hγK, hbq, hsg⟩

/-! ### Square roots of an adelic spinor-kernel element -/

theorem nondeg_formF {f : BinQF} (hf : f.disc ≠ 0) : (HilbertModular.formF (up f)).Nondegenerate := by
  have hQeq : HilbertModular.formF (up f) = f.map (Int.castRingHom ℚ) := by
    ext i j; simp [QuadForm.map]
  unfold QuadForm.Nondegenerate
  have hm := RingHom.map_det (Int.castRingHom ℚ) f.hessian
  rw [RingHom.mapMatrix_apply] at hm
  rw [hQeq, QuadForm.hessian_map, ← hm, hessian_det_binQF]
  simpa using hf

section Adelic

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Square roots of an adelic spinor-kernel element**: for $k$ in the adelic spinor kernel of $(\mathbb Q^2, f)$ there
is an adelic $\kappa$ with rotation components and $\kappa^2 = k$. (At almost all $v$ both $k_v \in O^+(\mathbb Z_v^2)$
and $v \nmid 2D$, and there the square root is integral, `exists_sq_eq_stdStab`.) -/
theorem exists_adelic_sqrt {f : BinQF} (hf : f.disc ≠ 0) (k : OAf (HilbertModular.formF (up f)))
    (hk : k ∈ spinorKernelAf (HilbertModular.formF (up f))) :
    ∃ κ : OAf (HilbertModular.formF (up f)),
      (∀ v, κ v ∈ Tamagawa.soSub (HilbertModular.formF (up f)) (v.adicCompletion ℚ)) ∧ κ * κ = k := by
  have hQ := nondeg_formF hf
  have hroot : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ κv : orthGroup (HilbertModular.formF (up f)) (v.adicCompletion ℚ),
      κv ∈ Tamagawa.soSub (HilbertModular.formF (up f)) (v.adicCompletion ℚ) ∧ κv * κv = k v ∧
      (k v ∈ stdStab (HilbertModular.formF (up f)) v → ((2 * f.disc : ℤ) : 𝓞 ℚ) ∉ v.asIdeal →
        κv ∈ stdStab (HilbertModular.formF (up f)) v) := by
    intro v
    have hkv := (mem_spinorKernelAf _).mp hk v
    rw [spinorKernel_eq_ker _ _ hQ, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
      spinorNormHom_apply] at hkv
    have hrot : k v ∈ Tamagawa.soSub (HilbertModular.formF (up f)) (v.adicCompletion ℚ) := by
      rw [Tamagawa.mem_soSub]
      have := hkv.2
      rw [← Units.val_eq_one, detHom_val] at this
      exact this
    by_cases hgood : k v ∈ stdStab (HilbertModular.formF (up f)) v ∧ ((2 * f.disc : ℤ) : 𝓞 ℚ) ∉ v.asIdeal
    · obtain ⟨κv, hκL, hκS, hκ⟩ := exists_sq_eq_stdStab f hQ hgood.2 (k v) hgood.1 hrot hkv.1
      exact ⟨κv, hκS, hκ, fun _ _ => hκL⟩
    · obtain ⟨κv, hκS, hκ⟩ := exists_sq_eq_of_spinorNorm_eq_one _ _ hQ (k v) hrot hkv.1
      exact ⟨κv, hκS, hκ, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩
  choose κv hκS hκsq hκL using hroot
  have h2D : ((2 * f.disc : ℤ) : 𝓞 ℚ) ≠ 0 := by
    have : (2 * f.disc : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hf
    exact_mod_cast this
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, κv v ∈ stdStab (HilbertModular.formF (up f)) v := by
    filter_upwards [k.2, Lattices.eventually_not_mem h2D] with v hv h2v
    exact hκL v hv h2v
  refine ⟨⟨κv, hev⟩, hκS, ?_⟩
  ext v : 1
  exact hκsq v

theorem bq_gamGL {L : Type*} [Field L] {a B C w : ℤ} (hw : (w : L) ≠ 0) (y : Fin 2 → L) :
    bq (BinQF.mk a B (C * w ^ 4)) ((gamGL (w : L) hw).val *ᵥ y) = bq (BinQF.mk (a * w ^ 2) B (C * w ^ 2)) y := by
  simp only [bq, gamGL, a_mk, b_mk, c_mk, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  field_simp
  ring

theorem bq_gamGL_sq {L : Type*} [Field L] {a B C w : ℤ} (hw : (w : L) ≠ 0) (y : Fin 2 → L) :
    bq (BinQF.mk a B (C * w ^ 4)) ((gamGL ((w : L) ^ 2) (pow_ne_zero 2 hw)).val *ᵥ y) =
      bq (BinQF.mk (a * w ^ 4) B C) y := bq_gammaW hw y

/-- Integer values of a binary form through `bq`. -/
theorem eval_cast_eq_bq (h : BinQF) (z : Fin 2 → ℤ) :
    ((QuadForm.eval h z : ℤ) : ℚ) = bq h (fun i => (z i : ℚ)) := by
  rw [eval_int_eq]; simp only [bq]; push_cast; ring

theorem mulVec_cast (U : Matrix (Fin 2) (Fin 2) ℤ) (z : Fin 2 → ℤ) :
    (U.map (Int.castRingHom ℚ)) *ᵥ (fun i => (z i : ℚ)) = fun i => ((U *ᵥ z) i : ℚ) := by
  ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det_map_int (L : Type*) [Field L] (P : GL (Fin 2) ℤ) :
    (GeneralLinearGroup.map (Int.castRingHom L) P).val.det = ((P.val.det : ℤ) : L) :=
  (RingHom.map_det (Int.castRingHom L) P.val).symm

theorem det_gamGL {L : Type*} [Field L] (w : L) (hw : w ≠ 0) : (gamGL w hw).val.det = 1 := by
  simp [gamGL, det_fin_two, hw]

theorem glImage_map_int (P : GL (Fin 2) ℤ) :
    glImage (GeneralLinearGroup.map (Int.castRingHom ℚ) P) (intVec : Submodule (𝓞 ℚ) (Fin 2 → ℚ)) = intVec := by
  have hint : ∀ (M : GL (Fin 2) ℤ) (i j : Fin 2),
      (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val i j ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
    intro M i j
    refine ⟨((M.val i j : ℤ) : 𝓞 ℚ), ?_⟩
    simp [GeneralLinearGroup.map]
  refine Tamagawa.BinaryNormOne.glImage_intVec_eq (hint P) ?_
  rw [← map_inv]; exact hint P⁻¹

theorem map_P_gam (v : HeightOneSpectrum (𝓞 ℚ)) (P : GL (Fin 2) ℤ) {x : ℚ} (hx : x ≠ 0)
    (hx' : algebraMap ℚ (v.adicCompletion ℚ) x ≠ 0) :
    GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) (GeneralLinearGroup.map (Int.castRingHom ℚ) P * gamGL x hx) =
      GeneralLinearGroup.map (Int.castRingHom (v.adicCompletion ℚ)) P * gamGL (algebraMap ℚ (v.adicCompletion ℚ) x) hx' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gamGL, Matrix.mul_apply, Fin.sum_univ_two, GeneralLinearGroup.map]

theorem gamGL_congr {L : Type*} [Field L] {x y : L} (hxy : x = y) (hx : x ≠ 0) (hy : y ≠ 0) :
    gamGL x hx = gamGL y hy := by subst hxy; rfl

end Adelic

section Main

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Estes–Pall, the "only if" direction** (Conway–Sloane, Ch. 15, §3.5, p. 366, proper reading; unconditional): for
primitive forms $f, g$ of discriminant $D \ne 0$, if $g$ is in the proper spinor genus of $f$ then
$[g] = [f]\,\mathfrak S^4$ for a class $\mathfrak S$ of Cassels' group $\mathcal G$. (No hypothesis that $D$ is a
nonsquare is needed.) -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, 'only if': same proper spinor genus gives a fourth-power quotient)"]
theorem fourth_of_sameProperSpinorGenusForm {D : ℤ} [NonzeroDisc D] (f g : PrimForm D)
    (h : SameProperSpinorGenusForm f.1 g.1) : ∃ S : FormClass D, mk g = mk f * S ^ 4 := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  have hfD : f.1.disc ≠ 0 := by rw [f.2.2]; exact hD0
  have hQ := nondeg_formF hfD
  obtain ⟨γ, hγdet, hform, hspn⟩ := h
  obtain ⟨σ0, hσ0, k, hk, hM⟩ := (sameProperSpinorGenus_iff (HilbertModular.formF (up f.1))).mp hspn
  obtain ⟨κ, hκrot, hκk⟩ := exists_adelic_sqrt hfD k hk
  obtain ⟨γK, gK, hγKdet, hKlat, hbqK, hsgK⟩ := exists_oriented_basis f κ
  obtain ⟨T, hT⟩ := exists_sq_of_sameGenus gK f hsgK.symm
  obtain ⟨a, B, C, w, hw, ha, ef, eg⟩ := exists_reps_of_sq f gK T hT
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  have hwq : (w : ℚ) ≠ 0 := by exact_mod_cast hw0
  have hf'd : (BinQF.mk a B (C * w ^ 4)).disc = D := (SLEquiv.disc_eq ef).symm.trans f.2.2
  have hf'd' : B ^ 2 - 4 * a * (C * w ^ 4) = D := by simpa [BinQF.disc] using hf'd
  have hcop : IsCoprime a B := by
    have haD : IsCoprime a D := ha.of_isCoprime_of_dvd_right ⟨2 * w, by ring⟩
    have h1 : IsCoprime a (B ^ 2) := by
      have e : B ^ 2 = D + a * (4 * C * w ^ 4) := by linear_combination hf'd'
      rw [e]; exact haD.add_mul_left_right _
    exact IsCoprime.of_mul_right_left (by rw [← sq]; exact h1)
  obtain ⟨P, hPdet, hP⟩ := ef
  obtain ⟨R, hRdet, hR⟩ := eg
  set Pg : GL (Fin 2) ℚ := GeneralLinearGroup.map (Int.castRingHom ℚ) P with hPg
  set Rg : GL (Fin 2) ℚ := GeneralLinearGroup.map (Int.castRingHom ℚ) R with hRg
  set Γg := gamGL (w : ℚ) hwq with hΓg
  have hPval : Pg.val = P.val.map (Int.cast : ℤ → ℚ) := rfl
  have hRval : Rg.val = R.val.map (Int.cast : ℤ → ℚ) := rfl
  have hdetP : Pg.val.det = 1 := by rw [hPg, det_map_int, hPdet]; simp
  have hdetR : Rg.val.det = 1 := by rw [hRg, det_map_int, hRdet]; simp
  have hdetΓ : Γg.val.det = 1 := det_gamGL _ _
  set δ := Pg * Γg * Rg with hδ
  have hdetδ : δ.val.det = 1 := by
    rw [hδ, Units.val_mul, Units.val_mul, det_mul, det_mul, hdetP, hdetΓ, hdetR]; ring
  -- the values of `f` on `δ`
  have hval : ∀ y, bq f.1 (δ.val *ᵥ y) = bq gK.1 y := by
    intro y
    rw [hδ, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hPval, bq_mulVec_of_int hP,
      bq_gamGL hwq, hRval, bq_mulVec_of_int hR]
  -- the global rotation `σ' = γ_K δ⁻¹`
  have hσ'mem : γK * δ⁻¹ ∈ orthGroup (HilbertModular.formF (up f.1)) ℚ := by
    refine mem_orthGroup_of_evalIn _ fun z => ?_
    rw [evalIn_formF_up, evalIn_formF_up, Units.val_mul, ← mulVec_mulVec, hbqK, ← hval, mulVec_inv_mulVec]
  set σ' : orthGroup (HilbertModular.formF (up f.1)) ℚ := ⟨γK * δ⁻¹, hσ'mem⟩ with hσ'
  have hσ'S : σ' ∈ Tamagawa.soSub (HilbertModular.formF (up f.1)) ℚ := by
    show (γK * δ⁻¹).val.det = 1
    have e : δ.val.det * δ⁻¹.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    rw [hdetδ, one_mul] at e
    rw [Units.val_mul, det_mul, hγKdet, e, one_mul]
  -- `κ' = σ'⁻¹κ` maps `ℤ²` to `PΓℤ²`
  set κ' : OAf (HilbertModular.formF (up f.1)) := (diagF (HilbertModular.formF (up f.1)) σ')⁻¹ * κ with hκ'
  have hκ'L : latSMul (HilbertModular.formF (up f.1)) κ' Lattices.stdLat = Lat.image (Pg * Γg) Lattices.stdLat := by
    let _ := latAction (HilbertModular.formF (up f.1))
    have e1 : latSMul (HilbertModular.formF (up f.1)) κ' Lattices.stdLat = latSMul (HilbertModular.formF (up f.1)) (diagF (HilbertModular.formF (up f.1)) σ'⁻¹) (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat) := by
      rw [hκ', ← map_inv]; exact mul_smul (diagF (HilbertModular.formF (up f.1)) σ'⁻¹) κ Lattices.stdLat
    rw [e1, diagF_smul]
    apply Subtype.ext
    show glImage ((σ'⁻¹ : orthGroup (HilbertModular.formF (up f.1)) ℚ) : GL (Fin 2) ℚ) (latSMul (HilbertModular.formF (up f.1)) κ Lattices.stdLat).1 =
      glImage (Pg * Γg) intVec
    rw [hKlat, latOf, ← glImage_mul]
    have e2 : ((σ'⁻¹ : orthGroup (HilbertModular.formF (up f.1)) ℚ) : GL (Fin 2) ℚ) * γK = Pg * Γg * Rg := by
      rw [Subgroup.coe_inv, hσ']; simp [hδ]
    rw [e2, glImage_mul, glImage_map_int]
  -- the components of `κ'` are rotations
  have hκ'S : ∀ v, κ' v ∈ Tamagawa.soSub (HilbertModular.formF (up f.1)) (v.adicCompletion ℚ) := by
    intro v
    have e : κ' v = (orthMap (HilbertModular.formF (up f.1)) (v.adicCompletion ℚ) σ')⁻¹ * κ v := rfl
    rw [e]
    exact (Tamagawa.soSub _ _).mul_mem ((Tamagawa.soSub _ _).inv_mem (orthMap_mem_soSub _ _ hσ'S)) (hκrot v)
  -- squaring at every prime: `κ'²ℤ² = PΓ²ℤ²`
  have hf'nd : (HilbertModular.formF (up (BinQF.mk a B (C * w ^ 4)))).Nondegenerate :=
    nondeg_formF (by rw [hf'd]; exact hD0)
  have hκ'2 : latSMul (HilbertModular.formF (up f.1)) (κ' * κ') Lattices.stdLat =
      Lat.image (Pg * gamGL ((w : ℚ) ^ 2) (pow_ne_zero 2 hwq)) Lattices.stdLat := by
    apply Subtype.ext
    refine loc_injective (latSMul _ _ _).2 (Lat.image _ _).2 fun v => ?_
    have hwv : ((w : ℤ) : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hw0
    have hL0 := congrArg (fun L : Lat ℚ 2 => loc v L.1) hκ'L
    simp only [loc_latSMul, Lat.image, loc_glImage] at hL0
    rw [show loc v (Lattices.stdLat : Lat ℚ 2).1 = std v from loc_intVec v] at hL0
    rw [map_P_gam v P hwq (by simpa using hwv), gamGL_congr (by simp) _ hwv] at hL0
    have hsq := sq_locAct_eq f.1 hwv hcop hf'nd P hPdet hP (κ' v) (hκ'S v) hL0
    rw [loc_latSMul, Lat.image, loc_glImage, show loc v (Lattices.stdLat : Lat ℚ 2).1 = std v from loc_intVec v]
    rw [map_P_gam v P (pow_ne_zero 2 hwq) (by simpa using pow_ne_zero 2 hwv),
      gamGL_congr (by simp) _ (pow_ne_zero 2 hwv)]
    exact hsq
  -- `κ² = σ'²κ'²` (binary rotations commute)
  have hcomm : κ' * diagF (HilbertModular.formF (up f.1)) σ' = diagF (HilbertModular.formF (up f.1)) σ' * κ' := by
    ext v : 1
    exact rot_commute _ _ hQ (hκ'S v) (orthMap_mem_soSub _ _ hσ'S)
  have hkk : k = diagF (HilbertModular.formF (up f.1)) (σ' * σ') * (κ' * κ') := by
    have hκeq : κ = diagF (HilbertModular.formF (up f.1)) σ' * κ' := by rw [hκ', mul_inv_cancel_left]
    rw [← hκk, hκeq, map_mul]
    calc diagF (HilbertModular.formF (up f.1)) σ' * κ' * (diagF (HilbertModular.formF (up f.1)) σ' * κ')
        = diagF (HilbertModular.formF (up f.1)) σ' * (κ' * diagF (HilbertModular.formF (up f.1)) σ') * κ' := by
          simp only [mul_assoc]
      _ = _ := by rw [hcomm]; simp only [mul_assoc]
  -- the lattice `M = τPΓ²ℤ²`
  set τ := σ0 * (σ' * σ') with hτ
  set Δ : GL (Fin 2) ℚ := (τ : GL (Fin 2) ℚ) * (Pg * gamGL ((w : ℚ) ^ 2) (pow_ne_zero 2 hwq)) with hΔ
  have hMlat : latOf γ = latOf Δ := by
    have e := congrArg Subtype.val hM
    let _ := latAction (HilbertModular.formF (up f.1))
    have e' : latSMul (HilbertModular.formF (up f.1)) (diagF _ σ0) (latSMul _ k Lattices.stdLat) =
        latSMul (HilbertModular.formF (up f.1)) (diagF _ τ) (latSMul _ (κ' * κ') Lattices.stdLat) := by
      have hms : ∀ (a b : OAf (HilbertModular.formF (up f.1))) (L : Lat ℚ 2),
          latSMul _ (a * b) L = latSMul _ a (latSMul _ b L) := fun a b L =>
        (latAction (HilbertModular.formF (up f.1))).mul_smul a b L
      rw [hkk, hms (diagF _ (σ' * σ')) (κ' * κ'), hτ, map_mul (diagF _) σ0, hms (diagF _ σ0)]
    rw [e', hκ'2, diagF_smul] at e
    simp only [Lat.image] at e
    rw [e]
    show glImage (τ : GL (Fin 2) ℚ) (glImage _ intVec) = glImage Δ intVec
    rw [hΔ]; simp only [glImage_mul]
  have hτS : τ ∈ Tamagawa.soSub (HilbertModular.formF (up f.1)) ℚ :=
    (Tamagawa.soSub _ _).mul_mem hσ0 ((Tamagawa.soSub _ _).mul_mem hσ'S hσ'S)
  have hdetΔ : Δ.val.det = 1 := by
    rw [hΔ, Units.val_mul, Units.val_mul, det_mul, det_mul, show (τ : GL (Fin 2) ℚ).val.det = 1 from hτS, hdetP,
      det_gamGL]; ring
  -- the integral change of basis `U = Δ⁻¹γ ∈ SL₂(ℤ)`
  obtain ⟨U, -, hU⟩ := exists_int_of_latOf_eq hMlat
  have hUdet : U.det = 1 := by
    have e : ((U.det : ℤ) : ℚ) = 1 := by
      rw [show ((U.det : ℤ) : ℚ) = (U.map (Int.castRingHom ℚ)).det from (RingHom.map_det (Int.castRingHom ℚ) U),
        hU, Units.val_mul, det_mul, hγdet, mul_one]
      have e2 : Δ.val.det * Δ⁻¹.val.det = 1 := by
        rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
      rw [hdetΔ, one_mul] at e2; exact e2
    exact_mod_cast e
  have hγU : γ.val = Δ.val * U.map (Int.castRingHom ℚ) := by
    rw [hU, ← Units.val_mul, mul_inv_cancel_left]
  -- `g ∼ [aw⁴, B, C]`
  have hg4 : SLEquiv (BinQF.mk (a * w ^ 4) B C) g.1 := by
    refine ⟨Matrix.nonsingInvUnit U (by rw [hUdet]; exact isUnit_one), hUdet, fun x => ?_⟩
    show QuadForm.eval _ (U *ᵥ x) = _
    apply Int.cast_injective (α := ℚ)
    set xq : Fin 2 → ℚ := fun i => (x i : ℚ)
    have hτf : ∀ y, bq f.1 ((τ : GL (Fin 2) ℚ).val *ᵥ y) = bq f.1 y := fun y => by
      rw [← evalIn_formF_up f.1 ℚ, ← evalIn_formF_up f.1 ℚ]; exact evalIn_mulVec_of_mem _ τ.2 y
    calc ((QuadForm.eval (BinQF.mk (a * w ^ 4) B C) (U *ᵥ x) : ℤ) : ℚ)
        = bq (BinQF.mk (a * w ^ 4) B C) (U.map (Int.castRingHom ℚ) *ᵥ xq) := by
          rw [eval_cast_eq_bq, mulVec_cast]
      _ = bq (BinQF.mk a B (C * w ^ 4))
          ((gamGL ((w : ℚ) ^ 2) (pow_ne_zero 2 hwq)).val *ᵥ (U.map (Int.castRingHom ℚ) *ᵥ xq)) :=
          (bq_gamGL_sq hwq _).symm
      _ = bq f.1 (Pg.val *ᵥ ((gamGL ((w : ℚ) ^ 2) (pow_ne_zero 2 hwq)).val *ᵥ (U.map (Int.castRingHom ℚ) *ᵥ xq))) := by
          rw [hPval]; exact (bq_mulVec_of_int hP _).symm
      _ = bq f.1 (γ.val *ᵥ xq) := by
          rw [← hτf, hγU, hΔ, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
      _ = bq g.1 xq := by rw [← evalIn_rat_eq_bq, hform, evalIn_rat_eq_bq]
      _ = ((QuadForm.eval g.1 x : ℤ) : ℚ) := (eval_cast_eq_bq g.1 x).symm
  -- the class of `g`
  have ha0 : a ≠ 0 := ne_zero_of_coprime_two_mul (N := D * w) (by rw [← mul_assoc]; exact ha)
  have hwD : IsCoprime w D := hw.of_isCoprime_of_dvd_right ⟨2, by ring⟩
  have hwB : IsCoprime w B := by
    have h1 : IsCoprime w (B ^ 2) := by
      have e : B ^ 2 = D + w * (4 * a * C * w ^ 3) := by linear_combination hf'd'
      rw [e]; exact hwD.add_mul_left_right _
    exact IsCoprime.of_mul_right_left (by rw [← sq]; exact h1)
  have hW4d : (BinQF.mk (w ^ 4) B (a * C)).disc = D := by
    simp only [BinQF.disc, a_mk, b_mk, c_mk]; linear_combination hf'd'
  let W4 : PrimForm D := ⟨BinQF.mk (w ^ 4) B (a * C), fun d h1 h2 _ => by
    simp only [a_mk, b_mk] at h1 h2
    exact (hwB.pow_left (m := 4)).isUnit_of_dvd' h1 h2, hW4d⟩
  let F' : PrimForm D := ofEquiv f ⟨P, hPdet, hP⟩
  have hc : Concordant F'.1 W4.1 := concordant_of_coprime
    (by simp [F', ofEquiv, W4]; exact ⟨ha0, hw0⟩) (by simp [F', ofEquiv, W4]) (F'.2.2.trans W4.2.2.symm)
    (by simp only [F', ofEquiv, W4, a_mk]; exact (ha.of_isCoprime_of_dvd_right ⟨2 * D, by ring⟩).pow_right)
  have hcompa : (PrimForm.comp F' W4 hc).1.a = a * w ^ 4 := by rw [primComp_a]; simp [F', ofEquiv, W4]
  have hcompb : (PrimForm.comp F' W4 hc).1.b = B := by rw [primComp_b]; simp [F', ofEquiv]
  have hcompc : (PrimForm.comp F' W4 hc).1.c = C := by
    have hd : (PrimForm.comp F' W4 hc).1.b ^ 2 - 4 * (PrimForm.comp F' W4 hc).1.a * (PrimForm.comp F' W4 hc).1.c = D :=
      (PrimForm.comp F' W4 hc).2.2
    rw [hcompa, hcompb] at hd
    have h4 : (4 * a * w ^ 4) * ((PrimForm.comp F' W4 hc).1.c - C) = 0 := by linear_combination hf'd' - hd
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) ha0) (pow_ne_zero 4 hw0)))
  have hcomp : (PrimForm.comp F' W4 hc).1 = BinQF.mk (a * w ^ 4) B C :=
    ext_abc (by simp [hcompa]) (by simp [hcompb]) (by simp [hcompc])
  have hgc : mk g = mk F' * mk W4 := by
    rw [mk_mul_mk F' W4 hc]
    apply mk_eq_mk.2
    rw [hcomp]; exact hg4.symm
  obtain ⟨S, hS⟩ := (exists_pow_eq_iff (D := D) (n := 4) (by norm_num) (mk W4)).mpr
    ⟨W4, rfl, w, 1, 0, isCoprime_one_left, hw, by simp [W4, BinQF.eval, eval_int_eq]⟩
  have hF' : mk F' = mk f := mk_ofEquiv f _
  refine ⟨S, ?_⟩
  rw [hgc, hF', hS]

end Main

/-- **The "only if" input is a theorem** (`EstesPallOnlyIfStatement`, `Section3EstesPallIf.lean`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, 'only if': proved)"]
theorem estesPallOnlyIfStatement : EstesPallOnlyIfStatement where
  fourth D _ _ f g h := fourth_of_sameProperSpinorGenusForm f g h

/-- **Estes–Pall** (Conway–Sloane, Ch. 15, §3.5, p. 366, citing Estes–Pall 1973; proper reading), **unconditional**: for
a discriminant $D \ne 0$ that is not a square and primitive forms $f, g$ of discriminant $D$, $g$ is in the proper spinor
genus of $f$ if and only if $[g] = [f]\,\mathfrak S^4$ for a class $\mathfrak S$ of Cassels' group $\mathcal G$. -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall: same spinor genus iff the quotient is a fourth power; proved)"]
theorem estesPallStatement : EstesPallStatement :=
  estesPallStatement_of_onlyIf estesPallOnlyIfStatement

/-- **Estes–Pall without the nonsquare hypothesis**: for every discriminant $D \ne 0$ the proper spinor genus of $f$
consists exactly of the classes $[f]\,\mathfrak S^4$ (the hypothesis "$D$ not a square" of `EstesPallStatement` is not
needed by either direction of the proof). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, every nonzero discriminant)"]
theorem sameProperSpinorGenusForm_iff_fourth {D : ℤ} [NonzeroDisc D] (f g : PrimForm D) :
    SameProperSpinorGenusForm f.1 g.1 ↔ ∃ S : FormClass D, FormClass.mk g = FormClass.mk f * S ^ 4 :=
  ⟨fourth_of_sameProperSpinorGenusForm f g, fun ⟨S, hS⟩ => sameProperSpinorGenusForm_of_fourth f g S hS⟩

end QuadFormsKB.ConwaySloane.EstesPall
