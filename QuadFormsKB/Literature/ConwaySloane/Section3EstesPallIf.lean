/-
# Conway–Sloane, Ch. 15, §3.5: Estes–Pall, the "if" direction

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §3.5, p. 366
(`conwaysloane1999`), citing D. R. Estes and G. Pall, *Spinor genera of binary quadratic forms*, J. Number Theory **5**
(1973), 421–432: two binary forms are in the same spinor genus if and only if their quotient is a fourth power in the
group. Read with the proper spinor genus (`SameProperSpinorGenusForm`, `Section3EstesPall.lean`, which explains why).

**Proves**
* `sameProperSpinorGenusForm_of_fourth` (**the "if" direction, unconditional**): for primitive forms $f, g$ of
  discriminant $D \ne 0$ with $[g] = [f]\,\mathfrak S^4$ in Cassels' group $\mathcal G$ of proper classes, $g$ is in
  the proper spinor genus of $f$. (No hypothesis that $D$ is a nonsquare is needed for this direction.)
* `EstesPallOnlyIfStatement` (**named statement**, the remaining "only if" direction) and
  `estesPallStatement_of_onlyIf`: the book's statement `EstesPallStatement` follows from it.

**Proof of the "if" direction** (classical, via Cassels' composition of forms and a purely local spinor-norm
computation; no idèles of $\mathbb Q(\sqrt D)$ are needed).
1. *Representatives* (`exists_reps_of_fourth`; Cassels, Ch. 14, Lemma 2.5 with $n = 4$, p. 338, and concordant
   composition as in the proof of the Corollary to Theorem 3.1, p. 339): $\mathfrak S^4$ represents primitively $w^4$
   with $w$ prime to $2D$; composing with a concordant representative $[a, B, *]$ of $[f]$ gives integers $a, B, C$ with
   $a$ prime to $2Dw$, $f \sim f' = [a, B, Cw^4]$ and $g \sim g' = [aw^4, B, C]$ (proper equivalence).
2. *The substitution.* $g'(x) = f'(\gamma x)$ for $\gamma = \operatorname{diag}(w^2, w^{-2})$, so $g(x) = f(\Gamma x)$
   with $\Gamma = P\gamma R$, $\det\Gamma = 1$ ($P, R \in \mathrm{SL}_2(\mathbb Z)$ the proper equivalences).
3. *Spinor genus.* $M = \Gamma\mathbb Z^2$ lies in the genus of $L = \mathbb Z^2$ in $(\mathbb Q^2, f)$ (Cassels' genus
   theorem, `sameGenus_of_mk_eq_mul_sq`), so $M = hL$ for an adelic $h$ with rotation components
   (`exists_oaf_soSub`). By Cassels' criterion (Ch. 11, Lemma 1.4 (iv), `sameProperSpinorGenus_smul_iff`, with the
   global rotation $1$) it suffices that $\theta(h_p) \in \theta(O^+(L_p))$ for every $p$:
   * $p \nmid w$: $\Gamma$ and $\Gamma^{-1}$ are $p$-integral, so $M_p = L_p$ and $h_p \in O^+(L_p)$;
   * $p \mid w$ (so $p \nmid 2aD$): $\theta(h_p)$ is a unit class (`isUnitSqClass_spinorNorm_local`: with $x = Pe_0$,
     $\theta(h_p) = Q(h_px - x)\,Q(y) = (w^{-1})^2 \cdot$ unit, `Section3EstesPallLocal.lean`), and units are spinor norms
     of $O^+(L_p)$ for the unimodular $L_p$ (O'Meara 92:5, `localSpinorUnits_of_unimodular`).
   The exponent of $w$ is $\pm 2$ because the quotient is a **fourth** power; for a mere square ($w^{\pm 1}$) the
   valuation of $\theta(h_p)$ would be odd.

**The converse is proved** in `Section3EstesPallOnlyIf.lean` (`fourth_of_sameProperSpinorGenusForm`,
`estesPallOnlyIfStatement`), without ideals: square roots of spinor-kernel rotations and a squaring lemma for
$\operatorname{diag}(w, w^{-1})$. The original note follows. **Why the converse stayed named.** The "only if" direction (the proper spinor genus of $f$ is no larger than
$[f]\,\mathcal G^4$) needs the converse dictionary: every rotation of $(\mathbb Q_p^2, f)$ in the spinor kernel moves
$L_p$ only by fourth powers of local ideal classes, i.e. the description $O^+(V_p) \cong E_p^\times/\mathbb Q_p^\times$
($E = \mathbb Q(\sqrt D)$) with $\theta(\alpha/\bar\alpha) = N(\alpha)$ and Hilbert's Theorem 90, together with the
correspondence between proper classes and ideal classes of the order of discriminant $D$ at the level of idèles.
-/
import QuadFormsKB.Literature.ConwaySloane.Section3EstesPallLocal
import QuadFormsKB.Literature.ConwaySloane.Section3EstesPall
import QuadFormsKB.Literature.Cassels.Ch11Sec3Group
import QuadFormsKB.Literature.Cassels.Ch11Sec1Criterion
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus

open NumberField Matrix IsDedekindDomain

noncomputable section

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.RatBridge QuadFormsKB.Composition BinQF Binary FormClass

/-- **Representatives for a fourth-power quotient** (Cassels, Ch. 14, Lemma 2.5 with $n = 4$, and the composition of
concordant forms, as in the proof of the Corollary to Theorem 3.1, p. 339): if $[g] = [f]\,\mathfrak S^4$ then there are
integers $a, B, C, w$ with $w$ prime to $2D$, $a$ prime to $2Dw$, and forms $f' = [a, B, Cw^4] \sim f$ and
$g' = [aw^4, B, C] \sim g$ (proper equivalence). -/
@[kb "cassels1978" "Ch. 14, Lemma 2.5, p. 338 (n = 4), and the proof of the Corollary to Thm. 3.1, p. 339"]
theorem exists_reps_of_fourth {D : ℤ} [NonzeroDisc D] (f g : PrimForm D) (S : FormClass D)
    (h : mk g = mk f * S ^ 4) :
    ∃ a B C w : ℤ, IsCoprime w (2 * D) ∧ IsCoprime a (2 * D * w) ∧
      SLEquiv f.1 (BinQF.mk a B (C * w ^ 4)) ∧ SLEquiv (BinQF.mk (a * w ^ 4) B C) g.1 := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  obtain ⟨m0, hm0, w, x, y, hxy, hw, hev⟩ :=
    (exists_pow_eq_iff (D := D) (n := 4) (by norm_num) (S ^ 4)).mp ⟨S, rfl⟩
  obtain ⟨mm, em, hmma⟩ := exists_sLEquiv_a_of_eval (f := m0.1) hxy
  rw [hev] at hmma
  obtain ⟨m, hmk, hma⟩ : ∃ m : PrimForm D, mk m = S ^ 4 ∧ m.1.a = w ^ 4 :=
    ⟨ofEquiv m0 em, by rw [← hm0]; exact mk_eq_mk.2 em.symm, hmma⟩
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  obtain ⟨g', hg', hga⟩ := exists_rep_coprime (mk f) (M := 2 * D * w)
    (mul_ne_zero (mul_ne_zero two_ne_zero hD0) hw0)
  have ha0 : g'.1.a ≠ 0 := ne_zero_of_coprime_two_mul (N := D * w)
    (by rw [← mul_assoc]; exact hga)
  have haw : IsCoprime g'.1.a w := hga.of_isCoprime_of_dvd_right ⟨2 * D, by ring⟩
  have haw4 : IsCoprime g'.1.a (w ^ 4) := haw.pow_right
  obtain ⟨B, hB1, hB2⟩ := exists_common_b (a := g'.1.a) (a' := m.1.a) (b := g'.1.b) (b' := m.1.b)
    (by rw [hma]; exact haw4) (two_dvd_b_sub_b (g'.2.2.trans m.2.2.symm))
  obtain ⟨k0, ek, hka, hkb⟩ := exists_sLEquiv_b (f := g'.1) (B := B) hB1
  obtain ⟨m1, em1, hm1a, hm1b⟩ := exists_sLEquiv_b (f := m.1) (B := B) hB2
  obtain ⟨K, hKk, hKa, hKb⟩ : ∃ K : PrimForm D, mk K = mk g' ∧ K.1.a = g'.1.a ∧ K.1.b = B :=
    ⟨ofEquiv g' ek, mk_eq_mk.2 ek.symm, hka, hkb⟩
  obtain ⟨M1, hM1k, hM1a, hM1b⟩ : ∃ M1 : PrimForm D, mk M1 = mk m ∧ M1.1.a = m.1.a ∧ M1.1.b = B :=
    ⟨ofEquiv m em1, mk_eq_mk.2 em1.symm, hm1a, hm1b⟩
  have hc : Concordant K.1 M1.1 := concordant_of_coprime
    (by rw [hKa, hM1a, hma]; exact mul_ne_zero ha0 (pow_ne_zero 4 hw0))
    (hKb.trans hM1b.symm) (K.2.2.trans M1.2.2.symm) (by rw [hKa, hM1a, hma]; exact haw4)
  have hprod := mk_mul_mk K M1 hc
  have hgc : mk g = mk (PrimForm.comp K M1 hc) := by
    rw [← hprod, hKk, hM1k, hmk, hg', h]
  have e1 : SLEquiv (PrimForm.comp K M1 hc).1 g.1 := (mk_eq_mk.1 hgc).symm
  have e2 : SLEquiv f.1 K.1 := mk_eq_mk.1 (hKk.trans hg').symm
  have hCa : (PrimForm.comp K M1 hc).1.a = K.1.a * w ^ 4 := by
    rw [primComp_a, hM1a, hma]
  have hCb : (PrimForm.comp K M1 hc).1.b = K.1.b := by rw [primComp_b]
  have hCd : (PrimForm.comp K M1 hc).1.disc = D := (PrimForm.comp K M1 hc).2.2
  have hKd : K.1.disc = D := K.2.2
  have hcc : K.1.c = (PrimForm.comp K M1 hc).1.c * w ^ 4 := by
    have h1 : K.1.b ^ 2 - 4 * K.1.a * K.1.c = D := hKd
    have h2 : (PrimForm.comp K M1 hc).1.b ^ 2 - 4 * (PrimForm.comp K M1 hc).1.a *
        (PrimForm.comp K M1 hc).1.c = D := hCd
    rw [hCa, hCb] at h2
    have h3 : (4 * K.1.a) * (K.1.c - (PrimForm.comp K M1 hc).1.c * w ^ 4) = 0 := by
      linear_combination h2 - h1
    have h4 : 4 * K.1.a ≠ 0 := mul_ne_zero (by norm_num) (by rw [hKa]; exact ha0)
    have := (mul_eq_zero.1 h3).resolve_left h4
    linarith
  refine ⟨K.1.a, B, (PrimForm.comp K M1 hc).1.c, w, hw, by rw [hKa]; exact hga, ?_, ?_⟩
  · have hK : K.1 = BinQF.mk K.1.a B ((PrimForm.comp K M1 hc).1.c * w ^ 4) :=
      ext_abc (by simp) (by simp [hKb]) (by simp [hcc])
    rw [← hK]; exact e2
  · have hG : (PrimForm.comp K M1 hc).1 = BinQF.mk (K.1.a * w ^ 4) B (PrimForm.comp K M1 hc).1.c :=
      ext_abc (by simp [hCa]) (by simp [hCb, hKb]) (by simp)
    rw [← hG]; exact e1


/-- $f(x) = ax_0^2 + bx_0x_1 + cx_1^2$ over a field. -/
def bq (f : BinQF) {L : Type*} [Field L] (x : Fin 2 → L) : L :=
  (f.a : L) * x 0 ^ 2 + (f.b : L) * x 0 * x 1 + (f.c : L) * x 1 ^ 2

theorem evalIn_formF_up (f : BinQF) (K : Type*) [Field K] [Algebra ℚ K] (x : Fin 2 → K) :
    (HilbertModular.formF (up f)).evalIn K x = bq f x := by
  simp [bq, QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c, QuadForm.map]
  ring

theorem evalIn_rat_eq_bq (f : BinQF) (x : Fin 2 → ℚ) : f.evalIn ℚ x = bq f x := by
  simp [bq, QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c]
  ring

theorem eval_int_eq (f : BinQF) (x : Fin 2 → ℤ) :
    QuadForm.eval f x = f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c]
  ring

/-- An integral substitution identity $f(Px) = K(x)$ on $\mathbb Z^2$ holds over every field. -/
theorem bq_mulVec_of_int {f K : BinQF} {P : Matrix (Fin 2) (Fin 2) ℤ}
    (h : ∀ x, QuadForm.eval f (P *ᵥ x) = QuadForm.eval K x) {L : Type*} [Field L] (x : Fin 2 → L) :
    bq f (P.map (Int.cast : ℤ → L) *ᵥ x) = bq K x := by
  have E1 := h ![1, 0]
  have E2 := h ![0, 1]
  have E3 := h ![1, 1]
  simp only [eval_int_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at E1 E2 E3
  simp only [mul_one, mul_zero, add_zero, zero_add] at E1 E2 E3
  have E1' := congrArg (Int.cast : ℤ → L) E1
  have E2' := congrArg (Int.cast : ℤ → L) E2
  have E3' := congrArg (Int.cast : ℤ → L) E3
  push_cast at E1' E2' E3'
  simp only [bq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  linear_combination x 0 ^ 2 * E1' + x 1 ^ 2 * E2' + x 0 * x 1 * (E3' - E1' - E2')

/-- $\gamma = \operatorname{diag}(w^2, w^{-2})$. -/
def gammaW {L : Type*} [Field L] (w : L) : Matrix (Fin 2) (Fin 2) L := !![w ^ 2, 0; 0, (w ^ 2)⁻¹]

theorem gammaW_mulVec {L : Type*} [Field L] (w : L) (t : Fin 2 → L) :
    gammaW w *ᵥ t = ![w ^ 2 * t 0, (w ^ 2)⁻¹ * t 1] := by
  ext i; fin_cases i <;> simp [gammaW, Matrix.mulVec, dotProduct]

theorem bq_gammaW {L : Type*} [Field L] {a B C w : ℤ} (hw : (w : L) ≠ 0) (y : Fin 2 → L) :
    bq (BinQF.mk a B (C * w ^ 4)) (gammaW (w : L) *ᵥ y) = bq (BinQF.mk (a * w ^ 4) B C) y := by
  rw [gammaW_mulVec]
  simp only [bq, a_mk, b_mk, c_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  field_simp

section Valuation

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem valued_intCast_eq (m : ℤ) :
    Valued.v ((m : ℤ) : v.adicCompletion ℚ) = v.intValuation (m : 𝓞 ℚ) := by
  have := valued_algebraMap_int (F := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at this

theorem valued_intCast_eq_one {m : ℤ} (hm : (m : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v ((m : ℤ) : v.adicCompletion ℚ) = 1 := by
  rw [valued_intCast_eq]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hm

theorem valued_intCast_lt_one {m : ℤ} (hm : (m : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v ((m : ℤ) : v.adicCompletion ℚ) < 1 := by
  rw [valued_intCast_eq]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).mpr hm

theorem not_mem_of_isCoprime {m k : ℤ} (h : IsCoprime m k) (hk : (k : 𝓞 ℚ) ∈ v.asIdeal) :
    (m : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hm
  obtain ⟨u, t, hut⟩ := h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have : ((u * m + t * k : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hk)
  rwa [hut, Int.cast_one] at this

end Valuation

theorem hessian_det_binQF (f : BinQF) : f.hessian.det = -f.disc := by
  have h10 : f.coeff 1 0 = 0 := f.upper (show (0 : Fin 2) < 1 by decide)
  rw [Matrix.det_fin_two, QuadForm.hessian]
  simp only [Matrix.add_apply, Matrix.transpose_apply, h10, BinQF.disc, BinQF.a, BinQF.b, BinQF.c]
  ring

theorem entries_mul_mem (R1 : Subring ℚ) {A B : Matrix (Fin 2) (Fin 2) ℚ} (hA : ∀ i j, A i j ∈ R1)
    (hB : ∀ i j, B i j ∈ R1) (i j : Fin 2) : (A * B) i j ∈ R1 := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => R1.mul_mem (hA i k) (hB k j)

/-- **Estes–Pall, the "if" direction** (Conway–Sloane, Ch. 15, §3.5, p. 366, proper reading): if the classes of two
primitive forms $f, g$ of discriminant $D$ differ by a fourth power, $[g] = [f]\,\mathfrak S^4$, then $g$ is in the
proper spinor genus of $f$. Unconditional; valid for every discriminant $D \ne 0$ (square or not). See the module
docstring for the proof. -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, 'if': a fourth-power quotient gives the same proper spinor genus)"]
theorem sameProperSpinorGenusForm_of_fourth {D : ℤ} [NonzeroDisc D] (f g : PrimForm D) (S : FormClass D)
    (h : mk g = mk f * S ^ 4) : SameProperSpinorGenusForm f.1 g.1 := by
  obtain ⟨a, B, C, w, hw, ha, ef, eg⟩ := exists_reps_of_fourth f g S h
  have hKd : (BinQF.mk a B (C * w ^ 4)).disc = D := (SLEquiv.disc_eq ef).symm.trans f.2.2
  have hKd' : B ^ 2 - 4 * a * (C * w ^ 4) = D := by simpa [BinQF.disc] using hKd
  obtain ⟨γP, hPdet, hP⟩ := ef
  obtain ⟨γR, hRdet, hR⟩ := eg
  have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
  have hwq : (w : ℚ) ≠ 0 := by exact_mod_cast hw0
  set Pq : Matrix (Fin 2) (Fin 2) ℚ := γP.val.map (Int.cast : ℤ → ℚ) with hPq
  set Rq : Matrix (Fin 2) (Fin 2) ℚ := γR.val.map (Int.cast : ℤ → ℚ) with hRq
  set Γm : Matrix (Fin 2) (Fin 2) ℚ := Pq * gammaW (w : ℚ) * Rq with hΓm
  have hdetmap : ∀ M : Matrix (Fin 2) (Fin 2) ℤ, (M.map (Int.cast : ℤ → ℚ)).det = (M.det : ℚ) := fun M =>
    (RingHom.map_det (Int.castRingHom ℚ) M).symm
  have hΓdet : Γm.det = 1 := by
    rw [hΓm, det_mul, det_mul, hPq, hRq, hdetmap, hdetmap, hPdet, hRdet]
    simp [gammaW, det_fin_two, hwq]
  let Γ : GL (Fin 2) ℚ := Matrix.nonsingInvUnit Γm (by rw [hΓdet]; exact isUnit_one)
  have hΓval : Γ.val = Γm := rfl
  -- the form identity `f(Γx) = g(x)`
  have hform : ∀ x : Fin 2 → ℚ, f.1.evalIn ℚ (Γ.val *ᵥ x) = g.1.evalIn ℚ x := by
    intro x
    rw [evalIn_rat_eq_bq, evalIn_rat_eq_bq, hΓval, hΓm, ← mulVec_mulVec, ← mulVec_mulVec,
      bq_mulVec_of_int hP, bq_gammaW hwq, bq_mulVec_of_int hR]
  refine ⟨Γ, hΓdet, hform, ?_⟩
  -- the spinor genus
  set Q : QuadForm ℚ 2 := HilbertModular.formF (up f.1) with hQdef
  have hQeq : Q = f.1.map (Int.castRingHom ℚ) := by ext i j; simp [Q, QuadForm.map]
  have hQ : Q.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    have hm := RingHom.map_det (Int.castRingHom ℚ) f.1.hessian
    rw [RingHom.mapMatrix_apply] at hm
    rw [hQeq, QuadForm.hessian_map, ← hm, hessian_det_binQF, f.2.2]
    simpa using NonzeroDisc.ne_zero (D := D)
  let L : Lat ℚ 2 := Lattices.stdLat
  let M : Lat ℚ 2 := ⟨latOf Γ, latOf_isLattice Γ⟩
  have hsg : Siegel.SameGenus f.1 g.1 :=
    (sameGenus_of_mk_eq_mul_sq g f (S ^ 2) (by rw [h, ← pow_mul])).symm
  have hM : SameGenus Q L.1 M.1 := by
    have := sameGenus_latOf_of_sameGenus (f₁ := f.1) (f₂ := g.1) (g := Γ) (fun x => (hform x).symm) hsg
    rw [hQeq]
    simpa [latOf, glImage_one, L, M, Lattices.stdLat] using this
  obtain ⟨hh, hrot, hhM⟩ := exists_oaf_soSub hQ L hM
  have hone : latSMul Q 1 L = L := by
    let _ := latAction Q
    exact one_smul (OAf Q) L
  have hθ1 : ∀ (K : Type) [Field K] [Algebra ℚ K] [CharZero K], spinorNorm Q K 1 = 1 := fun K _ _ _ => by
    have := (spinorNormHom Q K hQ).map_one
    rwa [spinorNormHom_apply] at this
  have key := (sameProperSpinorGenus_smul_iff Q hQ L 1 hh (fun v => (Tamagawa.soSub Q _).one_mem) hrot).mpr
    ⟨1, (Tamagawa.soSub Q ℚ).one_mem, fun v => ?_⟩
  · rw [hone, hhM] at key
    exact key
  -- the condition at `v`
  have hL : loc v L.1 = std v := loc_intVec v
  have hlocM : loc v M.1 = locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) Γ) (std v) := by
    show loc v (glImage Γ intVec) = _
    rw [loc_glImage, loc_intVec]
  have hhv : locAct v ((hh v : orthGroup Q _) : GL (Fin 2) _) (std v) = loc v M.1 := by
    rw [← hhM, loc_latSMul, hL]
  suffices hs : ∃ ρ ∈ locStabV Q v L ⊓ Tamagawa.soSub Q (v.adicCompletion ℚ),
      spinorNorm Q _ ρ = spinorNorm Q _ (hh v) by
    obtain ⟨ρ, hρ, e⟩ := hs
    refine ⟨ρ, hρ, ?_⟩
    rw [e, map_one, hθ1]
    have : ((1 : OAf Q) v) = 1 := rfl
    rw [this, hθ1, mul_one, mul_one]
  by_cases hwv : ((w : ℤ) : 𝓞 ℚ) ∈ v.asIdeal
  · -- `p ∣ w`: the spinor norm of `h_v` is a unit class
    have h2D : ((2 * D : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := not_mem_of_isCoprime v hw.symm hwv
    have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h2 => h2D (by push_cast; exact Ideal.mul_mem_right _ _ h2)
    have hDv : (D : 𝓞 ℚ) ∉ v.asIdeal := fun hD => h2D (by push_cast; exact Ideal.mul_mem_left _ _ hD)
    have hav : (a : 𝓞 ℚ) ∉ v.asIdeal :=
      not_mem_of_isCoprime v ha (by push_cast; exact Ideal.mul_mem_left _ _ hwv)
    have hBv : (B : 𝓞 ℚ) ∉ v.asIdeal := by
      intro hB
      apply hDv
      rw [← hKd']
      push_cast
      have e : (4 * (a : 𝓞 ℚ) * ((C : 𝓞 ℚ) * (w : 𝓞 ℚ) ^ 4)) = (4 * a * C) * (w : 𝓞 ℚ) ^ 4 := by ring
      rw [e]
      exact sub_mem (Ideal.pow_mem_of_mem _ hB 2 (by norm_num))
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hwv 4 (by norm_num)))
    have hdet : (up f.1).hessian.det ∉ v.asIdeal := by
      have hm := RingHom.map_det (Int.castRingHom (𝓞 ℚ)) f.1.hessian
      rw [RingHom.mapMatrix_apply] at hm
      rw [show (up f.1).hessian = f.1.hessian.map (Int.castRingHom (𝓞 ℚ)) from QuadForm.hessian_map _ _, ← hm,
        hessian_det_binQF, f.2.2]
      simpa using hDv
    have LSU := localSpinorUnits_of_unimodular v (up f.1) h2 hdet le_rfl L hL
    -- the local data
    set Pv : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := γP.val.map (Int.cast : ℤ → v.adicCompletion ℚ)
      with hPv
    set Rv : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := γR.val.map (Int.cast : ℤ → v.adicCompletion ℚ)
      with hRv
    have hPform : ∀ z, Q.evalIn (v.adicCompletion ℚ) (Pv *ᵥ z) = fq v a B C w z := fun z => by
      rw [hQdef, evalIn_formF_up, bq_mulVec_of_int hP]
      simp only [bq, fq, a_mk, b_mk, c_mk]
      push_cast
      ring
    have ha' : Valued.v ((a : ℤ) : v.adicCompletion ℚ) = 1 := valued_intCast_eq_one v hav
    have hB' : Valued.v ((B : ℤ) : v.adicCompletion ℚ) = 1 := valued_intCast_eq_one v hBv
    have h2' : Valued.v (2 : v.adicCompletion ℚ) = 1 := by
      have := valued_intCast_eq_one v (m := 2) (by exact_mod_cast h2)
      simpa using this
    have hD' : Valued.v (((B : ℤ) : v.adicCompletion ℚ) ^ 2 - 4 * (a : v.adicCompletion ℚ) *
        (C : v.adicCompletion ℚ) * (w : v.adicCompletion ℚ) ^ 4) = 1 := by
      have := valued_intCast_eq_one v hDv
      rw [← hKd'] at this
      push_cast at this
      convert this using 2
      ring
    have hC' : Valued.v ((C : ℤ) : v.adicCompletion ℚ) ≤ 1 := valued_intCast_le_one' v C
    have hw' : Valued.v ((w : ℤ) : v.adicCompletion ℚ) < 1 := valued_intCast_lt_one v hwv
    have hw0' : ((w : ℤ) : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hw0
    -- `σx ∈ M_v`
    set x : Fin 2 → v.adicCompletion ℚ := Pv *ᵥ ![1, 0] with hx
    have hxstd : x ∈ std v := mem_std_iff.mpr fun i => by
      simp only [hx, hPv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero]
      exact valued_intCast_le_one' v _
    have hmem : ((hh v : orthGroup Q _) : GL (Fin 2) _).val *ᵥ x ∈ loc v M.1 := by
      rw [← hhv]; exact ⟨x, hxstd, rfl⟩
    rw [hlocM] at hmem
    obtain ⟨s, hs, hse⟩ := mem_locAct.mp hmem
    have hs' := mem_std_iff.mp hs
    have hΓmap : Γ.val.map (algebraMap ℚ (v.adicCompletion ℚ)) = Pv * gammaW ((w : ℤ) : v.adicCompletion ℚ) * Rv := by
      have e1 : Pq.map (algebraMap ℚ (v.adicCompletion ℚ)) = Pv := by ext i j; simp [hPq, hPv]
      have e2 : (gammaW (w : ℚ)).map (algebraMap ℚ (v.adicCompletion ℚ)) =
          gammaW ((w : ℤ) : v.adicCompletion ℚ) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [gammaW]
      have e3 : Rq.map (algebraMap ℚ (v.adicCompletion ℚ)) = Rv := by ext i j; simp [hRq, hRv]
      rw [hΓval, hΓm, Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
    set t : Fin 2 → v.adicCompletion ℚ := Rv *ᵥ s with ht
    have htle : ∀ i, Valued.v (t i) ≤ 1 := fun i => by
      simp only [ht, hRv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;>
        exact mul_le_one' (valued_intCast_le_one' v _) (hs' _)
    have hσx : ((hh v : orthGroup Q _) : GL (Fin 2) _).val *ᵥ x =
        Pv *ᵥ ![((w : ℤ) : v.adicCompletion ℚ) ^ 2 * t 0, (((w : ℤ) : v.adicCompletion ℚ) ^ 2)⁻¹ * t 1] := by
      rw [← hse, glMap_val, hΓmap, ← mulVec_mulVec, ← mulVec_mulVec, gammaW_mulVec]
    have hunit := isUnitSqClass_spinorNorm_local v Q hQ Pv hPform ha' hB' h2' hD' hC' hw' hw0' (hh v)
      (hrot v) htle hσx
    obtain ⟨k, hk, hkσ⟩ := LSU (hh v) hunit
    refine ⟨k⁻¹ * hh v, ⟨hkσ, (Tamagawa.soSub Q _).mul_mem
      ((Tamagawa.soSub Q _).inv_mem (spinorKernel_le_soSub Q _ hk)) (hrot v)⟩, ?_⟩
    rw [spinorKernel_eq_ker Q _ hQ] at hk
    obtain ⟨hk1, -⟩ := Subgroup.mem_inf.mp hk
    rw [MonoidHom.mem_ker, spinorNormHom_apply] at hk1
    rw [← spinorNormHom_apply Q _ hQ, map_mul, map_inv, spinorNormHom_apply, spinorNormHom_apply, hk1,
      inv_one, one_mul]
  · -- `p ∤ w`: `M_v = L_v`
    have hwinv : (((w : ℚ)) ^ 2)⁻¹ ∈ locSub v := by
      rw [mem_locSub]
      have e : algebraMap ℚ (v.adicCompletion ℚ) (((w : ℚ)) ^ 2)⁻¹ = (((w : ℤ) : v.adicCompletion ℚ) ^ 2)⁻¹ := by
        simp
      rw [e, map_inv₀, map_pow, valued_intCast_eq_one v hwv, one_pow, inv_one]
    have hint : ∀ m : ℤ, (m : ℚ) ∈ locSub v := fun m => intCast_mem _ m
    have hG : ∀ i j, gammaW (w : ℚ) i j ∈ locSub v := by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa [gammaW] using pow_mem (hint w) 2
      · simp [gammaW]
      · simp [gammaW]
      · simpa [gammaW] using hwinv
    have hent : ∀ i j, Γ.val i j ∈ locSub v := by
      rw [hΓval, hΓm]
      exact entries_mul_mem _ (entries_mul_mem _ (fun i j => by simpa [hPq] using hint _) hG)
        (fun i j => by simpa [hRq] using hint _)
    have hlocΓ : loc v (latOf Γ) = std v := loc_latOf_eq_std v Γ hent (Or.inl hΓdet)
    refine ⟨hh v, ⟨?_, hrot v⟩, rfl⟩
    show locAct v _ (loc v L.1) = loc v L.1
    rw [hL, hhv]
    exact hlocΓ


/-- **The "only if" direction when every square class is a fourth power** ($\mathcal G^2 = \mathcal G^4$, e.g. when
the class number is odd or $\mathcal G$ is an elementary abelian $2$-group): forms in one proper spinor genus are in one
genus (`SameProperSpinorGenusForm.sameGenus`), so their quotient is a square (Cassels' genus theorem), hence a fourth
power. Unconditional. -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, 'only if', when every square class is a fourth power)"]
theorem fourth_of_sameProperSpinorGenusForm_of_sq {D : ℤ} [NonzeroDisc D]
    (hG : ∀ T : FormClass D, ∃ S : FormClass D, T ^ 2 = S ^ 4) (f g : PrimForm D)
    (h : SameProperSpinorGenusForm f.1 g.1) : ∃ S : FormClass D, mk g = mk f * S ^ 4 := by
  obtain ⟨T, hT⟩ := exists_sq_of_sameGenus g f h.sameGenus.symm
  obtain ⟨S, hS⟩ := hG T
  exact ⟨S, by rw [hT, hS]⟩

/-- **Estes–Pall, the "only if" direction** (Conway–Sloane, Ch. 15, §3.5, p. 366, proper reading), as a **named
statement**: for a discriminant $D \ne 0$ that is not a square and primitive forms $f, g$ of discriminant $D$, if $g$ is
in the proper spinor genus of $f$ then $[g] = [f]\,\mathfrak S^4$ for a class $\mathfrak S \in \mathcal G$. Together with
the proved "if" direction (`sameProperSpinorGenusForm_of_fourth`) it gives the book's statement
(`estesPallStatement_of_onlyIf`). Proved: `estesPallOnlyIfStatement` (`Section3EstesPallOnlyIf.lean`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, 'only if': same proper spinor genus gives a fourth-power quotient; stated)"]
structure EstesPallOnlyIfStatement : Prop where
  fourth : ∀ (D : ℤ) [NonzeroDisc D], ¬ IsSquare D → ∀ f g : PrimForm D,
    SameProperSpinorGenusForm f.1 g.1 → ∃ S : FormClass D, FormClass.mk g = FormClass.mk f * S ^ 4

/-- **Estes–Pall from its "only if" direction** (the "if" direction is proved, `sameProperSpinorGenusForm_of_fourth`). -/
@[kb "conwaysloane1999" "Ch. 15, §3.5, p. 366 (Estes–Pall, conditional on the 'only if' direction)"]
theorem estesPallStatement_of_onlyIf (h : EstesPallOnlyIfStatement) : EstesPallStatement where
  iff D _ hD f g := ⟨h.fourth D hD f g, fun ⟨S, hS⟩ => sameProperSpinorGenusForm_of_fourth f g S hS⟩

end QuadFormsKB.ConwaySloane.EstesPall
