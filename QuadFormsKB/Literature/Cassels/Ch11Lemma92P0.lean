/-
# Cassels, Chapter 11, proof of Lemma 9.2: the lattice at a prime $p$ with $p \Vert \det$ (case (c₂), $p = p(0)$)

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, case (c₂), p. 247:
"$p = p(0)$. We put $\Gamma_p = \mathbb Z_p^4 \cap V_p^{(2)}$ … We note also that $f$ represents primitively on $\Gamma_p$ at least
the whole of $U_p$ and of $-gU_p^2$."

**Proves.** `units_reps_of_det_val_one`: if the localization of a lattice at an odd place $v$ is $\mathfrak o_v^3$, the form is
integral there and $\det H$ has valuation exactly $1$, then $U_p \subseteq \theta(L_v)$ (Cassels, Lemma 3.7, Corollary) and every
unit of $\mathbb Q_v$ is represented by $L_v$ (a Jordan basis has two unit vectors; Cassels, Lemma 3.7).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92CaseA
import QuadFormsKB.Literature.Cassels.Ch11Thm13Int

open NumberField IsDedekindDomain Matrix WithZero QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

open QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion


/-- Helper (as `Lattices.valued_evalIn_le_one_int`, with the algebra structure of the completion used here): an integral
form takes integral values on $\mathfrak o_v^n$. -/
theorem valued_evalIn_le_one_int' {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ n)
    {x : Fin n → v.adicCompletion ℚ} (hx : x ∈ std v) :
    Valued.v ((f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
  rw [mem_std_iff] at hx
  unfold QuadForm.evalIn
  refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => ?_
  split_ifs
  · have hc : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((f.map (Int.castRingHom ℚ)).coeff i j)) ≤ 1 := by
      have : algebraMap ℚ (v.adicCompletion ℚ) ((f.map (Int.castRingHom ℚ)).coeff i j) =
          ((f.coeff i j : ℤ) : v.adicCompletion ℚ) := by simp [QuadForm.map]
      rw [this]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (K := ℚ) (v := v)).1
        (intCast_mem (v.adicCompletionIntegers ℚ) (f.coeff i j))
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hc (hx i)) (hx j)
  · simp

/-- Helper (as `Lattices.locGram_one_int_det`, with the algebra structure used here). -/
theorem locGram_one_int_det' {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ n) :
    (locGram (f.map (Int.castRingHom ℚ)) v 1).det = ((f.hessian.det : ℤ) : v.adicCompletion ℚ) := by
  have : locGram (f.map (Int.castRingHom ℚ)) v 1 = f.hessian.map (Int.castRingHom (v.adicCompletion ℚ)) := by
    ext k l; simp [locGram, QuadForm.hessian, QuadForm.map]
  rw [this]; exact (RingHom.map_det (Int.castRingHom (v.adicCompletion ℚ)) f.hessian).symm

/-- **Units at a prime dividing the determinant exactly once** (Cassels, Ch. 11, Lemma 3.7 and its Corollary, used in case
(c₂)): let $h$ be an integral ternary form, $v$ an odd place, $L$ a lattice with $L_v = \mathfrak o_v^3$ and
$|\det H_h|_v = |p|_v$. Then every unit is in $\theta(L_v)$ and is represented by $L_v$. -/
theorem units_reps_of_det_val_one (h : QuadForm ℤ 3) (hQ : (h.map (Int.castRingHom ℚ)).Nondegenerate)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (L : Lat ℚ 3) (hL : loc v L.1 = std v)
    (hdet : Valued.v ((h.hessian.det : ℤ) : v.adicCompletion ℚ) = exp (-1 : ℤ)) :
    (∀ w : (v.adicCompletion ℚ)ˣ, Valued.v (w : v.adicCompletion ℚ) = 1 →
      w ∈ localSpinorNormGroup _ hQ v L) ∧
    (∀ c : v.adicCompletion ℚ, Valued.v c = 1 →
      ∃ x ∈ std v, (h.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x = c) := by
  have hγ : loc v L.1 = locAct v 1 (std v) := by rw [locAct_one]; exact hL
  have hint : ∀ x ∈ loc v L.1, Valued.v ((h.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1 := by
    intro x hx; rw [hL] at hx; exact valued_evalIn_le_one_int' v h hx
  have hdet1 : Valued.v (locGram (h.map (Int.castRingHom ℚ)) v 1).det = exp (-1 : ℤ) := by rw [locGram_one_int_det', hdet]
  refine ⟨fun w hw => ?_, fun c hc => ?_⟩
  · by_contra hnot
    have := valued_det_le_of_not_units_mem (Q := h.map (Int.castRingHom ℚ)) (v := v) hQ h2 L hint (fun hall => hnot (hall w hw)) 1 hγ
    rw [hdet1, exp_le_exp] at this
    norm_num at this
  · obtain ⟨γ', ν, hγ', horth, hval, hdet'⟩ := exists_diag_basis (Q := h.map (Int.castRingHom ℚ)) (v := v) hQ h2 L 1 hγ hint
    -- `∑ ν = 1`
    have hsum : ∑ k, ν k = 1 := by
      have hG : locGram (h.map (Int.castRingHom ℚ)) v γ' = Matrix.diagonal (fun k => locGram (h.map (Int.castRingHom ℚ)) v γ' k k) := by
        ext k l
        by_cases hkl : k = l
        · subst hkl; simp
        · rw [horth k l hkl, Matrix.diagonal_apply_ne _ hkl]
      rw [hG, Matrix.det_diagonal, map_prod, hdet1] at hdet'
      simp only [hval] at hdet'
      rw [prod_exp, exp_inj] at hdet'
      have : (∑ k, -(ν k : ℤ)) = -((∑ k, ν k : ℕ) : ℤ) := by simp [Finset.sum_neg_distrib]
      rw [this] at hdet'
      omega
    -- two indices with `ν = 0`
    obtain ⟨i, j, hij, hi, hj⟩ : ∃ i j : Fin 3, i ≠ j ∧ ν i = 0 ∧ ν j = 0 := by
      rw [Fin.sum_univ_three] at hsum
      by_cases h0 : ν 0 = 0
      · by_cases h1 : ν 1 = 0
        · exact ⟨0, 1, by decide, h0, h1⟩
        · exact ⟨0, 2, by decide, h0, by omega⟩
      · exact ⟨1, 2, by decide, by omega, by omega⟩
    set a := locGram (h.map (Int.castRingHom ℚ)) v γ' i i with ha
    set b := locGram (h.map (Int.castRingHom ℚ)) v γ' j j with hb
    have hva : Valued.v a = 1 := by rw [ha, hval, hi]; simp
    have hvb : Valued.v b = 1 := by rw [hb, hval, hj]; simp
    have h2v : Valued.v (2 : v.adicCompletion ℚ) = 1 := valued_two h2
    have hw : Valued.v (2 * c) = 1 := by rw [map_mul, h2v, hc, one_mul]
    have hw0 : (2 * c : v.adicCompletion ℚ) ≠ 0 := fun h0 => by rw [h0, map_zero] at hw; exact zero_ne_one hw
    have ha0 : a ≠ 0 := fun h0 => by rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hA : Valued.v (a / (2 * c)) = 1 := by rw [map_div₀, hva, hw, div_one]
    have hB : Valued.v (b / (2 * c)) = 1 := by rw [map_div₀, hvb, hw, div_one]
    have hAu : IsUnit (toO v (a / (2 * c)) hA.le) :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hA
    have hBu : IsUnit (toO v (b / (2 * c)) hB.le) :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hB
    obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr (LocalDensity.NF.irreducible_π v)
      (LocalDensity.NF.π_not_dvd_two v h2) hAu hBu
    have hst' : a * (s : v.adicCompletion ℚ) ^ 2 + b * (t : v.adicCompletion ℚ) ^ 2 = 2 * c := by
      have := congrArg (fun z : v.adicCompletionIntegers ℚ => (z : v.adicCompletion ℚ)) hst
      push_cast at this
      change a / (2 * c) * (s : v.adicCompletion ℚ) ^ 2 + b / (2 * c) * (t : v.adicCompletion ℚ) ^ 2 = 1 at this
      have hc0 : c ≠ 0 := fun h0 => by rw [h0, map_zero] at hc; exact zero_ne_one hc
      field_simp at this
      linear_combination this
    set d : Fin 3 → v.adicCompletion ℚ := Pi.single i (s : v.adicCompletion ℚ) + Pi.single j (t : v.adicCompletion ℚ)
      with hd
    have hdi : d i = s := by simp [hd, hij]
    have hdj : d j = t := by simp [hd, hij.symm]
    have hs1 : Valued.v (s : v.adicCompletion ℚ) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp s.2
    have ht1 : Valued.v (t : v.adicCompletion ℚ) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2
    have hdstd : d ∈ std v := (std v).add_mem (single_mem_std i hs1) (single_mem_std j ht1)
    refine ⟨γ'.val *ᵥ d, ?_, ?_⟩
    · rw [← hL, hγ']; exact ⟨d, hdstd, rfl⟩
    · have := two_mul_evalIn_locGram (Q := (h.map (Int.castRingHom ℚ))) (v := v) γ' d
      rw [hd, add_dotProduct, single_dotProduct, single_dotProduct, locGram_mulVec_diag horth,
        locGram_mulVec_diag horth, ← hd, hdi, hdj] at this
      have h2ne : (2 : v.adicCompletion ℚ) ≠ 0 := two_ne_zero
      apply mul_left_cancel₀ h2ne
      rw [this]
      linear_combination hst'

/-- **Every residue is $x^2 - y^2$ with $x, y \ne 0$** (modulo a prime $p \ge 7$): the choice of $b$ at $p(0)$ when
$p(0) \mid a$ ("the only case requiring thought is $p = p(0)$", p. 248). With $d \in \{1, 2, 3\}$, $d^2 \ne \pm r$:
$x = (d + r/d)/2$, $y = (r/d - d)/2$. -/
theorem exists_sq_sub_sq (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (r : ZMod p) :
    ∃ x y : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 - y ^ 2 = r := by
  have hne : ∀ m : ℕ, 0 < m → m < 7 → (m : ZMod p) ≠ 0 := by
    intro m hm0 hm7 h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd hm0 h0
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hne 2 (by norm_num) (by norm_num)
  have key : ∀ d : ZMod p, d ≠ 0 → d ^ 2 ≠ r → d ^ 2 ≠ -r → ∃ x y : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 - y ^ 2 = r := by
    intro d hd h1 h2'
    refine ⟨(d + r / d) / 2, (r / d - d) / 2, ?_, ?_, ?_⟩
    · intro h0
      apply h2'
      field_simp at h0
      linear_combination h0
    · intro h0
      apply h1
      field_simp at h0
      linear_combination -h0
    · field_simp; ring
  by_contra hno
  have hall : ∀ d : ZMod p, d ≠ 0 → d ^ 2 = r ∨ d ^ 2 = -r := by
    intro d hd
    by_contra h
    push Not at h
    exact hno (key d hd h.1 h.2)
  have c1 := hall 1 one_ne_zero
  have c2 := hall 2 h2
  have n3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast hne 3 (by norm_num) (by norm_num)
  have n5 : (5 : ZMod p) ≠ 0 := by exact_mod_cast hne 5 (by norm_num) (by norm_num)
  rcases c1 with h1 | h1 <;> rcases c2 with h2' | h2'
  all_goals first
    | exact n3 (by linear_combination h2' - h1)
    | exact n5 (by linear_combination h2' + h1)

/-- **$p \Vert \det H_h$ at $p = p(0)$:** if $p$ is odd, $p \nmid \det H_f$ and $p \Vert f(\mathbf u)$, then $p \Vert \det H_h$
(from $\det([\mathbf u \mid W])^2\det H_f = 2f(\mathbf u)\det H_h$ and $\det[\mathbf u \mid W] \mid 2f(\mathbf u)$). -/
theorem dvd_det_exactly (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (Wt : Matrix (Fin 3) (Fin 4) ℤ) (hWt : Wt * W = 1) (horth : ∀ z, bl f u (W *ᵥ z) = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdetf : ¬ (p : ℤ) ∣ f.hessian.det) (hg : (p : ℤ) ∣ f.eval u) (hg2 : ¬ (p : ℤ) ^ 2 ∣ f.eval u) :
    ∃ m : ℤ, (gramOf f W).hessian.det = p * m ∧ ¬ (p : ℤ) ∣ m := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2' : ¬ (p : ℤ) ∣ 2 := by
    intro h; have := Int.le_of_dvd (by norm_num) h
    have := hp.two_le; have : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
    omega
  obtain ⟨g', hg'⟩ := hg
  have hg'p : ¬ (p : ℤ) ∣ g' := fun ⟨k, hk⟩ => hg2 ⟨k, by rw [hg', hk]; ring⟩
  have hid := det_uW_sq_mul f u W horth
  have hdvd := det_uW_dvd f u W Wt hWt horth
  set D := (uW u W).det
  set H := (gramOf f W).hessian.det
  -- `p ∣ D`
  have hpD : (p : ℤ) ∣ D := by
    have : (p : ℤ) ∣ D ^ 2 * f.hessian.det := by rw [hid, hg']; exact ⟨2 * g' * H, by ring⟩
    rcases hpp.dvd_or_dvd this with h | h
    · exact hpp.dvd_of_dvd_pow h
    · exact absurd h hdetf
  obtain ⟨D', hD'⟩ := hpD
  -- `p ∤ D'`
  have hD'p : ¬ (p : ℤ) ∣ D' := by
    rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := hdvd
    have : (p : ℤ) ∣ 2 * g' := by
      have e : 2 * f.eval u = (p : ℤ) * (2 * g') := by rw [hg']; ring
      have e2 : (p : ℤ) * (2 * g') = (p : ℤ) * ((p : ℤ) * (k * l)) := by rw [← e, hl, hD', hk]; ring
      exact ⟨k * l, mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) e2⟩
    rcases hpp.dvd_or_dvd this with h | h
    · exact hp2' h
    · exact hg'p h
  -- `p D'^2 det H_f = 2 g' H`
  have e : (p : ℤ) * (D' ^ 2 * f.hessian.det) = 2 * g' * H := by
    apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
    rw [← mul_assoc]
    linear_combination (by rw [hD'] at hid; rw [hg'] at hid; linear_combination hid :
      (p : ℤ) * (p * (D' ^ 2 * f.hessian.det)) = p * (2 * g' * H))
  have hpH : (p : ℤ) ∣ H := by
    have : (p : ℤ) ∣ 2 * g' * H := ⟨_, e.symm⟩
    rcases hpp.dvd_or_dvd this with h | h
    · rcases hpp.dvd_or_dvd h with h' | h'
      · exact absurd h' hp2'
      · exact absurd h' hg'p
    · exact h
  obtain ⟨m, hm⟩ := hpH
  refine ⟨m, hm, fun ⟨k, hk⟩ => ?_⟩
  have : (p : ℤ) ∣ D' ^ 2 * f.hessian.det := by
    have e3 : (p : ℤ) * (D' ^ 2 * f.hessian.det) = (p : ℤ) * (2 * g' * p * k) := by rw [e, hm, hk]; ring
    exact ⟨2 * g' * k, by linear_combination mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero) e3⟩
  rcases hpp.dvd_or_dvd this with h | h
  · exact hD'p (hpp.dvd_of_dvd_pow h)
  · exact hdetf h

/-- Helper: the valuation of an integer exactly divisible by $p$. -/
theorem valued_p_mul (v : HeightOneSpectrum (𝓞 ℚ)) {m : ℤ}
    (hm : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ m) :
    Valued.v (((Rat.HeightOneSpectrum.natGenerator v : ℤ) * m : ℤ) : v.adicCompletion ℚ) = exp (-1 : ℤ) := by
  push_cast
  rw [map_mul, valued_intCast_eq_one v m hm, mul_one]
  exact_mod_cast valued_natGenerator v

/-- **Case (c₂), $p = p(0)$, as a local package** (Cassels, pp. 247–249): $\Gamma_p = \mathbb Z_p^4 \cap V^{(2)}$ (the standard
lattice in the coordinates $W$). Hypotheses: $p \ge 7$ odd, $p \nmid \det H_f$, $p \Vert f(\mathbf u)$, $\mathbf u$ primitive at $p$,
$e \in \mathbb Z^4$ with $p \nmid B(\mathbf u, e)$, $W\tilde Wx = x$ for $x \perp \mathbf u$. Every integer $a$ is served (modulus $p$):
if $p \nmid a$ then $c = a - f(\mathbf u)b^2$ is a unit; if $p \mid a$ then $b$ is chosen with $c \in -f(\mathbf u)U_p^2$,
represented by a multiple of $w_0 = B(\mathbf u, e)\mathbf u - 2f(\mathbf u)e$. Primitivity: one of $b\mathbf u \pm Wz$
("on replacing $\mathbf c$ by $-\mathbf c$ if need be", p. 249). -/
def pkgP0 (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (Wt : Matrix (Fin 3) (Fin 4) ℤ) (hWt : Wt * W = 1) (horth : ∀ z, bl f u (W *ᵥ z) = 0)
    (hrec : ∀ x : Fin 4 → ℤ, bl f u x = 0 → W *ᵥ (Wt *ᵥ x) = x)
    (hQ : ((gramOf f W).map (Int.castRingHom ℚ)).Nondegenerate)
    (h7 : 7 ≤ pOf v) (hdetf : ¬ (pOf v : ℤ) ∣ f.hessian.det) (hg : (pOf v : ℤ) ∣ f.eval u)
    (hg2 : ¬ (pOf v : ℤ) ^ 2 ∣ f.eval u) (hu : ∃ i, ¬ (pOf v : ℤ) ∣ u i) (e : Fin 4 → ℤ)
    (he : ¬ (pOf v : ℤ) ∣ bl f u e) (A : ℤ → Prop) : LocalPkg f u W A (pOf v) v := by
  classical
  have hp : (pOf v).Prime := Fact.out
  have hp2 : pOf v ≠ 2 := by omega
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [two_mem_iff_natGenerator]; exact hp2
  have hdetv : Valued.v (((gramOf f W).hessian.det : ℤ) : v.adicCompletion ℚ) = exp (-1 : ℤ) := by
    obtain ⟨m, hm, hmp⟩ := dvd_det_exactly f u W Wt hWt horth hp hp2 hdetf hg hg2
    rw [hm]; exact valued_p_mul v hmp
  refine
    { M := std v
      isLattice := isLattice_of_bounds v le_rfl le_rfl
      le_std := le_rfl
      units := fun L hQ' hL w hw => (units_reps_of_det_val_one (gramOf f W) hQ' v h2 L hL hdetv).1 w hw
      N := 1
      cond := fun a _ => ?_ }
  set p := pOf v with hpdef
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set h := gramOf f W with hh
  have hrepU := (units_reps_of_det_val_one h hQ v h2 stdLat (loc_intVec v) hdetv).2
  -- the vector `w₀ = B(u,e) u - 2g e` and its coordinates `z₀`
  set B := bl f u e with hB
  set w0 : Fin 4 → ℤ := B • u - (2 * (f.eval u)) • e with hw0
  have hw0u : bl f u w0 = 0 := by
    rw [hw0, bl_sub_right, bl_smul_right, bl_smul_right, bl_self]; ring
  set z0 := Wt *ᵥ w0 with hz0
  have hWz0 : W *ᵥ z0 = w0 := hrec w0 hw0u
  set S := B ^ 2 - 4 * (f.eval u) * f.eval e with hS
  have hhz0 : h.eval z0 = -(f.eval u) * S := by
    rw [hh, gramOf_eval, hWz0, hw0, sub_eq_add_neg, ← neg_smul, eval_add, eval_smul, eval_smul, bl_smul_left,
      bl_smul_right, hS]
    ring
  obtain ⟨g', hg'0⟩ := hg
  have hg' : f.eval u = (p : ℤ) * g' := hg'0
  have hg'p : ¬ (p : ℤ) ∣ g' := fun ⟨k, hk⟩ => hg2 ⟨k, by rw [hg', hk]; ring⟩
  have hSp : ¬ (p : ℤ) ∣ S := by
    intro hS'
    have : (p : ℤ) ∣ B ^ 2 := by
      have := dvd_add hS' (show (p : ℤ) ∣ 4 * (f.eval u) * f.eval e from ⟨4 * g' * f.eval e, by rw [hg']; ring⟩)
      simpa [hS] using this
    exact he (hpp.dvd_of_dvd_pow this)
  -- the choice of `b₀`
  obtain ⟨b0, hb0p, hb0⟩ : ∃ b0 : ℤ, ¬ (p : ℤ) ∣ b0 ∧ ((p : ℤ) ∣ a → ∃ y : ZMod p, y ≠ 0 ∧
      ((a / p : ℤ) : ZMod p) - (g' : ZMod p) * (b0 : ZMod p) ^ 2 = -(g' : ZMod p) * y ^ 2) := by
    by_cases hpa : (p : ℤ) ∣ a
    · obtain ⟨x, y, hx, hy, hxy⟩ := exists_sq_sub_sq p h7 (((a / p : ℤ) : ZMod p) * ((g' : ZMod p))⁻¹)
      have hg'0 : (g' : ZMod p) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨(x.val : ℤ), fun hd => hx ?_, fun _ => ⟨y, hy, ?_⟩⟩
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
        simpa using this
      · have hxv : ((x.val : ℤ) : ZMod p) = x := by simp
        rw [hxv]
        rw [eq_mul_inv_iff_mul_eq₀ hg'0] at hxy
        linear_combination -hxy
    · exact ⟨1, fun hd => hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd),
        fun h' => absurd h' hpa⟩
  refine ⟨b0, fun b hb => ⟨?_, fun z _ _ => ?_⟩⟩
  · -- representation
    have hbb : (b : ZMod p) = (b0 : ZMod p) := by
      rw [ZMod.intCast_eq_intCast_iff']
      simpa using (show b % ((p ^ 1 : ℕ) : ℤ) = b0 % ((p ^ 1 : ℕ) : ℤ) from hb)
    by_cases hpa : (p : ℤ) ∣ a
    · obtain ⟨y, hy, hy'⟩ := hb0 hpa
      obtain ⟨a', ha'⟩ := hpa
      have ha'' : a / p = a' := by rw [ha']; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)
      rw [ha''] at hy'
      set D : ℤ := (a' - g' * b ^ 2) * (-g' * S) with hD
      have hDmod : (D : ZMod p) = ((g' : ZMod p) * y * (B : ZMod p)) ^ 2 := by
        have hSmod : (S : ZMod p) = (B : ZMod p) ^ 2 := by
          rw [hS]; push_cast
          have : (((f.eval u) : ℤ) : ZMod p) = 0 := by
            rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hg']; exact dvd_mul_right _ _
          rw [this]; ring
        rw [hD]; push_cast; rw [hSmod, hbb]
        linear_combination (-(g' : ZMod p) * (B : ZMod p) ^ 2) * hy'
      have hD0 : (D : ZMod p) ≠ 0 := by
        rw [hDmod]
        have hB0 : (B : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hg'0 : (g' : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hg'0 hy) hB0)
      obtain ⟨ζ, hζ⟩ := exists_sq_padic_of_isSquare hp2 hD0 ⟨_, by rw [hDmod, sq]⟩
      have hu' : IsUnit ((-g' * S : ℤ) : ℤ_[p]) := by
        rw [PadicInt.isUnit_iff]
        refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
        have := (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
        rcases hpp.dvd_or_dvd this with h1 | h1
        · exact hg'p (by simpa using h1)
        · exact hSp h1
      obtain ⟨κi, hκi⟩ := hu'.exists_right_inv
      set t : ℤ_[p] := ζ * κi with ht
      have hDc : ((D : ℤ) : ℤ_[p]) = ((a' - g' * b ^ 2 : ℤ) : ℤ_[p]) * ((-g' * S : ℤ) : ℤ_[p]) := by
        rw [hD]; push_cast; ring
      have ht2 : t ^ 2 * ((-g' * S : ℤ) : ℤ_[p]) = ((a' - g' * b ^ 2 : ℤ) : ℤ_[p]) := by
        rw [ht]
        linear_combination (κi ^ 2 * ((-g' * S : ℤ) : ℤ_[p])) * hζ +
          (κi ^ 2 * ((-g' * S : ℤ) : ℤ_[p])) * hDc +
          (((a' - g' * b ^ 2 : ℤ) : ℤ_[p]) * (((-g' * S : ℤ) : ℤ_[p]) * κi + 1)) * hκi
      -- the representing vector `χ(t) z₀`
      have hc : a - b ^ 2 * (f.eval u) = (p : ℤ) * (a' - g' * b ^ 2) := by rw [ha', hg']; ring
      refine ⟨χ v t • locVec v (fun i => (z0 i : ℚ)), fun i => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, locVec_apply, map_mul]
        have h1 := valued_ψ_le_one v t
        have h2' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (z0 i : ℚ)) ≤ 1 := by
          simpa using valued_intCast_le_one' v (z0 i)
        rw [← χ_apply] at h1
        exact mul_le_one' h1 h2'
      · rw [evalIn_smul', evalIn_locVec, show (h.map (Int.castRingHom ℚ)).eval (fun i => (z0 i : ℚ)) = (h.eval z0 : ℚ) from Ch11Sec9Gamma.evalIn_rat_intCast h z0, hhz0, hc]
        rw [← map_pow, ← χ_intCast, ← χ_intCast, ← map_mul]
        congr 1
        push_cast
        rw [hpdef]
        have e2 : ((-(f.eval u) * S : ℤ) : ℤ_[pOf v]) = (pOf v : ℤ_[pOf v]) * ((-g' * S : ℤ) : ℤ_[pOf v]) := by
          rw [hg']; push_cast; ring
        push_cast at e2 ht2 ⊢
        rw [e2]
        linear_combination (pOf v : ℤ_[pOf v]) * ht2
    · -- `p ∤ a`: `c` is a unit
      have hpc : ¬ (p : ℤ) ∣ a - b ^ 2 * (f.eval u) := by
        intro hd
        apply hpa
        have := dvd_add hd (show (p : ℤ) ∣ b ^ 2 * (f.eval u) from ⟨b ^ 2 * g', by rw [hg']; ring⟩)
        simpa using this
      obtain ⟨x, hx, hxc⟩ := hrepU (algebraMap ℚ (v.adicCompletion ℚ) ((a - b ^ 2 * (f.eval u) : ℤ) : ℚ))
        (by simpa using valued_intCast_eq_one v _ hpc)
      exact ⟨x, hx, hxc⟩
  · -- primitivity: `b u + W z` or `b u - W z`
    have hbp : ¬ (p : ℤ) ∣ b := by
      intro hd
      apply hb0p
      have h1 : ((p ^ 1 : ℕ) : ℤ) ∣ b - b0 := (Int.ModEq.dvd hb.symm)
      have := dvd_sub hd (by simpa using h1); simpa using this
    by_cases hplus : PrimAt (Rat.HeightOneSpectrum.natGenerator v) (b • u + W *ᵥ z)
    · exact Or.inl hplus
    · refine Or.inr ⟨rfl, fun hall => ?_⟩
      have hall1 : ∀ j, ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ (b • u + W *ᵥ z) j :=
        not_not.mp hplus
      obtain ⟨i, hi⟩ := hu
      have h3 : (p : ℤ) ∣ 2 * (b * u i) := by
        have := dvd_add (hall1 i) (hall i)
        have e : (b • u + W *ᵥ z) i + (b • u - W *ᵥ z) i = 2 * (b * u i) := by
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [e] at this; exact this
      have hp2' : ¬ (p : ℤ) ∣ 2 := by
        intro h'; have := Int.le_of_dvd (by norm_num) h'
        have : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
        have := hp.two_le; omega
      rcases hpp.dvd_or_dvd h3 with h4 | h4
      · exact hp2' h4
      · rcases hpp.dvd_or_dvd h4 with h5 | h5
        · exact hbp h5
        · exact hi h5

end QuadFormsKB.Cassels.Ch11L92
