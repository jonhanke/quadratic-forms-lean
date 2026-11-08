/-
# Cassels, Chapter 11, proof of Lemma 9.2: case (b), the primes of $P$ with $a \in gU_p^2$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, case (b), p. 246:
"$p \in P$, $k(p) \ne 0$. As in case (I) for $n \ge 5$, we pick any $\Gamma_p \subset p\mathbb Z_p^4 \cap V_p^{(2)}$ with
$\theta(\Gamma_p) \supset U_p$ (9.43). Then, as before, $y\mathbf u + \mathbf c \notin p\mathbb Z_p^4$ ($y \in U_p$, $\mathbf c \in \Gamma_p$)."

**Proves.**
* `exists_sq_of_pow_three_dvd`: $x \equiv 1 \pmod{p^3}$ is a square in $\mathbb Z_p$ (all $p$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92P0

open NumberField IsDedekindDomain Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

/-- **$x \equiv 1 \pmod{p^3}$ is a square in $\mathbb Z_p$** ($p = 2$: $x = (1 + 4z)^2$, $z + 2z^2 = t$; $p$ odd:
$x = (1 + pz)^2$, $2z + pz^2 = p^2t$; Hensel, `exists_root_quadratic`). -/
theorem exists_sq_of_pow_three_dvd {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} (hx : (p : ℤ_[p]) ^ 3 ∣ x - 1) :
    ∃ y : ℤ_[p], y ^ 2 = x := by
  obtain ⟨t, ht⟩ := hx
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨z, hz⟩ := exists_root_quadratic (p := 2) (-t) 1 1 isUnit_one
    refine ⟨1 + 4 * z, ?_⟩
    have : x = 1 + 8 * t := by linear_combination ht
    rw [this]
    push_cast at hz
    linear_combination 8 * hz
  · have h2 : IsUnit (2 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hp2 ?_)
      have h1 : ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by exact_mod_cast hlt
      have h3 : p ∣ 2 := by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd 2).mp h1
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3
    obtain ⟨z, hz⟩ := exists_root_quadratic (-((p : ℤ_[p]) ^ 2 * t)) 2 1 h2
    refine ⟨1 + (p : ℤ_[p]) * z, ?_⟩
    linear_combination (p : ℤ_[p]) * hz - ht

open QuadFormsKB.Lattices in
/-- **A scaled orthogonal basis over $\mathbb Z_p$** (for (9.42)–(9.43)): for a nondegenerate integral ternary form $h$ and
any $T$ there is $C \in M_3(\mathbb Z_p)$, $\det C \ne 0$, all entries divisible by $p$, whose columns $c_i$ are pairwise
orthogonal with $h(c_i) = p^{L_i}w_i$, $w_i$ units, $L_i \in \{2T', 2T' + 1\}$ for some $T' \ge T$. *Proof:* an orthogonal
basis of $\mathbb Q_p^3$ (`Lattices.exists_orthogonal_basis`), a common denominator, and scaling of each vector by a power of
$p$. -/
theorem exists_orth_basis_padic (h : QuadForm ℤ 3) (hQ : (h.map (Int.castRingHom ℚ)).Nondegenerate)
    (p : ℕ) [Fact p.Prime] (T : ℕ) :
    ∃ C : Matrix (Fin 3) (Fin 3) ℤ_[p], C.det ≠ 0 ∧ (∀ i j, (p : ℤ_[p]) ∣ C i j) ∧
      (∀ i j, i ≠ j → bl (h.map (Int.castRingHom ℤ_[p])) (C *ᵥ Pi.single i 1) (C *ᵥ Pi.single j 1) = 0) ∧
      ∃ (T' : ℕ) (L : Fin 3 → ℕ) (w : Fin 3 → ℤ_[p]), T ≤ T' ∧ (∀ i, IsUnit (w i)) ∧
        (∀ i, L i = 2 * T' ∨ L i = 2 * T' + 1) ∧
        ∀ i, (h.map (Int.castRingHom ℤ_[p])).eval (C *ᵥ Pi.single i 1) = (p : ℤ_[p]) ^ L i * w i := by
  classical
  set φ := Int.castRingHom ℤ_[p]
  set hp := h.map φ with hhp
  have hcast : ∀ x : Fin 3 → ℤ_[p], ((hp.eval x : ℤ_[p]) : ℚ_[p]) =
      (h.map (Int.castRingHom ℚ)).evalIn ℚ_[p] (fun i => (x i : ℚ_[p])) := by
    intro x
    rw [evalIn_castHom_rat]
    exact hom_eval_castHom h PadicInt.Coe.ringHom x
  have hcastbl : ∀ x y : Fin 3 → ℤ_[p], ((bl hp x y : ℤ_[p]) : ℚ_[p]) =
      qbil (h.map (Int.castRingHom ℚ)) ℚ_[p] (fun i => (x i : ℚ_[p])) (fun i => (y i : ℚ_[p])) := by
    intro x y
    simp only [qbil]
    rw [← QuadForm.polar_eq_hessian, bl_eq, PadicInt.coe_sub, PadicInt.coe_sub, hcast, hcast, hcast]
    congr 2
    try (funext i; simp)
  obtain ⟨e, horth, hne⟩ := exists_orthogonal_basis (h.map (Int.castRingHom ℚ)) ℚ_[p] hQ
  -- a common denominator
  obtain ⟨⟨d, hd⟩, hdx⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ_[p])
    (Finset.univ.image fun ij : Fin 3 × Fin 3 => e ij.1 ij.2)
  have hdx' : ∀ i k, ∃ y : ℤ_[p], (y : ℚ_[p]) = (d : ℚ_[p]) * e i k := by
    intro i k
    obtain ⟨y, hy⟩ := hdx (e i k) (Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩)
    exact ⟨y, hy.trans (by change (d : ℤ_[p]) • e i k = _; rw [Algebra.smul_def]; rfl)⟩
  choose x hx using hdx'
  have hd0 : (d : ℚ_[p]) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hd (Subtype.ext h0)
  have hxv : ∀ i, (fun k => ((x i k : ℤ_[p]) : ℚ_[p])) = (d : ℚ_[p]) • e i := by
    intro i; funext k; rw [hx]; rfl
  have hval0 : ∀ i, hp.eval (x i) ≠ 0 := by
    intro i h0
    have := hcast (x i)
    rw [h0, PadicInt.coe_zero, hxv, evalIn_smul'] at this
    exact hne i (by rcases mul_eq_zero.mp this.symm with h1 | h1
                    · exact absurd (pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h1) hd0
                    · exact h1)
  choose k u hu hku using fun i => decomp (hval0 i)
  set T' := max T (Finset.univ.sup k) with hT'
  have hkT : ∀ i, k i ≤ 2 * T' + 1 := fun i => by
    have : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
    omega
  set j : Fin 3 → ℕ := fun i => (2 * T' + 1 - k i) / 2 with hj
  set c : Fin 3 → Fin 3 → ℤ_[p] := fun i => (p : ℤ_[p]) ^ (1 + j i) • x i with hc
  set C : Matrix (Fin 3) (Fin 3) ℤ_[p] := Matrix.of fun r s => c s r with hC
  have hcol : ∀ i, C *ᵥ Pi.single i 1 = c i := by
    intro i; rw [mulVec_single_one]; funext r; simp [hC]
  refine ⟨C, ?_, fun r s => ?_, fun i i' hii' => ?_, T' + 1, fun i => 2 + 2 * j i + k i, u, by omega, hu,
    fun i => ?_, fun i => ?_⟩
  · -- `det C ≠ 0`
    intro h0
    obtain ⟨η, hη0, hη⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hη0
    have hsum : ∑ i, (((η i : ℤ_[p]) * (p : ℤ_[p]) ^ (1 + j i) * d : ℤ_[p]) : ℚ_[p]) • e i = 0 := by
      funext r
      have := congrFun hη r
      simp only [mulVec, dotProduct, hC, Matrix.of_apply, hc, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      have := congrArg (fun y : ℤ_[p] => (y : ℚ_[p])) this
      simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_zero] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hx]; push_cast; ring
    have hlin := (Fintype.linearIndependent_iff.mp e.linearIndependent) _ hsum
    funext i
    have := hlin i
    have hp0 : ((p : ℤ_[p]) : ℚ_[p]) ≠ 0 := by simp [(Fact.out : p.Prime).ne_zero]
    have : ((η i : ℤ_[p]) : ℚ_[p]) = 0 := by
      push_cast at this
      rcases mul_eq_zero.mp this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · exact absurd (pow_eq_zero_iff (by omega) |>.mp h2) hp0
      · exact absurd h1 hd0
    exact Subtype.ext this
  · -- entries divisible by `p`
    simp only [hC, Matrix.of_apply, hc, Pi.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  · -- orthogonality
    rw [hcol, hcol]
    have h1 := hcastbl (c i) (c i')
    have e1 : (fun r => ((c i r : ℤ_[p]) : ℚ_[p])) = (((p : ℤ_[p]) ^ (1 + j i) * d : ℤ_[p]) : ℚ_[p]) • e i := by
      funext r; simp only [hc, Pi.smul_apply, smul_eq_mul]; push_cast; rw [hx]; ring
    have e2 : (fun r => ((c i' r : ℤ_[p]) : ℚ_[p])) =
        (((p : ℤ_[p]) ^ (1 + j i') * d : ℤ_[p]) : ℚ_[p]) • e i' := by
      funext r; simp only [hc, Pi.smul_apply, smul_eq_mul]; push_cast; rw [hx]; ring
    rw [e1, e2, qbil_smul_left, qbil_smul_right, horth i i' hii', mul_zero, mul_zero] at h1
    exact Subtype.ext h1
  · -- levels
    show 2 + 2 * ((2 * T' + 1 - k i) / 2) + k i = 2 * (T' + 1) ∨
      2 + 2 * ((2 * T' + 1 - k i) / 2) + k i = 2 * (T' + 1) + 1
    have hdm := Nat.div_add_mod (2 * T' + 1 - k i) 2
    have hmod := Nat.mod_lt (2 * T' + 1 - k i) (show 2 > 0 by norm_num)
    have := hkT i
    omega
  · -- values
    rw [hcol, hc, eval_smul, hku]
    ring

section Gram

open QuadFormsKB.Lattices

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

theorem tMat_single (C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]) (k : Fin 3) :
    tMat v C *ᵥ Pi.single k 1 = fun i => χ v ((C *ᵥ Pi.single k 1) i) := by
  have : (Pi.single k 1 : Fin 3 → v.adicCompletion ℚ) = fun i => χ v ((Pi.single k 1 : Fin 3 → ℤ_[pOf v]) i) := by
    funext i; by_cases hik : i = k
    · subst hik; simp
    · simp [hik]
  rw [this, tMat_mulVec]

/-- **The Gram matrix of $\psi(C)\,\mathfrak o_v^3$:** its entries are $\chi(B_h(Ce_k, Ce_l))$. -/
theorem locGram_tGL (h : QuadForm ℤ 3) {C : Matrix (Fin 3) (Fin 3) ℤ_[pOf v]} (hC : C.det ≠ 0) (k l : Fin 3) :
    locGram (h.map (Int.castRingHom ℚ)) v (tGL v hC) k l =
      χ v (bl (h.map (Int.castRingHom ℤ_[pOf v])) (C *ᵥ Pi.single k 1) (C *ᵥ Pi.single l 1)) := by
  rw [← locGram_apply_eq, tGL_val, tMat_single, tMat_single, qbil_χ, bl_eq]

/-- Helper: $|\chi(xw)| = |\chi(x)|$ for a unit $w$. -/
theorem valued_χ_mul_unit (x w : ℤ_[pOf v]) (hw : IsUnit w) : Valued.v (χ v (x * w)) = Valued.v (χ v x) := by
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  have h1 : Valued.v (χ v w) * Valued.v (χ v wi) = 1 := by
    rw [← map_mul, ← map_mul, hwi, map_one, map_one]
  have hw1 : Valued.v (χ v w) = 1 := by
    have a1 := valued_ψ_le_one v w
    have a2 := valued_ψ_le_one v wi
    rw [← χ_apply] at a1 a2
    refine le_antisymm a1 ?_
    by_contra hlt
    push Not at hlt
    have : Valued.v (χ v w) * Valued.v (χ v wi) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' a2) hlt
    rw [h1] at this; exact lt_irrefl _ this
  rw [map_mul, map_mul, hw1, mul_one]

end Gram

section CaseB

theorem isUnit_of_mul_eq_one_right' {R : Type*} [CommRing R] {a b : R} (h : a * b = 1) : IsUnit b :=
  ⟨⟨b, a, by rw [mul_comm]; exact h, h⟩, rfl⟩

open QuadFormsKB.Lattices

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Case (b) as a local package** (Cassels, p. 246 and p. 248): for the integers $a = f(\mathbf u)\beta^2$ with $\beta$ a
$p$-adic unit, $\Gamma_p = $ `tLat v C` for a scaled orthogonal basis $C$ of $(\mathbb Q_p^3, h)$ inside $p\mathbb Z_p^3$ (so
$\Gamma_p \subset p\mathbb Z_p^4 \cap V^{(2)}$, (9.42)) with $\theta(\Gamma_p) \supseteq U_p$ ((9.43): Lemma 3.7 for odd $p$,
Lemma 3.8 for $p = 2$). The residue $b_0$ makes $c = a - f(\mathbf u)b^2 = h(\varepsilon c_0)$; primitivity is (9.44). -/
def pkgCaseB (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (hQ : ((gramOf f W).map (Int.castRingHom ℚ)).Nondegenerate)
    (hu : ∃ i, ¬ (pOf v : ℤ) ∣ u i) (hg0 : f.eval u ≠ 0) (A : ℤ → Prop)
    (hA : ∀ a, A a → ∃ β : ℤ_[pOf v], IsUnit β ∧ ((a : ℤ) : ℤ_[pOf v]) = ((f.eval u : ℤ) : ℤ_[pOf v]) * β ^ 2)
    (p0 : ℕ) : LocalPkg f u W A p0 v := by
  classical
  have hgp : ((f.eval u : ℤ) : ℤ_[pOf v]) ≠ 0 := by exact_mod_cast hg0
  have hdec := decomp hgp
  let vg : ℕ := hdec.choose
  have hex := exists_orth_basis_padic (gramOf f W) hQ (pOf v) (vg + 3)
  let C := hex.choose
  have hC := hex.choose_spec
  let T' : ℕ := hC.2.2.2.choose
  refine
    { M := tLat v hC.1
      isLattice := tLat_isLattice v hC.1
      le_std := tLat_le_std v hC.1
      units := fun L hQ' hL w hw => ?_
      N := 2 * T' + 4
      cond := fun a ha => ?_ }
  · -- `U_p ⊆ θ(Γ_p)`
    obtain ⟨hCdet, hCp, hCorth, hT⟩ := hC
    obtain ⟨Lv, wv, hTT, hwv, hLv, hval⟩ := hT.choose_spec
    have hγ : loc v L.1 = locAct v (tGL v hCdet) (std v) := hL
    have horth' : ∀ k l, k ≠ l → locGram ((gramOf f W).map (Int.castRingHom ℚ)) v (tGL v hCdet) k l = 0 := by
      intro k l hkl; rw [locGram_tGL, hCorth k l hkl, map_zero]
    have hG : ∀ k, locGram ((gramOf f W).map (Int.castRingHom ℚ)) v (tGL v hCdet) k k =
        χ v (2 * ((pOf v : ℤ_[pOf v]) ^ Lv k * wv k)) := by
      intro k; rw [locGram_tGL, bl_self, hval]
    have hvG : ∀ k l, Lv k = Lv l → Valued.v (locGram ((gramOf f W).map (Int.castRingHom ℚ)) v (tGL v hCdet) l l) = Valued.v (locGram ((gramOf f W).map (Int.castRingHom ℚ)) v (tGL v hCdet) k k) := by
      intro k l hkl
      obtain ⟨wi, hwi⟩ := (hwv k).exists_right_inv
      rw [hG, hG]
      have e : (2 * ((pOf v : ℤ_[pOf v]) ^ Lv l * wv l)) = (2 * ((pOf v : ℤ_[pOf v]) ^ Lv k * wv k)) * (wv l * wi) := by
        rw [hkl]; linear_combination (-(2 * (pOf v : ℤ_[pOf v]) ^ Lv l * wv l)) * hwi
      rw [e, valued_χ_mul_unit v _ _ ((hwv l).mul (isUnit_of_mul_eq_one_right' hwi))]
    have hvG2 : ∀ k l, Lv l = Lv k + 1 → pOf v = 2 →
        Valued.v (locGram ((gramOf f W).map (Int.castRingHom ℚ)) v (tGL v hCdet) l l) = Valued.v (2 * locGram ((gramOf f W).map (Int.castRingHom ℚ)) v (tGL v hCdet) k k) := by
      intro k l hkl hp2
      obtain ⟨wi, hwi⟩ := (hwv k).exists_right_inv
      have e : (2 * ((pOf v : ℤ_[pOf v]) ^ Lv l * wv l)) =
          (2 * (2 * ((pOf v : ℤ_[pOf v]) ^ Lv k * wv k))) * (wv l * wi) := by
        rw [hkl, pow_succ]
        have h2 : (pOf v : ℤ_[pOf v]) = 2 := by exact_mod_cast hp2
        rw [h2]
        linear_combination (-(2 * 2 ^ Lv k * 2 * wv l)) * hwi
      rw [hG, hG, e, valued_χ_mul_unit v _ _ ((hwv l).mul (isUnit_of_mul_eq_one_right' hwi)), map_mul,
        map_ofNat]
    -- three indices, two of them at the same level
    have key : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → Lv i = Lv j → w ∈ localSpinorNormGroup ((gramOf f W).map (Int.castRingHom ℚ)) hQ' v L := by
      intro i j k hij hik hjk hLij
      by_cases hp2 : pOf v = 2
      · have h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal := by rw [two_mem_iff_natGenerator]; exact hp2
        refine units_mem_localSpinorNormGroup_two_ternary (Q := ((gramOf f W).map (Int.castRingHom ℚ))) hQ' h2 L (tGL v hCdet) hγ hij hik hjk
          (fun l m hlm _ => horth' l m hlm) (hvG i j hLij) ?_ w hw
        have hi := hLv i
        have hk := hLv k
        rcases (show Lv k = Lv i ∨ Lv k = Lv i + 1 ∨ Lv i = Lv k + 1 by omega) with h | h | h
        · exact Or.inl (hvG i k h.symm)
        · exact Or.inr (Or.inl (hvG2 i k h hp2))
        · exact Or.inr (Or.inr (hvG2 k i h hp2))
      · have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := by rw [two_mem_iff_natGenerator]; exact hp2
        exact units_mem_localSpinorNormGroup_of_orthogonal ((gramOf f W).map (Int.castRingHom ℚ)) v hQ' h2 L (tGL v hCdet) hγ horth' hij
          (hvG i j hLij).symm w hw
    have h0 := hLv 0
    have h1 := hLv 1
    have h2 := hLv 2
    by_cases e01 : Lv 0 = Lv 1
    · exact key 0 1 2 (by decide) (by decide) (by decide) e01
    · by_cases e02 : Lv 0 = Lv 2
      · exact key 0 2 1 (by decide) (by decide) (by decide) e02
      · exact key 1 2 0 (by decide) (by decide) (by decide) (by omega)
  · -- the local conditions on `b`
    obtain ⟨hCdet, hCp, hCorth, hT⟩ := hC
    obtain ⟨Lv, wv, hTT, hwv, hLv, hval⟩ := hT.choose_spec
    obtain ⟨β, hβ, haβ⟩ := hA a ha
    obtain ⟨gu, hgu, hgdec⟩ := hdec.choose_spec
    have hTT' : vg + 3 ≤ T' := hTT
    have hL0' : Lv 0 = 2 * T' ∨ Lv 0 = 2 * T' + 1 := hLv 0
    obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
    obtain ⟨gui, hgui⟩ := hgu.exists_right_inv
    obtain ⟨w0i, hw0i⟩ := (hwv 0).exists_right_inv
    have hρv : ((gramOf f W).map (Int.castRingHom ℤ_[pOf v])).eval (C *ᵥ Pi.single 0 1) =
        (pOf v : ℤ_[pOf v]) ^ Lv 0 * wv 0 := hval 0
    -- `b⋆ = β √(1 - ρ/(gβ²))`
    obtain ⟨y, hy⟩ := exists_sq_of_pow_three_dvd (p := pOf v)
      (x := 1 - (pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg) * wv 0 * gui * βi ^ 2)
      ⟨-((pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg - 3) * wv 0 * gui * βi ^ 2), by
        have hpw : (pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg) = (pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg - 3) *
            (pOf v : ℤ_[pOf v]) ^ 3 := by rw [← pow_add]; congr 1; omega
        rw [hpw]; ring⟩
    have e : (pOf v : ℤ_[pOf v]) ^ vg * (pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg) = (pOf v : ℤ_[pOf v]) ^ Lv 0 := by
      rw [← pow_add]; congr 1; omega
    have hgb : ((f.eval u : ℤ) : ℤ_[pOf v]) * (β * y) ^ 2 = (a : ℤ_[pOf v]) -
        (pOf v : ℤ_[pOf v]) ^ Lv 0 * wv 0 := by
      rw [mul_pow, hy, haβ, hgdec]
      linear_combination (-(wv 0) * (gu * gui) * (β * βi) ^ 2) * e +
        (-((pOf v : ℤ_[pOf v]) ^ Lv 0 * wv 0)) * hgui +
        (-((pOf v : ℤ_[pOf v]) ^ Lv 0 * wv 0) * (gu * gui) * (β * βi + 1)) * hβi
    have hbsu : IsUnit (β * y) := by
      refine hβ.mul ?_
      have : IsUnit (y ^ 2) := by
        rw [hy]
        have := isUnit_add_p_mul (p := pOf v) isUnit_one
          (-((pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg - 1) * wv 0 * gui * βi ^ 2))
        convert this using 1
        have hpw : (pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg) = (pOf v : ℤ_[pOf v]) ^ (Lv 0 - vg - 1) *
            (pOf v : ℤ_[pOf v]) := by rw [← pow_succ]; congr 1; omega
        rw [hpw]; ring
      exact (isUnit_pow_iff (by norm_num)).mp this
    refine ⟨(PadicInt.appr (β * y) (2 * T' + 4) : ℤ), fun b hb => ?_⟩
    obtain ⟨t, ht⟩ : (pOf v : ℤ_[pOf v]) ^ (2 * T' + 4) ∣ β * y - (b : ℤ_[pOf v]) := by
      have h1 : (pOf v : ℤ_[pOf v]) ^ (2 * T' + 4) ∣ β * y - (PadicInt.appr (β * y) (2 * T' + 4) : ℤ_[pOf v]) :=
        Ideal.mem_span_singleton.mp (PadicInt.appr_spec _ (β * y))
      have h2 : (pOf v : ℤ_[pOf v]) ^ (2 * T' + 4) ∣
          ((b : ℤ) : ℤ_[pOf v]) - ((PadicInt.appr (β * y) (2 * T' + 4) : ℤ) : ℤ_[pOf v]) := by
        have : ((pOf v ^ (2 * T' + 4) : ℕ) : ℤ) ∣ b - (PadicInt.appr (β * y) (2 * T' + 4) : ℤ) :=
          Int.ModEq.dvd hb.symm
        have := Int.cast_dvd_cast (α := ℤ_[pOf v]) _ _ this
        simpa using this
      have := dvd_sub h1 h2
      simpa using this
    have hbP : (b : ℤ_[pOf v]) = β * y - (pOf v : ℤ_[pOf v]) ^ (2 * T' + 4) * t := by linear_combination -ht
    refine ⟨?_, fun z hzM _ => Or.inl ?_⟩
    · -- `c = ρ ε²`
      set s' : ℤ_[pOf v] := (pOf v : ℤ_[pOf v]) ^ (2 * T' + 1 - Lv 0) * ((f.eval u : ℤ) : ℤ_[pOf v]) * t *
        (β * y + b) with hs'
      have hc : ((a - b ^ 2 * f.eval u : ℤ) : ℤ_[pOf v]) =
          (pOf v : ℤ_[pOf v]) ^ Lv 0 * wv 0 * (1 + (pOf v : ℤ_[pOf v]) ^ 3 * (s' * w0i)) := by
        have e2 : (pOf v : ℤ_[pOf v]) ^ Lv 0 * (pOf v : ℤ_[pOf v]) ^ 3 *
            (pOf v : ℤ_[pOf v]) ^ (2 * T' + 1 - Lv 0) = (pOf v : ℤ_[pOf v]) ^ (2 * T' + 4) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        push_cast
        rw [hs']
        linear_combination (-1 : ℤ_[pOf v]) * hgb +
          (((f.eval u : ℤ) : ℤ_[pOf v]) * (β * y + b)) * ht +
          (-((pOf v : ℤ_[pOf v]) ^ Lv 0 * (pOf v : ℤ_[pOf v]) ^ 3 * (pOf v : ℤ_[pOf v]) ^ (2 * T' + 1 - Lv 0) *
            ((f.eval u : ℤ) : ℤ_[pOf v]) * t * (β * y + b))) * hw0i +
          (-(((f.eval u : ℤ) : ℤ_[pOf v]) * t * (β * y + b))) * e2
      obtain ⟨ε, hε⟩ := exists_sq_of_pow_three_dvd (p := pOf v)
        (x := 1 + (pOf v : ℤ_[pOf v]) ^ 3 * (s' * w0i)) ⟨s' * w0i, by ring⟩
      refine exists_mem_tLat_of_rep v (gramOf f W) hCdet ⟨ε • Pi.single 0 1, ?_⟩
      rw [mulVec_smul, eval_smul, hρv, hc, hε]; ring
    · -- primitivity
      obtain ⟨η, hη⟩ := (intVec_mem_tLat_iff v hCdet z).mp hzM
      obtain ⟨i0, hi0⟩ := hu
      have hu0 : IsUnit ((u i0 : ℤ) : ℤ_[pOf v]) := by
        rw [PadicInt.isUnit_iff]
        refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hi0 ?_)
        exact (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
      have hbu : IsUnit ((b : ℤ) : ℤ_[pOf v]) := by
        rw [hbP]
        have := isUnit_add_p_mul (p := pOf v) hbsu (-((pOf v : ℤ_[pOf v]) ^ (2 * T' + 3) * t))
        convert this using 1; rw [pow_succ]; ring
      have hWz : (pOf v : ℤ_[pOf v]) ∣ (((W *ᵥ z) i0 : ℤ) : ℤ_[pOf v]) := by
        rw [cast_mulVec, hη]
        simp only [mulVec, dotProduct]
        exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left
          (Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (hCp j k) _) _
      apply primAt_of_isUnit_cast v
      refine ⟨i0, ?_⟩
      obtain ⟨r, hr⟩ := hWz
      have e3 : (((b • u + W *ᵥ z) i0 : ℤ) : ℤ_[pOf v]) = (b : ℤ_[pOf v]) * (u i0 : ℤ_[pOf v]) +
          (((W *ᵥ z) i0 : ℤ) : ℤ_[pOf v]) := by simp
      rw [e3, hr]
      exact isUnit_add_p_mul (hbu.mul hu0) r

end CaseB

end QuadFormsKB.Cassels.Ch11L92
