/-
# The $\alpha$ transformation law at the non-dyadic primes

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime $\mathfrak p \nmid 2$.

**Proves** `alphaLaw_odd`: `AlphaLawAt v Q_o P` for **every** nondegenerate integral form $Q_o$ and every integral $P$ with
$\det P \ne 0$, at every prime $\mathfrak p \nmid 2$, i.e.
$$r\big(O(P\mathfrak o_\mathfrak p^N), O(\mathfrak o_\mathfrak p^N)\big)\,\beta_\mathfrak p(Q_o) = \beta_\mathfrak p(Q_o\circ P)\,\|\det P\|^{N+1}.$$
*Proof* (induction on $N$ and on $\mathrm{ord}\det P$; purely by counting):
* $P = U\,\mathrm{diag}(\varpi, 1, \dots, 1)\,P_2$ ($U \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$, a row of $P \bmod \varpi$ in the left kernel) and the cocycle
  (`alphaLaw_mul`) reduce to an **index-$q$ step** $\Lambda_1 = \{y : c\cdot y \equiv 0 \bmod \varpi\}$;
* in a diagonal (Jordan) basis $Q_o = \langle a_0, \dots, a_{N-1}\rangle$ (Hanke 2004, Lemma 2.1, p. 355) a vector $z \in \Lambda_1$
  splitting $\mathfrak o_\mathfrak p^N$ exists ($z = e_i$ if $\varpi \mid c_i$, else $z = e_i + \lambda e_j$), except for a binary hyperbolic
  $\Lambda_2 = \varpi^sH$ with $\Lambda_1$ the kernel of an isotropic line; then `alphaLaw_of_split` and the induction hypothesis;
* the exceptional binary step by the **similitude trick** (`alphaLaw_special`): $\Lambda_1 = \sigma\Lambda_2$ for a similitude $\sigma$ of
  multiplier $\varpi$ with $\sigma\tau\sigma = \varpi\tau$ ($\tau = \mathrm{diag}(1, -1) \in O(\Lambda_2)$), so $r^2 = 1$;
* rank one and scalars by `alphaLaw_scalar`.

Sources: Weil 1982, §3.4 [unverified]; Hanke 2004, Lemma 2.1, p. 355, and §3, pp. 358–361. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.AlphaLawMoves

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open NumberField IsDedekindDomain Lattices QuadForm LocalDensity LocalDensity.DVR

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### The exceptional binary step: the similitude trick -/

section Special

/-- The similitude $\sigma$: $f_\pm = e_0 \pm \mu e_1 \mapsto f_+,\ \varpi f_-$ (with $u_2 = 2^{-1}$, $\mu_i = \mu^{-1}$). -/
def simMat (u2 μ μi : 𝔬) : Matrix (Fin 2) (Fin 2) 𝔬 :=
  !![u2 * (1 + NF.π v), u2 * μi * (1 - NF.π v); u2 * μ * (1 - NF.π v), u2 * (1 + NF.π v)]

/-- $\tau = \mathrm{diag}(1, -1)$. -/
def tauMat : Matrix (Fin 2) (Fin 2) 𝔬 := !![1, 0; 0, -1]

theorem det_simMat {u2 μ μi : 𝔬} (h2 : 2 * u2 = 1) (hμ : μ * μi = 1) : (simMat v u2 μ μi).det = NF.π v := by
  rw [simMat, det_fin_two_of]
  linear_combination (NF.π v * (2 * u2 + 1)) * h2 + (-(u2 ^ 2 * (1 - NF.π v) ^ 2)) * hμ

theorem simMat_tau_simMat {u2 μ μi : 𝔬} (h2 : 2 * u2 = 1) (hμ : μ * μi = 1) :
    simMat v u2 μ μi * tauMat v * simMat v u2 μ μi = NF.π v • tauMat v := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [simMat, tauMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (NF.π v * (2 * u2 + 1)) * h2 + (-(u2 ^ 2 * (1 - NF.π v) ^ 2)) * hμ
  · ring
  · ring
  · linear_combination (-(NF.π v * (2 * u2 + 1))) * h2 + (u2 ^ 2 * (1 - NF.π v) ^ 2) * hμ

theorem eval_diag_two {R : Type*} [CommRing R] (a₀ a₁ : R) (x : Fin 2 → R) :
    (QuadForm.diag ![a₀, a₁]).eval x = a₀ * x 0 ^ 2 + a₁ * x 1 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal]
  ring

theorem diag_compMat_simMat {u2 μ μi : 𝔬} (h2 : 2 * u2 = 1) (hμ : μ * μi = 1) {a₀ a₁ : 𝔬} (ha : a₀ + μ ^ 2 * a₁ = 0) :
    (QuadForm.diag ![a₀, a₁]).compMat (simMat v u2 μ μi) = NF.π v • QuadForm.diag ![a₀, a₁] := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, eval_smul_form', eval_diag_two, eval_diag_two]
  simp only [simMat, mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  set A := u2 * (1 + NF.π v)
  set B := u2 * (1 - NF.π v)
  linear_combination ((A * x 0 + u2 * μi * (1 - NF.π v) * x 1) ^ 2 - NF.π v * x 0 ^ 2) * ha +
    (a₁ * (-(NF.π v * (2 * u2 + 1) * μ ^ 2 * x 0 ^ 2) + NF.π v * (2 * u2 + 1) * x 1 ^ 2)) * h2 +
    (a₁ * (-(2 * μ * A * B * x 0 * x 1) - B ^ 2 * (μ * μi + 1) * x 1 ^ 2)) * hμ

theorem diag_compMat_tau (a₀ a₁ : 𝔬) : (QuadForm.diag ![a₀, a₁]).compMat (tauMat v) = QuadForm.diag ![a₀, a₁] := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, eval_diag_two, eval_diag_two]
  simp [tauMat, mulVec, dotProduct, Fin.sum_univ_two]

theorem eval_smul_form_gen {A : Type*} [CommRing A] {N : ℕ} (Q : QuadForm A N) (s : A) (z : Fin N → A) :
    (s • Q).eval z = s * Q.eval z := by
  simp only [QuadForm.eval, QuadForm.evalIn, smul_coeff, Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
    RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem map_smul_form {A B : Type*} [CommRing A] [CommRing B] {N : ℕ} (f : A →+* B) (s : A) (Q : QuadForm A N) :
    (s • Q).map f = f s • Q.map f := by
  refine QuadForm.ext (Matrix.ext fun i j => ?_)
  simp [QuadForm.map, smul_coeff, Matrix.map_apply, map_mul]

theorem relRatio_mul_self_inv {G : Type*} [Group G] {A B : Subgroup G} (h : Commens A B) :
    relRatio A B * relRatio B A = 1 := by
  rw [relRatio_mul h h.symm ⟨by simp, by simp⟩, relRatio_self]

/-- **The exceptional binary step** (the similitude trick; $\mathfrak p \nmid 2$): for $Q = \langle a_0, a_1\rangle$ with
$a_0 + \mu^2a_1 = 0$ ($\mu$ a unit; $\Lambda_2 = \mathfrak o_\mathfrak p^2$ is $a_1$ times a hyperbolic plane), the law holds for
$\Lambda_1 = \sigma\Lambda_2$. *Proof:* $\tau = \mathrm{diag}(1,-1) \in O(\Lambda_2)$ and the similitude $\sigma$ (multiplier $\varpi$) satisfy
$\sigma\tau\sigma = \varpi\tau$; conjugating by $\tau$ and by $\sigma$ gives $r(K(\sigma\Lambda_2), K(\Lambda_2)) = r(K(\Lambda_2), K(\sigma\Lambda_2))$, so
$r = 1$; and $Q\circ\sigma = \varpi Q$, so $\beta(Q\circ\sigma) = q^3\beta(Q)$ (`localDensityForm_smul`) while $\|\det\sigma\|^3 = q^{-3}$. -/
@[kb "weil1982" "§3.4 (the hyperbolic index-q step) [unverified]"]
theorem alphaLaw_special {u2 μ μi : 𝔬} (h2 : 2 * u2 = 1) (hμ : μ * μi = 1) {a₀ a₁ : 𝔬} (ha1 : a₁ ≠ 0)
    (ha : a₀ + μ ^ 2 * a₁ = 0) (hσ : (simMat v u2 μ μi).det ≠ 0) :
    AlphaLawAt v (QuadForm.diag ![a₀, a₁]) (simMat v u2 μ μi) hσ := by
  classical
  have hπ := NF.irreducible_π v
  set Qd := QuadForm.diag ![a₀, a₁]
  set Qv := Qd.map (algebraMap 𝔬 Fv)
  have hμu : IsUnit μ := ⟨⟨μ, μi, hμ, by rw [mul_comm]; exact hμ⟩, rfl⟩
  have ha0 : a₀ ≠ 0 := by
    intro h0; rw [h0, zero_add] at ha
    exact ha1 ((mul_eq_zero.mp ha).resolve_left (pow_ne_zero 2 hμu.ne_zero))
  have h2' : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have hQnd : Qd.Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_diag]
    simp [Fin.prod_univ_two, ha0, ha1, h2']
  have hτ : (tauMat v).det ≠ 0 := by simp [tauMat, det_fin_two_of]
  have hτu : IsUnit (tauMat v).det := by
    rw [show (tauMat v).det = -1 by simp [tauMat, det_fin_two_of]]; exact isUnit_one.neg
  set σv := glOf v (simMat v u2 μ μi) hσ
  set τv := glOf v (tauMat v) hτ
  -- the forms
  have hQτ : Qv.compMat τv.val = Qv := by
    rw [← integralModel_compMat v rfl _ hτ, diag_compMat_tau]
  have hQσ : ∀ x, (Qv.compMat σv.val).eval x = (NF.π v : Fv) * Qv.eval x := by
    intro x
    rw [← integralModel_compMat v rfl _ hσ, diag_compMat_simMat v h2 hμ ha, map_smul_form, eval_smul_form_gen]
    rfl
  have hπF : ((NF.π v : 𝔬) : Fv) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext (by simpa using h))
  set r := relRatio (KL v Qv (locAct v σv (std v))) (KL v Qv (std v))
  have hτstd : locAct v τv (std v) = std v := locAct_glOf_unit v _ hτu hτ
  -- conjugation by `τ`
  have e1 : relRatio (KL v Qv (locAct v τv (locAct v σv (std v)))) (KL v Qv (std v)) = r := by
    calc relRatio (KL v Qv (locAct v τv (locAct v σv (std v)))) (KL v Qv (std v))
        = relRatio (KL v Qv (locAct v τv (locAct v σv (std v)))) (KL v Qv (locAct v τv (std v))) := by
          rw [hτstd]
      _ = relRatio (KL v (Qv.compMat τv.val) (locAct v σv (std v))) (KL v (Qv.compMat τv.val) (std v)) :=
          (relRatio_KL_conj v Qv τv _ _).symm
      _ = r := by rw [hQτ]
  -- conjugation by `σ`
  have e2 : relRatio (KL v Qv (locAct v σv (locAct v τv (locAct v σv (std v))))) (KL v Qv (locAct v σv (std v))) = r := by
    rw [← relRatio_KL_conj, KL_formSmul v hπF _ hQσ, KL_formSmul v hπF _ hQσ, e1]
  -- `στσ = ϖτ`
  have hστσ : locAct v σv (locAct v τv (locAct v σv (std v))) =
      (std v).map ((LinearMap.lsmul Fv (Fin 2 → Fv) ((NF.π v : 𝔬) : Fv)).restrictScalars 𝔬) := by
    rw [← locAct_mul, ← locAct_mul]
    have hπ1 : ((NF.π v • (1 : Matrix (Fin 2) (Fin 2) 𝔬))).det ≠ 0 := by
      rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ hπ.ne_zero
    have : σv * τv * σv = glOf v (NF.π v • (1 : Matrix (Fin 2) (Fin 2) 𝔬)) hπ1 * τv := by
      apply Units.ext
      simp only [Units.val_mul, glOf_val, σv, τv]
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, simMat_tau_simMat v h2 hμ, Matrix.smul_mul,
        Matrix.one_mul]
    rw [this, locAct_mul, hτstd, locAct_glOf_smul]
  rw [hστσ, KL_smul v _ _ hπF] at e2
  have hlat : (locAct v σv (std v)).IsLattice Fv := locAct_isLattice _ (std_isLattice v)
  have hcom := commens_KL v Qv hlat (std_isLattice v)
  have hrr := relRatio_mul_self_inv hcom
  rw [show relRatio (KL v Qv (locAct v σv (std v))) (KL v Qv (std v)) = r from rfl, e2] at hrr
  have hr : r = 1 := by
    have hpos := relRatio_pos hcom
    nlinarith [hrr, hpos]
  -- the densities
  unfold AlphaLawAt
  rw [show relRatio (KL v (Qd.map (algebraMap 𝔬 Fv)) (locAct v (glOf v (simMat v u2 μ μi) hσ) (std v)))
    (KL v (Qd.map (algebraMap 𝔬 Fv)) (std v)) = r from rfl, hr, one_mul, diag_compMat_simMat v h2 hμ ha]
  have hπ1 : NF.π v ^ 1 ∣ NF.π v := by rw [pow_one]
  have hπ2 : ¬ NF.π v ^ (1 + 1) ∣ NF.π v := by
    rintro ⟨t, ht⟩
    apply hπ.not_isUnit
    have : NF.π v * (NF.π v * t - 1) = 0 := by linear_combination -ht
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hπ.ne_zero
    · exact ⟨⟨NF.π v, t, by linear_combination h, by linear_combination h⟩, rfl⟩
  rw [localDensityForm_smul Qd hQnd hπ hπ1 hπ2, det_simMat v h2 hμ, norm_coe_of_pow_dvd v hπ1 hπ2]
  have hq : (0 : ℝ) < q 𝔬 := Nat.cast_pos.mpr q_pos
  norm_num
  field_simp

end Special

/-! ### A split vector in an index-$q$ sublattice (diagonal coordinates, $\mathfrak p \nmid 2$) -/

section SplitVector

variable {N : ℕ}

/-- The vector $x\,e_i + y\,e_j$. -/
def twoVec (i j : Fin N) (x y : 𝔬) : Fin N → 𝔬 := fun k => if k = i then x else if k = j then y else 0

theorem twoVec_i {i j : Fin N} (x y : 𝔬) : twoVec v i j x y i = x := by simp [twoVec]

theorem twoVec_j {i j : Fin N} (hij : i ≠ j) (x y : 𝔬) : twoVec v i j x y j = y := by
  simp [twoVec, Ne.symm hij]

theorem twoVec_other {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j) (x y : 𝔬) : twoVec v i j x y k = 0 := by
  simp [twoVec, hki, hkj]

theorem sum_twoVec (f : Fin N → 𝔬 → 𝔬) (hf : ∀ k, f k 0 = 0) {i j : Fin N} (hij : i ≠ j) (x y : 𝔬) :
    ∑ k, f k (twoVec v i j x y k) = f i x + f j y := by
  rw [Finset.sum_eq_add i j hij (fun k _ hk => by rw [twoVec_other v hk.1 hk.2, hf]) (by simp) (by simp),
    twoVec_i, twoVec_j v hij]

theorem exists_min_dvd {a : Fin N → 𝔬} (ha : ∀ i, a i ≠ 0) (hN : 0 < N) : ∃ i₀, ∀ j, a i₀ ∣ a j := by
  classical
  have hπ := NF.irreducible_π v
  choose e he he' using fun i => exists_pow_dvd_not_dvd (NF.π v) hπ (ha i)
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨i₀, fun j => ?_⟩
  obtain ⟨u, hu⟩ := he i₀
  obtain ⟨w, hw⟩ := he j
  have huu : IsUnit u := dvr_isUnit_of_not_dvd hπ fun h => he' i₀ (by rw [hu, pow_succ]; exact mul_dvd_mul_left _ h)
  rw [hu, hw]
  have hle := hmin j (Finset.mem_univ _)
  refine ⟨((huu.unit⁻¹ : 𝔬ˣ) : 𝔬) * NF.π v ^ (e j - e i₀) * w, ?_⟩
  have h1 : u * ((huu.unit⁻¹ : 𝔬ˣ) : 𝔬) = 1 := huu.mul_val_inv
  have h2 : NF.π v ^ e j = NF.π v ^ e i₀ * NF.π v ^ (e j - e i₀) := by rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [h2]
  linear_combination (-(NF.π v ^ e i₀ * NF.π v ^ (e j - e i₀) * w)) * h1

theorem dvd_of_mul_unit_dvd {x w : 𝔬} (hw : IsUnit w) {y : 𝔬} (h : x ∣ y) : x * w ∣ y * w := mul_dvd_mul_right h w

/-- **A split vector in an index-$q$ sublattice** ($\mathfrak p \nmid 2$; diagonal coordinates $Q = \langle a_i\rangle$; the sublattice
$\{y : c\cdot y \equiv 0\}$, $c$ primitive): either some $z$ in it has $Q(z) \ne 0$ and $Q(z) \mid a_kz_k$ for all $k$ (so $z$ splits
$\mathfrak o_\mathfrak p^N$), or $N = 2$ and the sublattice is the kernel of an isotropic line of $a_{i_0}$ times a hyperbolic plane. -/
theorem exists_split_or_special (hodd : ¬ NF.π v ∣ 2) {n : ℕ} (a : Fin (n + 2) → 𝔬) (ha : ∀ i, a i ≠ 0)
    (c : Fin (n + 2) → 𝔬) :
    (∃ z : Fin (n + 2) → 𝔬, NF.π v ∣ c ⬝ᵥ z ∧ (∑ i, a i * z i ^ 2) ≠ 0 ∧
      ∀ k, (∑ i, a i * z i ^ 2) ∣ a k * z k) ∨
    (n = 0 ∧ ∃ i₀ j : Fin (n + 2), i₀ ≠ j ∧ ¬ NF.π v ∣ c i₀ ∧ ¬ NF.π v ∣ c j ∧
      ∃ r, ¬ NF.π v ∣ r ∧ a j = a i₀ * r ∧ NF.π v ∣ c j ^ 2 + c i₀ ^ 2 * r) := by
  classical
  have hπ := NF.irreducible_π v
  have hp := hπ.prime
  by_cases hA : ∃ i, NF.π v ∣ c i
  · left
    obtain ⟨i, hi⟩ := hA
    have hsum : (∑ k, a k * (Pi.single i (1 : 𝔬) : Fin (n + 2) → 𝔬) k ^ 2) = a i := by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]; simp
    refine ⟨Pi.single i 1, by rw [dotProduct_single, mul_one]; exact hi, by rw [hsum]; exact ha i, fun k => ?_⟩
    rw [hsum]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  push_neg at hA
  have hcu : ∀ j, IsUnit (c j) := fun j => dvr_isUnit_of_not_dvd hπ (hA j)
  obtain ⟨i₀, hmin⟩ := exists_min_dvd v ha (by omega)
  choose r hr using hmin
  set ci : Fin (n + 2) → 𝔬 := fun j => (((hcu j).unit⁻¹ : 𝔬ˣ) : 𝔬)
  have hcci : ∀ j, c j * ci j = 1 := fun j => (hcu j).mul_val_inv
  -- the two-term vectors
  have key : ∀ i j : Fin (n + 2), i ≠ j → a i ∣ a j → ∀ s : 𝔬, ¬ NF.π v ∣ s →
      a i * s = a i + a j * (-(c i) * ci j) ^ 2 →
      ∃ z : Fin (n + 2) → 𝔬, NF.π v ∣ c ⬝ᵥ z ∧ (∑ k, a k * z k ^ 2) ≠ 0 ∧
        ∀ k, (∑ k', a k' * z k' ^ 2) ∣ a k * z k := by
    intro i j hij hdiv s hs hS
    have hsu : IsUnit s := dvr_isUnit_of_not_dvd hπ hs
    set μ := -(c i) * ci j
    have hsum : (∑ k, a k * twoVec v i j 1 μ k ^ 2) = a i * s := by
      rw [sum_twoVec v (fun k x => a k * x ^ 2) (fun k => by simp) hij, hS]; ring
    have hdot : c ⬝ᵥ twoVec v i j 1 μ = 0 := by
      show (∑ k, c k * twoVec v i j 1 μ k) = 0
      rw [sum_twoVec v (fun k x => c k * x) (fun k => by simp) hij]
      linear_combination (-(c i)) * hcci j
    refine ⟨twoVec v i j 1 μ, by rw [hdot]; exact dvd_zero _, ?_, fun k => ?_⟩
    · rw [hsum]; exact mul_ne_zero (ha i) hsu.ne_zero
    · rw [hsum]
      obtain ⟨t, ht⟩ := hdiv
      have hsi : s * ((hsu.unit⁻¹ : 𝔬ˣ) : 𝔬) = 1 := hsu.mul_val_inv
      by_cases hki : k = i
      · subst hki
        rw [twoVec_i]
        exact ⟨((hsu.unit⁻¹ : 𝔬ˣ) : 𝔬), by linear_combination (-(a k)) * hsi⟩
      · by_cases hkj : k = j
        · subst hkj
          rw [twoVec_j v hij, ht]
          exact ⟨((hsu.unit⁻¹ : 𝔬ˣ) : 𝔬) * t * μ, by linear_combination (-(a i * t * μ)) * hsi⟩
        · rw [twoVec_other v hki hkj, mul_zero]; exact dvd_zero _
  by_cases hB : ∃ j, j ≠ i₀ ∧ ¬ NF.π v ∣ c j ^ 2 + c i₀ ^ 2 * r j
  · left
    obtain ⟨j, hj, hnd⟩ := hB
    refine key i₀ j (Ne.symm hj) ⟨r j, hr j⟩ (1 + r j * (-(c i₀) * ci j) ^ 2) (fun hd => hnd ?_) (by rw [hr j]; ring)
    have : c j ^ 2 * (1 + r j * (-(c i₀) * ci j) ^ 2) = c j ^ 2 + c i₀ ^ 2 * r j := by
      linear_combination (r j * c i₀ ^ 2 * (c j * ci j + 1)) * hcci j
    rw [← this]; exact dvd_mul_of_dvd_right hd _
  push_neg at hB
  have hru : ∀ j, j ≠ i₀ → ¬ NF.π v ∣ r j := by
    intro j hj hd
    have h1 := hB j hj
    have h2 : NF.π v ∣ c j ^ 2 := by
      have := h1.sub (dvd_mul_of_dvd_right hd (c i₀ ^ 2))
      simpa using this
    exact hA j (hp.dvd_of_dvd_pow h2)
  rcases n with _ | n
  · right
    refine ⟨rfl, i₀, if i₀ = 0 then 1 else 0, ?_, hA i₀, hA _, r _, hru _ ?_, hr _, hB _ ?_⟩ <;>
      (fin_cases i₀ <;> simp)
  · left
    obtain ⟨j, k, hjk, hji, hki⟩ : ∃ j k : Fin (n + 3), j ≠ k ∧ j ≠ i₀ ∧ k ≠ i₀ := by
      by_cases h0 : i₀ = ⟨0, by omega⟩
      · refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;> (subst h0; simp [Fin.ext_iff])
      · by_cases h1 : i₀ = ⟨1, by omega⟩
        · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;> (subst h1; simp [Fin.ext_iff])
        · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], Ne.symm h0, Ne.symm h1⟩
    have hrju : IsUnit (r j) := dvr_isUnit_of_not_dvd hπ (hru j hji)
    set rji : 𝔬 := ((hrju.unit⁻¹ : 𝔬ˣ) : 𝔬)
    have hrr : r j * rji = 1 := hrju.mul_val_inv
    have hdiv : a j ∣ a k := ⟨rji * r k, by rw [hr j, hr k]; linear_combination (-(a i₀ * r k)) * hrr⟩
    refine key j k hjk hdiv (1 + rji * r k * (-(c j) * ci k) ^ 2) (fun hd => ?_)
      (by rw [hr j, hr k]; linear_combination (a i₀ * r k * (-(c j) * ci k) ^ 2) * hrr)
    -- `r_j c_k² s = r_j c_k² + r_k c_j²`, and `π ∤ r_j c_k² + r_k c_j²`
    have e1 : r j * c k ^ 2 * (1 + rji * r k * (-(c j) * ci k) ^ 2) = r j * c k ^ 2 + r k * c j ^ 2 := by
      linear_combination (r k * c j ^ 2 * (c k * ci k) ^ 2) * hrr + (r k * c j ^ 2 * (c k * ci k + 1)) * hcci k
    have hd' : NF.π v ∣ r j * c k ^ 2 + r k * c j ^ 2 := by rw [← e1]; exact dvd_mul_of_dvd_right hd _
    have e2 : c k ^ 2 * (c j ^ 2 + c i₀ ^ 2 * r j) + c j ^ 2 * (c k ^ 2 + c i₀ ^ 2 * r k) =
        2 * (c j ^ 2 * c k ^ 2) + c i₀ ^ 2 * (r j * c k ^ 2 + r k * c j ^ 2) := by ring
    have h3 : NF.π v ∣ 2 * (c j ^ 2 * c k ^ 2) := by
      have := (dvd_add (dvd_mul_of_dvd_right (hB j hji) (c k ^ 2))
        (dvd_mul_of_dvd_right (hB k hki) (c j ^ 2))).sub (dvd_mul_of_dvd_right hd' (c i₀ ^ 2))
      rwa [e2, add_sub_cancel_right] at this
    rcases hp.dvd_or_dvd h3 with h | h
    · exact hodd h
    · rcases hp.dvd_or_dvd h with h | h
      · exact hA j (hp.dvd_of_dvd_pow h)
      · exact hA k (hp.dvd_of_dvd_pow h)

end SplitVector

/-! ### Diagonal forms -/

section Diagonal

variable {N : ℕ}

theorem eval_diag_gen {R : Type*} [CommRing R] (a : Fin N → R) (z : Fin N → R) :
    (QuadForm.diag a).eval z = ∑ i, a i * z i ^ 2 := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp; ring

theorem hessian_diag_mulVec {R : Type*} [CommRing R] (a : Fin N → R) (z : Fin N → R) (k : Fin N) :
    ((QuadForm.diag a).hessian *ᵥ z) k = 2 * a k * z k := by
  simp only [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add, mulVec_diagonal]
  ring

/-- **Jordan diagonalization at $\mathfrak p \nmid 2$** (Hanke 2004, Lemma 2.1, p. 355; `exists_jordanForm_isGLEquiv`):
$Q_o\circ W = \langle a_0, \dots, a_{N-1}\rangle$ with $W \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$, all $a_i \ne 0$. -/
theorem exists_diag_compMat (hodd : ¬ NF.π v ∣ 2) (Qo : QuadForm 𝔬 N) (hQo : Qo.Nondegenerate) :
    ∃ (W : Matrix (Fin N) (Fin N) 𝔬) (a : Fin N → 𝔬), IsUnit W.det ∧ (∀ i, a i ≠ 0) ∧
      Qo.compMat W = QuadForm.diag a := by
  classical
  have hπ := NF.irreducible_π v
  have h2 : ¬ NF.π v ^ 2 ∣ 2 := fun h => hodd ((dvd_pow_self _ two_ne_zero).trans h)
  obtain ⟨Q', P, ν, hJ, hP, U, hU, heval⟩ := exists_jordanForm_isGLEquiv Qo hQo (NF.π v) hπ h2
  have hP0 : P = ∅ := hP hodd
  subst hP0
  have hdiag : Q' = QuadForm.diag fun i => Q'.coeff i i := by
    refine QuadForm.ext (Matrix.ext fun i j => ?_)
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [hJ.2.2.2.1 i j h (by simp), ite_eq_right_iff.mpr (fun h' => absurd h' h.ne)]
    · subst h; simp
    · rw [Q'.upper h, ite_eq_right_iff.mpr (fun h' => absurd h' h.ne')]
  refine ⟨U, fun i => Q'.coeff i i, hU, fun i => ?_, ?_⟩
  · obtain ⟨u, hu, hu'⟩ := hJ.2.2.2.2.2 i (by simp [IsPaired])
    show Q'.coeff i i ≠ 0
    rw [hu]; exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hu'.ne_zero
  · rw [← hdiag]
    exact eq_of_eval_eq fun x => by rw [eval_compMat, heval]

end Diagonal

/-! ### The exceptional binary step for the sublattice $\{c\cdot y \equiv 0\}$ -/

section SpecialKer

theorem simMat_mulVec (u2 μ μi : 𝔬) (x : Fin 2 → 𝔬) :
    simMat v u2 μ μi *ᵥ x = ![u2 * (1 + NF.π v) * x 0 + u2 * μi * (1 - NF.π v) * x 1,
      u2 * μ * (1 - NF.π v) * x 0 + u2 * (1 + NF.π v) * x 1] := by
  funext i
  fin_cases i <;> simp [simMat, mulVec, dotProduct, Fin.sum_univ_two]

/-- The exceptional binary step, first coordinate minimal. -/
theorem alphaLaw_special_ker0 (hodd : ¬ NF.π v ∣ 2) {a₀ a₁ c₀ c₁ r : 𝔬} (ha0 : a₀ ≠ 0) (hc1 : ¬ NF.π v ∣ c₁)
    (hr : ¬ NF.π v ∣ r) (har : a₁ = a₀ * r) (hrel : NF.π v ∣ c₁ ^ 2 + c₀ ^ 2 * r)
    (L : Matrix (Fin 2) (Fin 2) 𝔬) (hL : L.det ≠ 0)
    (hrange : ∀ y, (∃ x, L *ᵥ x = y) ↔ NF.π v ∣ c₀ * y 0 + c₁ * y 1) :
    AlphaLawAt v (QuadForm.diag ![a₀, a₁]) L hL := by
  classical
  have hπ := NF.irreducible_π v
  have hp := hπ.prime
  have h2u : IsUnit (2 : 𝔬) := dvr_isUnit_of_not_dvd hπ hodd
  set u2 : 𝔬 := ((h2u.unit⁻¹ : 𝔬ˣ) : 𝔬)
  have h2 : 2 * u2 = 1 := h2u.mul_val_inv
  have hc1u : IsUnit c₁ := dvr_isUnit_of_not_dvd hπ hc1
  set ci1 : 𝔬 := ((hc1u.unit⁻¹ : 𝔬ˣ) : 𝔬)
  have hc1i : c₁ * ci1 = 1 := hc1u.mul_val_inv
  set μ₀ := -c₀ * ci1
  -- Hensel: an exact root of `r μ² = -1`
  have hx : NF.π v ^ 1 ∣ (QuadForm.diag ![r]).eval ![μ₀] - (-1) := by
    rw [eval_diag_gen, pow_one]
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    have : r * μ₀ ^ 2 - -1 = ci1 ^ 2 * (c₁ ^ 2 + c₀ ^ 2 * r) := by
      linear_combination (-(c₁ * ci1 + 1)) * hc1i
    rw [this]; exact dvd_mul_of_dvd_right hrel _
  have he : NF.π v ^ 0 ∣ 2 * (-1 : 𝔬) := by simp
  have he' : ¬ NF.π v ^ (0 + 1) ∣ 2 * (-1 : 𝔬) := by
    rw [zero_add, pow_one, mul_neg_one, dvd_neg]; exact hodd
  obtain ⟨y, hy, hyμ⟩ := exists_eval_eq_of_dvd hπ (QuadForm.diag ![r]) he he' le_rfl ![μ₀] hx
  set μ := y 0
  have hrμ : r * μ ^ 2 = -1 := by
    rw [eval_diag_gen] at hy; simpa using hy
  have hμμ₀ : NF.π v ∣ μ - μ₀ := by simpa using hyμ 0
  set μi := -(r * μ)
  have hμ : μ * μi = 1 := by linear_combination -hrμ
  have ha : a₀ + μ ^ 2 * a₁ = 0 := by rw [har]; linear_combination a₀ * hrμ
  have ha1 : a₁ ≠ 0 := by rw [har]; exact mul_ne_zero ha0 (fun h => hr (h ▸ dvd_zero _))
  have hσ : (simMat v u2 μ μi).det ≠ 0 := by rw [det_simMat v h2 hμ]; exact hπ.ne_zero
  -- the two descriptions of the sublattice
  have hA : ∀ w : Fin 2 → 𝔬, NF.π v ∣ c₀ * w 0 + c₁ * w 1 ↔ NF.π v ∣ w 1 - μ * w 0 := by
    intro w
    obtain ⟨t, ht⟩ := hμμ₀
    have e : c₀ * w 0 + c₁ * w 1 = c₁ * (w 1 - μ * w 0) + NF.π v * (c₁ * t * w 0) := by
      linear_combination (w 0 * c₁) * ht + (-(c₀ * w 0)) * hc1i
    rw [e, dvd_add_left (dvd_mul_right _ _)]
    exact ⟨fun h => (hp.dvd_or_dvd h).resolve_left hc1, fun h => dvd_mul_of_dvd_right h _⟩
  have hB : ∀ x, NF.π v ∣ (simMat v u2 μ μi *ᵥ x) 1 - μ * (simMat v u2 μ μi *ᵥ x) 0 := by
    intro x
    rw [simMat_mulVec]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    exact ⟨x 1 - μ * x 0, by linear_combination (NF.π v * (x 1 - μ * x 0)) * h2 + (-(u2 * (1 - NF.π v) * x 1)) * hμ⟩
  have hC : ∀ w : Fin 2 → 𝔬, NF.π v ∣ w 1 - μ * w 0 → ∃ x, simMat v u2 μ μi *ᵥ x = w := by
    rintro w ⟨t, ht⟩
    refine ⟨![w 0 - μi * (u2 * (1 - NF.π v)) * t, μ * w 0 + u2 * (1 + NF.π v) * t], ?_⟩
    rw [simMat_mulVec]
    funext i
    fin_cases i <;> simp
    · linear_combination (w 0) * h2 + (u2 * (1 - NF.π v) * w 0) * hμ
    · linear_combination (μ * w 0 + NF.π v * t * (2 * u2 + 1)) * h2 + (-(u2 ^ 2 * (1 - NF.π v) ^ 2 * t)) * hμ - ht
  rw [alphaLaw_of_range_eq v _ L (simMat v u2 μ μi) hL hσ (fun x => ?_) (fun x => ?_)]
  · exact alphaLaw_special v h2 hμ ha1 ha hσ
  · exact hC _ ((hA _).mp ((hrange _).mp ⟨x, rfl⟩))
  · exact (hrange _).mpr ((hA _).mpr (hB x))

theorem fun_fin_two {R : Type*} (a : Fin 2 → R) : a = ![a 0, a 1] := by
  funext i; fin_cases i <;> rfl

/-- $S = \begin{pmatrix}0&1\\1&0\end{pmatrix}$. -/
def swapMat : Matrix (Fin 2) (Fin 2) 𝔬 := !![0, 1; 1, 0]

theorem swapMat_mul_self : swapMat v * swapMat v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapMat_mulVec (y : Fin 2 → 𝔬) : swapMat v *ᵥ y = ![y 1, y 0] := by
  funext i; fin_cases i <;> simp [swapMat, mulVec, dotProduct, Fin.sum_univ_two]

theorem diag_compMat_swap (a₀ a₁ : 𝔬) : (QuadForm.diag ![a₀, a₁]).compMat (swapMat v) = QuadForm.diag ![a₁, a₀] := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat, eval_diag_two, eval_diag_two, swapMat_mulVec]
  simp; ring

/-- **The exceptional binary step**, either coordinate minimal. -/
theorem alphaLaw_special_ker (hodd : ¬ NF.π v ∣ 2) (a c : Fin 2 → 𝔬) (ha : ∀ i, a i ≠ 0) {i₀ j : Fin 2} (hij : i₀ ≠ j)
    (hcj : ¬ NF.π v ∣ c j) {r : 𝔬} (hr : ¬ NF.π v ∣ r) (har : a j = a i₀ * r)
    (hrel : NF.π v ∣ c j ^ 2 + c i₀ ^ 2 * r) (L : Matrix (Fin 2) (Fin 2) 𝔬) (hL : L.det ≠ 0)
    (hrange : ∀ y, (∃ x, L *ᵥ x = y) ↔ NF.π v ∣ c ⬝ᵥ y) :
    AlphaLawAt v (QuadForm.diag a) L hL := by
  classical
  have hdot : ∀ y : Fin 2 → 𝔬, c ⬝ᵥ y = c 0 * y 0 + c 1 * y 1 := fun y => by
    simp [dotProduct, Fin.sum_univ_two]
  rw [fun_fin_two a]
  fin_cases i₀ <;> fin_cases j
  · exact absurd rfl hij
  · exact alphaLaw_special_ker0 v hodd (ha 0) hcj hr har hrel L hL fun y => by rw [hrange, hdot]; exact Iff.rfl
  · -- swap the coordinates
    have hS : IsUnit (swapMat v).det := by
      rw [show (swapMat v).det = -1 by simp [swapMat, det_fin_two_of]]; exact isUnit_one.neg
    have hSL : (swapMat v * L).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hS.ne_zero hL
    rw [← alphaLaw_conj v _ (swapMat v) (swapMat v) hS (swapMat_mul_self v) L hL hSL, diag_compMat_swap]
    refine alphaLaw_special_ker0 v hodd (ha 1) hcj hr har hrel _ hSL fun y => ?_
    have e : (∃ x, (swapMat v * L) *ᵥ x = y) ↔ ∃ x, L *ᵥ x = swapMat v *ᵥ y := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← hx, mulVec_mulVec, ← Matrix.mul_assoc, swapMat_mul_self, Matrix.one_mul]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [← mulVec_mulVec, hx, mulVec_mulVec, swapMat_mul_self, one_mulVec]⟩
    rw [e, hrange, hdot, swapMat_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [add_comm]
    exact Iff.rfl
  · exact absurd rfl hij

end SpecialKer

/-! ### The index-$q$ step -/

section IndexQ

variable {n : ℕ}

theorem cornerMat_mulVec' {R : Type*} [CommRing R] (c : R) (x : Fin (n + 1) → R) :
    cornerMat c (1 : Matrix (Fin n) (Fin n) R) *ᵥ x = Fin.cons (c * x 0) (Fin.tail x) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  rw [cornerMat_mulVec, one_mulVec]

/-- **The index-$q$ step** ($\mathfrak p \nmid 2$): the law for $\mathrm{diag}(\varpi, 1, \dots, 1)$ in rank $n + 2$, from the law in rank
$n + 1$. *Proof:* diagonalize ($Q\circ W = \langle a_i\rangle$, `exists_diag_compMat`); in these coordinates the sublattice is
$\{y : c\cdot y \equiv 0\}$, $c$ = the first row of $W$; a split vector in it (`exists_split_or_special`) and `alphaLaw_of_split`, or the
exceptional binary case (`alphaLaw_special_ker`). -/
theorem alphaLaw_index_q (hodd : ¬ NF.π v ∣ 2)
    (IH : ∀ (Q'' : QuadForm 𝔬 (n + 1)) (P'' : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬) (hP'' : P''.det ≠ 0),
      Q''.Nondegenerate → AlphaLawAt v Q'' P'' hP'')
    (Q : QuadForm 𝔬 (n + 2)) (hQ : Q.Nondegenerate)
    (hD : (cornerMat (NF.π v) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬)).det ≠ 0) :
    AlphaLawAt v Q (cornerMat (NF.π v) 1) hD := by
  classical
  have hπ := NF.irreducible_π v
  obtain ⟨W, a, hW, ha, hQW⟩ := exists_diag_compMat v hodd Q hQ
  set Winv := W⁻¹
  have hWW : W * Winv = 1 := Matrix.mul_nonsing_inv W hW
  have hWW' : Winv * W = 1 := Matrix.nonsing_inv_mul W hW
  set D := cornerMat (NF.π v) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬)
  have hL : (Winv * D).det ≠ 0 := by
    rw [det_mul]; exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det W hW).ne_zero hD
  rw [← alphaLaw_conj v Q W Winv hW hWW D hD hL, hQW]
  set c : Fin (n + 2) → 𝔬 := fun j => W 0 j
  have hcW : ∀ y, c ⬝ᵥ y = (W *ᵥ y) 0 := fun y => rfl
  have hrange : ∀ y, (∃ x, (Winv * D) *ᵥ x = y) ↔ NF.π v ∣ c ⬝ᵥ y := by
    intro y
    rw [hcW]
    constructor
    · rintro ⟨x, rfl⟩
      rw [mulVec_mulVec, ← Matrix.mul_assoc, hWW, Matrix.one_mul, cornerMat_mulVec']
      exact ⟨x 0, by simp⟩
    · rintro ⟨t, ht⟩
      refine ⟨Fin.cons t (Fin.tail (W *ᵥ y)), ?_⟩
      rw [← mulVec_mulVec, cornerMat_mulVec']
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [← ht, Fin.cons_self_tail, mulVec_mulVec, hWW', one_mulVec]
  have hnd : (QuadForm.diag a).Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_diag]
    exact mul_ne_zero (pow_ne_zero _ (NF.two_ne_zero' v)) (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
  rcases exists_split_or_special v hodd a ha c with ⟨z, hzc, hz0, hzd⟩ | ⟨hn, i₀, j, hij, -, hcj, r, hr, har, hrel⟩
  · refine alphaLaw_of_split v (QuadForm.diag a) hnd (Winv * D) hL z ((hrange z).mpr hzc)
      (by rw [eval_diag_gen]; exact hz0) (fun i => ?_) IH
    rw [eval_diag_gen, hessian_diag_mulVec, mul_assoc]
    exact mul_dvd_mul_left 2 (hzd i)
  · subst hn
    exact alphaLaw_special_ker v hodd a c ha hij hcj hr har hrel _ hL hrange

theorem cornerMat_one_mul_apply {R : Type*} [CommRing R] (c : R) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (i j : Fin (n + 1)) : (cornerMat c (1 : Matrix (Fin n) (Fin n) R) * X) i j = (if i = 0 then c else 1) * X i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [cornerMat]
  · simp only [cornerMat, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero, zero_mul, zero_add,
      Fin.succ_ne_zero, if_false, one_mul]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Matrix.one_apply, Ne.symm hk]) (by simp)]
    simp

/-- **Splitting off an index-$q$ step**: if $\varpi \mid \det P$, then $P = U\,\mathrm{diag}(\varpi, 1, \dots, 1)\,P_2$ with
$U \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$ (a nonzero row vector in the left kernel of $P \bmod \varpi$, extended to a basis). -/
theorem exists_factor_index_q (P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬) (hdvd : NF.π v ∣ P.det) :
    ∃ U Uinv P₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬, U * Uinv = 1 ∧ Uinv * U = 1 ∧
      P = U * cornerMat (NF.π v) (1 : Matrix (Fin n) (Fin n) 𝔬) * P₂ := by
  classical
  have hπ := NF.irreducible_π v
  set φ := IsLocalRing.residue 𝔬
  have hmax : ∀ x : 𝔬, φ x = 0 ↔ NF.π v ∣ x := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  have hdet : (P.map φ).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hmax]; exact hdvd
  obtain ⟨cb, hcb, hcbP⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  choose c hc using fun j => IsLocalRing.residue_surjective (cb j)
  obtain ⟨j, hj⟩ : ∃ j, cb j ≠ 0 := by
    by_contra h; push_neg at h; exact hcb (funext h)
  have hcj : IsUnit (c j) := by
    by_contra hu
    apply hj
    rw [← hc j]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hu
  obtain ⟨V, hV, hVe⟩ := exists_unit_mulVec_e₀ c ⟨j, hcj⟩
  set Uinv := Vᵀ
  have hUinv : IsUnit Uinv.det := by rw [det_transpose]; exact hV
  set U := Uinv⁻¹
  have hrow : ∀ l, Uinv 0 l = c l := by
    intro l
    have := congrFun hVe l
    rw [e₀_eq_single, mulVec_single_one] at this
    exact this
  set M := Uinv * P
  have hM0 : ∀ k, NF.π v ∣ M 0 k := by
    intro k
    rw [← hmax]
    have h1 := congrFun hcbP k
    have h2 : φ (M 0 k) = (cb ᵥ* P.map φ) k := by
      simp only [M, Matrix.mul_apply, vecMul, dotProduct, map_sum, map_mul, hrow, Matrix.map_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hc i]
    rw [h2, h1]; rfl
  choose t ht using hM0
  set P₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬 := Matrix.of fun i k => if i = 0 then t k else M i k
  have hM : cornerMat (NF.π v) (1 : Matrix (Fin n) (Fin n) 𝔬) * P₂ = M := by
    ext i k
    rw [cornerMat_one_mul_apply]
    by_cases hi : i = 0
    · subst hi; simp [P₂, ht k]
    · simp [P₂, hi]
  refine ⟨U, Uinv, P₂, Matrix.nonsing_inv_mul Uinv hUinv, Matrix.mul_nonsing_inv Uinv hUinv, ?_⟩
  rw [Matrix.mul_assoc, hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Uinv hUinv, Matrix.one_mul]

end IndexQ

/-! ### The law at the non-dyadic primes -/

section Main

theorem alphaLaw_one {N : ℕ} (Qo : QuadForm 𝔬 N) (h1 : (1 : Matrix (Fin N) (Fin N) 𝔬).det ≠ 0) :
    AlphaLawAt v Qo 1 h1 := by
  have hg : glOf v (1 : Matrix (Fin N) (Fin N) 𝔬) h1 = 1 :=
    Units.ext (by rw [glOf_val, Matrix.map_one _ (map_zero _) (map_one _)]; rfl)
  unfold AlphaLawAt
  rw [hg, locAct_one, relRatio_self, compMat_one, det_one]
  simp

theorem alphaLaw_unit {N : ℕ} (Qo : QuadForm 𝔬 N) (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0)
    (hu : IsUnit P.det) : AlphaLawAt v Qo P hP := by
  have h1 : (1 : Matrix (Fin N) (Fin N) 𝔬).det ≠ 0 := by simp
  have h1P : ((1 : Matrix (Fin N) (Fin N) 𝔬) * P).det ≠ 0 := by rw [Matrix.one_mul]; exact hP
  rw [← alphaLaw_congr v Qo (Matrix.one_mul P) h1P hP, alphaLaw_mul_right v Qo 1 P h1 hu h1P]
  exact alphaLaw_one v Qo h1

/-- **The $\alpha$ transformation law at every prime $\mathfrak p \nmid 2$** (purely by counting): for every nondegenerate
integral $Q_o$ in $N$ variables and every integral $P$ with $\det P \ne 0$,
$$r\big(O(P\mathfrak o_\mathfrak p^N), O(\mathfrak o_\mathfrak p^N)\big)\,\beta_\mathfrak p(Q_o, Q_o) = \beta_\mathfrak p(Q_o\circ P, Q_o\circ P)\,\|\det P\|_\mathfrak p^{N+1}.$$
*Proof:* induction on $N$, then on $\mathrm{ord}\det P$: `exists_factor_index_q`, the cocycle `alphaLaw_mul`, the index-$q$ step
`alphaLaw_index_q` (rank $\ge 2$) or `alphaLaw_scalar` (rank 1); units by `alphaLaw_unit`.

*Update (generalization of Hanke 2004, §3, pp. 358–361):* Hanke's reduction maps $\pi_Z$, $\pi_{B'}$, $\pi_{B''}$ compare solution
counts of $Q$ and of the rescaled forms $Q'$, $Q''$ inside one Jordan splitting; here the comparison is made for an arbitrary
sublattice $P\mathfrak o^N$, with the stabilizer index ratio as the correction factor. -/
@[kb "weil1982" "§3.4 (Haar measures of lattice stabilizers at p ∤ 2, finite form) [unverified]"]
theorem alphaLaw_odd (hodd : ¬ NF.π v ∣ 2) :
    ∀ (N : ℕ) (Qo : QuadForm 𝔬 N) (P : Matrix (Fin N) (Fin N) 𝔬) (hP : P.det ≠ 0),
      Qo.Nondegenerate → AlphaLawAt v Qo P hP := by
  classical
  have hπ := NF.irreducible_π v
  intro N
  induction N with
  | zero =>
    intro Qo P hP _
    exact alphaLaw_unit v Qo P hP (by rw [Matrix.det_isEmpty]; exact isUnit_one)
  | succ n IHn =>
    -- induction on the exponent of `det P`
    have claim : ∀ t : ℕ, ∀ (Qo : QuadForm 𝔬 (n + 1)) (P : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝔬)
        (hP : P.det ≠ 0), Qo.Nondegenerate → NF.π v ^ t ∣ P.det → ¬ NF.π v ^ (t + 1) ∣ P.det →
          AlphaLawAt v Qo P hP := by
      intro t
      induction t with
      | zero =>
        intro Qo P hP _ _ h1
        exact alphaLaw_unit v Qo P hP (dvr_isUnit_of_not_dvd hπ (by simpa using h1))
      | succ t IHt =>
        intro Qo P hP hQo ht ht'
        obtain ⟨U, Uinv, P₂, hUU, hUU', hfac⟩ :=
          exists_factor_index_q v P ((dvd_pow_self _ (Nat.succ_ne_zero t)).trans ht)
        set D := cornerMat (NF.π v) (1 : Matrix (Fin n) (Fin n) 𝔬)
        have hUu : IsUnit U.det := by
          have := congrArg Matrix.det hUU; rw [det_mul, det_one] at this
          exact ⟨⟨U.det, Uinv.det, this, by rw [mul_comm]; exact this⟩, rfl⟩
        have hUinvu : IsUnit Uinv.det := by
          have := congrArg Matrix.det hUU; rw [det_mul, det_one] at this
          exact ⟨⟨Uinv.det, U.det, by rw [mul_comm]; exact this, this⟩, rfl⟩
        have hdetD : D.det = NF.π v := by rw [det_cornerMat, det_one, mul_one]
        have hD : D.det ≠ 0 := by rw [hdetD]; exact hπ.ne_zero
        have hdetP : P.det = U.det * NF.π v * P₂.det := by rw [hfac, det_mul, det_mul, hdetD]
        have hP₂ : P₂.det ≠ 0 := fun h => hP (by rw [hdetP, h, mul_zero])
        have hUD : (U * D).det ≠ 0 := by rw [det_mul, hdetD]; exact mul_ne_zero hUu.ne_zero hπ.ne_zero
        -- the exponent of `det P₂`
        have hu' : IsUnit (U.det) := hUu
        have h₂ : NF.π v ^ t ∣ P₂.det := by
          rw [hdetP, show U.det * NF.π v * P₂.det = NF.π v * (U.det * P₂.det) by ring, pow_succ',
            mul_dvd_mul_iff_left hπ.ne_zero] at ht
          exact (hu'.dvd_mul_left).mp ht
        have h₂' : ¬ NF.π v ^ (t + 1) ∣ P₂.det := by
          intro h; apply ht'
          rw [hdetP, pow_succ, mul_comm (U.det), mul_assoc, mul_comm (NF.π v ^ (t + 1))]
          exact mul_dvd_mul (dvd_refl _) (dvd_mul_of_dvd_right h _)
        -- the index-`q` factor
        have hstep : AlphaLawAt v Qo (U * D) hUD := by
          have hQ' : (Qo.compMat U).compMat Uinv = Qo := by rw [compMat_mul, hUU, compMat_one]
          have hQ'nd : (Qo.compMat U).Nondegenerate := nondegenerate_compMat v hQo hUu.ne_zero
          suffices key : AlphaLawAt v (Qo.compMat U) D hD by
            have := (alphaLaw_conj v (Qo.compMat U) Uinv U hUinvu hUU' D hD hUD).mpr key
            rwa [hQ'] at this
          rcases n with _ | m
          · have hscal : D = NF.π v • (1 : Matrix (Fin 1) (Fin 1) 𝔬) := by
              ext i j; fin_cases i; fin_cases j; simp [D, cornerMat]
            have hs : ((NF.π v • (1 : Matrix (Fin 1) (Fin 1) 𝔬))).det ≠ 0 := by rw [← hscal]; exact hD
            rw [alphaLaw_congr v _ hscal hD hs]
            exact alphaLaw_scalar v _ hQ'nd (NF.π v) hπ.ne_zero hs
          · exact alphaLaw_index_q v hodd (IHn) _ hQ'nd hD
        have hQUD : (Qo.compMat (U * D)).Nondegenerate := nondegenerate_compMat v hQo hUD
        have hrest := IHt (Qo.compMat (U * D)) P₂ hP₂ hQUD h₂ h₂'
        have hUDP : ((U * D) * P₂).det ≠ 0 := by rw [← hfac]; exact hP
        have := alphaLaw_mul v Qo (U * D) P₂ hUD hP₂ hUDP hstep hrest
        exact (alphaLaw_congr v Qo hfac.symm hUDP hP).mp this
    intro Qo P hP hQo
    obtain ⟨t, ht, ht'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hP
    exact claim t Qo P hP hQo ht ht'

end Main

end QuadFormsKB.Tamagawa
