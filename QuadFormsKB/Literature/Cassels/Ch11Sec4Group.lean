/-
# Cassels, Chapter 11, §4: the map $c \mapsto g(c)$ and Lemma 4.3

**Layer:** Cassels' group $G = R/ST$ = `CasselsG Q hQ L P` of a finite set $P$ of primes (`Ch11Sec3Group.lean`).

**Defines** $g(c) \in G$, the image of $c \in F^\times$ under $F^\times \to R = \prod_{p\in P}F_p^\times \to G$
((4.5), p. 216), `casselsg`.

**Proves** Cassels' Lemma 4.3 (pp. 216–217), over $\mathbb Q$:
* (i) (`casselsg_eq_of_isSquare`, `casselsg_eq_of_cong`): if $c_1/c_2$ is a square in $\mathbb Q_p$ for all
  $p \in P$, then $g(c_1) = g(c_2)$; in particular this holds under the congruence conditions
  $\lvert c_1 - c_2\rvert_p < \lvert c_1\rvert_p$ ($p \in P$, $p \ne 2$) and $\lvert c_1 - c_2\rvert_2 \le
  \lvert 8c_1\rvert_2$ ($2 \in P$). *Reconstruction:* the scan has lost the conditions of (i) (only "$(p \in P, p \ne 2)$"
  survives); they are reconstructed from the proof ("the given conditions imply that $c_1/c_2 \in
  (\mathbb Q_p^\times)^2$ (all $p \in P$)") as the usual congruences modulo $p$ and modulo $8$.
* (ii) (`exists_casselsg_eq`): for $n \ge 3$, every $g^* \in G$ is $g(c)$ for some positive integer $c$ prime to a
  given positive integer $M$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3Group
import QuadFormsKB.Literature.Cassels.Ch11Thm13Int

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Cassels' $g(c)$** (Ch. 11, (4.5), p. 216): the image of $c \in F^\times$ under the composite map
$F^\times \to R = \prod_{p\in P}F_p^\times \to G = R/ST$ (the first map diagonal, `casselsDiag`). -/
@[kb "cassels1978" "Ch. 11, (4.5), p. 216"]
def casselsg (hQ : Q.Nondegenerate) (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F))) (c : Fˣ) :
    CasselsG Q hQ L P :=
  QuotientGroup.mk (casselsDiag P c)

/-- If every component of $r \in R$ is a square then $r \in S$ (as $R^2 \subseteq S$). -/
theorem mem_casselsS_of_isSquare (hQ : Q.Nondegenerate) (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (r : CasselsR P) (h : ∀ v : P, IsSquare ((r v : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)) :
    r ∈ casselsS Q hQ L P := by
  choose w hw using h
  have hw0 : ∀ v, w v ≠ 0 := fun v h0 => by
    have := (r v).ne_zero
    rw [hw v, h0, mul_zero] at this
    exact this rfl
  let s : CasselsR P := fun v => Units.mk0 (w v) (hw0 v)
  have : r = s ^ 2 := by
    funext v
    apply Units.ext
    simp [s, sq, hw v]
  rw [this]
  exact sq_mem_casselsS Q hQ L P s

/-- **Prescribed valuations on $P$, trivial outside** ($\mathcal O_F$ a PID): for any $k : \mathrm{Spec} \to \mathbb Z$
there is $s \in F^\times$ with $v(s) = e^{k(v)}$ for $v \in P$ and $v(s) = 1$ for $v \notin P$. -/
theorem exists_scalar_val [IsPrincipalIdealRing (𝓞 F)] (P : Finset (HeightOneSpectrum (𝓞 F)))
    (k : HeightOneSpectrum (𝓞 F) → ℤ) :
    ∃ s : Fˣ, (∀ v ∈ P, Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = WithZero.exp (k v)) ∧
      ∀ v ∉ P, Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = 1 := by
  classical
  let s0 : F := ∏ w ∈ P, (algebraMap (𝓞 F) F (primeGen w)) ^ (-(k w))
  have hs0 : s0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ =>
    zpow_ne_zero _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (primeGen_ne_zero w))
  have hvs : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) s0) =
      ∏ w ∈ P, (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (primeGen w))) ^ (-(k w)) := by
    intro v
    simp only [s0]
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, map_zpow₀, ← IsScalarTower.algebraMap_apply]
  have hother : ∀ v : HeightOneSpectrum (𝓞 F), ∀ w ∈ P, w ≠ v →
      (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (primeGen w))) ^ (-(k w)) = 1 := by
    intro v w _ hwv
    rw [valued_algebraMap_int, intValuation_primeGen_of_ne v (Ne.symm hwv), _root_.one_zpow]
  refine ⟨Units.mk0 s0 hs0, fun v hv => ?_, fun v hv => ?_⟩
  · simp only [Units.val_mk0]
    rw [hvs v, Finset.prod_eq_single_of_mem v hv (hother v), valued_algebraMap_int, intValuation_primeGen_self,
      ← WithZero.exp_zsmul]
    congr 1
    simp
  · simp only [Units.val_mk0]
    rw [hvs v]
    exact Finset.prod_eq_one fun w hw => hother v w hw (fun hwv => hv (hwv ▸ hw))

section Rat

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Cassels, Lemma 4.3 (i)** (Ch. 11, p. 217), in the form of its proof: *if $c_1/c_2 \in (\mathbb Q_p^\times)^2$
for all $p \in P$, then $g(c_1) = g(c_2)$* (over a number field). -/
@[kb "cassels1978" "Ch. 11, Lemma 4.3 (i), p. 217 (the step c₁/c₂ ∈ (ℚ_p^×)², over a number field)"]
theorem casselsg_eq_of_isSquare (hQ : Q.Nondegenerate) (L : Lat F n) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (c₁ c₂ : Fˣ) (h : ∀ v ∈ P, IsSquare (algebraMap F (v.adicCompletion F) ((c₁ : F) / c₂))) :
    casselsg Q hQ L P c₁ = casselsg Q hQ L P c₂ := by
  rw [casselsg, casselsg, QuotientGroup.eq]
  refine Subgroup.mem_sup_left (mem_casselsS_of_isSquare Q hQ L P _ fun v => ?_)
  obtain ⟨w, hw⟩ := h v.1 v.2
  refine ⟨w⁻¹, ?_⟩
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, casselsDiag_apply]
  rw [map_div₀] at hw
  rw [← mul_inv, ← hw, inv_div, div_eq_inv_mul]

/-! ### Squares in $\mathbb Q_p$ from congruences -/

section Hensel

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.NF

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem val_natCast_eq_one' (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) (h : (k : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v ((k : ℕ) : v.adicCompletion ℚ) = 1 := by
  have hπ : ¬ π v ∣ ι v (k : 𝓞 ℚ) := by rwa [π_dvd_ι_iff]
  have hu : IsUnit (ι v (k : 𝓞 ℚ)) := DVR.dvr_isUnit_of_not_dvd (irreducible_π v) hπ
  have := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
  rw [map_natCast] at this
  simpa using this

/-- $\lvert t - 1\rvert < 1$ forces $\lvert t\rvert = 1$. -/
theorem valued_eq_one_of_sub_one_lt {t : v.adicCompletion ℚ} (ht : Valued.v (t - 1) < 1) : Valued.v t = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (Valued.v : Valuation (v.adicCompletion ℚ) _) (x := t - 1) (y := 1)
    (by simpa using ht)
  rw [sub_add_cancel] at h
  rw [h, map_one]

/-- **Hensel, odd $p$:** $t \equiv 1 \bmod \mathfrak m$ is a square in $\mathbb Q_p$, $p$ odd. -/
theorem isSquare_of_val_sub_one_lt_odd (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) {t : v.adicCompletion ℚ}
    (ht : Valued.v (t - 1) < 1) : IsSquare t := by
  have ht1 := valued_eq_one_of_sub_one_lt ht
  let T : v.adicCompletionIntegers ℚ := ⟨t, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ht1.le⟩
  have hmon : (Polynomial.X ^ 2 - Polynomial.C T : Polynomial (v.adicCompletionIntegers ℚ)).Monic := by
    monicity!
  have h2u : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have := val_natCast_eq_one' v 2 (by simpa using h2)
    have e2 : ((2 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 2 :=
      map_ofNat (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) 2
    rw [e2]
    simpa using this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ 2 - Polynomial.C T) hmon 1
    (by
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      intro h
      have e : ((1 - T : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = -(t - 1) := by
        push_cast [T]; ring
      rw [e, Valuation.map_neg] at h
      exact absurd ht (by rw [h]; exact lt_irrefl _))
    (by
      have e : (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C T :
          Polynomial (v.adicCompletionIntegers ℚ))).eval 1 = 2 := by
        simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow] <;> norm_num
      rw [e]; exact h2u)
  refine ⟨(a : v.adicCompletion ℚ), ?_⟩
  have h : a ^ 2 = T := by
    simpa [sub_eq_zero] using ha
  have := congrArg (fun x : v.adicCompletionIntegers ℚ => (x : v.adicCompletion ℚ)) h
  simpa [sq, T] using this.symm

/-- **Hensel, $p = 2$:** $\lvert t - 1\rvert \le \lvert 8\rvert$ implies $t$ is a square in $\mathbb Q_2$. -/
theorem isSquare_of_val_sub_one_le_eight (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {t : v.adicCompletion ℚ}
    (ht : Valued.v (t - 1) ≤ Valued.v (8 : v.adicCompletion ℚ)) : IsSquare t := by
  have h8 : (8 : v.adicCompletion ℚ) ≠ 0 := by norm_num
  have hv8 : Valued.v (8 : v.adicCompletion ℚ) ≠ 0 := by simpa using h8
  have hm : Valued.v ((t - 1) / 8) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr hv8)).mpr ht
  let M : v.adicCompletionIntegers ℚ := ⟨(t - 1) / 8, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hm⟩
  obtain ⟨s, hs⟩ := exists_sq_one_add_eight h2 M
  refine ⟨(s : v.adicCompletion ℚ), ?_⟩
  have := congrArg (fun x : v.adicCompletionIntegers ℚ => (x : v.adicCompletion ℚ)) hs
  have e8 : ((8 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 8 :=
    map_ofNat (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) 8
  simp only [M] at this
  push_cast at this
  rw [e8] at this
  rw [← sq, this]
  field_simp
  ring

open Classical in
/-- The modulus used at $v$: $8$ if $v \mid 2$, else the prime $p_v$ of $v$. -/
def casselsMod (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  if (2 : 𝓞 ℚ) ∈ v.asIdeal then 8 else Rat.HeightOneSpectrum.natGenerator v

theorem casselsMod_pos (v : HeightOneSpectrum (𝓞 ℚ)) : 0 < casselsMod v := by
  unfold casselsMod
  split_ifs
  · norm_num
  · exact (Rat.HeightOneSpectrum.prime_natGenerator v).pos

theorem natGenerator_inj' {v w : HeightOneSpectrum (𝓞 ℚ)}
    (h : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w) : v = w :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem casselsMod_coprime {v w : HeightOneSpectrum (𝓞 ℚ)} (hvw : v ≠ w) : Nat.Coprime (casselsMod v) (casselsMod w) := by
  have hne : Rat.HeightOneSpectrum.natGenerator v ≠ Rat.HeightOneSpectrum.natGenerator w :=
    fun h => hvw (natGenerator_inj' h)
  have hpv := Rat.HeightOneSpectrum.prime_natGenerator v
  have hpw := Rat.HeightOneSpectrum.prime_natGenerator w
  unfold casselsMod
  by_cases h1 : (2 : 𝓞 ℚ) ∈ v.asIdeal <;> by_cases h2 : (2 : 𝓞 ℚ) ∈ w.asIdeal <;>
    simp only [h1, h2, ite_true, ite_false]
  · exact absurd (((two_mem_iff_natGenerator v).mp h1).trans ((two_mem_iff_natGenerator w).mp h2).symm) hne
  · have h3 : Rat.HeightOneSpectrum.natGenerator w ≠ 2 := fun h => h2 ((two_mem_iff_natGenerator w).mpr h)
    exact Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hpw).mpr (Ne.symm h3))
  · have h3 : Rat.HeightOneSpectrum.natGenerator v ≠ 2 := fun h => h1 ((two_mem_iff_natGenerator v).mpr h)
    exact (Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hpv).mpr (Ne.symm h3))).symm
  · exact (Nat.coprime_primes hpv hpw).mpr hne

theorem exp_neg_one_lt_one : (WithZero.exp (-((1 : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- Every element of $\mathbb Z_p$ is within $\mathfrak m$ of a rational integer. -/
theorem exists_int_approx (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletion ℚ) (hu : Valued.v u ≤ 1) :
    ∃ z : ℤ, Valued.v (u - (z : v.adicCompletion ℚ)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  let x : v.adicCompletionIntegers ℚ := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu⟩
  obtain ⟨r, hr⟩ := redHom_surjective v 1 (Ideal.Quotient.mk _ x)
  have hr' : π v ^ 1 ∣ x - ι v r := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hr.symm)
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) r
  have hzr : ι v r = (z : v.adicCompletionIntegers ℚ) := by
    have : (z : 𝓞 ℚ) = r := by
      rw [← Tamagawa.RatHeadline3.intEquiv_symm_intCast]
      exact RingEquiv.symm_apply_apply _ r
    rw [← this, map_intCast]
  rw [hzr] at hr'
  refine ⟨z, ?_⟩
  have := (mem_span_π_pow v 1 (x - (z : v.adicCompletionIntegers ℚ))).mp (Ideal.mem_span_singleton.mpr hr')
  simpa [x] using this

/-- If $\lvert u\rvert = 1$ and $\lvert u - z\rvert < 1$ then $p \nmid z$. -/
theorem not_dvd_of_approx (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletion ℚ) (hu : Valued.v u = 1)
    (z : ℤ) (hz : Valued.v (u - (z : v.adicCompletion ℚ)) ≤ WithZero.exp (-((1 : ℕ) : ℤ))) :
    ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ z := by
  intro hd
  have h1 : Valued.v (z : v.adicCompletion ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (valued_intCast_le_iff v z 1).mpr (by simpa using hd)
  have h2 : Valued.v u ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have : u = (u - (z : v.adicCompletion ℚ)) + z := by ring
    rw [this]
    exact Valuation.map_add_le _ hz h1
  rw [hu] at h2
  exact absurd h2 (not_le.mpr exp_neg_one_lt_one)

/-- **Local square classes via residues:** for $\lvert u\rvert_v = 1$ there is a residue $a$ modulo $q_v$, prime to
$q_v$, such that every integer $m \equiv a \bmod q_v$ has $m/u$ a square in $\mathbb Q_v$. -/
theorem exists_res (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletion ℚ) (hu : Valued.v u = 1) :
    ∃ a : ℕ, Nat.Coprime a (casselsMod v) ∧ ∀ m : ℤ, m ≡ (a : ℤ) [ZMOD (casselsMod v : ℤ)] →
      IsSquare ((m : v.adicCompletion ℚ) * u⁻¹) := by
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hu; exact zero_ne_one hu
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hq := casselsMod_pos v
  have hpq : Rat.HeightOneSpectrum.natGenerator v ∣ casselsMod v := by
    unfold casselsMod
    split_ifs with h2
    · rw [(two_mem_iff_natGenerator v).mp h2]; norm_num
    · exact dvd_rfl
  have hpq' : (casselsMod v) = Rat.HeightOneSpectrum.natGenerator v ∨ (casselsMod v = 8 ∧ Rat.HeightOneSpectrum.natGenerator v = 2) := by
    unfold casselsMod
    split_ifs with h2
    · exact Or.inr ⟨rfl, (two_mem_iff_natGenerator v).mp h2⟩
    · exact Or.inl rfl
  suffices H : ∃ z : ℤ, ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ z ∧
      ∀ m : ℤ, m ≡ z [ZMOD (casselsMod v : ℤ)] → IsSquare ((m : v.adicCompletion ℚ) * u⁻¹) by
    obtain ⟨z, hz, hsq⟩ := H
    have hqz : (casselsMod v : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have ha : (((z % (casselsMod v : ℤ)).toNat : ℕ) : ℤ) = z % (casselsMod v : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hqz)
    have hnd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (z % (casselsMod v : ℤ)).toNat := by
      intro hd
      have h1 : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ (((z % (casselsMod v : ℤ)).toNat : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hd
      rw [ha, Int.dvd_iff_emod_eq_zero, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr hpq),
        ← Int.dvd_iff_emod_eq_zero] at h1
      exact hz h1
    refine ⟨(z % (casselsMod v : ℤ)).toNat, ?_, fun m hm => hsq m ?_⟩
    · generalize (z % (casselsMod v : ℤ)).toNat = a at hnd ⊢
      rcases hpq' with h | ⟨h8, h2⟩
      · rw [h]
        exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
      · rw [h8]
        rw [h2] at hnd
        exact Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd).symm
    · refine hm.trans ?_
      rw [ha]
      exact Int.mod_modEq z _
  by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · have hp2 : Rat.HeightOneSpectrum.natGenerator v = 2 := (two_mem_iff_natGenerator v).mp h2
    have hq8 : casselsMod v = 8 := by unfold casselsMod; rw [if_pos h2]
    let x : v.adicCompletionIntegers ℚ := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
    obtain ⟨z, w, hzw⟩ := exists_int_cong h2 x
    have hu' : u = (z : v.adicCompletion ℚ) + 8 * (w : v.adicCompletion ℚ) := by
      have := congrArg (fun y : v.adicCompletionIntegers ℚ => (y : v.adicCompletion ℚ)) hzw
      simp only [x] at this
      have e8 : ((8 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 8 :=
        map_ofNat (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) 8
      push_cast at this
      rw [e8] at this
      exact this
    have hv8 : Valued.v (8 : v.adicCompletion ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have := (valued_intCast_le_iff v 8 1).mpr (by rw [hp2]; norm_num)
      simpa using this
    have hw1 : Valued.v (w : v.adicCompletion ℚ) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp w.2
    have hz1 : Valued.v (u - (z : v.adicCompletion ℚ)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have : u - (z : v.adicCompletion ℚ) = 8 * (w : v.adicCompletion ℚ) := by rw [hu']; ring
      rw [this, map_mul]
      calc Valued.v (8 : v.adicCompletion ℚ) * Valued.v (w : v.adicCompletion ℚ)
          ≤ Valued.v (8 : v.adicCompletion ℚ) * 1 := mul_le_mul_right hw1 _
        _ ≤ _ := by rw [mul_one]; exact hv8
    refine ⟨z, not_dvd_of_approx v u hu z hz1, fun m hm => ?_⟩
    rw [hq8] at hm
    obtain ⟨j, hj⟩ := (Int.modEq_iff_dvd.mp hm.symm)
    have hj' : (m : v.adicCompletion ℚ) - z = 8 * j := by exact_mod_cast hj
    apply isSquare_of_val_sub_one_le_eight h2
    have e : (m : v.adicCompletion ℚ) * u⁻¹ - 1 = 8 * ((j : v.adicCompletion ℚ) - w) * u⁻¹ := by
      field_simp
      rw [hu']
      linear_combination hj'
    rw [e, map_mul, map_mul, map_inv₀, hu, inv_one, mul_one]
    have hj1 : Valued.v ((j : ℤ) : v.adicCompletion ℚ) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (intCast_mem (v.adicCompletionIntegers ℚ) j)
    have hjw : Valued.v ((j : v.adicCompletion ℚ) - w) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le hj1 hw1)
    calc Valued.v (8 : v.adicCompletion ℚ) * Valued.v ((j : v.adicCompletion ℚ) - w)
        ≤ Valued.v (8 : v.adicCompletion ℚ) * 1 := mul_le_mul_right hjw _
      _ = _ := mul_one _
  · have hq8 : casselsMod v = Rat.HeightOneSpectrum.natGenerator v := by unfold casselsMod; rw [if_neg h2]
    obtain ⟨z, hz⟩ := exists_int_approx v u hu.le
    refine ⟨z, not_dvd_of_approx v u hu z hz, fun m hm => ?_⟩
    rw [hq8] at hm
    have hd : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ m - z := Int.modEq_iff_dvd.mp hm.symm
    have h1 : Valued.v (((m - z : ℤ)) : v.adicCompletion ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
      (valued_intCast_le_iff v (m - z) 1).mpr (by simpa using hd)
    apply isSquare_of_val_sub_one_lt_odd h2
    have e : (m : v.adicCompletion ℚ) * u⁻¹ - 1 = ((m - z : ℤ) + (z - u)) * u⁻¹ := by
      push_cast
      field_simp
      ring
    rw [e, map_mul, map_inv₀, hu, inv_one, mul_one]
    have h3 : Valued.v ((z : v.adicCompletion ℚ) - u) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [Valuation.map_sub_swap]; exact hz
    exact lt_of_le_of_lt (Valuation.map_add_le _ h1 h3) exp_neg_one_lt_one

end Hensel

/-- **Cassels, Lemma 4.3 (i)** (Ch. 11, pp. 216–217): *if $c_1, c_2 \in \mathbb Q^\times$ satisfy the congruence
conditions at the $p \in P$, then $g(c_1) = g(c_2)$.* The conditions are lost in the scan and are reconstructed
(module docstring): $\lvert c_1 - c_2\rvert_p < \lvert c_1\rvert_p$ for odd $p \in P$ and
$\lvert c_1 - c_2\rvert_2 \le \lvert 8c_1\rvert_2$ if $2 \in P$. -/
@[kb "cassels1978" "Ch. 11, Lemma 4.3 (i), pp. 216–217 (congruence conditions reconstructed)"]
theorem casselsg_eq_of_cong {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (L : Lat ℚ n)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (c₁ c₂ : ℚˣ)
    (hodd : ∀ v ∈ P, (2 : 𝓞 ℚ) ∉ v.asIdeal →
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((c₁ : ℚ) - c₂)) < Valued.v (algebraMap ℚ (v.adicCompletion ℚ) c₁))
    (htwo : ∀ v ∈ P, (2 : 𝓞 ℚ) ∈ v.asIdeal →
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((c₁ : ℚ) - c₂)) ≤
        Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (8 * c₁))) :
    casselsg Q hQ L P c₁ = casselsg Q hQ L P c₂ := by
  refine casselsg_eq_of_isSquare Q hQ L P c₁ c₂ fun v hv => ?_
  have hc1 : (c₁ : ℚ) ≠ 0 := c₁.ne_zero
  have hA1 : algebraMap ℚ (v.adicCompletion ℚ) (c₁ : ℚ) ≠ 0 := (map_ne_zero _).mpr hc1
  have hvc1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (c₁ : ℚ)) ≠ 0 := by simpa using hA1
  have e : algebraMap ℚ (v.adicCompletion ℚ) ((c₂ : ℚ) / c₁) - 1 =
      -(algebraMap ℚ (v.adicCompletion ℚ) ((c₁ : ℚ) - c₂)) / algebraMap ℚ (v.adicCompletion ℚ) (c₁ : ℚ) := by
    rw [map_div₀, map_sub]
    field_simp
    ring
  have key : IsSquare (algebraMap ℚ (v.adicCompletion ℚ) ((c₂ : ℚ) / c₁)) := by
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · apply isSquare_of_val_sub_one_le_eight h2
      rw [e, map_div₀, Valuation.map_neg]
      have := htwo v hv h2
      have e8 : algebraMap ℚ (v.adicCompletion ℚ) 8 = 8 := map_ofNat _ 8
      rw [map_mul, e8, map_mul] at this
      exact (div_le_iff₀ (zero_lt_iff.mpr hvc1)).mpr this
    · apply isSquare_of_val_sub_one_lt_odd h2
      rw [e, map_div₀, Valuation.map_neg]
      exact (div_lt_one₀ (zero_lt_iff.mpr hvc1)).mpr (hodd v hv h2)
  obtain ⟨w, hw⟩ := key
  refine ⟨w⁻¹, ?_⟩
  rw [map_div₀] at hw ⊢
  rw [← mul_inv, ← hw, inv_div]

/-- **Cassels, Lemma 4.3 (ii)** (Ch. 11, p. 217): *given $g^* \in G$ and any positive integer $M$ there is a positive
integer $c$ prime to $M$ such that $g(c) = g^*$* (over $\mathbb Q$, $n \ge 3$). -/
@[kb "cassels1978" "Ch. 11, Lemma 4.3 (ii), p. 217"]
theorem exists_casselsg_eq {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n) (L : Lat ℚ n)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : CasselsG Q hQ L P) (M : ℕ) (hM : 0 < M) :
    ∃ c : ℚˣ, ∃ m : ℕ, (c : ℚ) = m ∧ 0 < m ∧ Nat.Coprime m M ∧ casselsg Q hQ L P c = g := by
  classical
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
  -- (a) a positive rational `t ∈ T` with the valuations of `r` on `P`
  let k : HeightOneSpectrum (𝓞 ℚ) → ℤ := fun w =>
    if h : w ∈ P then WithZero.log (Valued.v ((r ⟨w, h⟩ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)) else 0
  obtain ⟨s, hsP, hsN⟩ := exists_scalar_val P k
  let t : ℚˣ := Units.mk0 |(s : ℚ)| (abs_ne_zero.mpr s.ne_zero)
  have ht_pos : 0 < (t : ℚ) := abs_pos.mpr s.ne_zero
  have htv : ∀ w : HeightOneSpectrum (𝓞 ℚ), Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (t : ℚ)) =
      Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (s : ℚ)) := by
    intro w
    change Valued.v (algebraMap ℚ (w.adicCompletion ℚ) |(s : ℚ)|) = _
    rcases abs_choice (s : ℚ) with h | h <;> rw [h]
    rw [map_neg, Valuation.map_neg]
  have htT : t ∈ casselsT Q hQ P :=
    ⟨(mem_spinorNormGroup_rat_iff Q hQ hn t).mpr (Or.inr ht_pos), fun v hv => by rw [htv]; exact hsN v hv⟩
  have hAt : ∀ w : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (w.adicCompletion ℚ) (t : ℚ) ≠ 0 :=
    fun w => (map_ne_zero _).mpr t.ne_zero
  -- the unit family
  let uK : ∀ v : P, v.1.adicCompletion ℚ :=
    fun v => ((r v : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) *
      (algebraMap ℚ (v.1.adicCompletion ℚ) (t : ℚ))⁻¹
  have huK : ∀ v : P, Valued.v (uK v) = 1 := by
    intro v
    have hrv : Valued.v ((r v : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) ≠ 0 := by
      simpa using (r v).ne_zero
    have hk : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (t : ℚ)) =
        Valued.v ((r v : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) := by
      rw [htv, hsP v.1 v.2]
      simp only [k, dif_pos v.2]
      exact WithZero.exp_log hrv
    simp only [uK]
    rw [map_mul, map_inv₀, hk, mul_inv_cancel₀ hrv]
  choose a ha hsq using fun v : P => exists_res v.1 (uK v) (huK v)
  -- (b) CRT
  let a' : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun w => if h : w ∈ P then a ⟨w, h⟩ else 0
  obtain ⟨kk, hkk⟩ := Nat.chineseRemainderOfFinset a' casselsMod P (fun i _ => (casselsMod_pos i).ne')
    (fun v _ w _ hvw => casselsMod_coprime hvw)
  set N : ℕ := ∏ w ∈ P, casselsMod w with hNdef
  have hN : 0 < N := Finset.prod_pos fun w _ => casselsMod_pos w
  have hkN : Nat.Coprime kk N := by
    refine Nat.Coprime.prod_right fun w hw => ?_
    have h1 := (hkk w hw).gcd_eq
    have h2 : a' w = a ⟨w, hw⟩ := dif_pos hw
    rw [Nat.Coprime, h1, h2]
    exact ha ⟨w, hw⟩
  haveI : NeZero (N * M) := ⟨(Nat.mul_pos hN hM).ne'⟩
  obtain ⟨b, hb⟩ := ZMod.unitsMap_surjective (n := N) (m := N * M) (dvd_mul_right N M)
    (ZMod.unitOfCoprime kk hkN)
  let m : ℕ := (b : ZMod (N * M)).val + N * M
  have hm_cast : (m : ZMod (N * M)) = b := by
    simp only [m]
    push_cast
    have h0 : ((N : ZMod (N * M)) * (M : ZMod (N * M))) = 0 := by rw [← Nat.cast_mul, ZMod.natCast_self]
    rw [h0, add_zero]
    try simp
  have hm_cop : Nat.Coprime m (N * M) :=
    (ZMod.isUnit_iff_coprime m (N * M)).mp (by rw [hm_cast]; exact b.isUnit)
  have hmN : m ≡ kk [MOD N] := by
    refine (ZMod.natCast_eq_natCast_iff m kk N).mp ?_
    have hb' := congrArg (fun x : (ZMod N)ˣ => (x : ZMod N)) hb
    have e1 : (m : ZMod N) = ZMod.castHom (dvd_mul_right N M) (ZMod N) (m : ZMod (N * M)) :=
      (map_natCast _ m).symm
    rw [e1, hm_cast]
    simpa [ZMod.unitsMap_def] using hb'
  have hmM : Nat.Coprime m M := Nat.Coprime.coprime_mul_left_right hm_cop
  have hmpos : 0 < m := Nat.add_pos_right _ (Nat.mul_pos hN hM)
  have hmv : ∀ v : P, IsSquare (((m : ℤ) : v.1.adicCompletion ℚ) * (uK v)⁻¹) := by
    intro v
    apply hsq v
    have h1 : m ≡ kk [MOD casselsMod v.1] := hmN.of_dvd (Finset.dvd_prod_of_mem _ v.2)
    have h2 : m ≡ a ⟨v.1, v.2⟩ [MOD casselsMod v.1] := by
      refine h1.trans ?_
      have := hkk v.1 v.2
      have e : a' v.1 = a ⟨v.1, v.2⟩ := dif_pos v.2
      rwa [e] at this
    exact Int.natCast_modEq_iff.mpr h2
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  refine ⟨Units.mk0 (m : ℚ) hm0, m, rfl, hmpos, hmM, ?_⟩
  rw [casselsg, QuotientGroup.eq]
  have hS : (casselsDiag P (Units.mk0 (m : ℚ) hm0))⁻¹ * (r * (casselsDiag P t)⁻¹) ∈ casselsS Q hQ L P := by
    refine mem_casselsS_of_isSquare Q hQ L P _ fun v => ?_
    obtain ⟨w, hw⟩ := hmv v
    refine ⟨w⁻¹, ?_⟩
    simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, casselsDiag_apply]
    have e : algebraMap ℚ (v.1.adicCompletion ℚ) ((Units.mk0 (m : ℚ) hm0 : ℚˣ) : ℚ) =
        ((m : ℤ) : v.1.adicCompletion ℚ) := by
      simp
    rw [e]
    have hw' : ((m : ℤ) : v.1.adicCompletion ℚ) * (uK v)⁻¹ = w * w := hw
    simp only [uK] at hw'
    rw [← mul_inv, ← hw', mul_inv, inv_inv]
  have hT : casselsDiag P t ∈ (casselsT Q hQ P).map (casselsDiag P) := ⟨t, htT, rfl⟩
  have := Subgroup.mul_mem_sup hS hT
  have e : (casselsDiag P (Units.mk0 (m : ℚ) hm0))⁻¹ * (r * (casselsDiag P t)⁻¹) * casselsDiag P t =
      (casselsDiag P (Units.mk0 (m : ℚ) hm0))⁻¹ * r := by group
  rw [e] at this
  exact this

end Rat

end QuadFormsKB.Lattices
