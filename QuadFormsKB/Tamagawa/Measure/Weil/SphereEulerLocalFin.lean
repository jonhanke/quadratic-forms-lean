import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereDensitiesProof
import QuadFormsKB.Tamagawa.SphericalLocalFactor
import QuadFormsKB.Tamagawa.Measure.ConeFiniteChart

/-!
# The local spherical identity at a finite place

$v$ a finite place, $\rho\in F^\times$, $T_v = \{Q_0 = \rho\}\subseteq F_v^N$ with the Leray measure $\sigma_v$ (`sigV`),
$q = N(v)$, $a = N + 2s$. For $j\in\mathbb Z$ let $T_v^{(j)} = T_v\cap\mathfrak p^{-j}L_v$ (`sphLat`, the points with
$|x_i|_v\le q^{j}$). Then (**`hasSum_sphLat`**)
$$\sum_{j\in\mathbb Z}q^{-ja}\,\sigma_v\big(T_v^{(j)}\big) = \frac{Z_\mathfrak p(s,\rho)}{|2\rho|_v|\rho|_v^s},$$
$Z_\mathfrak p$ = `sphLocal`. *Proof.* Homogeneity of the Leray measures (`lerayMeasure_map_smul_units`):
$\sigma_\rho(T^{(j)}) = q^{j(N-2)}\sigma_{\pi^{2j}\rho}(L_v)$, which is $q^{j(N-2)}\beta_v(\pi^{2j}\rho)$ for $\pi^{2j}\rho\in\mathcal O_v$
(`lerayMeasure_latL`) and $0$ otherwise; and the level series for `sphLocal` (`hasSum_levelTerm`):
$Z_\mathfrak p(s,\rho) = |2|_v\sum_{j}|\pi^{2j}\rho|_v^{1+s}\beta_v(\pi^{2j}\rho)$.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.Measure.ConeFinite QuadFormsKB.Tamagawa.Measure.LerayFinite

namespace AdelicSphereSetup

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

variable (Q₀ : QuadForm (𝓞 F) (k + 1)) (ρ : F) (v : HeightOneSpectrum (𝓞 F))

/-- **The points of the local sphere in $\mathfrak p^{-j}L_v$**: $|x_i|_v\le q^j$ for all $i$. -/
def sphLat (j : ℤ) : Set (sphV Q₀ ρ v) := {x | ∀ i, Valued.v (x.1 i) ≤ WithZero.exp j}

/-- The uniformizer power $\pi^j$ as a unit of $F_v$. -/
def uπ (j : ℤ) : (v.adicCompletion F)ˣ :=
  Units.mk0 (((LocalDensity.NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ j)
    (zpow_ne_zero _ (by
      intro h
      have := LocalDensity.NF.valued_π v
      rw [h, map_zero] at this
      exact WithZero.zero_ne_coe this))

theorem valued_uπ (j : ℤ) :
    Valued.v ((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) = WithZero.exp (-j) :=
  LocalZeta.valued_π_zpow v j

theorem sphLat_eq_preimage (j : ℤ) : sphLat Q₀ ρ v j = Subtype.val ⁻¹'
    ((fun x : Fin (k + 1) → v.adicCompletion F => ((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) • x) ⁻¹'
      LocalZeta.latL v (k + 1)) := by
  ext x
  simp only [sphLat, mem_ofPred_eq, mem_preimage, LocalZeta.latL, Pi.smul_apply, smul_eq_mul, map_mul, valued_uπ]
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    calc WithZero.exp (-j) * Valued.v (x.1 i) ≤ WithZero.exp (-j) * WithZero.exp j := mul_le_mul_right h _
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · intro h
    calc Valued.v (x.1 i) = WithZero.exp j * (WithZero.exp (-j) * Valued.v (x.1 i)) := by
          rw [← mul_assoc, ← WithZero.exp_add]; simp
      _ ≤ WithZero.exp j * 1 := mul_le_mul_right h _
      _ = WithZero.exp j := mul_one _

theorem measurableSet_sphLat (j : ℤ) : MeasurableSet (sphLat Q₀ ρ v j) := by
  rw [sphLat_eq_preimage]
  exact measurable_subtype_coe ((continuous_const_smul _).measurable (LocalZeta.measurableSet_latL v))

theorem sphLat_zero : sphLat Q₀ ρ v 0 = intSph Q₀ ρ v := by
  ext x
  simp [sphLat, intSph, IntVec]

variable {Q₀ ρ}

theorem localDensity_nonneg_aux (hQ : Q₀.Nondegenerate) {t : v.adicCompletionIntegers F} (ht : t ≠ 0) :
    0 ≤ DVR.localDensity (LocalDensity.NF.Qp v Q₀) (LocalDensity.NF.π v) t := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (DVR.localDensity_eventually_eq (LocalDensity.NF.Qp v Q₀)
    (LocalDensity.NF.nondegenerate_Qp v hQ) (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) _ ht
    (LocalZeta.two_ne_zero_O v))
  rw [← hK K le_rfl]; positivity

/-- The real number $A = N(v)$. -/
theorem distribHaarChar_uπ (j : ℤ) :
    ((distribHaarChar (v.adicCompletion F) (uπ v j) : NNReal) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [distribHaarChar_eq_norm v (uπ v j), LocalZeta.norm_eq_absNorm_pow v (uπ v j).ne_zero, valued_uπ,
    WithZero.log_exp]

/-- **Homogeneity**: $\sigma_\rho(T\cap\pi^{-j}L)$ in terms of $\sigma_{\pi^{2j}\rho}(L)$. -/
theorem sigV_sphLat_eq (hQ : Q₀.Nondegenerate) (j : ℤ) :
    sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j) =
      ((distribHaarChar (v.adicCompletion F) (uπ v j) : ENNReal) ^ 2 /
          (distribHaarChar (v.adicCompletion F) (uπ v j) : ENNReal) ^ (k + 1)) *
        FibreLeray.sig v Q₀ hQ (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ)
          (LocalZeta.latL v (k + 1)) := by
  have hs : MeasurableSet (sphV Q₀ ρ v) := (FibreLeray.isClosed_sphereV v Q₀ _).measurableSet
  rw [sigV, (MeasurableEmbedding.subtype_coe hs).comap_apply, sphLat_eq_preimage, Subtype.image_preimage_coe]
  have hcompl := FibreLeray.sig_sph_compl v Q₀ hQ (σV v ρ)
  rw [inter_comm, measure_inter_conull' (measure_mono_null (fun x hx => hx.2) hcompl)]
  have h := lerayMeasure_map_smul_units v (QuadFormsKB.Analysis.haarV v) (LocalDensity.NF.Qp v Q₀)
    (LocalDensity.NF.nondegenerate_Qp v hQ) (uπ v j) (σV v ρ)
  have hmeas : Measurable fun x : Fin (k + 1) → v.adicCompletion F =>
      ((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) • x := (continuous_const_smul _).measurable
  have h2 := congrArg (fun μ => μ (LocalZeta.latL v (k + 1))) h
  simp only [Measure.map_apply hmeas (LocalZeta.measurableSet_latL v), Measure.smul_apply, smul_eq_mul] at h2
  exact h2

theorem sig_latL_eq_zero (hQ : Q₀.Nondegenerate) {c : v.adicCompletion F} (hc : ¬ Valued.v c ≤ 1) :
    FibreLeray.sig v Q₀ hQ c (LocalZeta.latL v (k + 1)) = 0 := by
  refine measure_mono_null (t := (FibreLeray.sphereV v Q₀ c)ᶜ) ?_ (FibreLeray.sig_sph_compl v Q₀ hQ c)
  intro x hx hxs
  have h := LocalZeta.valued_evalIn_le_one v (LocalDensity.NF.Qp v Q₀) hx
  rw [LocalDensity.NF.evalIn_Qp] at h
  exact hc (by rw [← show Q₀.evalIn (v.adicCompletion F) x = c from hxs]; exact h)

theorem sig_latL_eq (hQ : Q₀.Nondegenerate) {c : v.adicCompletion F} (hc : c ≠ 0) (hc1 : Valued.v c ≤ 1) :
    FibreLeray.sig v Q₀ hQ c (LocalZeta.latL v (k + 1)) = ENNReal.ofReal (DVR.localDensity
      (LocalDensity.NF.Qp v Q₀) (LocalDensity.NF.π v)
      ⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc1⟩) := by
  have := lerayMeasure_latL v (QuadFormsKB.Analysis.haarV v) (LocalDensity.NF.Qp v Q₀) (LocalDensity.NF.nondegenerate_Qp v hQ)
    (n := k + 1) (by omega) ⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc1⟩
    (fun h => hc (congrArg Subtype.val h))
  rw [LocalZeta.haarV_real_O, one_pow, mul_one] at this
  exact this

theorem norm_absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [← LocalDensity.NF.q_completion]; exact_mod_cast LocalZeta.q_pos v

/-- The scaled target $c_j = \pi^{2j}\rho \ne 0$. -/
theorem uπ_sq_mul_ne_zero (hρ : ρ ≠ 0) (j : ℤ) :
    ((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (uπ v j).ne_zero) ((map_ne_zero (σV v)).mpr hρ)

theorem sigV_sphLat_of_le (hQ : Q₀.Nondegenerate) (hρ : ρ ≠ 0) (j : ℤ)
    (hc : Valued.v (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ) ≤ 1) :
    sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j) = ENNReal.ofReal
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-j)) ^ 2 / ((Ideal.absNorm v.asIdeal : ℝ) ^ (-j)) ^ (k + 1) *
        DVR.localDensity (LocalDensity.NF.Qp v Q₀) (LocalDensity.NF.π v)
          ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩) := by
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := zpow_pos (norm_absNorm_pos v) _
  have hΔ : (distribHaarChar (v.adicCompletion F) (uπ v j) : ENNReal) =
      ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (-j)) := by
    rw [← distribHaarChar_uπ, ENNReal.ofReal_coe_nnreal]
  rw [sigV_sphLat_eq, sig_latL_eq v hQ (uπ_sq_mul_ne_zero v hρ j) hc, hΔ, ← ENNReal.ofReal_pow hpos.le,
    ← ENNReal.ofReal_pow hpos.le, ← ENNReal.ofReal_div_of_pos (pow_pos hpos _),
    ← ENNReal.ofReal_mul (by positivity)]

theorem sigV_sphLat_of_not_le (hQ : Q₀.Nondegenerate) (j : ℤ)
    (hc : ¬ Valued.v (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ) ≤ 1) :
    sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j) = 0 := by
  rw [sigV_sphLat_eq, sig_latL_eq_zero v hQ hc, mul_zero]

theorem sigV_sphLat_ne_top (hQ : Q₀.Nondegenerate) (hρ : ρ ≠ 0) (j : ℤ) : sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j) ≠ ⊤ := by
  by_cases hc : Valued.v (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ) ≤ 1
  · rw [sigV_sphLat_of_le v hQ hρ j hc]; exact ENNReal.ofReal_ne_top
  · rw [sigV_sphLat_of_not_le v hQ j hc]; exact ENNReal.zero_ne_top

/-- Real-exponent bookkeeping: $A^{-j(N+2s)}\cdot r^2/r^N = (r^2)^{1+s}$ for $r = A^{-j}$. -/
theorem alg_aux {A : ℝ} (hA : 0 < A) (j : ℤ) (N : ℕ) (s : ℝ) :
    A ^ (-(j : ℝ) * ((N : ℝ) + 2 * s)) * (((A ^ (-j)) ^ 2) / (A ^ (-j)) ^ N) = ((A ^ (-j)) ^ 2) ^ (1 + s) := by
  have h1 : A ^ (-j) = A ^ (-(j : ℝ)) := by rw [← Real.rpow_intCast]; push_cast; rfl
  rw [h1, ← Real.rpow_natCast (A ^ (-(j : ℝ))) 2, ← Real.rpow_natCast (A ^ (-(j : ℝ))) N]
  simp only [← Real.rpow_mul hA.le]
  rw [← Real.rpow_sub hA, ← Real.rpow_add hA]
  congr 1
  push_cast
  ring

theorem norm_uπ (j : ℤ) : ‖((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ =
    (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [LocalZeta.norm_eq_absNorm_pow v (uπ v j).ne_zero, valued_uπ, WithZero.log_exp]

theorem valued_c_le_one_iff (hρ : ρ ≠ 0) (j : ℤ) :
    Valued.v (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ) ≤ 1 ↔
      0 ≤ 2 * j + SphericalLocalFactor.ordF v (σV v ρ) := by
  have hρv : σV v ρ ≠ 0 := (map_ne_zero (σV v)).mpr hρ
  have hv0 : Valued.v (σV v ρ) ≠ 0 := (Valued.v).ne_zero_iff.mpr hρv
  have hv : Valued.v (σV v ρ) = WithZero.exp (-SphericalLocalFactor.ordF v (σV v ρ)) := by
    rw [SphericalLocalFactor.ordF, neg_neg, WithZero.exp_log hv0]
  rw [map_mul, map_pow, valued_uπ, hv, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  simp only [nsmul_eq_mul]
  push_cast
  constructor <;> intro h <;> linarith

/-- **Termwise comparison** with the level series, at $\ell = 2j + \operatorname{ord}\rho$. -/
theorem term_eq (hQ : Q₀.Nondegenerate) (hρ : ρ ≠ 0) (s : ℝ) (j : ℤ) (ℓ : ℕ)
    (hℓ : (ℓ : ℤ) = 2 * j + SphericalLocalFactor.ordF v (σV v ρ)) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℝ) * (((k + 1 : ℕ) : ℝ) + 2 * s)) *
        (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j)).toReal =
      (‖σV v ρ‖ ^ (1 + s))⁻¹ * SphericalLocalFactor.levelTerm v (LocalDensity.NF.Qp v Q₀)
        ((map_ne_zero (σV v)).mpr hρ) s ℓ := by
  have hρv : σV v ρ ≠ 0 := (map_ne_zero (σV v)).mpr hρ
  have hc : Valued.v (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ) ≤ 1 :=
    (valued_c_le_one_iff v hρ j).mpr (by omega)
  have hA := norm_absNorm_pos v
  have hr : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := zpow_pos hA _
  have htl : SphericalLocalFactor.tLev v (σV v ρ) ℓ =
      ((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ := by
    unfold SphericalLocalFactor.tLev
    rw [show (ℓ : ℤ) - SphericalLocalFactor.ordF v (σV v ρ) = j * 2 by omega, zpow_mul, zpow_two]
    show σV v ρ * (((LocalDensity.NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ j *
      ((LocalDensity.NF.π v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ j) = _
    rw [sq]; exact mul_comm _ _
  have hev : Even ((ℓ : ℤ) - SphericalLocalFactor.ordF v (σV v ρ)) := ⟨j, by omega⟩
  have hβ := localDensity_nonneg_aux v hQ (t := ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩)
    (fun h => uπ_sq_mul_ne_zero v hρ j (congrArg Subtype.val h))
  have hO : SphericalLocalFactor.tLevO v hρv ℓ = ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩ :=
    Subtype.ext htl
  rw [SphericalLocalFactor.levelTerm, if_pos hev, hO, htl, sigV_sphLat_of_le v hQ hρ j hc,
    ENNReal.toReal_ofReal (by positivity), norm_mul, norm_pow, norm_uπ, Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hn : 0 < ‖σV v ρ‖ := norm_pos_iff.mpr hρv
  have hn' : 0 < ‖σV v ρ‖ ^ (1 + s) := Real.rpow_pos_of_pos hn _
  rw [← mul_assoc, ← alg_aux hA j (k + 1) s]
  field_simp

/-- **The local identity at a finite place**:
$\sum_{j\in\mathbb Z}q^{-j(N+2s)}\sigma_v(T_v\cap\mathfrak p^{-j}L_v) = Z_\mathfrak p(s,\rho)/(|2\rho|_v|\rho|_v^s)$. -/
theorem hasSum_sphLat (hQ : Q₀.Nondegenerate) (hρ : ρ ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun j : ℤ => (Ideal.absNorm v.asIdeal : ℝ) ^ (-(j : ℝ) * (((k + 1 : ℕ) : ℝ) + 2 * s)) *
        (sigV Q₀ ρ hQ v (sphLat Q₀ ρ v j)).toReal)
      (SphericalZeta.sphLocal Q₀ v (σV v ρ) s / (‖σV v (2 * ρ)‖ * ‖σV v ρ‖ ^ s)) := by
  have hρv : σV v ρ ≠ 0 := (map_ne_zero (σV v)).mpr hρ
  have h0 := SphericalLocalFactor.hasSum_levelTerm v Q₀ hQ (n := k + 1) (by omega) hρv hs
  have h1 := h0.mul_left ((‖σV v ρ‖ ^ (1 + s))⁻¹)
  have hn : 0 < ‖σV v ρ‖ := norm_pos_iff.mpr hρv
  have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  have hval : (‖σV v ρ‖ ^ (1 + s))⁻¹ * (‖(2 : v.adicCompletion F)‖⁻¹ * SphericalZeta.sphLocal Q₀ v (σV v ρ) s) =
      SphericalZeta.sphLocal Q₀ v (σV v ρ) s / (‖σV v (2 * ρ)‖ * ‖σV v ρ‖ ^ s) := by
    rw [map_mul, map_ofNat, norm_mul, Real.rpow_add hn, Real.rpow_one]
    have : 0 < ‖σV v ρ‖ ^ s := Real.rpow_pos_of_pos hn _
    field_simp
  rw [← hval]
  set g : ℕ → ℝ := fun ℓ => (‖σV v ρ‖ ^ (1 + s))⁻¹ *
    SphericalLocalFactor.levelTerm v (LocalDensity.NF.Qp v Q₀) hρv s ℓ with hg
  have hev : ∀ x : Function.support g, Even ((x.1 : ℤ) - SphericalLocalFactor.ordF v (σV v ρ)) := by
    intro x
    by_contra hne
    apply x.2
    simp [hg, SphericalLocalFactor.levelTerm, hne]
  refine (hasSum_iff_hasSum_of_ne_zero_bij
    (fun x : Function.support g => (((x.1 : ℤ) - SphericalLocalFactor.ordF v (σV v ρ)) / 2)) ?_ ?_ ?_).mpr h1
  · intro x y hxy
    obtain ⟨m, hm⟩ := hev x
    obtain ⟨n, hn⟩ := hev y
    apply Subtype.ext
    simp only at hxy
    omega
  · intro j hj
    have hc : Valued.v (((uπ v j : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ 2 * σV v ρ) ≤ 1 := by
      by_contra hc
      apply hj
      simp only [sigV_sphLat_of_not_le v hQ j hc, ENNReal.toReal_zero, mul_zero]
    have hnn := (valued_c_le_one_iff v hρ j).mp hc
    set ℓ := (2 * j + SphericalLocalFactor.ordF v (σV v ρ)).toNat with hℓdef
    have hℓ : (ℓ : ℤ) = 2 * j + SphericalLocalFactor.ordF v (σV v ρ) := Int.toNat_of_nonneg hnn
    have hmem : ℓ ∈ Function.support g := by
      show g ℓ ≠ 0
      rw [hg]
      simp only
      rw [← term_eq v hQ hρ s j ℓ hℓ]
      exact hj
    exact ⟨⟨ℓ, hmem⟩, by simp only; omega⟩
  · intro x
    obtain ⟨m, hm⟩ := hev x
    have := term_eq v hQ hρ s (((x.1 : ℤ) - SphericalLocalFactor.ordF v (σV v ρ)) / 2) x.1 (by omega)
    exact this

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
