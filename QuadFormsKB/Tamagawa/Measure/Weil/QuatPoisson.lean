import QuadFormsKB.Tamagawa.Measure.Weil.AdelicLattice
import QuadFormsKB.Tamagawa.Measure.Weil.QuatZetaGlobal

/-!
# The twisted Poisson formula on $\mathbb H_{\mathbb A}$

$\mathbb H = \mathbb H[F,a,b]$, $a, b\in F^\times$ integral, any number field, any signature. For
$u\in(\mathbb H\otimes\mathbb A)^\times$ and the Gaussian test function $\Phi = G\otimes\mathbf 1_{\hat\Lambda}$ (`quatTestFn`), the
theta sum $S(u) = \sum_{\xi\in\mathbb H}\Phi(u\xi)$ is a lattice sum: with $U_u = u_f^{-1}\hat\Lambda$ (in coordinates,
`quatUf`) and $L_u = u_\infty L_{U_u}$,
$$S(u) = \sum_{z\in L_u}G(z) = \frac{\mu_f(\hat\Lambda)}{\|\operatorname{nrd}u\|_{\mathbb A}^2}\Big(1 + \sum_{0\ne\eta\in L_u^\vee}G(\eta)\Big)$$
(`quatTheta_poisson`): Poisson summation on $F_\infty^4$ (`poisson_basisGauss`) with the covolume
$\mu_\infty(L_u) = \|\operatorname{nrd}u_\infty\|_\infty^2\,\mu_f(U_u)^{-1}$ (`fundamentalDomain_mul_eq_one`, `map_mulVec_muInfVec`)
and $\mu_f(U_u) = \|\operatorname{nrd}u_f\|_f^{-2}\mu_f(\hat\Lambda)$ (`map_mulVec_muFinVec`).

**Outside results used**: Mathlib's `Module.Basis.parallelepiped_map`,
`ZSpan.fundamentalDomain_ae_parallelepiped`, `IsCompact.elim_directed_cover` (bounded denominators), and the library's
`map_mulVec_muFinVec`, `map_mulVec_muInfVec`, `QuaternionAlgebra.det_mulLeft`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Clearing denominators uniformly on compact sets -/

theorem exists_nat_mul_mem_OHat (x : AF) : ∃ d : ℕ, d ≠ 0 ∧ (d : AF) * x ∈ OHat := by
  have hfin : {v | x v ∉ v.adicCompletionIntegers F}.Finite := x.2
  obtain ⟨d, hd0, hd⟩ := Analysis.exists_nat_clear hfin.toFinset (fun v => x v)
  refine ⟨d, hd0, fun v => ?_⟩
  change evalAt v ((d : AF) * x) ∈ v.adicCompletionIntegers F
  rw [map_mul, map_natCast]
  change (d : v.adicCompletion F) * x v ∈ _
  by_cases hv : v ∈ hfin.toFinset
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hd v hv
  · exact mul_mem (natCast_mem_O d v) (by simpa using hv)

theorem natCast_mul_mem_OHat {x : AF} (hx : x ∈ OHat) (d : ℕ) : (d : AF) * x ∈ OHat := fun v => by
  change evalAt v ((d : AF) * x) ∈ v.adicCompletionIntegers F
  rw [map_mul, map_natCast]
  exact mul_mem (natCast_mem_O d v) (hx v)

theorem natCast_mul_mul_mem_OHat {x : AF} {d : ℕ} (hx : (d : AF) * x ∈ OHat) (e : ℕ) :
    ((e * d : ℕ) : AF) * x ∈ OHat := by
  rw [Nat.cast_mul, mul_assoc]; exact natCast_mul_mem_OHat hx e

theorem isOpen_natCast_mul_mem_OHat (d : ℕ) : IsOpen {x : AF | (d : AF) * x ∈ OHat} :=
  isOpen_OHat.preimage (continuous_const.mul continuous_id)

/-- **Bounded denominators on a compact set**: there is $d\ne0$ with $dK\subseteq\hat{\mathcal O}$. -/
theorem exists_nat_mul_mem_OHat_of_isCompact {K : Set AF} (hK : IsCompact K) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ x ∈ K, (d : AF) * x ∈ OHat := by
  set U : ℕ → Set AF := fun n => {x : AF | ((n.factorial : ℕ) : AF) * x ∈ OHat}
  have hUo : ∀ n, IsOpen (U n) := fun n => isOpen_natCast_mul_mem_OHat _
  have hcov : K ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨d, hd0, hd⟩ := exists_nat_mul_mem_OHat x
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hd0) le_rfl
    have : x ∈ U d := by
      simp only [U, mem_ofPred_eq]
      rw [hk, Nat.mul_comm d k]
      exact natCast_mul_mul_mem_OHat hd k
    exact mem_iUnion.mpr ⟨d, this⟩
  have hdir : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le fun m n hmn x hx => ?_
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hmn
    simp only [U, mem_ofPred_eq] at hx ⊢
    rw [hk, Nat.mul_comm m.factorial k]
    exact natCast_mul_mul_mem_OHat hx k
  obtain ⟨n, hn⟩ := hK.elim_directed_cover U hUo hcov hdir
  exact ⟨n.factorial, (Nat.factorial_pos n).ne', fun x hx => hn hx⟩

/-! ### $\hat\Lambda$ as an additive group and a ring -/

section Lam

variable {a b : F}

variable (a b) in
/-- $\hat\Lambda$ as an additive subgroup of $\mathbb H[\mathbb A_f]$. -/
def lamHatAdd : AddSubgroup (QuatFin a b) where
  carrier := lamHat a b
  zero_mem' := ⟨zero_mem_OHat, zero_mem_OHat, zero_mem_OHat, zero_mem_OHat⟩
  add_mem' := fun hx hy => ⟨add_mem_OHat hx.1 hy.1, add_mem_OHat hx.2.1 hy.2.1, add_mem_OHat hx.2.2.1 hy.2.2.1,
    add_mem_OHat hx.2.2.2 hy.2.2.2⟩
  neg_mem' := fun hx => ⟨neg_mem_OHat hx.1, neg_mem_OHat hx.2.1, neg_mem_OHat hx.2.2.1, neg_mem_OHat hx.2.2.2⟩

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

include ha hb in
theorem mul_mem_lamHat {x y : QuatFin a b} (hx : x ∈ lamHat a b) (hy : y ∈ lamHat a b) : x * y ∈ lamHat a b :=
  (mem_lamHat_iff a b _).mpr fun v => by
    rw [map_mul]; exact mul_mem_lamLoc ha hb ((mem_lamHat_iff a b _).mp hx v) ((mem_lamHat_iff a b _).mp hy v)

theorem natCast_quatFin (d : ℕ) : ((d : QuatFin a b)) = ⟨(d : AF), 0, 0, 0⟩ := by
  induction d with
  | zero => ext <;> simp
  | succ n ih => ext <;> simp [ih]

theorem natCast_mul_quatFin (d : ℕ) (x : QuatFin a b) :
    (d : QuatFin a b) * x = ⟨(d : AF) * x.re, (d : AF) * x.imI, (d : AF) * x.imJ, (d : AF) * x.imK⟩ := by
  rw [natCast_quatFin]; ext <;> simp

theorem natCast_mul_mem_lamHat {x : QuatFin a b} (hx : x ∈ lamHat a b) (d : ℕ) : (d : QuatFin a b) * x ∈ lamHat a b := by
  rw [natCast_mul_quatFin]
  exact ⟨natCast_mul_mem_OHat hx.1 d, natCast_mul_mem_OHat hx.2.1 d, natCast_mul_mem_OHat hx.2.2.1 d,
    natCast_mul_mem_OHat hx.2.2.2 d⟩

/-- **Bounded denominators for a compact set of units of $\mathbb H[\mathbb A_f]$**: $du, du^{-1}\in\hat\Lambda$. -/
theorem exists_nat_mul_mem_lamHat {K : Set (QuatFin a b)ˣ} (hK : IsCompact K) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ u ∈ K, (d : QuatFin a b) * (u : QuatFin a b) ∈ lamHat a b ∧
      (d : QuatFin a b) * ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) ∈ lamHat a b := by
  have hc : ∀ f : (QuatFin a b)ˣ → AF, Continuous f → ∃ d : ℕ, d ≠ 0 ∧ ∀ u ∈ K, (d : AF) * f u ∈ OHat :=
    fun f hf => exists_nat_mul_mem_OHat_of_isCompact (hK.image hf) |>.imp fun d ⟨hd0, hd⟩ =>
      ⟨hd0, fun u hu => hd _ ⟨u, hu, rfl⟩⟩
  obtain ⟨d1, h1, e1⟩ := hc _ ((continuous_fre a b).comp Units.continuous_val)
  obtain ⟨d2, h2, e2⟩ := hc _ ((continuous_fimI a b).comp Units.continuous_val)
  obtain ⟨d3, h3, e3⟩ := hc _ ((continuous_fimJ a b).comp Units.continuous_val)
  obtain ⟨d4, h4, e4⟩ := hc _ ((continuous_fimK a b).comp Units.continuous_val)
  obtain ⟨d5, h5, e5⟩ := hc _ ((continuous_fre a b).comp Units.continuous_coe_inv)
  obtain ⟨d6, h6, e6⟩ := hc _ ((continuous_fimI a b).comp Units.continuous_coe_inv)
  obtain ⟨d7, h7, e7⟩ := hc _ ((continuous_fimJ a b).comp Units.continuous_coe_inv)
  obtain ⟨d8, h8, e8⟩ := hc _ ((continuous_fimK a b).comp Units.continuous_coe_inv)
  set d := d1 * d2 * d3 * d4 * d5 * d6 * d7 * d8
  have hd0 : d ≠ 0 := by simp [d, h1, h2, h3, h4, h5, h6, h7, h8]
  refine ⟨d, hd0, fun u hu => ⟨?_, ?_⟩⟩
  · rw [natCast_mul_quatFin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show d = (d2 * d3 * d4 * d5 * d6 * d7 * d8) * d1 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e1 u hu) _
    · rw [show d = (d1 * d3 * d4 * d5 * d6 * d7 * d8) * d2 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e2 u hu) _
    · rw [show d = (d1 * d2 * d4 * d5 * d6 * d7 * d8) * d3 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e3 u hu) _
    · rw [show d = (d1 * d2 * d3 * d5 * d6 * d7 * d8) * d4 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e4 u hu) _
  · rw [natCast_mul_quatFin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show d = (d1 * d2 * d3 * d4 * d6 * d7 * d8) * d5 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e5 u hu) _
    · rw [show d = (d1 * d2 * d3 * d4 * d5 * d7 * d8) * d6 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e6 u hu) _
    · rw [show d = (d1 * d2 * d3 * d4 * d5 * d6 * d8) * d7 by simp only [d]; ring]
      exact natCast_mul_mul_mem_OHat (e7 u hu) _
    · rw [show d = (d1 * d2 * d3 * d4 * d5 * d6 * d7) * d8 by simp only [d]]
      exact natCast_mul_mul_mem_OHat (e8 u hu) _

end Lam

/-! ### The finite twist: $U_u = u^{-1}\hat\Lambda$ in coordinates -/

section Uf

variable {a b : F}

/-- $U_u = \{c\in\mathbb A_f^4 : u\cdot c\in\hat\Lambda\}$, the coordinates of $u^{-1}\hat\Lambda$. -/
def quatUf (u : (QuatFin a b)ˣ) : AddSubgroup (Fin 4 → AF) :=
  (lamHatAdd a b).comap ((AddMonoidHom.mulLeft (u : QuatFin a b)).comp
    (quatFinCoord a b).symm.toLinearMap.toAddMonoidHom)

theorem mem_quatUf {u : (QuatFin a b)ˣ} {c : Fin 4 → AF} :
    c ∈ quatUf u ↔ (u : QuatFin a b) * (quatFinCoord a b).symm c ∈ lamHat a b := Iff.rfl

theorem quatFinCoord_symm_re (c : Fin 4 → AF) : ((quatFinCoord a b).symm c).re = c 0 := rfl
theorem quatFinCoord_symm_imI (c : Fin 4 → AF) : ((quatFinCoord a b).symm c).imI = c 1 := rfl
theorem quatFinCoord_symm_imJ (c : Fin 4 → AF) : ((quatFinCoord a b).symm c).imJ = c 2 := rfl
theorem quatFinCoord_symm_imK (c : Fin 4 → AF) : ((quatFinCoord a b).symm c).imK = c 3 := rfl

theorem mem_lamHat_symm_iff (c : Fin 4 → AF) : (quatFinCoord a b).symm c ∈ lamHat a b ↔ ∀ i, c i ∈ OHat := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3]
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

include ha hb in
/-- **Upper bound**: $dU_u\subseteq\hat{\mathcal O}^4$ when $du^{-1}\in\hat\Lambda$. -/
theorem quatUf_upper {u : (QuatFin a b)ˣ} {d : ℕ}
    (hd : (d : QuatFin a b) * ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) ∈ lamHat a b) :
    ∀ c ∈ quatUf u, ∀ i, (d : AF) * c i ∈ OHat := by
  intro c hc
  have h1 := mul_mem_lamHat ha hb hd (mem_quatUf.mp hc)
  rw [mul_assoc, ← mul_assoc ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b), Units.inv_mul, one_mul,
    natCast_mul_quatFin] at h1
  intro i
  fin_cases i
  exacts [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]

theorem jFin_mem_lamHat (ξ : Fin 4 → 𝓞 F) :
    (quatFinCoord a b).symm (jFin F (Fin 4) fun i => ((ξ i : 𝓞 F) : F)) ∈ lamHat a b := by
  rw [mem_lamHat_symm_iff]
  intro i
  exact (algebraMap_mem_OHat_iff _).mpr ⟨ξ i, rfl⟩

include ha hb in
/-- **Lower bound**: $d\,\mathcal O_F^4\subseteq U_u$ when $du\in\hat\Lambda$. -/
theorem quatUf_lower {u : (QuatFin a b)ˣ} {d : ℕ} (hd : (d : QuatFin a b) * (u : QuatFin a b) ∈ lamHat a b) :
    ∀ ξ : Fin 4 → 𝓞 F, jFin F (Fin 4) (fun i => (d : F) * (ξ i : F)) ∈ quatUf u := by
  intro ξ
  rw [mem_quatUf]
  have hsymm : (quatFinCoord a b).symm (jFin F (Fin 4) (fun i => (d : F) * (ξ i : F))) =
      (d : QuatFin a b) * (quatFinCoord a b).symm (jFin F (Fin 4) fun i => ((ξ i : 𝓞 F) : F)) := by
    rw [natCast_mul_quatFin]
    ext <;> simp [quatFinCoord_symm_re, quatFinCoord_symm_imI, quatFinCoord_symm_imJ, quatFinCoord_symm_imK]
  rw [hsymm, ← mul_assoc, ← (Nat.cast_commute d (u : QuatFin a b)).eq]
  exact mul_mem_lamHat ha hb hd (jFin_mem_lamHat ξ)

theorem isOpen_quatUf (u : (QuatFin a b)ˣ) : IsOpen (quatUf u : Set (Fin 4 → AF)) := by
  have : (quatUf u : Set (Fin 4 → AF)) =
      (fun c => (u : QuatFin a b) * (quatFinCoord a b).symm c) ⁻¹' lamHat a b := rfl
  rw [this]
  refine (isOpen_lamHat a b).preimage (continuous_const.mul ?_)
  exact (continuous_quatFin_iff a b).mpr ⟨continuous_apply 0, continuous_apply 1, continuous_apply 2,
    continuous_apply 3⟩

end Uf

/-! ### Left multiplication matrices and their scaling -/

section Scaling

variable {a b : F}

/-- The matrix of left multiplication on $\mathbb H[\mathbb A_f]$ in the basis $1,i,j,k$. -/
def lmFin (y : QuatFin a b) : Matrix (Fin 4) (Fin 4) AF :=
  Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) y

theorem quatFinCoord_mul (y x : QuatFin a b) : quatFinCoord a b (y * x) = lmFin y *ᵥ quatFinCoord a b x :=
  (Algebra.leftMulMatrix_mulVec_repr (QuaternionAlgebra.basisOneIJK _ 0 _) y x).symm

/-- $u\mapsto L_u\in\mathrm{GL}_4(\mathbb A_f)$. -/
def lmFinGL (u : (QuatFin a b)ˣ) : GL (Fin 4) AF :=
  Units.map (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _)).toMonoidHom u

theorem lmFinGL_val (u : (QuatFin a b)ˣ) : (lmFinGL u : Matrix (Fin 4) (Fin 4) AF) = lmFin (u : QuatFin a b) := rfl

theorem quatUf_eq_preimage (u : (QuatFin a b)ˣ) :
    (quatUf u : Set (Fin 4 → AF)) = (lmFin (u : QuatFin a b)).mulVec ⁻¹' OHatVec := by
  ext c
  simp only [SetLike.mem_coe, mem_quatUf, mem_preimage]
  rw [lamHat_eq, mem_preimage, quatFinCoord_mul, LinearEquiv.apply_symm_apply]
  rfl

theorem det_lmFinGL (u : (QuatFin a b)ˣ) :
    ((GeneralLinearGroup.det (lmFinGL u) : AFˣ) : AF) = (((u : QuatFin a b) * star (u : QuatFin a b)).re) ^ 2 := by
  change (Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) (u : QuatFin a b)).det = _
  rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix]
  exact QuaternionAlgebra.det_mulLeft _ _ _

theorem nrd_quatFin_apply (y : QuatFin a b) (v : HeightOneSpectrum (𝓞 F)) :
    (y * star y).re v = nrdLoc _ _ (projQ a b v y) := by
  simp only [nrdLoc, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, projQ_re, projQ_imI, projQ_imJ, projQ_imK]
  conv_lhs => rw [show ∀ x : AF, x v = evalAt v x from fun _ => rfl]
  simp only [map_add, map_mul, map_neg, map_sub, map_zero, evalAt_algebraMap]
  rfl

theorem mulSupport_norm_nrdLoc_finite (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1) (u : (QuatFin a b)ˣ) :
    (Function.mulSupport fun v => ‖nrdLoc _ _ (projQ a b v (u : QuatFin a b))‖).Finite := by
  refine (finite_not_mem_lamLocUnits u).subset fun v hv => ?_
  by_contra h
  exact hv (by have := norm_nrdLoc_eq_one ha hb (not_not.mp h); rwa [unitAtQ_val] at this)

/-- **$\Delta_f(\det L_u) = \|\operatorname{nrd}u\|_f^2$.** -/
theorem distribHaarChar_det_lmFinGL (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1) (u : (QuatFin a b)ˣ) :
    (distribHaarChar AF (GeneralLinearGroup.det (lmFinGL u)) : ℝ) = normFinQ a b u ^ 2 := by
  rw [distribHaarChar_finiteAdeleRing]
  have hcoe := MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective
    (fun v => modAt (GeneralLinearGroup.det (lmFinGL u)) v)
  change ((∏ᶠ v, modAt (GeneralLinearGroup.det (lmFinGL u)) v : ℝ≥0) : ℝ) = _ at hcoe ⊢
  rw [show ((∏ᶠ v, modAt (GeneralLinearGroup.det (lmFinGL u)) v : ℝ≥0) : ℝ) =
    ∏ᶠ v, ((modAt (GeneralLinearGroup.det (lmFinGL u)) v : ℝ≥0) : ℝ) from hcoe, normFinQ,
    finprod_pow (mulSupport_norm_nrdLoc_finite ha hb u)]
  refine finprod_congr fun v => ?_
  rw [modAt, distribHaarChar_adic_eq_norm, unitAt_val, det_lmFinGL, show (((u : QuatFin a b) * star
    (u : QuatFin a b)).re ^ 2) v = ((u : QuatFin a b) * star (u : QuatFin a b)).re v ^ 2 from by
      conv_lhs => rw [show ∀ x : AF, x v = evalAt v x from fun _ => rfl]
      rw [map_pow]; rfl, norm_pow, nrd_quatFin_apply]

/-- **$\mu_f(U_u) = \|\operatorname{nrd}u\|_f^{-2}\,\mu_f(\hat\Lambda)$.** -/
theorem muFinVec_quatUf (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1) (u : (QuatFin a b)ˣ) :
    muFinVec F (Fin 4) (quatUf u : Set (Fin 4 → AF)) =
      ENNReal.ofReal (normFinQ a b u ^ 2)⁻¹ * muFinVec F (Fin 4) OHatVec := by
  have hm : Measurable (lmFin (u : QuatFin a b)).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hOm : MeasurableSet (OHatVec (F := F) (ι := Fin 4)) := MeasurableSet.univ_pi fun _ => measurableSet_OHat
  rw [quatUf_eq_preimage, ← Measure.map_apply hm hOm, ← lmFinGL_val, map_mulVec_muFinVec, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, distribHaarChar_det_lmFinGL ha hb]

/-- The matrix of left multiplication on $\mathbb H[F_\infty]$. -/
def lmInf (y : QuatInf a b) : Matrix (Fin 4) (Fin 4) V :=
  Algebra.leftMulMatrix (QuaternionAlgebra.basisOneIJK _ _ _) y

theorem quatInfCoord_mul' (y x : QuatInf a b) : quatInfCoord a b (y * x) = lmInf y *ᵥ quatInfCoord a b x :=
  quatInfCoord_mul a b y x

theorem lmInf_mul (y z : QuatInf a b) : lmInf (y * z) = lmInf y * lmInf z := map_mul _ y z

theorem lmInf_one : lmInf (1 : QuatInf a b) = 1 := map_one _

theorem det_lmInf (y : QuatInf a b) : (lmInf y).det = nrdInf a b y ^ 2 := det_leftMulMatrix_inf a b y

/-- $z\mapsto L_uz$ on $F_\infty^4$, a real linear equivalence for $u$ a unit. -/
def lmInfEquiv (u : (QuatInf a b)ˣ) : (Fin 4 → V) ≃ₗ[ℝ] (Fin 4 → V) where
  toFun z := lmInf (u : QuatInf a b) *ᵥ z
  invFun z := lmInf ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ z
  map_add' z w := Matrix.mulVec_add _ _ _
  map_smul' c z := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]
  left_inv z := by
    show lmInf ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ (lmInf (u : QuatInf a b) *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, ← lmInf_mul, Units.inv_mul, lmInf_one, Matrix.one_mulVec]
  right_inv z := by
    show lmInf (u : QuatInf a b) *ᵥ (lmInf ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, ← lmInf_mul, Units.mul_inv, lmInf_one, Matrix.one_mulVec]

theorem lmInfEquiv_apply (u : (QuatInf a b)ˣ) (z : Fin 4 → V) : lmInfEquiv u z = lmInf (u : QuatInf a b) *ᵥ z := rfl

/-- **$\mu_\infty(L_uS) = \|\operatorname{nrd}u\|_\infty^2\,\mu_\infty(S)$.** -/
theorem muInfVec_lmInf_image (u : (QuatInf a b)ˣ) {S : Set (Fin 4 → V)} (hS : MeasurableSet S) :
    muInfVec F (Fin 4) (lmInfEquiv u '' S) = ENNReal.ofReal (absDetInf (nrdInf a b (u : QuatInf a b)) ^ 2) *
      muInfVec F (Fin 4) S := by
  set M := lmInf ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b)
  have hMu : IsUnit M.det := by
    rw [det_lmInf]; exact ((isUnit_iff_isUnit_nrdInf a b _).mp (u⁻¹).isUnit).pow 2
  have himg : lmInfEquiv u '' S = M.mulVec ⁻¹' S := (lmInfEquiv u).image_eq_preimage_symm S
  have hm : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [himg, ← Measure.map_apply hm hS, map_mulVec_muInfVec M hMu, Measure.smul_apply,
    smul_eq_mul]
  congr 1
  congr 1
  rw [det_lmInf, ← absDetInf, sq, absDetInf_mul, ← sq]
  have h1 : nrdInf a b ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b) * nrdInf a b (u : QuatInf a b) = 1 := by
    rw [← nrdInf_mul, Units.inv_mul, nrdInf_one]
  have h2 : absDetInf (nrdInf a b ((u⁻¹ : (QuatInf a b)ˣ) : QuatInf a b)) * absDetInf (nrdInf a b (u : QuatInf a b)) = 1 := by
    rw [← absDetInf_mul, h1, absDetInf, LinearMap.mulLeft_one, LinearMap.det_id, abs_one]
  rw [← inv_pow, eq_inv_of_mul_eq_one_left h2, inv_inv]

end Scaling

/-! ### The theta sum as a lattice sum, and Poisson -/

section Theta

variable {a b : F}

/-- The Gaussian test function on $\mathbb H_{\mathbb A}$: $G\otimes\mathbf 1_{\hat\Lambda}$. -/
def gaussPhi : (Fin 4 → V) → ℝ≥0∞ := fun z => ENNReal.ofReal (gV z)

variable (a b) in
/-- **The theta sum** $S(u) = \sum_{\xi\in\mathbb H}\Phi(u\xi)$ for $\Phi = G\otimes\mathbf 1_{\hat\Lambda}$. -/
def quatTheta (u : (QuatAdele a b)ˣ) : ℝ≥0∞ :=
  ∑' ξ : ℍ[F,a,b], quatTestFn a b gaussPhi ((u : QuatAdele a b) * quatDiagRing a b ξ)

/-- The archimedean and finite components of a unit. -/
def uInf (u : (QuatAdele a b)ˣ) : (QuatInf a b)ˣ := (quatUnitsEquiv a b u).1
def uFin (u : (QuatAdele a b)ˣ) : (QuatFin a b)ˣ := (quatUnitsEquiv a b u).2

theorem quatAdeleRingEquiv_diag_fst (ξ : ℍ[F,a,b]) :
    quatInfCoord a b (quatAdeleRingEquiv a b (quatDiagRing a b ξ)).1 =
      jInf F (Fin 4) (QuaternionAlgebra.linearEquivTuple a 0 b ξ) := by
  funext i; fin_cases i <;> rfl

theorem quatAdeleRingEquiv_diag_snd (ξ : ℍ[F,a,b]) :
    (quatAdeleRingEquiv a b (quatDiagRing a b ξ)).2 =
      (quatFinCoord a b).symm (jFin F (Fin 4) (QuaternionAlgebra.linearEquivTuple a 0 b ξ)) := by
  ext <;> rfl

/-- The term of the theta sum at $\xi$ with coordinates $c$:
$\Phi(u\xi) = G(L_{u_\infty}c_\infty)\,\mathbf 1[c_f\in U_{u_f}]$. -/
theorem quatTestFn_mul_diag (u : (QuatAdele a b)ˣ) (ξ : ℍ[F,a,b]) :
    quatTestFn a b gaussPhi ((u : QuatAdele a b) * quatDiagRing a b ξ) =
      ((quatUf (uFin u) : Set (Fin 4 → AF)).indicator (fun _ => (1 : ℝ≥0∞))
        (jFin F (Fin 4) (QuaternionAlgebra.linearEquivTuple a 0 b ξ))) *
      gaussPhi (lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ
        jInf F (Fin 4) (QuaternionAlgebra.linearEquivTuple a 0 b ξ)) := by
  rw [quatTestFn_eq, map_mul, Prod.fst_mul, Prod.snd_mul, quatInfCoord_mul', quatAdeleRingEquiv_diag_fst,
    quatAdeleRingEquiv_diag_snd, mul_comm]
  congr 1

/-- **The theta sum is a lattice sum**: $S(u) = \sum_{w\in L_{U_u}}G(L_{u_\infty}w)$. -/
theorem quatTheta_eq_tsum_lattice (u : (QuatAdele a b)ˣ) :
    quatTheta a b u = ∑' w : adelicLat (quatUf (uFin u)),
      gaussPhi (lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ (w : Fin 4 → V)) := by
  set U := quatUf (uFin u)
  set f : (Fin 4 → V) → ℝ≥0∞ := fun w => gaussPhi (lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ w)
  set T := QuaternionAlgebra.linearEquivTuple (R := F) a 0 b
  set G : (Fin 4 → F) → ℝ≥0∞ := fun c => (U : Set (Fin 4 → AF)).indicator (fun _ => (1 : ℝ≥0∞))
    (jFin F (Fin 4) c) * f (jInf F (Fin 4) c)
  have h1 : ∀ c : Fin 4 → F, G c =
      ((U.comap (jFin F (Fin 4)) : Set (Fin 4 → F))).indicator (fun c => f (jInf F (Fin 4) c)) c := by
    intro c
    by_cases h : jFin F (Fin 4) c ∈ U
    · simp only [G]
      rw [indicator_of_mem h, one_mul, indicator_of_mem (show c ∈ (U.comap (jFin F (Fin 4)) : Set _) from h)]
    · simp only [G]
      rw [indicator_of_notMem h, zero_mul,
        indicator_of_notMem (show c ∉ (U.comap (jFin F (Fin 4)) : Set _) from h)]
  let e : (U.comap (jFin F (Fin 4)) : Set (Fin 4 → F)) ≃ adelicLat U :=
    Equiv.ofBijective (fun c => ⟨jInf F (Fin 4) c.1, jInf_mem_adelicLat U c.2⟩)
      ⟨fun c₁ c₂ h => Subtype.ext (jInf_injective (congrArg Subtype.val h)),
        fun ⟨w, ξ, hξ, hw⟩ => ⟨⟨ξ, hξ⟩, Subtype.ext hw⟩⟩
  calc quatTheta a b u = ∑' ξ, G (T ξ) := by rw [quatTheta]; exact tsum_congr fun ξ => quatTestFn_mul_diag u ξ
    _ = ∑' c, G c := T.toEquiv.tsum_eq G
    _ = ∑' c, ((U.comap (jFin F (Fin 4)) : Set (Fin 4 → F))).indicator (fun c => f (jInf F (Fin 4) c)) c :=
        tsum_congr h1
    _ = ∑' c : (U.comap (jFin F (Fin 4)) : Set (Fin 4 → F)), f (jInf F (Fin 4) c) := (tsum_subtype _ _).symm
    _ = ∑' w : adelicLat U, f w := e.tsum_eq (fun w => f w)

/-- The dual of $L_u = L_{u_\infty}L_{U_u}$ for $\beta$, as a set. -/
def quatDualSet (u : (QuatAdele a b)ˣ) : Set (Fin 4 → V) :=
  {η | ∀ w ∈ adelicLat (quatUf (uFin u)), ∃ n : ℤ,
    betaV F (Fin 4) η (lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ w) = n}

theorem zero_mem_quatDualSet (u : (QuatAdele a b)ˣ) : (0 : Fin 4 → V) ∈ quatDualSet u :=
  fun _ _ => ⟨0, by simp⟩

/-- **The dual remainder** $R(u) = \sum_{0\ne\eta\in L_u^\vee}G(\eta)$. -/
def quatDualRem (u : (QuatAdele a b)ˣ) : ℝ≥0∞ :=
  ∑' η : quatDualSet u, if (η : Fin 4 → V) = 0 then 0 else gaussPhi (η : Fin 4 → V)

variable (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)

set_option maxHeartbeats 1000000 in
include ha hb in
/-- **The twisted Poisson formula on $\mathbb H_{\mathbb A}$**:
$\|\operatorname{nrd}u\|_{\mathbb A}^2\,S(u) = \mu_f(\hat\Lambda)\,(1 + R(u))$. -/
@[kb "weil1982" "§3.1, the additive calculation (Poisson formula on A_𝔸), pp. 39-40"]
theorem quatTheta_poisson (u : (QuatAdele a b)ˣ) :
    ENNReal.ofReal (ideleNorm F (nrdUnit u) ^ 2) * quatTheta a b u =
      muFinVec F (Fin 4) OHatVec * (1 + quatDualRem u) := by
  set U := quatUf (uFin u)
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_mem_lamHat (isCompact_singleton (x := uFin u))
  have hdu := hd (uFin u) rfl
  have : DiscreteTopology (adelicLat U) := discreteTopology_adelicLat U hd0 (quatUf_upper ha hb hdu.2)
  have : IsZLattice ℝ (adelicLat U) := isZLattice_adelicLat U hd0 (quatUf_lower ha hb hdu.1)
  set b' := latBasis (adelicLat U)
  have hb' : Submodule.span ℤ (Set.range b') = adelicLat U := span_latBasis _
  set e := lmInfEquiv (uInf u)
  set b'' := b'.map e
  -- the theta sum as a sum over span b''
  have hθ : quatTheta a b u = ∑' z : Submodule.span ℤ (Set.range b''), gaussPhi (z : Fin 4 → V) := by
    rw [quatTheta_eq_tsum_lattice, tsum_span_basis b'' (fun z => gaussPhi z)]
    have h1 := tsum_span_basis b' (fun w => gaussPhi (lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ w))
    rw [hb'] at h1
    rw [h1]
    refine tsum_congr fun k => ?_
    congr 1
    rw [show lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ (∑ j, (k j : ℝ) • b' j) =
      e (∑ j, (k j : ℝ) • b' j) from rfl, map_sum]
    simp only [map_smul, b'', Module.Basis.map_apply]
  -- the dual sets agree
  have hspan : Submodule.span ℤ (Set.range b'') = (adelicLat U).map (e.toLinearMap.restrictScalars ℤ) := by
    have hr : Set.range b'' = (e.toLinearMap.restrictScalars ℤ) '' Set.range b' := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hb']
  have hdual : ((betaV F (Fin 4)).dualSubmodule (Submodule.span ℤ (Set.range b'')) : Set (Fin 4 → V)) =
      quatDualSet u := by
    ext η
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_dualSubmodule, hspan]
    simp only [Submodule.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Submodule.mem_one]
    refine forall₂_congr fun w _ => ?_
    change (∃ n : ℤ, algebraMap ℤ ℝ n = betaV F (Fin 4) η (lmInf ((uInf u : (QuatInf a b)ˣ) : QuatInf a b) *ᵥ w)) ↔ _
    exact ⟨fun ⟨n, hn⟩ => ⟨n, by rw [← hn]; simp⟩, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; simp⟩⟩
  have hP := poisson_basisGauss b''
  have hiff : ∀ η, η ∈ (betaV F (Fin 4)).dualSubmodule (Submodule.span ℤ (Set.range b'')) ↔ η ∈ quatDualSet u :=
    fun η => by rw [← SetLike.mem_coe, hdual]
  have hdualsum : (∑' η : (betaV F (Fin 4)).dualSubmodule (Submodule.span ℤ (Set.range b'')),
      ENNReal.ofReal (gV (η : Fin 4 → V))) = ∑' η : quatDualSet u, gaussPhi (η : Fin 4 → V) :=
    (Equiv.subtypeEquivRight hiff).tsum_eq (fun η : quatDualSet u => gaussPhi (η : Fin 4 → V))
  rw [hdualsum] at hP
  have hsplit : ∑' η : quatDualSet u, gaussPhi (η : Fin 4 → V) = 1 + quatDualRem u := by
    rw [ENNReal.tsum_eq_add_tsum_ite (⟨0, zero_mem_quatDualSet u⟩ : quatDualSet u)]
    congr 1
    · simp [gaussPhi, gV_zero]
    · refine tsum_congr fun η => ?_
      congr 1
      exact propext ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  rw [hsplit] at hP
  -- the covolume
  have hPm : MeasurableSet ((b'.parallelepiped : Set (Fin 4 → V))) := b'.parallelepiped.isCompact.isClosed.measurableSet
  have hcov : muInfVec F (Fin 4) b''.parallelepiped = ENNReal.ofReal (absDetInf (nrdInf a b
      ((uInf u : (QuatInf a b)ˣ) : QuatInf a b)) ^ 2) * muInfVec F (Fin 4) b'.parallelepiped := by
    rw [Module.Basis.parallelepiped_map, TopologicalSpace.PositiveCompacts.coe_map]
    exact muInfVec_lmInf_image (uInf u) hPm
  have hfd : muInfVec F (Fin 4) b'.parallelepiped * muFinVec F (Fin 4) (U : Set (Fin 4 → AF)) = 1 := by
    rw [Module.Basis.coe_parallelepiped,
      ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b' (muInfVec F (Fin 4)))]
    exact fundamentalDomain_mul_eq_one U b' hb' (isOpen_quatUf _)
  rw [muFinVec_quatUf ha hb] at hfd
  have hnorm : ideleNorm F (nrdUnit u) = absDetInf (nrdInf a b ((uInf u : (QuatInf a b)ˣ) : QuatInf a b)) *
      normFinQ a b (uFin u) := ideleNorm_nrdUnit a b u
  set nI := absDetInf (nrdInf a b ((uInf u : (QuatInf a b)ˣ) : QuatInf a b))
  set nF := normFinQ a b (uFin u)
  set A := muFinVec F (Fin 4) (OHatVec (F := F) (ι := Fin 4))
  have hA0 : A ≠ 0 := muFinVec_OHatVec_ne_zero
  have hAT : A ≠ ⊤ := muFinVec_OHatVec_ne_top
  have hnI : 0 < nI := by
    simp only [nI, absDetInf]
    rw [abs_pos]
    exact det_mulLeft_ne_zero_of_isUnit ((isUnit_iff_isUnit_nrdInf a b _).mp (uInf u).isUnit)
  have hnF : 0 < nF := by
    have := ideleNorm_pos (nrdUnit u)
    rw [hnorm] at this
    exact pos_of_mul_pos_right this hnI.le
  set cI := ENNReal.ofReal (nI ^ 2)
  set cF := ENNReal.ofReal (nF ^ 2)
  have hcI0 : cI ≠ 0 := by simp [cI, hnI.ne']
  have hcF0 : cF ≠ 0 := by simp [cF, hnF.ne']
  have hcIT : cI ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcFT : cF ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinvF : ENNReal.ofReal (nF ^ 2)⁻¹ = cF⁻¹ := ENNReal.ofReal_inv_of_pos (by positivity)
  rw [hinvF] at hfd
  have hP' : muInfVec F (Fin 4) b'.parallelepiped = (cF⁻¹ * A)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hfd
  have hN : ENNReal.ofReal (ideleNorm F (nrdUnit u) ^ 2) = cI * cF := by
    rw [hnorm, mul_pow, ENNReal.ofReal_mul (by positivity)]
  rw [hθ]
  change ENNReal.ofReal (ideleNorm F (nrdUnit u) ^ 2) *
    ∑' z : Submodule.span ℤ (Set.range b''), ENNReal.ofReal (gV (z : Fin 4 → V)) = _
  rw [hP, hcov, hP', hN, ← mul_assoc]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hcI0) (Or.inl hcIT), inv_inv,
    show cI * cF * (cI⁻¹ * (cF⁻¹ * A)) = (cI * cI⁻¹) * (cF * cF⁻¹) * A by ring,
    ENNReal.mul_inv_cancel hcI0 hcIT, ENNReal.mul_inv_cancel hcF0 hcFT, one_mul, one_mul]

end Theta

end

end QuadFormsKB.Tamagawa.Measure.Weil
