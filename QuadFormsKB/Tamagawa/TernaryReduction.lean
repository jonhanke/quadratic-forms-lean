/-
# $\tau(SO_3) = 2$ reduces to the pure quaternion forms

**Layer:** a totally real number field $F$ with $\mathcal O_F$ a PID; `tauSO`; `TernaryTamagawaTwo` and
`QuatZeta.tamagawaNumberTwo_pureForm_iff`.

Every nondegenerate ternary form $Q_0'$ over $\mathcal O_F$ is, after an integral change of lattice, diagonal
(`exists_compMat_eq_diag`: $Q_0'\circ G = \langle e_0, e_1, e_2\rangle$, $\det G \ne 0$), and
$$e_0e_1e_2\cdot\langle e_0,e_1,e_2\rangle\circ\mathrm{diag}(1, 1, e_0e_1) = \langle -a, -b, ab\rangle,\qquad a = -e_0^2e_1e_2,\ b = -e_0e_1^2e_2,$$
the norm form on the pure quaternions of the standard order of $(a,b)_F$ (`pureFormO`; the similarity
$dQ \cong \langle -a,-b,ab\rangle$ made integral). Since the $\tau$ does not depend on the lattice or on rescaling
(`LatChange.tauSO_smul_compMat`):
* `tauSO_eq_tauSO_pureFormO`: $\tau(Q_0') = \tau(\langle -a,-b,ab\rangle)$;
* **`ternaryTamagawaTwo_of_pureForm`**: `TernaryTamagawaTwo F` follows from $\tau = 2$ for the forms $\langle -a,-b,ab\rangle$,
  $a, b \in \mathcal O_F$ (totally definite quaternion algebras $(a,b)_F$ with their standard orders);
* **`ternaryTamagawaTwo_iff_residues`** ($[F:\mathbb Q] \ge 2$): `TernaryTamagawaTwo F` holds **iff** for every totally definite
  $(a,b)_F$ the additive zeta function of the $SO_4$-genus of the standard order has the residue of the zeta function of $D$:
  $\lim_{s\to0^+}sZ^+(s) = \lim_{s\to0^+}sZ_D(s) = \rho_F\int\Phi$ (Weil's comparison, §3.1, p. 40).

So the base case is now exactly Weil's comparison of residues for the standard orders of quaternion algebras over $F$.
-/
import QuadFormsKB.Tamagawa.LatticeChangeGlobal
import QuadFormsKB.Tamagawa.QuaternionZeta
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open Matrix NumberField Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open QuadFormsKB.Lattices QuadFormsKB.QuadForm QuadFormsKB.QuatZeta QuadFormsKB.HilbertModular
  QuadFormsKB.AdditiveZeta QuadFormsKB.GlobalZeta

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem nondegenerate_compMat_of_det {S : QuadForm (𝓞 F) n} (hS : S.Nondegenerate) {G : Matrix (Fin n) (Fin n) (𝓞 F)}
    (hG : G.det ≠ 0) : (S.compMat G).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
  exact mul_ne_zero (mul_ne_zero hG hS) hG

theorem compMat_smul_mat {A : Type*} [CommRing A] (S : QuadForm A n) (t : A) (X : Matrix (Fin n) (Fin n) A) :
    S.compMat (t • X) = t ^ 2 • S.compMat X :=
  eq_of_eval_eq fun y => by
    rw [eval_compMat, eval_smul_form, eval_compMat, Matrix.smul_mulVec, eval_smul_gen]

/-- **Integral diagonalization:** a nondegenerate form over $\mathcal O_F$ becomes diagonal after an integral change of
lattice: $Q_0\circ G = \langle e_0, \dots, e_{n-1}\rangle$ with $G \in M_n(\mathcal O_F)$, $\det G \ne 0$, $e_i \ne 0$ (diagonalize over $F$,
`FieldGen.exists_isometric_diag`, and clear denominators). -/
theorem exists_compMat_eq_diag (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) :
    ∃ G : Matrix (Fin n) (Fin n) (𝓞 F), G.det ≠ 0 ∧ ∃ e : Fin n → 𝓞 F, (∀ i, e i ≠ 0) ∧
      Q₀.compMat G = QuadForm.diag e := by
  classical
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  have hQF : QF.Nondegenerate := nondegenerate_map Q₀ hQ₀
  obtain ⟨c, hc, P, hPdet, hP⟩ := FieldGen.exists_isometric_diag QF hQF
  have hPc : QF.compMat P = QuadForm.diag c := eq_of_eval_eq fun x => by
    rw [eval_compMat]; exact hP x
  -- clear denominators
  obtain ⟨k, hk, hkP⟩ := exists_int_mul_mem (Finset.univ.image fun p : Fin n × Fin n => P p.1 p.2)
  choose G hG using fun i j => hkP (P i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  set Gm : Matrix (Fin n) (Fin n) (𝓞 F) := Matrix.of G
  have hGm : Gm.map (algebraMap (𝓞 F) F) = (k : F) • P := by
    ext i j; simp [Gm, hG i j]
  have hk0 : (k : F) ≠ 0 := by exact_mod_cast hk
  have hdet : Gm.det ≠ 0 := by
    intro h0
    have := congrArg (algebraMap (𝓞 F) F) h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGm, det_smul, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hk0) hPdet.ne_zero this
  have hmap : (Q₀.compMat Gm).map (algebraMap (𝓞 F) F) = ((k : F) ^ 2) • QuadForm.diag c := by
    rw [← map_compMat, hGm, compMat_smul_mat, hPc]
  refine ⟨Gm, hdet, fun i => (Q₀.compMat Gm).coeff i i, fun i h0 => ?_, ?_⟩
  · have := congrArg (fun S : QuadForm F n => S.coeff i i) hmap
    simp only [QuadForm.map, Matrix.map_apply, h0, map_zero, smul_coeff, Matrix.smul_apply, smul_eq_mul,
      QuadForm.diag, diagonal_apply_eq] at this
    exact mul_ne_zero (pow_ne_zero _ hk0) (hc i) this.symm
  · ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.diag]
    · have := congrArg (fun S : QuadForm F n => S.coeff i j) hmap
      simp only [QuadForm.map, Matrix.map_apply, smul_coeff, Matrix.smul_apply, smul_eq_mul, QuadForm.diag,
        diagonal_apply_ne _ hij, mul_zero] at this
      rw [(map_eq_zero_iff _ RingOfIntegers.coe_injective).mp this]
      simp [QuadForm.diag, diagonal_apply_ne _ hij]

open scoped ComplexOrder in
theorem isTotallyPosDef_compMat_of_det {S : QuadForm F n} (hS : IsTotallyPosDef S) {X : Matrix (Fin n) (Fin n) F}
    (hX : X.det ≠ 0) : IsTotallyPosDef (S.compMat X) := by
  intro x hx
  rw [eval_compMat]
  refine hS _ fun h0 => hx ?_
  have := congrArg (fun y => X⁻¹ *ᵥ y) h0
  simpa [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit hX)] using this

open scoped ComplexOrder in
theorem isTotallyPos_mul {x y : F} (hx : IsTotallyPos x) (hy : IsTotallyPos y) : IsTotallyPos (x * y) :=
  fun σ => by rw [map_mul]; exact mul_pos (hx σ) (hy σ)

/-- **The diagonal form is similar to the pure quaternion form:**
$e_0e_1e_2\cdot\langle e_0,e_1,e_2
angle\circ\mathrm{diag}(1,1,e_0e_1) = \langle -a,-b,ab
angle$, $a = -e_0^2e_1e_2$, $b = -e_0e_1^2e_2$. -/
theorem smul_diag_compMat_eq_pureFormO (e : Fin 3 → 𝓞 F) :
    (e 0 * e 1 * e 2) • (QuadForm.diag e).compMat (diagonal ![1, 1, e 0 * e 1]) =
      pureFormO (-(e 0 ^ 2 * e 1 * e 2)) (-(e 0 * e 1 ^ 2 * e 2)) := by
  ext i j
  rw [smul_compMat_diagonal_coeff]
  fin_cases i <;> fin_cases j <;> simp [pureFormO, QuadForm.diag] <;> ring

variable [IsPrincipalIdealRing (𝓞 F)]

/-- **$\tau(Q_0') = \tau(\langle -a,-b,ab\rangle)$** for a suitable totally definite $(a,b)_F$, $a, b \in \mathcal O_F$: every totally
positive definite ternary form over $\mathcal O_F$ ($\mathcal O_F$ a PID) has the Tamagawa number of the pure part of the standard
order of a quaternion algebra. -/
theorem tauSO_eq_tauSO_pureFormO (Q₀' : QuadForm (𝓞 F) 3) (hQ : Q₀'.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀'.map (algebraMap (𝓞 F) F))) :
    ∃ a b : 𝓞 F, a ≠ 0 ∧ b ≠ 0 ∧ IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)) ∧
      tauSO Q₀' = tauSO (pureFormO a b) := by
  obtain ⟨G, hG, e, he, hGe⟩ := exists_compMat_eq_diag Q₀' hQ
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  -- the diagonal form is totally positive definite
  have hpdD : IsTotallyPosDef ((QuadForm.diag e).map (algebraMap (𝓞 F) F)) := by
    rw [← hGe, ← map_compMat]
    exact isTotallyPosDef_compMat_of_det hpd hGF
  have hepos : ∀ i, IsTotallyPos ((e i : 𝓞 F) : F) := fun i => by
    have := hpdD (Pi.single i 1) (by simp)
    rw [eval_single] at this
    simpa [QuadForm.map, QuadForm.diag] using this
  set cv : Fin 3 → 𝓞 F := ![1, 1, e 0 * e 1]
  have hcv : ∀ a, cv a ≠ 0 := by
    intro a; fin_cases a <;> simp [cv, he 0, he 1]
  set c' := e 0 * e 1 * e 2
  have hc' : c' ≠ 0 := mul_ne_zero (mul_ne_zero (he 0) (he 1)) (he 2)
  have hpdP : IsTotallyPosDef ((c' • (QuadForm.diag e).compMat (diagonal cv)).map (algebraMap (𝓞 F) F)) := by
    rw [map_smul_compMat_diagonal]
    intro x hx
    rw [eval_smul_form]
    refine isTotallyPos_mul ?_ ?_
    · show IsTotallyPos (((e 0 * e 1 * e 2 : 𝓞 F)) : F)
      push_cast
      exact isTotallyPos_mul (isTotallyPos_mul (hepos 0) (hepos 1)) (hepos 2)
    · have hD : (diagonal fun a => algebraMap (𝓞 F) F (cv a)).det ≠ 0 := by
        rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.mpr fun a _ => (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (hcv a)
      exact isTotallyPosDef_compMat_of_det hpdD hD x hx
  refine ⟨-(e 0 ^ 2 * e 1 * e 2), -(e 0 * e 1 ^ 2 * e 2), ?_, ?_, ?_, ?_⟩
  · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (he 0)) (he 1)) (he 2))
  · exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (he 0) (pow_ne_zero _ (he 1))) (he 2))
  · rw [← smul_diag_compMat_eq_pureFormO]; exact hpdP
  · have h1 := tauSO_smul_compMat (by norm_num) (by norm_num) Q₀' hQ hpd one_ne_zero G hG (by
      rw [show (1 : 𝓞 F) • Q₀'.compMat G = Q₀'.compMat G by ext a b; simp [smul_coeff], hGe]; exact hpdD)
    rw [show (1 : 𝓞 F) • Q₀'.compMat G = Q₀'.compMat G by ext a b; simp [smul_coeff], hGe] at h1
    have hQD : (QuadForm.diag e).Nondegenerate := by
      rw [← hGe]; exact nondegenerate_compMat_of_det hQ hG
    rw [← h1, ← smul_diag_compMat_eq_pureFormO, tauSO_smul_compMat_diagonal (by norm_num) (by norm_num) _ hQD
      hpdD hc' cv hcv hpdP]

/-- **The base case reduces to the pure quaternion forms** ($\mathcal O_F$ a PID): if $\tau(SO(\langle -a,-b,ab\rangle)) = 2$ for all
$a, b \in \mathcal O_F\setminus 0$ with $\langle -a,-b,ab\rangle$ totally positive definite (the pure parts of the standard orders of
the totally definite quaternion algebras $(a,b)_F$), then `TernaryTamagawaTwo F`. -/
@[kb "weil1982" "§3.7(a), p. 62-63 (SO_3 = D^×/F^×; every ternary space is similar to (D^0, nrd))"]
theorem ternaryTamagawaTwo_of_pureForm
    (h : ∀ a b : 𝓞 F, a ≠ 0 → b ≠ 0 → IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F)) →
      TamagawaNumberTwo (pureFormO a b)) : TernaryTamagawaTwo F :=
  ⟨fun Q₀' hQ hpd _ => by
    obtain ⟨a, b, ha, hb, hpd', he⟩ := tauSO_eq_tauSO_pureFormO Q₀' hQ hpd
    unfold TamagawaNumberTwo; rw [he]; exact h a b ha hb hpd'⟩

open scoped ComplexOrder in
theorem isTotallyPos_sq [IsTotallyReal F] {t : F} (ht : t ≠ 0) : IsTotallyPos (t ^ 2) := fun σ => by
  have hreal := NumberField.IsTotallyReal.complexEmbedding_isReal (K := F) σ.toRingHom
  have him : (σ t).im = 0 := by
    have := congrArg (fun φ : F →+* ℂ => φ t) (NumberField.ComplexEmbedding.isReal_iff.mp hreal)
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq] at this
    exact Complex.conj_eq_iff_im.mp this
  have hre : (σ t).re ≠ 0 := by
    intro h0
    exact (map_ne_zero σ).mpr ht (Complex.ext h0 him)
  rw [map_pow, Complex.lt_def]
  simp only [Complex.zero_re, Complex.zero_im, pow_two, Complex.mul_re, Complex.mul_im, him, mul_zero, sub_zero,
    zero_mul, add_zero]
  exact ⟨mul_self_pos.mpr hre, trivial⟩

open scoped ComplexOrder in
/-- $\langle 1\rangle\perp S$ is totally positive definite when $S$ is ($F$ totally real). -/
theorem isTotallyPosDef_splitForm_one [IsTotallyReal F] {S : QuadForm F n} (hS : IsTotallyPosDef S) :
    IsTotallyPosDef (splitForm 1 S) := by
  intro x hx
  rw [← Fin.cons_self_tail x, eval_splitForm_cons, one_mul, ← pow_two]
  by_cases ht : Fin.tail x = 0
  · have h0 : x 0 ≠ 0 := by
      intro h0; apply hx; rw [← Fin.cons_self_tail x, h0, ht]; ext i; refine Fin.cases ?_ (fun _ => ?_) i <;> simp
    rw [ht, show S.eval (0 : Fin n → F) = 0 by simp [QuadForm.evalIn]]
    simpa using isTotallyPos_sq h0
  · intro σ
    rw [map_add]
    refine add_pos_of_nonneg_of_pos ?_ (hS _ ht σ)
    by_cases h0 : x 0 = 0
    · simp [h0]
    · exact (isTotallyPos_sq h0 σ).le

variable [IsTotallyReal F]

/-- **`TernaryTamagawaTwo` is Weil's comparison of residues for the standard quaternion orders** ($F$ totally real of degree
$\ge 2$, $\mathcal O_F$ a PID): `TernaryTamagawaTwo F` holds iff for all $a, b \in \mathcal O_F$ with $D = (a,b)_F$ totally definite, the
additive zeta function of the $SO_4$-genus of the standard order $\mathcal O_F\langle1,i,j,k\rangle$ has the residue of the zeta
function of $D$: $\lim_{s\to0^+}s\,Z^+(s) = \rho_F\int_{D_\mathbb A}\Phi\,dx$ $(= \lim_{s\to0^+}s\,Z_D(s)$, `QuatZeta.tendsto_mul_zetaD`$)$.
*Proof:* `ternaryTamagawaTwo_of_pureForm` and `QuatZeta.tamagawaNumberTwo_pureForm_iff`. -/
@[kb "weil1982" "§3.1, p. 40 (c = ρ_k); §3.7(a), p. 62; Thm. 3.7.1 (m = 3), p. 65"]
theorem ternaryTamagawaTwo_iff_residues (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    TernaryTamagawaTwo F ↔ ∀ a b : 𝓞 F, IsTotallyPosDef (formF (normForm a b)) →
      Tendsto (fun s => s * genusAdditiveZeta (normForm a b) s) (𝓝[>] 0)
        (𝓝 (dedekindZeta_residue F * phiIntegral (gaussian (normForm a b) Real.pi))) := by
  constructor
  · intro I a b hpd
    have hpd₀ := hpd
    rw [formF, normForm, map_splitForm_alg] at hpd₀
    have hpd' := isTotallyPosDef_of_splitForm hpd₀
    refine (tamagawaNumberTwo_pureForm_iff hd hpd).mp ?_
    exact I.tau_eq_two _ (nondegenerate_of_map hpd'.nondegenerate) hpd' (isIntegral_std _)
  · intro h
    refine ternaryTamagawaTwo_of_pureForm fun a b _ _ hpd => ?_
    have hpdN : IsTotallyPosDef (formF (normForm a b)) := by
      rw [formF, normForm, map_splitForm_alg, map_one]
      exact isTotallyPosDef_splitForm_one hpd
    exact (tamagawaNumberTwo_pureForm_iff hd hpdN).mpr (h a b hpdN)

/-! ### Consequence: $\tau(SO_4) = 2$ for every quaternary genus, given the ternary input -/

omit [IsPrincipalIdealRing (𝓞 F)] in
open scoped ComplexOrder in
theorem realEmb_pos_of_isTotallyPos {x : F} (hx : IsTotallyPos x) (v : InfinitePlace F) : 0 < realEmb F v x := by
  have h := hx v.embedding.toRatAlgHom
  have e : ((realEmb F v x : ℝ) : ℂ) = v.embedding x := InfinitePlace.embedding_of_isReal_apply _ x
  have : (v.embedding.toRatAlgHom : F →ₐ[ℚ] ℂ) x = v.embedding x := rfl
  rw [this, ← e] at h
  exact_mod_cast h

omit [IsPrincipalIdealRing (𝓞 F)] [IsTotallyReal F] in
theorem diag_eq_splitForm {m : ℕ} (e : Fin (m + 1) → 𝓞 F) :
    QuadForm.diag e = splitForm (e 0) (QuadForm.diag fun i => e i.succ) := by
  ext i j
  rw [splitForm_coeff]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [QuadForm.diag, diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- **$\tau(SO_4) = 2$ for every totally positive definite quaternary form over $\mathcal O_F$**, given the ternary input
($F$ totally real of degree $\ge 2$, $\mathcal O_F$ a PID). The split lattices $\mathcal O_Fe_0\perp L'$ are
treated in `TauFour.lean`; change of lattice removes the restriction:
$Q_0\circ G = \langle e_0\rangle\perp\langle e_1, e_2, e_3\rangle$ and $\tau$ is lattice-independent. -/
@[kb "weil1982" "Thm. 3.7.1 (m = 4), p. 65"]
theorem tamagawaNumberTwo_four_all (I : TernaryTamagawaTwo F) (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    TamagawaNumberTwo Q₀ := by
  obtain ⟨G, hG, e, he, hGe⟩ := exists_compMat_eq_diag Q₀ hQ
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdD : IsTotallyPosDef ((QuadForm.diag e).map (algebraMap (𝓞 F) F)) := by
    rw [← hGe, ← map_compMat]
    exact isTotallyPosDef_compMat_of_det hpd hGF
  have h1 := tauSO_smul_compMat (by norm_num) (by norm_num) Q₀ hQ hpd one_ne_zero G hG (by
    rw [show (1 : 𝓞 F) • Q₀.compMat G = Q₀.compMat G by ext a b; simp [smul_coeff], hGe]; exact hpdD)
  rw [show (1 : 𝓞 F) • Q₀.compMat G = Q₀.compMat G by ext a b; simp [smul_coeff], hGe] at h1
  unfold TamagawaNumberTwo
  rw [← h1, diag_eq_splitForm]
  rw [diag_eq_splitForm] at hpdD
  have he0 : IsTotallyPos (((e 0 : 𝓞 F)) : F) := by
    have := hpdD (Pi.single 0 1) (by simp)
    rw [eval_single] at this
    simpa [QuadForm.map, splitForm_coeff] using this
  exact tamagawaNumberTwo_four I hd (fun v => realEmb_pos_of_isTotallyPos he0 v) _ hpdD (isIntegral_std _)

/-- **The mass formula for every totally positive definite quaternary genus**, given the ternary input. -/
@[kb "weil1982" "Thm. 3.7.1 (m = 4), p. 65; mass formula"]
theorem massFormula_four_all (I : TernaryTamagawaTwo F) (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    MassFormulaHolds Q₀ :=
  massFormula _ hQ (by norm_num) hpd (isIntegral_std _) (tamagawaNumberTwo_four_all I hd Q₀ hQ hpd)

/-- **The ternary and quaternary base cases are equivalent for all genera** ($F$ totally real of degree $\ge 2$, $\mathcal O_F$ a
PID): `TernaryTamagawaTwo F` iff $\tau(SO(Q_0)) = 2$ for every totally positive definite quaternary $Q_0$ over $\mathcal O_F$. -/
@[kb "weil1982" "Thm. 3.7.1, p. 65 (m = 3 ⟺ m = 4)"]
theorem ternaryTamagawaTwo_iff_four_all (hd : 2 ≤ Fintype.card (InfinitePlace F)) :
    TernaryTamagawaTwo F ↔ ∀ Q₀ : QuadForm (𝓞 F) 4, Q₀.Nondegenerate →
      IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)) → TamagawaNumberTwo Q₀ := by
  refine ⟨fun I Q₀ hQ hpd => tamagawaNumberTwo_four_all I hd Q₀ hQ hpd, fun h => ⟨fun Q₀' _ hpd' _ => ?_⟩⟩
  have hpd : IsTotallyPosDef ((splitForm 1 Q₀').map (algebraMap (𝓞 F) F)) := by
    rw [map_splitForm_alg, map_one]; exact isTotallyPosDef_splitForm_one hpd'
  have h1 : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F 1) := fun v => by simp
  exact tamagawaNumberTwo_three_of_four hd h1 Q₀' hpd (isIntegral_std _)
    (h _ (nondegenerate_of_map hpd.nondegenerate) hpd)

end QuadFormsKB.Tamagawa.LatChange
