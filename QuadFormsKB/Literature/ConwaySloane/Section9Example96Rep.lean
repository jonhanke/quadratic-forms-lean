/-
# Conway–Sloane, Ch. 15, §9.6: the second spinor genus is represented by $\begin{pmatrix}6&3&0\\3&6&0\\0&0&2\end{pmatrix}$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.6, p. 393
(`conwaysloane1999`): for the form
$$f = \begin{pmatrix} 2 & 1 & 0\\ 1 & 2 & 0\\ 0 & 0 & 18\end{pmatrix}$$
the genus contains two spinor genera, "the second represented by" the form
$\begin{pmatrix}6&3&0\\3&6&0\\0&0&2\end{pmatrix}$.

**Layer.** $f$ = `csQ A96` on $V = \mathbb Q^3$, the lattice $L = \mathbb Z^3$ (`stdLat`), Conway–Sloane's set
$\Pi = \{2, 3\}$ (`P96`), all from `Section9Example96.lean`.

**Defines**
* `BM96`: the matrix $B = \begin{pmatrix}1&2&0\\1&-1&0\\0&0&1/3\end{pmatrix} \in \mathrm{GL}_3(\mathbb Q)$, whose columns
  are $e_0 + e_1$, $2e_0 - e_1$, $\tfrac13 e_2$ (0-based coordinates);
* `M96` $= B\,\mathbb Z^3 = \mathbb Z(e_0+e_1) + \mathbb Z(2e_0-e_1) + \mathbb Z\tfrac13e_2$. Its Gram matrix for $f$ is
  $B^{\mathsf T} f B = \begin{pmatrix}6&3&0\\3&6&0\\0&0&2\end{pmatrix}$ (`BM96_gram`);
* `σ96` $= \tau_x\tau_y$ with $x = 3e_0 - e_2$, $y = e_2$ (so $Q(x) = 36$, $Q(y) = 18$): a rational rotation with
  $\sigma_3\mathbb Z_3^3 = M_3$ (`σ96 = B U` with $U \in \mathrm{GL}_3(\mathbb Z_{(3)})$, `U96`);
* `α96` $\in O(V)(\mathbb A_f)$: $\sigma$ at $3$, $1$ at every other prime; `latSMul_α96`: $\alpha L = M$.

**Proves** (all **unconditional**)
* `example96_rep_sameGenus`: $M$ is in the genus of $\mathbb Z^3$;
* `example96_rep_not_sameProperSpinorGenus`: $M$ is not in the proper spinor genus of $\mathbb Z^3$. The spinor norm
  of $\sigma$ is $Q(x)Q(y) = 648 = 2\cdot 18^2$, and $2 = (u_-)_3$ is a non-residue unit at $3$, not in
  $\langle 3\rangle\mathbb Q_3^{\times2} \supseteq \theta(O^+(\mathbb Z_3^3))$ (`theta3_le`); by Cassels' Theorem 3.1
  and its Corollary (`casselsAct_of_smul`, `casselsAct_unique`) $M$ lies in the spinor genus $g\,\mathcal S_L$ with
  $g$ the class of $(u_-)_3$, which is nontrivial by Theorem 17 (`not_mem_casselsST_of_qClass`);
* `example96_rep_second_class`: no isometry of $(\mathbb Q^3, f)$ maps $\mathbb Z^3$ onto $M$ (the coordinate swap
  $e_0 \leftrightarrow e_1$ is an improper automorph of $\mathbb Z^3$).

Since $\mathrm{gen}(f)$ has exactly the two spinor genera of the book only together with the upper bound (Cassels'
group has order $2$), here the claim "the second spinor genus is represented by $M$" is formalized as "$M$ is in the
genus and not in the spinor genus of $f$".
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Example96

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

local notation "F3" => v3.adicCompletion ℚ

/-! ### The lattice $M$ -/

/-- The basis matrix $B$ of $M$: columns $e_0 + e_1$, $2e_0 - e_1$, $\tfrac13 e_2$; $\det B = -1$. -/
def BM96 : GL (Fin 3) ℚ :=
  ⟨!![1, 2, 0; 1, -1, 0; 0, 0, 1/3], !![1/3, 2/3, 0; 1/3, -1/3, 0; 0, 0, 3],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- **The lattice $M = \mathbb Z(e_0+e_1) + \mathbb Z(2e_0-e_1) + \mathbb Z\tfrac13 e_2 = B\,\mathbb Z^3$** of
Conway–Sloane §9.6, p. 393. -/
def M96 : Lat ℚ 3 := Lat.image BM96 stdLat

/-- **The Gram matrix of $M$**: $B^{\mathsf T} f B = \begin{pmatrix}6&3&0\\3&6&0\\0&0&2\end{pmatrix}$, the form named
by the book for the second spinor genus. -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (the second spinor genus is represented by [[6,3,0],[3,6,0],[0,0,2]])"]
theorem BM96_gram :
    BM96.valᵀ * A96.map (Int.cast : ℤ → ℚ) * BM96.val = !![6, 3, 0; 3, 6, 0; 0, 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [BM96, A96, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

/-! ### The rotation $\sigma = \tau_x\tau_y$ -/

/-- $x = 3e_0 - e_2$. -/
def x96 : Fin 3 → ℚ := ![3, 0, -1]

/-- $y = e_2$. -/
def y96 : Fin 3 → ℚ := ![0, 0, 1]

theorem two_mul_evalIn_A96 (z : Fin 3 → ℚ) :
    2 * (csQ A96).evalIn ℚ z = z ⬝ᵥ (!![4, 2, 0; 2, 4, 0; 0, 0, 36] *ᵥ z) := by
  have h := two_mul_evalIn (csQ A96) z
  rw [csQ_A96_hessian] at h
  rw [h]
  simp

theorem evalIn_x96 : (csQ A96).evalIn ℚ x96 = 36 := by
  have h := two_mul_evalIn_A96 x96
  simp [x96, dotProduct, mulVec, Fin.sum_univ_three] at h
  show (csQ A96).evalIn ℚ ![3, 0, -1] = 36
  linarith

theorem evalIn_y96 : (csQ A96).evalIn ℚ y96 = 18 := by
  have h := two_mul_evalIn_A96 y96
  simp [y96, dotProduct, mulVec, Fin.sum_univ_three] at h
  show (csQ A96).evalIn ℚ ![0, 0, 1] = 18
  linarith

theorem symmVec_x96 : symmVec (csQ A96) ℚ x96 = ![1/3, 1/6, -1] := by
  rw [symmVec, evalIn_x96, csQ_A96_hessian]
  ext i
  fin_cases i <;> norm_num [x96]

theorem symmVec_y96 : symmVec (csQ A96) ℚ y96 = ![0, 0, 2] := by
  rw [symmVec, evalIn_y96, csQ_A96_hessian]
  ext i
  fin_cases i <;> norm_num [y96]

theorem x96_ne : (csQ A96).evalIn ℚ x96 ≠ 0 := by rw [evalIn_x96]; norm_num

theorem y96_ne : (csQ A96).evalIn ℚ y96 ≠ 0 := by rw [evalIn_y96]; norm_num

theorem symm_x96_val : ((Lattices.symm (csQ A96) ℚ x96 : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) =
    !![0, -1/2, 3; 0, 1, 0; 1/3, 1/6, 0] := by
  rw [symm_val _ _ x96_ne, QuadForm.reflMat, symmVec_x96]
  ext i j
  rw [Matrix.sub_apply, vecMulVec_apply]
  fin_cases i <;> fin_cases j <;> norm_num [x96]

theorem symm_y96_val : ((Lattices.symm (csQ A96) ℚ y96 : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) =
    !![1, 0, 0; 0, 1, 0; 0, 0, -1] := by
  rw [symm_val _ _ y96_ne, QuadForm.reflMat, symmVec_y96]
  ext i j
  rw [Matrix.sub_apply, vecMulVec_apply]
  fin_cases i <;> fin_cases j <;> norm_num [y96]

/-- **The rotation $\sigma = \tau_x\tau_y$** ($x = 3e_0 - e_2$, $y = e_2$), with matrix
$\begin{pmatrix}0&-1/2&-3\\0&1&0\\1/3&1/6&0\end{pmatrix}$ (`σ96_val`). -/
def σ96 : orthGroup (csQ A96) ℚ := Lattices.symm (csQ A96) ℚ x96 * Lattices.symm (csQ A96) ℚ y96

theorem σ96_val : ((σ96 : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) = !![0, -1/2, -3; 0, 1, 0; 1/3, 1/6, 0] := by
  rw [σ96, Subgroup.coe_mul, Units.val_mul, symm_x96_val, symm_y96_val]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

theorem σ96_det : ((σ96 : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).det = 1 := by
  rw [σ96_val, Matrix.det_fin_three]; norm_num

/-- $U = B^{-1}\sigma$, so that $\sigma = BU$. -/
def U96 : GL (Fin 3) ℚ := BM96⁻¹ * (σ96 : GL (Fin 3) ℚ)

theorem U96_val : U96.val = !![0, 1/2, -1; 0, -1/2, -1; 1, 1/2, 0] := by
  rw [U96, Units.val_mul, σ96_val]
  show !![1/3, 2/3, 0; 1/3, -1/3, 0; 0, 0, 3] * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three]

theorem σ96_eq : (σ96 : GL (Fin 3) ℚ) = BM96 * U96 := by
  rw [U96, mul_inv_cancel_left]

/-! ### Localizations -/

theorem valued_three_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ v3) :
    Valued.v (3 : v.adicCompletion ℚ) = 1 := by
  have h := valued_intCast_eq_one v 3 (by
    intro hd
    apply hv
    have hp := Rat.HeightOneSpectrum.prime_natGenerator v
    have hd' : Rat.HeightOneSpectrum.natGenerator v ∣ 3 := by exact_mod_cast hd
    have h3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd'
    exact primeOf_injective (h3.trans primeOf_v3.symm))
  simpa using h

/-- Away from $3$: $M_p = \mathbb Z_p^3$. -/
theorem loc_M96_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ v3) :
    loc v M96.1 = loc v (stdLat : Lat ℚ 3).1 := by
  have hT : ∀ i j, BM96.val i j ∈ locSub v := by
    intro i j
    have h2 : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by simpa using valued_intCast_le_one' v 2
    rw [mem_locSub]
    fin_cases i <;> fin_cases j <;> simp [BM96, valued_three_of_ne hv, h2]
  have hdet : BM96.val.det = 1 ∨ BM96.val.det = -1 :=
    Or.inr (by simp [BM96, Matrix.det_fin_three]; norm_num)
  have h := loc_latOf_eq_std v BM96 hT hdet
  exact h.trans (loc_intVec v).symm

/-- At $3$: $\sigma_3\mathbb Z_3^3 = M_3$. -/
theorem loc_M96_v3 :
    locAct v3 ((orthMap (csQ A96) F3 σ96 : orthGroup (csQ A96) F3) : GL (Fin 3) F3)
      (loc v3 (stdLat : Lat ℚ 3).1) = loc v3 M96.1 := by
  have hU : ∀ i j, U96.val i j ∈ locSub v3 := by
    intro i j
    rw [mem_locSub, U96_val]
    fin_cases i <;> fin_cases j <;> simp [valued_v3_two]
  have hdet : U96.val.det = 1 ∨ U96.val.det = -1 :=
    Or.inr (by rw [U96_val, Matrix.det_fin_three]; norm_num)
  have hstd := loc_latOf_eq_std v3 U96 hU hdet
  have e1 : locAct v3 ((orthMap (csQ A96) F3 σ96 : orthGroup (csQ A96) F3) : GL (Fin 3) F3)
      (loc v3 (stdLat : Lat ℚ 3).1) = loc v3 (glImage (σ96 : GL (Fin 3) ℚ) (stdLat : Lat ℚ 3).1) := by
    rw [loc_glImage]; rfl
  rw [e1, σ96_eq, glImage_mul]
  show loc v3 (glImage BM96 (latOf U96)) = loc v3 (glImage BM96 intVec)
  rw [loc_glImage, loc_glImage, hstd, loc_intVec]

/-! ### The adelic rotation $\alpha$ -/

open Classical in
/-- **The adelic rotation $\alpha$**: $\alpha_3 = \sigma$, $\alpha_p = 1$ for $p \ne 3$. -/
def α96 : OAf (csQ A96) :=
  ⟨fun v => if v = v3 then orthMap (csQ A96) (v.adicCompletion ℚ) σ96 else 1, by
    filter_upwards [Filter.eventually_cofinite_ne v3] with v hv
    simp only [hv, ↓reduceIte]
    exact (stdStab (csQ A96) v).one_mem⟩

theorem α96_v3 : α96 v3 = orthMap (csQ A96) F3 σ96 := by
  classical
  show (if v3 = v3 then _ else _) = _
  simp

theorem α96_of_ne {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ v3) : α96 v = 1 := by
  classical
  show (if v = v3 then _ else _) = _
  simp [hv]

/-- **$\alpha\,\mathbb Z^3 = M$.** -/
theorem latSMul_α96 : latSMul (csQ A96) α96 stdLat = M96 := by
  refine Subtype.ext (loc_injective (latSMul (csQ A96) α96 stdLat).2 M96.2 fun v => ?_)
  rw [loc_latSMul]
  by_cases hv : v = v3
  · subst hv
    rw [α96_v3]
    exact loc_M96_v3
  · rw [α96_of_ne hv, loc_M96_of_ne hv]
    exact locAct_one _

theorem α96_mem_soSub (v : HeightOneSpectrum (𝓞 ℚ)) : α96 v ∈ Tamagawa.soSub (csQ A96) (v.adicCompletion ℚ) := by
  by_cases hv : v = v3
  · subst hv
    rw [α96_v3, Tamagawa.mem_soSub]
    show ((σ96 : GL (Fin 3) ℚ).val.map (algebraMap ℚ F3)).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, σ96_det, map_one]
  · rw [α96_of_ne hv]
    exact (Tamagawa.soSub _ _).one_mem

/-- **The spinor norm of $\sigma_3$**: $\theta(\sigma_3) = Q(x)Q(y) = 648 = 2 \cdot 18^2$, the class of $2$. -/
theorem spinorNorm_α96_v3 : spinorNorm (csQ A96) F3 (α96 v3) = sqClassOf (2 : F3) := by
  rw [α96_v3, σ96, spinorNorm_orthMap_symm_mul (csQ A96) A96_nondeg v3 x96_ne y96_ne, evalIn_x96, evalIn_y96,
    show (36 * 18 : ℚ) = 2 * 18 ^ 2 by norm_num, map_mul, map_pow, map_ofNat, map_ofNat,
    sqClassOf_mul two_ne_zero (pow_ne_zero 2 (by norm_num)),
    (sqClassOf_eq_one_iff (pow_ne_zero 2 (by norm_num))).mpr ⟨_, sq _⟩, mul_one]

/-! ### $2$ is not automorphous at $3$ -/

/-- $2$ is not a square in $\mathbb Q_3$. -/
theorem not_isSquare_two_padic_three : ¬ IsSquare (2 : ℚ_[3]) := by
  rintro ⟨y, hy⟩
  have h2 : ‖(2 : ℚ_[3])‖ = 1 := by
    have h1 := Padic.norm_int_le_one (p := 3) 2
    have h2 : ¬ ‖((2 : ℤ) : ℚ_[3])‖ < 1 := by
      rw [Padic.norm_intCast_lt_one_iff]; norm_num
    have : ‖((2 : ℤ) : ℚ_[3])‖ = 1 := le_antisymm h1 (not_lt.mp h2)
    simpa using this
  have hn : ‖y‖ = 1 := by
    have h := congrArg norm hy
    rw [h2, norm_mul] at h
    nlinarith [norm_nonneg y]
  let z : ℤ_[3] := ⟨y, hn.le⟩
  have hz : z * z = 2 := Subtype.ext (by show y * y = 2; exact hy.symm)
  have h := congrArg PadicInt.toZMod hz
  rw [map_mul, map_ofNat] at h
  revert h
  generalize PadicInt.toZMod z = w
  revert w
  decide

theorem not_isSquare_two_v3 : ¬ IsSquare (2 : F3) := by
  rintro ⟨y, hy⟩
  have hp3 : ((Rat.HeightOneSpectrum.primesEquiv v3 : Nat.Primes) : ℕ) = 3 := primeOf_v3
  have key : ∀ (p : Nat.Primes), (p : ℕ) = 3 → ¬ IsSquare (2 : ℚ_[p]) := by
    rintro ⟨p, hp⟩ (rfl : p = 3)
    exact not_isSquare_two_padic_three
  refine key _ hp3 ⟨Rat.HeightOneSpectrum.adicCompletion.padicEquiv v3 y, ?_⟩
  rw [← map_mul, ← hy, map_ofNat]

/-- The unit $2 \in \mathbb Z_3^\times$ ($= (u_-)_3$). -/
def u96 : (q3.1.adicCompletion ℚ)ˣ := Units.mk0 2 two_ne_zero

open scoped Classical in
/-- The family $(u_-)_3$: $2$ at $3$, $1$ at $2$. -/
def xR96 : CasselsR P96 := Pi.mulSingle q3 u96

open scoped Classical in
/-- **$(u_-)_3 = 2$ is not in the spinor kernel**: as `mulSingle_neg_one_not_mem`, with the non-residue $2$ in place
of $-1$. -/
theorem xR96_not_mem : xR96 ∉ casselsST (csQ A96) A96_nondeg stdLat P96 := by
  classical
  refine not_mem_casselsST_of_qClass (csQ A96) A96_nondeg stdLat P96 (by norm_num) q3
    (fun A hA => theta3_le A hA) ?_ ?_ ?_ ?_
  · intro p hpq A hA
    obtain ⟨k, hk⟩ := theta2_even p.1 (primeOf_eq_two_of_ne_q3 p hpq) A hA
    have hord : ordP P96 p A = -k * 2 := by
      rw [ordP, hk, log_exp]; ring
    have e : casselsDiag P96 (natGenUnit p.1 ^ ordP P96 p A) q3 =
        (casselsDiag P96 (natGenUnit p.1 ^ (-k)) q3) ^ 2 := by
      rw [hord, _root_.zpow_mul, map_zpow, Pi.pow_apply]
      exact zpow_ofNat _ 2
    rw [e, (SqClass.mk_eq_one_iff _).mpr ⟨_, rfl⟩]
    exact Subgroup.one_mem _
  · rw [casselsJ_A96, map_one, Pi.one_apply]
    exact Subgroup.one_mem _
  · intro p
    by_cases hp : p = q3
    · subst hp
      rw [xR96, Pi.mulSingle_eq_same]
      exact valued_v3_two
    · rw [xR96, Pi.mulSingle_eq_of_ne hp]; simp
  · rw [xR96, Pi.mulSingle_eq_same]
    intro hmem
    rcases mem_zpowers_q3 hmem with h | h
    · apply not_isSquare_two_v3
      rw [← sqClassOf_eq_one_iff (two_ne_zero : (2 : F3) ≠ 0), sqClassOf_of_ne_zero two_ne_zero]
      exact h
    · have h' : sqClassOf (2 : F3) = sqClassOf (3 : F3) := by
        rw [sqClassOf_of_ne_zero (two_ne_zero : (2 : F3) ≠ 0)]
        exact h.trans sqClass_primeUnit_q3
      have hm : sqClassOf ((2 : F3) * 3⁻¹) = 1 := by
        rw [sqClassOf_mul two_ne_zero (by norm_num), h', ← sqClassOf_mul (by norm_num) (by norm_num),
          mul_inv_cancel₀ three_ne_zero, sqClassOf_one]
      refine not_isSquare_of_valued_eq_exp_odd (k := 0) ?_ ((sqClassOf_eq_one_iff (by norm_num)).mp hm)
      rw [map_mul, map_inv₀, valued_v3_two, valued_v3_three, one_mul, ← WithZero.exp_neg]
      norm_num

/-! ### The headline results -/

/-- **$M$ is in the genus of $\mathbb Z^3$** (Conway–Sloane §9.6, p. 393): $M = \alpha\,\mathbb Z^3$ for the adelic
rotation $\alpha$ (`latSMul_α96`). **Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (the second spinor genus is represented by [[6,3,0],[3,6,0],[0,0,2]])"]
theorem example96_rep_sameGenus : SameGenus (csQ A96) (stdLat : Lat ℚ 3).1 M96.1 := by
  have h := sameGenus_latSMul (csQ A96) α96 stdLat
  rwa [latSMul_α96] at h

/-- **The second spinor genus is represented by $M$** (Conway–Sloane §9.6, p. 393: "the second represented by
$\begin{pmatrix}6&3&0\\3&6&0\\0&0&2\end{pmatrix}$"): the lattice $M$ (`M96`, Gram matrix `BM96_gram`) is not in the
proper spinor genus of $\mathbb Z^3$. Proof: $M = \alpha\,\mathbb Z^3$ with $\alpha$ supported at $3$ of spinor norm
$2 = (u_-)_3$, so by Cassels' Theorem 3.1, Corollary, $M$ is in $g\,\mathcal S_{\mathbb Z^3}$ with $g$ the class of
$(u_-)_3$, and $g \ne 1$ (`xR96_not_mem`). **Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (the second spinor genus is represented by [[6,3,0],[3,6,0],[0,0,2]])"]
theorem example96_rep_not_sameProperSpinorGenus : ¬ SameProperSpinorGenus (csQ A96) stdLat M96 := by
  classical
  intro hLM
  have hP := casselsCond_std (by norm_num) _ A96_nondeg P96
    (primeSet_spec A96_symm (by rw [A96_det]; norm_num))
  have hn : 3 ≤ 3 := le_rfl
  have hθ : ∀ v : P96, SqClass.mk (xR96 v) = spinorNorm (csQ A96) (v.1.adicCompletion ℚ) (α96 v.1) := by
    intro v
    by_cases hv : v = q3
    · subst hv
      rw [xR96, Pi.mulSingle_eq_same]
      show SqClass.mk (Units.mk0 (2 : F3) two_ne_zero) = spinorNorm (csQ A96) F3 (α96 v3)
      exact (sqClassOf_of_ne_zero two_ne_zero).symm.trans spinorNorm_α96_v3.symm
    · have hv' : v.1 ≠ v3 := fun h => hv (Subtype.ext h)
      rw [xR96, Pi.mulSingle_eq_of_ne hv, α96_of_ne hv', ← spinorNormHom_apply (csQ A96) _ A96_nondeg, map_one]
      rfl
  have hact := casselsAct_of_smul (csQ A96) A96_nondeg stdLat P96 hn hP (SameGenus.refl _ _) α96
    (fun v _ => α96_mem_soSub v) (fun v hv => α96_of_ne (fun h => hv (h ▸ v3_mem))) xR96 hθ
  rw [latSMul_α96] at hact
  have h1 : CasselsAct (csQ A96) A96_nondeg stdLat P96 (QuotientGroup.mk (1 : CasselsR P96)) stdLat
      (latSMul (csQ A96) 1 stdLat) := by
    refine casselsAct_of_smul (csQ A96) A96_nondeg stdLat P96 hn hP (SameGenus.refl _ _) 1
      (fun v _ => (Tamagawa.soSub _ _).one_mem) (fun _ _ => rfl) 1 fun v => ?_
    rw [show ((1 : OAf (csQ A96)) v) = 1 from rfl, ← spinorNormHom_apply (csQ A96) _ A96_nondeg, map_one]
    rfl
  have e : latSMul (csQ A96) (1 : OAf (csQ A96)) stdLat = stdLat := by
    let _ : MulAction (OAf (csQ A96)) (Lat ℚ 3) := latAction (csQ A96)
    exact one_smul (OAf (csQ A96)) stdLat
  rw [e] at h1
  have h2 : CasselsAct (csQ A96) A96_nondeg stdLat P96 (QuotientGroup.mk xR96) stdLat stdLat := by
    obtain ⟨Γ', h1', h2', α, h3, h4, y, h5, h6, h7⟩ := hact
    exact ⟨Γ', h1', h2', α, h3, h4, y, h5, h6, SameProperSpinorGenus.trans _ hLM h7⟩
  have h12 := casselsAct_unique (csQ A96) A96_nondeg stdLat P96 hn hP (SameGenus.refl _ _) h2 h1
  apply xR96_not_mem
  rw [← QuotientGroup.eq_one_iff, h12]
  rfl

/-- **$M$ is a second class** (Conway–Sloane §9.6, p. 393): no isometry of $(\mathbb Q^3, f)$ maps $\mathbb Z^3$ onto
$M$, although $M$ is in the genus of $\mathbb Z^3$ (`example96_rep_sameGenus`). The swap of the first two coordinates
is an improper integral automorph of $\mathbb Z^3$, so an isometry $\mathbb Z^3 \to M$ would give a proper one.
**Unconditional.** -/
@[kb "conwaysloane1999" "Ch. 15, §9.6, p. 393 (the second spinor genus is represented by [[6,3,0],[3,6,0],[0,0,2]])"]
theorem example96_rep_second_class (σ : orthGroup (csQ A96) ℚ) :
    glImage (σ : GL (Fin 3) ℚ) (stdLat : Lat ℚ 3).1 ≠ M96.1 := by
  obtain ⟨α, hdet, hαL⟩ := exists_improper_swap A96 A96_symm 0 1 (by decide)
    (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  exact not_isometric_of_not_sameProperSpinorGenus (csQ A96) A96_nondeg stdLat
    example96_rep_not_sameProperSpinorGenus hdet hαL σ

end QuadFormsKB.ConwaySloane
