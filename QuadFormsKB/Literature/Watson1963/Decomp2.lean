/-
# Watson (1963): the shape of a form over $\mathbb Z_2$

For an integral form $f$ in $n$ variables let $F$ be $f$ over $\mathbb Z_2$ and $H_F$ its Hessian. This file splits
$\mathbb Z_2^n$ as $H\mathbb Z_2^{2k} \oplus K\mathbb Z_2^{m}$ ($2k + m = n$), orthogonally for $H_F$, where
* the Gram matrix $H^{\mathsf T} H_F H$ has unit determinant (an even unimodular part $U$ of rank $2k$), and
* the complement $\psi = F \circ K$ has a Hessian $\equiv 0 \pmod 2$ (maximality: $2k$ is the rank of $H_F$ modulo $2$),

and relates $k$ to Watson's rank modulo $2$: $2k \le r_2(f) \le 2k + 1$, with $r_2(f) \le 2k$ if $\psi$ takes only
even values (`exists_decomp_two`). Everything is stated with the matrices $H$, $K$ (no change of dimension).

If $F$ is square-free at $2$ (`SqFree2`, true for Watson-minimal $f$), then so is $\psi$ in the sense of
`SqFreePsi` (`sqFreePsi_of_decomp`).

The linear algebra (`exists_complement_of_left_inverse`) generalizes `exists_complement_of_unimodular_pid` to a
sublattice with a given orthogonal projection, which is also used for the splitting of $\Phi_4$.
-/
import QuadFormsKB.Literature.Watson1963.SqFree

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

/-! ### Complements over a principal ideal domain -/

section Complement

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- **Complement of a sublattice with an orthogonal projection, over a principal ideal domain $R$.** Let $A$ be an
$n \times n$ matrix, $H$ an $n \times v$ matrix and $L$ a $v \times n$ matrix with $LH = 1$ such that every $k$ with
$Lk = 0$ is $A$-orthogonal to the columns of $H$. Then there are $m$ with $v + m = n$ and an $n \times m$ matrix $K$
with columns $A$-orthogonal to those of $H$ such that every vector is uniquely $H\vec y + K\vec c$. -/
theorem exists_complement_of_left_inverse {n v : ℕ} (A : Matrix (Fin n) (Fin n) R) (H : Matrix (Fin n) (Fin v) R)
    (L : Matrix (Fin v) (Fin n) R) (hLH : L * H = 1) (horth : ∀ k, L *ᵥ k = 0 → Hᵀ *ᵥ (A *ᵥ k) = 0) :
    ∃ (m : ℕ) (_ : v + m = n) (K : Matrix (Fin n) (Fin m) R),
      (∀ (y : Fin v → R) (c : Fin m → R), (H *ᵥ y) ⬝ᵥ (A *ᵥ (K *ᵥ c)) = 0) ∧
      (∀ z : Fin n → R, ∃ (y : Fin v → R) (c : Fin m → R), z = H *ᵥ y + K *ᵥ c) ∧
      (∀ (y : Fin v → R) (c : Fin m → R), H *ᵥ y + K *ᵥ c = 0 → y = 0 ∧ c = 0) := by
  let Kr : Submodule R (Fin n → R) := LinearMap.ker (Matrix.mulVecLin L)
  let b := Module.finBasis R Kr
  have hmem : ∀ k : Fin n → R, k ∈ Kr ↔ L *ᵥ k = 0 := fun k => by simp [Kr]
  let e : (Fin n → R) ≃ₗ[R] (Fin v → R) × Kr :=
    { toFun := fun z => (L *ᵥ z, ⟨z - H *ᵥ (L *ᵥ z), by
        rw [hmem, mulVec_sub, mulVec_mulVec, hLH, one_mulVec, sub_self]⟩)
      map_add' := fun z w => by
        apply Prod.ext
        · simp [mulVec_add]
        · apply Subtype.ext
          simp [mulVec_add]; abel
      map_smul' := fun r z => by
        apply Prod.ext
        · show L *ᵥ (r • z) = r • (L *ᵥ z)
          rw [mulVec_smul]
        · apply Subtype.ext
          show r • z - H *ᵥ (L *ᵥ (r • z)) = r • (z - H *ᵥ (L *ᵥ z))
          rw [mulVec_smul, mulVec_smul, smul_sub]
      invFun := fun p => H *ᵥ p.1 + (p.2 : Fin n → R)
      left_inv := fun z => by simp
      right_inv := fun p => by
        have hk : L *ᵥ (p.2 : Fin n → R) = 0 := (hmem _).1 p.2.2
        apply Prod.ext
        · simp [mulVec_add, mulVec_mulVec, hLH, hk]
        · apply Subtype.ext
          simp [mulVec_add, mulVec_mulVec, hLH, hk] }
  have hrank : n = v + Module.finrank R Kr := by
    have := e.finrank_eq
    simpa [Module.finrank_prod] using this
  have hK : ∀ c, (Matrix.of fun (i : Fin n) (c : Fin (Module.finrank R Kr)) => ((b c : Kr) : Fin n → R) i) *ᵥ c
      = ((b.equivFun.symm c : Kr) : Fin n → R) := fun c => by
    ext i
    simp [mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank R Kr, hrank.symm,
    Matrix.of fun i c => ((b c : Kr) : Fin n → R) i, ?_, ?_, ?_⟩
  · intro y c
    rw [hK]
    have hk : L *ᵥ ((b.equivFun.symm c : Kr) : Fin n → R) = 0 := (hmem _).1 (b.equivFun.symm c).2
    have h0 := horth _ hk
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, h0, zero_dotProduct]
  · intro z
    refine ⟨(e z).1, b.equivFun (e z).2, ?_⟩
    have hz : z = H *ᵥ (e z).1 + ((e z).2 : Fin n → R) := (e.symm_apply_apply z).symm
    rw [hK, LinearEquiv.symm_apply_apply]
    exact hz
  · intro y c h
    rw [hK] at h
    have hk : L *ᵥ ((b.equivFun.symm c : Kr) : Fin n → R) = 0 := (hmem _).1 (b.equivFun.symm c).2
    have hy : y = 0 := by
      have := congrArg (L *ᵥ ·) h
      simp only [mulVec_add, mulVec_mulVec, hLH, one_mulVec, hk, add_zero, mulVec_zero] at this
      exact this
    refine ⟨hy, ?_⟩
    rw [hy, mulVec_zero, zero_add] at h
    have : (b.equivFun.symm c : Kr) = 0 := Subtype.ext h
    exact (LinearEquiv.map_eq_zero_iff _).1 this

/-- **Complement of a unimodular sublattice** (with uniqueness): the case $L = (H^{\mathsf T}AH)^{-1}H^{\mathsf T}A$ of
`exists_complement_of_left_inverse`. -/
theorem exists_complement_unimodular' {n v : ℕ} (A : Matrix (Fin n) (Fin n) R) (H : Matrix (Fin n) (Fin v) R)
    (hB : IsUnit (Hᵀ * A * H).det) :
    ∃ (m : ℕ) (_ : v + m = n) (K : Matrix (Fin n) (Fin m) R),
      (∀ (y : Fin v → R) (c : Fin m → R), (H *ᵥ y) ⬝ᵥ (A *ᵥ (K *ᵥ c)) = 0) ∧
      (∀ z : Fin n → R, ∃ (y : Fin v → R) (c : Fin m → R), z = H *ᵥ y + K *ᵥ c) ∧
      (∀ (y : Fin v → R) (c : Fin m → R), H *ᵥ y + K *ᵥ c = 0 → y = 0 ∧ c = 0) := by
  set B := Hᵀ * A * H with hBdef
  refine exists_complement_of_left_inverse A H (B⁻¹ * (Hᵀ * A)) ?_ fun k hk => ?_
  · rw [Matrix.mul_assoc, ← hBdef, Matrix.nonsing_inv_mul _ hB]
  · have : Hᵀ * A = B * (B⁻¹ * (Hᵀ * A)) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]
    rw [mulVec_mulVec, this, ← mulVec_mulVec, hk, mulVec_zero]

/-- **The isometry with an orthogonal sum from complement data.** If $Q(H\vec y) = \varphi(\vec y)$, the columns of
$K$ are orthogonal to those of $H$ and every vector is $H\vec y + K\vec c$, then $Q \cong \varphi \perp (Q \circ K)$
(`hm ▸` casts $\mathrm{Fin}(v+m)$ to $\mathrm{Fin}\,n$). -/
theorem isometricGL_of_complement {n v m : ℕ} (hm : v + m = n) {Q : QuadForm R n} {φ : QuadForm R v}
    (H : Matrix (Fin n) (Fin v) R) (hH : ∀ y, Q.eval (H *ᵥ y) = φ.eval y) (K : Matrix (Fin n) (Fin m) R)
    (horth : ∀ (y : Fin v → R) (c : Fin m → R), (H *ᵥ y) ⬝ᵥ (Q.hessian *ᵥ (K *ᵥ c)) = 0)
    (hspan : ∀ z : Fin n → R, ∃ (y : Fin v → R) (c : Fin m → R), z = H *ᵥ y + K *ᵥ c) :
    IsometricGL Q (hm ▸ QuadForm.orthSum φ (Q.compMat K)) := by
  subst hm
  let T : Matrix (Fin (v + m)) (Fin (v + m)) R :=
    Matrix.of fun i j => Fin.append (fun a => H i a) (fun b => K i b) j
  have hT : ∀ x, T *ᵥ x = H *ᵥ (fun a => x (Fin.castAdd m a)) + K *ᵥ (fun b => x (Fin.natAdd v b)) := by
    intro x; ext i
    simp [T, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have surj : ∀ z : Fin (v + m) → R, ∃ x, T *ᵥ x = z := by
    intro z
    obtain ⟨y, c, hz⟩ := hspan z
    refine ⟨Fin.append y c, ?_⟩
    rw [hT]
    simpa [Fin.append_left, Fin.append_right] using hz.symm
  choose S hS using surj
  let S' : Matrix (Fin (v + m)) (Fin (v + m)) R := Matrix.of fun i j => S (Pi.single j 1) i
  have hTS : T * S' = 1 := by
    ext i j
    have := congrFun (hS (Pi.single j 1)) i
    simp only [mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, S', Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
  have hST : S' * T = 1 := mul_eq_one_comm.mp hTS
  refine ⟨⟨T, S', hTS, hST⟩, fun x => ?_⟩
  show Q.eval (T *ᵥ x) = (QuadForm.orthSum φ (Q.compMat K)).eval x
  rw [hT]
  have hpol := QuadForm.eval_polar Q (H *ᵥ fun a => x (Fin.castAdd m a)) (K *ᵥ fun b => x (Fin.natAdd v b))
  rw [horth] at hpol
  show _ = (QuadForm.orthSum φ (Q.compMat K)).evalIn R x
  rw [QuadForm.evalIn_orthSum]
  show _ = φ.eval _ + (Q.compMat K).eval _
  rw [QuadForm.eval_compMat, ← hH]
  linear_combination hpol

end Complement

/-! ### Ranks modulo $2$ -/

section Ranks

variable {n : ℕ}

theorem hessMod2_map (f : QuadForm ℤ n) :
    hessMod2 (f.map (Int.castRingHom ℤ_[2])) = f.hessian.map (algebraMap ℤ (ZMod 2)) := by
  unfold hessMod2
  rw [QuadForm.hessian_map, Matrix.map_map]
  ext i j
  simp

/-- **The Hessian rank modulo $2$ is at most $r_2$:** $R_2(f)$ lies in the kernel of $\bar H_f$. -/
theorem rank_hessian_le_rankModP (f : QuadForm ℤ n) :
    (f.hessian.map (algebraMap ℤ (ZMod 2))).rank ≤ rankModP 2 f := by
  set M := f.hessian.map (algebraMap ℤ (ZMod 2))
  have hMs : Mᵀ = M := by rw [← Matrix.transpose_map, hessian_isSymm']
  have hvm : ∀ x : Fin n → ZMod 2, x ᵥ* M = M *ᵥ x := fun x => by
    conv_lhs => rw [← hMs]
    exact vecMul_transpose M x
  have hle : radModP 2 f ≤ LinearMap.ker M.mulVecLin := by
    intro x hx
    have h : ∀ z, x ⬝ᵥ (M *ᵥ z) = 0 := ((mem_radModP 2).1 hx).2
    show M *ᵥ x = 0
    funext i
    have := h (Pi.single i 1)
    rw [dotProduct_mulVec, hvm, dotProduct_single_one] at this
    exact this
  have e1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have e2 := Submodule.finrank_mono hle
  have e3 := rankModP_add_finrank 2 f
  simp only [Module.finrank_fin_fun] at e1
  have : M.rank = Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := rfl
  omega

/-- **A unimodular Gram matrix bounds the Hessian rank modulo $2$ from below:** if $X^{\mathsf T}H_Q X$ is invertible
($X$ an $n \times v$ matrix over $\mathbb Z_2$), then $v \le \operatorname{rank}(\bar H_Q)$. -/
theorem le_rank_hessMod2_of_gram {v : ℕ} (Q : QuadForm ℤ_[2] n) (X : Matrix (Fin n) (Fin v) ℤ_[2])
    (hX : IsUnit (Xᵀ * Q.hessian * X).det) : v ≤ (hessMod2 Q).rank := by
  have h1 : (Xᵀ * Q.hessian * X).map PadicInt.toZMod =
      (X.map PadicInt.toZMod)ᵀ * hessMod2 Q * X.map PadicInt.toZMod := by
    unfold hessMod2; rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have h2 : IsUnit ((Xᵀ * Q.hessian * X).map PadicInt.toZMod).det := by
    have : ((Xᵀ * Q.hessian * X).map PadicInt.toZMod).det = PadicInt.toZMod (Xᵀ * Q.hessian * X).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hX.map _
  have h3 := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h2)
  rw [h1] at h3
  have h4 := Matrix.rank_mul_le_left ((X.map PadicInt.toZMod)ᵀ * hessMod2 Q) (X.map PadicInt.toZMod)
  have h5 := Matrix.rank_mul_le_right (X.map PadicInt.toZMod)ᵀ (hessMod2 Q)
  simp only [Fintype.card_fin] at h3
  omega

end Ranks

/-! ### The decomposition -/

section Decomp

variable {n : ℕ}

theorem toZMod_ne_zero_of_not_dvd {b : ℤ_[2]} (hb : ¬ (2 : ℤ_[2]) ∣ b) : PadicInt.toZMod b ≠ 0 := fun h => by
  have := (toZMod_eq_zero_iff_dvd 2 b).1 h
  exact hb (by exact_mod_cast this)

/-- Helper: a binary Gram matrix with even $(0,0)$ entry and odd symmetric off-diagonal entries has unit
determinant. -/
theorem isUnit_det_two_of_odd (A : Matrix (Fin 2) (Fin 2) ℤ_[2]) (ha : (2 : ℤ_[2]) ∣ A 0 0)
    (hs : A 1 0 = A 0 1) (hb : ¬ (2 : ℤ_[2]) ∣ A 0 1) : IsUnit A.det := by
  apply isUnit_of_toZMod_ne_zero
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, toZMod_eq_zero_of_two_dvd ha, zero_mul, zero_sub, hs]
  have := toZMod_ne_zero_of_not_dvd hb
  exact neg_ne_zero.2 (mul_ne_zero this this)

/-- Helper: $(E^{\mathsf T} M E)_{ab} = M_{\sigma(a)\sigma(b)}$ for $E$ the columns $e_{\sigma(a)}$. -/
theorem transpose_mul_mul_submatrix_one {R : Type*} [CommRing R] {m v : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (σ : Fin v → Fin m) (a b : Fin v) :
    (((1 : Matrix (Fin m) (Fin m) R).submatrix id σ)ᵀ * M * (1 : Matrix (Fin m) (Fin m) R).submatrix id σ) a b =
      M (σ a) (σ b) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.one_apply, id, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Shape of a form over $\mathbb Z_2$** (see the module docstring). For an integral form $f$ in $n$ variables, with
$F = f$ over $\mathbb Z_2$: there are $k, m$ with $2k + m = n$, an $n \times 2k$ matrix $H$ and an $n \times m$ matrix
$K$ over $\mathbb Z_2$ such that
* $H^{\mathsf T}H_F H$ has unit determinant;
* the columns of $K$ are $H_F$-orthogonal to those of $H$, and every vector is uniquely $H\vec y + K\vec c$;
* $\psi = F \circ K$ has all Hessian entries even;
* $2k \le r_2(f) \le 2k + 1$, and $r_2(f) \le 2k$ if $\psi$ takes only even values.
Argument: the form `f`. -/
theorem exists_decomp_two (f : QuadForm ℤ n) :
    ∃ (k m : ℕ) (_ : 2 * k + m = n) (H : Matrix (Fin n) (Fin (2 * k)) ℤ_[2]) (K : Matrix (Fin n) (Fin m) ℤ_[2]),
      IsUnit (Hᵀ * (f.map (Int.castRingHom ℤ_[2])).hessian * H).det ∧
      (∀ y c, (H *ᵥ y) ⬝ᵥ ((f.map (Int.castRingHom ℤ_[2])).hessian *ᵥ (K *ᵥ c)) = 0) ∧
      (∀ z, ∃ y c, z = H *ᵥ y + K *ᵥ c) ∧
      (∀ y c, H *ᵥ y + K *ᵥ c = 0 → y = 0 ∧ c = 0) ∧
      (∀ i j, (2 : ℤ_[2]) ∣ ((f.map (Int.castRingHom ℤ_[2])).compMat K).hessian i j) ∧
      2 * k ≤ rankModP 2 f ∧ rankModP 2 f ≤ 2 * k + 1 ∧
      ((∀ c, (2 : ℤ_[2]) ∣ (f.map (Int.castRingHom ℤ_[2])).eval (K *ᵥ c)) → rankModP 2 f ≤ 2 * k) := by
  classical
  set F := f.map (Int.castRingHom ℤ_[2]) with hFdef
  set ρ := (f.hessian.map (algebraMap ℤ (ZMod 2))).rank with hρ
  set k := (ρ + 1) / 2 with hk
  have hk1 : 2 * k ≤ ρ + 1 := by omega
  have hk2 : ρ ≤ 2 * k := by omega
  have hrF : (hessMod2 F).rank = ρ := by rw [hFdef, hessMod2_map]
  obtain ⟨H, hH⟩ := exists_gram_unit k F (by rw [hrF]; exact hk1)
  obtain ⟨m, hm, K, horth, hspan, huniq⟩ := exists_complement_unimodular' F.hessian H hH
  have hρ2k : 2 * k ≤ ρ := by have := le_rank_hessMod2_of_gram F H hH; omega
  have hrρ := rank_hessian_le_rankModP f
  have hr1 := rankModP_two_le_rank_add_one f
  have hpsi : ∀ i j, (2 : ℤ_[2]) ∣ (F.compMat K).hessian i j := by
    intro i j
    by_contra hodd
    have hij : i ≠ j := by
      rintro rfl
      exact hodd ⟨(F.compMat K).coeff i i, by
        rw [show (F.compMat K).hessian i i = (F.compMat K).coeff i i + (F.compMat K).coeff i i from rfl]; ring⟩
    -- the columns K eᵢ, K eⱼ
    let E : Matrix (Fin m) (Fin 2) ℤ_[2] := (1 : Matrix (Fin m) (Fin m) ℤ_[2]).submatrix id ![i, j]
    let P : Matrix (Fin n) (Fin 2) ℤ_[2] := K * E
    have hPc : ∀ c, P *ᵥ c = K *ᵥ (E *ᵥ c) := fun c => by rw [mulVec_mulVec]
    let T : Matrix (Fin n) (Fin (2 * k + 2)) ℤ_[2] :=
      Matrix.of fun r c => Fin.append (fun a => H r a) (fun b => P r b) c
    have hT : ∀ z, T *ᵥ z = H *ᵥ (fun a => z (Fin.castAdd 2 a)) + P *ᵥ (fun b => z (Fin.natAdd (2 * k) b)) := by
      intro z; ext r
      simp [T, mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hQT : F.compMat T = QuadForm.orthSum (F.compMat H) (F.compMat P) := by
      refine QuadForm.eq_of_eval_eq fun z => ?_
      rw [QuadForm.eval_compMat, hT]
      show _ = (QuadForm.orthSum (F.compMat H) (F.compMat P)).evalIn ℤ_[2] z
      rw [QuadForm.evalIn_orthSum]
      show _ = (F.compMat H).eval _ + (F.compMat P).eval _
      rw [QuadForm.eval_compMat, QuadForm.eval_compMat]
      have hpol := QuadForm.eval_polar F (H *ᵥ (fun a => z (Fin.castAdd 2 a)))
        (P *ᵥ (fun b => z (Fin.natAdd (2 * k) b)))
      rw [hPc, horth] at hpol
      rw [hPc]
      linear_combination hpol
    set M := (F.compMat K).hessian with hMdef
    have hMs : ∀ a b, M a b = M b a := fun a b => by
      have := congrFun (congrFun (hessian_isSymm' (F.compMat K)) b) a
      simpa [Matrix.transpose_apply] using this
    have hdetT : IsUnit (Tᵀ * F.hessian * T).det := by
      rw [← QuadForm.hessian_compMat, hQT, hessian_orthSum_det]
      refine IsUnit.mul (by rw [QuadForm.hessian_compMat]; exact hH) ?_
      have hPh : (F.compMat P).hessian = Eᵀ * M * E := by
        rw [QuadForm.hessian_compMat, hMdef, QuadForm.hessian_compMat]
        simp only [P, Matrix.transpose_mul, Matrix.mul_assoc]
      have hent : ∀ a b, (Eᵀ * M * E) a b = M (![i, j] a) (![i, j] b) := fun a b =>
        transpose_mul_mul_submatrix_one M ![i, j] a b
      rw [hPh]
      refine isUnit_det_two_of_odd _ ?_ ?_ ?_
      · rw [hent]
        exact ⟨(F.compMat K).coeff i i, by
          simp only [Matrix.cons_val_zero, hMdef]
          rw [show (F.compMat K).hessian i i = (F.compMat K).coeff i i + (F.compMat K).coeff i i from rfl]; ring⟩
      · rw [hent, hent]; simpa using hMs j i
      · rw [hent]; simpa using hodd
    have := le_rank_hessMod2_of_gram F T hdetT
    omega
  refine ⟨k, m, by omega, H, K, hH, horth, hspan, huniq, hpsi, by omega, by omega, ?_⟩
  -- all values even ⇒ r ≤ 2k
  · intro hev
    have hsurj : ∀ c : Fin m → ZMod 2, ∃ ch : Fin m → ℤ_[2], (fun a => PadicInt.toZMod (ch a)) = c := by
      intro c
      choose ch hch using fun a => ZMod.ringHom_surjective (PadicInt.toZMod (p := 2)) (c a)
      exact ⟨ch, funext hch⟩
    have hsurjn : ∀ c : Fin n → ZMod 2, ∃ ch : Fin n → ℤ_[2], (fun a => PadicInt.toZMod (ch a)) = c := by
      intro c
      choose ch hch using fun a => ZMod.ringHom_surjective (PadicInt.toZMod (p := 2)) (c a)
      exact ⟨ch, funext hch⟩
    set Kb := K.map PadicInt.toZMod
    have hKb : ∀ ch : Fin m → ℤ_[2], Kb *ᵥ (fun a => PadicInt.toZMod (ch a)) =
        fun r => PadicInt.toZMod ((K *ᵥ ch) r) := fun ch => by
      funext r; simp [Kb, mulVec, dotProduct, map_sum, map_mul]
    have hdotz : ∀ v w : Fin n → ℤ_[2], (fun r => PadicInt.toZMod (v r)) ⬝ᵥ
        (f.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ fun r => PadicInt.toZMod (w r)) =
        PadicInt.toZMod (v ⬝ᵥ (F.hessian *ᵥ w)) := fun v w => by
      rw [hFdef, QuadForm.hessian_map]
      simp [dotProduct, mulVec, map_sum, map_mul]
    have hsymF : ∀ v w : Fin n → ℤ_[2], v ⬝ᵥ (F.hessian *ᵥ w) = w ⬝ᵥ (F.hessian *ᵥ v) := fun v w => by
      rw [dotProduct_mulVec, ← mulVec_transpose, hessian_isSymm', dotProduct_comm]
    have hle : LinearMap.range Kb.mulVecLin ≤ radModP 2 f := by
      rintro _ ⟨c, rfl⟩
      obtain ⟨ch, rfl⟩ := hsurj c
      show Kb *ᵥ _ ∈ radModP 2 f
      rw [hKb]
      refine (mem_radModP 2).2 ⟨?_, fun z => ?_⟩
      · rw [← map_evalIn_hom, ← eval_map_padic, ← hFdef]
        exact toZMod_eq_zero_of_two_dvd (hev ch)
      · obtain ⟨zh, rfl⟩ := hsurjn z
        rw [hdotz]
        apply toZMod_eq_zero_of_two_dvd
        obtain ⟨y, c', rfl⟩ := hspan zh
        rw [mulVec_add, dotProduct_add, hsymF (K *ᵥ ch) (H *ᵥ y), horth, zero_add]
        have : (K *ᵥ ch) ⬝ᵥ (F.hessian *ᵥ (K *ᵥ c')) = ch ⬝ᵥ ((F.compMat K).hessian *ᵥ c') := by
          rw [QuadForm.hessian_compMat, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec ch Kᵀ,
            vecMul_transpose]
        rw [this]
        refine Finset.dvd_sum fun a _ => Dvd.dvd.mul_left ?_ _
        simp only [mulVec, dotProduct]
        exact Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (hpsi a b) _
    have hinj : Function.Injective Kb.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      obtain ⟨ch, rfl⟩ := hsurj c
      have h0 : Kb *ᵥ (fun a => PadicInt.toZMod (ch a)) = 0 := hc
      rw [hKb] at h0
      have h2 : ∀ r, (2 : ℤ_[2]) ∣ (K *ᵥ ch) r := fun r => by
        have := (toZMod_eq_zero_iff_dvd 2 _).1 (congrFun h0 r)
        exact_mod_cast this
      choose w hw using h2
      have hKw : K *ᵥ ch = (2 : ℤ_[2]) • w := funext fun r => by rw [hw r]; rfl
      obtain ⟨y, c', hwc⟩ := hspan w
      have hz : H *ᵥ ((-2 : ℤ_[2]) • y) + K *ᵥ (ch - (2 : ℤ_[2]) • c') = 0 := by
        rw [mulVec_smul, mulVec_sub, mulVec_smul, hKw, hwc]
        ext r
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
        ring
      obtain ⟨-, hc0⟩ := huniq _ _ hz
      funext a
      have ha : ch a = 2 * c' a := by
        have := congrFun hc0 a
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        linear_combination this
      simp only [Pi.zero_apply]
      rw [ha]
      exact toZMod_eq_zero_of_two_dvd (dvd_mul_right 2 _)
    have e1 := LinearMap.finrank_range_of_inj hinj
    have e2 := Submodule.finrank_mono hle
    have e3 := rankModP_add_finrank 2 f
    simp only [Module.finrank_fin_fun] at e1
    omega

end Decomp

end QuadFormsKB.Watson1963
