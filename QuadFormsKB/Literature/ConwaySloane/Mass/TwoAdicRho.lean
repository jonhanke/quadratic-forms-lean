/-
# $\alpha_2(U \perp 2B) = \rho\,\alpha_2(U)\,\alpha_2(2B)$ for every unimodular $U$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, and §12, p. 281 (bibliography key `conwaysloane1988`); J. W. S. Cassels, *Rational Quadratic
Forms*, Ch. 8, Lemma 4.2 and Corollary (`cassels1978`).

**The splitting step at $p = 2$ with arbitrary types.** For $U$ ($a \times a$) a block model of exponent $0$ (unimodular,
of type I or II) and $B$ ($b \times b$) integral symmetric with $\det B \ne 0$, the block count identity
(`card_fromBlocks_eq_sum`) over $\mathbb Z/2^r$ reads
$$N_r(U \perp 2B) = \sum_W \#\{Y : Y^{\mathsf T}U'_WY = U\}\cdot\#\{Z : Z^{\mathsf T}C'_WZ = 2B\},\qquad
U'_W = U + 2W^{\mathsf T}BW,\ C'_W = 2B + 4BWU^{-1}W^{\mathsf T}B.$$
* the first factor is $N_r(U)$ if $U'_W$ is $\mathbb Z_2$-equivalent to $U$ (`Good`) and $0$ otherwise ($r \ge 3$:
  a solution modulo $8$ already gives a $\mathbb Z_2$-equivalence, `dyadic_zpEquiv_of_int`);
* when $U'_W \sim U$, the second factor is $N_r(2B)$: the matrix $T_W = \begin{pmatrix}1 & -U^{-1}W^{\mathsf T}C\\ W &
  1\end{pmatrix}$ is in $GL(\mathbb Z_2)$ and $T_W^{\mathsf T}(U \perp C)T_W = U'_W \perp C'_W$, so
  $U \perp 2B \sim U \perp C'_W$, and the unimodular $U$ cancels (`zpEquiv_cancel_dyMat`, Cassels' Lemma 4.2), so
  $C'_W \sim 2B$. The perturbed second block never has to be classified.

Hence $N_r(U \perp 2B) = \#\{W : U'_W \sim U\}\,N_r(U)\,N_r(2B)$ (`countN_blk_two_rho`). Whether $U'_W \sim U$ depends
only on $W$ modulo $4$, so with
$$\rho(U, B) = 4^{-ab}\,\#\{W \in M_{b\times a}(\mathbb Z/4) : U + 2W^{\mathsf T}BW \sim U\}$$
(`rho`), $\alpha_2(U \perp 2B) = \rho(U, B)\,\alpha_2(U)\,\alpha_2(2B)$ (`alphaP_blk_two_rho`) and
$m_2(U \perp 2B) = m_2(U)\,m_2(B)\,2^{a(b + \operatorname{ord}_2\det B)/2}/\rho(U, B)$ (`pMassDensity_blk_two_rho`).
This reduces the open step of formula (3) at $p = 2$ to statements about unimodular forms only. Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicCancel

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

variable {a b : ℕ}

/-! ### The condition on $W$ -/

/-- $U + 2W^{\mathsf T}BW$ is $\mathbb Z_2$-equivalent to $U$. -/
def Good (U : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) (W : Matrix (Fin b) (Fin a) ℤ) : Prop :=
  ZpEquiv (U.map (Int.cast : ℤ → ℚ_[2])) ((U + (2 : ℤ) • (Wᵀ * B * W)).map (Int.cast : ℤ → ℚ_[2]))

theorem allDvd_quad_sub {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    {W W' : Matrix (Fin b) (Fin a) ℤ} (hW : AllDvd 4 (W' - W)) :
    AllDvd 8 ((U + (2 : ℤ) • (W'ᵀ * B * W')) - (U + (2 : ℤ) • (Wᵀ * B * W))) := by
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin b) (Fin a) ℤ, W' = W + (4 : ℤ) • E := by
    refine ⟨Matrix.of fun i j => (W' i j - W i j) / 4, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have := hW i j
    simp only [Matrix.sub_apply] at this
    rw [Int.mul_ediv_cancel' this]; ring
  have e : (U + (2 : ℤ) • (W'ᵀ * B * W')) - (U + (2 : ℤ) • (Wᵀ * B * W)) =
      (8 : ℤ) • (Eᵀ * B * W + Wᵀ * B * E + (4 : ℤ) • (Eᵀ * B * E)) := by
    rw [hE]
    simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  intro i j
  exact ⟨(Eᵀ * B * W + Wᵀ * B * E + (4 : ℤ) • (Eᵀ * B * E)) i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩

/-- $\det(U + 2K) \equiv \det U \pmod 2$. -/
theorem not_two_dvd_det_add {m : ℕ} {U : Matrix (Fin m) (Fin m) ℤ} (hU : ¬ 2 ∣ U.det) (K : Matrix (Fin m) (Fin m) ℤ) :
    ¬ 2 ∣ (U + (2 : ℤ) • K).det := by
  have e : (U + (2 : ℤ) • K).map (Int.castRingHom (ZMod 2)) = U.map (Int.castRingHom (ZMod 2)) := by
    ext i j
    simp only [map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, eq_intCast,
      Int.cast_ofNat]
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp [h2]
  have h1 : (Int.castRingHom (ZMod 2)) (U + (2 : ℤ) • K).det = (Int.castRingHom (ZMod 2)) U.det := by
    rw [RingHom.map_det, RingHom.map_det]; exact congrArg Matrix.det e
  intro h2
  apply hU
  have h3 : (Int.castRingHom (ZMod 2)) (U + (2 : ℤ) • K).det = 0 := by
    rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h2
  rw [h1, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  exact_mod_cast h3

theorem good_of_allDvd {U : Matrix (Fin a) (Fin a) ℤ} (hUs : Uᵀ = U) (hU : ¬ 2 ∣ U.det)
    {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) {W W' : Matrix (Fin b) (Fin a) ℤ} (hW : AllDvd 4 (W' - W))
    (h : Good U B W) : Good U B W' := by
  refine h.trans (dyadic_zpEquiv_of_int _ _ 1 ?_ ?_ ?_ (by simp) fun i j => ?_)
  · rw [transpose_add, transpose_smul, quad_symm hBs, hUs]
  · rw [transpose_add, transpose_smul, quad_symm hBs, hUs]
  · exact Int.not_even_iff_odd.mp (fun he => not_two_dvd_det_add hU _ (even_iff_two_dvd.mp he))
  · have := allDvd_quad_sub (U := U) (B := B) hW i j
    simp only [transpose_one, Matrix.one_mul, Matrix.mul_one]
    obtain ⟨c, hc⟩ := this
    rw [Matrix.sub_apply] at hc
    exact ⟨-c, by linarith⟩

/-! ### The first factor of the block count -/

section First

variable {r : ℕ} [NeZero (2 ^ r)] {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}

theorem pertU_red (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) :
    pertU (red r U) ((2 : ZMod (2 ^ r)) • red r B) W = red r (U + (2 : ℤ) • ((lift W)ᵀ * B * lift W)) := by
  rw [pertU, red_add, red_smul, red_mul, red_mul, red_transpose, red_lift]
  simp [Matrix.smul_mul, Matrix.mul_smul]

theorem isUnit_red_det (hU : ¬ 2 ∣ U.det) : IsUnit (red r U).det := by
  rw [show (red r U).det = ((U.det : ℤ) : ZMod (2 ^ r)) from
    (RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) U).symm]
  exact isUnit_odd hU

/-- **The first factor when $U'_W \sim U$**: it is $N_r(U)$. -/
theorem card_first_of_good (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) (h : Good U B (lift W)) :
    Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) //
      Yᵀ * pertU (red r U) ((2 : ZMod (2 ^ r)) • red r B) W * Y = red r U} = countN 2 r U := by
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h r
  rw [pertU_red]
  change Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) //
      Yᵀ * (U + (2 : ℤ) • ((lift W)ᵀ * B * lift W)).map (Int.castRingHom (ZMod (2 ^ r))) * Y =
        U.map (Int.castRingHom (ZMod (2 ^ r)))} = _
  rw [← hGe, card_congr_unit hG]
  rfl

theorem not_two_dvd_of_isUnit {z : ℤ} (hr : 1 ≤ r) (h : IsUnit (z : ZMod (2 ^ r))) : ¬ 2 ∣ z := by
  rintro ⟨k, rfl⟩
  push_cast at h
  have hn : IsNilpotent ((2 : ZMod (2 ^ r)) * k) := (Commute.all _ _).isNilpotent_mul_right (two_nilpotent r)
  have : Nontrivial (ZMod (2 ^ r)) := ZMod.nontrivial_iff.mpr (by
    have : 2 ≤ 2 ^ r := by calc 2 = 2 ^ 1 := by norm_num
                                _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    omega)
  exact hn.not_isUnit h

theorem allDvd_of_red_eq {m k : Type*} {X Y : Matrix m k ℤ} (h : red r X = red r Y) : AllDvd (2 ^ r) (X - Y) := by
  intro i j
  have := congrFun (congrFun h i) j
  simp only [map_apply, Int.coe_castRingHom] at this
  have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub (Y i j) (X i j) (2 ^ r)).mp this.symm
  simpa using h'

/-- **The first factor when $U'_W \not\sim U$**: it is $0$ ($r \ge 3$). -/
theorem card_first_of_not_good (hr : 3 ≤ r) (hUs : Uᵀ = U) (hU : ¬ 2 ∣ U.det) (hBs : Bᵀ = B)
    (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) (h : ¬ Good U B (lift W)) :
    Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) //
      Yᵀ * pertU (red r U) ((2 : ZMod (2 ^ r)) • red r B) W * Y = red r U} = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨Y, hY⟩ => h ?_⟩
  rw [pertU_red] at hY
  set U' := U + (2 : ℤ) • ((lift W)ᵀ * B * lift W) with hU'
  have hU's : U'ᵀ = U' := by rw [hU', transpose_add, transpose_smul, quad_symm hBs, hUs]
  have hU'd : ¬ 2 ∣ U'.det := not_two_dvd_det_add hU _
  -- the lift of `Y`
  have hY' : red r ((lift Y)ᵀ * U' * lift Y) = red r U := by
    rw [red_mul, red_mul, red_transpose, red_lift]; exact hY
  have hdY : ¬ 2 ∣ (lift Y).det := by
    refine not_two_dvd_of_isUnit (r := r) (by omega) ?_
    rw [show (((lift Y).det : ℤ) : ZMod (2 ^ r)) = (red r (lift Y)).det from
      RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) (lift Y), red_lift]
    have hd := congrArg Matrix.det hY
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
    have hu := isUnit_red_det (r := r) hU
    rw [← hd] at hu
    exact isUnit_of_mul_isUnit_right hu
  have h8 := allDvd_of_red_eq hY'
  refine (dyadic_zpEquiv_of_int U' U (lift Y) hU's hUs (Int.not_even_iff_odd.mp fun he =>
    hU'd (even_iff_two_dvd.mp he)) (Int.not_even_iff_odd.mp fun he => hdY (even_iff_two_dvd.mp he))
    fun i j => ?_).symm
  have := (pow_dvd_pow (2 : ℤ) hr).trans (h8 i j)
  norm_num at this
  exact this

end First

/-! ### Congruence over $\mathbb Z_2$ -/

section ZEq

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- $N = T^{\mathsf T}MT$ for an invertible $T$ over $\mathbb Z_2$. -/
def ZEq (M N : Matrix ι ι ℤ_[2]) : Prop := ∃ T : Matrix ι ι ℤ_[2], IsUnit T ∧ Tᵀ * M * T = N

theorem ZEq.refl (M : Matrix ι ι ℤ_[2]) : ZEq M M := ⟨1, isUnit_one, by simp⟩

theorem ZEq.trans {M N P : Matrix ι ι ℤ_[2]} (h₁ : ZEq M N) (h₂ : ZEq N P) : ZEq M P := by
  obtain ⟨T, hT, rfl⟩ := h₁; obtain ⟨S, hS, rfl⟩ := h₂
  exact ⟨T * S, hT.mul hS, by simp [transpose_mul, Matrix.mul_assoc]⟩

theorem ZEq.symm {M N : Matrix ι ι ℤ_[2]} (h : ZEq M N) : ZEq N M := by
  obtain ⟨T, hT, rfl⟩ := h
  obtain ⟨u, rfl⟩ := hT
  set v : Matrix ι ι ℤ_[2] := ((u⁻¹ : (Matrix ι ι ℤ_[2])ˣ) : Matrix ι ι ℤ_[2]) with hv
  refine ⟨v, (u⁻¹).isUnit, ?_⟩
  have h1 : (u : Matrix ι ι ℤ_[2]) * v = 1 := Units.mul_inv u
  have h1t : vᵀ * (u : Matrix ι ι ℤ_[2])ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  calc _ = (vᵀ * (u : Matrix ι ι ℤ_[2])ᵀ) * M * ((u : Matrix ι ι ℤ_[2]) * v) := by
          simp only [Matrix.mul_assoc]
    _ = M := by rw [h1t, h1, Matrix.one_mul, Matrix.mul_one]

theorem ZEq.fromBlocks {A A' : Matrix ι ι ℤ_[2]} {D D' : Matrix κ κ ℤ_[2]} (h₁ : ZEq A A') (h₂ : ZEq D D') :
    ZEq (Matrix.fromBlocks A 0 0 D) (Matrix.fromBlocks A' 0 0 D') := by
  obtain ⟨T, hT, rfl⟩ := h₁; obtain ⟨S, hS, rfl⟩ := h₂
  refine ⟨Matrix.fromBlocks T 0 0 S, ?_, by simp [fromBlocks_transpose, fromBlocks_multiply]⟩
  obtain ⟨u, rfl⟩ := hT; obtain ⟨v, rfl⟩ := hS
  exact ⟨⟨Matrix.fromBlocks u 0 0 v, Matrix.fromBlocks ↑u⁻¹ 0 0 ↑v⁻¹, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, rfl⟩

theorem ZEq.submatrix {M N : Matrix ι ι ℤ_[2]} (h : ZEq M N) (e : κ ≃ ι) :
    ZEq (M.submatrix e e) (N.submatrix e e) := by
  obtain ⟨T, hT, rfl⟩ := h
  refine ⟨T.submatrix e e, ?_, ?_⟩
  · have := hT.map (Matrix.reindexAlgEquiv ℤ_[2] ℤ_[2] e.symm)
    simpa [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply] using this
  · rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ e.bijective, ← submatrix_mul _ _ _ _ _ e.bijective]

/-- `ZpEquiv` of the images in $\mathbb Q_2$ is congruence over $\mathbb Z_2$. -/
theorem zpEquiv_coe_iff {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℤ_[2]} :
    ZpEquiv (M.map PadicInt.Coe.ringHom) (N.map PadicInt.Coe.ringHom) ↔ ZEq M N := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T.val, T.isUnit, ?_⟩
    apply Matrix.map_injective (f := PadicInt.Coe.ringHom) (fun x y hxy => Subtype.ext hxy)
    simpa [Matrix.map_mul, Matrix.transpose_map] using hT
  · rintro ⟨T, hT, rfl⟩
    refine ⟨hT.unit, ?_⟩
    simp [Matrix.map_mul, Matrix.transpose_map]

/-- A congruence over $\mathbb Z_2$ reduces to a congruence modulo $2^r$. -/
theorem ZEq.map {M N : Matrix ι ι ℤ_[2]} (h : ZEq M N) (r : ℕ) :
    ∃ G : Matrix ι ι (ZMod (2 ^ r)), IsUnit G ∧
      Gᵀ * M.map (PadicInt.toZModPow r) * G = N.map (PadicInt.toZModPow r) := by
  obtain ⟨T, hT, rfl⟩ := h
  refine ⟨T.map (PadicInt.toZModPow r), hT.map (RingHom.mapMatrix (PadicInt.toZModPow r)), ?_⟩
  simp [Matrix.map_mul, Matrix.transpose_map]

end ZEq

/-! ### The second factor of the block count -/

section Second

variable {L : List DyBlock} {B : Matrix (Fin b) (Fin b) ℤ}

theorem det_odd_of_zero (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) : ¬ 2 ∣ (intMat L).det := by
  obtain ⟨u, hu, h⟩ := det_intMat L hv
  have h0 : (L.map bVal).sum = 0 := List.sum_eq_zero fun x hx => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    simp [bVal, he c hc]
  rw [h, h0, pow_zero, one_mul]
  exact hu

theorem map_coe_int {m k : Type*} (M : Matrix m k ℤ) :
    (M.map (Int.castRingHom ℤ_[2])).map PadicInt.Coe.ringHom = M.map (Int.cast : ℤ → ℚ_[2]) := by
  ext i j; simp

theorem map_red_int {r : ℕ} {m k : Type*} (M : Matrix m k ℤ) :
    (M.map (Int.castRingHom ℤ_[2])).map (PadicInt.toZModPow r) = red r M := by
  ext i j; simp

theorem map_nonsing_inv' {R S : Type*} [CommRing R] [CommRing S] {m : Type*} [Fintype m] [DecidableEq m]
    (f : R →+* S) (M : Matrix m m R) (hM : IsUnit M.det) : (M⁻¹).map f = (M.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hM, Matrix.map_one _ f.map_zero f.map_one]

/-- A form with all entries in $2\mathbb Z_2$ is not properly primitive. -/
theorem not_pp_two_smul {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ_[2]) :
    ¬ IsProperlyPrimitive (((2 : ℤ_[2]) • G).map PadicInt.Coe.ringHom) := by
  rintro ⟨-, j, hj⟩
  have hu : IsUnit ((2 : ℤ_[2]) * G j j) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_def]
    simpa [Matrix.smul_apply] using hj
  have h2 : IsUnit (2 : ℤ_[2]) := isUnit_of_mul_isUnit_left hu
  rw [PadicInt.isUnit_iff] at h2
  have := PadicInt.norm_p (p := 2)
  norm_num at this
  rw [this] at h2
  norm_num at h2

theorem integral_coe {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ_[2]) : IsClassIntegral (G.map PadicInt.Coe.ringHom) :=
  fun i j => PadicInt.norm_le_one _

/-- **The perturbed second block is equivalent to $2B$ when $U'_W \sim U$** (over $\mathbb Z_2$): the block count's
$C'_W = C + CWU^{-1}W^{\mathsf T}C$, $C = 2B$, is congruent to $C$ by an invertible matrix. Proof: $T_W$ (`blockSol`
with identity diagonal blocks) is invertible and carries $U \perp C$ to $U'_W \perp C'_W \sim U \perp C'_W$; Cassels'
cancellation (`zpEquiv_cancel_dyMat`) removes $U$. -/
theorem zEq_pertC (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) (hBs : Bᵀ = B)
    {W : Matrix (Fin b) (Fin (dyDim L)) ℤ} (h : Good (intMat L) B W) :
    ZEq (((2 : ℤ) • B).map (Int.castRingHom ℤ_[2]))
      (pertC ((intMat L).map (Int.castRingHom ℤ_[2])) (((2 : ℤ) • B).map (Int.castRingHom ℤ_[2]))
        (W.map (Int.castRingHom ℤ_[2]))) := by
  set ι₂ := Int.castRingHom ℤ_[2]
  set U := intMat L with hUdef
  set Uz := U.map ι₂
  set Bz := B.map ι₂
  set Cz := ((2 : ℤ) • B).map ι₂
  set Wz := W.map ι₂
  have hUs : Uᵀ = U := (isSymm_intMat L).eq
  have hUd := det_odd_of_zero hv he
  have hUu : IsUnit Uz.det :=
    dyadic_unit_det_map U (Int.not_even_iff_odd.mp fun h => hUd (even_iff_two_dvd.mp h))
  have hUzs : Uzᵀ = Uz := by simp only [Uz, ← Matrix.transpose_map, hUs]
  have hCz : Cz = (2 : ℤ_[2]) • Bz := by
    ext i j; simp only [Cz, Bz, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
  have hBzs : Bzᵀ = Bz := by simp only [Bz, ← Matrix.transpose_map, hBs]
  have hCzs : Czᵀ = Cz := by rw [hCz, transpose_smul, hBzs]
  -- (a) `U'_W ∼ U` over `ℤ₂`
  have hU' : pertU Uz Cz Wz = (U + (2 : ℤ) • (Wᵀ * B * W)).map ι₂ := by
    have e1 : (Wᵀ * B * W).map ι₂ = Wzᵀ * Bz * Wz := by rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have e2 : ((2 : ℤ) • (Wᵀ * B * W)).map ι₂ = (2 : ℤ_[2]) • (Wᵀ * B * W).map ι₂ := by
      ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
    rw [pertU, Matrix.map_add _ (map_add ι₂), e2, e1, hCz, Matrix.mul_smul, Matrix.smul_mul]
  have hG₁ : ZEq Uz (pertU Uz Cz Wz) := by
    rw [hU']
    have := h
    unfold Good at this
    rw [← map_coe_int, ← map_coe_int] at this
    exact zpEquiv_coe_iff.mp this
  -- (b), (c) the matrix `T_W` is invertible
  set Pz := pertC Uz Cz Wz with hPz
  set T₀ := blockSol Uz Cz Wz 1 1 with hT₀
  have hT : T₀ᵀ * Matrix.fromBlocks Uz 0 0 Cz * T₀ = Matrix.fromBlocks (pertU Uz Cz Wz) 0 0 Pz := by
    rw [hT₀, blockSol_eqn hUzs hUu hCzs Wz 1 1]; simp [hPz]
  have hT₀u : IsUnit T₀ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    by_contra hn
    have hmem : T₀.det ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
      rw [PadicInt.ker_toZMod]; exact hn
    rw [RingHom.mem_ker, RingHom.map_det] at hmem
    have hC0 : Cz.map (PadicInt.toZMod (p := 2)) = 0 := by
      rw [hCz]; ext i j
      simp only [map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.zero_apply]
      have : (PadicInt.toZMod (p := 2)) 2 = 0 := by
        rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]; rfl
      rw [this, zero_mul]
    have hmap : (RingHom.mapMatrix (PadicInt.toZMod (p := 2))) T₀ =
        Matrix.fromBlocks 1 0 (Wz.map (PadicInt.toZMod (p := 2))) 1 := by
      rw [RingHom.mapMatrix_apply, hT₀, blockSol, Matrix.fromBlocks_map]
      congr 1
      · exact Matrix.map_one _ (map_zero _) (map_one _)
      · rw [Matrix.map_neg _ (map_neg _), Matrix.map_mul, Matrix.map_mul, hC0]; simp
      · rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      · exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [hmap, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one] at hmem
    exact one_ne_zero hmem
  -- (d) `U ⊥ C ∼ U ⊥ C'_W` over `ℤ₂`
  have hZ : ZEq (Matrix.fromBlocks Uz 0 0 Cz) (Matrix.fromBlocks Uz 0 0 Pz) :=
    ZEq.trans ⟨T₀, hT₀u, hT⟩ (ZEq.fromBlocks hG₁.symm (ZEq.refl Pz))
  -- (e) as `ZpEquiv` of orthogonal sums over `ℚ₂`
  have hZ' := hZ.submatrix (finSumFinEquiv.symm : Fin (dyDim L + b) ≃ Fin (dyDim L) ⊕ Fin b)
  rw [← zpEquiv_coe_iff] at hZ'
  have hsum : ∀ M : Matrix (Fin b) (Fin b) ℤ_[2],
      ((Matrix.fromBlocks Uz 0 0 M).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map PadicInt.Coe.ringHom =
        orthSumMat (dyMat L) (M.map PadicInt.Coe.ringHom) := fun M => by
    rw [dyadic_orthSumMat_eq, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      Matrix.map_zero _ (map_zero _)]
    congr 2
    rw [map_coe_int, intMat_map L fun c hc => (he c hc).ge]
  rw [hsum, hsum] at hZ'
  -- (f) cancel `U`
  have hPzs : Pzᵀ = Pz := by
    rw [hPz, pertC, transpose_add, hCzs]
    simp only [transpose_mul, hCzs, transpose_transpose, transpose_nonsing_inv, hUzs, Matrix.mul_assoc]
  have hPz2 : Pz = (2 : ℤ_[2]) • (Bz + (2 : ℤ_[2]) • (Bz * Wz * Uz⁻¹ * Wzᵀ * Bz)) := by
    rw [hPz, pertC, hCz]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  have hc := zpEquiv_cancel_dyMat L hv he (by rw [← Matrix.transpose_map, hCzs]) (by rw [← Matrix.transpose_map, hPzs])
    (integral_coe _) (integral_coe _) (by rw [hCz]; exact not_pp_two_smul _)
    (by rw [hPz2]; exact not_pp_two_smul _) hZ'
  exact zpEquiv_coe_iff.mp hc

/-- **The second factor when $U'_W \sim U$**: it is $N_r(2B)$. -/
theorem card_second_of_good {r : ℕ} [NeZero (2 ^ r)] (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0)
    (hBs : Bᵀ = B) (W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r))) (h : Good (intMat L) B (lift W)) :
    Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
      Zᵀ * pertC (red r (intMat L)) ((2 : ZMod (2 ^ r)) • red r B) W * Z = (2 : ZMod (2 ^ r)) • red r B} =
    Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
      Zᵀ * ((2 : ZMod (2 ^ r)) • red r B) * Z = (2 : ZMod (2 ^ r)) • red r B} := by
  obtain ⟨G, hG, hGe⟩ := (zEq_pertC hv he hBs h).map r
  have hUd := det_odd_of_zero hv he
  have hUu : IsUnit ((intMat L).map (Int.castRingHom ℤ_[2])).det :=
    dyadic_unit_det_map _ (Int.not_even_iff_odd.mp fun h => hUd (even_iff_two_dvd.mp h))
  have hC : (((2 : ℤ) • B).map (Int.castRingHom ℤ_[2])).map (PadicInt.toZModPow r) =
      (2 : ZMod (2 ^ r)) • red r B := by
    rw [map_red_int, red_smul]; norm_num
  have hP : (pertC ((intMat L).map (Int.castRingHom ℤ_[2])) (((2 : ℤ) • B).map (Int.castRingHom ℤ_[2]))
      ((lift W).map (Int.castRingHom ℤ_[2]))).map (PadicInt.toZModPow r) =
      pertC (red r (intMat L)) ((2 : ZMod (2 ^ r)) • red r B) W := by
    rw [pertC, pertC, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, map_nonsing_inv' _ _ hUu, hC, map_red_int, map_red_int, red_lift]
  rw [← hP, ← hC, ← hGe, card_congr_unit hG]

end Second

/-! ### The count, and the proportion $\rho$ -/

section Count

variable {L : List DyBlock} {B : Matrix (Fin b) (Fin b) ℤ}

/-- **The block count identity for arbitrary types** (Conway–Sloane 1988, (18), p. 281):
$N_r(U \perp 2B) = \#\{W \bmod 2^r : U + 2W^{\mathsf T}BW \sim U\}\cdot N_r(U)\cdot N_r(2B)$ for $r \ge 3$, $U$ a
block model of exponent $0$. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off the unimodular constituent, p = 2, any types)"]
theorem countN_blk_two_rho {r : ℕ} (hr : 3 ≤ r) (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0)
    (hBs : Bᵀ = B) :
    countN 2 r (blk 2 (intMat L) B) = Nat.card {W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r)) //
      Good (intMat L) B (lift W)} * countN 2 r (intMat L) * countN 2 r (((2 : ℕ) : ℤ) • B) := by
  classical
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  set U := intMat L
  have hUs : Uᵀ = U := (isSymm_intMat L).eq
  have hUd := det_odd_of_zero hv he
  have hsm : (((2 : ℕ) : ℤ) • B).map (Int.castRingHom (ZMod (2 ^ r))) = (2 : ZMod (2 ^ r)) • red r B := by
    rw [show (((2 : ℕ) : ℤ) • B).map (Int.castRingHom (ZMod (2 ^ r))) = red r (((2 : ℕ) : ℤ) • B) from rfl,
      red_smul]
    norm_num
  have hmap : (blk 2 U B).map (Int.castRingHom (ZMod (2 ^ r))) =
      (fromBlocks (red r U) 0 0 ((2 : ZMod (2 ^ r)) • red r B)).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
    rw [blk, ← Matrix.submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero _),
      Matrix.map_zero _ (map_zero _), hsm]
  have hUbs : (red r U)ᵀ = red r U := by rw [← red_transpose, hUs]
  have hCs : ((2 : ZMod (2 ^ r)) • red r B)ᵀ = (2 : ZMod (2 ^ r)) • red r B := by
    rw [transpose_smul, ← red_transpose, hBs]
  unfold countN
  rw [hmap, card_sol_submatrix, card_fromBlocks_eq_sum hUbs (isUnit_red_det hUd) hCs (two_nilpotent r) rfl, hsm]
  have hterm : ∀ W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r)),
      Nat.card {Y : Matrix (Fin (dyDim L)) (Fin (dyDim L)) (ZMod (2 ^ r)) //
        Yᵀ * pertU (red r U) ((2 : ZMod (2 ^ r)) • red r B) W * Y = red r U} *
      Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
        Zᵀ * pertC (red r U) ((2 : ZMod (2 ^ r)) • red r B) W * Z = (2 : ZMod (2 ^ r)) • red r B} =
      if Good U B (lift W) then countN 2 r U * Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
        Zᵀ * ((2 : ZMod (2 ^ r)) • red r B) * Z = (2 : ZMod (2 ^ r)) • red r B} else 0 := by
    intro W
    split_ifs with hg
    · rw [card_first_of_good W hg, card_second_of_good hv he hBs W hg]
    · rw [card_first_of_not_good hr hUs hUd hBs W hg, zero_mul]
  rw [Finset.sum_congr rfl fun W _ => hterm W, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  unfold countN
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

/-- For a surjective homomorphism of finite additive groups, the proportion of $g$ with $P(f(g))$ equals the
proportion of $h$ with $P(h)$. -/
theorem card_comp_div {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →+ H) (hf : Function.Surjective f) (P : H → Prop) [DecidablePred P] :
    ((Finset.univ.filter fun g => P (f g)).card : ℝ) / Fintype.card G =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card H := by
  classical
  set K := (Finset.univ.filter fun g : G => f g = 0).card
  have hfib : ∀ h : H, (Finset.univ.filter fun g : G => f g = h).card = K := by
    intro h
    obtain ⟨g₀, rfl⟩ := hf h
    refine Finset.card_bij (fun g _ => g - g₀) (fun g hg => ?_) (fun g _ g' _ hgg => ?_) (fun k hk => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢; rw [map_sub, hg, sub_self]
    · simpa using hgg
    · refine ⟨k + g₀, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; rw [map_add, hk, zero_add]
  have hP : (Finset.univ.filter fun g => P (f g)).card = (Finset.univ.filter P).card * K := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ.filter P) (fun g hg => by
      simpa using hg)]
    rw [Finset.sum_congr rfl fun h hh => ?_, Finset.sum_const, smul_eq_mul]
    rw [← hfib h]
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hg; rw [hg]; simpa using hh
  have hG : Fintype.card G = Fintype.card H * K := by
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
      (fun g _ => Finset.mem_univ _)
    rw [Finset.card_univ, Finset.sum_congr rfl fun h _ => ?_, Finset.sum_const, smul_eq_mul,
      Finset.card_univ] at this
    · exact this
    · simpa using hfib h
  have hK : (0 : ℝ) < K := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
    rw [hG] at this
    exact_mod_cast Nat.pos_of_mul_pos_left this
  rw [hP, hG]
  push_cast
  field_simp

end Count

/-! ### The proportion $\rho$ and the density -/

section Rho

/-- **The proportion $\rho(U, B)$**: $4^{-ab}\,\#\{W \in M_{b\times a}(\mathbb Z/4) : U + 2W^{\mathsf T}BW \sim U\}$
($\mathbb Z_2$-equivalence; $W$ read as an integer matrix with entries in $\{0, 1, 2, 3\}$). -/
noncomputable def rho (U : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) : ℝ :=
  (Nat.card {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)) // Good U B (lift W)} : ℝ) / 4 ^ (b * a)

variable {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}

theorem allDvd_lift_reduce {r : ℕ} (hr : 2 ≤ r) [NeZero (2 ^ r)] (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) :
    AllDvd 4 (lift (W.map (ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 2)))) - lift W) := by
  intro i j
  simp only [Matrix.sub_apply, lift, map_apply, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]
  have h := Nat.mod_add_div (W i j).val (2 ^ 2)
  refine ⟨-(((W i j).val / 2 ^ 2 : ℕ) : ℤ), ?_⟩
  have h' : (((W i j).val % 2 ^ 2 : ℕ) : ℤ) + 2 ^ 2 * (((W i j).val / 2 ^ 2 : ℕ) : ℤ) = ((W i j).val : ℤ) := by
    exact_mod_cast h
  linarith

theorem allDvd_neg {m k : Type*} {c : ℤ} {X : Matrix m k ℤ} (h : AllDvd c X) : AllDvd c (-X) :=
  fun i j => by simpa using (h i j).neg_right

theorem good_iff_reduce {r : ℕ} (hr : 2 ≤ r) [NeZero (2 ^ r)] (hUs : Uᵀ = U) (hU : ¬ 2 ∣ U.det) (hBs : Bᵀ = B)
    (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) :
    Good U B (lift (W.map (ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 2))))) ↔ Good U B (lift W) := by
  have h := allDvd_lift_reduce hr W
  refine ⟨fun hg => good_of_allDvd hUs hU hBs ?_ hg, fun hg => good_of_allDvd hUs hU hBs h hg⟩
  have := allDvd_neg h
  rwa [neg_sub] at this

theorem castHom_surj {r : ℕ} (hr : 2 ≤ r) :
    Function.Surjective ((ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 2))).toAddMonoidHom.mapMatrix :
      Matrix (Fin b) (Fin a) (ZMod (2 ^ r)) →+ Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) := by
  intro V
  have hs := ZMod.ringHom_surjective (ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 2)))
  refine ⟨Matrix.of fun i j => Classical.choose (hs (V i j)), ?_⟩
  ext i j
  exact Classical.choose_spec (hs (V i j))

/-- **$\rho$ from any level $r \ge 2$**: the proportion of good $W$ modulo $2^r$ is $\rho(U, B)$. -/
theorem card_good_div {r : ℕ} (hr : 2 ≤ r) [NeZero (2 ^ r)] (hUs : Uᵀ = U) (hU : ¬ 2 ∣ U.det) (hBs : Bᵀ = B) :
    (Nat.card {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r)) // Good U B (lift W)} : ℝ) / (2 ^ r) ^ (b * a) =
      rho U B := by
  classical
  have := card_comp_div _ (castHom_surj (a := a) (b := b) hr) (fun V => Good U B (lift V))
  simp only [AddMonoidHom.mapMatrix_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at this
  simp only [good_iff_reduce hr hUs hU hBs] at this
  unfold rho
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert this using 2
  · rw [Fintype.card_eq_nat_card, Matrix.card_matrix]
    simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]
  · rw [Fintype.card_eq_nat_card, Matrix.card_matrix]
    simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]

theorem good_zero : Good U B 0 := by
  unfold Good
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, smul_zero, add_zero]
  exact ZpEquiv.refl _

theorem rho_pos : 0 < rho U B := by
  unfold rho
  have : NeZero (2 ^ 2) := ⟨by norm_num⟩
  have hne : Nonempty {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)) // Good U B (lift W)} :=
    ⟨⟨0, by
      have : lift (0 : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) = 0 := by ext i j; simp [lift]
      rw [this]; exact good_zero⟩⟩
  have := Nat.card_pos (α := {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)) // Good U B (lift W)})
  positivity

theorem rho_le_one : rho U B ≤ 1 := by
  classical
  unfold rho
  rw [div_le_one (by positivity)]
  have h1 := Finite.card_subtype_le (fun W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)) => Good U B (lift W))
  have h2 : Nat.card (Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) = 4 ^ (b * a) := by
    rw [Matrix.card_matrix]; simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]
  rw [h2] at h1
  exact_mod_cast h1

variable {L : List DyBlock}

/-- **$\alpha_2(U \perp 2B) = \rho(U, B)\,\alpha_2(U)\,\alpha_2(2B)$** for every block model $U$ of exponent $0$
(Conway–Sloane 1988, §12, p. 281; the splitting step of (3) at $p = 2$, any types). -/
@[kb "conwaysloane1988" "§12, p. 281 (splitting off the unimodular constituent, p = 2, any types)"]
theorem alphaP_blk_two_rho (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) (hBs : B.IsSymm)
    (hB : B.det ≠ 0) :
    alphaP 2 (blk 2 (intMat L) B) = rho (intMat L) B * alphaP 2 (intMat L) * alphaP 2 (((2 : ℕ) : ℤ) • B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUs := isSymm_intMat L
  have hUd := det_odd_of_zero hv he
  have hU0 : (intMat L).det ≠ 0 := fun h => hUd (h ▸ dvd_zero _)
  have hblk0 : (blk 2 (intMat L) B).det ≠ 0 := by
    rw [blk_det]; exact mul_ne_zero hU0 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB)
  obtain ⟨r1, h1⟩ := alphaP_stabilizes Nat.prime_two (blk_isSymm (p := 2) hUs hBs) hblk0
  obtain ⟨r2, h2⟩ := alphaP_stabilizes Nat.prime_two hUs hU0
  obtain ⟨r3, h3⟩ := alphaP_stabilizes Nat.prime_two (smul_isSymm (p := 2) hBs) (smul_det_ne (p := 2) hB)
  set r := max (max r1 r2) (max r3 3)
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  have hr3 : 3 ≤ r := le_trans (le_max_right _ _) (le_max_right _ _)
  rw [← h1 r (le_trans (le_max_left _ _) (le_max_left _ _)), ← h2 r (le_trans (le_max_right _ _) (le_max_left _ _)),
    ← h3 r (le_trans (le_max_left _ _) (le_max_right _ _)), countN_blk_two_rho hr3 hv he hBs.eq, tri_add,
    ← card_good_div (by omega : 2 ≤ r) hUs.eq hUd hBs.eq]
  push_cast
  rw [mul_add, mul_add, pow_add, pow_add, ← pow_mul, mul_comm (r : ℕ) (b * dyDim L)]
  push_cast
  field_simp

/-- **The 2-mass of $U \perp 2B$ for any types**: $m_2(U \perp 2B) = m_2(U)\,m_2(B)\,2^{as/2}/\rho(U, B)$,
$s = b + \operatorname{ord}_2\det B$. -/
@[kb "conwaysloane1988" "(3), p. 263 (one step of the induction over the constituents, p = 2, any types)"]
theorem pMassDensity_blk_two_rho (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) (hBs : B.IsSymm)
    (hB : B.det ≠ 0) :
    pMassDensity 2 (blk 2 (intMat L) B) = pMassDensity 2 (intMat L) * pMassDensity 2 B *
      (2 : ℝ) ^ ((((b + padicValInt 2 B.det : ℕ) : ℝ) * dyDim L) / 2) / rho (intMat L) B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUs := isSymm_intMat L
  have hUd := det_odd_of_zero hv he
  have hU0 : (intMat L).det ≠ 0 := fun h => hUd (h ▸ dvd_zero _)
  have hvU : padicValInt 2 (intMat L).det = 0 := padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hUd)
  have hval : padicValInt 2 (blk 2 (intMat L) B).det = b + padicValInt 2 B.det := by
    rw [blk_det, padicValInt.mul hU0 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB), hvU,
      zero_add, padicValInt.mul (pow_ne_zero _ (by norm_num)) hB]
    congr 1
    unfold padicValInt
    simp
  have hαB := alphaP_smul_prime Nat.prime_two hBs hB
  have hαU := (alphaP_pos Nat.prime_two hUs hU0).ne'
  have hαB0 := (alphaP_pos Nat.prime_two hBs hB).ne'
  have hρ := (rho_pos (U := intMat L) (B := B)).ne'
  unfold pMassDensity
  rw [alphaP_blk_two_rho hv he hBs hB, hαB, hval, hvU, ← Real.rpow_natCast ((2 : ℕ) : ℝ) (b * (b + 1) / 2),
    cast_half]
  simp only [Nat.cast_zero, zero_mul, zero_div, Real.rpow_zero]
  set s : ℝ := ((b + padicValInt 2 B.det : ℕ) : ℝ)
  have hs : s = (b : ℝ) + (padicValInt 2 B.det : ℝ) := by simp [s]
  have e : ((2 : ℕ) : ℝ) ^ (s * (((dyDim L + b : ℕ) : ℝ) + 1) / 2) = ((2 : ℕ) : ℝ) ^ ((b : ℝ) * ((b : ℝ) + 1) / 2) *
      ((2 : ℕ) : ℝ) ^ ((padicValInt 2 B.det : ℝ) * ((b : ℝ) + 1) / 2) * ((2 : ℕ) : ℝ) ^ (s * (dyDim L : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    rw [hs]; push_cast; ring
  rw [e]
  have : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ ((b : ℝ) * ((b : ℝ) + 1) / 2) := by positivity
  push_cast at this ⊢
  field_simp

end Rho

end QuadFormsKB.ConwaySloane.Mass.Two
