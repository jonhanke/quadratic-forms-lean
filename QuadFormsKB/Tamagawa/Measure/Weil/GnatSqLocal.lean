/-
# Square discriminant, locally:
$\{(\alpha,\beta) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}/K^\times \cong SO(D,\operatorname{nrd})(K)$


**Layer:** a field $K$ with $2\ne0$, $D = (A,B)_K$; then a number field $F$ and its completions. This is the local half of
the square-discriminant adelic isomorphism: the map $G^\natural\to SO(V_0)$ (`Quat.Gnat.phiSO`) for $d = 1$, $t = 1$, read
through `pairEquiv` as $(\alpha,\beta)\mapsto(x\mapsto\alpha x\beta^{-1})$ on $D$ with the norm form
$\langle1,-A,-B,AB\rangle$ = `V0Form A B 1`.

**Defines/proves**
* `qVec`, `vecQ`: coordinates $1,i,j,k$; `sqPair A B` = $\{(\alpha,\beta)\in(D^\times)^2 : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}$;
* `sqLift : sqPair A B →* Gnat A B 1` (the inverse of `pairEquiv`), `sqSO := phiSO ∘ sqLift`;
  **`sqSO_mulVec`**: $\mathrm{sqSO}(\alpha,\beta)\,v = \alpha\,v\,\beta^{-1}$ in coordinates; **`sqSO_surjective`**;
  **`sqSO_eq_one_iff`** (kernel = the diagonal scalars $K^\times$);
* `sqMat`, `continuous_sqMat_comp`: the matrix entries are polynomials in the coordinates of $\alpha$ and $\beta^{-1}$;
* for a ring homomorphism $\rho : F\to K$ and the integral model `qSq a b` over $\mathcal O_F$: the hessian form
  (`sqSO_hessian`, `exists_sqSO_eq`) used by `orthGroup`/`soReal`/`soC`;
* at a finite place $v$ with $|2|_v = |a|_v = |b|_v = 1$: **`exists_smul_mem_lamLocUnits_sq`** (if $x\mapsto\alpha x\beta^{-1}$
  stabilizes $\Lambda_v$ then $(c\alpha, c\beta)\in(\Lambda_v^\times)^2$ for some $c\in F_v^\times$; via $\alpha\beta^{-1}\in\Lambda_v^\times$ and
  the trace-identity lemma `exists_smul_mem_lamLocUnits` for conjugation by $\alpha$), and the converse
  `sqMat_mulVec_mem_std`.

Source: Weil 1982, §3.7, p. 65 [unverified page] ($SO_4\cong(D^\times\times D^\times)'/G_m$ for square discriminant);
Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*, §15 [unverified] ($D_2 = A_1\times A_1$).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSO4
import QuadFormsKB.Tamagawa.Measure.Weil.PDGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatTamagawa

open Matrix Quaternion NumberField IsDedekindDomain WithZero Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices

/-! ### Coordinates -/

section Generic

variable {K : Type*} [Field K] {A B : K}

/-- The coordinates $(x_0,x_1,x_2,x_3)$ of $x = x_0 + x_1 i + x_2 j + x_3 k$. -/
def qVec (x : ℍ[K,A,B]) : Fin 4 → K := ![x.re, x.imI, x.imJ, x.imK]

/-- The quaternion with coordinates $v$. -/
def vecQ (v : Fin 4 → K) : ℍ[K,A,B] := ⟨v 0, v 1, v 2, v 3⟩

@[simp] theorem qVec_vecQ (v : Fin 4 → K) : qVec (vecQ v : ℍ[K,A,B]) = v := by
  funext i; fin_cases i <;> rfl

@[simp] theorem vecQ_qVec (x : ℍ[K,A,B]) : vecQ (qVec x) = x := QuaternionAlgebra.ext rfl rfl rfl rfl

theorem one_sq_eq_one : (1 : K) ^ 2 = 1 := one_pow 2

/-- With $d = t = 1$, `ev_1 ∘ emb` is the identity on coordinates. -/
theorem evQ_one_emb (v : Fin 4 → K) :
    evQ (a := A) (b := B) (1 : K) one_sq_eq_one (emb v : DE A B 1) = vecQ v := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [emb, vecQ, evE_apply]

/-! ### The group $\{(\alpha,\beta) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}$ and the lift to $G^\natural$ -/

variable (A B) in
/-- $\{(\alpha,\beta)\in(D^\times)^2 : \operatorname{nrd}\alpha = \operatorname{nrd}\beta\}$. -/
def sqPair : Subgroup ((ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ) where
  carrier := {p | nrd (p.1 : ℍ[K,A,B]) = nrd (p.2 : ℍ[K,A,B])}
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, Units.val_mul, nrd_mul] at hp hq ⊢
    rw [hp, hq]
  one_mem' := rfl
  inv_mem' {p} hp := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv] at hp ⊢
    have h1 := nrd_mul (p.1 : ℍ[K,A,B]) ((p.1⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
    have h2 := nrd_mul (p.2 : ℍ[K,A,B]) ((p.2⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
    rw [Units.mul_inv, nrd_one] at h1 h2
    rw [hp] at h1
    exact mul_left_cancel₀ (nrd_units_ne_zero p.2) (h1.symm.trans h2)

theorem mem_sqPair {p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ} :
    p ∈ sqPair A B ↔ nrd (p.1 : ℍ[K,A,B]) = nrd (p.2 : ℍ[K,A,B]) := Iff.rfl

variable (h2 : (2 : K) ≠ 0)

/-- `D_E ≅ D × D` for $d = t = 1$. -/
abbrev pairE : DE A B 1 ≃+* ℍ[K,A,B] × ℍ[K,A,B] := pairEquiv h2 one_sq_eq_one one_ne_zero

theorem pairE_apply (x : DE A B 1) :
    pairE h2 x = (evQ 1 one_sq_eq_one x, evQ (-1) (neg_sq_eq one_sq_eq_one) x) := rfl

/-- The unit of $D_E$ with components $(\alpha,\beta)$, as a homomorphism. -/
def pairUnit : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ →* (DE A B 1)ˣ :=
  (Units.map (pairE (A := A) (B := B) h2).symm.toRingHom.toMonoidHom).comp
    (MulEquiv.prodUnits (M := ℍ[K,A,B]) (N := ℍ[K,A,B])).symm.toMonoidHom

theorem pairE_pairUnit (p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ) :
    pairE h2 ((pairUnit h2 p : (DE A B 1)ˣ) : DE A B 1) = ((p.1 : ℍ[K,A,B]), (p.2 : ℍ[K,A,B])) := by
  change pairE h2 ((pairE h2).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem evQ_pairUnit (p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ) :
    evQ 1 one_sq_eq_one ((pairUnit h2 p : (DE A B 1)ˣ) : DE A B 1) = p.1 :=
  congrArg Prod.fst (pairE_pairUnit h2 p)

theorem evQ_neg_pairUnit (p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ) :
    evQ (-1) (neg_sq_eq one_sq_eq_one) ((pairUnit h2 p : (DE A B 1)ˣ) : DE A B 1) = p.2 :=
  congrArg Prod.snd (pairE_pairUnit h2 p)

theorem pairUnit_mem (p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ) (hp : p ∈ sqPair A B) : pairUnit h2 p ∈ Gnat A B 1 := by
  rw [mem_Gnat_iff_nrd_eq h2 one_sq_eq_one one_ne_zero, evQ_pairUnit, evQ_neg_pairUnit]
  exact hp

/-- **The lift** $(\alpha,\beta)\mapsto\alpha\in G^\natural(K)$ ($d = 1$). -/
def sqLift : sqPair A B →* Gnat A B 1 :=
  ((pairUnit (A := A) (B := B) h2).comp (sqPair A B).subtype).codRestrict _ fun p => by
    rw [MonoidHom.comp_apply]; exact pairUnit_mem h2 _ p.2

theorem coe_sqLift (p : sqPair A B) :
    ((sqLift h2 p : Gnat A B 1) : (DE A B 1)ˣ) = pairUnit h2 p := rfl

theorem sqLift_surjective : Function.Surjective (sqLift (A := A) (B := B) h2) := by
  intro α
  set x := ((α : (DE A B 1)ˣ) : DE A B 1)
  set y := (((α : (DE A B 1)ˣ)⁻¹ : (DE A B 1)ˣ) : DE A B 1)
  have hxy : x * y = 1 := Units.mul_inv _
  have hyx : y * x = 1 := Units.inv_mul _
  let p₁ : (ℍ[K,A,B])ˣ := ⟨(pairE h2 x).1, (pairE h2 y).1, by rw [← Prod.fst_mul, ← map_mul, hxy, map_one]; rfl,
    by rw [← Prod.fst_mul, ← map_mul, hyx, map_one]; rfl⟩
  let p₂ : (ℍ[K,A,B])ˣ := ⟨(pairE h2 x).2, (pairE h2 y).2, by rw [← Prod.snd_mul, ← map_mul, hxy, map_one]; rfl,
    by rw [← Prod.snd_mul, ← map_mul, hyx, map_one]; rfl⟩
  have hmem : (p₁, p₂) ∈ sqPair A B := by
    have := (mem_Gnat_iff_nrd_eq h2 one_sq_eq_one one_ne_zero (α : (DE A B 1)ˣ)).1 α.2
    exact this
  refine ⟨⟨(p₁, p₂), hmem⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_sqLift]
  apply (pairE (A := A) (B := B) h2).injective
  rw [pairE_pairUnit]

include h2 in
/-- $\varphi_\alpha$ in coordinates for $\alpha\in G^\natural$ with components $(p_1, p_2)$: $v\mapsto p_1vp_2^{-1}$. -/
theorem phiLin_pair_eq (α : (DE A B 1)ˣ) (hα : α ∈ Gnat A B 1) (p₁ p₂ : (ℍ[K,A,B])ˣ)
    (e1 : evQ 1 one_sq_eq_one (α : DE A B 1) = p₁) (e2 : evQ (-1) (neg_sq_eq one_sq_eq_one) (α : DE A B 1) = p₂)
    (v : Fin 4 → K) : phiLin (α : DE A B 1) v = qVec ((p₁ : ℍ[K,A,B]) * vecQ v * ((p₂⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])) := by
  have h := evQ_phiLin h2 one_sq_eq_one hα v
  rw [evQ_one_emb, evQ_one_emb, e1] at h
  have e2' : Units.map (evQ (-1) (neg_sq_eq one_sq_eq_one)).toMonoidHom α = p₂ := Units.ext e2
  rw [e2'] at h
  exact (qVec_vecQ _).symm.trans (congrArg qVec h)

/-! ### The map to $SO(\langle1,-A,-B,AB\rangle)$ -/

variable (hA : A ≠ 0)

/-- **$(\alpha,\beta)\mapsto(x\mapsto\alpha x\beta^{-1})$** into $SO(\langle1,-A,-B,AB\rangle)(K)$ = `SO (V0Form A B 1)`. -/
def sqSO : sqPair A B →* SO (V0Form A B 1) :=
  (phiSO h2 hA one_ne_zero).comp (sqLift h2)

/-- **In coordinates, `sqSO (α, β)` is $x\mapsto\alpha x\beta^{-1}$.** -/
theorem sqSO_mulVec (p : sqPair A B) (v : Fin 4 → K) :
    ((sqSO h2 hA p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v =
      qVec (((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).1 : ℍ[K,A,B]) * vecQ v *
        (((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).2⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])) := by
  change LinearMap.toMatrix' (phiLin (((sqLift h2 p : Gnat A B 1) : (DE A B 1)ˣ) : DE A B 1)) *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]
  exact phiLin_pair_eq h2 _ (sqLift h2 p).2 _ _ (evQ_pairUnit h2 _) (evQ_neg_pairUnit h2 _) v

/-- **`sqSO` is surjective** ($A, B\ne0$). -/
theorem sqSO_surjective (hB : B ≠ 0) : Function.Surjective (sqSO (A := A) (B := B) h2 hA) :=
  (phiSO_surjective h2 hA hB one_ne_zero).comp (sqLift_surjective h2)

/-- **The kernel of `sqSO` is the diagonal $K^\times$**: $(\alpha,\beta)\mapsto1$ iff $\alpha = \beta = r\in K^\times$. -/
theorem sqSO_eq_one_iff (p : sqPair A B) :
    sqSO h2 hA p = 1 ↔ ∃ r : K, ((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).1 : ℍ[K,A,B]) = (r : ℍ[K,A,B]) ∧
      ((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).2 : ℍ[K,A,B]) = (r : ℍ[K,A,B]) := by
  change sqLift h2 p ∈ (phiSO h2 hA one_ne_zero).ker ↔ _
  rw [ker_phiSO]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_, ?_⟩
    · have := congrArg (evQ (a := A) (b := B) 1 one_sq_eq_one) hr
      rw [coe_sqLift, evQ_pairUnit] at this
      rw [this]
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [evE_apply]
    · have := congrArg (evQ (a := A) (b := B) (-1) (neg_sq_eq one_sq_eq_one)) hr
      rw [coe_sqLift, evQ_neg_pairUnit] at this
      rw [this]
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [evE_apply]
  · rintro ⟨r, h1, h2'⟩
    refine ⟨r, ?_⟩
    rw [coe_sqLift]
    apply (pairE (A := A) (B := B) h2).injective
    rw [pairE_pairUnit, h1, h2', pairE_apply]
    refine Prod.ext ?_ ?_ <;> refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp [evE_apply]

/-! ### The matrix of $x\mapsto\alpha x\beta$ and continuity -/

/-- The matrix of $x\mapsto x_1xy_1$ in the basis $1,i,j,k$: column $j$ is the coordinate vector of $x_1e_jy_1$. -/
def sqMat (x y : ℍ[K,A,B]) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => qVec (x * vecQ (Pi.single j 1) * y) i

theorem sqSO_val (p : sqPair A B) :
    ((sqSO h2 hA p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      sqMat ((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).1 : ℍ[K,A,B])
        (((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).2⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) := by
  ext i j
  have := congrFun (sqSO_mulVec h2 hA p (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem sqSO_inv_val (p : sqPair A B) :
    (((sqSO h2 hA p)⁻¹ : SO (V0Form A B 1)) : GL (Fin 4) K).val =
      sqMat (((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).1⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
        ((p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).2 : ℍ[K,A,B]) := by
  rw [← map_inv, sqSO_val, Subgroup.coe_inv, Prod.snd_inv, inv_inv]
  rfl

/-- **Continuity of $x\mapsto x_1 x y_1$** in the coordinates of $x_1$ and $y_1$. -/
theorem continuous_sqMat_comp [TopologicalSpace K] [IsTopologicalRing K] {X : Type*} [TopologicalSpace X]
    (f g : X → ℍ[K,A,B]) (h0 : Continuous fun t => (f t).re) (h1 : Continuous fun t => (f t).imI)
    (h2' : Continuous fun t => (f t).imJ) (h3 : Continuous fun t => (f t).imK)
    (g0 : Continuous fun t => (g t).re) (g1 : Continuous fun t => (g t).imI)
    (g2 : Continuous fun t => (g t).imJ) (g3 : Continuous fun t => (g t).imK) :
    Continuous fun t => sqMat (f t) (g t) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
  simp [sqMat, qVec, vecQ, Pi.single_apply, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> fun_prop

set_option maxHeartbeats 2000000 in
/-- **The matrix of $x\mapsto x_1xy_1$ commutes with base change** (coordinatewise images under $f : K\to L$). -/
theorem sqMat_map {K L : Type*} [Field K] [Field L] (f : K →+* L) {A B : K} (x y : ℍ[K,A,B])
    (x' y' : ℍ[L, f A, f B]) (h0 : x'.re = f x.re) (h1 : x'.imI = f x.imI) (h2 : x'.imJ = f x.imJ)
    (h3 : x'.imK = f x.imK) (g0 : y'.re = f y.re) (g1 : y'.imI = f y.imI) (g2 : y'.imJ = f y.imJ)
    (g3 : y'.imK = f y.imK) : sqMat x' y' = (sqMat x y).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sqMat, qVec, vecQ, Pi.single_apply, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, h0, h1, h2, h3, g0, g1, g2, g3]

end Generic

/-! ### Over a number field: the integral model `qSq a b` -/

section Model

variable {F : Type} [Field F] [NumberField F]

theorem two_ne_zero_of_ringHom {K : Type*} [Field K] (ρ : F →+* K) : (2 : K) ≠ 0 := two_ne_zero_ringHom ρ

/-- $q_{\mathrm{sq}}(a,b)\otimes_\rho K = \langle1,-\rho a,-\rho b,\rho a\,\rho b\rangle$ = `V0Form (ρ a) (ρ b) 1`. -/
theorem qSq_map_ringHom {K : Type*} [Field K] (ρ : F →+* K) (a b : 𝓞 F) :
    ((qSq a b).map (algebraMap (𝓞 F) F)).map ρ = V0Form (ρ (a : F)) (ρ (b : F)) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qSq, V0Form, QuadForm.diag, QuadForm.map]

theorem hessian_qSq_map_ringHom {K : Type*} [Field K] (ρ : F →+* K) (a b : 𝓞 F) :
    ((qSq a b).map (algebraMap (𝓞 F) F)).hessian.map ρ = (V0Form (ρ (a : F)) (ρ (b : F)) 1).hessian := by
  rw [← qSq_map_ringHom ρ a b, QuadFormsKB.Siegel.hessian_map_NF ρ (QuadForm.map (algebraMap (𝓞 F) F) (qSq a b))]

/-- The hessian form of membership: `sqSO` preserves the hessian of $q_{\mathrm{sq}}^\rho$ and has determinant $1$. -/
theorem sqSO_hessian {K : Type*} [Field K] (ρ : F →+* K) (a b : 𝓞 F) (ha : (a : F) ≠ 0)
    (p : sqPair (ρ (a : F)) (ρ (b : F))) :
    ((sqSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
        ((qSq a b).map (algebraMap (𝓞 F) F)).hessian.map ρ *
        ((sqSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) p : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((qSq a b).map (algebraMap (𝓞 F) F)).hessian.map ρ ∧
      ((sqSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) p : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [hessian_qSq_map_ringHom]
  have := (mem_SO_iff_hessian (two_ne_zero_of_ringHom ρ)).1 (sqSO (two_ne_zero_of_ringHom ρ)
    ((map_ne_zero ρ).2 ha) p).2
  exact ⟨this.2, this.1⟩

/-- Conversely, an element preserving the hessian of $q_{\mathrm{sq}}^\rho$ with determinant $1$ is some
$x\mapsto\alpha x\beta^{-1}$. -/
theorem exists_sqSO_eq {K : Type*} [Field K] (ρ : F →+* K) (a b : 𝓞 F) (ha : (a : F) ≠ 0) (hb : (b : F) ≠ 0)
    (g : GL (Fin 4) K)
    (hg : (g : Matrix (Fin 4) (Fin 4) K)ᵀ * ((qSq a b).map (algebraMap (𝓞 F) F)).hessian.map ρ * g =
      ((qSq a b).map (algebraMap (𝓞 F) F)).hessian.map ρ)
    (hdet : (g : Matrix (Fin 4) (Fin 4) K).det = 1) :
    ∃ p : sqPair (ρ (a : F)) (ρ (b : F)),
      (sqSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) p : GL (Fin 4) K) = g := by
  rw [hessian_qSq_map_ringHom] at hg
  have hmem : g ∈ SO (V0Form (ρ (a : F)) (ρ (b : F)) 1) :=
    (mem_SO_iff_hessian (two_ne_zero_of_ringHom ρ)).2 ⟨hdet, hg⟩
  obtain ⟨p, hp⟩ := sqSO_surjective (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) ((map_ne_zero ρ).2 hb)
    ⟨g, hmem⟩
  exact ⟨p, congrArg Subtype.val hp⟩

/-- The kernel in the hessian form: `sqSO p = 1` iff $\alpha = \beta$ is a scalar. -/
theorem sqSO_val_eq_one_iff {K : Type*} [Field K] (ρ : F →+* K) (a : 𝓞 F) (b : F) (ha : (a : F) ≠ 0)
    (p : sqPair (ρ (a : F)) (ρ b)) :
    (sqSO (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) p : GL (Fin 4) K) = 1 ↔
      ∃ r : K, ((p : (ℍ[K, ρ (a : F), ρ b])ˣ × (ℍ[K, ρ (a : F), ρ b])ˣ).1 : ℍ[K, ρ (a : F), ρ b]) =
          (r : ℍ[K, ρ (a : F), ρ b]) ∧
        ((p : (ℍ[K, ρ (a : F), ρ b])ˣ × (ℍ[K, ρ (a : F), ρ b])ˣ).2 : ℍ[K, ρ (a : F), ρ b]) =
          (r : ℍ[K, ρ (a : F), ρ b]) := by
  rw [← sqSO_eq_one_iff (two_ne_zero_of_ringHom ρ) ((map_ne_zero ρ).2 ha) p]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

/-! #### $F$-algebras: `orthGroup` and `soSub` -/

variable (K : Type*) [Field K] [Algebra F K] (a b : 𝓞 F)

local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

/-- The units of $D\otimes_FK$. -/
abbrev HK : Type _ := (ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)])ˣ

variable {a b} in
/-- **$(\alpha,\beta)\mapsto(x\mapsto\alpha x\beta^{-1})$ into `soSub QF K`** for an $F$-algebra field $K$. -/
def sqSOK (ha : (a : F) ≠ 0) :
    sqPair (algebraMap F K (a : F)) (algebraMap F K (b : F)) →* soSub QF K where
  toFun p := ⟨⟨(sqSO (two_ne_zero_of_ringHom (algebraMap F K)) ((map_ne_zero _).2 ha) p : GL (Fin 4) K),
    (sqSO_hessian (algebraMap F K) a b ha p).1⟩, (sqSO_hessian (algebraMap F K) a b ha p).2⟩
  map_one' := by ext : 3; simp
  map_mul' p q := by ext : 3; simp

variable {K a b}

@[simp] theorem sqSOK_coe (ha : (a : F) ≠ 0) (p : sqPair (algebraMap F K (a : F)) (algebraMap F K (b : F))) :
    (((sqSOK K ha p : soSub QF K) : orthGroup QF K) : GL (Fin 4) K) =
      (sqSO (two_ne_zero_of_ringHom (algebraMap F K)) ((map_ne_zero _).2 ha) p : GL (Fin 4) K) := by
  simp only [sqSOK, MonoidHom.coe_mk, OneHom.coe_mk]

theorem sqSOK_surjective (ha : (a : F) ≠ 0) (hb : (b : F) ≠ 0) : Function.Surjective (sqSOK K (b := b) ha) := by
  intro g
  obtain ⟨p, hp⟩ := exists_sqSO_eq (algebraMap F K) a b ha hb ((g : orthGroup QF K) : GL (Fin 4) K)
    ((mem_orthGroup QF).1 (g : orthGroup QF K).2) (mem_soSub.1 g.2)
  exact ⟨p, by ext : 3; rw [sqSOK_coe, hp]⟩

theorem sqSOK_eq_one_iff (ha : (a : F) ≠ 0) (p : sqPair (algebraMap F K (a : F)) (algebraMap F K (b : F))) :
    sqSOK K ha p = 1 ↔ ∃ r : K, ((p : HK K a b × HK K a b).1 : ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)]) =
      (r : ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)]) ∧
        ((p : HK K a b × HK K a b).2 : ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)]) =
          (r : ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)]) := by
  rw [← sqSO_val_eq_one_iff (algebraMap F K) a (b : F) ha p]
  constructor
  · intro h
    have h' := congrArg (fun g : soSub QF K => ((g : orthGroup QF K) : GL (Fin 4) K)) h
    simp only [sqSOK_coe, OneMemClass.coe_one] at h'
    exact h'
  · intro h; ext : 3; rw [sqSOK_coe, h]; simp

theorem sqSOK_mulVec (ha : (a : F) ≠ 0) (p : sqPair (algebraMap F K (a : F)) (algebraMap F K (b : F)))
    (v : Fin 4 → K) :
    omat (sqSOK K ha p : orthGroup QF K) *ᵥ v =
      qVec (((p : HK K a b × HK K a b).1 : ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)]) * vecQ v *
        ((((p : HK K a b × HK K a b).2)⁻¹ : HK K a b) : ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)])) :=
  by rw [omat, sqSOK_coe]; exact sqSO_mulVec _ ((map_ne_zero _).2 ha) p v

end Model

/-! ### Finite places: integral lifts -/

section Place

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

theorem mem_std_iff4 (y : Fin 4 → Fv) : y ∈ std v ↔ ∀ i, y i ∈ (𝔬).toSubring := by
  refine forall_congr' fun i => ?_
  rw [neg_zero, exp_zero, mem_O_iff]

theorem qInt_vecQ_iff {A B : Fv} (y : Fin 4 → Fv) : QInt (𝔬).toSubring (vecQ y : ℍ[Fv,A,B]) ↔ y ∈ std v := by
  rw [mem_std_iff4]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i
    exacts [h0, h1, h2, h3]
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩

theorem qVec_mem_std_iff {A B : Fv} (x : ℍ[Fv,A,B]) : qVec x ∈ std v ↔ QInt (𝔬).toSubring x := by
  rw [← qInt_vecQ_iff, vecQ_qVec]

theorem mulVec_mem_std_of_mem_stdStab {n : ℕ} {Q : QuadForm F n} {g : orthGroup Q Fv} (hg : g ∈ stdStab Q v)
    {y : Fin n → Fv} (hy : y ∈ std v) : omat g *ᵥ y ∈ std v := by
  have hmem : omat g *ᵥ y ∈ locAct v (g : GL (Fin n) Fv) (std v) := ⟨y, hy, rfl⟩
  rwa [show locAct v (g : GL (Fin n) Fv) (std v) = std v from hg] at hmem

variable (ha : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (w.adicCompletion F) (a : F)) ≤ 1)
  (hb : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (w.adicCompletion F) (b : F)) ≤ 1)
  (ha0 : (a : F) ≠ 0)

include ha hb in
/-- **$(\Lambda_v^\times)^2$ acts integrally**: for $\alpha,\beta\in\Lambda_v^\times$ with equal norms, $x\mapsto\alpha x\beta^{-1}$
lies in $O(\mathfrak o_v^4)$. -/
theorem sqSOK_mem_stdStab (p : sqPair (algebraMap F Fv (a : F)) (algebraMap F Fv (b : F)))
    (h1 : (p : HK Fv a b × HK Fv a b).1 ∈ lamLocUnits (a : F) (b : F) v)
    (h2 : (p : HK Fv a b × HK Fv a b).2 ∈ lamLocUnits (a : F) (b : F) v) :
    (sqSOK Fv ha0 p : orthGroup QF Fv) ∈ stdStab QF v := by
  have hA : algebraMap F Fv (a : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 (ha v)
  have hB : algebraMap F Fv (b : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 (hb v)
  refine mem_stdStab_of_mulVec v _ (fun y hy => ?_) (fun y hy => ?_)
  · rw [sqSOK_mulVec, qVec_mem_std_iff]
    exact ((qInt_of_mem_lamLoc v h1.1).mul hA hB ((qInt_vecQ_iff v y).2 hy)).mul hA hB
      (qInt_of_mem_lamLoc v h2.2)
  · rw [show ((sqSOK Fv ha0 p : orthGroup QF Fv))⁻¹ = (sqSOK Fv ha0 p⁻¹ : orthGroup QF Fv) by
      rw [map_inv]; rfl, sqSOK_mulVec, qVec_mem_std_iff]
    simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv, inv_inv]
    exact ((qInt_of_mem_lamLoc v h1.2).mul hA hB ((qInt_vecQ_iff v y).2 hy)).mul hA hB
      (qInt_of_mem_lamLoc v h2.1)

include ha hb in
/-- **Integral lifts at good places.** Let $|2|_v = |a|_v = |b|_v = 1$. If $x\mapsto\alpha x\beta^{-1}$ ($\operatorname{nrd}\alpha
= \operatorname{nrd}\beta$) stabilizes $\mathfrak o_v^4$, then $(c\alpha, c\beta)\in(\Lambda_v^\times)^2$ for some $c\in F_v^\times$.

*Proof.* $u = \alpha\beta^{-1}$ is the image of $1$, so $u\in\Lambda_v$, and $\operatorname{nrd}u = 1$, so $u\in\Lambda_v^\times$. Conjugation
by $\alpha$ is $y\mapsto(\alpha y\beta^{-1})u^{-1}$, hence integral on $\mathfrak o_v^3$; the trace-identity lemma
`exists_smul_mem_lamLocUnits` gives $c\alpha\in\Lambda_v^\times$, and $c\beta = u^{-1}(c\alpha)$. -/
theorem exists_smul_mem_lamLocUnits_sq (h2v : Valued.v (2 : Fv) = 1)
    (hav : Valued.v (algebraMap F Fv (a : F)) = 1) (hbv : Valued.v (algebraMap F Fv (b : F)) = 1)
    (p : sqPair (algebraMap F Fv (a : F)) (algebraMap F Fv (b : F)))
    (hp : (sqSOK Fv ha0 p : orthGroup QF Fv) ∈ stdStab QF v) :
    ∃ r : Fvˣ, Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r *
        (p : HK Fv a b × HK Fv a b).1 ∈ lamLocUnits (a : F) (b : F) v ∧
      Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r *
        (p : HK Fv a b × HK Fv a b).2 ∈ lamLocUnits (a : F) (b : F) v := by
  have hA : algebraMap F Fv (a : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 (ha v)
  have hB : algebraMap F Fv (b : F) ∈ (𝔬).toSubring := (mem_O_iff v _).2 (hb v)
  set α : HK Fv a b := (p : HK Fv a b × HK Fv a b).1 with hα
  set β : HK Fv a b := (p : HK Fv a b × HK Fv a b).2 with hβ
  -- the image of `y` is integral for integral `y`
  have himg : ∀ y : Fin 4 → Fv, y ∈ std v → QInt (𝔬).toSubring
      ((α : QuatV (a : F) (b : F) v) * vecQ y * ((β⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v)) := by
    intro y hy
    have := mulVec_mem_std_of_mem_stdStab v hp hy
    rwa [sqSOK_mulVec, qVec_mem_std_iff] at this
  set u : HK Fv a b := α * β⁻¹ with hu
  have he0 : (Pi.single 0 1 : Fin 4 → Fv) ∈ std v := by
    rw [mem_std_iff4]; intro i
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  have hvec0 : (vecQ (Pi.single 0 1 : Fin 4 → Fv) : QuatV (a : F) (b : F) v) = 1 :=
    QuaternionAlgebra.ext (by simp [vecQ]) (by simp [vecQ]) (by simp [vecQ]) (by simp [vecQ])
  have hulam : (u : QuatV (a : F) (b : F) v) ∈ lamLoc (a : F) (b : F) v := by
    have := himg _ he0
    rw [hvec0, mul_one] at this
    exact this
  have hnrdu : nrd (u : QuatV (a : F) (b : F) v) = 1 := by
    have hn := mem_sqPair.1 p.2
    have h1 := nrd_mul (β : QuatV (a : F) (b : F) v) ((β⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v)
    rw [Units.mul_inv, nrd_one] at h1
    rw [hu, Units.val_mul, nrd_mul]
    change nrd (α : QuatV (a : F) (b : F) v) * _ = 1
    rw [show nrd (α : QuatV (a : F) (b : F) v) = nrd (β : QuatV (a : F) (b : F) v) from hn]
    exact h1.symm
  have huU : u ∈ lamLocUnits (a : F) (b : F) v := by
    rw [mem_lamLocUnits_iff ha hb]
    refine ⟨hulam, ?_⟩
    rw [nrdLoc_eq_nrd, hnrdu, map_one]
  -- conjugation by α is integral
  have hint : ∀ i j, Valued.v (((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) i j) ≤ 1 := by
    intro i j
    have hcol : ((conjGL α : GL (Fin 3) Fv) : Matrix (Fin 3) (Fin 3) Fv) i j =
        conjLin α (Pi.single j 1) i := by
      rw [← conjGL_mulVec, Matrix.mulVec_single_one]; rfl
    rw [hcol, conjLin_apply]
    have hy : (Fin.cons 0 (Pi.single j 1) : Fin 4 → Fv) ∈ std v := by
      rw [mem_std_iff4]; intro k
      refine Fin.cases ?_ (fun l => ?_) k
      · simp
      · by_cases h : l = j
        · subst h; simp
        · simp [h]
    have hpure : (Quat.pure (Pi.single j 1) : QuatV (a : F) (b : F) v) = vecQ (Fin.cons 0 (Pi.single j 1)) :=
      QuaternionAlgebra.ext rfl rfl rfl rfl
    have hfac : (α : QuatV (a : F) (b : F) v) * Quat.pure (Pi.single j 1) *
        ((α⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v) =
        ((α : QuatV (a : F) (b : F) v) * vecQ (Fin.cons 0 (Pi.single j 1)) *
          ((β⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v)) * ((u⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v) := by
      rw [hpure, hu, _root_.mul_inv_rev, inv_inv, Units.val_mul, mul_assoc _ ((β⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v),
        ← mul_assoc ((β⁻¹ : HK Fv a b) : QuatV (a : F) (b : F) v), ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mul]
    rw [hfac]
    have hq := (himg _ hy).mul hA hB (qInt_of_mem_lamLoc v huU.2)
    rw [← mem_O_iff]
    fin_cases i
    · exact hq.2.1
    · exact hq.2.2.1
    · exact hq.2.2.2
  obtain ⟨r, hr⟩ := exists_smul_mem_lamLocUnits v ha hb h2v hav hbv α hint
  refine ⟨r, hr, ?_⟩
  have hβ' : Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r * β =
      u⁻¹ * (Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r * α) := by
    set R := Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r
    have hcomm : ∀ x : HK Fv a b, R * x = x * R := fun x => Units.ext (Algebra.commutes (r : Fv) (x : QuatV (a : F) (b : F) v))
    rw [hcomm β, hcomm α, hu, _root_.mul_inv_rev, inv_inv]
    group
  rw [hβ']
  exact lamLocUnits_mul_mem ha hb ⟨huU.2, by rw [inv_inv]; exact huU.1⟩ hr

end Place

end QuadFormsKB.Tamagawa.Measure.Weil
