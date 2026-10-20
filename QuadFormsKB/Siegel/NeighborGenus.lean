/-
# Kneser neighbours, part 4: neighbours are in the genus

**Layer:** lattices in $\mathbb{Q}^n$ with the form of an integral $Q$ (`Siegel/Neighbors.lean`), and integral forms
(`QuadForm ℤ n`) via a basis.

**Defines** the lattice spanned by the columns of $g \in M_n(\mathbb{Q})$ (`imgLat`); the Gram form of a lattice in a basis
is the integral form $Q'(\vec{c}) = Q(g\vec{c})$.

**Proves**, for $p$ an odd prime with $p \nmid \det H$ and a $p$-neighbour $L'$ of $\mathbb{Z}^n$:
- `exists_basis`: $L' = g\,\mathbb{Z}^n$ for some $g \in \mathrm{GL}_n(\mathbb{Q})$ (via Mathlib's bases of submodules over a PID), with
  $|\det g| = 1$ (`abs_det_eq_one`, by comparing $[L' : p\mathbb{Z}^n] = [\mathbb{Z}^n : p\mathbb{Z}^n]$ through $L' \cap \mathbb{Z}^n$);
- `exists_gramForm`: the Gram form $Q'$ with $Q'(\vec{x}) = Q(g\vec{x})$ is integral, with Hessian $g^{\mathsf T}Hg$;
- `sameGenus_of_basis` (AWS notes, Thm. 1.10.3(1), p. 23): **$Q'$ is in the genus of $Q$**. At $\infty$ and at $\ell \ne p$ the
  matrix $g$ itself works ($pg$ and $pg^{-1}$ are integral, and $p \in \mathbb{Z}_\ell^\times$); at $p$ both forms are unimodular with
  the same determinant, so they are $\mathbb{Z}_p$-equivalent (`isometricGL_of_unimodular`);
- `latRep_eq_repNum`: $r_{L'}(m) = r_{Q'}(m)$.
-/
import QuadFormsKB.Siegel.EichlerCommutation
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Siegel.GenusFinite

open Matrix Module

namespace QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-- **The lattice spanned by the columns of $g$:** $g\mathbb{Z}^n = \{g\vec{c} : \vec{c} \in \mathbb{Z}^n\} \subset \mathbb{Q}^n$. -/
def imgLat (g : Matrix (Fin n) (Fin n) ℚ) : Submodule ℤ (Fin n → ℚ) where
  carrier := {x | ∃ c : Fin n → ℤ, x = g *ᵥ cv c}
  add_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, by rw [cv_add, mulVec_add]⟩
  zero_mem' := ⟨0, by simp [cv_zero]⟩
  smul_mem' := by
    rintro k _ ⟨c, rfl⟩
    refine ⟨k • c, ?_⟩
    rw [cv_smul, mulVec_smul, ← Int.cast_smul_eq_zsmul ℚ]

theorem mem_imgLat {g : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → ℚ} :
    x ∈ imgLat g ↔ ∃ c : Fin n → ℤ, x = g *ᵥ cv c := Iff.rfl

theorem mulVec_cv_eq_sum (g : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℤ) :
    g *ᵥ cv c = ∑ j, c j • g.col j := by
  ext i
  simp only [mulVec, dotProduct, cv_apply, Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section Basis

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The lattice $\frac1p\mathbb{Z}^n$.** -/
def scaledLat (n p : ℕ) : Submodule ℤ (Fin n → ℚ) where
  carrier := {x | ∃ y : Fin n → ℤ, x = (1 / (p : ℚ)) • cv y}
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, by rw [cv_add, smul_add]⟩
  zero_mem' := ⟨0, by simp [cv_zero]⟩
  smul_mem' := by
    rintro k _ ⟨y, rfl⟩
    refine ⟨k • y, ?_⟩
    rw [cv_smul, smul_comm, ← Int.cast_smul_eq_zsmul ℚ]

/-- $\frac1p\mathbb{Z}^n \cong \mathbb{Z}^n$. -/
noncomputable def scaledEquiv : (Fin n → ℤ) ≃ₗ[ℤ] scaledLat n p where
  toFun y := ⟨(1 / (p : ℚ)) • cv y, y, rfl⟩
  map_add' y z := by ext1; simp [cv_add, smul_add]
  map_smul' k y := by
    ext1
    simp only [RingHom.id_apply, SetLike.val_smul, cv_smul]
    rw [smul_comm, ← Int.cast_smul_eq_zsmul ℚ]
  invFun x := intPart ((p : ℚ) • (x : Fin n → ℚ))
  left_inv y := by
    have := p_ne_zero (p := p)
    simp only
    rw [smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul, intPart_cv]
  right_inv x := by
    obtain ⟨x, y, rfl⟩ := x
    have := p_ne_zero (p := p)
    ext1
    simp only
    rw [smul_smul, show (p : ℚ) * (1 / p) = 1 by field_simp, one_smul, intPart_cv]

/-- **Lattices between $p\mathbb{Z}^n$ and $\frac1p\mathbb{Z}^n$ have a basis:** $L = g\mathbb{Z}^n$ with $\det g \ne 0$. -/
theorem exists_basis_of_le {L : Submodule ℤ (Fin n → ℚ)} (hL : L ≤ scaledLat n p)
    (hpL : ∀ y : Fin n → ℤ, cv ((p : ℤ) • y) ∈ L) :
    ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det ≠ 0 ∧ L = imgLat g := by
  have hp0 := p_ne_zero (p := p)
  let bO : Basis (Fin n) ℤ (scaledLat n p) := (Pi.basisFun ℤ (Fin n)).map scaledEquiv
  obtain ⟨k, bL⟩ := Submodule.basisOfPidOfLE hL bO
  haveI : Module.Finite ℤ (scaledLat n p) := Module.Finite.of_basis bO
  haveI : Module.Finite ℤ L := Module.Finite.of_basis bL
  have hk1 : k ≤ n := by
    have hli : LinearIndependent ℤ ((Submodule.inclusion hL) ∘ bL) :=
      bL.linearIndependent.map' _ (Submodule.ker_inclusion _ _ hL)
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, finrank_eq_card_basis bO, Fintype.card_fin] at this
  have hk2 : n ≤ k := by
    let v : Fin n → L := fun i => ⟨cv ((p : ℤ) • Pi.single i 1), hpL _⟩
    have hli : LinearIndependent ℤ v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have := congrArg (fun x : L => (x : Fin n → ℚ) i) hc
      simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, cv_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Submodule.coe_zero, Pi.zero_apply] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at this
      simp only [if_true, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast] at this
      have hpq : ((p : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      have : (c i : ℚ) * p = 0 := by simpa using this
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hp0
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin, finrank_eq_card_basis bL, Fintype.card_fin] at this
  have hk : k = n := le_antisymm hk1 hk2
  subst hk
  let g : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun i j => ((bL j : L) : Fin k → ℚ) i
  have hcol : ∀ j, g.col j = ((bL j : L) : Fin k → ℚ) := fun j => by ext i; rfl
  have hLg : L = imgLat g := by
    ext x
    constructor
    · intro hx
      refine ⟨fun j => bL.repr ⟨x, hx⟩ j, ?_⟩
      rw [mulVec_cv_eq_sum]
      have := congrArg (fun y : L => (y : Fin k → ℚ)) (bL.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      conv_lhs => rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hcol]
    · rintro ⟨c, rfl⟩
      rw [mulVec_cv_eq_sum]
      exact L.sum_mem fun j _ => L.smul_of_tower_mem _ (by rw [hcol]; exact (bL j).2)
  refine ⟨g, ?_, hLg⟩
  -- g C = p • 1 for an integer matrix C
  have hC : ∀ i, ∃ c : Fin k → ℤ, cv ((p : ℤ) • Pi.single i 1) = g *ᵥ cv c := fun i => by
    have := hpL (Pi.single i 1); rw [hLg] at this; exact this
  choose C hC using hC
  let Cm : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun r i => (C i r : ℚ)
  have hgC : g * Cm = (p : ℚ) • (1 : Matrix (Fin k) (Fin k) ℚ) := by
    ext r i
    have h1 := congrFun (hC i) r
    have h2 : (g * Cm) r i = (g *ᵥ cv (C i)) r := by
      simp only [mul_apply, mulVec, dotProduct, Cm, of_apply, cv_apply]
    rw [h2, ← h1]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  intro h0
  have := congrArg Matrix.det hgC
  rw [det_mul, h0, zero_mul, det_smul, det_one, mul_one, Fintype.card_fin] at this
  exact pow_ne_zero _ hp0 this.symm

end Basis

/-! ### General facts on forms and matrices -/

section Forms

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]

theorem evalIn_smul_gen (Q : QuadForm R n) (x : Fin n → K) (t : K) :
    Q.evalIn K (t • x) = t ^ 2 * Q.evalIn K x := by
  rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem eval_smul_gen (Q : QuadForm K n) (x : Fin n → K) (t : K) :
    Q.eval (t • x) = t ^ 2 * Q.eval x := evalIn_smul_gen Q x t

/-- $2Q(\vec{x}) = \vec{x}^{\mathsf T}H\vec{x}$ over any $R$-algebra. -/
theorem two_mul_evalIn (Q : QuadForm R n) (x : Fin n → K) :
    2 * Q.evalIn K x = x ⬝ᵥ (Q.hessian.map (algebraMap R K) *ᵥ x) := by
  have h := QuadForm.polar_eq_hessian K Q x x
  have h2 : x + x = (2 : K) • x := (two_smul K x).symm
  rw [h2, evalIn_smul_gen] at h
  linear_combination h

theorem hessian_map {S : Type*} [CommRing S] (f : R →+* S) (Q : QuadForm R n) :
    (Q.map f).hessian = Q.hessian.map f := by
  ext i j; simp [QuadForm.hessian, QuadForm.map, Matrix.map_apply]

theorem entry_eq_dotProduct {T : Type*} [CommRing T] (M : Matrix (Fin n) (Fin n) T) (i j : Fin n) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [Matrix.col_apply]

theorem conj_apply_col {T : Type*} [CommRing T] (g H : Matrix (Fin n) (Fin n) T) (i j : Fin n) :
    (gᵀ * H * g) i j = g.col i ⬝ᵥ (H *ᵥ g.col j) := by
  simp only [mul_apply, transpose_apply, mulVec, dotProduct, Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem dotProduct_conj {T : Type*} [CommRing T] (g H : Matrix (Fin n) (Fin n) T) (x y : Fin n → T) :
    x ⬝ᵥ ((gᵀ * H * g) *ᵥ y) = (g *ᵥ x) ⬝ᵥ (H *ᵥ (g *ᵥ y)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x gᵀ, vecMul_transpose]

end Forms

section Gram

variable {Q : QuadForm ℤ n}

/-- **The Hessian of $Q \circ g$:** if $Q'(\vec{x}) = Q(g\vec{x})$ on $\mathbb{Q}^n$, then $H' = g^{\mathsf T}Hg$. -/
theorem hessian_eq_conj {Q' : QuadForm ℤ n} {g : Matrix (Fin n) (Fin n) ℚ}
    (h : ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) :
    Q'.hessian.map (algebraMap ℤ ℚ) = gᵀ * Q.hessian.map (algebraMap ℤ ℚ) * g := by
  ext i j
  have h1 := QuadForm.polar_eq_hessian ℚ Q' (Pi.single i 1) (Pi.single j 1)
  have h2 := QuadForm.polar_eq_hessian ℚ Q (g *ᵥ Pi.single i 1) (g *ᵥ Pi.single j 1)
  rw [h, h, h, mulVec_add, entry_eq_dotProduct] at h1
  rw [← h1, h2, ← dotProduct_conj, entry_eq_dotProduct]

/-- **The Gram form in a basis** (integral when $Q$ is $\mathbb{Z}$-valued on $g\mathbb{Z}^n$): there is an integral $Q'$ with
$Q'(\vec{x}) = Q(g\vec{x})$ for all $\vec{x} \in \mathbb{Q}^n$. -/
theorem exists_gramForm {g : Matrix (Fin n) (Fin n) ℚ}
    (hint : ∀ c : Fin n → ℤ, ∃ z : ℤ, Q.evalIn ℚ (g *ᵥ cv c) = z) :
    ∃ Q' : QuadForm ℤ n, ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x) := by
  set Hq := Q.hessian.map (algebraMap ℤ ℚ)
  have hcol : ∀ i, g.col i = g *ᵥ cv (Pi.single i 1) := by
    intro i; ext r; simp [mulVec, dotProduct, Pi.single_apply, Matrix.col_apply]
  have hN : ∀ i j, ∃ z : ℤ, (gᵀ * Hq * g) i j = z := by
    intro i j
    rw [conj_apply_col]
    have hp := evalIn_add_smulQ Q (g.col i) (g.col j) 1
    rw [one_smul, one_mul, one_pow, one_mul] at hp
    obtain ⟨a, ha⟩ := hint (Pi.single i 1 + Pi.single j 1)
    obtain ⟨b, hb⟩ := hint (Pi.single i 1)
    obtain ⟨c, hc⟩ := hint (Pi.single j 1)
    rw [cv_add, mulVec_add, ← hcol, ← hcol] at ha
    rw [← hcol] at hb
    rw [← hcol] at hc
    refine ⟨a - b - c, ?_⟩
    have : bQ Q (g.col i) (g.col j) = a - b - c := by rw [ha, hb, hc] at hp; push_cast; linarith
    push_cast; rw [← this]; rfl
  choose z hz using hN
  let N' : Matrix (Fin n) (Fin n) ℤ := Matrix.of z
  have hNN : N'.map (algebraMap ℤ ℚ) = gᵀ * Hq * g := by ext i j; simp [N', hz]
  have hsym : N'.IsSymm := by
    ext i j
    have hHs : Hqᵀ = Hq := by rw [← Matrix.transpose_map, LocalDensity.hessian_isSymm Q]
    have : (gᵀ * Hq * g)ᵀ = gᵀ * Hq * g := by
      simp only [transpose_mul, transpose_transpose, hHs, Matrix.mul_assoc]
    have h2 := congrFun (congrFun this i) j
    rw [transpose_apply, hz, hz] at h2
    simp only [transpose_apply, N', of_apply]
    exact_mod_cast h2
  have hev : ∀ i, Even (N' i i) := by
    intro i
    obtain ⟨b, hb⟩ := hint (Pi.single i 1)
    have h1 := two_mul_evalIn (K := ℚ) Q (g.col i)
    rw [hcol, hb] at h1
    have h3 : (gᵀ * Hq * g) i i = 2 * b := by
      rw [conj_apply_col, hcol, ← h1]
    refine ⟨b, ?_⟩
    have : (z i i : ℚ) = b + b := by rw [← hz, h3]; ring
    simp only [N', of_apply]; exact_mod_cast this
  obtain ⟨Q', hQ'⟩ := exists_hessian_eq N' hsym hev
  refine ⟨Q', fun x => ?_⟩
  have h1 := two_mul_evalIn (K := ℚ) Q' x
  have h2 := two_mul_evalIn (K := ℚ) Q (g *ᵥ x)
  rw [hQ', hNN, dotProduct_conj] at h1
  linarith

end Gram

/-! ### Neighbour bases: integrality, $|\det g| = 1$, genus -/

section NbGenus

variable {Q : QuadForm ℤ n} {p : ℕ} [hp : Fact p.Prime]

theorem imgLat_toAddSubgroup (g : Matrix (Fin n) (Fin n) ℚ) :
    (imgLat g).toAddSubgroup = AddSubgroup.closure (Set.range g.col) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [mulVec_cv_eq_sum]
    exact AddSubgroup.sum_mem _ fun j _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) _
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    ext r; simp [mulVec, dotProduct, Pi.single_apply, Matrix.col_apply]

theorem stdLat_eq_imgLat_one : stdLat n = imgLat 1 := by
  ext x; simp [mem_stdLat, mem_imgLat]

/-- **A neighbour basis has $|\det g| = 1$** ($L' = g\mathbb{Z}^n$ a $p$-neighbour containing $p\mathbb{Z}^n$): both
$[L' : p\mathbb{Z}^n]$ and $[\mathbb{Z}^n : p\mathbb{Z}^n]$ equal $p \cdot [L' \cap \mathbb{Z}^n : p\mathbb{Z}^n]$, while they are
$p^n/|\det g|$ and $p^n$ (`AddSubgroup.relIndex_eq_abs_det`). -/
theorem abs_det_eq_one {g : Matrix (Fin n) (Fin n) ℚ} (hg : g.det ≠ 0) (hL : IsNeighbor Q p (imgLat g))
    (hpL : ∀ y : Fin n → ℤ, cv ((p : ℤ) • y) ∈ imgLat g) : |g.det| = 1 := by
  classical
  have hp0 := p_ne_zero (p := p)
  set e := Pi.basisFun ℚ (Fin n)
  set bp := e.isUnitSMul (w := fun _ => (p : ℚ)) (fun _ => isUnit_iff_ne_zero.mpr hp0)
  have hbp : ∀ i, bp i = cv ((p : ℤ) • Pi.single i 1) := by
    intro i; ext r
    simp [bp, e, Basis.isUnitSMul_apply, Pi.single_apply, cv_apply]
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range g.col) := by
    intro x _
    have : x = g *ᵥ (g⁻¹ *ᵥ x) := by
      rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), one_mulVec]
    rw [this]
    have e2 : g *ᵥ (g⁻¹ *ᵥ x) = ∑ j, (g⁻¹ *ᵥ x) j • g.col j := by
      ext i; simp [mulVec, dotProduct, Finset.sum_apply, Matrix.col_apply, mul_comm]
    rw [e2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  set bg := Basis.mk (linearIndependent_cols_of_det_ne_zero hg) hspan
  have hbg : ∀ j, bg j = g.col j := fun j => by simp [bg]
  set S := (stdLat n).toAddSubgroup
  set LA := (imgLat g).toAddSubgroup
  set pS := AddSubgroup.closure (Set.range bp)
  have hpSL : pS ≤ LA := by
    rw [AddSubgroup.closure_le]; rintro _ ⟨i, rfl⟩; rw [hbp]; exact hpL _
  have hpSS : pS ≤ S := by
    rw [AddSubgroup.closure_le]; rintro _ ⟨i, rfl⟩; rw [hbp]
    show cv _ ∈ stdLat n; exact ⟨_, rfl⟩
  have hS : S = AddSubgroup.closure (Set.range e) := by
    have : (fun i => e i) = (1 : Matrix (Fin n) (Fin n) ℚ).col := by
      ext i r; simp [e, Pi.single_apply, Matrix.one_apply, Matrix.col_apply, eq_comm]
    simp only [S, stdLat_eq_imgLat_one, imgLat_toAddSubgroup]
    congr 1; rw [← this]
  have hLg : LA = AddSubgroup.closure (Set.range bg) := by
    simp only [LA, imgLat_toAddSubgroup]; congr 1; ext x; simp [hbg]
  have i1 := AddSubgroup.relIndex_eq_abs_det pS S hpSS bp e rfl hS
  have i2 := AddSubgroup.relIndex_eq_abs_det pS LA hpSL bp bg rfl hLg
  -- the two indices agree
  have heq : pS.relIndex S = pS.relIndex LA := by
    have h1 := AddSubgroup.relIndex_mul_relIndex pS (LA ⊓ S) S (le_inf hpSL hpSS) inf_le_right
    have h2 := AddSubgroup.relIndex_mul_relIndex pS (S ⊓ LA) LA (le_inf hpSS hpSL) inf_le_right
    rw [AddSubgroup.inf_relIndex_right, hL.relIndex_std] at h1
    rw [AddSubgroup.inf_relIndex_right, hL.relIndex_self, inf_comm] at h2
    rw [← h1, ← h2]
  have hdet_e : e.det bp = (p : ℚ) ^ n := by
    rw [Basis.det_apply]
    have : e.toMatrix bp = (p : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
      ext i j
      rw [Basis.toMatrix_apply, hbp]
      simp [e, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [this, det_smul, det_one, mul_one, Fintype.card_fin]
  have hmul : g.det * bg.det bp = (p : ℚ) ^ n := by
    have := congrArg Matrix.det (Basis.toMatrix_mul_toMatrix e bg bp)
    rw [det_mul, ← Basis.det_apply, ← Basis.det_apply, ← Basis.det_apply, hdet_e] at this
    have he : e.det bg = g.det := by
      rw [Basis.det_apply]; congr 1
      ext i j; rw [Basis.toMatrix_apply, hbg]; simp [e, Matrix.col_apply]
    rw [he] at this
    exact this
  have habs : |bg.det bp| = (p : ℚ) ^ n := by
    rw [← i2, ← heq, i1, hdet_e, abs_pow, abs_of_pos (by positivity)]
  have := congrArg abs hmul
  rw [abs_mul, habs, abs_pow, abs_of_pos (show (0 : ℚ) < p by positivity)] at this
  have hpn : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ hp0
  exact mul_right_cancel₀ hpn (this.trans (one_mul _).symm)

theorem eval_smul_form {R : Type*} [CommRing R] (c : R) (Q' : QuadForm R n) (x : Fin n → R) :
    (c • Q').eval x = c * Q'.eval x := by
  simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem map_smul_form {K : Type*} [CommRing K] (f : ℤ →+* K) (c : ℤ) (Q' : QuadForm ℤ n) :
    (c • Q').map f = f c • Q'.map f := by
  ext i j
  simp only [QuadForm.map, QuadForm.smul_coeff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem det_map_eq {K : Type*} [CommRing K] (f : ℤ →+* K) (M : Matrix (Fin n) (Fin n) ℤ) :
    (M.map f).det = f M.det := (RingHom.map_det f M).symm

/-- **Equivalence after inverting $p$:** if $D, D' \in M_n(\mathbb{Z})$ with $DD' = D'D = p^2$ and $Q(D\vec{c}) = p^2Q'(\vec{c})$, then
$Q \cong Q'$ over every ring $K$ in which $p$ is a unit (via $p^{-1}D$). -/
theorem isometricGL_of_scaled {K : Type*} [CommRing K] (f : ℤ →+* K) {Q Q' : QuadForm ℤ n} (c : ℤ)
    (u : Kˣ) (hu : (u : K) = f c) {D D' : Matrix (Fin n) (Fin n) ℤ}
    (hDD : ∀ i j, (D * D') i j = if i = j then c ^ 2 else 0)
    (hD'D : ∀ i j, (D' * D) i j = if i = j then c ^ 2 else 0)
    (hQD : ∀ x, Q.eval (D *ᵥ x) = (c ^ 2 • Q').eval x) :
    IsometricGL (Q.map f) (Q'.map f) := by
  set M := ((u⁻¹ : Kˣ) : K) • D.map f
  set M' := ((u⁻¹ : Kˣ) : K) • D'.map f
  have hinv : ((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) * (f c ^ 2) = 1 := by
    rw [← hu]; simp [← mul_assoc, sq]
  have key : ∀ A B : Matrix (Fin n) (Fin n) ℤ, (∀ i j, (A * B) i j = if i = j then c ^ 2 else 0) →
      (((u⁻¹ : Kˣ) : K) • A.map f) * (((u⁻¹ : Kˣ) : K) • B.map f) = 1 := by
    intro A B hAB
    ext i j
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_apply, ← Matrix.map_mul, Matrix.map_apply,
      hAB, Matrix.one_apply]
    split_ifs
    · rw [map_pow, smul_eq_mul, hinv]
    · rw [map_zero, smul_zero]
  refine ⟨⟨M, M', key D D' hDD, key D' D hD'D⟩, fun x => ?_⟩
  show (Q.map f).eval (M *ᵥ x) = _
  simp only [M]
  rw [Matrix.smul_mulVec, eval_smul_gen, eval_mulVec_map f hQD x, map_smul_form, eval_smul_form, map_pow,
    ← mul_assoc, sq ((u⁻¹ : Kˣ) : K), hinv, one_mul]

theorem toZMod_intCast {ℓ : ℕ} [Fact ℓ.Prime] (z : ℤ) : PadicInt.toZMod (z : ℤ_[ℓ]) = (z : ZMod ℓ) :=
  map_intCast _ z

/-- **Neighbours are in the genus** (AWS notes, Thm. 1.10.3(1), p. 23): for $p$ an odd prime, $p \nmid \det H$,
$g\mathbb{Z}^n$ a $p$-neighbour of $\mathbb{Z}^n$ ($\det g \ne 0$), and $Q'$ the Gram form, $Q'(\vec{x}) = Q(g\vec{x})$, the form $Q'$ is in the
genus of $Q$. -/
@[kb "hanke2011aws" "Thm. 1.10.3(1), p. 23"]
theorem sameGenus_of_neighbor (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    {g : Matrix (Fin n) (Fin n) ℚ} (hg : g.det ≠ 0) (hL : IsNeighbor Q p (imgLat g)) {Q' : QuadForm ℤ n}
    (hQ' : ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) : SameGenus Q Q' := by
  classical
  have hp0 := p_ne_zero (p := p)
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨v, hv, hv0, hLv⟩ := exists_eq_nbLat hdet hL
  have hpL : ∀ y : Fin n → ℤ, cv ((p : ℤ) • y) ∈ imgLat g := by
    intro y; rw [hLv, cv_mem_nbLat_iff hv, bZ_smul_left]; exact dvd_mul_right _ _
  have habs := abs_det_eq_one hg hL hpL
  have hgU : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  have hcol : ∀ c : Fin n → ℤ, g *ᵥ cv c ∈ imgLat g := fun c => ⟨c, rfl⟩
  -- p g and p g⁻¹ are integral
  have hgp : ∀ i j, ∃ z : ℤ, (p : ℚ) * g i j = z := by
    intro i j
    have h := hcol (Pi.single j 1)
    rw [hLv] at h
    obtain ⟨y, hy⟩ := exists_eq_of_mem_nbLat h
    refine ⟨y i, ?_⟩
    have := congrFun hy i
    simp only [mulVec, dotProduct, cv_apply, Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply,
      smul_eq_mul] at this
    rw [this]; field_simp
  have hgp' : ∀ i j, ∃ z : ℤ, (p : ℚ) * g⁻¹ i j = z := by
    intro i j
    obtain ⟨c, hc⟩ := hpL (Pi.single j 1)
    refine ⟨c i, ?_⟩
    have := congrArg (fun w => g⁻¹ *ᵥ w) hc
    simp only [mulVec_mulVec, nonsing_inv_mul _ hgU, one_mulVec] at this
    have := congrFun this i
    simp only [mulVec, dotProduct, cv_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Int.cast_ite, Int.cast_mul, Int.cast_natCast, Int.cast_one, Int.cast_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]; ring
  have hH := hessian_eq_conj hQ'
  have hdetH : Q'.hessian.det = Q.hessian.det := by
    have h1 := congrArg Matrix.det hH
    rw [det_mul, det_mul, det_transpose, det_map_eq, det_map_eq] at h1
    have hsq : g.det * g.det = 1 := by
      have := congrArg (· ^ 2) habs; simp only [sq_abs, one_pow] at this; rw [← sq]; exact this
    rw [show g.det * algebraMap ℤ ℚ Q.hessian.det * g.det = algebraMap ℤ ℚ Q.hessian.det by
      rw [mul_comm, ← mul_assoc, mul_comm _ g.det, hsq, one_mul]] at h1
    exact_mod_cast h1
  choose z hz using hgp
  choose z' hz' using hgp'
  set D : Matrix (Fin n) (Fin n) ℤ := Matrix.of z
  set D' : Matrix (Fin n) (Fin n) ℤ := Matrix.of z'
  have hDq : D.map (algebraMap ℤ ℚ) = (p : ℚ) • g := by ext i j; simp [D, ← hz]
  have hD'q : D'.map (algebraMap ℤ ℚ) = (p : ℚ) • g⁻¹ := by ext i j; simp [D', ← hz']
  have hinj : ∀ A B : Matrix (Fin n) (Fin n) ℤ, A.map (algebraMap ℤ ℚ) = B.map (algebraMap ℤ ℚ) → A = B := by
    intro A B h; ext i j; have := congrFun (congrFun h i) j; simpa using this
  have hDD : ∀ i j, (D * D') i j = if i = j then (p : ℤ) ^ 2 else 0 := by
    intro i j
    have h := congrFun (congrFun (show (D * D').map (algebraMap ℤ ℚ) = ((p : ℚ) * p) • (1 : Matrix _ _ ℚ) by
      rw [Matrix.map_mul, hDq, hD'q, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_nonsing_inv _ hgU]) i) j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] at h
    split_ifs at h ⊢
    · have h' : (((D * D') i j : ℤ) : ℚ) = ((p : ℤ) ^ 2 : ℤ) := by simpa [sq] using h
      exact_mod_cast h'
    · have h' : (((D * D') i j : ℤ) : ℚ) = 0 := by simpa using h
      exact_mod_cast h'
  have hD'D : ∀ i j, (D' * D) i j = if i = j then (p : ℤ) ^ 2 else 0 := by
    intro i j
    have h := congrFun (congrFun (show (D' * D).map (algebraMap ℤ ℚ) = ((p : ℚ) * p) • (1 : Matrix _ _ ℚ) by
      rw [Matrix.map_mul, hDq, hD'q, Matrix.smul_mul, Matrix.mul_smul, smul_smul, nonsing_inv_mul _ hgU,
        mul_comm]) i) j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply] at h
    split_ifs at h ⊢
    · have h' : (((D' * D) i j : ℤ) : ℚ) = ((p : ℤ) ^ 2 : ℤ) := by simpa [sq] using h
      exact_mod_cast h'
    · have h' : (((D' * D) i j : ℤ) : ℚ) = 0 := by simpa using h
      exact_mod_cast h'
  have hQD : ∀ x, Q.eval (D *ᵥ x) = (((p : ℤ) ^ 2) • Q').eval x := by
    intro x
    rw [eval_smul_form]
    have e1 : cv (D *ᵥ x) = (p : ℚ) • (g *ᵥ cv x) := by
      ext i
      simp only [cv_apply, mulVec, dotProduct, D, of_apply, Int.cast_sum, Int.cast_mul, Pi.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hz]; ring
    have := evalIn_cv Q (D *ᵥ x)
    rw [e1, evalIn_smulQ, ← hQ', evalIn_cv] at this
    exact_mod_cast this.symm
  refine ⟨fun ℓ _ => ?_, ?_⟩
  · by_cases hℓ : ℓ = p
    · subst hℓ
      apply isometricGL_of_unimodular hp2
      · rw [hessian_map, det_map_eq]
        rintro ⟨c, hc⟩
        apply hdet
        rw [← dvd_of_red, ← toZMod_intCast]
        change PadicInt.toZMod ((Int.castRingHom ℤ_[ℓ]) Q.hessian.det) = 0
        rw [hc, map_mul, toZMod_natCast_self, zero_mul]
      · rw [hessian_map, hessian_map, det_map_eq, det_map_eq, hdetH]
    · have hu : IsUnit ((p : ℤ) : ℤ_[ℓ]) := by
        apply isUnit_of_toZMod_ne_zero
        rw [toZMod_intCast]
        intro h
        rw [dvd_of_red] at h
        have : ℓ ∣ p := by exact_mod_cast h
        exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp.out).mp this)
      exact isometricGL_of_scaled (Int.castRingHom ℤ_[ℓ]) (p : ℤ) hu.unit (by simp) hDD hD'D hQD
  · -- the real place
    let f := Rat.castHom ℝ
    let gU : GL (Fin n) ℚ := Matrix.nonsingInvUnit g hgU
    refine ⟨Units.map f.mapMatrix.toMonoidHom gU, fun x => ?_⟩
    have egU : ((Units.map f.mapMatrix.toMonoidHom gU : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) = g.map f :=
      rfl
    rw [egU, eval_map_real, eval_map_real]
    have h1 := two_mul_evalIn (K := ℝ) Q' x
    have h2 := two_mul_evalIn (K := ℝ) Q (g.map f *ᵥ x)
    have hmap : ∀ A : Matrix (Fin n) (Fin n) ℤ, A.map (algebraMap ℤ ℝ) = (A.map (algebraMap ℤ ℚ)).map f := by
      intro A; ext i j; simp [f]
    rw [hmap, hH, Matrix.map_mul, Matrix.map_mul, transpose_map, ← hmap, dotProduct_conj] at h1
    linarith

/-- **Representation numbers of a lattice in a basis:** $r_{g\mathbb{Z}^n}(m) = r_{Q'}(m)$ for $Q'(\vec{x}) = Q(g\vec{x})$. -/
theorem latRep_imgLat {g : Matrix (Fin n) (Fin n) ℚ} (hg : g.det ≠ 0) {Q' : QuadForm ℤ n}
    (hQ' : ∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) (m : ℤ) : latRep Q (imgLat g) m = repNum Q' m := by
  have hgU : IsUnit g.det := isUnit_iff_ne_zero.mpr hg
  unfold latRep repNum repSet
  symm
  refine Nat.card_congr
    { toFun := fun c => ⟨g *ᵥ cv c.1, ⟨c.1, rfl⟩, by
        rw [← hQ', evalIn_cv]; exact_mod_cast c.2⟩
      invFun := fun x => ⟨intPart (g⁻¹ *ᵥ x.1), by
        obtain ⟨⟨c, hc⟩, hq⟩ := x.2
        simp only [Set.mem_setOf_eq]
        rw [hc, mulVec_mulVec, nonsing_inv_mul _ hgU, one_mulVec, intPart_cv]
        have := hq; rw [hc, ← hQ', evalIn_cv] at this; exact_mod_cast this⟩
      left_inv := fun c => by
        apply Subtype.ext
        simp only
        rw [mulVec_mulVec, nonsing_inv_mul _ hgU, one_mulVec, intPart_cv]
      right_inv := fun x => by
        obtain ⟨x, ⟨c, rfl⟩, -⟩ := x
        apply Subtype.ext
        simp only
        rw [mulVec_mulVec, nonsing_inv_mul _ hgU, one_mulVec, intPart_cv] }

/-- **Every $p$-neighbour has an integral Gram form in the genus** ($p$ odd, $p \nmid \det H$): for $L' \in$ `neighbors Q p`
there are $g$ with $L' = g\mathbb{Z}^n$ and an integral $Q' = Q \circ g$ in the genus of $Q$; then $r_{L'}(m) = r_{Q'}(m)$. -/
theorem exists_gram_of_mem_neighbors (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    {L : Submodule ℤ (Fin n → ℚ)} (hL : L ∈ neighbors Q p) :
    ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det ≠ 0 ∧ L = imgLat g ∧
      ∃ Q' : QuadForm ℤ n, (∀ x, Q'.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ SameGenus Q Q' := by
  have hN := (mem_neighbors_iff hdet).mp hL
  obtain ⟨v, hv, hv0, rfl⟩ := exists_eq_nbLat hdet hN
  obtain ⟨g, hg, hLg⟩ := exists_basis_of_le (p := p) (L := nbLat Q p v)
    (fun x hx => exists_eq_of_mem_nbLat hx)
    (fun y => by rw [cv_mem_nbLat_iff hv, bZ_smul_left]; exact dvd_mul_right _ _)
  rw [hLg] at hN ⊢
  obtain ⟨Q', hQ'⟩ := exists_gramForm (Q := Q) (g := g) fun c => hN.integral _ ⟨c, rfl⟩
  exact ⟨g, hg, rfl, Q', hQ', sameGenus_of_neighbor hp2 hdet hg hN hQ'⟩

end NbGenus

end QuadFormsKB.Siegel.Kneser
