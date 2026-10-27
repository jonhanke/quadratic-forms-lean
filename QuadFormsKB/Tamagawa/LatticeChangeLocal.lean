/-
# Change of lattice at a finite prime of a number field

**Layer:** a number field $F$, a finite prime $\mathfrak p$, the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$; the groups
$O(V)(F_\mathfrak p)$ of `Lattices/` and the integral representation `intRep` of the local orbital identity.

For $Q_0$ over $\mathcal O_F$, $c \in \mathcal O_F\setminus0$ and $D = \mathrm{diag}(c_0, \dots, c_{n-1})$ over $\mathcal O_F$ with $\det D \ne 0$, the
form $Q_1 = c\,(Q_0\circ D)$ is the form of the lattice $D\mathcal O_F^n$ (rescaled). Conjugation by $D$ identifies
$O(Q_1)(F_\mathfrak p)$ with $O(Q_0)(F_\mathfrak p)$ (`conjOrth`) and carries $O(\mathfrak o_\mathfrak p^n)$ for $Q_1$ to the stabilizer
$B_\mathfrak p$ of $D\mathfrak o_\mathfrak p^n$. The DVR formula (`LatChange.selfDensity_formula`, applied to $Q_1$ and to $Q_0$ with the
same $j$) gives **the local change-of-lattice identity** (`localDensity_mul_relRatio`):
$$\beta_\mathfrak p(Q_1, Q_1)\cdot\frac{[A : A\cap B]}{[B : A\cap B]} = \prod_{a \le b}q^{\mathrm{ord}_\mathfrak p(c\,c_ac_b)}\cdot\beta_\mathfrak p(Q_0, Q_0),
\qquad A = O(\mathfrak o_\mathfrak p^n),\ B = \mathrm{Stab}(D\mathfrak o_\mathfrak p^n),$$
i.e. The normalization $\mathrm{vol}(O(L_\mathfrak p)) = \beta_\mathfrak p(L, L)$ is the same Haar measure for every lattice (the gauge-form
measure), up to the Jacobian $\prod_{a\le b}|c\,c_ac_b|_\mathfrak p^{-1}$ of $S \mapsto c\,(S\circ D)$ on coefficients.
-/
import QuadFormsKB.Tamagawa.LatticeChange
import QuadFormsKB.Tamagawa.LocalUnimodular

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm

/-! ### Similar forms have conjugate orthogonal groups -/

section Conj

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

theorem hessian_smul {A : Type*} [CommRing A] (c : A) (S : QuadForm A n) : (c • S).hessian = c • S.hessian := by
  ext a b; simp [hessian, mul_add]

theorem conj_iff {A : Type*} [CommRing A] {G Gi X H : Matrix (Fin n) (Fin n) A} (h1 : G * Gi = 1) (h2 : Gi * G = 1) :
    Xᵀ * (Gᵀ * H * G) * X = Gᵀ * H * G ↔ (G * X * Gi)ᵀ * H * (G * X * Gi) = H := by
  have hT : Giᵀ * Gᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  constructor
  · intro e
    calc (G * X * Gi)ᵀ * H * (G * X * Gi) = Giᵀ * (Xᵀ * (Gᵀ * H * G) * X) * Gi := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = Giᵀ * Gᵀ * H * (G * Gi) := by rw [e]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hT, h1, Matrix.one_mul, Matrix.mul_one]
  · intro e
    have e2 : G * X * Gi * G = G * X := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    calc Xᵀ * (Gᵀ * H * G) * X = (G * X * Gi * G)ᵀ * H * (G * X * Gi * G) := by
          rw [e2]; simp only [transpose_mul, Matrix.mul_assoc]
      _ = Gᵀ * ((G * X * Gi)ᵀ * H * (G * X * Gi)) * G := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = Gᵀ * H * G := by rw [e]

variable (Q : QuadForm F n) {c : F} (hc : c ≠ 0) (g : GL (Fin n) F) (R : Type*) [Field R] [Algebra F R]

/-- $g$ over $R$. -/
abbrev gR : GL (Fin n) R := Matrix.GeneralLinearGroup.map (algebraMap F R) g

include hc in
theorem mem_orthGroup_smul_compMat {h : GL (Fin n) R} :
    h ∈ orthGroup (c • Q.compMat g.val) R ↔ gR g R * h * (gR g R)⁻¹ ∈ orthGroup Q R := by
  rw [mem_orthGroup, mem_orthGroup, hessian_smul, hessian_compMat]
  set H := Q.hessian.map (algebraMap F R)
  set G : Matrix (Fin n) (Fin n) R := (gR g R).val
  set Gi : Matrix (Fin n) (Fin n) R := ((gR g R)⁻¹ : GL (Fin n) R).val
  have hGGi : G * Gi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmap : (c • (g.valᵀ * Q.hessian * g.val)).map (algebraMap F R) = algebraMap F R c • (Gᵀ * H * G) := by
    have : (g.valᵀ * Q.hessian * g.val).map (algebraMap F R) = Gᵀ * H * G := by
      simp only [G, H, Matrix.map_mul, Matrix.transpose_map]; rfl
    rw [← this]; ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hc' : algebraMap F R c ≠ 0 := (map_ne_zero _).mpr hc
  rw [hmap, Units.val_mul, Units.val_mul]
  change (h.val)ᵀ * (algebraMap F R c • (Gᵀ * H * G)) * h.val = algebraMap F R c • (Gᵀ * H * G) ↔
    (G * h.val * Gi)ᵀ * H * (G * h.val * Gi) = H
  rw [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro e
    refine (conj_iff hGGi hGiG).mp ?_
    have := congrArg (fun M => (algebraMap F R c)⁻¹ • M) e
    simpa only [smul_smul, inv_mul_cancel₀ hc', one_smul] using this
  · intro e
    rw [(conj_iff hGGi hGiG).mpr e]

/-- **Conjugation by $g$:** $O(c\,(Q\circ g))(R) \cong O(Q)(R)$, $h \mapsto ghg^{-1}$. -/
def conjOrth : orthGroup (c • Q.compMat g.val) R ≃* orthGroup Q R where
  toFun h := ⟨gR g R * h * (gR g R)⁻¹, (mem_orthGroup_smul_compMat Q hc g R).mp h.2⟩
  invFun σ := ⟨(gR g R)⁻¹ * σ * gR g R, (mem_orthGroup_smul_compMat Q hc g R).mpr (by
    rw [show gR g R * ((gR g R)⁻¹ * (σ : GL (Fin n) R) * gR g R) * (gR g R)⁻¹ = σ by group]; exact σ.2)⟩
  left_inv h := by apply Subtype.ext; simp only; group
  right_inv σ := by apply Subtype.ext; simp only; group
  map_mul' a b := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

theorem conjOrth_apply (h : orthGroup (c • Q.compMat g.val) R) :
    ((conjOrth Q hc g R h : orthGroup Q R) : GL (Fin n) R) = gR g R * h * (gR g R)⁻¹ := rfl

theorem conjOrth_symm_apply (σ : orthGroup Q R) :
    (((conjOrth Q hc g R).symm σ : orthGroup (c • Q.compMat g.val) R) : GL (Fin n) R) =
      (gR g R)⁻¹ * σ * gR g R := rfl

end Conj

/-! ### The setting at a finite prime -/

section Setting

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem map_smul_compMat_diagonal {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (c : A) (S : QuadForm A n)
    (cv : Fin n → A) :
    (c • S.compMat (diagonal cv)).map f = f c • (S.map f).compMat (diagonal (fun a => f (cv a))) := by
  ext a b
  show f ((c • S.compMat (diagonal cv)).coeff a b) = _
  rw [smul_compMat_diagonal_coeff, smul_compMat_diagonal_coeff]
  simp only [QuadForm.map, map_mul]
  rfl

/-- **The diagonal matrix** $D = \mathrm{diag}(c_a)$ as an element of $\mathrm{GL}_n(F)$. -/
def gDiag (cv : Fin n → 𝓞 F) (hcv : ∀ a, cv a ≠ 0) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal fun a => (cv a : F)) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (hcv a))

theorem gDiag_val (cv : Fin n → 𝓞 F) (hcv : ∀ a, cv a ≠ 0) : (gDiag cv hcv).val = diagonal fun a => (cv a : F) := rfl

/-- $Q_1 = c\,(Q_0\circ D)$ over $F$ is $c\,(Q_{0,F}\circ D)$. -/
theorem map_Q₁ (Q₀ : QuadForm (𝓞 F) n) (c : 𝓞 F) (cv : Fin n → 𝓞 F) (hcv : ∀ a, cv a ≠ 0) :
    (c • Q₀.compMat (diagonal cv)).map (algebraMap (𝓞 F) F) =
      (c : F) • (Q₀.map (algebraMap (𝓞 F) F)).compMat (gDiag cv hcv).val := by
  rw [map_smul_compMat_diagonal, gDiag_val]

end Setting

/-! ### The local identity -/

section LocalIdentity

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable (Q₀ : QuadForm (𝓞 F) n) {c : 𝓞 F} (hc : c ≠ 0) (cv : Fin n → 𝓞 F) (hcv : ∀ a, cv a ≠ 0)

theorem coe_ne_zero {x : 𝓞 F} (hx : x ≠ 0) : (x : F) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hx

/-- **$Q_1 = c\,(Q_0\circ D)$ over $F$.** -/
abbrev Q1F : QuadForm F n := (c : F) • (Q₀.map (algebraMap (𝓞 F) F)).compMat (gDiag cv hcv).val

/-- **Conjugation by $D$:** $O(Q_1)(F_\mathfrak p) \cong O(Q_0)(F_\mathfrak p)$. -/
def conjD : orthGroup (Q1F Q₀ (c := c) cv hcv) Fv ≃* orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv :=
  conjOrth _ (coe_ne_zero hc) (gDiag cv hcv) Fv

/-- **The stabilizer of $D\mathfrak o_\mathfrak p^n$** in $O(Q_0)(F_\mathfrak p)$: the image of $O(\mathfrak o_\mathfrak p^n)$ for $Q_1$. -/
def stabB : Subgroup (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv) :=
  (stdStab (Q1F Q₀ (c := c) cv hcv) v).map (conjD v Q₀ hc cv hcv).toMonoidHom

theorem isIntModel_Q1F : IsIntModel v (Q1F Q₀ (c := c) cv hcv)
    ((NF.ι v c) • (NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a))) := fun y => by
  rw [Q1F, ← map_Q₁, evalIn_coe_o, NF.Qp, map_smul_compMat_diagonal]

theorem isIntModel_QF : IsIntModel v (Q₀.map (algebraMap (𝓞 F) F)) (NF.Qp v Q₀) := fun y => evalIn_coe_o v Q₀ y

/-- The diagonal matrix over $F_\mathfrak p$. -/
theorem gR_gDiag_val : (gR (gDiag cv hcv) Fv).val =
    (diagonal fun a => NF.ι v (cv a)).map (algebraMap 𝔬 Fv) := by
  ext a b
  by_cases h : a = b
  · subst h; simp [gDiag_val]; rfl
  · simp [gDiag_val, h]

theorem cancel_gl {R : Type*} [CommRing R] (g : GL (Fin n) R) {X Y : Matrix (Fin n) (Fin n) R}
    (h : g.val * X = g.val * Y) : X = Y := by
  have := congrArg (fun M => (g⁻¹ : GL (Fin n) R).val * M) h
  simpa only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] using this

theorem cancel_gl_right {R : Type*} [CommRing R] (g : GL (Fin n) R) {X Y : Matrix (Fin n) (Fin n) R}
    (h : X * g.val = Y * g.val) : X = Y := by
  have := congrArg (fun M => M * (g⁻¹ : GL (Fin n) R).val) h
  simpa only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] using this

theorem conjD_val_mul (h : orthGroup (Q1F Q₀ (c := c) cv hcv) Fv) :
    ((conjD v Q₀ hc cv hcv h : orthGroup _ Fv) : GL (Fin n) Fv).val * (gR (gDiag cv hcv) Fv).val =
      (gR (gDiag cv hcv) Fv).val * (h : GL (Fin n) Fv).val := by
  rw [conjD, conjOrth_apply, ← Units.val_mul, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem gR_mul_conjD_symm_val (κ : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv) :
    (gR (gDiag cv hcv) Fv).val * (((conjD v Q₀ hc cv hcv).symm κ : orthGroup _ Fv) : GL (Fin n) Fv).val =
      (κ : GL (Fin n) Fv).val * (gR (gDiag cv hcv) Fv).val := by
  rw [conjD, conjOrth_symm_apply, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
    one_mul]

theorem one_ne_zero' : ∀ _ : Fin n, (1 : 𝔬) ≠ 0 := fun _ => one_ne_zero

include hcv in
theorem ι_cv_ne_zero : ∀ a, NF.ι v (cv a) ≠ 0 := fun a => NF.ι_ne_zero v (hcv a)

/-- **Boxes correspond under conjugation, forward.** -/
theorem box_fwd (j : ℕ) (h : stdStab (Q1F Q₀ (c := c) cv hcv) v)
    (hh : h ∈ boxSub (NF.π v) (intRep v (Q1F Q₀ (c := c) cv hcv)) (ι_cv_ne_zero v cv hcv) j) :
    ∃ κ ∈ boxSub (NF.π v) (intRep v (Q₀.map (algebraMap (𝓞 F) F))) (one_ne_zero' (n := n) v) j,
      (κ : orthGroup _ Fv) = conjD v Q₀ hc cv hcv h := by
  set φ := algebraMap 𝔬 Fv
  set Do : Matrix (Fin n) (Fin n) 𝔬 := diagonal fun a => NF.ι v (cv a)
  have hDF : (gR (gDiag cv hcv) Fv).val = Do.map φ := gR_gDiag_val v cv hcv
  -- the conjugate of a box element is `1 + π^j Z`
  have key : ∀ h' : stdStab (Q1F Q₀ (c := c) cv hcv) v,
      h' ∈ boxSub (NF.π v) (intRep v (Q1F Q₀ (c := c) cv hcv)) (ι_cv_ne_zero v cv hcv) j →
      ∃ Z : Matrix (Fin n) (Fin n) 𝔬, ((conjD v Q₀ hc cv hcv h' : orthGroup _ Fv) : GL (Fin n) Fv).val =
        (1 + NF.π v ^ j • Z).map φ := by
    intro h' hh'
    obtain ⟨Z, hZ⟩ := hh'
    refine ⟨Z, cancel_gl_right (gR (gDiag cv hcv) Fv) ?_⟩
    rw [conjD_val_mul, hDF, ← intRep_map, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have : Do * intRep v _ (h' : stdStab _ v) = Do + NF.π v ^ j • Z * Do := by
      rw [← hZ, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [this, Matrix.add_mul, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ := key h hh
  obtain ⟨Z', hZ'⟩ := key h⁻¹ (inv_mem hh)
  have hmem : (conjD v Q₀ hc cv hcv h : orthGroup _ Fv) ∈ stdStab (Q₀.map (algebraMap (𝓞 F) F)) v := by
    refine mem_stdStab_of_integral v _ _ (1 + NF.π v ^ j • Z) (1 + NF.π v ^ j • Z') hZ.symm ?_
    rw [← map_inv, ← hZ']; rfl
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  have hrep : intRep v (Q₀.map (algebraMap (𝓞 F) F)) ⟨_, hmem⟩ = 1 + NF.π v ^ j • Z :=
    map_o_injective v (by beta_reduce; rw [intRep_map]; exact hZ)
  rw [mem_boxSub, hrep, add_sub_cancel_left]
  refine ⟨Z, ?_⟩
  rw [show (diagonal fun _ => (1 : 𝔬) : Matrix (Fin n) (Fin n) 𝔬) = 1 from diagonal_one, Matrix.one_mul,
    Matrix.mul_one]

/-- **Boxes correspond under conjugation, backward** ($j \ge \mathrm{ord}\,c_a$). -/
theorem box_bwd {j : ℕ} (hj : ∀ a, ord (NF.irreducible_π v) (NF.ι v (cv a)) ≤ j)
    (κ : stdStab (Q₀.map (algebraMap (𝓞 F) F)) v)
    (hκ : κ ∈ boxSub (NF.π v) (intRep v (Q₀.map (algebraMap (𝓞 F) F))) (one_ne_zero' (n := n) v) j) :
    ∃ h ∈ boxSub (NF.π v) (intRep v (Q1F Q₀ (c := c) cv hcv)) (ι_cv_ne_zero v cv hcv) j,
      conjD v Q₀ hc cv hcv h = (κ : orthGroup _ Fv) := by
  set φ := algebraMap 𝔬 Fv
  set Do : Matrix (Fin n) (Fin n) 𝔬 := diagonal fun a => NF.ι v (cv a)
  have hDF : (gR (gDiag cv hcv) Fv).val = Do.map φ := gR_gDiag_val v cv hcv
  obtain ⟨ev, hev⟩ := exists_ev (NF.irreducible_π v) (ι_cv_ne_zero v cv hcv) hj
  have key : ∀ κ' : stdStab (Q₀.map (algebraMap (𝓞 F) F)) v,
      κ' ∈ boxSub (NF.π v) (intRep v (Q₀.map (algebraMap (𝓞 F) F))) (one_ne_zero' (n := n) v) j →
      ∃ Z : Matrix (Fin n) (Fin n) 𝔬, (((conjD v Q₀ hc cv hcv).symm κ' : orthGroup _ Fv) : GL (Fin n) Fv).val =
        (1 + psi (fun a => NF.ι v (cv a)) ev Z).map φ := by
    intro κ' hκ'
    obtain ⟨Z, hZ⟩ := hκ'
    rw [show (diagonal fun _ => (1 : 𝔬) : Matrix (Fin n) (Fin n) 𝔬) = 1 from diagonal_one, Matrix.one_mul,
      Matrix.mul_one] at hZ
    refine ⟨Z, cancel_gl (gR (gDiag cv hcv) Fv) ?_⟩
    rw [gR_mul_conjD_symm_val, hDF, ← intRep_map, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, diagonal_mul_psi hev, show intRep v _ κ' = 1 + NF.π v ^ j • Z by
      rw [← hZ]; abel, Matrix.add_mul, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ := key κ hκ
  obtain ⟨Z', hZ'⟩ := key κ⁻¹ (inv_mem hκ)
  have hmem : (conjD v Q₀ hc cv hcv).symm κ ∈ stdStab (Q1F Q₀ (c := c) cv hcv) v := by
    refine mem_stdStab_of_integral v _ _ (1 + psi (fun a => NF.ι v (cv a)) ev Z)
      (1 + psi (fun a => NF.ι v (cv a)) ev Z') hZ.symm ?_
    rw [← map_inv, ← hZ']; rfl
  refine ⟨⟨_, hmem⟩, ?_, by simp⟩
  have hrep : intRep v (Q1F Q₀ (c := c) cv hcv) ⟨_, hmem⟩ = 1 + psi (fun a => NF.ι v (cv a)) ev Z :=
    map_o_injective v (by beta_reduce; rw [intRep_map]; exact hZ)
  rw [mem_boxSub, hrep, add_sub_cancel_left]
  exact psi_mem_boxV hev Z

omit [NumberField F] in
/-- $\beta_\mathfrak p(L, L) > 0$ for nondegenerate $Q$ (the identity solves $Q\circ X \equiv Q$). -/
theorem localDensityForm_self_pos [NumberField F] {m : ℕ} (Q : QuadForm (𝓞 F) m) (hQ : Q.Nondegenerate) :
    0 < NF.localDensityForm v Q Q := by
  obtain ⟨k, hk⟩ := (NF.localDensityForm_self_eventually_eq v Q hQ).exists
  have hfin : Finite (𝓞 F ⧸ v.asIdeal ^ k) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  have hcount : 0 < NF.repCountForm v Q Q k := by
    unfold NF.repCountForm
    have : Nonempty {X : Matrix (Fin m) (Fin m) (𝓞 F ⧸ v.asIdeal ^ k) //
        (Q.map (Ideal.Quotient.mk _)).compMat X = Q.map (Ideal.Quotient.mk _)} :=
      ⟨⟨1, QuadForm.compMat_one _⟩⟩
    exact Nat.card_pos
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  rw [← hk]; exact div_pos (by exact_mod_cast hcount) (pow_pos hN _)

theorem relIndex_map_subtype {G : Type*} [Group G] {K : Subgroup G} (W : Subgroup K) :
    (W.map K.subtype).relIndex K = W.index := by
  rw [Subgroup.relIndex]
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, hxy⟩; rwa [← Subtype.ext hxy]
  · intro hx; exact ⟨x, hx, rfl⟩

/-- **The boxes correspond:** $D\,W_1(j)\,D^{-1} = W_0(j)$ for $j \ge \mathrm{ord}\,c_a$. -/
theorem map_box_eq {j : ℕ} (hj : ∀ a, ord (NF.irreducible_π v) (NF.ι v (cv a)) ≤ j) :
    ((boxSub (NF.π v) (intRep v (Q1F Q₀ (c := c) cv hcv)) (ι_cv_ne_zero v cv hcv) j).map
        (stdStab (Q1F Q₀ (c := c) cv hcv) v).subtype).map (conjD v Q₀ hc cv hcv).toMonoidHom =
      (boxSub (NF.π v) (intRep v (Q₀.map (algebraMap (𝓞 F) F))) (one_ne_zero' (n := n) v) j).map
        (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v).subtype := by
  ext σ
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, ⟨h, hh, rfl⟩, rfl⟩
    obtain ⟨κ, hκ, he⟩ := box_fwd v Q₀ hc cv hcv j h hh
    exact ⟨κ, hκ, he⟩
  · rintro ⟨κ, hκ, rfl⟩
    obtain ⟨h, hh, he⟩ := box_bwd v Q₀ hc cv hcv hj κ hκ
    exact ⟨h, ⟨h, hh, rfl⟩, he⟩

/-- **The local change-of-lattice identity** at a finite prime $\mathfrak p$ (dyadic included): for $Q_0$ nondegenerate over
$\mathcal O_F$, $c \ne 0$, $D = \mathrm{diag}(c_a)$ with $c_a \ne 0$ and $Q_1 = c\,(Q_0\circ D)$,
$$\beta_\mathfrak p(Q_1, Q_1)\cdot r(A, B) = \prod_{a \le b}q^{\mathrm{ord}_\mathfrak p(c\,c_ac_b)}\cdot\beta_\mathfrak p(Q_0, Q_0),$$
$A = O(\mathfrak o_\mathfrak p^n)$, $B$ = the stabilizer of $D\mathfrak o_\mathfrak p^n$ in $O(Q_0)(F_\mathfrak p)$, $r(A,B) = [A : A\cap B]/[B : A\cap B]$
(`relRatio`). Weil 1982, §2.2.1, p. 14 (the local measure $\omega_v$ of a gauge form does not depend on the local coordinates). -/
@[kb "weil1982" "§2.2.1, p. 14 (the local measure does not depend on the coordinates)"]
theorem localDensity_mul_relRatio (hQ₀ : Q₀.Nondegenerate) :
    NF.localDensityForm v (c • Q₀.compMat (diagonal cv)) (c • Q₀.compMat (diagonal cv)) *
        relRatio (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) (stabB v Q₀ hc cv hcv) =
      (∏ p : DVR.UpperIdx n, (DVR.q 𝔬 : ℝ) ^ ord (NF.irreducible_π v) (NF.ι v (wts c cv p))) *
        NF.localDensityForm v Q₀ Q₀ := by
  classical
  set hπ := NF.irreducible_π v
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set Q₁ := c • Q₀.compMat (diagonal cv)
  have hQ₁ : Q₁.Nondegenerate := nondegenerate_Q₁ hc hQ₀ hcv
  have e₁ : NF.Qp v Q₁ = NF.ι v c • (NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a)) :=
    map_smul_compMat_diagonal _ _ _ _
  have e₀ : (1 : 𝔬) • (NF.Qp v Q₀).compMat (diagonal fun _ : Fin n => (1 : 𝔬)) = NF.Qp v Q₀ := by
    rw [diagonal_one, compMat_one]; ext a b; simp [smul_coeff]
  have hQo : (NF.Qp v Q₀).Nondegenerate := NF.nondegenerate_Qp v hQ₀
  have hQ₁o : (NF.ι v c • (NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a))).Nondegenerate := by
    rw [← e₁]; exact NF.nondegenerate_Qp v hQ₁
  -- the formula for `Q₁` and for `Q₀`
  have h1 := selfDensity_formula hπ (NF.ι_ne_zero v hc) hQo (ι_cv_ne_zero v cv hcv)
    (intRep v (Q1F Q₀ (c := c) cv hcv)) (fun a => compMat_intRep v (isIntModel_Q1F v Q₀ cv hcv) a)
    (fun X hX => exists_intRep_eq v (isIntModel_Q1F v Q₀ cv hcv) hQ₁o X hX)
  have h0 := selfDensity_formula hπ one_ne_zero hQo (one_ne_zero' (n := n) v) (intRep v QF)
    (fun a => by rw [e₀]; exact compMat_intRep v (isIntModel_QF v Q₀) a)
    (fun X hX => by rw [e₀] at hX; exact exists_intRep_eq v (isIntModel_QF v Q₀) hQo X hX)
  set m := Finset.univ.sup fun a => ord hπ (NF.ι v (cv a))
  obtain ⟨j, ⟨hj1, hj0⟩, hjm⟩ := ((h1.and h0).and (Filter.eventually_ge_atTop m)).exists
  have hj : ∀ a, ord hπ (NF.ι v (cv a)) ≤ j := fun a =>
    (Finset.le_sup (f := fun a => ord hπ (NF.ι v (cv a))) (Finset.mem_univ a)).trans hjm
  rw [e₀] at hj0
  -- indices
  set A := stdStab QF v
  set B := stabB v Q₀ hc cv hcv
  set W₁ := boxSub (NF.π v) (intRep v (Q1F Q₀ (c := c) cv hcv)) (ι_cv_ne_zero v cv hcv) j
  set W₀ := boxSub (NF.π v) (intRep v QF) (one_ne_zero' (n := n) v) j
  set D' := W₀.map A.subtype
  have hmap := map_box_eq v Q₀ hc cv hcv hj
  have iB : W₁.index = D'.relIndex B := by
    rw [← relIndex_map_subtype, ← Subgroup.relIndex_map_map_of_injective
      (f := (conjD v Q₀ hc cv hcv).toMonoidHom) _ _ (conjD v Q₀ hc cv hcv).injective]
    rw [show D' = _ from hmap.symm]; rfl
  have iA : W₀.index = D'.relIndex A := (relIndex_map_subtype W₀).symm
  have hD'A : D' ≤ A := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hD'B : D' ≤ B := by
    rw [show D' = _ from hmap.symm]; exact Subgroup.map_mono (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  have hΦ0 : (∏ p : DVR.UpperIdx n, (DVR.q 𝔬 : ℝ) ^ ord hπ (wts (1 : 𝔬) (fun _ : Fin n => (1 : 𝔬)) p)) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    rw [show wts (1 : 𝔬) (fun _ : Fin n => (1 : 𝔬)) p = 1 by simp [wts], ord_unit hπ isUnit_one, pow_zero]
  rw [hΦ0, mul_one, iA] at hj0
  rw [iB] at hj1
  have hwts : ∀ p : DVR.UpperIdx n, wts (NF.ι v c) (fun a => NF.ι v (cv a)) p = NF.ι v (wts c cv p) := fun p => by
    simp [wts, map_mul]
  simp only [hwts] at hj1
  -- positivity of the densities
  have hpos₀ := localDensityForm_self_pos v Q₀ hQ₀
  have hpos₁ := localDensityForm_self_pos v Q₁ hQ₁
  rw [NF.localDensityForm_eq_completion v Q₀] at hpos₀ ⊢
  rw [NF.localDensityForm_eq_completion v Q₁, e₁] at hpos₁ ⊢
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) ^ (j * (n * (n - 1) / 2)) := pow_pos (by exact_mod_cast DVR.q_pos) _
  have hB0 : (D'.relIndex B : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul, zero_mul] at hj1
    exact (mul_pos hpos₁ hq).ne' hj1
  have hA0 : D'.relIndex A ≠ 0 := by
    intro h0; rw [h0, Nat.cast_zero, zero_mul] at hj0
    exact (mul_pos hpos₀ hq).ne' hj0
  rw [relRatio_eq_of_le (le_inf hD'A hD'B) hA0]
  have : (DVR.localDensityForm (NF.ι v c • (NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a)))
      (NF.ι v c • (NF.Qp v Q₀).compMat (diagonal fun a => NF.ι v (cv a))) (NF.π v) *
        ((D'.relIndex A : ℝ) / (D'.relIndex B : ℝ))) * (DVR.q 𝔬 : ℝ) ^ (j * (n * (n - 1) / 2)) =
      ((∏ p : DVR.UpperIdx n, (DVR.q 𝔬 : ℝ) ^ ord hπ (NF.ι v (wts c cv p))) *
        DVR.localDensityForm (NF.Qp v Q₀) (NF.Qp v Q₀) (NF.π v)) * (DVR.q 𝔬 : ℝ) ^ (j * (n * (n - 1) / 2)) := by
    rw [mul_right_comm, hj1, mul_assoc _ (DVR.localDensityForm _ _ _), hj0]
    field_simp
  exact mul_right_cancel₀ hq.ne' this

end LocalIdentity

end QuadFormsKB.Tamagawa.LatChange
