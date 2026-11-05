/-
# Hanke 2005, (3.3) at dyadic places: the shape $\mathbb H^k\perp N$ of a maximal lattice (proof)

Setting: $\mathfrak o=\mathfrak o_\mathfrak p$ the integers of $F_\mathfrak p$, a discrete valuation ring, $Q$ a nondegenerate
form in $n$ variables over $\mathfrak o$ whose base change to $F_\mathfrak p$ has the extension property `MaxProp`
(a vector $y\in F_\mathfrak p^n$ with $Q(y)$ and $Hy$ integral is integral; this is maximality of $\mathfrak o^n$,
`maxProp_Qp`). Write $B(x,y)=x^{\mathsf T}Hy=Q(x+y)-Q(x)-Q(y)$ for the polar form, $H$ the Hessian.

This file proves `DyadicMaximalKernel` (`dyadicMaximalKernel`), by induction on $n$ (O'Meara 91:2, §82):

1. (*hyperbolic pair*, `exists_hyperbolic_pair`) if $Q\otimes F_\mathfrak p$ is isotropic, an isotropic vector scales to a
   primitive $x\in\mathfrak o^n$; $Hx$ is again primitive (else $x/\pi$ violates `MaxProp`), so there is
   $z\in\mathfrak o^n$ with $B(x,z)=1$, and $e=x$, $f=z-Q(z)x$ satisfy $Q(e)=Q(f)=0$, $B(e,f)=1$.
2. (*splitting*, `exists_split_hyperbolic`) $\mathfrak o^n=M\perp(\mathfrak oe+\mathfrak of)$ with
   $M=\{w:B(w,e)=B(w,f)=0\}$ free of rank $n-2$; in a basis of $M$ followed by $e,f$ the form is $Q'\perp\mathbb H$, and
   $Q'$ is nondegenerate with `MaxProp`.
3. (*induction*) in the anisotropic case $k=0$ and $N=Q$; otherwise apply the induction hypothesis to $Q'$ and transport
   along $\mathrm{GL}$-equivalence of orthogonal sums (`isGLEquiv_orthSum_left`).
4. (*anisotropic dimension*) $t_\mathfrak p=r$ by Witt's uniqueness of the Witt index.

Indices are 0-based. The hypotheses $3\le n$, `ShimuraDetHyp`, $\mathfrak p\mid2$ and $[\widetilde\Lambda:\Lambda]\ne1$ of the
statement are not used: the argument holds at every place.
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicBadShape
import QuadFormsKB.Literature.Hanke2005.DensityOddJordan
import QuadFormsKB.Literature.Hanke2005.DensityOddWitt
import QuadFormsKB.Literature.Hanke2005.LocalTypes
import QuadFormsKB.Literature.Hanke2005.WittDiag
import QuadFormsKB.Literature.Hanke2005.DensityDyadicWitt

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa QuadFormsKB.Lattices QuadForm

section Generic

variable {R : Type*} [CommRing R]

theorem hessian_transpose_eq {m : ℕ} (Q : QuadForm R m) : Q.hessianᵀ = Q.hessian := by
  simp [QuadForm.hessian, add_comm]

/-- The polar form $B(x,y)=x^{\mathsf T}Hy$ is symmetric. -/
theorem dot_hessian_comm {m : ℕ} (Q : QuadForm R m) (x y : Fin m → R) :
    x ⬝ᵥ (Q.hessian *ᵥ y) = y ⬝ᵥ (Q.hessian *ᵥ x) := by
  have h : x ᵥ* Q.hessian = Q.hessian *ᵥ x := by
    conv_lhs => rw [← hessian_transpose_eq Q]
    rw [Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec, h, dotProduct_comm]

/-- **The polar form of an orthogonal sum is the sum of the polar forms.** -/
theorem bil_orthSum {m n : ℕ} (K : Type*) [CommRing K] [Algebra R K] (A : QuadForm R m) (B : QuadForm R n)
    (x y : Fin (m + n) → K) :
    x ⬝ᵥ ((orthSum A B).hessian.map (algebraMap R K) *ᵥ y) =
      (fun a => x (Fin.castAdd n a)) ⬝ᵥ (A.hessian.map (algebraMap R K) *ᵥ fun a => y (Fin.castAdd n a)) +
      (fun b => x (Fin.natAdd m b)) ⬝ᵥ (B.hessian.map (algebraMap R K) *ᵥ fun b => y (Fin.natAdd m b)) := by
  rw [← polar_eq_hessian, ← polar_eq_hessian, ← polar_eq_hessian]
  have e1 : (fun a => (x + y) (Fin.castAdd n a)) =
      (fun a => x (Fin.castAdd n a)) + fun a => y (Fin.castAdd n a) := rfl
  have e2 : (fun b => (x + y) (Fin.natAdd m b)) =
      (fun b => x (Fin.natAdd m b)) + fun b => y (Fin.natAdd m b) := rfl
  rw [evalIn_orthSum, evalIn_orthSum, evalIn_orthSum, e1, e2]
  ring

theorem single_dotProduct_one {N : ℕ} (w : Fin N → R) (i : Fin N) : (Pi.single i (1 : R)) ⬝ᵥ w = w i := by
  simp [dotProduct, Pi.single_apply]

section Dom

variable [IsDomain R]

/-- A summand of a nondegenerate orthogonal sum is nondegenerate. -/
theorem nondegenerate_of_orthSum_left {m n : ℕ} {A : QuadForm R m} {B : QuadForm R n}
    (h : (orthSum A B).Nondegenerate) : A.Nondegenerate := by
  intro hA
  obtain ⟨y, hy, hAy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  apply h
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.append y 0, ?_, ?_⟩
  · intro h0
    apply hy
    funext a
    have := congrFun h0 (Fin.castAdd n a)
    simpa using this
  · funext i
    have := bil_orthSum R A B (Pi.single i 1) (Fin.append y 0)
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at this
    have hl : (fun a => (Fin.append y (0 : Fin n → R)) (Fin.castAdd n a)) = y := by
      funext a; simp
    have hr : (fun b => (Fin.append y (0 : Fin n → R)) (Fin.natAdd m b)) = 0 := by
      funext b; simp
    rw [hl, hr, hAy] at this
    simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero] at this
    rw [single_dotProduct_one] at this
    simpa using this

end Dom

/-- **$\mathrm{GL}$-equivalence of the first summand gives that of the orthogonal sum** (block-diagonal matrix
$\mathrm{diag}(U,1)$). -/
theorem isGLEquiv_orthSum_left {m n : ℕ} [IsDomain R] [IsDiscreteValuationRing R] {A A' : QuadForm R m}
    (B : QuadForm R n) (h : DVR.IsGLEquiv A A') : DVR.IsGLEquiv (orthSum A B) (orthSum A' B) := by
  obtain ⟨U, hU, hUe⟩ := h
  refine ⟨(Matrix.fromBlocks U 0 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm, ?_, fun x => ?_⟩
  · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simpa using hU
  · rw [QuadForm.eval, QuadForm.eval, evalIn_orthSum, evalIn_orthSum]
    have hx : (Matrix.fromBlocks U 0 0 1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) *ᵥ
        (x ∘ finSumFinEquiv) =
        Sum.elim (U *ᵥ fun a => x (Fin.castAdd n a)) (fun b => x (Fin.natAdd m b)) := by
      have : (x ∘ finSumFinEquiv) = Sum.elim (fun a => x (Fin.castAdd n a)) (fun b => x (Fin.natAdd m b)) := by
        funext s; cases s <;> rfl
      rw [this, Matrix.fromBlocks_mulVec]
      simp
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hx]
    simp only [Function.comp, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr]
    have := hUe fun a => x (Fin.castAdd n a)
    rw [QuadForm.eval, QuadForm.eval] at this
    rw [this]

end Generic

section Pair

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem eval_map_eq_evalIn (Q : QuadForm 𝔬 n) (y : Fin n → Fv) :
    (Q.map (algebraMap 𝔬 Fv)).eval y = Q.evalIn Fv y := by
  simp [QuadForm.evalIn, QuadForm.map]

theorem hessian_map_eq (Q : QuadForm 𝔬 n) :
    (Q.map (algebraMap 𝔬 Fv)).hessian = Q.hessian.map (algebraMap 𝔬 Fv) := by
  ext i j; simp [QuadForm.hessian, QuadForm.map]

theorem pi_ne_zero_Fv : (algebraMap 𝔬 Fv (NF.π v)) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr (NF.irreducible_π v).ne_zero

/-- **A primitive isotropic vector:** an isotropic vector of $Q\otimes F_\mathfrak p$ scales to $x\in\mathfrak o^n$ with a
unit coordinate and $Q(x)=0$ (divide by a coordinate of maximal valuation). -/
@[kb "omeara1963" "§82:? (scaling an isotropic vector to a primitive vector of the lattice)"]
theorem exists_primitive (Q : QuadForm 𝔬 n) {y : Fin n → Fv} (hy : y ≠ 0)
    (h0 : (Q.map (algebraMap 𝔬 Fv)).eval y = 0) :
    ∃ x : Fin n → 𝔬, (∃ i, IsUnit (x i)) ∧ Q.eval x = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hall; push Not at hall; exact hy (funext hall)
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun i => Valued.v (y i)) ⟨j, Finset.mem_univ j⟩
  have hv0 : Valued.v (y j) ≠ 0 := (Valuation.ne_zero_iff _).mpr hj
  have hi0v : Valued.v (y i₀) ≠ 0 := fun h =>
    hv0 (le_antisymm ((hmax j (Finset.mem_univ j)).trans h.le) zero_le)
  have hi0 : y i₀ ≠ 0 := fun h => hi0v (by rw [h, map_zero])
  set c : Fv := (y i₀)⁻¹ with hc
  have hle : ∀ l, Valued.v (c * y l) ≤ 1 := by
    intro l
    rw [hc, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr hi0v)]
    simpa using hmax l (Finset.mem_univ l)
  refine ⟨fun l => toO v (c * y l) (hle l), ⟨i₀, ?_⟩, ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v (c * y i₀) = 1
    rw [hc, inv_mul_cancel₀ hi0, map_one]
  · apply IsFractionRing.injective 𝔬 Fv
    rw [map_zero]
    rw [← eval_map_comp' (algebraMap 𝔬 Fv) Q (fun l => toO v (c * y l) (hle l))]
    have e : (fun l => algebraMap 𝔬 Fv (toO v (c * y l) (hle l))) = c • y := by funext l; rfl
    rw [e, eval_smul_sq, h0, mul_zero]

/-- **The Hessian image of a primitive isotropic vector is primitive** (maximality: otherwise $x/\pi$ is an isotropic
vector of integral polar form, hence integral by `MaxProp`, contradicting primitivity of $x$). -/
@[kb "omeara1963" "§82H, p. 234 (maximality forces Hx primitive for a primitive isotropic x)"]
theorem exists_unit_hessian (Q : QuadForm 𝔬 n) (MP : MaxProp v (Q.map (algebraMap 𝔬 Fv)))
    {x : Fin n → 𝔬} (hxu : ∃ i, IsUnit (x i)) (hx0 : Q.eval x = 0) :
    ∃ j, IsUnit ((Q.hessian *ᵥ x) j) := by
  by_contra hall
  push Not at hall
  have hπ := NF.irreducible_π v
  have hdiv : ∀ j, ∃ c, (Q.hessian *ᵥ x) j = NF.π v * c := fun j => by
    by_contra hnd
    push Not at hnd
    exact hall j (DVR.dvr_isUnit_of_not_dvd hπ (fun ⟨c, hc⟩ => hnd c hc))
  choose w hw using hdiv
  obtain ⟨π', hπ'⟩ : ∃ π' : Fv, π' = algebraMap 𝔬 Fv (NF.π v) := ⟨_, rfl⟩
  have hπ0 : π' ≠ 0 := by rw [hπ']; exact pi_ne_zero_Fv v
  have hvπ : Valued.v π' = WithZero.exp (-1 : ℤ) := by rw [hπ']; exact NF.valued_π v
  set y : Fin n → Fv := π'⁻¹ • fun i => algebraMap 𝔬 Fv (x i) with hy
  have h1 : Valued.v ((Q.map (algebraMap 𝔬 Fv)).eval y) ≤ 1 := by
    rw [hy, eval_smul_sq]
    have := eval_map_comp' (algebraMap 𝔬 Fv) Q x
    rw [this, hx0, map_zero, mul_zero, map_zero]
    exact zero_le
  have h2 : ((Q.map (algebraMap 𝔬 Fv)).hessian *ᵥ y) ∈ std v := by
    refine mem_std_of_le_one v fun j => ?_
    have e : ((Q.map (algebraMap 𝔬 Fv)).hessian *ᵥ y) j = algebraMap 𝔬 Fv (w j) := by
      rw [hessian_map_eq, hy, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have := RingHom.map_mulVec (algebraMap 𝔬 Fv) Q.hessian x j
      have e2 : (Q.hessian.map (algebraMap 𝔬 Fv) *ᵥ fun i => algebraMap 𝔬 Fv (x i)) j =
          algebraMap 𝔬 Fv ((Q.hessian *ᵥ x) j) := this.symm
      rw [e2, hw j, map_mul, ← hπ']
      field_simp
    rw [e]; exact valued_le_one_of_mem v _
  have h3 := v_le_one_of_mem_std v (MP y h1 h2)
  obtain ⟨i, hi⟩ := hxu
  have hxi : Valued.v (algebraMap 𝔬 Fv (x i)) = 1 :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hi
  have h4 := h3 i
  rw [hy, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, hvπ] at h4
  have h5 : Valued.v (algebraMap 𝔬 Fv (x i)) = 1 := hxi
  simp only [h5, mul_one] at h4
  have h6 : (1 : WithZero (Multiplicative ℤ)) < (WithZero.exp (-1 : ℤ))⁻¹ := by
    rw [← WithZero.exp_neg]
    have : (WithZero.exp (1 : ℤ)) > WithZero.exp 0 := WithZero.exp_lt_exp.mpr (by norm_num)
    have h7 : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(-1 : ℤ)) := by
      rw [neg_neg]; simp
    exact h7
  exact absurd h4 (not_le.mpr h6)

/-- **A hyperbolic pair in the lattice** (O'Meara 82:?): if $\mathfrak o^n$ is maximal for $Q$ (`MaxProp`) and $Q$ is
isotropic over $F_\mathfrak p$, there are $e,f\in\mathfrak o^n$ with $Q(e)=Q(f)=0$ and $B(e,f)=1$. -/
@[kb "omeara1963" "§82:? (hyperbolic pair in a maximal lattice on an isotropic space)"]
theorem exists_hyperbolic_pair (Q : QuadForm 𝔬 n) (MP : MaxProp v (Q.map (algebraMap 𝔬 Fv)))
    {y : Fin n → Fv} (hy : y ≠ 0) (h0 : (Q.map (algebraMap 𝔬 Fv)).eval y = 0) :
    ∃ e f : Fin n → 𝔬, Q.eval e = 0 ∧ Q.eval f = 0 ∧ e ⬝ᵥ (Q.hessian *ᵥ f) = 1 := by
  obtain ⟨x, hxu, hx0⟩ := exists_primitive v Q hy h0
  obtain ⟨j, hj⟩ := exists_unit_hessian v Q MP hxu hx0
  obtain ⟨z, hxz⟩ : ∃ z : Fin n → 𝔬, x ⬝ᵥ (Q.hessian *ᵥ z) = 1 := by
    refine ⟨(↑(hj.unit⁻¹) : 𝔬) • Pi.single j (1 : 𝔬), ?_⟩
    rw [dot_hessian_comm, smul_dotProduct, single_dotProduct_one, smul_eq_mul]
    exact hj.val_inv_mul
  have hzx : z ⬝ᵥ (Q.hessian *ᵥ x) = 1 := by rw [dot_hessian_comm]; exact hxz
  have hxx : x ⬝ᵥ (Q.hessian *ᵥ x) = 0 := by rw [dotProduct_hessian_self, hx0, mul_zero]
  set t : 𝔬 := -(Q.eval z) with ht
  refine ⟨x, z + t • x, hx0, ?_, ?_⟩
  · rw [eval_add_hessian, eval_smul_sq, hx0, Matrix.mulVec_smul, dotProduct_smul, hzx, ht]
    simp
  · rw [Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_smul, dotProduct_smul, hxz, hxx]
    simp

end Pair

section Split

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **The orthogonal complement $M=\{w:B(w,e)=B(w,f)=0\}$ of a pair $e,f$** (a submodule of $R^n$). -/
def orthSub (Q : QuadForm R n) (e f : Fin n → R) : Submodule R (Fin n → R) where
  carrier := {w | w ⬝ᵥ (Q.hessian *ᵥ e) = 0 ∧ w ⬝ᵥ (Q.hessian *ᵥ f) = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [add_dotProduct, ha1, hb1, add_zero], by rw [add_dotProduct, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c w ⟨h1, h2⟩
    exact ⟨by rw [smul_dotProduct, h1, smul_zero], by rw [smul_dotProduct, h2, smul_zero]⟩

/-- The matrix with columns $e,f$. -/
def eMat (e f : Fin n → R) : Matrix (Fin n) (Fin 2) R := Matrix.of fun l j => (![e, f] j) l

theorem eMat_mulVec (e f : Fin n → R) (s : Fin 2 → R) : eMat e f *ᵥ s = s 0 • e + s 1 • f := by
  funext l
  simp [eMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The map $(w,s)\mapsto w+s_0e+s_1f$ from $M\times R^2$ to $R^n$. -/
def splitMap (Q : QuadForm R n) (e f : Fin n → R) : (orthSub Q e f × (Fin 2 → R)) →ₗ[R] (Fin n → R) :=
  (orthSub Q e f).subtype.coprod (Matrix.mulVecLin (eMat e f))

theorem splitMap_apply (Q : QuadForm R n) (e f : Fin n → R) (w : orthSub Q e f) (s : Fin 2 → R) :
    splitMap Q e f (w, s) = (w : Fin n → R) + eMat e f *ᵥ s := by
  simp [splitMap]

theorem splitMap_bijective (Q : QuadForm R n) (e f : Fin n → R) (he : Q.eval e = 0) (hf : Q.eval f = 0)
    (hef : e ⬝ᵥ (Q.hessian *ᵥ f) = 1) : Function.Bijective (splitMap Q e f) := by
  have hee : e ⬝ᵥ (Q.hessian *ᵥ e) = 0 := by rw [dotProduct_hessian_self, he, mul_zero]
  have hff : f ⬝ᵥ (Q.hessian *ᵥ f) = 0 := by rw [dotProduct_hessian_self, hf, mul_zero]
  have hfe : f ⬝ᵥ (Q.hessian *ᵥ e) = 1 := by rw [dot_hessian_comm]; exact hef
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w, s⟩ h0
    rw [splitMap_apply] at h0
    have h1 : ((w : Fin n → R) + eMat e f *ᵥ s) ⬝ᵥ (Q.hessian *ᵥ e) = s 1 := by
      rw [eMat_mulVec, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, w.2.1, hee, hfe]
      simp
    have h2 : ((w : Fin n → R) + eMat e f *ᵥ s) ⬝ᵥ (Q.hessian *ᵥ f) = s 0 := by
      rw [eMat_mulVec, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, w.2.2, hef, hff]
      simp
    rw [h0, zero_dotProduct] at h1 h2
    have hs : s = 0 := by
      funext j
      fin_cases j
      · exact h2.symm
      · exact h1.symm
    subst hs
    have hw : (w : Fin n → R) = 0 := by simpa [eMat_mulVec] using h0
    refine Prod.ext (Subtype.ext ?_) rfl
    simpa using hw
  · intro v
    have hw : v - (v ⬝ᵥ (Q.hessian *ᵥ f)) • e - (v ⬝ᵥ (Q.hessian *ᵥ e)) • f ∈ orthSub Q e f := by
      refine ⟨?_, ?_⟩
      · rw [sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, hee, hfe]
        simp
      · rw [sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, hef, hff]
        simp
    refine ⟨(⟨_, hw⟩, ![v ⬝ᵥ (Q.hessian *ᵥ f), v ⬝ᵥ (Q.hessian *ᵥ e)]), ?_⟩
    rw [splitMap_apply, eMat_mulVec]
    simp

/-- **The complement has rank $n-2$:** $R^n\cong M\times R^2$. -/
theorem finrank_orthSub_add_two (Q : QuadForm R n) (e f : Fin n → R) (he : Q.eval e = 0) (hf : Q.eval f = 0)
    (hef : e ⬝ᵥ (Q.hessian *ᵥ f) = 1) : Module.finrank R (orthSub Q e f) + 2 = n := by
  have h := LinearEquiv.finrank_eq (LinearEquiv.ofBijective (splitMap Q e f) (splitMap_bijective Q e f he hf hef))
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  exact h

/-- **Splitting off a hyperbolic plane** (O'Meara 82:?, §42): if $Q$ on $R^{m+2}$ has $e,f$ with $Q(e)=Q(f)=0$,
$B(e,f)=1$ and the complement $M$ of $e,f$ has rank $m$ (automatic, `finrank_orthSub_add_two`), then $Q$ is
$\mathrm{GL}_{m+2}(R)$-equivalent to $Q'\perp\mathbb H$, $Q'=Q|_M$ in a basis of $M$. -/
@[kb "omeara1963" "§42, §82:? (splitting a unimodular hyperbolic plane off a lattice)"]
theorem exists_split_aux {m : ℕ} (Q : QuadForm R (m + 2)) (e f : Fin (m + 2) → R) (he : Q.eval e = 0)
    (hf : Q.eval f = 0) (hef : e ⬝ᵥ (Q.hessian *ᵥ f) = 1) (hrk : Module.finrank R (orthSub Q e f) = m) :
    ∃ Q' : QuadForm R m, DVR.IsGLEquiv Q (orthSum Q' (DVR.hyperbolic R)) := by
  have hg := splitMap_bijective Q e f he hf hef
  have hee : e ⬝ᵥ (Q.hessian *ᵥ e) = 0 := by rw [dotProduct_hessian_self, he, mul_zero]
  have hff : f ⬝ᵥ (Q.hessian *ᵥ f) = 0 := by rw [dotProduct_hessian_self, hf, mul_zero]
  have hfe : f ⬝ᵥ (Q.hessian *ᵥ e) = 1 := by rw [dot_hessian_comm]; exact hef
  let bM := Module.finBasisOfFinrankEq R (orthSub Q e f) hrk
  let bV : Module.Basis (Fin (m + 2)) R (Fin (m + 2) → R) :=
    ((bM.prod (Pi.basisFun R (Fin 2))).map (LinearEquiv.ofBijective (splitMap Q e f) hg)).reindex finSumFinEquiv
  let X : Matrix (Fin (m + 2)) (Fin m) R := Matrix.of fun l a => (bM a : Fin (m + 2) → R) l
  let U : Matrix (Fin (m + 2)) (Fin (m + 2)) R := Matrix.of fun i j => bV j i
  have hbl : ∀ (a : Fin m) l, bV (Fin.castAdd 2 a) l = X l a := by
    intro a l
    simp [bV, X, Module.Basis.reindex_apply, splitMap_apply]
  have hbr : ∀ (j : Fin 2) l, bV (Fin.natAdd m j) l = eMat e f l j := by
    intro j l
    simp [bV, eMat, Module.Basis.reindex_apply, splitMap_apply]
  have hU : ∀ x : Fin (m + 2) → R, U *ᵥ x =
      X *ᵥ (fun a => x (Fin.castAdd 2 a)) + eMat e f *ᵥ (fun j => x (Fin.natAdd m j)) := by
    intro x
    funext i
    simp only [U, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Pi.add_apply, hbl, hbr]
  have hdet : IsUnit U.det := by
    have : U = (Pi.basisFun R (Fin (m + 2))).toMatrix bV := by
      ext i j; simp [U, Module.Basis.toMatrix_apply]
    rw [this, ← Module.Basis.det_apply]
    exact Module.Basis.isUnit_det _ _
  refine ⟨Q.compMat X, U, hdet, fun x => ?_⟩
  set y : Fin m → R := fun a => x (Fin.castAdd 2 a) with hy_def
  set t : Fin 2 → R := fun j => x (Fin.natAdd m j) with ht_def
  have hy : (X *ᵥ y) ∈ orthSub Q e f := by
    have : X *ᵥ y = ((∑ a, y a • bM a : orthSub Q e f) : Fin (m + 2) → R) := by
      funext l
      simp [Matrix.mulVec, dotProduct, X, mul_comm]
    rw [this]
    exact (∑ a, y a • bM a : orthSub Q e f).2
  have hc : (X *ᵥ y) ⬝ᵥ (Q.hessian *ᵥ (t 0 • e + t 1 • f)) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      dotProduct_smul, hy.1, hy.2]
    simp
  have hq : Q.eval (t 0 • e + t 1 • f) = t 0 * t 1 := by
    rw [eval_add_hessian, eval_smul_sq, eval_smul_sq, he, hf, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, hef]
    simp
    ring
  have hh : (DVR.hyperbolic R).evalIn R (fun b => x (Fin.natAdd m b)) = t 0 * t 1 := by
    simp [QuadForm.evalIn, DVR.hyperbolic, QuadForm.ofUpper, Fin.sum_univ_two, t]
  rw [QuadForm.eval, evalIn_orthSum, hh, hU]
  change (Q.compMat X).eval y + t 0 * t 1 = _
  rw [eval_compMat, eMat_mulVec, eval_add_hessian, hc, hq]
  ring

end Split

section Induct

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The extension property passes to an orthogonal summand:** if $A\perp B$ has `MaxProp` then so does $A$ (use the
vector $(y,0)$). -/
@[kb "omeara1963" "§82H, p. 234 (a summand of a maximal lattice is maximal)"]
theorem maxProp_of_orthSum_left {m k : ℕ} (A : QuadForm 𝔬 m) (B : QuadForm 𝔬 k)
    (h : MaxProp v ((orthSum A B).map (algebraMap 𝔬 Fv))) : MaxProp v (A.map (algebraMap 𝔬 Fv)) := by
  intro y h1 h2
  set z : Fin (m + k) → Fv := Fin.append y 0 with hz
  have hzl : (fun a => z (Fin.castAdd k a)) = y := by funext a; simp [hz]
  have hzr : (fun b => z (Fin.natAdd m b)) = 0 := by funext b; simp [hz]
  have e1 : Valued.v (((orthSum A B).map (algebraMap 𝔬 Fv)).eval z) ≤ 1 := by
    rw [eval_map_eq_evalIn, evalIn_orthSum, hzl, hzr]
    have : B.evalIn Fv (0 : Fin k → Fv) = 0 := by simp [QuadForm.evalIn]
    rw [this, add_zero, ← eval_map_eq_evalIn]
    exact h1
  have e2 : (((orthSum A B).map (algebraMap 𝔬 Fv)).hessian *ᵥ z) ∈ std v := by
    refine mem_std_of_le_one v fun i => ?_
    have hb := bil_orthSum Fv A B (Pi.single i 1) z
    rw [hzl, hzr] at hb
    rw [hessian_map_eq, ← single_dotProduct_one (_ *ᵥ z) i, hb]
    simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero]
    refine v_dotProduct_le_one v ?_ ?_
    · refine mem_std_of_le_one v fun a => ?_
      by_cases ha : Fin.castAdd k a = i
      · simp [ha]
      · simp [ha]
    · rw [hessian_map_eq] at h2
      exact h2
  have := h z e1 e2
  exact mem_std_of_le_one v fun a => by
    simpa [hz] using v_le_one_of_mem_std v this (Fin.castAdd k a)

/-- **The induction** (O'Meara 91:2): a nondegenerate $Q$ over $\mathfrak o_\mathfrak p$ with `MaxProp` is
$\mathrm{GL}$-equivalent to $\mathbb H^k\perp N$ with $N$ nondegenerate, `MaxProp`, and anisotropic over $F_\mathfrak p$. -/
@[kb "omeara1963" "91:2, §82 (maximal lattice H^k ⊥ N on an anisotropic kernel; induction on the dimension)"]
theorem exists_hypSum_shape : ∀ (n : ℕ) (Q : QuadForm 𝔬 n), Q.Nondegenerate →
    MaxProp v (Q.map (algebraMap 𝔬 Fv)) →
    ∃ (k r : ℕ) (h : r + 2 * k = n) (N : QuadForm 𝔬 r), N.Nondegenerate ∧
      MaxProp v (N.map (algebraMap 𝔬 Fv)) ∧
      (∀ y : Fin r → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0) ∧
      DVR.IsGLEquiv Q (h ▸ hypSum N k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hQ MP
    by_cases hiso : ∃ y : Fin n → Fv, y ≠ 0 ∧ (Q.map (algebraMap 𝔬 Fv)).eval y = 0
    · obtain ⟨y, hy, h0⟩ := hiso
      obtain ⟨e, f, he, hf, hef⟩ := exists_hyperbolic_pair v Q MP hy h0
      have hrk := finrank_orthSub_add_two Q e f he hf hef
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨Module.finrank 𝔬 (orthSub Q e f), hrk.symm⟩
      obtain ⟨Q', hGL⟩ := exists_split_aux Q e f he hf hef (by omega)
      have hQ'' := hGL.nondegenerate hQ
      have hQ' := nondegenerate_of_orthSum_left hQ''
      have MP' := maxProp_of_orthSum_left v Q' _ (maxProp_of_isGLEquiv v hGL MP)
      obtain ⟨k, r, h, N, hN, hNM, hNa, hNE⟩ := ih m (by omega) Q' hQ' MP'
      subst h
      refine ⟨k + 1, r, by omega, N, hN, hNM, hNa, ?_⟩
      exact hGL.trans (isGLEquiv_orthSum_left _ hNE)
    · push Not at hiso
      exact ⟨0, n, by simp, Q, hQ, MP, fun y hy => by_contra fun hne => hiso y hne hy,
        DVR.IsGLEquiv.refl Q⟩

end Induct

section WittIdx

open QuadraticMap QuadraticForm

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem toQF_map_apply {n : ℕ} (Q : QuadForm 𝔬 n) (x : Fin n → Fv) :
    (Q.map (algebraMap 𝔬 Fv)).toQuadraticForm x = Q.evalIn Fv x := by
  rw [QuadForm.toQuadraticForm_apply, eval_map_eq_evalIn]

/-- **The Mathlib form of an orthogonal sum over $F_\mathfrak p$ is the `prod` of the forms.** -/
def orthSumIso {m k : ℕ} (A : QuadForm 𝔬 m) (B : QuadForm 𝔬 k) :
    (((orthSum A B).map (algebraMap 𝔬 Fv)).toQuadraticForm).IsometryEquiv
      (((A.map (algebraMap 𝔬 Fv)).toQuadraticForm).prod ((B.map (algebraMap 𝔬 Fv)).toQuadraticForm)) :=
  { finAddLinearEquiv Fv m k with
    map_app' := fun x => by
      simp only [QuadraticMap.prod_apply, toQF_map_apply, evalIn_orthSum]
      rfl }

/-- **The hyperbolic plane $x_0x_1$ over $F_\mathfrak p$ is Mathlib's `hyperbolicPlane`.** -/
def hypIso : (((DVR.hyperbolic 𝔬).map (algebraMap 𝔬 Fv)).toQuadraticForm).IsometryEquiv
    (QuadraticForm.hyperbolicPlane Fv) :=
  { LinearEquiv.finTwoArrow Fv Fv with
    map_app' := fun x => by
      rw [toQF_map_apply]
      simp [QuadForm.evalIn, DVR.hyperbolic, QuadForm.ofUpper, Fin.sum_univ_two] }

/-- Swapping the two factors of an orthogonal sum. -/
def prodSwap {K : Type*} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) :
    (Q₁.prod Q₂).IsometryEquiv (Q₂.prod Q₁) where
  toLinearEquiv := LinearEquiv.prodComm K V₁ V₂
  map_app' x := by simp [add_comm]

/-- $(\mathbb H^k\perp W)\perp\mathbb H\cong\mathbb H^{k+1}\perp W$. -/
def hypStep {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (k : ℕ) (W : QuadraticForm K V) :
    (((hyperbolicSpace K k).prod W).prod (hyperbolicPlane K)).IsometryEquiv
      ((hyperbolicSpace K (k + 1)).prod W) :=
  (Witt.prodAssoc _ _ _).trans (((QuadraticMap.IsometryEquiv.refl _).prod (prodSwap _ _)).trans
    ((Witt.prodAssoc _ _ _).symm.trans
      (((prodSwap _ _).trans (Witt.hyperbolicSpaceSucc k)).prod (QuadraticMap.IsometryEquiv.refl _))))

/-- **$\mathbb H^k\perp N$ over $\mathfrak o_\mathfrak p$ is $\mathbb H^k\perp N$ over $F_\mathfrak p$** (Mathlib's
`hyperbolicSpace`). -/
theorem equivalent_hypSum {r : ℕ} (N : QuadForm 𝔬 r) :
    ∀ k : ℕ, (((hypSum N k).map (algebraMap 𝔬 Fv)).toQuadraticForm).Equivalent
      ((hyperbolicSpace Fv k).prod ((N.map (algebraMap 𝔬 Fv)).toQuadraticForm))
  | 0 => ⟨(Witt.hyperbolicSpaceZeroProd _).symm⟩
  | k + 1 => by
    obtain ⟨ih⟩ := equivalent_hypSum N k
    exact ⟨(orthSumIso v (hypSum N k) (DVR.hyperbolic 𝔬)).trans
      ((ih.prod (hypIso v)).trans (hypStep k _))⟩

/-- **The anisotropic dimension of $\mathbb H^k\perp N$ is $r$** (Witt's uniqueness of the Witt index,
`eq_wittIndex`): if $Q_\mathfrak p\simeq\mathbb H^k\perp N$ with $N$ nondegenerate and anisotropic over $F_\mathfrak p$,
then $t_\mathfrak p=r$. -/
@[kb "omeara1963" "§42 (Witt decomposition; uniqueness of the anisotropic kernel)"]
theorem anisoDim_of_hypSum {k r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2 * k)) (hQ : Q₀.Nondegenerate)
    (N : QuadForm 𝔬 r)
    (hNa : ∀ y : Fin r → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hE : DVR.IsGLEquiv (NF.Qp v Q₀) (hypSum N k)) : anisoDim v Q₀ = r := by
  have hnd : ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).Nondegenerate := by
    rw [Tamagawa.map_Qp_eq]; exact nondegenerate_Qf v Q₀ hQ
  have hrad := radical_eq_bot_map v _ hnd
  have e1 := equivalent_map_of_isGLEquiv v hE
  have ha : ((N.map (algebraMap 𝔬 Fv)).toQuadraticForm).Anisotropic := fun x hx =>
    hNa x (by rwa [QuadForm.toQuadraticForm_apply] at hx)
  have hk := eq_wittIndex _ hrad ha (e1.trans (equivalent_hypSum v N k))
  unfold anisoDim
  have hQV : Tamagawa.Measure.LerayPadic.QV v Q₀ = (NF.Qp v Q₀).map (algebraMap 𝔬 Fv) := rfl
  rw [hQV, ← hk]
  omega

end WittIdx

section Main

variable {F : Type} [Field F] [NumberField F]

variable (F) in
/-- **The shape of a maximal lattice at any place** (O'Meara 91:2, §82; proved): `DyadicMaximalKernel F` holds. The
hypotheses $3\le n$, `ShimuraDetHyp`, $\mathfrak p\mid2$ and $[\widetilde\Lambda:\Lambda]\ne1$ are not used. -/
@[kb "omeara1963" "91:2, §82 (maximal lattice H^k ⊥ N on an anisotropic kernel at a dyadic place; proved)"]
theorem dyadicMaximalKernel : DyadicMaximalKernel F := by
  refine ⟨fun {n} _ Q₀ hQ hmax _ v _ _ => ?_⟩
  obtain ⟨k, r, h, N, hN, hNM, hNa, hE⟩ :=
    exists_hypSum_shape v n (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (maxProp_Qp v Q₀ hQ hmax)
  refine ⟨k, r, h, N, hN, hNM, hNa, hE, ?_⟩
  subst h
  exact anisoDim_of_hypSum v Q₀ hQ N hNa hE

/-- **(3.3) at the dyadic places with $\widetilde\Lambda_\mathfrak p\ne\Lambda_\mathfrak p$, from the kernel density alone**:
the shape input is proved (`dyadicMaximalKernel`), so `ShimuraDensityDyadicBad F` follows from `DyadicKernelDensity F`. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic places with Λ̃_p ≠ Λ_p; from the kernel density)"]
theorem shimuraDensityDyadicBad_of_kernelDensity (IB : DyadicKernelDensity F) : ShimuraDensityDyadicBad F :=
  shimuraDensityDyadicBad_of_split (dyadicMaximalKernel F) IB

/-- **All places of Shimura's (3.3) not proved directly, from the dyadic kernel density alone**: the only named input
left for `ShimuraMaximalDensityRest F` is `DyadicKernelDensity F` (Shimura's density of $\mathbb H^k\perp N$ with $N$ an
anisotropic maximal kernel at a dyadic place). -/
@[kb "hanke2005crelle" "(3.3), p. 8 (places p | 2e; from the dyadic kernel density)"]
theorem shimuraMaximalDensityRest_of_kernelDensity (IB : DyadicKernelDensity F) : ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_dyadicBad (shimuraDensityDyadicBad_of_kernelDensity IB)

end Main

end QuadFormsKB.Hanke2005
