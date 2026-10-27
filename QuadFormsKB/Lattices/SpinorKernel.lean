/-
# Symmetries and the spinor kernel $O'(V)$

**Layer:** the quadratic space $V = F^n$ with the form $Q$ = `Q : QuadForm F n` over a number field $F$
(`Lattices/Genus.lean`), its points over a field $K \supseteq F$ ($K = F$ or a completion $F_\mathfrak p$), and the
finite adelic orthogonal group $O(V)(\mathbb A_f)$ (`Lattices/ClassSet.lean`). The bilinear form is
$B(x, y) = Q(x + y) - Q(x) - Q(y) = x^{\mathsf T} H y$ with $H$ = `Q.hessian`, so $B(x, x) = 2Q(x)$.

**Defines**
* `symm Q K x` $= \tau_x \in O(V)(K)$, the **symmetry** (reflection) in an anisotropic $x \in K^n$,
  $\tau_x(y) = y - \frac{B(x, y)}{Q(x)}\,x$ (and $1$ when $Q(x) = 0$, so that `symm` is a total function);
* `spinorKernel Q K` $= O'(V)(K)$, the **spinor kernel**: the products $\tau_{x_1} \cdots \tau_{x_r}$ of an **even**
  number of symmetries with $Q(x_1) \cdots Q(x_r) \in K^{\times 2}$;
* `spinorKernelAf Q` $= O'(V_{\mathbb A_f}) = \{h \in O(V)(\mathbb A_f) : h_\mathfrak p \in O'(V_\mathfrak p)\ \forall \mathfrak p\}$;
* `IsIndefinite Q`: $V \otimes F_w$ is isotropic at some infinite place $w$ of $F$.

**Proves** that $\tau_x$ is an isometry of determinant $-1$ with $\tau_x^2 = 1$, $\tau_x(x) = -x$, and
$\sigma\tau_x\sigma^{-1} = \tau_{\sigma x}$ (`symm_conj`); that `spinorKernel` is a subgroup **normal** in $O(V)(K)$;
that $O'(V)(F)$ maps into $O'(V_\mathfrak p)$ (`orthMap_mem_spinorKernel`), so $O'(V) \subseteq O'(V_{\mathbb A_f})$.

*Definition choice.* O'Meara (§55, p. 137) defines $O'(V)$ as the kernel of the spinor norm $\theta$ on the rotation group
$O^+(V)$. Here $O'(V)$ is defined directly from symmetry factorizations, which needs no well-definedness of
$\theta$; `Lattices/SpinorNorm.lean` proves that it is the kernel of $\theta$ on $O^+(V)$ (the two definitions
agree). Sources: O'Meara 1963, §42E, pp. 96–97, and §43B, p. 102 (symmetries), §55, p. 137 (spinor norm, $O'(V)$),
§101D, p. 296 ($J'_V$, the adelic $O'$); Cassels 1978, Ch. 10, §3, Corollary 3 to Thm. 3.1, p. 178 (spinor norm $\theta$; Cassels writes $\Theta$ for its kernel, O'Meara's
$O'$, to avoid confusion with the commutator subgroup).
-/
import QuadFormsKB.Lattices.ClassSet
import QuadFormsKB.Tamagawa.Reflection

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

variable (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] [CharZero K]

/-! ### Symmetries -/

/-- The vector $w = Q(x)^{-1} H x$, so that $\tau_x = 1 - x w^{\mathsf T}$. -/
def symmVec (x : Fin n → K) : Fin n → K :=
  (Q.evalIn K x)⁻¹ • (Q.hessian.map (algebraMap F K) *ᵥ x)

theorem hessian_map_eq : (Q.map (algebraMap F K)).hessian = Q.hessian.map (algebraMap F K) :=
  QuadForm.hessian_map _ Q

theorem eval_map_eq (x : Fin n → K) : (Q.map (algebraMap F K)).eval x = Q.evalIn K x :=
  (evalIn_eq_eval_map Q x).symm

theorem symmVec_spec {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    (Q.map (algebraMap F K)).hessian *ᵥ x = (Q.map (algebraMap F K)).eval x • symmVec Q K x := by
  rw [hessian_map_eq, eval_map_eq, symmVec, smul_smul, mul_inv_cancel₀ hx, one_smul]

/-- $w \cdot x = 2$ for $w = Q(x)^{-1}Hx$ ($x^{\mathsf T}Hx = 2Q(x)$). -/
theorem symmVec_dotProduct_self {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) : symmVec Q K x ⬝ᵥ x = 2 := by
  have h := QuadForm.dotProduct_hessian_self (Q.map (algebraMap F K)) x
  rw [symmVec_spec Q K hx, dotProduct_smul, smul_eq_mul, dotProduct_comm] at h
  have : (Q.map (algebraMap F K)).eval x ≠ 0 := by rwa [eval_map_eq]
  exact mul_left_cancel₀ this (by rw [h]; ring)

theorem symmMat_det {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    (QuadForm.reflMat x (symmVec Q K x)).det = -1 :=
  QuadForm.det_reflMat _ (symmVec_spec Q K hx) (by rwa [eval_map_eq])

theorem symmMat_mul_self {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    QuadForm.reflMat x (symmVec Q K x) * QuadForm.reflMat x (symmVec Q K x) = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  simp only [Matrix.toLin'_apply, ← mulVec_mulVec, QuadForm.reflMat_mulVec, one_mulVec]
  rw [dotProduct_sub, dotProduct_smul, symmVec_dotProduct_self Q K hx, smul_eq_mul]
  rw [sub_sub, ← add_smul]
  ring_nf
  simp

open scoped Classical in
/-- The symmetry as an element of $\mathrm{GL}_n(K)$ ($1$ if $Q(x) = 0$). -/
def symmGL (x : Fin n → K) : GL (Fin n) K :=
  if hx : Q.evalIn K x ≠ 0 then
    Matrix.nonsingInvUnit (QuadForm.reflMat x (symmVec Q K x))
      (by rw [symmMat_det Q K hx]; exact isUnit_one.neg)
  else 1

theorem symmGL_val {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    (symmGL Q K x).val = QuadForm.reflMat x (symmVec Q K x) := by
  simp only [symmGL, ne_eq, hx, not_false_eq_true, dite_true]
  rfl

theorem symmGL_of_eq_zero {x : Fin n → K} (hx : Q.evalIn K x = 0) : symmGL Q K x = 1 := by
  simp [symmGL, hx]

theorem symmGL_mem (x : Fin n → K) : symmGL Q K x ∈ orthGroup Q K := by
  by_cases hx : Q.evalIn K x ≠ 0
  · refine mem_orthGroup_of_evalIn Q fun z => ?_
    rw [symmGL_val Q K hx, ← eval_map_eq, ← eval_map_eq]
    exact QuadForm.eval_reflMat _ (symmVec_spec Q K hx) z
  · rw [symmGL_of_eq_zero Q K (not_not.mp hx)]; exact (orthGroup Q K).one_mem

/-- **The symmetry** $\tau_x \in O(V)(K)$ in $x \in K^n$ with $Q(x) \ne 0$:
$\tau_x(y) = y - \frac{B(x,y)}{Q(x)}\,x$ (O'Meara 1963, §42E, pp. 96–97, who writes $\tau_y x = x - \frac{2B(x,y)}{Q(y)}\,y$ with $B(x,x) = Q(x)$; the same
map). For $Q(x) = 0$ it is $1$ by convention. -/
@[kb "omeara1963" "§42E, pp. 96–97 (symmetry τ_y)"]
def symm (x : Fin n → K) : orthGroup Q K := ⟨symmGL Q K x, symmGL_mem Q K x⟩

theorem symm_val {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    ((symm Q K x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = QuadForm.reflMat x (symmVec Q K x) :=
  symmGL_val Q K hx

theorem symm_mulVec {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) (y : Fin n → K) :
    ((symm Q K x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y =
      y - ((Q.evalIn K x)⁻¹ * (x ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ y))) • x := by
  rw [symm_val Q K hx, QuadForm.reflMat_mulVec, symmVec, smul_dotProduct, smul_eq_mul]
  congr 3
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, ← Matrix.transpose_map, ← hessian_map_eq,
    QuadForm.hessian_transpose, hessian_map_eq, dotProduct_comm]

theorem symm_det {x : Fin n → K} (hx : Q.evalIn K x ≠ 0) :
    ((symm Q K x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = -1 := by
  rw [symm_val Q K hx, symmMat_det Q K hx]

theorem symm_mul_self (x : Fin n → K) : symm Q K x * symm Q K x = 1 := by
  by_cases hx : Q.evalIn K x ≠ 0
  · ext1; ext1
    change ((symm Q K x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((symm Q K x : GL (Fin n) K)) = 1
    rw [symm_val Q K hx, symmMat_mul_self Q K hx]
  · ext1; simp [symm, symmGL_of_eq_zero Q K (not_not.mp hx)]

theorem symm_inv (x : Fin n → K) : (symm Q K x)⁻¹ = symm Q K x :=
  inv_eq_of_mul_eq_one_right (symm_mul_self Q K x)

/-- $\sigma \in O(V)(K)$ preserves $B$: $(\sigma x)^{\mathsf T} H (\sigma y) = x^{\mathsf T} H y$. -/
theorem bilin_orth (σ : orthGroup Q K) (x y : Fin n → K) :
    ((σ : GL (Fin n) K).val *ᵥ x) ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ ((σ : GL (Fin n) K).val *ᵥ y)) =
      x ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ y) := by
  conv_rhs => rw [← (mem_orthGroup Q).mp σ.2]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

/-- **Conjugating a symmetry:** $\sigma\tau_x\sigma^{-1} = \tau_{\sigma x}$ for $\sigma \in O(V)(K)$
(O'Meara 1963, §42E, p. 97). -/
@[kb "omeara1963" "§42E, p. 97 (στ_xσ⁻¹ = τ_{σ x})"]
theorem symm_conj (σ : orthGroup Q K) (x : Fin n → K) :
    σ * symm Q K x * σ⁻¹ = symm Q K ((σ : GL (Fin n) K).val *ᵥ x) := by
  have hQσ : Q.evalIn K ((σ : GL (Fin n) K).val *ᵥ x) = Q.evalIn K x :=
    evalIn_mulVec_of_mem Q σ.2 x
  by_cases hx : Q.evalIn K x ≠ 0
  · have hx' : Q.evalIn K ((σ : GL (Fin n) K).val *ᵥ x) ≠ 0 := by rwa [hQσ]
    ext1; ext1
    refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
    simp only [Matrix.toLin'_apply]
    change ((σ : GL (Fin n) K).val * (symm Q K x : GL (Fin n) K).val * (σ⁻¹ : orthGroup Q K).1.val) *ᵥ y = _
    rw [← mulVec_mulVec, ← mulVec_mulVec, symm_mulVec Q K hx, symm_mulVec Q K hx', mulVec_sub,
      mulVec_smul, hQσ]
    have e : (σ : GL (Fin n) K).val *ᵥ ((σ⁻¹ : orthGroup Q K).1.val *ᵥ y) = y := by
      rw [mulVec_mulVec]
      change ((σ * σ⁻¹ : orthGroup Q K) : GL (Fin n) K).val *ᵥ y = y
      simp
    rw [e]
    congr 3
    conv_rhs => rw [← e, bilin_orth Q K σ]
  · have hx0 : Q.evalIn K x = 0 := not_not.mp hx
    have hx0' : Q.evalIn K ((σ : GL (Fin n) K).val *ᵥ x) = 0 := by rw [hQσ, hx0]
    have h1 : symm Q K x = 1 := by ext1; simp [symm, symmGL_of_eq_zero Q K hx0]
    have h2 : symm Q K ((σ : GL (Fin n) K).val *ᵥ x) = 1 := by
      ext1; simp [symm, symmGL_of_eq_zero Q K hx0']
    rw [h1, h2, mul_one, mul_inv_cancel]

/-! ### The spinor kernel -/

/-- The product $\tau_{x_1}\cdots\tau_{x_r}$ of the symmetries in a list of vectors. -/
def symmProd (xs : List (Fin n → K)) : orthGroup Q K := (xs.map (symm Q K)).prod

/-- The product $Q(x_1)\cdots Q(x_r)$ of the values on a list of vectors. -/
def valProd (xs : List (Fin n → K)) : K := (xs.map (Q.evalIn K)).prod

theorem symmProd_append (xs ys : List (Fin n → K)) :
    symmProd Q K (xs ++ ys) = symmProd Q K xs * symmProd Q K ys := by
  simp [symmProd]

theorem valProd_append (xs ys : List (Fin n → K)) :
    valProd Q K (xs ++ ys) = valProd Q K xs * valProd Q K ys := by
  simp [valProd]

theorem symmProd_reverse (xs : List (Fin n → K)) : symmProd Q K xs.reverse = (symmProd Q K xs)⁻¹ := by
  induction xs with
  | nil => simp [symmProd]
  | cons x xs ih =>
    rw [List.reverse_cons, symmProd_append, ih]
    simp [symmProd, symm_inv]

theorem valProd_reverse (xs : List (Fin n → K)) : valProd Q K xs.reverse = valProd Q K xs := by
  simp [valProd, List.prod_reverse]

/-- A **spinor word**: a list of anisotropic vectors of even length whose values multiply to a square. -/
def IsSpinorWord (xs : List (Fin n → K)) : Prop :=
  (∀ x ∈ xs, Q.evalIn K x ≠ 0) ∧ Even xs.length ∧ IsSquare (valProd Q K xs)

/-- **The spinor kernel** $O'(V)(K)$: the products $\tau_{x_1}\cdots\tau_{x_r}$ of an even number $r$ of symmetries in
anisotropic vectors with $Q(x_1)\cdots Q(x_r) \in K^{\times 2}$. Equivalently (`Lattices/SpinorNorm.lean`) the kernel
of the spinor norm $\theta : O^+(V)(K) \to K^\times/K^{\times 2}$ (O'Meara 1963, §55, p. 137). -/
@[kb "omeara1963" "§55, p. 137 (O'(V))"]
def spinorKernel : Subgroup (orthGroup Q K) where
  carrier := {g | ∃ xs, IsSpinorWord Q K xs ∧ symmProd Q K xs = g}
  mul_mem' := by
    rintro _ _ ⟨xs, ⟨hxa, hxe, hxs⟩, rfl⟩ ⟨ys, ⟨hya, hye, hys⟩, rfl⟩
    refine ⟨xs ++ ys, ⟨fun z hz => ?_, ?_, ?_⟩, symmProd_append Q K xs ys⟩
    · rcases List.mem_append.mp hz with h | h
      exacts [hxa z h, hya z h]
    · rw [List.length_append]; exact hxe.add hye
    · rw [valProd_append]; exact hxs.mul hys
  one_mem' := ⟨[], ⟨by simp, by simp, by simp [valProd]⟩, by simp [symmProd]⟩
  inv_mem' := by
    rintro _ ⟨xs, ⟨hxa, hxe, hxs⟩, rfl⟩
    refine ⟨xs.reverse, ⟨fun z hz => hxa z (List.mem_reverse.mp hz), by rwa [List.length_reverse], ?_⟩,
      symmProd_reverse Q K xs⟩
    rwa [valProd_reverse]

theorem mem_spinorKernel {g : orthGroup Q K} :
    g ∈ spinorKernel Q K ↔ ∃ xs, IsSpinorWord Q K xs ∧ symmProd Q K xs = g := Iff.rfl

theorem symmProd_conj (σ : orthGroup Q K) (xs : List (Fin n → K)) :
    σ * symmProd Q K xs * σ⁻¹ = symmProd Q K (xs.map ((σ : GL (Fin n) K).val *ᵥ ·)) := by
  induction xs with
  | nil => simp [symmProd]
  | cons x xs ih =>
    have : σ * symmProd Q K (x :: xs) * σ⁻¹ = (σ * symm Q K x * σ⁻¹) * (σ * symmProd Q K xs * σ⁻¹) := by
      simp [symmProd, mul_assoc]
    rw [this, ih, symm_conj]
    simp [symmProd]

theorem valProd_map_orth (σ : orthGroup Q K) (xs : List (Fin n → K)) :
    valProd Q K (xs.map ((σ : GL (Fin n) K).val *ᵥ ·)) = valProd Q K xs := by
  simp only [valProd, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => evalIn_mulVec_of_mem Q σ.2 x

/-- **$O'(V)(K)$ is normal in $O(V)(K)$** ($\sigma\tau_x\sigma^{-1} = \tau_{\sigma x}$ and $Q(\sigma x) = Q(x)$). -/
@[kb "omeara1963" "§55, p. 138 (normal subgroups of O_n)"]
theorem spinorKernel_normal : (spinorKernel Q K).Normal where
  conj_mem := by
    rintro _ ⟨xs, ⟨hxa, hxe, hxs⟩, rfl⟩ σ
    refine ⟨xs.map ((σ : GL (Fin n) K).val *ᵥ ·), ⟨?_, by rwa [List.length_map], ?_⟩,
      (symmProd_conj Q K σ xs).symm⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      rw [evalIn_mulVec_of_mem Q σ.2 x]; exact hxa x hx
    · rwa [valProd_map_orth]

/-! ### Base change -/

section BaseChange

variable {K} (L : Type*) [Field L] [Algebra F L] [CharZero L] [Algebra K L] [IsScalarTower F K L]

theorem evalIn_map_tower (x : Fin n → K) :
    Q.evalIn L (fun i => algebraMap K L (x i)) = algebraMap K L (Q.evalIn K x) := by
  simp only [QuadForm.evalIn, map_sum, map_mul, apply_ite, map_zero, IsScalarTower.algebraMap_apply F K L]

end BaseChange

/-- The image of a rational symmetry: $\tau_x \mapsto \tau_x$ in $O(V)(F_\mathfrak p)$. -/
@[kb "omeara1963" "§101B, p. 289 (localization of an isometry; (τ_u)_{𝔭} = τ_{u_{𝔭}})"]
theorem orthMap_symm (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → F) :
    orthMap Q (v.adicCompletion F) (symm Q F x) = symm Q (v.adicCompletion F) (fun i => algebraMap F _ (x i)) := by
  set K := v.adicCompletion F
  have hval : Q.evalIn K (fun i => algebraMap F K (x i)) = algebraMap F K (Q.evalIn F x) := by
    simpa using evalIn_map_tower Q K (K := F) x
  by_cases hx : Q.evalIn F x ≠ 0
  · have hx' : Q.evalIn K (fun i => algebraMap F K (x i)) ≠ 0 := by
      rw [hval]; exact (map_ne_zero _).mpr hx
    ext1; ext1
    change ((symm Q F x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map (algebraMap F K) = _
    rw [symm_val Q F hx, symm_val Q K hx']
    ext i j
    simp only [QuadForm.reflMat, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply,
      symmVec, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, hval]
    split_ifs <;> simp [map_sum, map_mul, map_inv₀, map_sub]
  · have hx0 : Q.evalIn F x = 0 := not_not.mp hx
    have hx0' : Q.evalIn K (fun i => algebraMap F K (x i)) = 0 := by rw [hval, hx0, map_zero]
    have h1 : symm Q F x = 1 := by ext1; simp [symm, symmGL_of_eq_zero Q F hx0]
    have h2 : symm Q K (fun i => algebraMap F K (x i)) = 1 := by
      ext1; simp [symm, symmGL_of_eq_zero Q K hx0']
    rw [h1, h2, map_one]

/-- **$O'(V)(F) \to O'(V_\mathfrak p)$:** a rational spinor word stays a spinor word over $F_\mathfrak p$. -/
theorem orthMap_mem_spinorKernel (v : HeightOneSpectrum (𝓞 F)) {γ : orthGroup Q F}
    (hγ : γ ∈ spinorKernel Q F) : orthMap Q (v.adicCompletion F) γ ∈ spinorKernel Q (v.adicCompletion F) := by
  set K := v.adicCompletion F
  obtain ⟨xs, ⟨hxa, hxe, ⟨c, hc⟩⟩, rfl⟩ := hγ
  have hval : ∀ x : Fin n → F,
      Q.evalIn K (fun i => algebraMap F K (x i)) = algebraMap F K (Q.evalIn F x) := fun x => by
    simpa using evalIn_map_tower Q K (K := F) x
  refine ⟨xs.map fun x i => algebraMap F K (x i), ⟨?_, by rwa [List.length_map], ⟨algebraMap F K c, ?_⟩⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    rw [hval]; exact (map_ne_zero _).mpr (hxa x hx)
  · rw [← map_mul, ← hc, valProd, valProd, List.map_map, map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => hval x
  · rw [symmProd, symmProd, map_list_prod, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => (orthMap_symm Q v x).symm

/-! ### The adelic spinor kernel -/

/-- **The adelic spinor kernel** $O'(V_{\mathbb A_f}) = \{h \in O(V)(\mathbb A_f) : h_\mathfrak p \in O'(V_\mathfrak p)$ for
every finite prime $\mathfrak p\}$ (cf. O'Meara 1963, §101D, p. 296, whose $J'_V$ also has components at the infinite
spots and requires $\|\Sigma_\mathfrak p\|_\mathfrak p = 1$ for almost all $\mathfrak p$). -/
@[kb "omeara1963" "§101D, p. 296 (J'_V)"]
def spinorKernelAf : Subgroup (OAf Q) where
  carrier := {h | ∀ v, h v ∈ spinorKernel Q (v.adicCompletion F)}
  mul_mem' ha hb v := (spinorKernel Q _).mul_mem (ha v) (hb v)
  one_mem' _ := (spinorKernel Q _).one_mem
  inv_mem' ha v := (spinorKernel Q _).inv_mem (ha v)

theorem mem_spinorKernelAf {h : OAf Q} :
    h ∈ spinorKernelAf Q ↔ ∀ v, h v ∈ spinorKernel Q (v.adicCompletion F) := Iff.rfl

/-- $O'(V) \subseteq O'(V_{\mathbb A_f})$ (diagonally). -/
theorem diagF_mem_spinorKernelAf {γ : orthGroup Q F} (hγ : γ ∈ spinorKernel Q F) :
    diagF Q γ ∈ spinorKernelAf Q := fun v => orthMap_mem_spinorKernel Q v hγ

/-- **$O'(V_{\mathbb A_f})$ is normal in $O(V)(\mathbb A_f)$** (componentwise `spinorKernel_normal`). -/
theorem spinorKernelAf_normal : (spinorKernelAf Q).Normal where
  conj_mem _ hh g v := (spinorKernel_normal Q _).conj_mem _ (hh v) (g v)

/-! ### Indefinite forms -/

/-- **$Q$ is indefinite:** $V \otimes_F F_w$ is isotropic for some infinite place $w$ of $F$ (for $F = \mathbb Q$:
$Q$ is indefinite over $\mathbb R$). This is the hypothesis of strong approximation (O'Meara 1963, 104:2–104:3,
p. 311); for $n \ge 3$ it holds automatically when $F$ has a complex place. -/
@[kb "omeara1963" "§104, 104:2, p. 311 (indefinite set of spots)"]
def IsIndefinite : Prop := ∃ w : InfinitePlace F, Q.IsotropicIn w.Completion

end QuadFormsKB.Lattices
