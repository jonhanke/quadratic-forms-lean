/-
# Cassels, Chapter 8, Lemmas 2.1, 3.1–3.3: bases of $\mathbb Z_p^n$, maximal values, integral symmetries

**Setting.** $\mathbb Z_p^n$ = `Fin n → ℤ_[p]`, a lattice in $\mathbb Q_p^n$; vectors $c_0, \dots, c_{J-1} \in
\mathbb Z_p^n$ (Cassels: $c_1, \dots, c_J$) and their $n \times J$ coordinate matrix `colsMatP c` (column $j$ is $c_j$).
"$c_0, \dots, c_{J-1}$ extend to a basis" means: they are the first $J$ columns of some $T \in \mathrm{GL}_n(\mathbb Z_p)$.

**Proves** Lemma 2.1 (p. 112) as a `List.TFAE` (`tfae_extends_basis_padic`): (i) the $c_j$ extend to a basis of
$\mathbb Z_p^n$; (ii) some $J \times J$ minor of the matrix $(c_0 \cdots c_{J-1})$ is a $p$-adic unit; (iii) if
$\sum_j v_jc_j \in \mathbb Z_p^n$ with $v_j \in \mathbb Q_p$ then all $v_j \in \mathbb Z_p$.

Lemma 3.1 (p. 113, `exists_equiv_sup_first`): a form $f(\vec x) = \vec x^{t}F\vec x$, $F \in M_n(\mathbb Q_p)$ (`qf F`), is
$\mathbb Z_p$-equivalent to a form $g$ with $\lvert g(e_0)\rvert_p = \sup_{\vec a \in \mathbb Z_p^n}\lvert g(\vec a)\rvert_p$. Proof
as Cassels': the supremum is attained since the nonzero values of $\lvert\cdot\rvert_p$ are powers of $p$ and
bounded; a maximizing $\vec c$ with $f(\vec c) \ne 0$ is primitive (else $\vec c = p\vec b$ and
$\lvert f(\vec b)\rvert = p^{2}\lvert f(\vec c)\rvert$), so by Lemma 2.1 it is the first vector of a basis.

Lemma 3.2 (p. 114, `isIntAut_tau`): if $\lvert f(\vec b)\rvert$ is the supremum (and $\ne 0$), the symmetry
$\tau_b$ (`tau`) is an integral automorph (`IsIntAut`: preserves $f$, and it and its inverse map $\mathbb Z_p^n$ into
itself). Lemma 3.3 (p. 114, $p \ne 2$, `exists_intAut_apply_eq`): vectors $\vec a_1, \vec a_2$ with
$f(\vec a_1) = f(\vec a_2)$ of maximal value are moved to one another by an integral automorph ($\tau_{a_1 - a_2}$
or $\tau_{a_2}\tau_{a_1 + a_2}$, as in Cassels). In this part vectors live in $\mathbb Q_p^n$ with the predicate
`IsIntVec` ($\lVert x_i\rVert \le 1$); `bil F x y` $= f(\vec x + \vec y) - f(\vec x) - f(\vec y)$ is Cassels' $2f(\vec x, \vec y)$.

**Proof notes.** Cassels deduces the lemma from Chapter 7, Theorem 3.1 ($\mathbb Z_p$ is a principal ideal domain);
here it is proved directly, as for $\mathbb Z$ in `Siegel.tfae_extends_basis` (`Ch9Sec2.lean`), using that
$\mathbb Z_p$ is local: (i) $\Rightarrow$ (ii) by the Cauchy–Binet formula (a sum of non-units is a non-unit);
(ii) $\Rightarrow$ (iii) by inverting the unit minor; (iii) $\Rightarrow$ (i) by adding one vector at a time: the new
vector, in the coordinates of the basis built so far, has a unit coordinate at or after position $J'$ (otherwise
(iii) fails with a denominator $p$), which a transposition moves to position $J'$. Cassels' hypothesis that the
$c_j$ are linearly independent is not needed (each of (i)–(iii) implies it).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- Rectangular Cauchy–Binet (a copy of `Lattices.det_mul_rect`, `Ch11Sec6Subst.lean`, to keep the imports small). -/
private theorem det_mul_rect {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ p : Fin m → Fin k, (∏ i, A i (p i)) * (B.submatrix p id).det := by
  classical
  have key : ∀ M : Matrix (Fin m) (Fin m) R,
      M.det = ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) • ∏ i, M i (σ i) := by
    intro M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [key (A * B)]
  have h1 : ∀ σ : Equiv.Perm (Fin m), ∏ i, (A * B) i (σ i) =
      ∑ p : Fin m → Fin k, (∏ i, A i (p i)) * ∏ i, B (p i) (σ i) := by
    intro σ
    simp_rw [Matrix.mul_apply]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]
  simp_rw [h1, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [key (B.submatrix p id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [zsmul_eq_mul, Matrix.submatrix_apply, id]
  ring

/-- The $n \times J$ matrix with columns $c_0, \dots, c_{J-1}$. -/
def colsMatP {J : ℕ} (c : Fin J → Fin n → ℤ_[p]) : Matrix (Fin n) (Fin J) ℤ_[p] := Matrix.of fun i j => c j i

/-- Lemma 2.1, (i) $\Rightarrow$ (ii). -/
private theorem one_two {J : ℕ} (hJ : J ≤ n) (c : Fin J → Fin n → ℤ_[p])
    (h : ∃ T : GL (Fin n) ℤ_[p], ∀ j, T.val *ᵥ Pi.single (Fin.castLE hJ j) 1 = c j) :
    ∃ s : Fin J ↪ Fin n, IsUnit ((colsMatP c).submatrix s id).det := by
  obtain ⟨T, hT⟩ := h
  have hcol : ∀ j k, T.val k (Fin.castLE hJ j) = c j k := fun j k => by
    rw [← hT j]; simp
  set A : Matrix (Fin J) (Fin n) ℤ_[p] := Matrix.of fun j k => (T⁻¹).val (Fin.castLE hJ j) k with hA
  have hAB : A * colsMatP c = 1 := by
    ext j j'
    have := congrFun (congrFun (Units.inv_mul T) (Fin.castLE hJ j)) (Fin.castLE hJ j')
    simp only [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, hA, colsMatP, Matrix.of_apply, ← hcol, Matrix.one_apply]
    rw [this]
    simp [Matrix.one_apply, Fin.ext_iff]
  have hdet := det_mul_rect A (colsMatP c)
  rw [hAB, Matrix.det_one] at hdet
  by_contra hne'
  have hne : ∀ s : Fin J ↪ Fin n, ¬ IsUnit ((colsMatP c).submatrix s id).det := fun s hs => hne' ⟨s, hs⟩
  have hmem : (1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [hdet]
    refine Ideal.sum_mem _ fun q _ => ?_
    by_cases hq : Function.Injective q
    · exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne ⟨q, hq⟩))
    · obtain ⟨i, i', hii, hne'⟩ : ∃ i i', q i = q i' ∧ i ≠ i' := by
        simpa [Function.Injective] using hq
      rw [Matrix.det_zero_of_row_eq hne' (by ext l; simp [hii])]
      simp
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem isUnit_one

/-- Lemma 2.1, (ii) $\Rightarrow$ (iii). -/
private theorem two_three {J : ℕ} (c : Fin J → Fin n → ℤ_[p])
    (h : ∃ s : Fin J ↪ Fin n, IsUnit ((colsMatP c).submatrix s id).det) :
    ∀ v : Fin J → ℚ_[p], (∃ y : Fin n → ℤ_[p], ∑ j, v j • (fun i => (c j i : ℚ_[p])) = fun i => (y i : ℚ_[p])) →
      ∀ j, ∃ z : ℤ_[p], v j = z := by
  obtain ⟨s, hs⟩ := h
  rintro v ⟨y, hy⟩ j
  set M := (colsMatP c).submatrix s id with hM
  set φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom with hφ
  have hMv : M.map φ *ᵥ v = fun k => (y (s k) : ℚ_[p]) := by
    funext k
    have := congrFun hy (s k)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.map_apply, Matrix.submatrix_apply, colsMatP,
      Matrix.of_apply, id]
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hφ, mul_comm]
  have hinv : (M⁻¹).map φ * M.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hs, Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨(M⁻¹ *ᵥ fun k => y (s k)) j, ?_⟩
  have hv : v = (M⁻¹).map φ *ᵥ (fun k => (y (s k) : ℚ_[p])) := by
    rw [← hMv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [hv]
  simp [Matrix.mulVec, dotProduct, hφ]

/-- Lemma 2.1, (iii) $\Rightarrow$ (i). -/
private theorem three_one {J : ℕ} (hJ : J ≤ n) (c : Fin J → Fin n → ℤ_[p])
    (h : ∀ v : Fin J → ℚ_[p], (∃ y : Fin n → ℤ_[p], ∑ j, v j • (fun i => (c j i : ℚ_[p])) =
      fun i => (y i : ℚ_[p])) → ∀ j, ∃ z : ℤ_[p], v j = z) :
    ∃ T : GL (Fin n) ℤ_[p], ∀ j, T.val *ᵥ Pi.single (Fin.castLE hJ j) 1 = c j := by
  classical
  have key : ∀ J' : ℕ, J' ≤ J → ∃ T : GL (Fin n) ℤ_[p], ∀ j : Fin J, j.val < J' →
      T.val *ᵥ Pi.single (Fin.castLE hJ j) 1 = c j := by
    intro J'
    induction J' with
    | zero => intro _; exact ⟨1, fun j hj => absurd hj (by omega)⟩
    | succ J' ih =>
      intro hJ'
      obtain ⟨T, hT⟩ := ih (by omega)
      set j' : Fin J := ⟨J', by omega⟩ with hj'
      set i' : Fin n := Fin.castLE hJ j' with hi'
      have hi'val : i'.val = J' := rfl
      set e' : Fin n → ℤ_[p] := (T⁻¹).val *ᵥ c j' with he'
      have hTe : T.val *ᵥ e' = c j' := by
        rw [he', Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      -- some coordinate of `e'` at or after `i'` is a unit
      have hunit : ∃ i₀ : Fin n, i' ≤ i₀ ∧ IsUnit (e' i₀) := by
        by_contra hno
        have hpe : ∀ k : Fin n, i' ≤ k → (p : ℤ_[p]) ∣ e' k := by
          intro k hk
          have : ¬ IsUnit (e' k) := fun hu => hno ⟨k, hk, hu⟩
          rw [← PadicInt.norm_lt_one_iff_dvd, ← PadicInt.mem_nonunits]
          exact this
        choose w hw using hpe
        set W : Fin n → ℤ_[p] := fun k => if hk : i' ≤ k then w k hk else 0 with hW
        set a : Fin J → ℤ_[p] := fun j => if j.val < J' then e' (Fin.castLE hJ j) else 0 with ha
        have hcols : ∀ j : Fin J, j.val < J' → ∀ i, T.val i (Fin.castLE hJ j) = c j i := by
          intro j hj i
          rw [← hT j hj]; simp
        have hint : ∀ i : Fin n, (p : ℤ_[p]) * (∑ k, T.val i k * W k) = c j' i - ∑ j, a j * c j i := by
          intro i
          have h1 : c j' i = ∑ k, T.val i k * e' k := by rw [← hTe]; rfl
          have h2 : ∑ j, a j * c j i = ∑ k : Fin n, if k.val < J' then T.val i k * e' k else 0 := by
            have h3 : ∀ j : Fin J, a j * c j i =
                if j.val < J' then T.val i (Fin.castLE hJ j) * e' (Fin.castLE hJ j) else 0 := by
              intro j
              by_cases hj : j.val < J'
              · simp only [ha, hj, ite_true]
                rw [hcols j hj i]; ring
              · simp [ha, hj]
            simp_rw [h3]
            refine Finset.sum_of_injOn (Fin.castLE hJ) (fun x _ y _ h => Fin.castLE_injective hJ h)
              (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun k _ hk => ?_) (fun j _ => ?_)
            · have : ¬ k.val < J' := by
                by_contra hlt
                exact hk ⟨⟨k.val, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), Fin.ext rfl⟩
              simp [this]
            · simp
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : k.val < J'
          · have : ¬ i' ≤ k := by rw [Fin.le_def, hi'val]; omega
            simp only [hW, hk, this, ite_true, dite_false]
            ring
          · have hik : i' ≤ k := by rw [Fin.le_def, hi'val]; omega
            simp only [hW, hk, hik, ite_false, dite_true]
            rw [hw k hik]
            ring
        have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
        have hv := h (fun j => (((if j = j' then 1 else 0 : ℚ_[p])) - (a j : ℚ_[p])) / p)
          ⟨fun i => ∑ k, T.val i k * W k, ?_⟩ j'
        · obtain ⟨z, hz⟩ := hv
          have ha0 : a j' = 0 := by simp [ha, hj']
          rw [ite_eq_left_iff.2 (fun h => absurd rfl h), ha0] at hz
          have h1 : (p : ℚ_[p]) * z = 1 := by
            rw [← hz]; field_simp; simp
          have hz1 : ‖(z : ℚ_[p])‖ ≤ 1 := z.2
          have h3 := congrArg norm h1
          rw [norm_mul, norm_one] at h3
          have := Padic.norm_p_lt_one (p := p)
          nlinarith [norm_nonneg (p : ℚ_[p]), norm_nonneg (z : ℚ_[p])]
        · funext i
          have hq := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) (hint i)
          simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
          have h4 : ∀ j : Fin J, ((((if j = j' then 1 else 0 : ℚ_[p])) - (a j : ℚ_[p])) / p) * (c j i : ℚ_[p]) =
              ((if j = j' then (c j' i : ℚ_[p]) else 0) - (a j : ℚ_[p]) * c j i) / p := by
            intro j
            by_cases hjj : j = j'
            · subst hjj; simp only [ite_true]; ring
            · simp only [hjj, ite_false]; ring
          simp_rw [h4]
          rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ j' (fun _ => (c j' i : ℚ_[p]))]
          simp only [Finset.mem_univ, ite_true]
          have hs : ∀ {m : ℕ} (f : Fin m → ℤ_[p]), ((∑ x, f x : ℤ_[p]) : ℚ_[p]) = ∑ x, (f x : ℚ_[p]) :=
            fun f => map_sum PadicInt.Coe.ringHom f _
          rw [PadicInt.coe_mul, PadicInt.coe_sub, hs, hs] at hq
          rw [hs]
          simp only [PadicInt.coe_mul, PadicInt.coe_natCast] at hq ⊢
          field_simp
          linear_combination hq.symm
      obtain ⟨i₀, hi₀, hu⟩ := hunit
      -- move the unit coordinate to position `i'` and complete
      set σ : Equiv.Perm (Fin n) := Equiv.swap i' i₀ with hσ
      set T₁ : Matrix (Fin n) (Fin n) ℤ_[p] := T.val.submatrix id σ with hT₁
      set e'' : Fin n → ℤ_[p] := fun k => e' (σ k) with he''
      set T₂ : Matrix (Fin n) (Fin n) ℤ_[p] := (1 : Matrix (Fin n) (Fin n) ℤ_[p]).updateCol i' e'' with hT₂
      have hT₁e : T₁ *ᵥ e'' = c j' := by
        rw [← hTe]
        funext k
        simp only [Matrix.mulVec, dotProduct, hT₁, he'', Matrix.submatrix_apply, id]
        exact Equiv.sum_comp σ (fun l => T.val k l * e' l)
      have hdet₁ : IsUnit T₁.det := by
        rw [hT₁, Matrix.det_permute']
        refine IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det _).1 T.isUnit)
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      have hT₂col : ∀ k, T₂ *ᵥ Pi.single k 1 = if k = i' then e'' else Pi.single k 1 := by
        intro k
        rw [Matrix.mulVec_single_one]
        funext l
        by_cases hk : k = i'
        · subst hk; simp [hT₂, Matrix.col]
        · simp [hT₂, Matrix.col, hk, Matrix.one_apply, Pi.single_apply, eq_comm]
      have hdet₂ : IsUnit T₂.det := by
        have h := Matrix.det_updateCol_sum (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i' e''
        have he : (fun k => ∑ i, e'' i • (1 : Matrix (Fin n) (Fin n) ℤ_[p]) k i) = e'' := by
          funext k; simp [Matrix.one_apply]
        rw [he, Matrix.det_one, smul_eq_mul, mul_one] at h
        rw [hT₂, h]
        simpa [he'', hσ] using hu
      have hU : IsUnit (T₁ * T₂) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [Matrix.det_mul]; exact hdet₁.mul hdet₂)
      refine ⟨hU.unit, fun j hj => ?_⟩
      rw [IsUnit.unit_spec, ← Matrix.mulVec_mulVec, hT₂col]
      by_cases hjl : j.val < J'
      · have hne : Fin.castLE hJ j ≠ i' := by
          intro h; have := congrArg Fin.val h; simp [hi'val] at this; omega
        have hne₀ : Fin.castLE hJ j ≠ i₀ := by
          intro h; have := congrArg Fin.val h; rw [Fin.le_def, hi'val] at hi₀; simp at this; omega
        rw [ite_eq_right_iff.2 (fun h => absurd h hne), ← hT j hjl]
        funext l
        simp [hT₁, Matrix.mulVec, dotProduct, Pi.single_apply, hσ, Equiv.swap_apply_of_ne_of_ne hne hne₀]
      · have hjj : j = j' := Fin.ext (by simp [hj']; omega)
        subst hjj
        rw [ite_eq_left_iff.2 (fun h => absurd rfl h), hT₁e]
  obtain ⟨T, hT⟩ := key J le_rfl
  exact ⟨T, fun j => hT j j.2⟩

/-- **Cassels, Ch. 8, Lemma 2.1**: *let $c_1, \dots, c_J$ be elements of $\mathbb Z_p^n$; then the following are
equivalent: (i) there exist $c_{J+1}, \dots, c_n$ such that $c_1, \dots, c_n$ is a basis of $\mathbb Z_p^n$; (ii) the
$n \times J$ matrix $c_1 \cdots c_J$ contains a $J \times J$ minor whose determinant is a $p$-adic unit; (iii) if
$\vec a = v_1c_1 + \cdots + v_Jc_J \in \mathbb Z_p^n$ for some $v_1, \dots, v_J \in \mathbb Q_p$ then necessarily
$v_1, \dots, v_J \in \mathbb Z_p$.* In (i) the basis is the columns of $T \in \mathrm{GL}_n(\mathbb Z_p)$ and the given
vectors are its first $J$ columns; in (ii) the minor takes the rows $s(0), \dots, s(J-1)$ for an injection $s$;
indices are $0, \dots, J-1$. -/
@[kb "cassels1978" "Ch. 8, Lemma 2.1, p. 112"]
theorem tfae_extends_basis_padic {J : ℕ} (hJ : J ≤ n) (c : Fin J → Fin n → ℤ_[p]) :
    List.TFAE
      [∃ T : GL (Fin n) ℤ_[p], ∀ j, T.val *ᵥ Pi.single (Fin.castLE hJ j) 1 = c j,
       ∃ s : Fin J ↪ Fin n, IsUnit ((colsMatP c).submatrix s id).det,
       ∀ v : Fin J → ℚ_[p], (∃ y : Fin n → ℤ_[p], ∑ j, v j • (fun i => (c j i : ℚ_[p])) =
         fun i => (y i : ℚ_[p])) → ∀ j, ∃ z : ℤ_[p], v j = z] := by
  tfae_have 1 → 2 := one_two hJ c
  tfae_have 2 → 3 := two_three c
  tfae_have 3 → 1 := three_one hJ c
  tfae_finish

/-! ### Lemma 3.1 -/

/-- The quadratic form $f(\vec x) = \vec x^{t} F \vec x = \sum_{i,j} f_{ij}x_ix_j$ of a matrix $F$. -/
noncomputable def qf (F : Matrix (Fin n) (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p]) : ℚ_[p] := x ⬝ᵥ (F *ᵥ x)

/-- A vector of $\mathbb Z_p^n$ viewed in $\mathbb Q_p^n$. -/
def toQ (a : Fin n → ℤ_[p]) : Fin n → ℚ_[p] := fun i => (a i : ℚ_[p])

private theorem qf_bound (F : Matrix (Fin n) (Fin n) ℚ_[p]) (a : Fin n → ℤ_[p]) :
    ‖qf F (toQ a)‖ ≤ ∑ i, ∑ j, ‖F i j‖ := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_))
  have hi : ‖(toQ a i)‖ ≤ 1 := (a i).2
  have hj : ‖(toQ a j)‖ ≤ 1 := (a j).2
  rw [norm_mul, norm_mul]
  calc ‖toQ a i‖ * (‖F i j‖ * ‖toQ a j‖) ≤ 1 * (‖F i j‖ * 1) := by gcongr
    _ = ‖F i j‖ := by ring

private theorem qf_smul (F : Matrix (Fin n) (Fin n) ℚ_[p]) (t : ℚ_[p]) (x : Fin n → ℚ_[p]) :
    qf F (t • x) = t ^ 2 * qf F x := by
  simp only [qf, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

/-- The supremum of $\lvert f(\vec a)\rvert_p$ over $\vec a \in \mathbb Z_p^n$ is attained. -/
private theorem exists_max (F : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∃ a₀ : Fin n → ℤ_[p], ∀ a, ‖qf F (toQ a)‖ ≤ ‖qf F (toQ a₀)‖ := by
  classical
  by_cases h0 : ∀ a : Fin n → ℤ_[p], qf F (toQ a) = 0
  · exact ⟨0, fun a => by simp [h0]⟩
  push Not at h0
  obtain ⟨b, hb⟩ := h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  set P : ℤ → Prop := fun k => ∃ a, qf F (toQ a) ≠ 0 ∧ ‖qf F (toQ a)‖ = (p : ℝ) ^ k with hP
  have hnorm : ∀ a, qf F (toQ a) ≠ 0 → P (-(qf F (toQ a)).valuation) := fun a ha =>
    ⟨a, ha, Padic.norm_eq_zpow_neg_valuation ha⟩
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ i, ∑ j, ‖F i j‖) hp1
  have hbdd : ∃ K : ℤ, ∀ k, P k → k ≤ K := by
    refine ⟨N, fun k ⟨a, _, ha⟩ => ?_⟩
    have h1 : (p : ℝ) ^ k < (p : ℝ) ^ (N : ℤ) := by
      rw [← ha, zpow_natCast]; exact (qf_bound F a).trans_lt hN
    exact ((zpow_lt_zpow_iff_right₀ hp1).1 h1).le
  obtain ⟨k₀, ⟨a₀, ha₀, hk₀⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨_, hnorm b hb⟩
  refine ⟨a₀, fun a => ?_⟩
  by_cases ha : qf F (toQ a) = 0
  · rw [ha, norm_zero]; exact norm_nonneg _
  · rw [hk₀, Padic.norm_eq_zpow_neg_valuation ha]
    exact zpow_le_zpow_right₀ hp1.le (hmax _ (hnorm a ha))

/-- **Cassels, Ch. 8, Lemma 3.1**: *the form $f(\vec x) = \vec x^{t}F\vec x$ with $F \in M_n(\mathbb Q_p)$ is
$\mathbb Z_p$-equivalent to a form $g$ with $\lvert g_{11}\rvert = \sup_{\vec a \in \mathbb Z_p^n}\lvert g(\vec a)\rvert$*:
there is $T \in \mathrm{GL}_n(\mathbb Z_p)$ such that $g(\vec x) = f(T\vec x)$ (matrix $T^{t}FT$) satisfies
$\lvert g(\vec a)\rvert_p \le \lvert g(e_0)\rvert_p$ for all $\vec a \in \mathbb Z_p^n$; $g(e_0) = g_{00}$ is Cassels'
$g_{11}$. Cassels assumes $f$ regular; this is not needed. -/
@[kb "cassels1978" "Ch. 8, Lemma 3.1, p. 113"]
theorem exists_equiv_sup_first (hn : 0 < n) (F : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ∃ T : GL (Fin n) ℤ_[p], ∀ a : Fin n → ℤ_[p],
      ‖qf ((T.val.map PadicInt.Coe.ringHom)ᵀ * F * T.val.map PadicInt.Coe.ringHom) (toQ a)‖ ≤
        ‖qf ((T.val.map PadicInt.Coe.ringHom)ᵀ * F * T.val.map PadicInt.Coe.ringHom)
          (toQ (Pi.single ⟨0, hn⟩ 1))‖ := by
  classical
  obtain ⟨a₀, hmax⟩ := exists_max F
  -- a maximizing vector with `f(a₀) ≠ 0` has a unit coordinate
  by_cases hz : qf F (toQ a₀) = 0
  · refine ⟨1, fun a => ?_⟩
    have := hmax a
    rw [hz, norm_zero] at this
    have h0 : ‖qf ((((1 : GL (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom)ᵀ * F *
        (((1 : GL (Fin n) ℤ_[p]) : Matrix (Fin n) (Fin n) ℤ_[p]).map PadicInt.Coe.ringHom)) (toQ a)‖ = 0 := by
      simp only [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one]
      exact le_antisymm this (norm_nonneg _)
    rw [h0]; exact norm_nonneg _
  have hunit : ∃ i, IsUnit (a₀ i) := by
    by_contra hno
    push Not at hno
    have hdvd : ∀ i, (p : ℤ_[p]) ∣ a₀ i := fun i => by
      rw [← PadicInt.norm_lt_one_iff_dvd, ← PadicInt.mem_nonunits]; exact hno i
    choose b hb using hdvd
    have hab : toQ a₀ = (p : ℚ_[p]) • toQ b := by
      funext i; simp [toQ, hb i]
    have h1 := hmax b
    rw [hab, qf_smul, norm_mul, norm_pow, Padic.norm_p] at h1
    have hpos : 0 < ‖qf F (toQ b)‖ := by
      rw [norm_pos_iff]; intro h; apply hz; rw [hab, qf_smul, h, mul_zero]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have : ((p : ℝ)⁻¹) ^ 2 < 1 := by
      rw [inv_pow]; exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 two_ne_zero)
    nlinarith
  obtain ⟨i, hi⟩ := hunit
  have hJ : 1 ≤ n := hn
  have h2 : ∃ s : Fin 1 ↪ Fin n, IsUnit ((colsMatP (fun _ : Fin 1 => a₀)).submatrix s id).det :=
    ⟨⟨fun _ => i, fun x y _ => Subsingleton.elim x y⟩, by rw [Matrix.det_unique]; exact hi⟩
  obtain ⟨T, hT⟩ := ((tfae_extends_basis_padic hJ (fun _ => a₀)).out 2 1).1 h2
  have hT0 : T.val *ᵥ Pi.single ⟨0, hn⟩ 1 = a₀ := hT 0
  set φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom with hφ
  have hcomp : ∀ x : Fin n → ℤ_[p], qf ((T.val.map φ)ᵀ * F * T.val.map φ) (toQ x) = qf F (toQ (T.val *ᵥ x)) := by
    intro x
    have hmv : toQ (T.val *ᵥ x) = T.val.map φ *ᵥ toQ x := by
      funext k; exact RingHom.map_mulVec φ T.val x k
    rw [hmv]
    simp only [qf, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mul_assoc]
    rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
  refine ⟨T, fun a => ?_⟩
  rw [hcomp, hcomp, hT0]
  exact hmax _

/-! ### Lemmas 3.2 and 3.3: integral symmetries -/

/-- A vector of $\mathbb Q_p^n$ with all coordinates in $\mathbb Z_p$. -/
def IsIntVec (x : Fin n → ℚ_[p]) : Prop := ∀ i, ‖x i‖ ≤ 1

/-- The polar form $f(\vec x + \vec y) - f(\vec x) - f(\vec y) = \vec x^{t}F\vec y + \vec y^{t}F\vec x$ (Cassels'
$2f(\vec x, \vec y)$). -/
noncomputable def bil (F : Matrix (Fin n) (Fin n) ℚ_[p]) (x y : Fin n → ℚ_[p]) : ℚ_[p] := x ⬝ᵥ (F *ᵥ y) + y ⬝ᵥ (F *ᵥ x)

/-- An *integral automorph* of $f$: a $\mathbb Q_p$-linear automorphism $\sigma$ of $\mathbb Q_p^n$ with
$f(\sigma\vec x) = f(\vec x)$ such that $\sigma$ and $\sigma^{-1}$ map $\mathbb Z_p^n$ into itself (equivalently, the
matrix of $\sigma$ is in $\mathrm{GL}_n(\mathbb Z_p)$). -/
def IsIntAut (F : Matrix (Fin n) (Fin n) ℚ_[p]) (σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p])) : Prop :=
  (∀ x, qf F (σ x) = qf F x) ∧ (∀ x, IsIntVec x → IsIntVec (σ x)) ∧ (∀ x, IsIntVec x → IsIntVec (σ.symm x))

theorem qf_add (F : Matrix (Fin n) (Fin n) ℚ_[p]) (x y : Fin n → ℚ_[p]) :
    qf F (x + y) = qf F x + qf F y + bil F x y := by
  simp only [qf, bil, Matrix.mulVec_add, dotProduct_add, add_dotProduct]; ring

theorem bil_comm (F : Matrix (Fin n) (Fin n) ℚ_[p]) (x y : Fin n → ℚ_[p]) : bil F x y = bil F y x := by
  simp only [bil]; ring

theorem bil_self (F : Matrix (Fin n) (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p]) : bil F x x = 2 * qf F x := by
  simp only [bil, qf]; ring

theorem bil_sub_smul (F : Matrix (Fin n) (Fin n) ℚ_[p]) (b x : Fin n → ℚ_[p]) (t : ℚ_[p]) :
    bil F b (x - t • b) = bil F b x - t * bil F b b := by
  simp only [bil, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]; ring

/-- The symmetry $\tau_b(\vec x) = \vec x - \frac{2f(\vec b, \vec x)}{f(\vec b)}\vec b$ (Cassels' (3.7)). -/
noncomputable def tauFun (F : Matrix (Fin n) (Fin n) ℚ_[p]) (b : Fin n → ℚ_[p]) :
    (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p]) where
  toFun x := x - (bil F b x / qf F b) • b
  map_add' x y := by
    have : bil F b (x + y) = bil F b x + bil F b y := by
      simp only [bil, Matrix.mulVec_add, dotProduct_add, add_dotProduct]; ring
    rw [this, add_div, add_smul]; abel
  map_smul' c x := by
    have : bil F b (c • x) = c * bil F b x := by
      simp only [bil, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    simp only [RingHom.id_apply, this, smul_sub, smul_smul, mul_div_assoc]

theorem tauFun_apply (F : Matrix (Fin n) (Fin n) ℚ_[p]) (b x : Fin n → ℚ_[p]) :
    tauFun F b x = x - (bil F b x / qf F b) • b := rfl

theorem tauFun_involutive (F : Matrix (Fin n) (Fin n) ℚ_[p]) {b : Fin n → ℚ_[p]} (hb : qf F b ≠ 0) :
    Function.Involutive (tauFun F b) := by
  intro x
  rw [tauFun_apply, tauFun_apply, bil_sub_smul, bil_self]
  have : (bil F b x - bil F b x / qf F b * (2 * qf F b)) / qf F b = -(bil F b x / qf F b) := by
    field_simp; ring
  rw [this, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem qf_tauFun (F : Matrix (Fin n) (Fin n) ℚ_[p]) {b : Fin n → ℚ_[p]} (hb : qf F b ≠ 0) (x : Fin n → ℚ_[p]) :
    qf F (tauFun F b x) = qf F x := by
  rw [tauFun_apply, sub_eq_add_neg, qf_add, ← neg_smul, qf_smul]
  have h1 : bil F x (-(bil F b x / qf F b) • b) = -(bil F b x / qf F b) * bil F b x := by
    simp only [bil, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  rw [h1]
  field_simp
  ring

/-- The symmetry $\tau_b$ as a linear automorphism (for $f(\vec b) \ne 0$). -/
noncomputable def tau (F : Matrix (Fin n) (Fin n) ℚ_[p]) {b : Fin n → ℚ_[p]} (hb : qf F b ≠ 0) :
    (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  LinearEquiv.ofInvolutive (tauFun F b) (tauFun_involutive F hb)

private theorem norm_sub3 (a b c : ℚ_[p]) (C : ℝ) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hc : ‖c‖ ≤ C) :
    ‖a - b - c‖ ≤ C := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le ha ?_)) ?_)
  · rwa [norm_neg]
  · rwa [norm_neg]

theorem isIntVec_add {x y : Fin n → ℚ_[p]} (hx : IsIntVec x) (hy : IsIntVec y) : IsIntVec (x + y) :=
  fun i => (Padic.nonarchimedean _ _).trans (max_le (hx i) (hy i))

/-- **Cassels, Ch. 8, Lemma 3.2**: *suppose $\lvert f(\vec b)\rvert = \sup_{\vec a \in \mathbb Z_p^n}\lvert f(\vec a)\rvert$
(here $\vec b \in \mathbb Z_p^n$, $f(\vec b) \ne 0$); then $\tau_b$ is a $\mathbb Z_p$-automorph of $f$.* -/
@[kb "cassels1978" "Ch. 8, Lemma 3.2, p. 114"]
theorem isIntAut_tau (F : Matrix (Fin n) (Fin n) ℚ_[p]) {b : Fin n → ℚ_[p]} (hb : qf F b ≠ 0)
    (hbint : IsIntVec b) (hsup : ∀ a, IsIntVec a → ‖qf F a‖ ≤ ‖qf F b‖) : IsIntAut F (tau F hb) := by
  have hint : ∀ x, IsIntVec x → IsIntVec (tauFun F b x) := by
    intro x hx i
    have ht : ‖bil F b x / qf F b‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.2 hb)]
      have : bil F b x = qf F (b + x) - qf F b - qf F x := by rw [qf_add]; ring
      rw [this]
      exact norm_sub3 _ _ _ _ (hsup _ (isIntVec_add hbint hx)) le_rfl (hsup _ hx)
    rw [tauFun_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le (hx i) ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_mul ht (hbint i) (norm_nonneg _) zero_le_one).trans (by norm_num)
  refine ⟨qf_tauFun F hb, hint, fun x hx => ?_⟩
  exact hint x hx

/-- **Cassels, Ch. 8, Lemma 3.3** ($p \ne 2$, a Witt lemma over $\mathbb Z_p$): *suppose that
$\vec a_1, \vec a_2 \in \mathbb Z_p^n$ satisfy $f(\vec a_1) = f(\vec a_2)$ and
$\lvert f(\vec a_1)\rvert = \lvert f(\vec a_2)\rvert = \sup_{\vec a \in \mathbb Z_p^n}\lvert f(\vec a)\rvert$; then there
is an integral automorph $\sigma$ of $f$ with $\sigma\vec a_1 = \vec a_2$.* The supremum is assumed nonzero
($f(\vec a_1) \ne 0$), which holds for a regular $f$. Indices: Cassels' $a_1, a_2$ are `a₁`, `a₂`. -/
@[kb "cassels1978" "Ch. 8, Lemma 3.3, p. 114"]
theorem exists_intAut_apply_eq (hp2 : p ≠ 2) (F : Matrix (Fin n) (Fin n) ℚ_[p]) {a₁ a₂ : Fin n → ℚ_[p]}
    (h1 : IsIntVec a₁) (h2 : IsIntVec a₂) (heq : qf F a₁ = qf F a₂) (hne : qf F a₁ ≠ 0)
    (hsup : ∀ a, IsIntVec a → ‖qf F a‖ ≤ ‖qf F a₁‖) :
    ∃ σ, IsIntAut F σ ∧ σ a₁ = a₂ := by
  have hsum : qf F (a₁ - a₂) + qf F (a₁ + a₂) = 4 * qf F a₁ := by
    have e1 := qf_add F a₁ a₂
    have e2 := qf_add F a₁ (-a₂)
    have hb : bil F a₁ (-a₂) = - bil F a₁ a₂ := by
      simp only [bil, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]
      ring
    have hq : qf F (-a₂) = qf F a₂ := by
      simp only [qf, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]
      ring
    rw [← sub_eq_add_neg] at e2
    rw [e1, e2, hb, hq, ← heq]; ring
  have h4 : ‖(4 : ℚ_[p])‖ = 1 := by
    have : (4 : ℚ_[p]) = ((2 ^ 2 : ℕ) : ℚ_[p]) := by norm_num
    rw [this, Padic.norm_natCast_eq_one_iff]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  have hcase : ‖qf F (a₁ - a₂)‖ = ‖qf F a₁‖ ∨ ‖qf F (a₁ + a₂)‖ = ‖qf F a₁‖ := by
    have hm : IsIntVec (a₁ - a₂) := by
      intro i; rw [Pi.sub_apply, sub_eq_add_neg]
      exact (Padic.nonarchimedean _ _).trans (max_le (h1 i) (by rw [norm_neg]; exact h2 i))
    by_contra hc
    push Not at hc
    have l1 := lt_of_le_of_ne (hsup _ hm) hc.1
    have l2 := lt_of_le_of_ne (hsup _ (isIntVec_add h1 h2)) hc.2
    have := congrArg norm hsum
    rw [norm_mul, h4, one_mul] at this
    have := (Padic.nonarchimedean (qf F (a₁ - a₂)) (qf F (a₁ + a₂))).trans_lt (max_lt l1 l2)
    linarith
  have hsup₂ : ∀ a, IsIntVec a → ‖qf F a‖ ≤ ‖qf F a₂‖ := by rw [← heq]; exact hsup
  rcases hcase with hc | hc
  · have hb : qf F (a₁ - a₂) ≠ 0 := by rw [← norm_ne_zero_iff, hc, norm_ne_zero_iff]; exact hne
    have hbint : IsIntVec (a₁ - a₂) := by
      intro i; rw [Pi.sub_apply, sub_eq_add_neg]
      exact (Padic.nonarchimedean _ _).trans (max_le (h1 i) (by rw [norm_neg]; exact h2 i))
    refine ⟨tau F hb, isIntAut_tau F hb hbint (by rw [hc]; exact hsup), ?_⟩
    show tauFun F (a₁ - a₂) a₁ = a₂
    rw [tauFun_apply]
    have : bil F (a₁ - a₂) a₁ = qf F (a₁ - a₂) := by
      have e := qf_add F a₁ (-a₂)
      rw [← sub_eq_add_neg] at e
      have hq : qf F (-a₂) = qf F a₂ := by
        simp only [qf, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]
        ring
      rw [e, hq, ← heq]
      simp only [bil, Matrix.mulVec_sub, Matrix.mulVec_neg, dotProduct_sub, sub_dotProduct, dotProduct_neg,
        neg_dotProduct, qf]; ring
    rw [this, div_self hb, one_smul]; abel
  · have hb : qf F (a₁ + a₂) ≠ 0 := by rw [← norm_ne_zero_iff, hc, norm_ne_zero_iff]; exact hne
    have hbint : IsIntVec (a₁ + a₂) := isIntVec_add h1 h2
    have hne₂ : qf F a₂ ≠ 0 := heq ▸ hne
    have A1 := isIntAut_tau F hb hbint (by rw [hc]; exact hsup)
    have A2 := isIntAut_tau F hne₂ h2 hsup₂
    refine ⟨(tau F hb).trans (tau F hne₂), ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
    · simp only [LinearEquiv.trans_apply]; rw [A2.1, A1.1]
    · simp only [LinearEquiv.trans_apply]; exact A2.2.1 _ (A1.2.1 _ hx)
    · simp only [LinearEquiv.symm_trans_apply]; exact A1.2.2 _ (A2.2.2 _ hx)
    · show tauFun F a₂ (tauFun F (a₁ + a₂) a₁) = a₂
      have : bil F (a₁ + a₂) a₁ = qf F (a₁ + a₂) := by
        rw [qf_add, ← heq]
        simp only [bil, Matrix.mulVec_add, dotProduct_add, add_dotProduct, qf]; ring
      rw [tauFun_apply F (a₁ + a₂), this, div_self hb, one_smul, sub_add_cancel_left, map_neg, tauFun_apply,
        bil_self]
      rw [show 2 * qf F a₂ / qf F a₂ = 2 by field_simp]
      rw [two_smul]; abel

end QuadFormsKB.Cassels
