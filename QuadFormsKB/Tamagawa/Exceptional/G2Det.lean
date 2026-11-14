/-
# $G_2\subseteq SO(7)$: automorphisms of an octonion algebra have determinant $1$ on $\mathbb O_0$

For an octonion algebra $\mathbb O = (a, b, c)_K$ with $a, b, c\ne0$ over a field $K$ of characteristic $0$
(every number field), every $g\in G_2(K) = \operatorname{Aut}(\mathbb O)$ restricts to an isometry of
$(\mathbb O_0, N)$ (`G2.toPure`, `G2.norm_toPure`) of **determinant $1$** (`G2.det_toPure`). So $G_2(K)$ is a
subgroup of $SO(\mathbb O_0, N)$, the special orthogonal group of the 7-dimensional form
$\langle -a,-b,ab,-c,ac,bc,-abc\rangle$ (Springer–Veldkamp 2000, §2.3 [unverified locator], where it is a consequence
of the connectedness of $G_2$).

**Proof (an elementary replacement for connectedness).** Let $L_x(y) = xy$ (`leftMul`) and
$\Omega(v_0, \dots, v_6) = \sum_{\sigma\in S_7}\operatorname{sgn}(\sigma)\,L_{v_{\sigma 0}}\cdots L_{v_{\sigma 6}}$, the alternation of
the product of left multiplications, an alternating 7-form on $\mathbb O_0$ with values in
$\operatorname{End}_K(\mathbb O)$ (`omega`). Then:
1. $g$ conjugates $L$: $L_{gx} = gL_xg^{-1}$, so $\Omega(gv) = g\,\Omega(v)\,g^{-1}$;
2. $\Omega(gv) = \det(g|_{\mathbb O_0})\,\Omega(v)$, as for every alternating form of top degree;
3. on the standard orthogonal basis $e_0, \dots, e_6 = i, j, k, \ell, i\ell, j\ell, k\ell$ of $\mathbb O_0$ the operators
   $L_{e_r}$ anticommute ($x(yw) + y(xw) = (xy+yx)w$ and $xy + yx = -\langle x, y\rangle$ for pure $x, y$), so
   $\Omega(e) = 7!\,L_{e_0}\cdots L_{e_6}$, and $e_0(e_1(\cdots(e_6\cdot1))) = -a^2b^2c^2$ (direct computation);
4. evaluating at $1$: $\Omega(ge)(1) = g(\Omega(e)(1)) = g(-7!\,a^2b^2c^2) = -7!\,a^2b^2c^2$, while
   $\Omega(ge)(1) = \det(g)\cdot(-7!\,a^2b^2c^2)$. Hence $\det g = 1$.

The characteristic-$0$ hypothesis is used only for $7!\ne0$ and $2\ne0$; the statement holds in every
characteristic $\ne2$ (Springer–Veldkamp), but this proof needs $7!\ne0$.
-/
import QuadFormsKB.Tamagawa.Exceptional.Spin7

open Quaternion

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace QuadFormsKB.Exceptional

open Octonion

variable {K : Type*} [Field K] {a b c : K}

/-! ### The standard basis of the pure octonions -/

/-- The coordinates $(x_1, \dots, x_7)$ of a pure octonion
$x = x_1 i + x_2 j + x_3 k + (x_4 + x_5 i + x_6 j + x_7 k)\ell$, indexed $0, \dots, 6$ (0-based). -/
def pureCoords [CharZero K] : pureOct K a b c ≃ₗ[K] (Fin 7 → K) where
  toFun x := ![(x : Octonion K a b c).fst.imI, (x : Octonion K a b c).fst.imJ,
    (x : Octonion K a b c).fst.imK, (x : Octonion K a b c).snd.re, (x : Octonion K a b c).snd.imI,
    (x : Octonion K a b c).snd.imJ, (x : Octonion K a b c).snd.imK]
  invFun v := ⟨⟨⟨0, v 0, v 1, v 2⟩, ⟨v 3, v 4, v 5, v 6⟩⟩, by
    rw [mem_pure]; simp [trace]⟩
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' t x := by ext i; fin_cases i <;> simp
  left_inv x := by
    have h := mem_pure.mp x.2
    simp only [trace] at h
    have h0 : (x : Octonion K a b c).fst.re = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h two_ne_zero
      · exact h
    apply Subtype.ext
    ext <;> simp [h0]
  right_inv v := by ext i; fin_cases i <;> rfl

/-- The basis $e_0, \dots, e_6 = i, j, k, \ell, i\ell, j\ell, k\ell$ of $\mathbb O_0$. -/
def pureBasis [CharZero K] : Module.Basis (Fin 7) K (pureOct K a b c) :=
  Module.Basis.ofEquivFun pureCoords

/-- The standard pure octonions $i, j, k, \ell, i\ell, j\ell, k\ell$ as pairs $(p, q)$. -/
def stdPure : Fin 7 → Octonion K a b c :=
  ![⟨⟨0, 1, 0, 0⟩, 0⟩, ⟨⟨0, 0, 1, 0⟩, 0⟩, ⟨⟨0, 0, 0, 1⟩, 0⟩, ⟨0, ⟨1, 0, 0, 0⟩⟩, ⟨0, ⟨0, 1, 0, 0⟩⟩,
    ⟨0, ⟨0, 0, 1, 0⟩⟩, ⟨0, ⟨0, 0, 0, 1⟩⟩]

theorem pureBasis_apply [CharZero K] (r : Fin 7) :
    ((pureBasis r : pureOct K a b c) : Octonion K a b c) = stdPure r := by
  rw [pureBasis, Module.Basis.coe_ofEquivFun]
  fin_cases r <;> ext <;> simp [pureCoords, stdPure]

theorem polar_stdPure (r s : Fin 7) (h : r ≠ s) :
    polar (stdPure r : Octonion K a b c) (stdPure s) = 0 := by
  fin_cases r <;> fin_cases s <;> simp at h <;> simp only [polar, stdPure] <;> oct_coords <;>
    simp <;> ring

/-! ### Products of left multiplications -/

/-- For pure $x, y$: $L_yL_x = -L_xL_y - \langle x, y\rangle$; in particular orthogonal pure octonions give
anticommuting left multiplications. -/
theorem leftMul_anticomm (x y : pureOct K a b c) (h : polar (x : Octonion K a b c) y = 0) :
    leftMul y * leftMul x = -(leftMul x * leftMul y) := by
  have hx := mem_pure.mp x.2
  have hy := mem_pure.mp y.2
  ext w : 1
  simp only [Module.End.mul_apply, leftMul_apply, LinearMap.neg_apply]
  have key : ∀ (x y w : Octonion K a b c), x * (y * w) + y * (x * w) =
      (trace x * trace y - polar x y) • w + trace x • (y * w) + trace y • (x * w)
        - (trace x * trace y) • w := by
    intro x y w; simp only [polar]; oct_ring
  have := key x y w
  rw [hx, hy, h] at this
  simp only [zero_mul, sub_self, zero_smul, add_zero] at this
  exact eq_neg_of_add_eq_zero_right this

/-- The product $L_{v_0}\cdots L_{v_6}$ as a multilinear map. -/
def leftProd : MultilinearMap K (fun _ : Fin 7 => pureOct K a b c) (Module.End K (Octonion K a b c)) :=
  (MultilinearMap.mkPiAlgebraFin K 7 (Module.End K (Octonion K a b c))).compLinearMap
    (fun _ => (leftMul : pureOct K a b c →ₗ[K] Module.End K (Octonion K a b c)))

theorem leftProd_apply (v : Fin 7 → pureOct K a b c) :
    leftProd v = (List.ofFn fun r => leftMul (v r)).prod := by
  rw [leftProd, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply]

private theorem list_swap {M : Type*} [Ring M] (l₁ l₂ : List M) (x y : M) (h : y * x = -(x * y)) :
    (l₁ ++ y :: x :: l₂).prod = -(l₁ ++ x :: y :: l₂).prod := by
  simp only [List.prod_append, List.prod_cons, ← mul_assoc, h, neg_mul, mul_neg]

private theorem ofFn_swap {M : Type*} (f : Fin 7 → M) (r : Fin 6) :
    ∃ l₁ l₂ : List M, List.ofFn (fun i => f (Equiv.swap r.castSucc r.succ i)) =
      l₁ ++ f r.succ :: f r.castSucc :: l₂ ∧ List.ofFn f = l₁ ++ f r.castSucc :: f r.succ :: l₂ := by
  fin_cases r
  · exact ⟨[], [f 2, f 3, f 4, f 5, f 6], by rw [List.ofFn_eq_map]; rfl, by rw [List.ofFn_eq_map]; rfl⟩
  · exact ⟨[f 0], [f 3, f 4, f 5, f 6], by rw [List.ofFn_eq_map]; rfl, by rw [List.ofFn_eq_map]; rfl⟩
  · exact ⟨[f 0, f 1], [f 4, f 5, f 6], by rw [List.ofFn_eq_map]; rfl, by rw [List.ofFn_eq_map]; rfl⟩
  · exact ⟨[f 0, f 1, f 2], [f 5, f 6], by rw [List.ofFn_eq_map]; rfl, by rw [List.ofFn_eq_map]; rfl⟩
  · exact ⟨[f 0, f 1, f 2, f 3], [f 6], by rw [List.ofFn_eq_map]; rfl, by rw [List.ofFn_eq_map]; rfl⟩
  · exact ⟨[f 0, f 1, f 2, f 3, f 4], [], by rw [List.ofFn_eq_map]; rfl,
      by rw [List.ofFn_eq_map]; rfl⟩

/-- An adjacent transposition changes the sign of the product of left multiplications of a pairwise
orthogonal family. -/
theorem leftProd_swap (v : Fin 7 → pureOct K a b c)
    (horth : ∀ r s, r ≠ s → polar (v r : Octonion K a b c) (v s) = 0) (r : Fin 6) :
    leftProd (fun i => v (Equiv.swap r.castSucc r.succ i)) = -leftProd v := by
  obtain ⟨l₁, l₂, e₁, e₂⟩ := ofFn_swap (fun i => leftMul (v i)) r
  rw [leftProd_apply, leftProd_apply, e₁, e₂]
  exact list_swap l₁ l₂ _ _ (leftMul_anticomm (v r.castSucc) (v r.succ)
    (horth _ _ (Fin.castSucc_lt_succ (i := r)).ne))

/-- For a pairwise orthogonal family, $L_{v_{\sigma0}}\cdots L_{v_{\sigma6}} = \operatorname{sgn}(\sigma)L_{v_0}\cdots L_{v_6}$. -/
theorem leftProd_perm (σ : Equiv.Perm (Fin 7)) : ∀ v : Fin 7 → pureOct K a b c,
    (∀ r s, r ≠ s → polar (v r : Octonion K a b c) (v s) = 0) →
    leftProd (fun i => v (σ i)) = Equiv.Perm.sign σ • leftProd v := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun r : Fin 6 => Equiv.swap r.castSucc r.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨r, rfl⟩ := hτ
    intro v horth
    rw [leftProd_swap v horth r, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := r)).ne, Units.neg_smul,
      one_smul]
  | one => intro v _; simp
  | mul σ τ _ _ hσ hτ =>
    intro v horth
    have horth' : ∀ r s, r ≠ s → polar (v (σ r) : Octonion K a b c) (v (σ s)) = 0 :=
      fun r s hrs => horth _ _ (σ.injective.ne hrs)
    have e : (fun i => v ((σ * τ) i)) = fun i => (fun j => v (σ j)) (τ i) := rfl
    rw [e, hτ (fun j => v (σ j)) horth', hσ v horth, smul_smul, Equiv.Perm.sign_mul, mul_comm]

/-- **The alternated product** $\Omega(v) = \sum_\sigma\operatorname{sgn}(\sigma)L_{v_{\sigma0}}\cdots L_{v_{\sigma6}}$. -/
def omega : (pureOct K a b c) [⋀^Fin 7]→ₗ[K] Module.End K (Octonion K a b c) :=
  MultilinearMap.alternatization leftProd

theorem omega_orth (v : Fin 7 → pureOct K a b c)
    (horth : ∀ r s, r ≠ s → polar (v r : Octonion K a b c) (v s) = 0) :
    omega v = (5040 : K) • leftProd v := by
  rw [omega, MultilinearMap.alternatization_apply]
  have : ∀ σ : Equiv.Perm (Fin 7),
      Equiv.Perm.sign σ • (leftProd.domDomCongr σ) v = leftProd v := by
    intro σ
    rw [MultilinearMap.domDomCongr_apply, leftProd_perm σ v horth, smul_smul, Int.units_mul_self,
      one_smul]
  rw [Finset.sum_congr rfl (fun σ _ => this σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  have h7 : Nat.factorial 7 = 5040 := by decide
  rw [h7, ← Nat.cast_smul_eq_nsmul K]; simp

private theorem prod_ofFn_seven {M : Type*} [Monoid M] (f : Fin 7 → M) :
    (List.ofFn f).prod = f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * f 6))))) := by
  simp [List.ofFn_succ]

/-- $e_0(e_1(\cdots(e_6\cdot1))) = -a^2b^2c^2$. -/
theorem leftProd_pureBasis_one [CharZero K] :
    leftProd (pureBasis : Fin 7 → pureOct K a b c) 1 = scalar (-(a ^ 2 * b ^ 2 * c ^ 2)) := by
  rw [leftProd_apply, prod_ofFn_seven]
  simp only [Module.End.mul_apply, leftMul_apply, pureBasis_apply]
  have s0 : (stdPure 0 : Octonion K a b c) = ⟨⟨0, 1, 0, 0⟩, 0⟩ := rfl
  have s1 : (stdPure 1 : Octonion K a b c) = ⟨⟨0, 0, 1, 0⟩, 0⟩ := rfl
  have s2 : (stdPure 2 : Octonion K a b c) = ⟨⟨0, 0, 0, 1⟩, 0⟩ := rfl
  have s3 : (stdPure 3 : Octonion K a b c) = ⟨0, ⟨1, 0, 0, 0⟩⟩ := rfl
  have s4 : (stdPure 4 : Octonion K a b c) = ⟨0, ⟨0, 1, 0, 0⟩⟩ := rfl
  have s5 : (stdPure 5 : Octonion K a b c) = ⟨0, ⟨0, 0, 1, 0⟩⟩ := rfl
  have s6 : (stdPure 6 : Octonion K a b c) = ⟨0, ⟨0, 0, 0, 1⟩⟩ := rfl
  rw [s0, s1, s2, s3, s4, s5, s6]
  have h6 : (⟨0, ⟨0, 0, 0, 1⟩⟩ : Octonion K a b c) * 1 = ⟨0, ⟨0, 0, 0, 1⟩⟩ := by oct_ring
  have h5 : (⟨0, ⟨0, 0, 1, 0⟩⟩ : Octonion K a b c) * ⟨0, ⟨0, 0, 0, 1⟩⟩ =
      ⟨⟨0, -(b * c), 0, 0⟩, 0⟩ := by oct_ring
  have h4 : (⟨0, ⟨0, 1, 0, 0⟩⟩ : Octonion K a b c) * ⟨⟨0, -(b * c), 0, 0⟩, 0⟩ =
      ⟨0, ⟨a * b * c, 0, 0, 0⟩⟩ := by oct_ring
  have h3 : (⟨0, ⟨1, 0, 0, 0⟩⟩ : Octonion K a b c) * ⟨0, ⟨a * b * c, 0, 0, 0⟩⟩ =
      ⟨⟨a * b * c ^ 2, 0, 0, 0⟩, 0⟩ := by oct_ring
  have h2 : (⟨⟨0, 0, 0, 1⟩, 0⟩ : Octonion K a b c) * ⟨⟨a * b * c ^ 2, 0, 0, 0⟩, 0⟩ =
      ⟨⟨0, 0, 0, a * b * c ^ 2⟩, 0⟩ := by oct_ring
  have h1 : (⟨⟨0, 0, 1, 0⟩, 0⟩ : Octonion K a b c) * ⟨⟨0, 0, 0, a * b * c ^ 2⟩, 0⟩ =
      ⟨⟨0, -(a * b ^ 2 * c ^ 2), 0, 0⟩, 0⟩ := by oct_ring
  have h0 : (⟨⟨0, 1, 0, 0⟩, 0⟩ : Octonion K a b c) * ⟨⟨0, -(a * b ^ 2 * c ^ 2), 0, 0⟩, 0⟩ =
      scalar (-(a ^ 2 * b ^ 2 * c ^ 2)) := by oct_ring
  rw [h6, h5, h4, h3, h2, h1, h0]

/-! ### Conjugation by an automorphism -/

theorem leftMul_toPure (g : G2 K a b c) (x : pureOct K a b c) :
    leftMul (G2.toPure g x) = g.1.conj (leftMul x) := by
  ext y : 1
  simp only [leftMul_apply, G2.toPure_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [G2.map_mul, LinearEquiv.apply_symm_apply]

theorem G2.symm_one (g : G2 K a b c) : g.1.symm 1 = 1 := by
  conv_lhs => rw [← G2.map_one g]
  exact g.1.symm_apply_apply 1

theorem conj_apply_one (g : G2 K a b c) (X : Module.End K (Octonion K a b c)) :
    (g.1.conj X) 1 = g.1 (X 1) := by
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [G2.symm_one]

/-- Conjugation by $g$ as a monoid homomorphism of $\operatorname{End}_K(\mathbb O)$. -/
def conjHom (g : G2 K a b c) : Module.End K (Octonion K a b c) →* Module.End K (Octonion K a b c) where
  toFun := g.1.conj
  map_one' := LinearEquiv.conj_id g.1
  map_mul' f h := LinearEquiv.conj_comp g.1 h f

theorem leftProd_toPure (g : G2 K a b c) (v : Fin 7 → pureOct K a b c) :
    leftProd (fun r => G2.toPure g (v r)) = g.1.conj (leftProd v) := by
  simp only [leftProd_apply, leftMul_toPure]
  change _ = conjHom g _
  rw [map_list_prod, List.map_ofFn]; rfl

theorem omega_toPure (g : G2 K a b c) (v : Fin 7 → pureOct K a b c) :
    omega (fun r => G2.toPure g (v r)) = g.1.conj (omega v) := by
  simp only [omega, MultilinearMap.alternatization_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def]
  rw [map_zsmul]
  congr 1
  exact leftProd_toPure g (v ∘ σ)

/-! ### The determinant -/

/-- Evaluation at $1$ followed by the real part, a linear form on $\operatorname{End}_K(\mathbb O)$. -/
def evalRe : Module.End K (Octonion K a b c) →ₗ[K] K where
  toFun X := (X 1).fst.re
  map_add' X Y := by simp
  map_smul' t X := by simp

@[simp] theorem evalRe_apply (X : Module.End K (Octonion K a b c)) : evalRe X = (X 1).fst.re := rfl

/-- **$G_2\subseteq SO(7)$**: for $a, b, c\ne0$ over a field of characteristic $0$, every automorphism of the
octonion algebra $(a, b, c)_K$ acts on the pure octonions $\mathbb O_0$ with determinant $1$.

Source: Springer–Veldkamp 2000, §2.3 [unverified locator]; the proof here is elementary (module
docstring). -/
@[kb "springerveldkamp2000" "§2.3"]
theorem G2.det_toPure [CharZero K] (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (g : G2 K a b c) :
    LinearMap.det ((G2.toPure g : pureOct K a b c ≃ₗ[K] pureOct K a b c) :
      pureOct K a b c →ₗ[K] pureOct K a b c) = 1 := by
  set e := (pureBasis : Module.Basis (Fin 7) K (pureOct K a b c))
  set ω := (evalRe : Module.End K (Octonion K a b c) →ₗ[K] K).compAlternatingMap omega
  have horth : ∀ r s, r ≠ s → polar ((e r : pureOct K a b c) : Octonion K a b c) (e s) = 0 := by
    intro r s hrs; rw [pureBasis_apply, pureBasis_apply]; exact polar_stdPure r s hrs
  set s : K := 5040 * (-(a ^ 2 * b ^ 2 * c ^ 2)) with hs
  have hΩ : omega e 1 = scalar s := by
    rw [omega_orth e horth, LinearMap.smul_apply, leftProd_pureBasis_one, smul_eq_scalar_mul]
    rw [hs]; oct_ring
  have hω : ω e = s := by
    rw [LinearMap.compAlternatingMap_apply, evalRe_apply, hΩ]; simp
  have hs0 : s ≠ 0 := by
    rw [hs]
    have : (5040 : K) ≠ 0 := by exact_mod_cast (by norm_num : (5040 : ℕ) ≠ 0)
    exact mul_ne_zero this (neg_ne_zero.mpr (by positivity))
  -- (2): the top-degree form transforms by the determinant
  have h1 : ω (fun r => G2.toPure g (e r)) = LinearMap.det
      ((G2.toPure g : pureOct K a b c ≃ₗ[K] pureOct K a b c) : pureOct K a b c →ₗ[K] _) * s := by
    rw [ω.eq_smul_basis_det e]
    simp only [smul_apply, smul_eq_mul]
    rw [hω]
    have := e.det_comp ((G2.toPure g : pureOct K a b c ≃ₗ[K] pureOct K a b c) :
      pureOct K a b c →ₗ[K] _) e
    rw [e.det_self, _root_.mul_one] at this
    rw [show (fun r => G2.toPure g (e r)) = ((G2.toPure g : pureOct K a b c ≃ₗ[K] _) :
      pureOct K a b c →ₗ[K] _) ∘ e from rfl, this, mul_comm]
  -- (1): conjugation by `g` fixes the scalar `Ω(e)(1)`
  have h2 : ω (fun r => G2.toPure g (e r)) = s := by
    rw [LinearMap.compAlternatingMap_apply, evalRe_apply, omega_toPure, conj_apply_one, hΩ,
      G2.map_scalar, fst_scalar, QuaternionAlgebra.re_coe]
  have := h1.symm.trans h2
  exact (mul_eq_right₀ hs0).mp this

end QuadFormsKB.Exceptional
