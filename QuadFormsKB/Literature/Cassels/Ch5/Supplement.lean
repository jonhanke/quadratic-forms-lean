/-
# Cassels, Chapter 5: supplementary items on convexity, lattices and Hermite's bound

**Setting.** As in `Minkowski.lean`: Euclidean space $\mathbb R^n$ is `Fin n → ℝ` with Lebesgue measure `volume`,
$\mathbb Z^n$ is `stdLattice n`, and an integral point is `fun i => (u i : ℝ)` for `u : Fin n → ℤ`. Indices are
$0, \dots, n-1$ (Cassels: $1, \dots, n$); so Cassels' $u_1, u_2$ are `u 0`, `u 1` below.

**Formalizes** (Cassels, *Rational Quadratic Forms*, Chapter 5; statements paraphrased, not quoted)
* §2, (2.4): Cassels' definition of a convex set equals Mathlib's `Convex ℝ`: `convex_iff`;
* §2, Note after Theorem 2.4: Minkowski's convex body theorem with $v(\mathcal C) \ge 2^n$ for compact $\mathcal C$:
  `minkowski_convex_body_compact`;
* §2, proof of Theorem 2.4: the volume of the parallelepiped $\lvert L_j(\vec x)\rvert < t_j$:
  `volume_parallelepiped`;
* §2, Corollary to Theorem 2.4, as printed (strict $0 < m < M$ and non-strict $\lvert m\theta_j - l_j\rvert \le M^{-1/n}$):
  `simultaneous_approximation_printed`;
* §3, p. 72: a discrete subgroup containing $n$ linearly independent points is a lattice
  (`exists_basis_of_discrete`) and a lattice is discrete (`discreteTopology_span_basis`);
* §3, (3.1): $d(\Gamma)$ does not depend on the basis: `abs_det_eq_of_span_eq`;
* §2, p. 69: the integral formulation of the proof of Blichfeldt's theorem: `blichfeldt_integral`,
  `blichfeldt_exists_point`;
* §3, p. 73: Hermite's bound is sharp for $n = 2$: `hermite_sharp_two`.

**Proof notes.** Almost everything is a repackaging of Mathlib (`Convex`, the geometry of numbers
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`, `Measure.addHaar_preimage_linearMap`,
`ZLattice`/`ZSpan`) and of `minkowski_linear_forms_at`. The argument for `hermite_sharp_two` is a direct
computation; for `minkowski_convex_body_compact` the hypothesis $n \ge 1$ is needed (see its docstring).
-/
import QuadFormsKB.Literature.Cassels.Ch5.Background
import QuadFormsKB.Literature.Cassels.Ch5.Approximation

namespace QuadFormsKB.Cassels.Ch5

open MeasureTheory Module Submodule ZSpan Matrix

/-- **Cassels, Ch. 5, §2, (2.4)** (convex set): a set $\mathcal C \subseteq \mathbb R^n$ is convex in Cassels' sense
(for all $\vec c_1, \vec c_2 \in \mathcal C$ and all real $\lambda_1, \lambda_2 \ge 0$ with $\lambda_1 + \lambda_2 = 1$ the
point $\lambda_1 \vec c_1 + \lambda_2 \vec c_2$ lies in $\mathcal C$) exactly when it is convex in Mathlib's sense
`Convex ℝ C`. Arguments: `n` the dimension, `C` the set. -/
@[kb "cassels1978" "Ch. 5, §2, (2.4), p. 69 (convex set)"]
theorem convex_iff {n : ℕ} (C : Set (Fin n → ℝ)) :
    Convex ℝ C ↔ ∀ c₁ ∈ C, ∀ c₂ ∈ C, ∀ l₁ l₂ : ℝ, 0 ≤ l₁ → 0 ≤ l₂ → l₁ + l₂ = 1 →
      l₁ • c₁ + l₂ • c₂ ∈ C :=
  Iff.rfl

/-- **Cassels, Ch. 5, §2, Note after Theorem 2.4** (Minkowski's convex body theorem, compact case): *if
$\mathcal C \subseteq \mathbb R^n$ is compact, convex and symmetric with $v(\mathcal C) \ge 2^n$, then $\mathcal C$
contains a $\vec u \in \mathbb Z^n$ other than $\vec 0$.* Here `n` is the dimension, `C` the set (`hsymm`: symmetric,
`hconv`: convex, `hcomp`: compact) and `hvol` the volume bound $2^n \le v(\mathcal C)$ with Lebesgue measure `volume`.
The conclusion is as in `minkowski_convex_body`.
*Update:* the hypothesis `hn : 0 < n` is needed (it is implicit in Cassels, whose $n$ is a positive dimension): for
$n = 0$ the space is a point, a compact set $\{0\}$ has volume $1 = 2^0$, and $\mathbb Z^0$ has no nonzero point. -/
@[kb "cassels1978" "Ch. 5, §2, Note after Thm. 2.4, p. 71"]
theorem minkowski_convex_body_compact {n : ℕ} (hn : 0 < n) {C : Set (Fin n → ℝ)}
    (hsymm : ∀ x ∈ C, -x ∈ C) (hconv : Convex ℝ C) (hcomp : IsCompact C) (hvol : 2 ^ n ≤ volume C) :
    ∃ u : Fin n → ℤ, u ≠ 0 ∧ (fun i => (u i : ℝ)) ∈ C := by
  have : Nontrivial (Fin n → ℝ) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  have fund := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin n)) (volume : Measure (Fin n → ℝ))
  have hF : volume (fundamentalDomain (Pi.basisFun ℝ (Fin n))) = 1 := by
    have : Matrix.of ⇑(Pi.basisFun ℝ (Fin n)) = 1 := by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp [this]
  have : Countable (stdLattice n).toAddSubgroup := (inferInstance : Countable (stdLattice n))
  obtain ⟨x, hx0, hxC⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (stdLattice n).toAddSubgroup) fund hsymm hconv hcomp (by simpa [hF] using hvol)
  obtain ⟨u, hu⟩ := mem_stdLattice.1 x.2
  refine ⟨u, fun h0 => hx0 ?_, hu ▸ hxC⟩
  apply Subtype.ext
  funext i; simp [hu, h0]

/-- **Cassels, Ch. 5, §2, proof of Theorem 2.4** (volume of the parallelepiped): *for a real $n \times n$ matrix $A$
of nonzero determinant (the linear forms $L_j(\vec x) = (A\vec x)_j$) and $t_j > 0$, the set
$\{\vec x : \lvert L_j(\vec x)\rvert < t_j \text{ for all } j\}$ has volume $2^n \lvert\det A\rvert^{-1} t_0 \cdots t_{n-1}$.*
Arguments: `A` the matrix, `hA` its determinant is nonzero, `t` the bounds, `ht` their positivity. -/
@[kb "cassels1978" "Ch. 5, §2, proof of Thm. 2.4, p. 71 (volume of the parallelepiped)"]
theorem volume_parallelepiped {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (t : Fin n → ℝ) (ht : ∀ j, 0 < t j) :
    volume {x : Fin n → ℝ | ∀ j, |(A *ᵥ x) j| < t j} =
      ENNReal.ofReal (2 ^ n * |A.det|⁻¹ * ∏ j, t j) := by
  have hset : {x : Fin n → ℝ | ∀ j, |(A *ᵥ x) j| < t j} =
      (Matrix.toLin' A) ⁻¹' (Set.univ.pi fun j => Set.Ioo (-t j) (t j)) := by
    ext x
    simp [abs_lt, Set.mem_pi]
  rw [hset, Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])]
  rw [LinearMap.det_toLin', Real.volume_pi_Ioo]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by linarith [ht j]), abs_inv,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Finset.prod_congr rfl (fun j _ => (by ring : t j - -t j = 2 * t j)), Finset.prod_mul_distrib]
  simp
  ring

/-- **Cassels, Ch. 5, §3, p. 72** (a lattice is a discrete subgroup): the $\mathbb Z$-span of a real basis `b` of
$\mathbb R^n$ is a discrete subgroup. -/
@[kb "cassels1978" "Ch. 5, §3, p. 72 (a lattice is a discrete subgroup)"]
theorem discreteTopology_span_basis {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    DiscreteTopology (span ℤ (Set.range b)) :=
  inferInstance

/-- **Cassels, Ch. 5, §3, p. 72** (a discrete subgroup containing $n$ linearly independent points is a lattice):
*let $\Gamma \subseteq \mathbb R^n$ be a discrete subgroup (`L`, with the discrete topology as a subspace) containing
$n$ linearly independent (over $\mathbb R$) points `v 0, …, v (n-1)`; then $\Gamma$ has a basis, i.e. there is an
$\mathbb R$-basis `b` of $\mathbb R^n$ with $\Gamma = \operatorname{span}_{\mathbb Z}\{b_0, \dots, b_{n-1}\}$.* -/
@[kb "cassels1978" "Ch. 5, §3, p. 72 (a discrete subgroup containing n linearly independent points is a lattice)"]
theorem exists_basis_of_discrete {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (h : ∃ v : Fin n → (Fin n → ℝ), LinearIndependent ℝ v ∧ ∀ i, v i ∈ L) :
    ∃ b : Basis (Fin n) ℝ (Fin n → ℝ), L = span ℤ (Set.range b) := by
  obtain ⟨v, hv, hvL⟩ := h
  have htop : span ℝ (L : Set (Fin n → ℝ)) = ⊤ := by
    have h1 : span ℝ (Set.range v) = ⊤ := by
      apply hv.span_eq_top_of_card_eq_finrank'
      simp
    rw [eq_top_iff, ← h1]
    exact span_mono (by rintro _ ⟨i, rfl⟩; exact hvL i)
  have : IsZLattice ℝ L := ⟨htop⟩
  let b := Module.Free.chooseBasis ℤ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n := by
    have h1 := ZLattice.rank ℝ L
    have h2 := Module.finrank_eq_card_chooseBasisIndex ℤ L
    simp only [finrank_fin_fun] at h1
    exact h2.symm.trans h1
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨(b.ofZLatticeBasis ℝ L).reindex e, ?_⟩
  rw [Basis.coe_reindex, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  exact ((b.ofZLatticeBasis_span ℝ L)).symm

/-- Helper: the covolume of the $\mathbb Z$-span of a real basis `b` of $\mathbb R^n$ is $\lvert\det(b_0, \dots,
b_{n-1})\rvert$, where `Matrix.of b` has the vector `b i` as its row `i`. -/
theorem covolume_span_basis {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    ZLattice.covolume (span ℤ (Set.range b)) = |(Matrix.of b).det| := by
  rw [ZLattice.covolume_eq_det (span ℤ (Set.range b)) (b.restrictScalars ℤ)]
  congr 3
  ext i j
  simp

/-- **Cassels, Ch. 5, §3, (3.1)** ($d(\Gamma)$ is independent of the basis): *if two real bases $b, b'$ of
$\mathbb R^n$ generate the same lattice $\Gamma = \operatorname{span}_{\mathbb Z}\{b_i\} = \operatorname{span}_{\mathbb Z}\{b'_i\}$,
then $\lvert\det(b_0, \dots, b_{n-1})\rvert = \lvert\det(b'_0, \dots, b'_{n-1})\rvert$* (the matrix `Matrix.of b` has the
vector `b i` as its row `i`). Arguments: `b`, `b'` the two bases, `h` equality of their $\mathbb Z$-spans. -/
@[kb "cassels1978" "Ch. 5, §3, (3.1), p. 72 (d(Γ) is independent of the basis)"]
theorem abs_det_eq_of_span_eq {n : ℕ} (b b' : Basis (Fin n) ℝ (Fin n → ℝ))
    (h : span ℤ (Set.range b) = span ℤ (Set.range b')) :
    |(Matrix.of b).det| = |(Matrix.of b').det| := by
  rw [← covolume_span_basis b, ← covolume_span_basis b', h]

/-- **Cassels, Ch. 5, §3, p. 73** (Hermite's bound is best possible for $n = 2$): the binary form
$u_0^2 + u_0 u_1 + u_1^2$, with Gram matrix `G` $= \begin{pmatrix} 1 & 1/2 \\ 1/2 & 1\end{pmatrix}$ (Cassels' $u_1, u_2$ are
`u 0`, `u 1`), is positive definite of determinant $3/4$, takes integer values $\ge 1$ on nonzero integral vectors, takes
the value $1$ at $(1, 0)$, and $1 = (4/3)^{(n-1)/2}\, d^{1/n}$ for $n = 2$, $d = 3/4$: Hermite's bound
$m \le (4/3)^{(n-1)/2} d^{1/n}$ for the minimum $m$ holds with equality. The five conjuncts are, in order, positive
definiteness, the determinant, the lower bound $1 \le \vec u^{T} G \vec u$ for integral $\vec u \ne 0$, the value at
$(1, 0)$, and the equality. -/
@[kb "cassels1978" "Ch. 5, §3, p. 73 (for n = 2 the bound (3.9) is best possible: u₁² + u₁u₂ + u₂²)"]
theorem hermite_sharp_two :
    let G : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]
    G.PosDef ∧ G.det = 3 / 4 ∧
      (∀ u : Fin 2 → ℤ, u ≠ 0 → 1 ≤ (fun i => (u i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (u i : ℝ))) ∧
      ((fun i => ((![1, 0] : Fin 2 → ℤ) i : ℝ)) ⬝ᵥ G *ᵥ (fun i => ((![1, 0] : Fin 2 → ℤ) i : ℝ)) = 1) ∧
      (1 : ℝ) = (4 / 3) ^ ((1 : ℝ) / 2) * G.det ^ ((1 : ℝ) / 2) := by
  intro G
  have hq : ∀ x : Fin 2 → ℝ, x ⬝ᵥ G *ᵥ x = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 := by
    intro x
    simp [G, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hdet : G.det = 3 / 4 := by
    simp [G, Matrix.det_fin_two]; norm_num
  refine ⟨?_, hdet, ?_, ?_, ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [G]
    · simp only [star_trivial]
      rw [hq]
      have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hx; ext i; fin_cases i <;> simp [hc.1, hc.2]
      rcases this with h | h
      · nlinarith [sq_nonneg (x 0 + 2 * x 1), sq_pos_of_ne_zero h, sq_nonneg (x 1)]
      · nlinarith [sq_nonneg (2 * x 0 + x 1), sq_pos_of_ne_zero h, sq_nonneg (x 0)]
  · intro u hu
    have hq' : (fun i => (u i : ℝ)) ⬝ᵥ G *ᵥ (fun i => (u i : ℝ)) =
        ((u 0 ^ 2 + u 0 * u 1 + u 1 ^ 2 : ℤ) : ℝ) := by
      rw [hq]; push_cast; ring
    rw [hq']
    have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hu; ext i; fin_cases i <;> simp [hc.1, hc.2]
    have hpos : (0 : ℤ) < u 0 ^ 2 + u 0 * u 1 + u 1 ^ 2 := by
      rcases hne with h | h
      · nlinarith [sq_nonneg (u 0 + 2 * u 1), sq_pos_of_ne_zero h, sq_nonneg (u 1)]
      · nlinarith [sq_nonneg (2 * u 0 + u 1), sq_pos_of_ne_zero h, sq_nonneg (u 0)]
    exact_mod_cast hpos
  · rw [hq]; simp
  · rw [hdet, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num

/-- **Cassels, Ch. 5, Corollary to Theorem 2.4, (2.8)–(2.9), as printed** (Dirichlet's simultaneous approximation):
*let $n \ge 1$, let $M > 1$ and let $\theta_0, \dots, \theta_{n-1}$ be real numbers; then there are an integer $m$ with
$0 < m < M$ and integers $l_0, \dots, l_{n-1}$ with $\lvert m\theta_j - l_j\rvert \le M^{-1/n}$ for all $j$.* This is the
printed form: the bound on $m$ is strict (2.8) and the approximation is non-strict (2.9), the reverse of the version
`simultaneous_approximation` of `Approximation.lean`. Arguments: `n` the number of $\theta$'s, `hn` that $n \ge 1$, `θ`
the reals, `M` the bound, `hM` that $M > 1$. Cassels takes $M$ an integer; here $M$ is any real $> 1$ (a
generalization; same proof). Proof as Cassels': Theorem 2.4 (`minkowski_linear_forms_at`) for the $n + 1$ forms
$\theta_j x_n - x_j$ ($0 \le j < n$) and $x_n$, with the non-strict inequality at the index $0$ (a $\theta$-form) and the
strict one at the last form $x_n$. -/
@[kb "cassels1978" "Ch. 5, Cor. to Thm. 2.4, (2.8)–(2.9), pp. 71–72 (as printed)"]
theorem simultaneous_approximation_printed {n : ℕ} (hn : 1 ≤ n) (θ : Fin n → ℝ) {M : ℝ} (hM : 1 < M) :
    ∃ m : ℤ, 0 < m ∧ (m : ℝ) < M ∧ ∃ l : Fin n → ℤ, ∀ j, |m * θ j - l j| ≤ M ^ (-(1 / n : ℝ)) := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 < M := by linarith
  set D : ℝ := M ^ (-(1 / n : ℝ)) with hD
  have hDpos : 0 < D := Real.rpow_pos_of_pos hM0 _
  have hD1 : D < 1 := Real.rpow_lt_one_of_one_lt_of_neg hM (by
    have : 0 < (1 / n : ℝ) := by positivity
    linarith)
  set θ' : Fin (n + 1) → ℝ := fun i => if h : i.val < n then θ ⟨i.val, h⟩ else 0 with hθ'
  have hθ'last : θ' (Fin.last n) = 0 := by simp [hθ']
  have hθ'cast : ∀ j : Fin n, θ' j.castSucc = θ j := fun j => by simp [hθ']
  set v : Fin (n + 1) → ℝ := Pi.single (Fin.last n) 1 with hv
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    -(1 + Matrix.replicateCol (Fin 1) (fun i => -θ' i) * Matrix.replicateRow (Fin 1) v) with hA
  have hAv : ∀ x : Fin (n + 1) → ℝ, ∀ i, (A *ᵥ x) i = θ' i * x (Fin.last n) - x i := by
    intro x i
    simp only [hA, Matrix.neg_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Pi.neg_apply, Pi.add_apply]
    have : (Matrix.replicateCol (Fin 1) (fun i => -θ' i) *ᵥ (Matrix.replicateRow (Fin 1) v *ᵥ x)) i
        = -θ' i * x (Fin.last n) := by
      simp [Matrix.mulVec, dotProduct, hv, Pi.single_apply]
    rw [this]; ring
  have hdet : |A.det| = 1 := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (fun i => -θ' i) v
    rw [hA, Matrix.det_neg]
    erw [h]
    have : v ⬝ᵥ (fun i => -θ' i) = 0 := by simp [hv, hθ'last]
    rw [this]; simp
  have hdet0 : A.det ≠ 0 := fun h => by rw [h, abs_zero] at hdet; norm_num at hdet
  set t : Fin (n + 1) → ℝ := fun j => if j = Fin.last n then M else D with ht
  have htpos : ∀ j, 0 < t j := fun j => by simp only [ht]; split_ifs <;> assumption
  have hprod : |A.det| ≤ ∏ j, t j := by
    rw [hdet, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (Fin.last n))]
    have : ∏ j ∈ Finset.univ.erase (Fin.last n), t j = D ^ n := by
      rw [Finset.prod_congr rfl (fun j hj => by simp [ht, Finset.ne_of_mem_erase hj] :
        ∀ j ∈ Finset.univ.erase (Fin.last n), t j = D)]
      simp
    rw [this]
    simp only [ht, ite_true]
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
      neg_mul, one_div, inv_mul_cancel₀ hnr.ne', Real.rpow_neg_one, mul_inv_cancel₀ hM0.ne']
  set j₀ : Fin (n + 1) := (⟨0, hn⟩ : Fin n).castSucc with hj₀
  obtain ⟨a, ha0, hal, haj⟩ := minkowski_linear_forms_at j₀ A hdet0 t htpos hprod
  have hj₀last : Fin.last n ≠ j₀ := (Fin.castSucc_ne_last _).symm
  have hlast : |(a (Fin.last n) : ℝ)| < M := by
    have := haj (Fin.last n) hj₀last; rw [hAv] at this; simpa [ht, hθ'last] using this
  have hj : ∀ j : Fin n, |θ j * (a (Fin.last n) : ℝ) - a j.castSucc| ≤ D := by
    intro j
    by_cases hjj : j.castSucc = j₀
    · have := hal; rw [← hjj, hAv, hθ'cast] at this
      simpa [ht, Fin.castSucc_ne_last j] using this
    · have := haj j.castSucc hjj
      rw [hAv, hθ'cast] at this
      simpa [ht, Fin.castSucc_ne_last j] using this.le
  have hm0 : a (Fin.last n) ≠ 0 := by
    intro h0
    apply ha0
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using h0
    · have := hj j
      rw [h0] at this
      simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg] at this
      have h1 : |(a j.castSucc : ℝ)| < 1 := this.trans_lt hD1
      have h2 : |a j.castSucc| < 1 := by exact_mod_cast h1
      have := abs_lt.1 h2
      simp only [Pi.zero_apply]
      omega
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · have hnegr : (a (Fin.last n) : ℝ) < 0 := by exact_mod_cast hneg
    refine ⟨-a (Fin.last n), by omega, ?_, fun j => -a j.castSucc, fun j => ?_⟩
    · have := abs_of_neg hnegr
      push_cast
      rw [← this]; exact hlast
    · have := hj j
      push_cast
      rw [← abs_neg]; convert this using 2; ring
  · refine ⟨a (Fin.last n), hpos, ?_, fun j => a j.castSucc, fun j => ?_⟩
    · exact (le_abs_self _).trans_lt hlast
    · have := hj j
      rw [mul_comm]; exact this

/-- Helper: the bijection $\mathbb Z^n \to$ `stdLattice n` (as an additive subgroup), $u \mapsto (u_i)_i$. -/
noncomputable def intVecEquivStdLattice (n : ℕ) : (Fin n → ℤ) ≃ (stdLattice n).toAddSubgroup :=
  Equiv.ofBijective (fun u => ⟨fun i => (u i : ℝ), mem_stdLattice.2 ⟨u, rfl⟩⟩)
    ⟨fun u w h => by
      funext i
      have : (u i : ℝ) = w i := congrFun (congrArg Subtype.val h) i
      exact_mod_cast this,
     fun g => by
      obtain ⟨u, hu⟩ := mem_stdLattice.1 g.2
      exact ⟨u, Subtype.ext hu.symm⟩⟩

/-- Helper: the half-open unit cube $W = [0,1)^n$ equals the fundamental domain of the standard basis. -/
theorem unitCube_eq_fundamentalDomain (n : ℕ) :
    Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1) = fundamentalDomain (Pi.basisFun ℝ (Fin n)) := by
  ext x
  simp [fundamentalDomain, Set.mem_pi]

/-- **Cassels, Ch. 5, §2, p. 69** (the integral formulation of the proof of Theorem 2.1): *for a measurable set
$\mathcal S \subseteq \mathbb R^n$, integrating over the unit cube $W = [0,1)^n$ the number of integral translates
$\vec w + \vec u$ ($\vec u \in \mathbb Z^n$) lying in $\mathcal S$ gives $v(\mathcal S)$:*
$\int_W \sum_{\vec u \in \mathbb Z^n} 1_{\mathcal S}(\vec w + \vec u)\, d\vec w = v(\mathcal S)$, in $[0, \infty]$.
Arguments: `S` the set, `hS` its measurability. -/
@[kb "cassels1978" "Ch. 5, §2, p. 69 (the integral formulation of the proof of Thm. 2.1)"]
theorem blichfeldt_integral {n : ℕ} {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    ∫⁻ x in Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
      ∑' u : Fin n → ℤ, S.indicator 1 (x + fun i => (u i : ℝ)) = volume S := by
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) (volume : Measure (Fin n → ℝ))
  set G := (stdLattice n).toAddSubgroup
  have : Countable G := (inferInstance : Countable (stdLattice n))
  set f : (Fin n → ℝ) → ENNReal := S.indicator 1 with hf
  have hmeas : ∀ g : G, Measurable fun x => f (g +ᵥ x) := fun g =>
    (measurable_one.indicator hS).comp (measurable_const_add _)
  have htot : volume S = ∫⁻ x in fundamentalDomain (Pi.basisFun ℝ (Fin n)), ∑' g : G, f (g +ᵥ x) := by
    rw [← lintegral_indicator_one hS, fund.lintegral_eq_tsum'' f, lintegral_tsum]
    exact fun g => (hmeas g).aemeasurable
  rw [htot, unitCube_eq_fundamentalDomain]
  refine setLIntegral_congr_fun (fundamentalDomain_measurableSet _) fun x _ => ?_
  rw [← (intVecEquivStdLattice n).tsum_eq]
  refine tsum_congr fun u => ?_
  simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm x]
  rfl

/-- **Cassels, Ch. 5, §2, p. 69** (consequence of the integral formulation): *if $k$ is a natural number with
$k < v(\mathcal S)$ for a measurable $\mathcal S \subseteq \mathbb R^n$, then some $\vec w$ in the unit cube
$W = [0,1)^n$ has more than $k$ integral translates $\vec w + \vec u$ in $\mathcal S$* (the number of translates in
$\mathcal S$, counted as the sum of the indicator over $\mathbb Z^n$, is $> k$; hence at least $k + 1$ translates lie
in $\mathcal S$). Arguments: `S` the set, `hS` its measurability, `k` the count, `hk` the volume bound. -/
@[kb "cassels1978" "Ch. 5, §2, p. 69 (the integral formulation of the proof of Thm. 2.1)"]
theorem blichfeldt_exists_point {n : ℕ} {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) {k : ℕ}
    (hk : (k : ENNReal) < volume S) :
    ∃ w ∈ Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1),
      (k : ENNReal) < ∑' u : Fin n → ℤ, S.indicator 1 (w + fun i => (u i : ℝ)) := by
  by_contra hno
  push Not at hno
  have hW : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have h1 := setLIntegral_mono' (μ := volume) hW (g := fun _ => (k : ENNReal)) hno
  rw [setLIntegral_const, blichfeldt_integral hS, Real.volume_pi_Ico] at h1
  simp at h1
  exact absurd hk (not_lt.2 h1)
