/-
# Class finiteness over $F$: number-field lemmas (O'Meara 103:1–103:2)

**Layer:** a number field $F$ with ring of integers $\mathcal O_F$ and a $\mathbb Z$-basis $\omega$ of $\mathcal O_F$
(`RingOfIntegers.basis F`). Elementary lemmas used by the finiteness of the class number of an arbitrary (definite or
indefinite) genus (`Lattices/ClassFinite.lean`).

**Proves**
* `exists_scale_ideal` (ideal classes have small integral representatives): there is a constant $C_F$ such that for every
  nonzero finitely generated $\mathcal O_F$-submodule $\mathfrak a \subseteq F$ there is $b \ne 0$ with $b\mathfrak a \subseteq \mathcal O_F$
  and a positive integer $m \le C_F$ in $b\mathfrak a$ (from Mathlib's Minkowski bound
  `exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr`; $m = N(b\mathfrak a)$).
* `exists_pigeon` (O'Meara 103:1 + the pigeonhole of 103:2): for $B \in M_n(\mathcal O_F)$ with $\det B \ne 0$ and $T$ with
  $T^{n[F:\mathbb Q]} > |N(\det B)|$ there is $0 \ne \xi \in \mathcal O_F^n$ such that every coordinate of $B\xi$ has
  $\omega$-coordinates of absolute value $< T$. ($[\mathcal O_F^n : B\mathcal O_F^n] = |N(\det B)|$ by Mathlib's
  `Submodule.natAbs_det_equiv` and `LinearMap.det_restrictScalars`.)
* `exists_short` (O'Meara 103:2): for $P \in \mathrm{GL}_n(F)$ with $|N(\det P)| \le D$ there is $0 \ne \xi \in \mathcal O_F^n$ with
  $|\varphi((P\xi)_i)| \le (\lfloor D\rfloor + 1)\,W$ for every coordinate $i$ and every embedding $\varphi : F \to \mathbb C$, where
  $W = \sum_\varphi\sum_k |\varphi(\omega_k)|$ (`embW`).
* `finite_bounded` (Mathlib's `Embeddings.finite_of_norm_le`): the algebraic integers with all conjugates bounded form a
  finite set; `exists_sub_mem_box`: every $z \in \mathcal O_F$ is $\equiv$ modulo $m$ to an element with $\omega$-coordinates in
  $[0, m)$.

*Route.* O'Meara counts field elements bounded by an idèle (his Theorem 33:5); here the pigeonhole runs over the
$\mathbb Z$-box $\{\sum_k t_k\omega_k : 0 \le t_k < T\}^n$ and the scaling $\lambda$ with $\lambda P$ integral is a rational integer,
so that all conjugates of $\lambda$ have the same size. No reduction theory and no geometry of numbers beyond Mathlib's
Minkowski bound for ideal classes.

O'Meara, *Introduction to Quadratic Forms* (1973), 103:1, 103:2 (printed p. 305–307 = PDF p. 313–315).
-/
import QuadFormsKB.Lattices.Finite
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Norm.Transitivity

open NumberField Module Matrix
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices.ClassFin

variable {F : Type*} [Field F] [NumberField F]

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### Small representatives of ideal classes -/

/-- **Ideal classes have small integral representatives** (Minkowski): there is $C_F \in \mathbb N$ such that every nonzero
finitely generated $\mathcal O_F$-submodule $\mathfrak a \subseteq F$ (a fractional ideal) has a scaling $b \ne 0$ with
$b\mathfrak a \subseteq \mathcal O_F$ and some $a \in \mathfrak a$ with $ba = m$ a positive integer $\le C_F$ (take $b$ in
$\mathfrak a^{-1}$ of small norm, so that $N(b\mathfrak a) \le C_F$, and $m = N(b\mathfrak a) \in b\mathfrak a$). -/
@[kb "omeara1963" "§103, proof of 103:3, step 2, p. 307 (ideal class representatives)"]
theorem exists_scale_ideal :
    ∃ C : ℕ, ∀ A : Submodule (𝓞 F) F, A.FG → A ≠ ⊥ →
      ∃ b : F, b ≠ 0 ∧ (∀ a ∈ A, b * a ∈ (algebraMap (𝓞 F) F).range) ∧
        ∃ a ∈ A, ∃ m : ℕ, 0 < m ∧ m ≤ C ∧ b * a = m := by
  classical
  set K : ℝ := (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F * (finrank ℚ F).factorial /
    (finrank ℚ F) ^ (finrank ℚ F) * Real.sqrt |(discr F : ℝ)| with hK
  refine ⟨⌊K⌋₊, fun A hA hA0 => ?_⟩
  let I : FractionalIdeal (𝓞 F)⁰ F := ⟨A, FractionalIdeal.isFractional_of_fg hA⟩
  have hI : I ≠ 0 := by
    intro h
    apply hA0
    have : (I : Submodule (𝓞 F) F) = ⊥ := by rw [h, FractionalIdeal.coe_zero]
    exact this
  obtain ⟨b, hb, hb0, hnorm⟩ :=
    NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr F (Units.mk0 I⁻¹ (inv_ne_zero hI))
  simp only [Units.val_mk0] at hb hnorm
  have hJ : FractionalIdeal.spanSingleton (𝓞 F)⁰ b * I ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 F)⁰ b * I ≤ I⁻¹ * I :=
          mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hb) I
      _ = 1 := inv_mul_cancel₀ hI
  obtain ⟨I₁, hI₁⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have habs : (Ideal.absNorm I₁ : ℚ) = |Algebra.norm ℚ b| * FractionalIdeal.absNorm I := by
    rw [← FractionalIdeal.coeIdeal_absNorm (K := F), hI₁, map_mul,
      FractionalIdeal.absNorm_span_singleton]
  have habs' : FractionalIdeal.absNorm I⁻¹ * FractionalIdeal.absNorm I = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hI, map_one]
  have hIpos : (0 : ℝ) ≤ (FractionalIdeal.absNorm I : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I
  have hle : (Ideal.absNorm I₁ : ℝ) ≤ K := by
    have e1 : (Ideal.absNorm I₁ : ℝ) = (|Algebra.norm ℚ b| : ℝ) * (FractionalIdeal.absNorm I : ℝ) := by
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) habs
    have e2 : ((FractionalIdeal.absNorm I⁻¹ : ℚ) : ℝ) * (FractionalIdeal.absNorm I : ℝ) = 1 := by
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) habs'
    have hn' : (|Algebra.norm ℚ b| : ℝ) ≤ ((FractionalIdeal.absNorm I⁻¹ : ℚ) : ℝ) * K := by
      have := hnorm
      rw [hK]
      push_cast at this ⊢
      linarith [this, show ((FractionalIdeal.absNorm I⁻¹ : ℚ) : ℝ) * (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F *
          (finrank ℚ F).factorial / (finrank ℚ F) ^ (finrank ℚ F) * Real.sqrt |(discr F : ℝ)| =
          ((FractionalIdeal.absNorm I⁻¹ : ℚ) : ℝ) * ((4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F * (finrank ℚ F).factorial /
          (finrank ℚ F) ^ (finrank ℚ F) * Real.sqrt |(discr F : ℝ)|) by ring]
    rw [e1]
    calc (|Algebra.norm ℚ b| : ℝ) * (FractionalIdeal.absNorm I : ℝ)
        ≤ ((FractionalIdeal.absNorm I⁻¹ : ℚ) : ℝ) * K * (FractionalIdeal.absNorm I : ℝ) :=
          mul_le_mul_of_nonneg_right hn' hIpos
      _ = K := by rw [mul_comm _ K, mul_assoc, e2, mul_one]
  have hI₁ne : I₁ ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot] at hI₁
    have : FractionalIdeal.spanSingleton (𝓞 F)⁰ b * I ≠ 0 :=
      mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr hb0) hI
    exact this hI₁.symm
  have hm0 : 0 < Ideal.absNorm I₁ :=
    Nat.pos_of_ne_zero fun h => hI₁ne (Ideal.absNorm_eq_zero_iff.mp h)
  have hmem : ((Ideal.absNorm I₁ : 𝓞 F) : F) ∈ (I₁ : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, Ideal.absNorm_mem I₁, rfl⟩
  rw [hI₁, FractionalIdeal.mem_singleton_mul] at hmem
  obtain ⟨a, ha, hba⟩ := hmem
  refine ⟨b, hb0, fun a' ha' => ?_, a, ha, Ideal.absNorm I₁, hm0, Nat.le_floor hle, ?_⟩
  · have : b * a' ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ b * I :=
      FractionalIdeal.mem_singleton_mul.mpr ⟨a', ha', rfl⟩
    obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp (hJ this)
    exact ⟨x, hx⟩
  · rw [← hba]; simp

/-! ### Bounded algebraic integers -/

/-- The $\mathbb Z$-basis $\omega$ of $\mathcal O_F$. -/
abbrev ω : Basis (OIdx F) ℤ (𝓞 F) := RingOfIntegers.basis F

variable (F) in
/-- $W = \sum_\varphi \sum_k |\varphi(\omega_k)|$ over the embeddings $\varphi : F \to \mathbb C$. -/
def embW : ℝ :=
  ∑ φ : F →+* ℂ, ∑ k : OIdx F, ‖φ (ιO (ω k))‖

theorem embW_nonneg : 0 ≤ embW F := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_omega_le (φ : F →+* ℂ) (k : OIdx F) : ‖φ (ιO (ω k))‖ ≤ embW F := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ∑ k : OIdx F, ‖φ (ιO (ω k))‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ))
  exact Finset.single_le_sum (f := fun k : OIdx F => ‖φ (ιO (ω k))‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ k)

/-- **A bounded combination of the $\omega_k$:** if $|q_k| \le T$ then $|\varphi(\sum_k q_k\omega_k)| \le T\,W\cdot|OIdx|$;
we use the cruder but uniform $\sum_k |q_k|\,|\varphi\omega_k|$. -/
theorem norm_sum_omega_le (φ : F →+* ℂ) (q : OIdx F → ℤ) (T : ℝ) (hq : ∀ k, |(q k : ℝ)| ≤ T) :
    ‖φ (ιO (∑ k, q k • ω k))‖ ≤ T * embW F := by
  have hT : 0 ≤ T := le_trans (abs_nonneg _) (hq (Classical.arbitrary _))
  rw [map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖φ (ιO (q k • ω k))‖ ≤ ∑ k, T * ‖φ (ιO (ω k))‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [map_zsmul, map_zsmul, norm_zsmul ℚ]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simpa [Int.norm_eq_abs] using hq k
    _ = T * ∑ k, ‖φ (ιO (ω k))‖ := by rw [Finset.mul_sum]
    _ ≤ T * embW F := by
        refine mul_le_mul_of_nonneg_left ?_ hT
        exact Finset.single_le_sum (f := fun φ : F →+* ℂ => ∑ k : OIdx F, ‖φ (ιO (ω k))‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ)

/-- **Bounded algebraic integers** (Mathlib `Embeddings.finite_of_norm_le`): the $z \in F$ that are integral with
$|\varphi(z)| \le B$ for every embedding $\varphi : F \to \mathbb C$ form a finite set. -/
theorem finite_bounded (B : ℝ) :
    {z : F | z ∈ (algebraMap (𝓞 F) F).range ∧ ∀ φ : F →+* ℂ, ‖φ z‖ ≤ B}.Finite := by
  refine (Embeddings.finite_of_norm_le F ℂ B).subset ?_
  rintro z ⟨⟨a, rfl⟩, hz⟩
  exact ⟨a.2, hz⟩

/-- **Reduction modulo $m$:** every $z \in \mathcal O_F$ is $z = m w + \sum_k q_k\omega_k$ with $w \in \mathcal O_F$ and
$0 \le q_k < m$. -/
theorem exists_sub_mem_box (m : ℕ) (hm : 0 < m) (z : 𝓞 F) :
    ∃ w : 𝓞 F, ∃ q : OIdx F → ℤ, (∀ k, 0 ≤ q k ∧ q k < m) ∧ z = (m : 𝓞 F) * w + ∑ k, q k • ω k := by
  classical
  set c := (ω (F := F)).repr z
  refine ⟨∑ k, (c k / (m : ℤ)) • ω k, fun k => c k % (m : ℤ), fun k => ⟨Int.emod_nonneg _ (by omega),
    Int.emod_lt_of_pos _ (by omega)⟩, ?_⟩
  conv_lhs => rw [← (ω (F := F)).sum_repr z]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (m : 𝓞 F) * ((c k / (m : ℤ)) • ω k) = ((m : ℤ) * (c k / (m : ℤ))) • ω k by
    rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring]
  rw [← add_smul, Int.mul_ediv_add_emod]

/-! ### The pigeonhole (O'Meara 103:1, 103:2) -/

variable {n : ℕ}

theorem mulVec_injective_of_det_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (B : Matrix (Fin n) (Fin n) R) (hB : B.det ≠ 0) : Function.Injective (B *ᵥ ·) := by
  intro x y h
  have h' : B *ᵥ (x - y) = 0 := by simp only at h; rw [mulVec_sub, h, sub_self]
  have : B.det • (x - y) = 0 := by
    have e : adjugate B *ᵥ (B *ᵥ (x - y)) = B.det • (x - y) := by
      rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
    rw [← e, h', mulVec_zero]
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_left hB)

/-- **The pigeonhole of O'Meara 103:2** (with 103:1, $[\mathcal O_F^n : B\mathcal O_F^n] = |N(\det B)|$): if
$T^{n[F:\mathbb Q]} > |N(\det B)|$ then some $0 \ne \xi \in \mathcal O_F^n$ has $(B\xi)_i = \sum_k q_{ik}\omega_k$ with
$|q_{ik}| < T$. Two of the $T^{n[F:\mathbb Q]}$ vectors with $\omega$-coordinates in $[0, T)$ are congruent modulo
$B\mathcal O_F^n$. -/
@[kb "omeara1963" "§103, 103:1, 103:2, p. 305"]
theorem exists_pigeon (B : Matrix (Fin n) (Fin n) (𝓞 F)) (hB : B.det ≠ 0) (T : ℕ)
    (hT : (Algebra.norm ℤ B.det).natAbs < T ^ (n * Fintype.card (OIdx F))) :
    ∃ ξ : Fin n → 𝓞 F, ξ ≠ 0 ∧ ∀ i, ∃ q : OIdx F → ℤ, (∀ k, |q k| < T) ∧
      (B *ᵥ ξ) i = ∑ k, q k • ω k := by
  classical
  let f : (Fin n → 𝓞 F) →ₗ[𝓞 F] (Fin n → 𝓞 F) := Matrix.mulVecLin B
  have hinj : Function.Injective (f.restrictScalars ℤ) := mulVec_injective_of_det_ne_zero B hB
  set N := LinearMap.range (f.restrictScalars ℤ)
  let e : (Fin n → 𝓞 F) ≃ₗ[ℤ] N := LinearEquiv.ofInjective (f.restrictScalars ℤ) hinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin n → 𝓞 F) →+ N) =
      f.restrictScalars ℤ := by
    refine LinearMap.ext fun x => ?_
    rfl
  rw [hcomp, LinearMap.det_restrictScalars] at hcard
  have hdet : LinearMap.det f = B.det := LinearMap.det_toLin' B
  rw [hdet] at hcard
  have hne : (Algebra.norm ℤ B.det).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact (Algebra.norm_ne_zero_iff).mpr hB
  have hfin : Finite ((Fin n → 𝓞 F) ⧸ N) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  let _ := Fintype.ofFinite ((Fin n → 𝓞 F) ⧸ N)
  let u : (Fin n → OIdx F → Fin T) → (Fin n → 𝓞 F) := fun t i => ∑ k, ((t i k : ℕ) : ℤ) • ω k
  have hu : Function.Injective u := by
    intro t t' h
    funext i k
    have := congrArg (fun v => (ω (F := F)).repr (v i) k) h
    simp only [u, map_sum, map_zsmul, Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
    exact Fin.ext (by exact_mod_cast this)
  have hlt : Fintype.card ((Fin n → 𝓞 F) ⧸ N) < Fintype.card (Fin n → OIdx F → Fin T) := by
    rw [← Nat.card_eq_fintype_card, ← hcard]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rwa [← pow_mul, mul_comm]
  obtain ⟨t, t', htt, he⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t => N.mkQ (u t)) hlt
  have hmem : u t - u t' ∈ N := (Submodule.Quotient.eq N).mp he
  obtain ⟨ξ, hξ⟩ := hmem
  refine ⟨ξ, ?_, fun i => ⟨fun k => ((t i k : ℕ) : ℤ) - ((t' i k : ℕ) : ℤ), fun k => ?_, ?_⟩⟩
  · rintro rfl
    apply htt
    apply hu
    have : (f.restrictScalars ℤ) 0 = u t - u t' := hξ
    rw [map_zero] at this
    exact (sub_eq_zero.mp this.symm)
  · have h1 : ((t i k : ℕ) : ℤ) < T := by exact_mod_cast (t i k).2
    have h2 : ((t' i k : ℕ) : ℤ) < T := by exact_mod_cast (t' i k).2
    have h3 : (0 : ℤ) ≤ ((t i k : ℕ) : ℤ) := by positivity
    have h4 : (0 : ℤ) ≤ ((t' i k : ℕ) : ℤ) := by positivity
    rw [abs_lt]; constructor <;> linarith
  · have : (B *ᵥ ξ) = u t - u t' := hξ
    rw [this]
    simp only [Pi.sub_apply, u, ← Finset.sum_sub_distrib, sub_smul]

/-- **Short vectors in a free lattice (O'Meara 103:2):** for $P \in M_n(F)$ ($n \ge 1$) with $\det P \ne 0$ and
$|N(\det P)| \le D$ there is $0 \ne \xi \in \mathcal O_F^n$ with $|\varphi((P\xi)_i)| \le (\lfloor D\rfloor + 1)\,W$ for every
coordinate $i$ and every embedding $\varphi$. *Proof:* choose $0 \ne \lambda \in \mathbb Z$ with $B = \lambda P$ integral and apply
`exists_pigeon` with $T = |\lambda|(\lfloor D\rfloor + 1)$ *Update (simplification):* O'Meara counts field elements bounded by an idèle
(Theorem 33:5) and takes $\lambda \in \mathfrak o$; with $\lambda \in \mathbb Z$ all conjugates of $\lambda$ have the same size and a
$\mathbb Z$-box count suffices. -/
@[kb "omeara1963" "§103, 103:2, p. 305"]
theorem exists_short (hn : 0 < n) (P : Matrix (Fin n) (Fin n) F) (hP : P.det ≠ 0) (D : ℝ)
    (hD : |(Algebra.norm ℚ P.det : ℝ)| ≤ D) :
    ∃ ξ : Fin n → 𝓞 F, ξ ≠ 0 ∧ ∀ i (φ : F →+* ℂ),
      ‖φ ((P *ᵥ fun j => ιO (ξ j)) i)‖ ≤ ((⌊D⌋₊ : ℝ) + 1) * embW F := by
  classical
  obtain ⟨l, hl0, hl⟩ := exists_int_mul_mem (Finset.univ.image fun ij : Fin n × Fin n => P ij.1 ij.2)
  have hl' : ∀ i j, (l : F) * P i j ∈ (algebraMap (𝓞 F) F).range := fun i j =>
    hl _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  choose B hB using hl'
  set B' : Matrix (Fin n) (Fin n) (𝓞 F) := Matrix.of B
  have hBmap : B'.map ιO = (l : F) • P := by ext i j; simp [B', hB]
  have hdetB : ιO B'.det = (l : F) ^ n * P.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hBmap, det_smul, Fintype.card_fin]
  have hB0 : B'.det ≠ 0 := by
    intro h; rw [h, map_zero] at hdetB
    exact hP ((mul_eq_zero.mp hdetB.symm).resolve_left (pow_ne_zero _ (by exact_mod_cast hl0)))
  set d := Fintype.card (OIdx F)
  have hd : finrank ℚ F = d := by
    rw [← RingOfIntegers.rank F, Module.finrank_eq_card_chooseBasisIndex]
  set T₀ : ℕ := ⌊D⌋₊ + 1
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have hT₀ : D < T₀ := by simpa [T₀] using Nat.lt_floor_add_one D
  have hnd : 0 < n * d := Nat.mul_pos hn (by rw [← hd]; exact Module.finrank_pos)
  -- the norm of `det B`
  have hnormB : ((Algebra.norm ℤ B'.det : ℤ) : ℚ) = (l : ℚ) ^ (n * d) * Algebra.norm ℚ P.det := by
    rw [Algebra.coe_norm_int, show ((B'.det : 𝓞 F) : F) = ιO B'.det from rfl, hdetB, map_mul, map_pow, show ((l : F)) = algebraMap ℚ F (l : ℚ) by simp,
      Algebra.norm_algebraMap, hd, ← pow_mul, mul_comm d n]
  have hlpos : (0 : ℝ) < |(l : ℝ)| ^ (n * d) := pow_pos (abs_pos.mpr (by exact_mod_cast hl0)) _
  have hT : (Algebra.norm ℤ B'.det).natAbs < (l.natAbs * T₀) ^ (n * Fintype.card (OIdx F)) := by
    have h1 : ((Algebra.norm ℤ B'.det).natAbs : ℝ) = |(l : ℝ)| ^ (n * d) * |(Algebra.norm ℚ P.det : ℝ)| := by
      have := congrArg (fun q : ℚ => |(q : ℝ)|) hnormB
      simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow] at this
      rw [Nat.cast_natAbs, Int.cast_abs, this]
    have h2 : (D : ℝ) < (T₀ : ℝ) ^ (n * d) := by
      calc D < T₀ := hT₀
        _ ≤ (T₀ : ℝ) ^ (n * d) := by
          have : (1 : ℝ) ≤ T₀ := by simp [T₀]
          exact le_self_pow₀ this hnd.ne'
    have : ((Algebra.norm ℤ B'.det).natAbs : ℝ) < ((l.natAbs * T₀ : ℕ) : ℝ) ^ (n * d) := by
      rw [h1]
      push_cast
      rw [mul_pow, Nat.cast_natAbs, Int.cast_abs]
      calc |(l : ℝ)| ^ (n * d) * |(Algebra.norm ℚ P.det : ℝ)| ≤ |(l : ℝ)| ^ (n * d) * D :=
            mul_le_mul_of_nonneg_left hD hlpos.le
        _ < |(l : ℝ)| ^ (n * d) * (T₀ : ℝ) ^ (n * d) := mul_lt_mul_of_pos_left h2 hlpos
    exact_mod_cast this
  obtain ⟨ξ, hξ0, hξ⟩ := exists_pigeon B' hB0 _ hT
  refine ⟨ξ, hξ0, fun i φ => ?_⟩
  obtain ⟨q, hq, hqe⟩ := hξ i
  have hPξ : (P *ᵥ fun j => ιO (ξ j)) i = (l : F)⁻¹ * ιO ((B' *ᵥ ξ) i) := by
    have : ιO ((B' *ᵥ ξ) i) = (l : F) * (P *ᵥ fun j => ιO (ξ j)) i := by
      rw [RingHom.map_mulVec, hBmap, smul_mulVec, Pi.smul_apply, smul_eq_mul]; rfl
    rw [this, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hl0), one_mul]
  rw [hPξ, hqe, map_mul, norm_mul, map_inv₀, norm_inv, map_intCast, Complex.norm_intCast]
  have hla : (0 : ℝ) < |(l : ℝ)| := abs_pos.mpr (by exact_mod_cast hl0)
  have hb := norm_sum_omega_le φ q (|(l : ℝ)| * T₀) (fun k => by
    have := hq k
    have h' := (Int.cast_lt (R := ℝ)).mpr this
    push_cast at h'
    exact h'.le)
  calc |(l : ℝ)|⁻¹ * ‖φ (ιO (∑ k, q k • ω k))‖ ≤ |(l : ℝ)|⁻¹ * (|(l : ℝ)| * T₀ * embW F) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hla.le)
    _ = ((⌊D⌋₊ : ℝ) + 1) * embW F := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hla.ne', one_mul]; simp [T₀]

end QuadFormsKB.Lattices.ClassFin
