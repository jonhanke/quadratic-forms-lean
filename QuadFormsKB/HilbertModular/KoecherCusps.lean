/-
# Hilbert modular forms IX: the Koecher principle at every cusp for congruence subgroups

`KoecherBounded.mem_modularFormSpace_of_koecher` reduces the cusp condition of $M_k(\Gamma)$ (for $d \ge 2$) to a
group-theoretic one: every conjugate $\gamma^{-1}\Gamma\gamma$ contains the translations by a fractional ideal and
$\mathrm{diag}(u^m, u^{-m})$ for all units $u$. Here that hypothesis is verified for every $\Gamma$ containing a principal
congruence subgroup $\Gamma(\mathfrak N)$, $\mathfrak N \ne 0$ (`koecher_cusp_hyp_of_GammaFull_le`):

* $\gamma T(\beta)\gamma^{-1} = \begin{pmatrix}1 - ac\beta & a^2\beta\\ -c^2\beta & 1 + ac\beta\end{pmatrix}$ (`conj_transl_apply`), so with
  $D \in \mathcal{O}_F\setminus0$ a common denominator of the entries of $\gamma$ (`exists_denom`) and $\beta \in \mathfrak M = D^2\mathfrak N$,
  $\gamma T(\beta)\gamma^{-1} \equiv 1 \bmod \mathfrak N$;
* $\gamma\,\mathrm{diag}(t, t^{-1})\gamma^{-1} - 1$ has entries $ad(t-1) - bc(t^{-1}-1)$, $ab(t^{-1}-t)$, $cd(t-t^{-1})$,
  $ad(t^{-1}-1) - bc(t-1)$ (`conj_diagU_apply`), which lie in $\mathfrak N$ when $t \equiv t^{-1} \equiv 1 \bmod \mathfrak M$; this holds for
  $t = u^m$, $m = |(\mathcal{O}_F/\mathfrak M)^\times|$ ($\mathcal{O}_F/\mathfrak M$ is finite);
* `mem_GammaFull_of`: a matrix of $\mathrm{SL}_2(F)$ congruent to $1$ modulo $\mathfrak N$ is in $\Gamma(\mathfrak N)$.

Consequences (`mem_modularFormSpace_of_GammaFull_le`, `mem_modularFormSpace_Gamma0_of_koecher`): for $d \ge 2$ and
$\Gamma \supseteq \Gamma(\mathfrak N)$ (e.g. $\Gamma(\mathfrak N)$, $\Gamma_1(\mathfrak N)$, $\Gamma_0(\mathfrak N)$, $\mathrm{SL}_2(\mathcal{O}_F)$), a holomorphic
$\Gamma$-invariant function is a Hilbert modular form: the cusp condition in `modularFormSpace` is redundant.

Sources: Freitag, *Hilbert Modular Forms* (1990), Ch. I §4 [unverified].
-/
import QuadFormsKB.HilbertModular.KoecherBounded

open Matrix NumberField UpperHalfPlane
open scoped MatrixGroups nonZeroDivisors ModularForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

lemma sl2_det (γ : SL(2, F)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rw [det_fin_two] at this; exact this

lemma sl2_inv_apply (γ : SL(2, F)) :
    (γ⁻¹ : SL(2, F)) 0 0 = γ 1 1 ∧ (γ⁻¹ : SL(2, F)) 0 1 = -γ 0 1 ∧
      (γ⁻¹ : SL(2, F)) 1 0 = -γ 1 0 ∧ (γ⁻¹ : SL(2, F)) 1 1 = γ 0 0 := by
  simp

lemma conj_transl_apply (γ : SL(2, F)) (β : F) :
    (γ * transl β * γ⁻¹) 0 0 = 1 - γ 0 0 * γ 1 0 * β ∧
    (γ * transl β * γ⁻¹) 0 1 = γ 0 0 ^ 2 * β ∧
    (γ * transl β * γ⁻¹) 1 0 = -(γ 1 0 ^ 2 * β) ∧
    (γ * transl β * γ⁻¹) 1 1 = 1 + γ 0 0 * γ 1 0 * β := by
  have hd := sl2_det γ
  have e : ∀ i j, (γ * transl β * γ⁻¹) i j = ((γ : Matrix (Fin 2) (Fin 2) F) *
      (transl β : Matrix (Fin 2) (Fin 2) F) * ((γ⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j :=
    fun i j => rfl
  simp only [e, mul_apply, Fin.sum_univ_two]
  have t00 : (transl β : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := rfl
  have t01 : (transl β : Matrix (Fin 2) (Fin 2) F) 0 1 = β := rfl
  have t10 : (transl β : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl
  have t11 : (transl β : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl
  simp only [t00, t01, t10, t11]
  obtain ⟨i0, i1, i2, i3⟩ := sl2_inv_apply γ
  rw [i0, i1, i2, i3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hd
  · ring
  · ring
  · linear_combination hd

lemma conj_diagU_apply (γ : SL(2, F)) (t : Fˣ) :
    (γ * diagU t * γ⁻¹) 0 0 = γ 0 0 * γ 1 1 * t - γ 0 1 * γ 1 0 * ((t⁻¹ : Fˣ) : F) ∧
    (γ * diagU t * γ⁻¹) 0 1 = γ 0 0 * γ 0 1 * (((t⁻¹ : Fˣ) : F) - t) ∧
    (γ * diagU t * γ⁻¹) 1 0 = γ 1 0 * γ 1 1 * (t - ((t⁻¹ : Fˣ) : F)) ∧
    (γ * diagU t * γ⁻¹) 1 1 = γ 0 0 * γ 1 1 * ((t⁻¹ : Fˣ) : F) - γ 0 1 * γ 1 0 * t := by
  have e : ∀ i j, (γ * diagU t * γ⁻¹) i j = ((γ : Matrix (Fin 2) (Fin 2) F) *
      (diagU t : Matrix (Fin 2) (Fin 2) F) * ((γ⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) i j :=
    fun i j => rfl
  simp only [e, mul_apply, Fin.sum_univ_two]
  have t00 : (diagU t : Matrix (Fin 2) (Fin 2) F) 0 0 = t := rfl
  have t01 : (diagU t : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := rfl
  have t10 : (diagU t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := rfl
  have t11 : (diagU t : Matrix (Fin 2) (Fin 2) F) 1 1 = ((t⁻¹ : Fˣ) : F) := rfl
  simp only [t00, t01, t10, t11]
  obtain ⟨i0, i1, i2, i3⟩ := sl2_inv_apply γ
  rw [i0, i1, i2, i3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- A matrix in $\mathrm{SL}_2(F)$ congruent to $1$ modulo $\mathfrak N$ (all entries of $A - 1$ in $\mathfrak N \subseteq \mathcal{O}_F$) lies in
$\Gamma(\mathfrak N)$. -/
lemma mem_GammaFull_of (𝔑 : Ideal (𝓞 F)) (A : SL(2, F)) (r : Fin 2 → Fin 2 → 𝓞 F)
    (hr : ∀ i j, r i j ∈ 𝔑)
    (hA : ∀ i j, A i j = (if i = j then 1 else 0) + algebraMap (𝓞 F) F (r i j)) :
    A ∈ GammaFull 𝔑 := by
  set B : Matrix (Fin 2) (Fin 2) (𝓞 F) := fun i j => (if i = j then 1 else 0) + r i j with hB
  have hmap : B.map (algebraMap (𝓞 F) F) = (A : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    rw [map_apply, hA i j, hB]
    split_ifs <;> simp_all
  have hdet : B.det = 1 := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, A.2, map_one]
  refine ⟨⟨B, hdet⟩, ?_, ?_⟩
  · change SpecialLinearGroup.map (Ideal.Quotient.mk 𝔑) ⟨B, hdet⟩ = 1
    ext i j
    change Ideal.Quotient.mk 𝔑 (B i j) = (1 : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ 𝔑)) i j
    rw [hB, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (hr i j), add_zero, one_apply]
    split_ifs <;> simp
  · ext i j
    change algebraMap (𝓞 F) F (B i j) = A i j
    rw [← hmap]; rfl

/-- A common denominator for the entries of $\gamma \in \mathrm{SL}_2(F)$. -/
lemma exists_denom (γ : SL(2, F)) : ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ i j, ∃ e : 𝓞 F,
    algebraMap (𝓞 F) F e = algebraMap (𝓞 F) F D * γ i j := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰
    (Finset.univ : Finset (Fin 2 × Fin 2)) (fun p => γ p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i j => ?_⟩
  obtain ⟨e, he⟩ := hb (i, j) (Finset.mem_univ _)
  exact ⟨e, by rw [he, Algebra.smul_def]⟩


variable [IsTotallyReal F]

/-- **The cusp hypothesis of `mem_modularFormSpace_of_koecher` holds for every $\Gamma \supseteq \Gamma(\mathfrak N)$**, $\mathfrak N \ne 0$:
for each $\gamma \in \mathrm{SL}_2(F)$, with $D \in \mathcal{O}_F \setminus 0$ a common denominator of the entries of $\gamma$ and
$\mathfrak M = D^2\mathfrak N$, the conjugate $\gamma^{-1}\Gamma\gamma$ contains $T(\beta)$ for $\beta \in \mathfrak M$ and $\mathrm{diag}(u^m, u^{-m})$
for all units $u$, $m = |(\mathcal{O}_F/\mathfrak M)^\times|$ (so $u^m \equiv 1 \bmod \mathfrak M$). -/
theorem koecher_cusp_hyp_of_GammaFull_le (𝔑 : Ideal (𝓞 F)) (h𝔑 : 𝔑 ≠ ⊥)
    {Γ : Subgroup SL(2, F)} (hΓ : GammaFull 𝔑 ≤ Γ) (γ : SL(2, F)) :
    ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∃ m : ℕ, 0 < m ∧
      (∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), γ * transl β * γ⁻¹ ∈ Γ) ∧
      ∀ u : (𝓞 F)ˣ, γ * diagU (unitF u ^ m) * γ⁻¹ ∈ Γ := by
  obtain ⟨D, hD, he⟩ := exists_denom γ
  choose e he using he
  have hd := sl2_det γ
  set 𝔐 : Ideal (𝓞 F) := Ideal.span {D ^ 2} * 𝔑 with h𝔐def
  have h𝔐 : 𝔐 ≠ ⊥ := by
    rw [h𝔐def, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨pow_ne_zero 2 hD, h𝔑⟩
  have := Ideal.finiteQuotientOfFreeOfNeBot 𝔐 h𝔐
  have hI0 : (𝔐 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr h𝔐
  refine ⟨Units.mk0 _ hI0, Nat.card ((𝓞 F ⧸ 𝔐)ˣ), Nat.card_pos, ?_, ?_⟩
  · intro β hβ
    apply hΓ
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hβ
    obtain ⟨z, hz, rfl⟩ := Ideal.mem_span_singleton_mul.mp hx
    obtain ⟨c0, c1, c2, c3⟩ := conj_transl_apply γ (algebraMap (𝓞 F) F (D ^ 2 * z))
    have c0' : (γ * transl (algebraMap (𝓞 F) F (D ^ 2 * z)) * γ⁻¹) 0 0 =
        1 + algebraMap (𝓞 F) F (-(e 0 0 * e 1 0 * z)) := by
      rw [c0]; simp only [map_neg, map_mul, map_pow, he]; ring
    have c1' : (γ * transl (algebraMap (𝓞 F) F (D ^ 2 * z)) * γ⁻¹) 0 1 =
        0 + algebraMap (𝓞 F) F (e 0 0 ^ 2 * z) := by
      rw [c1]; simp only [map_mul, map_pow, he]; ring
    have c2' : (γ * transl (algebraMap (𝓞 F) F (D ^ 2 * z)) * γ⁻¹) 1 0 =
        0 + algebraMap (𝓞 F) F (-(e 1 0 ^ 2 * z)) := by
      rw [c2]; simp only [map_neg, map_mul, map_pow, he]; ring
    have c3' : (γ * transl (algebraMap (𝓞 F) F (D ^ 2 * z)) * γ⁻¹) 1 1 =
        1 + algebraMap (𝓞 F) F (e 0 0 * e 1 0 * z) := by
      rw [c3]; simp only [map_mul, map_pow, he]; ring
    refine mem_GammaFull_of 𝔑 _ ![![-(e 0 0 * e 1 0 * z), e 0 0 ^ 2 * z],
      ![-(e 1 0 ^ 2 * z), e 0 0 * e 1 0 * z]] ?_ ?_
    · intro i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
        cons_val_zero, cons_val_one] <;>
        first | exact Ideal.mul_mem_left _ _ hz | exact neg_mem (Ideal.mul_mem_left _ _ hz)
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cons_val_zero, cons_val_one,
          c0', c1', c2', c3'] <;> simp
  · intro u
    apply hΓ
    set m := Nat.card ((𝓞 F ⧸ 𝔐)ˣ)
    have hpow : ∀ w : (𝓞 F)ˣ, ((w ^ m : (𝓞 F)ˣ) : 𝓞 F) - 1 ∈ 𝔐 := by
      intro w
      have h1 : (Units.map (Ideal.Quotient.mk 𝔐).toMonoidHom w) ^ m = 1 := pow_card_eq_one'
      rw [← Ideal.Quotient.eq]
      have := congrArg Units.val h1
      simpa using this
    obtain ⟨z1, hz1, hz1'⟩ := Ideal.mem_span_singleton_mul.mp (hpow u)
    obtain ⟨z2, hz2, hz2'⟩ := Ideal.mem_span_singleton_mul.mp (hpow u⁻¹)
    have hT : ((unitF u ^ m : Fˣ) : F) = 1 + algebraMap (𝓞 F) F (D ^ 2 * z1) := by
      rw [hz1']; simp [unitF]
    have hS : (((unitF u ^ m)⁻¹ : Fˣ) : F) = 1 + algebraMap (𝓞 F) F (D ^ 2 * z2) := by
      rw [hz2']; simp [unitF]
    obtain ⟨c0, c1, c2, c3⟩ := conj_diagU_apply γ (unitF u ^ m)
    rw [hT, hS] at c0 c1 c2 c3
    have c0' : (γ * diagU (unitF u ^ m) * γ⁻¹) 0 0 =
        1 + algebraMap (𝓞 F) F (e 0 0 * e 1 1 * z1 - e 0 1 * e 1 0 * z2) := by
      rw [c0]; simp only [map_sub, map_mul, map_pow, he]; linear_combination hd
    have c1' : (γ * diagU (unitF u ^ m) * γ⁻¹) 0 1 =
        0 + algebraMap (𝓞 F) F (e 0 0 * e 0 1 * (z2 - z1)) := by
      rw [c1]; simp only [map_sub, map_mul, map_pow, he]; ring
    have c2' : (γ * diagU (unitF u ^ m) * γ⁻¹) 1 0 =
        0 + algebraMap (𝓞 F) F (e 1 0 * e 1 1 * (z1 - z2)) := by
      rw [c2]; simp only [map_sub, map_mul, map_pow, he]; ring
    have c3' : (γ * diagU (unitF u ^ m) * γ⁻¹) 1 1 =
        1 + algebraMap (𝓞 F) F (e 0 0 * e 1 1 * z2 - e 0 1 * e 1 0 * z1) := by
      rw [c3]; simp only [map_sub, map_mul, map_pow, he]; linear_combination hd
    refine mem_GammaFull_of 𝔑 _ ![![e 0 0 * e 1 1 * z1 - e 0 1 * e 1 0 * z2,
      e 0 0 * e 0 1 * (z2 - z1)], ![e 1 0 * e 1 1 * (z1 - z2),
      e 0 0 * e 1 1 * z2 - e 0 1 * e 1 0 * z1]] ?_ ?_
    · intro i j
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
        cons_val_zero, cons_val_one] <;>
        first
        | exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hz1) (Ideal.mul_mem_left _ _ hz2)
        | exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hz2) (Ideal.mul_mem_left _ _ hz1)
        | exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hz2 hz1)
        | exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hz1 hz2)
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cons_val_zero, cons_val_one,
          c0', c1', c2', c3'] <;> simp

/-- **Koecher at every cusp for $\Gamma \supseteq \Gamma(\mathfrak N)$** ($d \ge 2$, $\mathfrak N \ne 0$): every holomorphic $f$ with
$f\,|_k\,\gamma = f$ for $\gamma \in \Gamma$ is in $M_k(\Gamma)$; the cusp condition (bounded at $i\infty$ after every
$\gamma \in \mathrm{SL}_2(F)$) is automatic. Applies to $\Gamma(\mathfrak N)$, $\Gamma_1(\mathfrak N)$, $\Gamma_0(\mathfrak N)$, $\mathrm{SL}_2(\mathcal{O}_F)$. -/
@[kb "freitag1990" "Ch. I, §4, Koecher principle [unverified]"]
theorem mem_modularFormSpace_of_GammaFull_le (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (𝔑 : Ideal (𝓞 F)) (h𝔑 : 𝔑 ≠ ⊥) {Γ : Subgroup SL(2, F)} (hΓ : GammaFull 𝔑 ≤ Γ) {k : ℤ}
    {f : (InfinitePlace F → ℍ) → ℂ} (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f)
    (hf : IsHolomorphic f) : f ∈ modularFormSpace (realEmb F) Γ k :=
  mem_modularFormSpace_of_koecher hd hinv hf (koecher_cusp_hyp_of_GammaFull_le 𝔑 h𝔑 hΓ)

/-- **Koecher for $M_k(\Gamma_0(\mathfrak N))$** ($d \ge 2$, $\mathfrak N \ne 0$): holomorphy and $\Gamma_0(\mathfrak N)$-invariance suffice. -/
theorem mem_modularFormSpace_Gamma0_of_koecher (hd : 2 ≤ Fintype.card (InfinitePlace F))
    (𝔑 : Ideal (𝓞 F)) (h𝔑 : 𝔑 ≠ ⊥) {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hinv : ∀ γ ∈ Gamma0 𝔑, f ∣[k] slHom (realEmb F) γ = f) (hf : IsHolomorphic f) :
    f ∈ modularFormSpace (realEmb F) (Gamma0 𝔑) k :=
  mem_modularFormSpace_of_GammaFull_le hd 𝔑 h𝔑
    ((GammaFull_le_Gamma1 𝔑).trans (Gamma1_le_Gamma0 𝔑)) hinv hf

end QuadFormsKB.HilbertModular
