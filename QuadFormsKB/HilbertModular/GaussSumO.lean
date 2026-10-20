import QuadFormsKB.Siegel.QuadGaussSum

/-!
# Quadratic Gauss sums over $\mathcal{O}/\mathfrak m$ at good moduli

Let $\mathcal{O}$ be the ring of integers of a number field, $S \in M_n(\mathcal{O})$ symmetric, $n = 2k$ even, $q(x) = x^{\mathsf T}Sx$, and
$\mathfrak m \ne 0$ an ideal prime to $2\det S$. For every primitive additive character $\psi$ of $\mathcal{O}/\mathfrak m$
(`AddChar.IsPrimitive`):
$$\sum_{x\in(\mathcal{O}/\mathfrak m)^n}\psi(q(x)) = N(\mathfrak m)^k\,\Big(\frac{(-1)^k\det S}{\mathfrak m}\Big)\qquad
  (\texttt{sum\_addChar\_quadForm\_quot}),$$
where $(\frac{D}{\mathfrak m}) = \prod_{\mathfrak p^e\|\mathfrak m}(\frac{D}{\mathfrak p})^e$ is the Jacobi symbol of $\mathcal{O}$ (`jacobiO`) and
$(\frac D{\mathfrak p})$ the quadratic character of the residue field $\mathcal{O}/\mathfrak p$ (`legendreO`).

*Proof.* Induction over the factorization of $\mathfrak m$ (`UniqueFactorizationMonoid.induction_on_coprime`):
* coprime factors: the Chinese remainder theorem splits the sum (`Ideal.quotientMulEquivQuotientProd`);
* $\mathfrak p$: the finite-field evaluation `QuadFormsKB.Siegel.sum_addChar_quadForm`;
* $\mathfrak p^e \to \mathfrak p^{e-2}$ ($e \ge 2$): with $\pi \in \mathfrak p\setminus\mathfrak p^2$, averaging over $x \mapsto x + \pi^{e-1}w$ restricts
  the sum to $x \in \mathfrak p^n$; then $x = \pi z$ and $\psi(\pi^2q(z))$ only depends on $z \bmod \mathfrak p^{e-2}$, giving
  $G_{\mathfrak p^e} = N(\mathfrak p)^nG_{\mathfrak p^{e-2}}$. Fibre counts come from `sum_comp_addMonoidHom`.

No dyadic prime and no prime dividing $\det S$ occurs: these are excluded by the hypothesis, which is how the theta
multiplier is evaluated (the modulus is the entry $a$ of $\gamma$, moved off the bad primes; see `ThetaCharF.lean`).
Sources: Lidl–Niederreiter, *Finite Fields*, §5.4 and §6.2 [unverified]; Hecke, *Vorlesungen über die Theorie der
algebraischen Zahlen*, §§54–58 [unverified].
-/

open Matrix Finset

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.HilbertModular

noncomputable section

/-! ### Fibre counts -/

/-- **Fibres of a surjective homomorphism of finite groups**: $\sum_{g\in G}f(\varphi(g)) = |\ker\varphi|\sum_{h\in H}f(h)$. -/
theorem sum_comp_addMonoidHom' {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [Fintype H] [DecidableEq H] (φ : G →+ H) (f : H → ℂ) :
    ∑ g, f (φ g) = (Nat.card φ.ker : ℂ) * ∑ h ∈ Finset.univ.filter (fun h => ∃ g, φ g = h), f h := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ.filter (fun h => ∃ g, φ g = h))
    (fun g _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, rfl⟩), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  obtain ⟨g0, rfl⟩ := (Finset.mem_filter.mp hh).2
  have hfib : ∀ g ∈ Finset.univ.filter (fun g => φ g = φ g0), f (φ g) = f (φ g0) := by
    intro g hg; rw [(Finset.mem_filter.mp hg).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have e : {g // g ∈ Finset.univ.filter (fun g => φ g = φ g0)} ≃ φ.ker :=
    { toFun := fun g => ⟨g.1 - g0, by
        have := (Finset.mem_filter.mp g.2).2
        rw [AddMonoidHom.mem_ker, map_sub, this, sub_self]⟩
      invFun := fun x => ⟨x.1 + g0, by
        rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, AddMonoidHom.mem_ker.mp x.2, zero_add]⟩
      left_inv := fun g => by simp
      right_inv := fun x => by simp }
  rw [← Nat.card_eq_finsetCard, Nat.card_congr e]

theorem sum_comp_addMonoidHom {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G]
    [Fintype H] [DecidableEq H] (φ : G →+ H) (hφ : Function.Surjective φ) (f : H → ℂ) :
    ∑ g, f (φ g) = (Nat.card φ.ker : ℂ) * ∑ h, f h := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hfib : ∀ g ∈ Finset.univ.filter (fun g => φ g = h), f (φ g) = f h := by
    intro g hg; rw [(Finset.mem_filter.mp hg).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  congr 1
  obtain ⟨g0, rfl⟩ := hφ h
  have e : {g // g ∈ Finset.univ.filter (fun g => φ g = φ g0)} ≃ φ.ker :=
    { toFun := fun g => ⟨g.1 - g0, by
        have := (Finset.mem_filter.mp g.2).2
        rw [AddMonoidHom.mem_ker, map_sub, this, sub_self]⟩
      invFun := fun x => ⟨x.1 + g0, by
        rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, AddMonoidHom.mem_ker.mp x.2, zero_add]⟩
      left_inv := fun g => by simp
      right_inv := fun x => by simp }
  rw [← Nat.card_eq_finsetCard, Nat.card_congr e]

/-! ### Uniformizers and valuations in a Dedekind domain -/

section Dedekind

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

lemma Ideal.sup_eq_top_of_isRelPrime {I J : Ideal O} (h : IsRelPrime I J) : I ⊔ J = ⊤ := by
  have h1 : I ⊔ J ∣ I := Ideal.dvd_iff_le.mpr le_sup_left
  have h2 : I ⊔ J ∣ J := Ideal.dvd_iff_le.mpr le_sup_right
  exact Ideal.isUnit_iff.mp (h h1 h2)

/-- A uniformizer: $\pi \in \mathfrak p \setminus \mathfrak p^2$, $(\pi) = \mathfrak p\mathfrak a$ with $\mathfrak a + \mathfrak p = 1$. -/
lemma exists_uniformizer {𝔭 : Ideal O} [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) :
    ∃ π : O, ∃ 𝔞 : Ideal O, Ideal.span {π} = 𝔭 * 𝔞 ∧ 𝔞 ⊔ 𝔭 = ⊤ := by
  obtain ⟨π, hπ, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ 𝔭 h0 h𝔭.ne_top 1
  rw [pow_one] at hπ
  have hdvd : 𝔭 ∣ Ideal.span {π} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)
  obtain ⟨𝔞, h𝔞⟩ := hdvd
  refine ⟨π, 𝔞, h𝔞, ?_⟩
  by_contra hne
  have hle : 𝔞 ≤ 𝔭 := by
    have := h𝔭.eq_of_le hne (le_sup_right : 𝔭 ≤ 𝔞 ⊔ 𝔭)
    rw [this]; exact le_sup_left
  apply hπ2
  have : Ideal.span {π} ≤ 𝔭 ^ (1 + 1) := by
    rw [h𝔞, pow_two]; exact Ideal.mul_mono_right hle
  exact (Ideal.span_singleton_le_iff_mem _).mp this

/-- **Valuation**: if $(\pi) = \mathfrak p\mathfrak a$ with $\mathfrak a + \mathfrak p = 1$ and $\pi^mx \in \mathfrak p^{m+j}$, then $x \in \mathfrak p^j$. -/
lemma mem_pow_of_uniformizer_pow_mul_mem {𝔭 𝔞 : Ideal O} (h0 : 𝔭 ≠ ⊥) {π : O}
    (hπ : Ideal.span {π} = 𝔭 * 𝔞) (h𝔞 : 𝔞 ⊔ 𝔭 = ⊤) {m j : ℕ} {x : O}
    (hx : π ^ m * x ∈ 𝔭 ^ (m + j)) : x ∈ 𝔭 ^ j := by
  have h1 : Ideal.span {π ^ m * x} ≤ 𝔭 ^ (m + j) := (Ideal.span_singleton_le_iff_mem _).mpr hx
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hπ, mul_pow,
    pow_add, mul_assoc] at h1
  have h2 : 𝔞 ^ m * Ideal.span {x} ≤ 𝔭 ^ j := by
    have hd : 𝔭 ^ m * 𝔭 ^ j ∣ 𝔭 ^ m * (𝔞 ^ m * Ideal.span {x}) := Ideal.dvd_iff_le.mpr h1
    exact Ideal.dvd_iff_le.mp ((mul_dvd_mul_iff_left (pow_ne_zero m h0)).mp hd)
  have hcop : 𝔞 ^ m ⊔ 𝔭 ^ j = ⊤ := by
    have := ((Ideal.isCoprime_iff_sup_eq).mpr h𝔞).pow (m := m) (n := j)
    exact (Ideal.isCoprime_iff_sup_eq).mp this
  have h3 : (1 : O) ∈ 𝔞 ^ m ⊔ 𝔭 ^ j := by rw [hcop]; trivial
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.mp h3
  have hx' : x = α * x + x * β := by rw [mul_comm α, ← mul_add, hαβ, mul_one]
  rw [hx']
  refine Ideal.add_mem _ (h2 (Ideal.mul_mem_mul hα (Ideal.mem_span_singleton_self x))) ?_
  exact Ideal.mul_mem_left _ _ hβ

/-- $(\pi) + \mathfrak p^e = \mathfrak p$ for $e \ge 1$. -/
lemma span_uniformizer_sup_pow {𝔭 𝔞 : Ideal O} {π : O}
    (hπ : Ideal.span {π} = 𝔭 * 𝔞) (h𝔞 : 𝔞 ⊔ 𝔭 = ⊤) {e : ℕ} (he : 1 ≤ e) :
    Ideal.span {π} ⊔ 𝔭 ^ e = 𝔭 := by
  apply le_antisymm
  · refine sup_le ?_ (Ideal.pow_le_self (I := 𝔭) (show e ≠ 0 by omega))
    rw [hπ]; exact Ideal.mul_le_left (I := 𝔭) (J := 𝔞)
  · intro p hp
    have hcop : 𝔞 ⊔ 𝔭 ^ e = ⊤ := by
      have := ((Ideal.isCoprime_iff_sup_eq).mpr h𝔞).pow (m := 1) (n := e)
      rw [pow_one] at this
      exact (Ideal.isCoprime_iff_sup_eq).mp this
    have h3 : (1 : O) ∈ 𝔞 ⊔ 𝔭 ^ e := by rw [hcop]; trivial
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.mp h3
    have hp' : p = p * α + p * β := by rw [← mul_add, hαβ, mul_one]
    rw [hp']
    refine Submodule.add_mem_sup ?_ (Ideal.mul_mem_left _ _ hβ)
    rw [hπ]; exact Ideal.mul_mem_mul hp hα

end Dedekind

/-! ### Gauss sums over $\mathcal{O}/I$ -/

section GaussQuot

variable {O : Type*} [CommRing O] {n : ℕ}

/-- The reduction $q(x) = x^{\mathsf T}\bar Sx$ of the form $x^{\mathsf T}Sx$ to $\mathcal{O}/I$. -/
@[kb "lidl1997" "§6.2, quadratic forms over finite rings [unverified]"]
def quadQ (I : Ideal O) (S : Matrix (Fin n) (Fin n) O) (x : Fin n → O ⧸ I) : O ⧸ I :=
  x ⬝ᵥ (S.map (Ideal.Quotient.mk I)) *ᵥ x

/-- **The quadratic Gauss sum over $\mathcal{O}/I$** for an additive character $\psi$: $\sum_{x\in(\mathcal{O}/I)^n}\psi(x^{\mathsf T}Sx)$. -/
@[kb "lidl1997" "§5.4, Gauss sums [unverified]"]
def gsQ (I : Ideal O) [Fintype (O ⧸ I)] (S : Matrix (Fin n) (Fin n) O) (ψ : AddChar (O ⧸ I) ℂ) : ℂ :=
  ∑ x : Fin n → O ⧸ I, ψ (quadQ I S x)

lemma addChar_sum {R : Type*} [AddCommMonoid R] {ι : Type*} (ψ : AddChar R ℂ) (s : Finset ι)
    (f : ι → R) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma quadQ_add_smul (I : Ideal O) {S : Matrix (Fin n) (Fin n) O} (hS : Sᵀ = S)
    (x w : Fin n → O ⧸ I) (t : O ⧸ I) (ht : t * t = 0) :
    quadQ I S (x + t • w) = quadQ I S x + ∑ i, w i * (t * (2 * ((S.map (Ideal.Quotient.mk I)) *ᵥ x) i)) := by
  have hSb : (S.map (Ideal.Quotient.mk I))ᵀ = S.map (Ideal.Quotient.mk I) := by
    rw [← transpose_map, hS]
  have hsym : w ⬝ᵥ (S.map (Ideal.Quotient.mk I)) *ᵥ x = x ⬝ᵥ (S.map (Ideal.Quotient.mk I)) *ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hSb, dotProduct_comm]
  have hdot : ∑ i, w i * (t * (2 * ((S.map (Ideal.Quotient.mk I)) *ᵥ x) i)) =
      2 * t * (w ⬝ᵥ (S.map (Ideal.Quotient.mk I)) *ᵥ x) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdot]
  simp only [quadQ, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hsym]
  linear_combination (w ⬝ᵥ (S.map (Ideal.Quotient.mk I)) *ᵥ w) * ht

lemma quadQ_factor {I J : Ideal O} (hIJ : I ≤ J) (S : Matrix (Fin n) (Fin n) O) (x : Fin n → O ⧸ I) :
    quadQ J S (fun i => Ideal.Quotient.factor hIJ (x i)) = Ideal.Quotient.factor hIJ (quadQ I S x) := by
  simp only [quadQ, dotProduct, mulVec, map_sum, map_mul, Matrix.map_apply, Ideal.Quotient.factor_mk]

end GaussQuot

section PrimePower

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {n : ℕ}

lemma isUnit_mk_of_not_mem {𝔭 : Ideal O} [h𝔭 : 𝔭.IsMaximal] {d : O} (hd : d ∉ 𝔭) (e : ℕ) :
    IsUnit (Ideal.Quotient.mk (𝔭 ^ e) d) := by
  have h1 : Ideal.span {d} ⊔ 𝔭 = ⊤ := by
    by_contra hne
    have := h𝔭.eq_of_le hne (le_sup_right : 𝔭 ≤ Ideal.span {d} ⊔ 𝔭)
    exact hd (this ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self d))
  have h2 : Ideal.span {d} ⊔ 𝔭 ^ e = ⊤ := by
    have := ((Ideal.isCoprime_iff_sup_eq).mpr h1).pow (m := 1) (n := e)
    rw [pow_one] at this
    exact (Ideal.isCoprime_iff_sup_eq).mp this
  have h3 : (1 : O) ∈ Ideal.span {d} ⊔ 𝔭 ^ e := by rw [h2]; trivial
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.mp h3
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hα
  refine IsUnit.of_mul_eq_one (b := Ideal.Quotient.mk _ u) ?_
  rw [← map_mul, mul_comm, ← sub_eq_iff_eq_add.mpr hαβ.symm, map_sub, map_one,
    Ideal.Quotient.eq_zero_iff_mem.mpr hβ, sub_zero]

open Classical in
/-- **Step 1** ($e \ge 2$): only $x \in (\mathfrak p/\mathfrak p^e)^n$ contribute to the Gauss sum modulo $\mathfrak p^e$. -/
theorem gsQ_eq_sum_mem {𝔭 𝔞 : Ideal O} [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) {π : O}
    (hπ : Ideal.span {π} = 𝔭 * 𝔞) (h𝔞 : 𝔞 ⊔ 𝔭 = ⊤) {e : ℕ} (he : 2 ≤ e)
    [Fintype (O ⧸ 𝔭 ^ e)] [DecidableEq (O ⧸ 𝔭 ^ e)] {S : Matrix (Fin n) (Fin n) O} (hS : Sᵀ = S)
    (hdet : 2 * S.det ∉ 𝔭) (ψ : AddChar (O ⧸ 𝔭 ^ e) ℂ) (hψ : ψ.IsPrimitive) :
    gsQ (𝔭 ^ e) S ψ = ∑ x ∈ Finset.univ.filter (fun x : Fin n → O ⧸ 𝔭 ^ e =>
      ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e))), ψ (quadQ _ S x) := by
  classical
  have hπ𝔭 : π ∈ 𝔭 := by
    have : π ∈ Ideal.span {π} := Ideal.mem_span_singleton_self π
    rw [hπ] at this; exact Ideal.mul_le_left (I := 𝔭) (J := 𝔞) this
  set t : O ⧸ 𝔭 ^ e := Ideal.Quotient.mk _ (π ^ (e - 1)) with ht_def
  have ht : t * t = 0 := by
    rw [ht_def, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_add]
    exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hπ𝔭 _)
  have h2 : (2 : O) ∉ 𝔭 := fun h => hdet (Ideal.mul_mem_right _ _ h)
  have hdS : S.det ∉ 𝔭 := fun h => hdet (Ideal.mul_mem_left _ _ h)
  -- the key equivalence
  have hiff : ∀ x : Fin n → O ⧸ 𝔭 ^ e,
      (∀ i, t * (2 * ((S.map (Ideal.Quotient.mk _)) *ᵥ x) i) = 0) ↔
        ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e)) := by
    intro x
    have hle : 𝔭 ^ e ≤ 𝔭 := Ideal.pow_le_self (I := 𝔭) (by omega)
    constructor
    · intro hx
      have hSx : ∀ i, ((S.map (Ideal.Quotient.mk _)) *ᵥ x) i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e)) := by
        intro i
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (((S.map (Ideal.Quotient.mk _)) *ᵥ x) i)
        rw [← hy, Ideal.mem_quotient_iff_mem hle]
        have h1 := hx i
        rw [← hy, ht_def, ← map_ofNat (Ideal.Quotient.mk (𝔭 ^ e)) 2, ← map_mul, ← map_mul,
          Ideal.Quotient.eq_zero_iff_mem] at h1
        have h3 : π ^ (e - 1) * (2 * y) ∈ 𝔭 ^ ((e - 1) + 1) := by
          rwa [show e - 1 + 1 = e by omega]
        have h4 := mem_pow_of_uniformizer_pow_mul_mem h0 hπ h𝔞 h3
        rw [pow_one] at h4
        exact ((h𝔭.isPrime.mem_or_mem h4).resolve_left h2)
      have hu : IsUnit (S.map (Ideal.Quotient.mk (𝔭 ^ e))).det := by
        rw [show (S.map (Ideal.Quotient.mk (𝔭 ^ e))).det = Ideal.Quotient.mk (𝔭 ^ e) S.det from
          (RingHom.map_det _ _).symm]
        exact isUnit_mk_of_not_mem hdS e
      have hx' : x = (S.map (Ideal.Quotient.mk (𝔭 ^ e)))⁻¹ *ᵥ ((S.map (Ideal.Quotient.mk _)) *ᵥ x) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
      intro i
      rw [hx']
      simp only [mulVec, dotProduct]
      exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hSx j)
    · intro hx i
      have hSx : ((S.map (Ideal.Quotient.mk _)) *ᵥ x) i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e)) := by
        simp only [mulVec, dotProduct]
        exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (((S.map (Ideal.Quotient.mk _)) *ᵥ x) i)
      rw [← hy, Ideal.mem_quotient_iff_mem hle] at hSx
      rw [← hy, ht_def, ← map_ofNat (Ideal.Quotient.mk (𝔭 ^ e)) 2, ← map_mul, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      have : π ^ (e - 1) * (2 * y) ∈ 𝔭 ^ (e - 1) * 𝔭 :=
        Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ𝔭 _) (Ideal.mul_mem_left _ _ hSx)
      rwa [← pow_succ, show e - 1 + 1 = e by omega] at this
  -- averaging over `x ↦ x + t • w`
  have hcard : (Fintype.card (Fin n → O ⧸ 𝔭 ^ e) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  have hL : ∑ w : Fin n → O ⧸ 𝔭 ^ e, ∑ x, ψ (quadQ _ S (x + t • w)) =
      (Fintype.card (Fin n → O ⧸ 𝔭 ^ e) : ℂ) * gsQ (𝔭 ^ e) S ψ := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun w _ => ?_
    exact Fintype.sum_equiv (Equiv.addRight (t • w)) _ _ fun x => rfl
  rw [← hL]
  simp_rw [quadQ_add_smul _ hS _ _ t ht, AddChar.map_add_eq_mul, addChar_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hprod : ∀ x : Fin n → O ⧸ 𝔭 ^ e, ∑ w : Fin n → O ⧸ 𝔭 ^ e,
      ∏ i, ψ (w i * (t * (2 * ((S.map (Ideal.Quotient.mk _)) *ᵥ x) i))) =
      if ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e)) then
        (Fintype.card (Fin n → O ⧸ 𝔭 ^ e) : ℂ) else 0 := by
    intro x
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (O ⧸ 𝔭 ^ e)))
      (fun i w => ψ (w * (t * (2 * ((S.map (Ideal.Quotient.mk _)) *ᵥ x) i))))]
    simp_rw [AddChar.sum_mulShift _ hψ]
    by_cases h : ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e))
    · rw [ite_eq_left h]
      have h' := (hiff x).mpr h
      rw [Finset.prod_congr rfl fun i _ => by rw [ite_eq_left (h' i)]]
      simp [Fintype.card_pi]
    · rw [ite_eq_right h]
      have h' : ¬ ∀ i, t * (2 * ((S.map (Ideal.Quotient.mk _)) *ᵥ x) i) = 0 :=
        fun h' => h ((hiff x).mp h')
      push Not at h'
      obtain ⟨i, hi⟩ := h'
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [ite_eq_right hi]; simp)
  simp_rw [hprod, mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end PrimePower

/-! ### The scaled character and Step 2 -/

section Scale

variable {O : Type*} [CommRing O]

/-- **The scaled character** $\psi_t(w) = \psi(t\tilde w)$ on $\mathcal{O}/J$ for $tJ \subseteq I$. -/
def scaleChar {I J : Ideal O} (ψ : AddChar (O ⧸ I) ℂ) (t : O) (ht : ∀ y ∈ J, t * y ∈ I) :
    AddChar (O ⧸ J) ℂ where
  toFun w := ψ (Ideal.Quotient.mk I (t * (Ideal.Quotient.mk_surjective w).choose))
  map_zero_eq_one' := by
    have h := (Ideal.Quotient.mk_surjective (0 : O ⧸ J)).choose_spec
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (ht _ h), AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    rw [← AddChar.map_add_eq_mul, ← map_add, ← mul_add]
    congr 1
    rw [Ideal.Quotient.eq, ← mul_sub]
    refine ht _ ?_
    rw [← Ideal.Quotient.eq, map_add, (Ideal.Quotient.mk_surjective (a + b)).choose_spec,
      (Ideal.Quotient.mk_surjective a).choose_spec, (Ideal.Quotient.mk_surjective b).choose_spec]

lemma scaleChar_mk {I J : Ideal O} (ψ : AddChar (O ⧸ I) ℂ) (t : O) (ht : ∀ y ∈ J, t * y ∈ I) (y : O) :
    scaleChar ψ t ht (Ideal.Quotient.mk J y) = ψ (Ideal.Quotient.mk I (t * y)) := by
  show ψ (Ideal.Quotient.mk I (t * (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk J y)).choose)) = _
  congr 1
  rw [Ideal.Quotient.eq, ← mul_sub]
  refine ht _ ?_
  rw [← Ideal.Quotient.eq, (Ideal.Quotient.mk_surjective _).choose_spec]

end Scale

section Step2

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {n : ℕ}

lemma card_quot_pow {𝔭 : Ideal O} [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (j : ℕ) [Fintype (O ⧸ 𝔭 ^ j)] [Fintype (O ⧸ 𝔭)] :
    Fintype.card (O ⧸ 𝔭 ^ j) = Fintype.card (O ⧸ 𝔭) ^ j := by
  have h := cardQuot_pow_of_prime (S := O) (P := 𝔭) h0 (i := j)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at h
  exact h

/-- The kernel of the reduction $(\mathcal{O}/I)^n \to (\mathcal{O}/J)^n$ ($I \le J$) has $(|\mathcal{O}/I|/|\mathcal{O}/J|)^n$
elements: $|\mathcal{O}/I|^n = |\ker|\cdot|\mathcal{O}/J|^n$. -/
lemma card_ker_red {I J : Ideal O} (hIJ : I ≤ J) [Fintype (O ⧸ I)] [Fintype (O ⧸ J)]
    [DecidableEq (O ⧸ J)] :
    ((Fintype.card (O ⧸ I) : ℂ) ^ n) = (Nat.card (AddMonoidHom.compLeft
      (Ideal.Quotient.factor hIJ).toAddMonoidHom (Fin n)).ker : ℂ) * (Fintype.card (O ⧸ J) : ℂ) ^ n := by
  classical
  have hsurj : Function.Surjective (AddMonoidHom.compLeft
      (Ideal.Quotient.factor hIJ).toAddMonoidHom (Fin n)) := by
    intro w
    refine ⟨fun i => (Ideal.Quotient.factor_surjective hIJ (w i)).choose, funext fun i => ?_⟩
    exact (Ideal.Quotient.factor_surjective hIJ (w i)).choose_spec
  have h := sum_comp_addMonoidHom _ hsurj (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    nsmul_eq_mul, mul_one, Fintype.card_fin] at h
  push_cast at h
  exact h

open Classical in
/-- **Step 2** ($e \ge 2$): $\sum_{x\in(\mathfrak p/\mathfrak p^e)^n}\psi(q(x)) = N(\mathfrak p)^n\sum_{z\in(\mathcal{O}/\mathfrak p^{e-2})^n}\psi(\pi^2q(z))$. -/
theorem sum_mem_eq_gsQ {𝔭 𝔞 : Ideal O} [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) {π : O}
    (hπ : Ideal.span {π} = 𝔭 * 𝔞) (h𝔞 : 𝔞 ⊔ 𝔭 = ⊤) {e : ℕ} (he : 2 ≤ e)
    [hfin : ∀ j : ℕ, Fintype (O ⧸ 𝔭 ^ j)] [Fintype (O ⧸ 𝔭)] (S : Matrix (Fin n) (Fin n) O)
    (ψ : AddChar (O ⧸ 𝔭 ^ e) ℂ) (hπ2 : ∀ y ∈ 𝔭 ^ (e - 2), π ^ 2 * y ∈ 𝔭 ^ e) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → O ⧸ 𝔭 ^ e =>
      ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e))), ψ (quadQ _ S x) =
      (Fintype.card (O ⧸ 𝔭) : ℂ) ^ n * gsQ (𝔭 ^ (e - 2)) S (scaleChar ψ (π ^ 2) hπ2) := by
  have hπ𝔭 : π ∈ 𝔭 := by
    have : π ∈ Ideal.span {π} := Ideal.mem_span_singleton_self π
    rw [hπ] at this; exact Ideal.mul_le_left (I := 𝔭) (J := 𝔞) this
  set t : O ⧸ 𝔭 ^ e := Ideal.Quotient.mk _ π with ht_def
  let μ : (Fin n → O ⧸ 𝔭 ^ e) →+ (Fin n → O ⧸ 𝔭 ^ e) :=
    { toFun := fun z => t • z, map_zero' := smul_zero _, map_add' := smul_add _ }
  have hμ : ∀ z, μ z = t • z := fun z => rfl
  have hle1 : 𝔭 ^ e ≤ 𝔭 ^ (e - 1) := Ideal.pow_le_pow_right (by omega)
  have hle2 : 𝔭 ^ e ≤ 𝔭 ^ (e - 2) := Ideal.pow_le_pow_right (by omega)
  have hle : 𝔭 ^ e ≤ 𝔭 := Ideal.pow_le_self (I := 𝔭) (by omega)
  -- the range of `μ`
  have hrange : ∀ x : Fin n → O ⧸ 𝔭 ^ e, (∃ z, μ z = x) ↔ ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e)) := by
    intro x
    constructor
    · rintro ⟨z, rfl⟩ i
      rw [hμ, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπ𝔭)
    · intro hx
      have : ∀ i, ∃ zi, t * zi = x i := by
        intro i
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x i)
        have hy𝔭 : y ∈ 𝔭 := by
          have := hx i; rwa [← hy, Ideal.mem_quotient_iff_mem hle] at this
        rw [← span_uniformizer_sup_pow hπ h𝔞 (e := e) (by omega)] at hy𝔭
        obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Submodule.mem_sup.mp hy𝔭
        obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp ha1
        refine ⟨Ideal.Quotient.mk _ z, ?_⟩
        rw [← hy, ht_def, ← map_mul, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha2, add_zero,
          mul_comm]
      choose z hz using this
      exact ⟨z, funext fun i => by rw [hμ, Pi.smul_apply, smul_eq_mul, hz]⟩
  -- the kernel of `μ` is the kernel of reduction modulo `𝔭^(e-1)`
  set red1 := AddMonoidHom.compLeft (Ideal.Quotient.factor hle1).toAddMonoidHom (Fin n)
  set red2 := AddMonoidHom.compLeft (Ideal.Quotient.factor hle2).toAddMonoidHom (Fin n)
  have hker : μ.ker = red1.ker := by
    ext z
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hμ]
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (z i)
      rw [← hy, ht_def, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hi
      have h3 : π ^ 1 * y ∈ 𝔭 ^ (1 + (e - 1)) := by
        rwa [pow_one, show 1 + (e - 1) = e by omega]
      have h4 := mem_pow_of_uniformizer_pow_mul_mem h0 hπ h𝔞 h3
      show Ideal.Quotient.factor hle1 (z i) = 0
      rw [← hy, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact h4
    · intro h
      funext i
      have hi : Ideal.Quotient.factor hle1 (z i) = 0 := congrFun h i
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (z i)
      rw [← hy, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hi
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hy, ht_def, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have : π * y ∈ 𝔭 * 𝔭 ^ (e - 1) := Ideal.mul_mem_mul hπ𝔭 hi
      rwa [← pow_succ', show e - 1 + 1 = e by omega] at this
  have hsurj2 : Function.Surjective red2 := by
    intro w
    refine ⟨fun i => (Ideal.Quotient.factor_surjective hle2 (w i)).choose, funext fun i => ?_⟩
    exact (Ideal.Quotient.factor_surjective hle2 (w i)).choose_spec
  -- the two fibre counts
  have h1 := sum_comp_addMonoidHom' μ (fun x => ψ (quadQ _ S x))
  have hfilter : Finset.univ.filter (fun h => ∃ g, μ g = h) = Finset.univ.filter (fun x :
      Fin n → O ⧸ 𝔭 ^ e => ∀ i, x i ∈ 𝔭.map (Ideal.Quotient.mk (𝔭 ^ e))) :=
    Finset.filter_congr fun x _ => hrange x
  rw [hfilter] at h1
  have hterm : ∀ z, ψ (quadQ _ S (μ z)) = scaleChar ψ (π ^ 2) hπ2 (quadQ (𝔭 ^ (e - 2)) S (red2 z)) := by
    intro z
    have : red2 z = fun i => Ideal.Quotient.factor hle2 (z i) := rfl
    rw [this, quadQ_factor]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (quadQ (𝔭 ^ e) S z)
    rw [← hy, Ideal.Quotient.factor_mk, scaleChar_mk, map_mul, hy, map_pow, ← ht_def, hμ]
    congr 1
    simp only [quadQ, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  simp_rw [hterm] at h1
  have h2 := sum_comp_addMonoidHom red2 hsurj2 (fun w => scaleChar ψ (π ^ 2) hπ2 (quadQ _ S w))
  rw [h2, hker] at h1
  -- cardinalities
  have hc1 := card_ker_red (n := n) hle1
  have hc2 := card_ker_red (n := n) hle2
  rw [card_quot_pow h0, card_quot_pow h0] at hc1 hc2
  set N : ℂ := (Fintype.card (O ⧸ 𝔭) : ℂ) with hN
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  push_cast at hc1 hc2
  rw [← hN] at hc1 hc2
  have hk1 : (Nat.card red1.ker : ℂ) = N ^ n := by
    have : (N ^ (e - 1)) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hN0)
    apply mul_right_cancel₀ this
    rw [← hc1, ← mul_pow, ← pow_succ', show e - 1 + 1 = e by omega]
  have hk2 : (Nat.card red2.ker : ℂ) = N ^ n * N ^ n := by
    have : (N ^ (e - 2)) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hN0)
    apply mul_right_cancel₀ this
    rw [← hc2, ← mul_pow, ← mul_pow]
    congr 1
    rw [← pow_two, ← pow_add, show 2 + (e - 2) = e by omega]
  rw [hk1, hk2] at h1
  have hNn : N ^ n ≠ 0 := pow_ne_zero _ hN0
  apply mul_left_cancel₀ hNn
  rw [← h1, gsQ]
  ring

end Step2

/-! ### Legendre and Jacobi symbols of $\mathcal{O}$ -/

section Symbols

variable {O : Type*} [CommRing O]

open Classical in
/-- **The Legendre symbol** $(\frac D{\mathfrak p}) \in \{0, \pm1\}$: $0$ if $D \in \mathfrak p$, $1$ if $D$ is a nonzero square modulo $\mathfrak p$,
$-1$ otherwise. For $\mathfrak p$ maximal with finite residue field it is the quadratic character of $\mathcal{O}/\mathfrak p$ at $D$
(`quadraticChar_mk_eq_legendreO`). -/
@[kb "neukirch1999" "Ch. V §3, the power residue symbol [unverified]"]
def legendreO (D : O) (𝔭 : Ideal O) : ℤ :=
  if D ∈ 𝔭 then 0 else if ∃ y : O, y * y - D ∈ 𝔭 then 1 else -1

/-- **The Jacobi symbol** $(\frac D{\mathfrak m}) = \prod_{\mathfrak p}(\frac D{\mathfrak p})^{v_{\mathfrak p}(\mathfrak m)}$ (product over the prime
factors of $\mathfrak m$ with multiplicity, `UniqueFactorizationMonoid.normalizedFactors`). -/
@[kb "neukirch1999" "Ch. V §3, the power residue symbol [unverified]"]
def jacobiO [IsDedekindDomain O] (D : O) (𝔪 : Ideal O) : ℤ :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔪).map (legendreO D)).prod

lemma legendreO_sq_eq_one {D : O} {𝔭 : Ideal O} (hD : D ∉ 𝔭) : legendreO D 𝔭 ^ 2 = 1 := by
  classical
  unfold legendreO
  rw [ite_eq_right hD]
  split_ifs <;> norm_num

lemma quadraticChar_mk_eq_legendreO {𝔭 : Ideal O} [𝔭.IsMaximal] [Fintype (O ⧸ 𝔭)]
    [DecidableEq (O ⧸ 𝔭)] (D : O) :
    @quadraticChar (O ⧸ 𝔭) (Ideal.Quotient.field 𝔭) _ _ (Ideal.Quotient.mk 𝔭 D) = legendreO D 𝔭 := by
  classical
  letI := Ideal.Quotient.field 𝔭
  show quadraticCharFun (O ⧸ 𝔭) (Ideal.Quotient.mk 𝔭 D) = _
  unfold quadraticCharFun legendreO
  have h0 : Ideal.Quotient.mk 𝔭 D = 0 ↔ D ∈ 𝔭 := Ideal.Quotient.eq_zero_iff_mem
  have h1 : IsSquare (Ideal.Quotient.mk 𝔭 D) ↔ ∃ y : O, y * y - D ∈ 𝔭 := by
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨y, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hr, sub_self]
    · rintro ⟨y, hy⟩
      refine ⟨Ideal.Quotient.mk 𝔭 y, ?_⟩
      rw [← map_mul, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hy
  by_cases hD : D ∈ 𝔭
  · rw [ite_eq_left (h0.mpr hD), ite_eq_left hD]
  · rw [ite_eq_right (fun h => hD (h0.mp h)), ite_eq_right hD]
    by_cases hs : ∃ y : O, y * y - D ∈ 𝔭
    · rw [ite_eq_left (h1.mpr hs), ite_eq_left hs]
    · rw [ite_eq_right (fun h => hs (h1.mp h)), ite_eq_right hs]

end Symbols

/-! ### The cases $\mathfrak m = 1$, $\mathfrak m = \mathfrak p$, and transport -/

section Cases

variable {O : Type*} [CommRing O] {n : ℕ}

lemma gsQ_congr_inst (I : Ideal O) (i1 i2 : Fintype (O ⧸ I)) (S : Matrix (Fin n) (Fin n) O)
    (ψ : AddChar (O ⧸ I) ℂ) : @gsQ O _ n I i1 S ψ = @gsQ O _ n I i2 S ψ := by
  rw [Subsingleton.elim i1 i2]

/-- Transport along an equality of ideals. -/
lemma gsQ_of_eq {I J : Ideal O} (h : I = J) [Fintype (O ⧸ I)] [Fintype (O ⧸ J)]
    (S : Matrix (Fin n) (Fin n) O) (ψ : AddChar (O ⧸ I) ℂ) :
    gsQ I S ψ = gsQ J S (ψ.compAddMonoidHom (Ideal.quotEquivOfEq h).symm.toRingHom.toAddMonoidHom) := by
  subst h
  rw [gsQ_congr_inst I _ ‹Fintype (O ⧸ I)›]
  unfold gsQ
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (quadQ I S x)
  simp only [AddChar.compAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← hz]
  rfl

lemma isPrimitive_comp_equiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {ψ : AddChar B ℂ} (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.toRingHom.toAddMonoidHom).IsPrimitive := by
  intro r hr h
  apply hψ (show e r ≠ 0 by simpa using hr)
  ext y
  have := congrArg (fun χ : AddChar A ℂ => χ (e.symm y)) h
  simpa [AddChar.mulShift_apply] using this

lemma gsQ_top [Fintype (O ⧸ (⊤ : Ideal O))] (S : Matrix (Fin n) (Fin n) O)
    (ψ : AddChar (O ⧸ (⊤ : Ideal O)) ℂ) : gsQ ⊤ S ψ = 1 := by
  have : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have hu : Unique (Fin n → O ⧸ (⊤ : Ideal O)) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  have h0 : ∀ y : O ⧸ (⊤ : Ideal O), y = 0 := fun y => Subsingleton.elim y 0
  rw [gsQ, Fintype.sum_unique, h0 (quadQ _ _ _), AddChar.map_zero_eq_one]

end Cases

section Field

variable {O : Type*} [CommRing O] {n : ℕ}

/-- **The case $\mathfrak m = \mathfrak p$** (residue field of odd characteristic, $\det S$ a unit): the finite-field evaluation. -/
theorem gsQ_maximal {𝔭 : Ideal O} [h𝔭 : 𝔭.IsMaximal] [Fintype (O ⧸ 𝔭)]
    {S : Matrix (Fin n) (Fin n) O} (hS : Sᵀ = S) (hdet : 2 * S.det ∉ 𝔭) {k : ℕ} (hn : n = 2 * k)
    (ψ : AddChar (O ⧸ 𝔭) ℂ) (hψ : ψ.IsPrimitive) :
    gsQ 𝔭 S ψ = (legendreO ((-1) ^ k * S.det) 𝔭 : ℂ) * (Fintype.card (O ⧸ 𝔭) : ℂ) ^ k := by
  classical
  letI := Ideal.Quotient.field 𝔭
  have h2 : (2 : O) ∉ 𝔭 := fun h => hdet (Ideal.mul_mem_right _ _ h)
  have hdS : S.det ∉ 𝔭 := fun h => hdet (Ideal.mul_mem_left _ _ h)
  have hK : ringChar (O ⧸ 𝔭) ≠ 2 := by
    intro h
    have h' : ((2 : ℕ) : O ⧸ 𝔭) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
    apply h2
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact_mod_cast h'
  set M : Matrix (Fin n) (Fin n) (O ⧸ 𝔭) := S.map (Ideal.Quotient.mk 𝔭) with hMdef
  have hM : Mᵀ = M := by rw [hMdef, ← transpose_map, hS]
  have hdetM : M.det = Ideal.Quotient.mk 𝔭 S.det := (RingHom.map_det _ _).symm
  have hdetM0 : M.det ≠ 0 := by
    rw [hdetM]; exact fun h => hdS (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h := QuadFormsKB.Siegel.sum_addChar_quadForm hK hψ hn M hM hdetM0 (one_ne_zero)
  simp only [one_mul] at h
  rw [gsQ]
  simp only [quadQ]
  rw [← hMdef, h, hdetM]
  congr 1
  rw [QuadFormsKB.Siegel.quadCharC, MulChar.ringHomComp_apply,
    show (-1 : O ⧸ 𝔭) ^ k * Ideal.Quotient.mk 𝔭 S.det = Ideal.Quotient.mk 𝔭 ((-1) ^ k * S.det) by
      simp, quadraticChar_mk_eq_legendreO]
  simp

end Field

/-! ### Prime powers -/

section PrimePowerEval

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {n : ℕ}

lemma gsQ_of_subsingleton {I : Ideal O} [Fintype (O ⧸ I)] [Subsingleton (O ⧸ I)]
    (S : Matrix (Fin n) (Fin n) O) (ψ : AddChar (O ⧸ I) ℂ) : gsQ I S ψ = 1 := by
  have hu : Unique (Fin n → O ⧸ I) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  have h0 : ∀ y : O ⧸ I, y = 0 := fun y => Subsingleton.elim y 0
  rw [gsQ, Fintype.sum_unique, h0 (quadQ _ _ _), AddChar.map_zero_eq_one]

lemma scaleChar_isPrimitive {𝔭 𝔞 : Ideal O} (h0 : 𝔭 ≠ ⊥) {π : O}
    (hπ : Ideal.span {π} = 𝔭 * 𝔞) (h𝔞 : 𝔞 ⊔ 𝔭 = ⊤) {e : ℕ} (he : 2 ≤ e)
    {ψ : AddChar (O ⧸ 𝔭 ^ e) ℂ} (hψ : ψ.IsPrimitive) (hπ2 : ∀ y ∈ 𝔭 ^ (e - 2), π ^ 2 * y ∈ 𝔭 ^ e) :
    (scaleChar ψ (π ^ 2) hπ2).IsPrimitive := by
  intro r hr h
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hy : y ∉ 𝔭 ^ (e - 2) := fun hy => hr (Ideal.Quotient.eq_zero_iff_mem.mpr hy)
  have hne : Ideal.Quotient.mk (𝔭 ^ e) (π ^ 2 * y) ≠ 0 := by
    intro h0'
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0'
    apply hy
    exact mem_pow_of_uniformizer_pow_mul_mem h0 hπ h𝔞 (by rwa [show 2 + (e - 2) = e by omega])
  apply hψ hne
  ext z
  obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
  have := congrArg (fun χ : AddChar (O ⧸ 𝔭 ^ (e - 2)) ℂ => χ (Ideal.Quotient.mk _ z')) h
  simp only [AddChar.mulShift_apply, ← map_mul, scaleChar_mk, AddChar.one_apply] at this
  simp only [AddChar.mulShift_apply, ← map_mul, AddChar.one_apply]
  rw [← this, mul_assoc]

/-- **Gauss sums modulo a prime power** ($\mathfrak p \nmid 2\det S$, $n = 2k$, $\psi$ primitive):
$\sum_{x\in(\mathcal{O}/\mathfrak p^e)^n}\psi(q(x)) = (\frac{(-1)^k\det S}{\mathfrak p})^eN(\mathfrak p)^{ek}$. -/
theorem gsQ_prime_pow {𝔭 : Ideal O} [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥)
    [hfin : ∀ j : ℕ, Fintype (O ⧸ 𝔭 ^ j)] [Fintype (O ⧸ 𝔭)] {S : Matrix (Fin n) (Fin n) O}
    (hS : Sᵀ = S) (hdet : 2 * S.det ∉ 𝔭) {k : ℕ} (hn : n = 2 * k) :
    ∀ (e : ℕ) (ψ : AddChar (O ⧸ 𝔭 ^ e) ℂ), ψ.IsPrimitive →
      gsQ (𝔭 ^ e) S ψ = (legendreO ((-1) ^ k * S.det) 𝔭 : ℂ) ^ e *
        (Fintype.card (O ⧸ 𝔭) : ℂ) ^ (e * k) := by
  classical
  have hdS : S.det ∉ 𝔭 := fun h => hdet (Ideal.mul_mem_left _ _ h)
  have hD : (-1) ^ k * S.det ∉ 𝔭 := by
    intro h
    rcases h𝔭.isPrime.mem_or_mem h with h1 | h1
    · exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr (by
        have := Ideal.mul_mem_left 𝔭 ((-1) ^ k) h1
        rwa [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow] at this))
    · exact hdS h1
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro ψ hψ
  rcases Nat.lt_or_ge e 2 with he | he
  · interval_cases e
    · have : Subsingleton (O ⧸ 𝔭 ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
      rw [gsQ_of_subsingleton]; simp
    · rw [gsQ_of_eq (pow_one 𝔭), gsQ_maximal hS hdet hn _
        (isPrimitive_comp_equiv _ hψ), pow_one, one_mul]
  · obtain ⟨π, 𝔞, hπ, h𝔞⟩ := exists_uniformizer h0
    have hπ𝔭 : π ∈ 𝔭 := by
      have : π ∈ Ideal.span {π} := Ideal.mem_span_singleton_self π
      rw [hπ] at this; exact Ideal.mul_le_left (I := 𝔭) (J := 𝔞) this
    have hπ2 : ∀ y ∈ 𝔭 ^ (e - 2), π ^ 2 * y ∈ 𝔭 ^ e := by
      intro y hy
      have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ𝔭 2) hy
      rwa [← pow_add, show 2 + (e - 2) = e by omega] at this
    rw [gsQ_eq_sum_mem h0 hπ h𝔞 he hS hdet ψ hψ, sum_mem_eq_gsQ h0 hπ h𝔞 he S ψ hπ2,
      ih (e - 2) (by omega) _ (scaleChar_isPrimitive h0 hπ h𝔞 he hψ hπ2)]
    have hsq : (legendreO ((-1) ^ k * S.det) 𝔭 : ℂ) ^ 2 = 1 := by
      exact_mod_cast legendreO_sq_eq_one hD
    have he' : e = (e - 2) + 2 := by omega
    conv_rhs => rw [he', pow_add, hsq, mul_one, add_mul, pow_add]
    have hnk : (Fintype.card (O ⧸ 𝔭) : ℂ) ^ n = (Fintype.card (O ⧸ 𝔭) : ℂ) ^ (2 * k) := by rw [hn]
    rw [hnk]
    ring

end PrimePowerEval

/-! ### The Chinese remainder theorem and the general modulus -/

section CRT

variable {O : Type*} [CommRing O] {n : ℕ}

/-- The CRT isomorphism $\mathcal{O}/\mathfrak a\mathfrak b \simeq \mathcal{O}/\mathfrak a \times \mathcal{O}/\mathfrak b$. -/
def crtEquiv {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) : O ⧸ 𝔞 * 𝔟 ≃+* (O ⧸ 𝔞) × O ⧸ 𝔟 :=
  Ideal.quotientMulEquivQuotientProd 𝔞 𝔟 ((Ideal.isCoprime_iff_sup_eq).mpr hcop)

/-- The left component of a character of $\mathcal{O}/\mathfrak a\mathfrak b$. -/
def crtLeft {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) (ψ : AddChar (O ⧸ 𝔞 * 𝔟) ℂ) : AddChar (O ⧸ 𝔞) ℂ :=
  ψ.compAddMonoidHom (((crtEquiv hcop).symm.toRingHom.toAddMonoidHom).comp (AddMonoidHom.inl _ _))

/-- The right component of a character of $\mathcal{O}/\mathfrak a\mathfrak b$. -/
def crtRight {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) (ψ : AddChar (O ⧸ 𝔞 * 𝔟) ℂ) : AddChar (O ⧸ 𝔟) ℂ :=
  ψ.compAddMonoidHom (((crtEquiv hcop).symm.toRingHom.toAddMonoidHom).comp (AddMonoidHom.inr _ _))

lemma crt_split {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) (ψ : AddChar (O ⧸ 𝔞 * 𝔟) ℂ) (y : O ⧸ 𝔞 * 𝔟) :
    ψ y = crtLeft hcop ψ ((crtEquiv hcop y).1) * crtRight hcop ψ ((crtEquiv hcop y).2) := by
  rw [crtLeft, crtRight, AddChar.compAddMonoidHom_apply, AddChar.compAddMonoidHom_apply,
    ← AddChar.map_add_eq_mul]
  congr 1
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
    AddMonoidHom.inr_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ← map_add, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta, RingEquiv.symm_apply_apply]

lemma crtLeft_isPrimitive {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) {ψ : AddChar (O ⧸ 𝔞 * 𝔟) ℂ}
    (hψ : ψ.IsPrimitive) : (crtLeft hcop ψ).IsPrimitive := by
  intro r hr h
  apply hψ (show (crtEquiv hcop).symm (r, 0) ≠ 0 by
    intro h0; apply hr
    have := congrArg (fun x => (crtEquiv hcop x).1) h0
    simpa using this)
  ext z
  have := congrArg (fun χ : AddChar (O ⧸ 𝔞) ℂ => χ ((crtEquiv hcop z).1)) h
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this ⊢
  rw [← this, crtLeft, AddChar.compAddMonoidHom_apply]
  congr 1
  apply (crtEquiv hcop).injective
  simp only [map_mul, RingEquiv.apply_symm_apply]
  ext <;> simp

lemma crtRight_isPrimitive {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) {ψ : AddChar (O ⧸ 𝔞 * 𝔟) ℂ}
    (hψ : ψ.IsPrimitive) : (crtRight hcop ψ).IsPrimitive := by
  intro r hr h
  apply hψ (show (crtEquiv hcop).symm (0, r) ≠ 0 by
    intro h0; apply hr
    have := congrArg (fun x => (crtEquiv hcop x).2) h0
    simpa using this)
  ext z
  have := congrArg (fun χ : AddChar (O ⧸ 𝔟) ℂ => χ ((crtEquiv hcop z).2)) h
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this ⊢
  rw [← this, crtRight, AddChar.compAddMonoidHom_apply]
  congr 1
  apply (crtEquiv hcop).injective
  simp only [map_mul, RingEquiv.apply_symm_apply]
  ext <;> simp

/-- **CRT for Gauss sums**: $G_{\mathfrak a\mathfrak b}(\psi) = G_{\mathfrak a}(\psi_1)G_{\mathfrak b}(\psi_2)$ for coprime $\mathfrak a, \mathfrak b$. -/
theorem gsQ_mul {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) [Fintype (O ⧸ 𝔞)] [Fintype (O ⧸ 𝔟)]
    [Fintype (O ⧸ 𝔞 * 𝔟)] (S : Matrix (Fin n) (Fin n) O) (ψ : AddChar (O ⧸ 𝔞 * 𝔟) ℂ) :
    gsQ (𝔞 * 𝔟) S ψ = gsQ 𝔞 S (crtLeft hcop ψ) * gsQ 𝔟 S (crtRight hcop ψ) := by
  set E : (Fin n → O ⧸ 𝔞 * 𝔟) ≃ (Fin n → O ⧸ 𝔞) × (Fin n → O ⧸ 𝔟) :=
    (Equiv.piCongrRight fun _ => (crtEquiv hcop).toEquiv).trans
      (Equiv.arrowProdEquivProdArrow _ _ _) with hE
  rw [gsQ, gsQ, gsQ, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv E _ _ fun x => ?_
  rw [crt_split hcop ψ]
  congr 2
  · have : (E x).1 = fun i => Ideal.Quotient.factor (Ideal.mul_le_left (I := 𝔞) (J := 𝔟)) (x i) := by
      funext i; simp [hE, crtEquiv, Equiv.arrowProdEquivProdArrow]
    rw [this, quadQ_factor]
    simp [crtEquiv]
  · have : (E x).2 = fun i => Ideal.Quotient.factor (Ideal.mul_le_right (I := 𝔞) (J := 𝔟)) (x i) := by
      funext i; simp [hE, crtEquiv, Equiv.arrowProdEquivProdArrow]
    rw [this, quadQ_factor]
    simp [crtEquiv]

lemma card_quot_mul {𝔞 𝔟 : Ideal O} (hcop : 𝔞 ⊔ 𝔟 = ⊤) [Fintype (O ⧸ 𝔞)] [Fintype (O ⧸ 𝔟)]
    [Fintype (O ⧸ 𝔞 * 𝔟)] :
    Fintype.card (O ⧸ 𝔞 * 𝔟) = Fintype.card (O ⧸ 𝔞) * Fintype.card (O ⧸ 𝔟) := by
  rw [Fintype.card_congr (crtEquiv hcop).toEquiv, Fintype.card_prod]

end CRT

/-! ### The general good modulus -/

section General

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {n : ℕ}

lemma jacobiO_top (D : O) : jacobiO D ⊤ = 1 := by
  rw [jacobiO, ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]; simp

lemma jacobiO_mul (D : O) {𝔞 𝔟 : Ideal O} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    jacobiO D (𝔞 * 𝔟) = jacobiO D 𝔞 * jacobiO D 𝔟 := by
  rw [jacobiO, UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add,
    Multiset.prod_add, jacobiO, jacobiO]

lemma jacobiO_prime_pow (D : O) {𝔭 : Ideal O} (hp : Prime 𝔭) (e : ℕ) :
    jacobiO D (𝔭 ^ e) = legendreO D 𝔭 ^ e := by
  rw [jacobiO, UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible, normalize_eq,
    Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul, Multiset.prod_singleton]

lemma natCard_quot_pow {𝔭 : Ideal O} [𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) (j : ℕ) :
    Nat.card (O ⧸ 𝔭 ^ j) = Nat.card (O ⧸ 𝔭) ^ j := by
  have h := cardQuot_pow_of_prime (S := O) (P := 𝔭) h0 (i := j)
  rwa [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h

/-- **Quadratic Gauss sums at a good modulus.** Let $\mathcal{O}$ be a Dedekind domain with finite residue rings
(`hfin`), $S \in M_n(\mathcal{O})$ symmetric, $n = 2k$, $\mathfrak m \ne 0$ with $\mathfrak m + (2\det S) = \mathcal{O}$, and $\psi$ a primitive
additive character of $\mathcal{O}/\mathfrak m$. Then
$$\sum_{x\in(\mathcal{O}/\mathfrak m)^n}\psi(x^{\mathsf T}Sx) = \Big(\frac{(-1)^k\det S}{\mathfrak m}\Big)N(\mathfrak m)^k,\qquad N(\mathfrak m) = |\mathcal{O}/\mathfrak m|.$$
For $\mathcal{O} = \mathbb{Z}$ and $\mathfrak m = (p)$ this is `QuadFormsKB.Siegel.gaussSum_prime`. -/
@[kb "lidl1997" "Thm. 5.33, §6.2 (finite fields); Hecke 1923 §§54–58 (moduli) [unverified]"]
theorem gsQ_eval (hfin : ∀ I : Ideal O, I ≠ ⊥ → Finite (O ⧸ I)) {S : Matrix (Fin n) (Fin n) O}
    (hS : Sᵀ = S) {k : ℕ} (hn : n = 2 * k) (𝔪 : Ideal O) (h𝔪 : 𝔪 ≠ ⊥)
    (hcop : 𝔪 ⊔ Ideal.span {2 * S.det} = ⊤) [Fintype (O ⧸ 𝔪)] (ψ : AddChar (O ⧸ 𝔪) ℂ)
    (hψ : ψ.IsPrimitive) :
    gsQ 𝔪 S ψ = (jacobiO ((-1) ^ k * S.det) 𝔪 : ℂ) * (Nat.card (O ⧸ 𝔪) : ℂ) ^ k := by
  classical
  revert h𝔪 hcop ψ
  rename_i inst
  revert inst
  induction 𝔪 using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => intro _ h; exact absurd rfl h
  | h1 hu =>
    intro inst _ _ ψ _
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Unique (O ⧸ (⊤ : Ideal O)) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
    rw [gsQ_of_subsingleton, jacobiO_top, Nat.card_unique]; simp
  | hpr i hp =>
    rename_i 𝔭
    intro inst h𝔪 hcop ψ hψ
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have : Subsingleton (O ⧸ 𝔭 ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
      have : Unique (O ⧸ 𝔭 ^ 0) := { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
      rw [gsQ_of_subsingleton, Nat.card_unique, jacobiO_prime_pow _ hp, pow_zero]; simp
    have h𝔭0 : 𝔭 ≠ ⊥ := fun h => h𝔪 (by rw [h, Ideal.bot_pow (by omega)])
    have h𝔭 : 𝔭.IsPrime := Ideal.isPrime_of_prime hp
    haveI : 𝔭.IsMaximal := h𝔭.isMaximal h𝔭0
    letI hf : ∀ j : ℕ, Fintype (O ⧸ 𝔭 ^ j) := fun j =>
      @Fintype.ofFinite _ (hfin _ (pow_ne_zero _ h𝔭0))
    letI : Fintype (O ⧸ 𝔭) := @Fintype.ofFinite _ (hfin _ h𝔭0)
    have hdet : 2 * S.det ∉ 𝔭 := by
      intro h
      have hle : 𝔭 ^ i ⊔ Ideal.span {2 * S.det} ≤ 𝔭 :=
        sup_le (Ideal.pow_le_self (I := 𝔭) (by omega)) ((Ideal.span_singleton_le_iff_mem _).mpr h)
      rw [hcop] at hle
      exact h𝔭.ne_top (top_le_iff.mp hle)
    rw [gsQ_congr_inst _ inst (hf i), gsQ_prime_pow h𝔭0 hS hdet hn i ψ hψ, jacobiO_prime_pow _ hp,
      natCard_quot_pow h𝔭0, Nat.card_eq_fintype_card (α := O ⧸ 𝔭)]
    push_cast
    ring
  | hcp hxy hx hy =>
    intro inst h𝔪 hcop ψ hψ
    rename_i 𝔞 𝔟
    have h𝔞 : 𝔞 ≠ ⊥ := fun h => h𝔪 (by rw [h, Ideal.bot_mul])
    have h𝔟 : 𝔟 ≠ ⊥ := fun h => h𝔪 (by rw [h, Ideal.mul_bot])
    have hab := Ideal.sup_eq_top_of_isRelPrime hxy
    have hc𝔞 : 𝔞 ⊔ Ideal.span {2 * S.det} = ⊤ :=
      top_le_iff.mp (hcop ▸ sup_le_sup_right (Ideal.mul_le_left (I := 𝔞) (J := 𝔟)) _)
    have hc𝔟 : 𝔟 ⊔ Ideal.span {2 * S.det} = ⊤ :=
      top_le_iff.mp (hcop ▸ sup_le_sup_right (Ideal.mul_le_right (I := 𝔞) (J := 𝔟)) _)
    letI : Fintype (O ⧸ 𝔞) := @Fintype.ofFinite _ (hfin _ h𝔞)
    letI : Fintype (O ⧸ 𝔟) := @Fintype.ofFinite _ (hfin _ h𝔟)
    rw [gsQ_mul hab S ψ, hx h𝔞 hc𝔞 _ (crtLeft_isPrimitive hab hψ),
      hy h𝔟 hc𝔟 _ (crtRight_isPrimitive hab hψ), jacobiO_mul _ h𝔞 h𝔟,
      Nat.card_congr (crtEquiv hab).toEquiv, Nat.card_prod]
    push_cast
    ring

end General

end

end QuadFormsKB.HilbertModular
