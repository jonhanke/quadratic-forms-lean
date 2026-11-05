/-
# O'Meara §95: step 3 of the proof of 95:1, $(O'_4 : \Omega_4) \le 2$

**Setting.** A field $F$ with $2 \ne 0$ and a regular finite-dimensional quadratic space $(V, Q)$ over $F$ (as in
`Sec55.lean`), together with $\Delta, \pi \in \dot F$ such that every $x \in \dot F$ is $s^2$ times one of
$1, \Delta, \pi, \pi\Delta$ (`hcls`) and $\Delta^m\pi^n \in \dot F^2$ only for $m, n$ even (`hsq`): the square classes
of a non-dyadic local field (`Sec95Classes.lean`). Vectors $y_0, \dots, y_3$ with $Q(y_i) = 1, \Delta, \pi, \pi\Delta$
are given.

**Proves** `S95.mem_omega_or_of_classes` (O'Meara 1973 printing, proof of 95:1, step 3, pp. 281–282): every
$\sigma \in O'(V)$ lies in $\Omega(V)$ or in $\tau_{y_0}\tau_{y_1}\tau_{y_2}\tau_{y_3}\Omega(V)$. The book argues with
a factorization into four symmetries; here the factorization is arbitrary: writing
$\sigma = \tau_{u_1}\cdots\tau_{u_r}$ and $n_i$ for the number of $u_k$ with $Q(u_k)$ in the class $i$, the
coset $\sigma\Omega$ is $\prod_i (\tau_{y_i}\Omega)^{n_i}$ (by 55:3), and $\theta(\sigma) = 1$, $r$ even force all
$n_i$ to have the same parity.
-/
import QuadFormsKB.Literature.OMeara.Sec95Omega

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open Cl54

namespace S95

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The class of the symmetry $\tau_u$ in the abelianization of $O(V)$ depends only on the square class of
$Q(u)$. -/
theorem of_tauHat_eq_of_sq (hQ : (QuadraticMap.associated Q).Nondegenerate) {u w : V} (hw : Q w ≠ 0) {s : F}
    (hs : s ≠ 0) (h : Q u = s ^ 2 * Q w) :
    Abelianization.of (Sp55.tauHat Q u) = Abelianization.of (Sp55.tauHat Q w) := by
  have hu : Q u ≠ 0 := by rw [h]; exact mul_ne_zero (pow_ne_zero 2 hs) hw
  have hsu : Q (s⁻¹ • u) = Q w := by
    rw [Q_smul, h]; field_simp
  have hsu0 : Q (s⁻¹ • u) ≠ 0 := by rw [hsu]; exact hw
  have e : Sp55.tauHat Q (s⁻¹ • u) = Sp55.tauHat Q u := by
    apply Subtype.ext
    rw [Sp55.coe_tauHat Q hsu0, Sp55.coe_tauHat Q hu, Sp55.symmetry_smul_vec Q (inv_ne_zero hs) hu]
  rw [← e]
  exact Sp55.of_tauHat_eq Q hQ hsu

theorem of_tauHat_sq {u : V} (hu : Q u ≠ 0) : Abelianization.of (Sp55.tauHat Q u) ^ 2 = 1 := by
  rw [← map_pow]
  have : Sp55.tauHat Q u ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two, Subgroup.coe_mul, Sp55.coe_tauHat Q hu, Subgroup.coe_one]
    ext x
    exact symmetry_symmetry Q hu x
  rw [this, map_one]

/-- Counting the square classes along a factorization $\sigma = \tau_{u_1}\cdots\tau_{u_r}$: with $n_i$ the number of
$u_k$ whose value $Q(u_k)$ lies in the class of $c_i$ ($c = (1, \Delta, \pi, \pi\Delta)$), the class of $\sigma$ in the
abelianization of $O(V)$ is $\prod_i \bar\tau_{y_i}^{n_i}$, the product of the values is
$\Delta^{n_1 + n_3}\pi^{n_2 + n_3}$ up to a square, and $r = \sum_i n_i$. -/
theorem exists_class_count (hQ : (QuadraticMap.associated Q).Nondegenerate) {Δ π : F}
    (hcls : ∀ x : F, x ≠ 0 → ∃ i : Fin 4, ∃ s : F, s ≠ 0 ∧ x = s ^ 2 * ![1, Δ, π, π * Δ] i)
    (y : Fin 4 → V) (hy : ∀ i, Q (y i) = ![1, Δ, π, π * Δ] i) (hyi : ∀ i, Q (y i) ≠ 0) :
    ∀ l : List V, (∀ u ∈ l, Q u ≠ 0) → ∃ n : Fin 4 → ℕ,
      Abelianization.of (l.map (Sp55.tauHat Q)).prod =
        ∏ i, Abelianization.of (Sp55.tauHat Q (y i)) ^ n i ∧
      (∃ s : F, s ≠ 0 ∧ (l.map Q).prod = s ^ 2 * (Δ ^ (n 1 + n 3) * π ^ (n 2 + n 3))) ∧
      l.length = ∑ i, n i ∧
      ∀ u ∈ l, ∃ i, n i ≠ 0 ∧ ∃ s : F, s ≠ 0 ∧ Q u = s ^ 2 * ![1, Δ, π, π * Δ] i := by
  classical
  set c : Fin 4 → F := ![1, Δ, π, π * Δ] with hc
  have hc_eq : ∀ i, c i = Δ ^ (if i = 1 ∨ i = 3 then 1 else 0) * π ^ (if i = 2 ∨ i = 3 then 1 else 0) := by
    intro i; fin_cases i <;> simp [hc, mul_comm]
  intro l hl
  induction l with
  | nil => exact ⟨0, by simp, ⟨1, one_ne_zero, by simp⟩, by simp, by simp⟩
  | cons u l ih =>
    obtain ⟨n, h1, ⟨s, hs, h2⟩, h3, h4⟩ := ih fun w hw => hl w (List.mem_cons_of_mem u hw)
    have hu := hl u List.mem_cons_self
    obtain ⟨i, t, ht, hut⟩ := hcls (Q u) hu
    refine ⟨n + Pi.single i 1, ?_, ⟨t * s, mul_ne_zero ht hs, ?_⟩, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, map_mul, h1,
        of_tauHat_eq_of_sq Q hQ (hyi i) ht (by rw [hut, hy i])]
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [Finset.prod_eq_single i]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · rw [List.map_cons, List.prod_cons, h2, hut, hc_eq i]
      simp only [Pi.add_apply, pow_add]
      fin_cases i <;> simp [Pi.single_apply] <;> ring
    · rw [List.length_cons, h3]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      simp
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨i, by simp, t, ht, hut⟩
      · obtain ⟨j, hj, r, hr, hwr⟩ := h4 w hw
        exact ⟨j, by simp [hj], r, hr, hwr⟩

/-- **The coset of $\sigma \in O'(V)$ from the class count** (O'Meara 1973, proof of 95:1, step 3, pp. 281–282): for a
factorization $\sigma = \tau_{u_1}\cdots\tau_{u_r}$ of $\sigma \in O'(V)$ the class counts $n_i$ all have the same
parity; $\sigma \in \Omega(V)$ if they are even, and $\sigma \in \tau_{y_0}\tau_{y_1}\tau_{y_2}\tau_{y_3}\Omega(V)$ if
they are odd. -/
theorem class_count_parity (hQ : (QuadraticMap.associated Q).Nondegenerate) {Δ π : F}
    (hcls : ∀ x : F, x ≠ 0 → ∃ i : Fin 4, ∃ s : F, s ≠ 0 ∧ x = s ^ 2 * ![1, Δ, π, π * Δ] i)
    (hsq : ∀ m n : ℕ, IsSquare (Δ ^ m * π ^ n) ↔ Even m ∧ Even n)
    (y : Fin 4 → V) (hy : ∀ i, Q (y i) = ![1, Δ, π, π * Δ] i)
    (hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPrime Q) (l : List V) (hl : ∀ u ∈ l, Q u ≠ 0) (hσl : σ = symProd Q l hl) :
    ∃ n : Fin 4 → ℕ, (∀ i, n i % 2 = n 3 % 2) ∧ l.length = ∑ i, n i ∧
      (∀ u ∈ l, ∃ i, n i ≠ 0 ∧ ∃ s : F, s ≠ 0 ∧ Q u = s ^ 2 * ![1, Δ, π, π * Δ] i) ∧
      (n 3 % 2 = 0 → σ ∈ omega Q) ∧ (n 3 % 2 = 1 → σ * (symProd Q [y 0, y 1, y 2, y 3] hy0)⁻¹ ∈ omega Q) := by
  classical
  set T : Fin 4 → Abelianization (OMeara.orth Q) := fun i => Abelianization.of (Sp55.tauHat Q (y i)) with hT
  have hyi : ∀ i, Q (y i) ≠ 0 := fun i => by
    fin_cases i <;> exact hy0 _ (by simp)
  have hT2 : ∀ i, T i ^ 2 = 1 := fun i => of_tauHat_sq Q (hyi i)
  obtain ⟨n, h1, ⟨s, hs, h2⟩, h3, h4⟩ := exists_class_count Q hQ hcls y hy hyi l hl
  have hev : Even l.length := Sp55.even_length_of_mem_orthPlus Q hσ.1 l hl hσl
  have hspin : HasSpinorNorm Q σ (l.map Q).prod :=
    (Sp55.hasSpinorNorm_iff Q).mpr ⟨l, hl, hσl, 1, one_ne_zero, by simp⟩
  have hsqprod : IsSquare (l.map Q).prod :=
    ((mem_orthPrime_iff Q hQ ⟨_, hspin⟩).mp hσ).2 _ hspin
  have hsq2 : IsSquare (Δ ^ (n 1 + n 3) * π ^ (n 2 + n 3)) := by
    obtain ⟨r, hr⟩ := hsqprod
    refine ⟨r / s, ?_⟩
    rw [h2] at hr
    field_simp
    linear_combination hr
  obtain ⟨he13, he23⟩ := (hsq _ _).mp hsq2
  have hlen := h3
  rw [h3, Fin.sum_univ_four] at hev
  have hpar : ∀ i, (n i) % 2 = (n 3) % 2 := by
    have a := Nat.even_iff.mp he13
    have b := Nat.even_iff.mp he23
    have d := Nat.even_iff.mp hev
    intro i; fin_cases i <;> simp <;> omega
  have hpow : ∀ i, T i ^ n i = T i ^ (n 3 % 2) := by
    intro i
    rw [← Nat.mod_add_div (n i) 2, pow_add, pow_mul, hT2, one_pow, mul_one, hpar i]
  have hσof : Abelianization.of (l.map (Sp55.tauHat Q)).prod = (∏ i, T i) ^ (n 3 % 2) := by
    rw [h1, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => hpow i
  have hσcoe : (((l.map (Sp55.tauHat Q)).prod : OMeara.orth Q) : V ≃ₗ[F] V) = σ := by
    rw [Sp55.coe_prod_tauHat Q l hl, hσl]
  have hρcoe : ((([y 0, y 1, y 2, y 3].map (Sp55.tauHat Q)).prod : OMeara.orth Q) : V ≃ₗ[F] V) =
      symProd Q [y 0, y 1, y 2, y 3] hy0 := Sp55.coe_prod_tauHat Q _ hy0
  have hρof : Abelianization.of ([y 0, y 1, y 2, y 3].map (Sp55.tauHat Q)).prod = ∏ i, T i := by
    simp [Fin.prod_univ_four, hT, map_mul, mul_assoc]
  refine ⟨n, hpar, hlen, h4, fun h0 => ?_, fun h1' => ?_⟩
  · have := Sp55.mem_omega_of_of_eq Q (a := (l.map (Sp55.tauHat Q)).prod) (b := 1)
      (by rw [hσof, h0, pow_zero, map_one])
    rwa [Subgroup.coe_one, inv_one, mul_one, hσcoe] at this
  · have := Sp55.mem_omega_of_of_eq Q (a := (l.map (Sp55.tauHat Q)).prod)
      (b := ([y 0, y 1, y 2, y 3].map (Sp55.tauHat Q)).prod) (by rw [hσof, h1', pow_one, hρof])
    rwa [hσcoe, hρcoe] at this

/-- **Step 3 of the proof of 95:1** (O'Meara 1973, pp. 281–282: "Hence $O'_4$ consists of at most two cosets of
$\Omega_4$, namely $\Omega_4$ and $\tau_{(1)}\tau_{(\Delta)}\tau_{(\pi)}\tau_{(\pi\Delta)}\Omega_4$"), for any
factorization: if every $x \in \dot F$ is a square times one of $c_0, \dots, c_3 = 1, \Delta, \pi, \pi\Delta$,
$\Delta^m\pi^n$ is a square only for $m, n$ even, and $Q(y_i) = c_i$, then every $\sigma \in O'(V)$ satisfies
$\sigma \in \Omega(V)$ or $\sigma(\tau_{y_0}\tau_{y_1}\tau_{y_2}\tau_{y_3})^{-1} \in \Omega(V)$. -/
@[kb "omeara1963" "§95, proof of 95:1, step 3, pp. 281–282 (O'₄ is Ω₄ ∪ τ⟨1⟩τ⟨Δ⟩τ⟨π⟩τ⟨πΔ⟩Ω₄)"]
theorem mem_omega_or_of_classes (hQ : (QuadraticMap.associated Q).Nondegenerate) {Δ π : F}
    (hcls : ∀ x : F, x ≠ 0 → ∃ i : Fin 4, ∃ s : F, s ≠ 0 ∧ x = s ^ 2 * ![1, Δ, π, π * Δ] i)
    (hsq : ∀ m n : ℕ, IsSquare (Δ ^ m * π ^ n) ↔ Even m ∧ Even n)
    (y : Fin 4 → V) (hy : ∀ i, Q (y i) = ![1, Δ, π, π * Δ] i)
    (hy0 : ∀ u ∈ [y 0, y 1, y 2, y 3], Q u ≠ 0)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ orthPrime Q) :
    σ ∈ omega Q ∨ σ * (symProd Q [y 0, y 1, y 2, y 3] hy0)⁻¹ ∈ omega Q := by
  obtain ⟨l, hl, hσl, -⟩ := exists_symmetry_prod_eq_length_le Q hQ hσ.1.1
  rw [attach_prod_eq_symProd Q l hl] at hσl
  obtain ⟨n, -, -, -, h0, h1⟩ := class_count_parity Q hQ hcls hsq y hy hy0 hσ l hl hσl
  rcases Nat.mod_two_eq_zero_or_one (n 3) with h | h
  · exact Or.inl (h0 h)
  · exact Or.inr (h1 h)

end S95

end QuadFormsKB.OMeara
