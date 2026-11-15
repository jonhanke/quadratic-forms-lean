/-
# Chenevier–Lannes, §3.4.2–3.4.3: roots of the holy neighbours

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.2, Scholium 3.4.2.13, Propositions 3.4.2.14, 3.4.2.15,
Corollary 3.4.2.17, pp. 71–73, and §3.4.3, Proposition 3.4.3.4, p. 79. Printed page numbers.

Setting: $L = \mathbb{Z}^{24}$ with an even unimodular form $Q$ (a Niemeier lattice) with roots, Coxeter number
$h = h(L)$, a Weyl vector $\rho \in L$, and the holy neighbours $\mathrm{vois}_h(L; \rho)$ and
$\mathrm{vois}_{h+1}(L; \rho) = s_\rho(\mathrm{vois}_h(L; \rho))$ (`voisLat`, `reflQ`).

**Proves** (unconditional):
- `voisLat_congr`: $\mathrm{vois}_d(L; u)$ depends only on the class of $u$ modulo $dL$ and not on the auxiliary
  $v$ with $u \cdot v \equiv 1 \bmod d$ (the book's notation $\mathrm{vois}_d(L; u)$, §3.1, p. 48, presupposes it);
- `smul_mem_voisLat`: $d\,\mathrm{vois}_d(L; u) \subset L$ when $d \mid q(u)$.

**Proves**, conditional on `VenkovRootSum 24` (Proposition 2.3.2) and `WeylVectorNorm` (Proposition 3.4.2.5):
- `scholium_3_4_2_13` (Scholium 3.4.2.13): for $x \in \mathrm{vois}_h(L; \rho)$, $\rho \cdot x \in \mathbb{Z}$,
  $hx \in M_h(L; \rho)$, $(h + 1)s_\rho(x) \in M_{h+1}(L; \rho)$ and $hx \equiv (\rho \cdot x)\rho \bmod h$,
  $(h + 1)s_\rho(x) \equiv (\rho \cdot x)\rho \bmod (h + 1)$;
- `prop_3_4_2_14_a1`, `prop_3_4_2_14_b1` (Proposition 3.4.2.14 (a.1), (b.1)): for a root $\alpha'$ of
  $\mathrm{vois}_h(L; \rho)$, neither $h$ nor $h + 1$ divides $\rho \cdot \alpha'$;
- `prop_3_4_2_15_a` (Proposition 3.4.2.15 (a), only `VenkovRootSum 24`): $\rho$ is $(h + 1)$-regular;
- `prop_3_4_3_4` (Proposition 3.4.3.4 (1), (2), (5)): for a root $\alpha$ and $d = 2h + 1 - \rho \cdot \alpha$,
  $d \ge h + 2$, $q(\rho - h\alpha) = hd$, and, for $v$ with $(\rho - h\alpha) \cdot v \equiv 1 \bmod hd$,
  $\mathrm{vois}_d(L; \rho - h\alpha) = s_{\rho - h\alpha}(\mathrm{vois}_h(L; \rho))$, an isometric copy.

**States** `HRegularDecomposition` (Proposition 3.4.2.8 (b), (i) ⇒ (ii)) and `PlusOneRegularDecomposition`
(Proposition 3.4.2.15 (c), (i) ⇒ (ii)); both rest on Scholium 3.4.1.3 (every orbit of the affine Weyl group meets the
closed alcove), which is not formalized. **Proves**, conditional on them as well:
- `cor_3_4_2_17` (Corollary 3.4.2.17): no $u \in L$ with $q(u) = (h + 1)^2$ is $(h + 1)$-regular;
- `prop_3_4_2_14_a2`, `prop_3_4_2_14_b2` (Proposition 3.4.2.14 (a.2), (b.2)), hence `holyRootConstraints_of_inputs`:
  the named statement `HolyRootConstraints` of wave 5 follows from the two decompositions;
- `voisLat_rootless_of_prime` (the second proof of Theorem 3.4.2.10 (c), p. 73, first step): if $h$ or $h + 1$ is
  prime, $\mathrm{vois}_h(L; \rho)$ has no roots; `prime_coxeter_table`: this covers the $19$ entries of Table 1.1
  other than $h \in \{25, 14, 9, 8\}$ (unconditional, by computation).

Not formalized: Proposition 3.4.3.4 (3), (4) (a simple root orthogonal to $\alpha$, by inspection of the classification;
we assume instead the existence of $v$ with $(\rho - h\alpha) \cdot v \equiv 1 \bmod hd$, i.e. the primitivity (4) in
the unimodular lattice $L$); Proposition 3.4.2.15 (b) and the uniqueness parts of (c).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.Reflections
import QuadFormsKB.Literature.ChenevierLannes.Wave4.HolyArithmetic

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

variable {n : ℕ}

/-! ### Two facts about $\mathrm{vois}_d(L; u)$ -/

/-- $q(u + d w) = q(u) + d\,(u \cdot w) + d^2 q(w)$ in $\mathbb{Z}$. -/
theorem eval_add_smul (Q : QuadForm ℤ n) (u w : Fin n → ℤ) (d : ℤ) :
    Q.eval (u + d • w) = Q.eval u + d * bZ Q u w + d ^ 2 * Q.eval w := by
  have h := evalIn_add_smulQ Q (cv u) (cv w) (d : ℚ)
  rw [← cv_smul, ← cv_add, evalIn_cv, evalIn_cv, evalIn_cv, bQ_cv] at h
  exact_mod_cast h

/-- One inclusion of `voisLat_congr`. -/
theorem voisLat_le_of_congr {Q : QuadForm ℤ n} {d : ℕ} (hd : 1 ≤ d) {u u' v v' : Fin n → ℤ} (w : Fin n → ℤ)
    (hu' : u' = u + (d : ℤ) • w) (hq : (d : ℤ) ∣ Q.eval u) (hq' : (d : ℤ) ∣ Q.eval u')
    (hv : (d : ℤ) ∣ bZ Q u v - 1) (hv' : (d : ℤ) ∣ bZ Q u' v' - 1) :
    voisLat Q d u' v' ≤ voisLat Q d u v := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  obtain ⟨a, ha⟩ := hq
  obtain ⟨a', ha'⟩ := hq'
  obtain ⟨c, hc⟩ := hv
  obtain ⟨c', hc'⟩ := hv'
  have hbu' : ∀ y, bZ Q u' y = bZ Q u y + d * bZ Q w y := by
    intro y; rw [hu', bZ_add_left, bZ_smul_left]
  have hq2 : Q.eval u' = Q.eval u + d * bZ Q u w + (d : ℤ) ^ 2 * Q.eval w := by
    rw [hu']; exact eval_add_smul Q u w d
  rw [voisLat, Submodule.span_le]
  rintro x (⟨y, rfl, hy⟩ | rfl)
  · refine Submodule.subset_span (Or.inl ⟨y, rfl, ?_⟩)
    rw [hbu'] at hy
    have : (d : ℤ) ∣ d * bZ Q w y := dvd_mul_right _ _
    simpa using (Int.dvd_add_left this).mp hy
  · -- $g' = g + t$ with $t = w - a' v' + a v \in M_d(L; u)$
    set t : Fin n → ℤ := w - a' • v' + a • v
    have hg : (1 / (d : ℚ)) • cv (u' - Q.eval u' • v') =
        (1 / (d : ℚ)) • cv (u - Q.eval u • v) + cv t := by
      rw [ha, ha', hu']
      ext i
      simp only [t, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, cv_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
    rw [hg]
    refine Submodule.add_mem _ (Submodule.subset_span (Or.inr rfl))
      (Submodule.subset_span (Or.inl ⟨t, rfl, ?_⟩))
    -- $u \cdot t \equiv u \cdot w - a' + a \equiv -d\,q(w) \equiv 0$
    have ha'' : a' = a + bZ Q u w + d * Q.eval w := by
      have h1 : (d : ℤ) * a' = d * (a + bZ Q u w + d * Q.eval w) := by
        rw [← ha', hq2, ha]; ring
      exact mul_left_cancel₀ (by exact_mod_cast (by omega : d ≠ 0)) h1
    have hbv' : bZ Q u v' = 1 + d * c' - d * bZ Q w v' := by
      have := hbu' v'; linarith
    have hbt : bZ Q u t = bZ Q u w - a' * bZ Q u v' + a * bZ Q u v := by
      simp only [t, bZ_add_right', bZ_sub_right', bZ_smul_right']
    refine ⟨a * c - (a + bZ Q u w + d * Q.eval w) * (c' - bZ Q w v') - Q.eval w, ?_⟩
    rw [hbt, hbv', ha'']
    linear_combination a * hc

/-- **$\mathrm{vois}_d(L; u)$ is well defined** (Chenevier–Lannes, §3.1, p. 48, implicit in the notation): for
$d \ge 1$, $u' = u + dw$ with $d \mid q(u)$ and $d \mid q(u')$, and $v, v'$ with $u \cdot v \equiv u' \cdot v' \equiv 1
\bmod d$, $\mathrm{vois}_d(L; u', v') = \mathrm{vois}_d(L; u, v)$. Unconditional. -/
@[kb "chenevierlannes2019" "§3.1, p. 48 (vois_d(L; u) depends only on [u])"]
theorem voisLat_congr {Q : QuadForm ℤ n} {d : ℕ} (hd : 1 ≤ d) {u u' v v' : Fin n → ℤ} (w : Fin n → ℤ)
    (hu' : u' = u + (d : ℤ) • w) (hq : (d : ℤ) ∣ Q.eval u) (hq' : (d : ℤ) ∣ Q.eval u')
    (hv : (d : ℤ) ∣ bZ Q u v - 1) (hv' : (d : ℤ) ∣ bZ Q u' v' - 1) :
    voisLat Q d u' v' = voisLat Q d u v := by
  refine le_antisymm (voisLat_le_of_congr hd w hu' hq hq' hv hv') (voisLat_le_of_congr hd (-w) ?_ hq' hq hv' hv)
  rw [hu', smul_neg, add_neg_cancel_right]

/-- $d\,\mathrm{vois}_d(L; u) \subset L$ when $d \mid q(u)$ (the quotient $\mathrm{vois}_d(L;u)/M_d(L;u)$ is killed
by $d$). Unconditional. -/
theorem smul_mem_voisLat {Q : QuadForm ℤ n} {d : ℕ} {u v : Fin n → ℤ} {x : Fin n → ℚ}
    (hx : x ∈ voisLat Q d u v) : ∃ y : Fin n → ℤ, (d : ℚ) • x = cv y := by
  refine Submodule.span_induction (p := fun x _ => ∃ y : Fin n → ℤ, (d : ℚ) • x = cv y) ?_ ?_ ?_ ?_ hx
  · rintro x (⟨y, rfl, -⟩ | rfl)
    · exact ⟨(d : ℤ) • y, by rw [cv_smul]; push_cast; rfl⟩
    · by_cases hd : (d : ℚ) = 0
      · exact ⟨0, by rw [hd, zero_smul, cv_zero]⟩
      · exact ⟨u - Q.eval u • v, by rw [smul_smul, mul_one_div_cancel hd, one_smul]⟩
  · exact ⟨0, by rw [smul_zero, cv_zero]⟩
  · rintro x x' - - ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y + y', by rw [smul_add, hy, hy', cv_add]⟩
  · rintro a x - ⟨y, hy⟩
    refine ⟨a • y, ?_⟩
    rw [cv_smul, ← hy, ← Int.cast_smul_eq_zsmul ℚ a x, smul_comm]

/-! ### The data of a Weyl vector -/

/-- Data attached to a Weyl vector $\rho \in L$ of a Niemeier lattice with roots (conditional on Venkov's identity and
`WeylVectorNorm`): $h \ge 2$, $q(\rho) = h(h + 1)$, a root $v_0$ with $\rho \cdot v_0 = 1$, and the bounds
$1 \le |\rho \cdot \alpha| \le h - 1$ for every root $\alpha$. -/
theorem weyl_facts (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ)) :
    2 ≤ h ∧ Q.eval ρ = (h : ℤ) * (h + 1) ∧ (∃ v₀ : Fin 24 → ℤ, bZ Q ρ v₀ = 1) ∧
      ∀ α ∈ rootSet Q, (1 ≤ bZ Q ρ α ∨ bZ Q ρ α ≤ -1) ∧ bZ Q ρ α ≤ h - 1 ∧ -(h - 1 : ℤ) ≤ bZ Q ρ α := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨ξ, hξ, h2⟩ := hρ.exists_posRoots hQ'.posDef
  have hb := fun α (hα : α ∈ rootSet Q) => weyl_dot_bounds hV hQ' hh hξ h2 hα
  obtain ⟨r, hr, -, ⟨v₀, -, hv₀⟩, -⟩ := prop_3_4_2_8_a hV hQ hR hρ
  have hrρ : r = ρ := cv_injective hr.symm
  subst hrρ
  have hn := hN Q hQ hR _ hρ
  rw [evalIn_cv, hh] at hn
  have hn' : Q.eval r = (h : ℤ) * (h + 1) := by exact_mod_cast hn
  obtain ⟨α, hα⟩ := hR
  obtain ⟨h1, h2', h3⟩ := hb α hα
  refine ⟨by omega, hn', ⟨v₀, hv₀⟩, hb⟩

/-! ### Scholium 3.4.2.13 -/

/-- **Scholium 3.4.2.13** (Chenevier–Lannes, p. 71): **conditional** on `VenkovRootSum 24` and `WeylVectorNorm`. Let
$L$ be a Niemeier lattice with roots, $h = h(L)$, $\rho \in L$ a Weyl vector, $v \in L$ with $\rho \cdot v \equiv 1
\bmod h$ and $x \in \mathrm{vois}_h(L; \rho)$. Then $k = \rho \cdot x$ is an integer; $hx = y \in L$ with
$y \in M_h(L; \rho)$ and $y \equiv k\rho \bmod h$; $(h + 1)\,s_\rho(x) = z \in L$ with $z \in M_{h+1}(L; \rho)$ and
$z \equiv k\rho \bmod (h + 1)$. (Congruences coordinatewise in $L = \mathbb{Z}^{24}$.) -/
@[kb "chenevierlannes2019" "Scholium 3.4.2.13, p. 71 (conditional)"]
theorem scholium_3_4_2_13 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) {x : Fin 24 → ℚ} (hx : x ∈ voisLat Q h ρ v) :
    ∃ k : ℤ, bQ Q (cv ρ) x = k ∧
      (∃ y : Fin 24 → ℤ, (h : ℚ) • x = cv y ∧ (h : ℤ) ∣ bZ Q ρ y ∧ ∀ i, (h : ℤ) ∣ y i - k * ρ i) ∧
      (∃ z : Fin 24 → ℤ, ((h : ℚ) + 1) • reflQ Q ρ x = cv z ∧ ((h : ℤ) + 1) ∣ bZ Q ρ z ∧
        ∀ i, ((h : ℤ) + 1) ∣ z i - k * ρ i) := by
  obtain ⟨hh2, hq, ⟨v₀, hv₀⟩, -⟩ := weyl_facts hV hN hQ hR hh hρ
  have hh1 : 1 ≤ h := by omega
  have hh0 : (h : ℚ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hq0 : Q.eval ρ ≠ 0 := by rw [hq]; positivity
  -- switch to $v_0$ (with $\rho \cdot v_0 = 1$)
  have hqh : (h : ℤ) ∣ Q.eval ρ := ⟨h + 1, hq⟩
  have hswap : voisLat Q h ρ v = voisLat Q h ρ v₀ :=
    voisLat_congr hh1 0 (by simp) hqh hqh (by rw [hv₀]; simp) hv
  rw [hswap] at hx
  -- the clearing lemma for $d = h$
  obtain ⟨y', k, hy', hk, -, hcong⟩ := voisLat_mem_clearing hh1 hqh (by rw [hv₀]; simp) hx
  obtain ⟨y, hy⟩ := smul_mem_voisLat hx
  have hyy : y' = ((h : ℤ) + 1) • y := by
    apply cv_injective
    rw [← hy', cv_smul, ← hy, smul_smul, hq]
    push_cast; ring_nf
  refine ⟨k, hk, ⟨y, hy, ?_, ?_⟩, ?_⟩
  · refine ⟨k, ?_⟩
    have : (bZ Q ρ y : ℚ) = h * k := by
      rw [← bQ_cv, ← hy, bQ_smul_right, hk]
    exact_mod_cast this
  · intro i
    have := hcong i
    rw [hyy] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have e : y i - k * ρ i = ((h : ℤ) + 1) * y i - k * ρ i - h * y i := by ring
    rw [e]
    exact dvd_sub this (dvd_mul_right _ _)
  · -- $s_\rho(x) \in \mathrm{vois}_{h+1}(L; \rho)$
    have hq' : Q.eval ρ = (h : ℤ) * ((h + 1 : ℕ) : ℤ) := by rw [hq]; push_cast; ring
    have hvv : ((h : ℤ) * ((h + 1 : ℕ) : ℤ)) ∣ bZ Q ρ v₀ - 1 := by rw [hv₀]; simp
    have heq := voisLat_eq_map_reflQ (d₁ := h) (d₂ := h + 1) hh1 (by omega) hq' hvv
    have hsx : reflQ Q ρ x ∈ voisLat Q (h + 1) ρ v₀ := by
      rw [heq]; exact ⟨x, hx, rfl⟩
    have hqh1 : ((h + 1 : ℕ) : ℤ) ∣ Q.eval ρ := ⟨h, by rw [hq]; push_cast; ring⟩
    obtain ⟨z', k', hz', hk', -, hcong'⟩ :=
      voisLat_mem_clearing (by omega) hqh1 (by rw [hv₀]; simp) hsx
    obtain ⟨z, hz⟩ := smul_mem_voisLat hsx
    have hkk : k' = -k := by
      have h1 : bQ Q (cv ρ) (reflQ Q ρ x) = - bQ Q (cv ρ) x := by
        rw [bQ_symm, bQ_reflQ Q hq0, bQ_symm]
      rw [hk', hk] at h1
      exact_mod_cast h1
    have hzz : z' = (h : ℤ) • z := by
      apply cv_injective
      rw [← hz', cv_smul, ← hz, smul_smul, hq]
      push_cast; ring_nf
    push_cast at hz
    refine ⟨z, hz, ⟨-k, ?_⟩, ?_⟩
    · have : (bZ Q ρ z : ℚ) = (h + 1) * (-k) := by
        rw [← bQ_cv, ← hz, bQ_smul_right, hk', hkk]; push_cast; ring
      exact_mod_cast this
    · intro i
      have := hcong' i
      rw [hzz, hkk] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      push_cast at this
      have e : z i - k * ρ i = ((h : ℤ) + 1) * z i - (h * z i - -k * ρ i) := by ring
      rw [e]
      exact dvd_sub (dvd_mul_right _ _) this

/-! ### Proposition 3.4.2.14 (a.1), (b.1) -/

/-- If $d \ge 1$, $d\,x = y \in \mathbb{Z}^n$ and $d \mid y_i$ for all $i$, then $x \in \mathbb{Z}^n$. -/
theorem exists_cv_of_smul {d : ℕ} (hd : 1 ≤ d) {x : Fin n → ℚ} {y : Fin n → ℤ} (hy : (d : ℚ) • x = cv y)
    (hdy : ∀ i, (d : ℤ) ∣ y i) : ∃ w : Fin n → ℤ, x = cv w := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  choose w hw using hdy
  refine ⟨w, ?_⟩
  ext i
  have := congrFun hy i
  simp only [Pi.smul_apply, smul_eq_mul, cv_apply, hw i] at this
  push_cast at this
  simp only [cv_apply]
  exact mul_left_cancel₀ hd0 this

/-- **Proposition 3.4.2.14 (a.1)** (Chenevier–Lannes, p. 72): **conditional** on `VenkovRootSum 24` and
`WeylVectorNorm`. For a root $\alpha'$ of $\mathrm{vois}_h(L; \rho)$ (an element with $q(\alpha') = 1$), the integer
$\rho \cdot \alpha'$ is not divisible by $h$. *Proof* (the book's): otherwise $\alpha' \in L$ by Scholium 3.4.2.13, a
root of $L$ with $h \mid \rho \cdot \alpha'$, against $1 \le |\rho \cdot \alpha'| \le h - 1$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.14 (a.1), p. 72 (conditional)"]
theorem prop_3_4_2_14_a1 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) {α' : Fin 24 → ℚ} (hα' : α' ∈ voisLat Q h ρ v)
    (hq1 : Q.evalIn ℚ α' = 1) : ∃ k : ℤ, bQ Q (cv ρ) α' = k ∧ ¬ (h : ℤ) ∣ k := by
  obtain ⟨hh2, -, -, hb⟩ := weyl_facts hV hN hQ hR hh hρ
  obtain ⟨k, hk, ⟨y, hy, -, hcong⟩, -⟩ := scholium_3_4_2_13 hV hN hQ hR hh hρ hv hα'
  refine ⟨k, hk, fun hdk => ?_⟩
  obtain ⟨w, rfl⟩ := exists_cv_of_smul (by omega) hy (fun i => by
    have := hcong i
    exact (Int.dvd_iff_dvd_of_dvd_sub this).mpr (Dvd.dvd.mul_right hdk _))
  rw [evalIn_cv] at hq1
  have hwR : w ∈ rootSet Q := by show Q.eval w = 1; exact_mod_cast hq1
  rw [bQ_cv] at hk
  have hk' : bZ Q ρ w = k := by exact_mod_cast hk
  obtain ⟨h1, h2, h3⟩ := hb w hwR
  rw [hk'] at h1 h2 h3
  obtain ⟨m, rfl⟩ := hdk
  rcases h1 with h1 | h1
  · have : 0 < m := by by_contra hm; push Not at hm; nlinarith
    nlinarith
  · have : m < 0 := by by_contra hm; push Not at hm; nlinarith
    nlinarith

/-- **Proposition 3.4.2.14 (b.1)** (Chenevier–Lannes, p. 72): **conditional** on `VenkovRootSum 24` and
`WeylVectorNorm`. For a root $\alpha'$ of $\mathrm{vois}_h(L; \rho)$, $\rho \cdot \alpha'$ is not divisible by $h + 1$.
*Proof* (the book's): otherwise $s_\rho(\alpha') \in L$ by Scholium 3.4.2.13, a root of $L$ with
$\rho \cdot s_\rho(\alpha') = -\rho \cdot \alpha' \in (h + 1)\mathbb{Z}$, against $1 \le |\rho \cdot \beta| \le h - 1$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.14 (b.1), p. 72 (conditional)"]
theorem prop_3_4_2_14_b1 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) {α' : Fin 24 → ℚ} (hα' : α' ∈ voisLat Q h ρ v)
    (hq1 : Q.evalIn ℚ α' = 1) : ∃ k : ℤ, bQ Q (cv ρ) α' = k ∧ ¬ ((h : ℤ) + 1) ∣ k := by
  obtain ⟨hh2, hq, -, hb⟩ := weyl_facts hV hN hQ hR hh hρ
  have hq0 : Q.eval ρ ≠ 0 := by rw [hq]; positivity
  obtain ⟨k, hk, -, ⟨z, hz, -, hcong⟩⟩ := scholium_3_4_2_13 hV hN hQ hR hh hρ hv hα'
  refine ⟨k, hk, fun hdk => ?_⟩
  obtain ⟨w, hw⟩ := exists_cv_of_smul (d := h + 1) (by omega) (by push_cast; exact hz) (fun i => by
    have := hcong i
    push_cast
    exact (Int.dvd_iff_dvd_of_dvd_sub this).mpr (Dvd.dvd.mul_right hdk _))
  have hq1' := evalIn_reflQ Q hq0 α'
  rw [hq1, hw, evalIn_cv] at hq1'
  have hwR : w ∈ rootSet Q := by show Q.eval w = 1; exact_mod_cast hq1'
  have hdot : bQ Q (cv ρ) (reflQ Q ρ α') = -k := by
    rw [bQ_symm, bQ_reflQ Q hq0, bQ_symm, hk]
  rw [hw, bQ_cv] at hdot
  have hk' : bZ Q ρ w = -k := by exact_mod_cast hdot
  obtain ⟨h1, h2, h3⟩ := hb w hwR
  rw [hk'] at h1 h2 h3
  obtain ⟨m, rfl⟩ := hdk
  rcases h1 with h1 | h1
  · have : m < 0 := by by_contra hm; push Not at hm; nlinarith
    nlinarith
  · have : 0 < m := by by_contra hm; push Not at hm; nlinarith
    nlinarith

/-! ### Proposition 3.4.2.15 (a) and the two decompositions -/

/-- **Proposition 3.4.2.15 (a)** (Chenevier–Lannes, p. 72): **conditional** on `VenkovRootSum 24`. A Weyl vector
$\rho$ of a Niemeier lattice with roots is $(h + 1)$-regular: $\alpha \cdot \rho \notin (h + 1)\mathbb{Z}$ for every
root $\alpha$ (as $1 \le |\alpha \cdot \rho| \le h - 1$). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.15 (a), p. 72 (conditional)"]
theorem prop_3_4_2_15_a (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) {h : ℕ}
    (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) : IsDRegular Q (h + 1) ρ := by
  have hQ' : IsEvenUnimodular Q := hQ
  intro β hβ k hk
  have hR : (rootSet Q).Nonempty := ⟨β, hβ⟩
  obtain ⟨r, h', ξ, rfl, hh', hξ, h2⟩ := weyl_data hV hQ hR hρ
  have hhh : h' = h := by exact_mod_cast hh'.symm.trans hh
  subst hhh
  rw [bQ_symm, bQ_cv] at hk
  have hk' : bZ Q r β = (h' + 1) * k := by exact_mod_cast hk
  obtain ⟨hnz, hle, hge⟩ := weyl_dot_bounds hV hQ' hh' hξ h2 hβ
  rw [hk'] at hnz hle hge
  rcases hnz with hnz | hnz
  · have : 0 < k := by by_contra hk0; push Not at hk0; nlinarith
    nlinarith
  · have : k < 0 := by by_contra hk0; push Not at hk0; nlinarith
    nlinarith

/-- **Proposition 3.4.2.8 (b), (i) ⇒ (ii)** (Chenevier–Lannes, p. 67; named statement): for a Niemeier lattice with
roots, Coxeter number $h$, every $h$-regular $\xi \in Q(R)^\sharp$ (that is, $\alpha \cdot \xi \in \mathbb{Z}$ for all
roots $\alpha$) is $w\rho + hx$ with $w \in W$, $x \in Q(R)^\sharp$. Here $w\rho$ is written as "a Weyl vector
$\rho'$" (the Weyl vectors are the $w\rho$, $W$ acting transitively on the chambers) and $x = -\eta$. The book's proof
uses Scholium 3.4.1.3 (the closed alcove meets every orbit of $W \ltimes Q(R)$) and the description of the alcove by a
basis and the highest roots; not formalized. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.8 (b), p. 67 ((i) ⇒ (ii))"]
def HRegularDecomposition : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ h : ℕ, coxeterNumber Q = h →
    ∀ ξ : Fin 24 → ℚ, (∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) ξ = k) → IsDRegular Q h ξ →
      ∃ ρ' η : Fin 24 → ℚ, IsWeylVector Q ρ' ∧ (∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) η = k) ∧
        ξ = ρ' - (h : ℚ) • η

/-- **Proposition 3.4.2.15 (c), (i) ⇒ (ii)** (Chenevier–Lannes, p. 72; named statement): for a Niemeier lattice $L$
with roots and Coxeter number $h$, every $(h + 1)$-regular $u \in L$ is $w\rho + (h + 1)x$ with $w \in W$, $x \in L$
($w\rho$ written as a Weyl vector $\rho'$, as in `HRegularDecomposition`). The book's proof goes through part (b)
(Scholium 3.4.1.3 again) and Proposition 3.4.2.9 (c); not formalized. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.15 (c), p. 72 ((i) ⇒ (ii))"]
def PlusOneRegularDecomposition : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ h : ℕ, coxeterNumber Q = h →
    ∀ u : Fin 24 → ℤ, IsDRegular Q (h + 1) (cv u) →
      ∃ (ρ' : Fin 24 → ℚ) (x : Fin 24 → ℤ), IsWeylVector Q ρ' ∧ cv u = ρ' + ((h : ℚ) + 1) • cv x

/-- An $h$-regular element of $L$ has $q \ge h(h + 1)$: **conditional** on `VenkovRootSum 24`, `WeylVectorNorm` and
`HRegularDecomposition` (via Proposition 3.4.2.9 (b), `prop_3_4_2_9_bc`). This is the form in which Scholium 3.4.2.7
is used in the proof of Proposition 3.4.2.14 (a.2). -/
theorem le_eval_of_hRegular (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hD : HRegularDecomposition)
    {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h)
    {u : Fin 24 → ℤ} (hu : IsDRegular Q h (cv u)) : (h : ℚ) * (h + 1) ≤ Q.eval u := by
  have hQ' : IsEvenUnimodular Q := hQ
  obtain ⟨ρ', η, hρ', hη, he⟩ := hD Q hQ hR h hh (cv u) (fun α _ => ⟨bZ Q α u, bQ_cv Q α u⟩) hu
  obtain ⟨ξ, hξ, h2⟩ := hρ'.exists_posRoots hQ'.posDef
  have h1 := (prop_3_4_2_9_bc hV hQ' hξ h2 hR hη).1
  rw [hN Q hQ hR ρ' hρ', hh, ← he, evalIn_cv] at h1
  exact h1

/-! ### Corollary 3.4.2.17 -/

/-- **Corollary 3.4.2.17** (Chenevier–Lannes, p. 73): **conditional** on `VenkovRootSum 24`, `WeylVectorNorm` and
`PlusOneRegularDecomposition`. For a Niemeier lattice $L$ with roots and $u \in L$ with $q(u) = (h + 1)^2$, $u$ is not
$(h + 1)$-regular. *Update:* the book also assumes $u$ to be $(h + 1)$-primitive; the proof does not use it, so it
is dropped.
*Proof* (the book's): $u = \rho' + (h + 1)x$ with $\rho'$ a Weyl vector and $x \in L$; then $q(u) = h(h + 1)$ if
$x = 0$ (Proposition 3.4.2.5) and $q(u) \ge (h + 1)(h + 2)$ otherwise (Proposition 3.4.2.16). -/
@[kb "chenevierlannes2019" "Cor. 3.4.2.17, p. 73 (conditional)"]
theorem cor_3_4_2_17 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hP : PlusOneRegularDecomposition)
    {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h)
    {u : Fin 24 → ℤ} (hu : Q.eval u = ((h : ℤ) + 1) ^ 2) : ¬ IsDRegular Q (h + 1) (cv u) := by
  intro hreg
  obtain ⟨ρ', x, hρ', he⟩ := hP Q hQ hR h hh u hreg
  have hq : (Q.eval u : ℚ) = ((h : ℚ) + 1) ^ 2 := by exact_mod_cast hu
  by_cases hx : x = 0
  · subst hx
    rw [cv_zero, smul_zero, add_zero] at he
    have := hN Q hQ hR ρ' hρ'
    rw [← he, evalIn_cv, hq, hh] at this
    nlinarith
  · have h16 := prop_3_4_2_16 hV hN hQ hR hρ' (x := -x) (neg_ne_zero.mpr hx)
    rw [cv_neg', smul_neg, sub_neg_eq_add, hh] at h16
    rw [← he, evalIn_cv, hq] at h16
    have : (0 : ℚ) ≤ h := by positivity
    nlinarith

/-! ### Proposition 3.4.2.14 (a.2), (b.2) -/

/-- If $y \equiv k\rho \bmod d$ coordinatewise, then $\beta \cdot y \equiv k\,(\beta \cdot \rho) \bmod d$. -/
theorem bZ_congr_of_congr (Q : QuadForm ℤ n) {d k : ℤ} {y ρ : Fin n → ℤ} (hy : ∀ i, d ∣ y i - k * ρ i)
    (β : Fin n → ℤ) : d ∣ bZ Q β y - k * bZ Q β ρ := by
  choose t ht using hy
  have : y - k • ρ = d • t := by ext i; simp [ht i]
  have e : bZ Q β y - k * bZ Q β ρ = bZ Q β (y - k • ρ) := by
    rw [bZ_sub_right', bZ_smul_right']
  rw [e, this, bZ_smul_right']
  exact dvd_mul_right _ _

/-- If $y \equiv k\rho \bmod d$ with $\gcd(k, d) = 1$ and $\rho$ is $d$-regular, then $y$ is $d$-regular. -/
theorem isDRegular_of_congr (Q : QuadForm ℤ n) {d : ℕ} {k : ℤ} {y ρ : Fin n → ℤ}
    (hy : ∀ i, (d : ℤ) ∣ y i - k * ρ i) (hk : IsCoprime k (d : ℤ)) (hρ : IsDRegular Q d (cv ρ)) :
    IsDRegular Q d (cv y) := by
  intro β hβ m hm
  rw [bQ_cv] at hm
  have hm' : bZ Q β y = d * m := by exact_mod_cast hm
  have h1 := bZ_congr_of_congr Q hy β
  rw [hm'] at h1
  have h2 : (d : ℤ) ∣ k * bZ Q β ρ := by
    have := dvd_sub (dvd_mul_right (d : ℤ) m) h1
    simpa using this
  obtain ⟨c, hc⟩ := hk.symm.dvd_of_dvd_mul_left h2
  exact hρ β hβ c (by rw [bQ_cv, hc]; push_cast; ring)

/-- **Proposition 3.4.2.14 (a.2)** (Chenevier–Lannes, p. 72): **conditional** on `VenkovRootSum 24`, `WeylVectorNorm`
and `HRegularDecomposition`. For a root $\alpha'$ of $\mathrm{vois}_h(L; \rho)$, $\rho \cdot \alpha'$ and $h$ are not
coprime. *Proof* (the book's): otherwise $y = h\alpha' \in L$ is congruent to $(\rho \cdot \alpha')\rho$ modulo $h$
(Scholium 3.4.2.13), hence $h$-regular, while $q(y) = h^2 < h(h + 1)$ (`le_eval_of_hRegular`). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.14 (a.2), p. 72 (conditional)"]
theorem prop_3_4_2_14_a2 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hD : HRegularDecomposition)
    {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) {α' : Fin 24 → ℚ} (hα' : α' ∈ voisLat Q h ρ v)
    (hq1 : Q.evalIn ℚ α' = 1) : ∃ k : ℤ, bQ Q (cv ρ) α' = k ∧ Int.gcd k h ≠ 1 := by
  obtain ⟨hh2, -, -, -⟩ := weyl_facts hV hN hQ hR hh hρ
  obtain ⟨k, hk, ⟨y, hy, -, hcong⟩, -⟩ := scholium_3_4_2_13 hV hN hQ hR hh hρ hv hα'
  refine ⟨k, hk, fun hg => ?_⟩
  have hcop : IsCoprime k (h : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hg
  obtain ⟨r, hr, -, -, h', hh', hreg⟩ := prop_3_4_2_8_a hV hQ hR hρ
  have : r = ρ := cv_injective hr.symm
  subst this
  have hhh : h' = h := by exact_mod_cast hh'.symm.trans hh
  subst hhh
  have hyreg := isDRegular_of_congr Q hcong hcop hreg
  have hle := le_eval_of_hRegular hV hN hD hQ hR hh hyreg
  have hqy : (Q.eval y : ℚ) = (h' : ℚ) ^ 2 := by
    rw [← evalIn_cv, ← hy, evalIn_smulQ, hq1, mul_one]
  rw [hqy] at hle
  have : (2 : ℚ) ≤ h' := by exact_mod_cast hh2
  nlinarith

/-- **Proposition 3.4.2.14 (b.2)** (Chenevier–Lannes, p. 72): **conditional** on `VenkovRootSum 24`, `WeylVectorNorm`
and `PlusOneRegularDecomposition`. For a root $\alpha'$ of $\mathrm{vois}_h(L; \rho)$, $\rho \cdot \alpha'$ and $h + 1$
are not coprime. *Proof* (the book's): otherwise $z = (h + 1)s_\rho(\alpha') \in L$ is congruent to
$(\rho \cdot \alpha')\rho$ modulo $h + 1$ (Scholium 3.4.2.13), hence $(h + 1)$-regular (Proposition 3.4.2.15 (a)), with
$q(z) = (h + 1)^2$, against Corollary 3.4.2.17. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.14 (b.2), p. 72 (conditional)"]
theorem prop_3_4_2_14_b2 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hP : PlusOneRegularDecomposition)
    {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) {α' : Fin 24 → ℚ} (hα' : α' ∈ voisLat Q h ρ v)
    (hq1 : Q.evalIn ℚ α' = 1) : ∃ k : ℤ, bQ Q (cv ρ) α' = k ∧ Int.gcd k (h + 1 : ℕ) ≠ 1 := by
  obtain ⟨hh2, hq, -, -⟩ := weyl_facts hV hN hQ hR hh hρ
  have hq0 : Q.eval ρ ≠ 0 := by rw [hq]; exact mul_ne_zero (by omega) (by omega)
  obtain ⟨k, hk, -, ⟨z, hz, -, hcong⟩⟩ := scholium_3_4_2_13 hV hN hQ hR hh hρ hv hα'
  refine ⟨k, hk, fun hg => ?_⟩
  have hcop : IsCoprime k ((h + 1 : ℕ) : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hg
  have hreg := prop_3_4_2_15_a hV hQ hh hρ
  have hcong' : ∀ i, ((h + 1 : ℕ) : ℤ) ∣ z i - k * ρ i := by intro i; push_cast; exact hcong i
  have hzreg := isDRegular_of_congr Q hcong' hcop hreg
  have hqz : Q.eval z = ((h : ℤ) + 1) ^ 2 := by
    have : (Q.eval z : ℚ) = ((h : ℚ) + 1) ^ 2 := by
      rw [← evalIn_cv, ← hz, evalIn_smulQ, evalIn_reflQ Q hq0, hq1, mul_one]
    exact_mod_cast this
  exact cor_3_4_2_17 hV hN hP hQ hR hh hqz hzreg

/-- **Proposition 3.4.2.14 in full** (Chenevier–Lannes, p. 72): the named statement `HolyRootConstraints` of wave 5
holds, **conditional** on `VenkovRootSum 24`, `WeylVectorNorm`, `HRegularDecomposition` and
`PlusOneRegularDecomposition` (the book's proof). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.14, p. 72 (conditional)"]
theorem holyRootConstraints_of_inputs (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hD : HRegularDecomposition)
    (hP : PlusOneRegularDecomposition) : HolyRootConstraints := by
  intro Q hQ hR h hh ρ hρ v hv α' hα' hq1
  obtain ⟨k, hk, ha1⟩ := prop_3_4_2_14_a1 hV hN hQ hR hh hρ hv hα' hq1
  obtain ⟨k2, hk2, hb1⟩ := prop_3_4_2_14_b1 hV hN hQ hR hh hρ hv hα' hq1
  obtain ⟨k3, hk3, ha2⟩ := prop_3_4_2_14_a2 hV hN hD hQ hR hh hρ hv hα' hq1
  obtain ⟨k4, hk4, hb2⟩ := prop_3_4_2_14_b2 hV hN hP hQ hR hh hρ hv hα' hq1
  have e2 : k2 = k := by exact_mod_cast hk2.symm.trans hk
  have e3 : k3 = k := by exact_mod_cast hk3.symm.trans hk
  have e4 : k4 = k := by exact_mod_cast hk4.symm.trans hk
  subst e2 e3 e4
  refine ⟨k4.natAbs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk, Nat.cast_natAbs, Int.cast_abs]
    rcases le_or_gt 0 (k4 : ℚ) with h0 | h0
    · left; rw [abs_of_nonneg h0]
    · right; rw [abs_of_neg h0, neg_neg]
  · intro hd; exact ha1 (Int.natCast_dvd.mpr hd)
  · intro hd; exact hb1 (by exact_mod_cast Int.natCast_dvd.mpr hd)
  · intro hg; exact ha2 (by rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact hg)
  · intro hg; exact hb2 (by rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact hg)

/-- **Theorem 3.4.2.10 (c), second proof, first step** (Chenevier–Lannes, p. 73, after Corollary 3.4.2.17):
**conditional** on `VenkovRootSum 24`, `WeylVectorNorm`, `HRegularDecomposition` and `PlusOneRegularDecomposition`.
If $h$ or $h + 1$ is prime, then $\mathrm{vois}_h(L; \rho)$ has no roots. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 73 (vois_h(L; ρ) has no roots if h or h + 1 is prime; conditional)"]
theorem voisLat_rootless_of_prime (hV : VenkovRootSum 24) (hN : WeylVectorNorm) (hD : HRegularDecomposition)
    (hP : PlusOneRegularDecomposition) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {h : ℕ}
    (hh : coxeterNumber Q = h) (hp : h.Prime ∨ (h + 1).Prime) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {v : Fin 24 → ℤ} (hv : (h : ℤ) ∣ bZ Q ρ v - 1) : ∀ α' ∈ voisLat Q h ρ v, Q.evalIn ℚ α' ≠ 1 := by
  intro α' hα' hq1
  obtain ⟨t, -, ha1, hb1, ha2, hb2⟩ := holyRootConstraints_of_inputs hV hN hD hP Q hQ hR h hh ρ hρ v hv α' hα' hq1
  rcases hp with hp | hp
  · exact ha2 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha1)))
  · exact hb2 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb1)))

/-- **The $19$ Niemeier lattices covered by `voisLat_rootless_of_prime`** (Chenevier–Lannes, p. 73: "This is the case
for 19 of the Niemeier lattices with roots. The four that resist correspond to $h = 25, 14, 9, 8$"): unconditional, by
computation on Table 1.1. -/
@[kb "chenevierlannes2019" "§3.4.2, p. 73 (19 of the 23 Coxeter numbers)"]
theorem prime_coxeter_table :
    (∀ e ∈ niemeierRootTable, (e.2.Prime ∨ (e.2 + 1).Prime) ↔ e.2 ∉ ({25, 14, 9, 8} : Finset ℕ)) ∧
      (niemeierRootTable.filter (fun e => e.2.Prime ∨ (e.2 + 1).Prime)).length = 19 := by
  refine ⟨?_, by decide⟩
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  decide

/-! ### Proposition 3.4.3.4 -/

/-- **Proposition 3.4.3.4 (1), (2), (5)** (Chenevier–Lannes, p. 79): **conditional** on `VenkovRootSum 24` and
`WeylVectorNorm`. Let $L$ be a Niemeier lattice with roots, $\rho \in L$ a Weyl vector, $\alpha$ a root and
$d = 2h + 1 - \rho \cdot \alpha$. Then (1) $d \ge h + 2$; (2) $q(\rho - h\alpha) = hd$; (5) for $v \in L$ with
$(\rho - h\alpha) \cdot v \equiv 1 \bmod hd$ (the primitivity (4)),
$$\mathrm{vois}_d(L; \rho - h\alpha) = s_{\rho - h\alpha}\bigl(\mathrm{vois}_h(L; \rho)\bigr),$$
so the two lattices are isometric (`evalIn_reflQ`; by Theorem 3.4.2.10 (c) both are then the Leech lattice). The
book's proof of (5) is Proposition 3.1.14 (b) (`voisLat_eq_map_reflQ`) together with
$\mathrm{vois}_h(L; \rho - h\alpha) = \mathrm{vois}_h(L; \rho)$ (`voisLat_congr`). Parts (3) and (4) (a simple root
orthogonal to $\alpha$, by inspection of the root systems) are not formalized: (4) is assumed through $v$. -/
@[kb "chenevierlannes2019" "Prop. 3.4.3.4 (1), (2), (5), p. 79 (conditional)"]
theorem prop_3_4_3_4 (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) {h : ℕ} (hh : coxeterNumber Q = h) {ρ : Fin 24 → ℤ} (hρ : IsWeylVector Q (cv ρ))
    {α : Fin 24 → ℤ} (hα : α ∈ rootSet Q) :
    (h : ℤ) + 2 ≤ 2 * h + 1 - bZ Q ρ α ∧
      Q.eval (ρ - (h : ℤ) • α) = h * (2 * h + 1 - bZ Q ρ α) ∧
      ∀ (d : ℕ) (v : Fin 24 → ℤ), (d : ℤ) = 2 * h + 1 - bZ Q ρ α →
        ((h : ℤ) * d) ∣ bZ Q (ρ - (h : ℤ) • α) v - 1 →
        ∀ w : Fin 24 → ℤ, (h : ℤ) ∣ bZ Q ρ w - 1 →
          voisLat Q d (ρ - (h : ℤ) • α) v = (voisLat Q h ρ w).map ((reflQ Q (ρ - (h : ℤ) • α)).restrictScalars ℤ) := by
  obtain ⟨hh2, hq, -, hb⟩ := weyl_facts hV hN hQ hR hh hρ
  obtain ⟨-, hle, -⟩ := hb α hα
  have hαq : Q.eval α = 1 := hα
  have hq2 : Q.eval (ρ - (h : ℤ) • α) = h * (2 * h + 1 - bZ Q ρ α) := by
    rw [sub_eq_add_neg, ← neg_smul, eval_add_smul, hq, hαq]
    ring
  refine ⟨by omega, hq2, ?_⟩
  intro d v hd hv w hw
  have hh1 : 1 ≤ h := by omega
  have hd1 : 1 ≤ d := by omega
  have hq' : Q.eval (ρ - (h : ℤ) • α) = (h : ℤ) * d := by rw [hq2, hd]
  rw [voisLat_eq_map_reflQ hh1 hd1 hq' hv]
  congr 1
  -- $\mathrm{vois}_h(L; \rho - h\alpha) = \mathrm{vois}_h(L; \rho)$
  have hhv : (h : ℤ) ∣ bZ Q (ρ - (h : ℤ) • α) v - 1 := Dvd.dvd.trans (dvd_mul_right _ _) hv
  refine voisLat_congr hh1 (-α) (by rw [smul_neg, sub_eq_add_neg]) ⟨h + 1, hq⟩ ⟨d, hq'⟩ hw hhv
