/-
# Regrouping of the archimedean places and the archimedean constant of the non-square model

**Layer:** an *arbitrary* number field $F$ (no total reality), $K = F(\delta)$ with $\delta^2 = d$, basis $(1,\delta)$ of $K/F$,
$\alpha = a$, $\beta = b$ in $\mathcal O_K$; **no** positivity or definiteness hypotheses on $a, b, d$ (only $a, b, d \ne 0$).

**Part 1** (regrouping of the infinite places of $K$ over those of $F$). For a function $f$ on the infinite places of $F$
with values in a commutative monoid, using the fibres of `InfinitePlace.comap` (`GnatNSPlaces`):
* `prod_real_comap`: $\prod_{w\ \mathrm{real}} f(w|_F) = \prod_{v\ \mathrm{real}} (f(v)^2$ if $\sigma_v(d) > 0$, else $1)$;
* `prod_complex_comap`: $\prod_{w\ \mathrm{complex}} f(w|_F) = \prod_{v\ \mathrm{real}} (1$ if $\sigma_v(d) > 0$, else $f(v))
  \cdot \prod_{v\ \mathrm{complex}} f(v)^2$;
* the counts `nrRealPlaces_eq`, `nrComplexPlaces_eq`:
  $r_1(K) = 2\,\#\{v\ \mathrm{real} : \sigma_v(d) > 0\}$ and $r_2(K) = \#\{v\ \mathrm{real} : \sigma_v(d) < 0\} + 2\,r_2(F)$.

**Part 2** (`const_identity_ns_any`). With $S$ = `nsBad`, $r_v$ = `nsRatio`, $K_\infty$ = `kInf`, $c_F$ = `cF`, and
$N$ the number of infinite places of $F$:
$$2^{N}\,8^{r_2(K)}\,K_\infty(K;\alpha,\beta)\Bigl(\prod_{v\in S} r_v\Bigr)2^{r_2(F)}
  = c_F(4)\,2^{6 r_2(F)}\Bigl(\prod_{v\ \mathrm{real}}\kappa_v\Bigr)\Bigl(\prod_{v\ \mathrm{complex}}\kappa_v\Bigr),$$
where, writing $a_v = \sigma_v(a)$, etc., $\kappa_v = 1/(32|a_v|^3|b_v|^3|d_v|^{15/2})$ at a real $v$ with $d_v > 0$,
$\kappa_v = 1/(4|a_v|^3|b_v|^3|d_v|^{15/2})$ at a real $v$ with $d_v < 0$, and
$\kappa_v = 1/(1024\|a_v\|^6\|b_v\|^6\|d_v\|^{15})$ at a complex $v$ (`nsKappaR`, `nsKappaC`).
The proof is the product formula (`finprod_norm_eq_inv_real_complex`) for $ab$ and $d$, `prod_relDisc_eq` for the
discriminants, and the regrouping of Part 1 for $K_\infty$.

Source: Weil 1982, Thm 2.3.1 (product formula).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSPlaces
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSArch
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFinal
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchRatio

open MeasureTheory Set Function NumberField NumberField.InfinitePlace IsDedekindDomain Module
open scoped ENNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

open QuadFormsKB.Lattices

/-! ### Part 1: regrouping the infinite places of $K$ over those of $F$ -/

section Regroup

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) {d : F} (hb₁ : bK 1 * bK 1 = algebraMap F K d)

include hb₀ hb₁ in
/-- Real place $v$ with $\sigma_v(d) > 0$: two real places of $K$ lie over $v$. -/
theorem card_realFiber_pos (v : {v : InfinitePlace F // v.IsReal}) (hpos : 0 < embedding_of_isReal v.2 d) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} => w.1.comap (algebraMap F K) = v.1).card = 2 := by
  obtain ⟨w₁, w₂, hne, h1, h2, hall, -, -⟩ := exists_two_real_places bK hb₀ hb₁ v hpos
  rw [Finset.card_eq_two]
  refine ⟨w₁, w₂, hne, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases hall w.1 h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    exacts [h1, h2]

include hb₀ hb₁ in
/-- Real place $v$ with $\sigma_v(d) < 0$: no real place of $K$ lies over $v$. -/
theorem card_realFiber_neg (v : {v : InfinitePlace F // v.IsReal}) (hneg : embedding_of_isReal v.2 d < 0) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} => w.1.comap (algebraMap F K) = v.1).card = 0 := by
  obtain ⟨w', -, -, hnone, -⟩ := exists_unique_complex_place bK hb₀ hb₁ v hneg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ h
  exact hnone w h

/-- Complex place $v$: no real place of $K$ lies over $v$. -/
theorem card_realFiber_complex (v : {v : InfinitePlace F // v.IsComplex}) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} => w.1.comap (algebraMap F K) = v.1).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ h
  have := w.2.comap (algebraMap F K)
  rw [h] at this
  exact (not_isReal_iff_isComplex.2 v.2) this

include hb₀ hb₁ in
/-- Real place $v$ with $\sigma_v(d) > 0$: no complex place of $K$ lies over $v$. -/
theorem card_complexFiber_pos (v : {v : InfinitePlace F // v.IsReal}) (hpos : 0 < embedding_of_isReal v.2 d) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsComplex} => w.1.comap (algebraMap F K) = v.1).card = 0 := by
  obtain ⟨w₁, w₂, -, -, -, -, hnone, -⟩ := exists_two_real_places bK hb₀ hb₁ v hpos
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ h
  exact hnone w h

include hb₀ hb₁ in
/-- Real place $v$ with $\sigma_v(d) < 0$: exactly one complex place of $K$ lies over $v$. -/
theorem card_complexFiber_neg (v : {v : InfinitePlace F // v.IsReal}) (hneg : embedding_of_isReal v.2 d < 0) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsComplex} => w.1.comap (algebraMap F K) = v.1).card = 1 := by
  obtain ⟨w', h1, hall, -⟩ := exists_unique_complex_place bK hb₀ hb₁ v hneg
  rw [Finset.card_eq_one]
  refine ⟨w', ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => Subtype.ext (hall w.1 h), fun h => h ▸ h1⟩

include hb₀ hb₁ in
/-- Complex place $v$: exactly two complex places of $K$ lie over $v$. -/
theorem card_complexFiber_complex (v : {v : InfinitePlace F // v.IsComplex}) :
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsComplex} => w.1.comap (algebraMap F K) = v.1).card = 2 := by
  obtain ⟨w₁, w₂, hne, h1, h2, hall⟩ := exists_two_complex_places bK hb₀ hb₁ v
  rw [Finset.card_eq_two]
  refine ⟨w₁, w₂, hne, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases hall w.1 h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    exacts [h1, h2]

include hb₀ hb₁ in
/-- **Regrouping over the real places of $K$**: $\prod_{w\ \mathrm{real}} f(w|_F)
= \prod_{v\ \mathrm{real}} (f(v)^2$ if $\sigma_v(d) > 0$, else $1)$. -/
theorem prod_real_comap {M : Type*} [CommMonoid M] (f : InfinitePlace F → M) :
    ∏ w : {w : InfinitePlace K // w.IsReal}, f (w.1.comap (algebraMap F K)) =
      ∏ v : {v : InfinitePlace F // v.IsReal}, (if 0 < embedding_of_isReal v.2 d then f v.1 ^ 2 else 1) := by
  rw [← Finset.prod_fiberwise' Finset.univ (fun w : {w : InfinitePlace K // w.IsReal} => w.1.comap (algebraMap F K)) f]
  simp only [Finset.prod_const]
  rw [prod_eq_prod_mul_prod (fun j : InfinitePlace F => f j ^
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} => w.1.comap (algebraMap F K) = j).card)]
  have hC : ∏ v : {v : InfinitePlace F // v.IsComplex}, f v.1 ^
      (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} => w.1.comap (algebraMap F K) = v.1).card = 1 :=
    Finset.prod_eq_one fun v _ => by rw [card_realFiber_complex, pow_zero]
  rw [hC, mul_one]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hne : embedding_of_isReal v.2 d ≠ 0 := (map_ne_zero _).2 (d_ne_zero bK hb₁)
  split_ifs with h
  · rw [card_realFiber_pos bK hb₀ hb₁ v h]
  · rw [card_realFiber_neg bK hb₀ hb₁ v (lt_of_le_of_ne (not_lt.1 h) hne), pow_zero]

include hb₀ hb₁ in
/-- **Regrouping over the complex places of $K$**: $\prod_{w\ \mathrm{complex}} f(w|_F)
= \prod_{v\ \mathrm{real}} (1$ if $\sigma_v(d) > 0$, else $f(v)) \cdot \prod_{v\ \mathrm{complex}} f(v)^2$. -/
theorem prod_complex_comap {M : Type*} [CommMonoid M] (f : InfinitePlace F → M) :
    ∏ w : {w : InfinitePlace K // w.IsComplex}, f (w.1.comap (algebraMap F K)) =
      (∏ v : {v : InfinitePlace F // v.IsReal}, (if 0 < embedding_of_isReal v.2 d then 1 else f v.1)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, f v.1 ^ 2 := by
  rw [← Finset.prod_fiberwise' Finset.univ (fun w : {w : InfinitePlace K // w.IsComplex} => w.1.comap (algebraMap F K)) f]
  simp only [Finset.prod_const]
  rw [prod_eq_prod_mul_prod (fun j : InfinitePlace F => f j ^
    (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsComplex} => w.1.comap (algebraMap F K) = j).card)]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    have hne : embedding_of_isReal v.2 d ≠ 0 := (map_ne_zero _).2 (d_ne_zero bK hb₁)
    split_ifs with h
    · rw [card_complexFiber_pos bK hb₀ hb₁ v h, pow_zero]
    · rw [card_complexFiber_neg bK hb₀ hb₁ v (lt_of_le_of_ne (not_lt.1 h) hne), pow_one]
  · exact Finset.prod_congr rfl fun v _ => by rw [card_complexFiber_complex bK hb₀ hb₁ v]

include hb₀ hb₁ in
/-- **Number of real places of $K$**: $r_1(K) = 2\,\#\{v\ \mathrm{real} : \sigma_v(d) > 0\}$. -/
theorem nrRealPlaces_eq :
    nrRealPlaces K = 2 * (Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} =>
      0 < embedding_of_isReal v.2 d).card := by
  have h := prod_real_comap bK hb₀ hb₁ (fun _ => (2 : ℕ))
  rw [Finset.prod_const, Finset.card_univ] at h
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const] at h
  have h' : 2 ^ nrRealPlaces K = 2 ^ (2 * (Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} =>
      0 < embedding_of_isReal v.2 d).card) := by
    rw [pow_mul]; exact h
  exact Nat.pow_right_injective (le_refl 2) h'

include hb₀ hb₁ in
/-- **Number of complex places of $K$**: $r_2(K) = \#\{v\ \mathrm{real} : \sigma_v(d) < 0\} + 2\,r_2(F)$. -/
theorem nrComplexPlaces_eq :
    nrComplexPlaces K = (Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} =>
      embedding_of_isReal v.2 d < 0).card + 2 * nrComplexPlaces F := by
  have h := prod_complex_comap bK hb₀ hb₁ (fun _ => (2 : ℕ))
  rw [Finset.prod_const, Finset.card_univ] at h
  have hne : ∀ v : {v : InfinitePlace F // v.IsReal}, embedding_of_isReal v.2 d ≠ 0 := fun v =>
    (map_ne_zero _).2 (d_ne_zero bK hb₁)
  have hfil : (Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} => ¬ 0 < embedding_of_isReal v.2 d) =
      Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} => embedding_of_isReal v.2 d < 0 :=
    Finset.filter_congr fun v _ => ⟨fun hv => lt_of_le_of_ne (not_lt.1 hv) (hne v), fun hv => not_lt.2 hv.le⟩
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hfil, Finset.prod_const, Finset.card_univ] at h
  have h' : 2 ^ nrComplexPlaces K = 2 ^ ((Finset.univ.filter fun v : {v : InfinitePlace F // v.IsReal} =>
      embedding_of_isReal v.2 d < 0).card + 2 * nrComplexPlaces F) := by
    rw [h, pow_add, pow_mul]
  exact Nat.pow_right_injective (le_refl 2) h'

end Regroup

/-! ### Part 2: the archimedean constant -/

section Const

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- The factor $f_{\mathbb R}(v) = 1/(8\,|a|_v^3\,|b|_v^3)$ of $K_\infty$ at a real place. -/
def nsFR (a b : F) (v : InfinitePlace F) : ℝ := 1 / (8 * v a ^ 3 * v b ^ 3)

/-- The factor $f_{\mathbb C}(v) = 1/(8\,|a|_v^3\,|b|_v^3)^2$ of $K_\infty$ at a complex place. -/
def nsFC (a b : F) (v : InfinitePlace F) : ℝ := 1 / (8 * v a ^ 3 * v b ^ 3) ^ 2

/-- **Archimedean constant at a real place $v$ of $F$**: with $a_v = \sigma_v(a)$ etc.,
$1/(32|a_v|^3|b_v|^3|d_v|^{15/2})$ if $d_v > 0$ and $1/(4|a_v|^3|b_v|^3|d_v|^{15/2})$ if $d_v < 0$. -/
def nsKappaR (a b d : F) (v : {v : InfinitePlace F // v.IsReal}) : ℝ :=
  if 0 < embedding_of_isReal v.2 d then
    1 / (32 * |embedding_of_isReal v.2 a| ^ 3 * |embedding_of_isReal v.2 b| ^ 3 *
      |embedding_of_isReal v.2 d| ^ ((15 : ℝ) / 2))
  else
    1 / (4 * |embedding_of_isReal v.2 a| ^ 3 * |embedding_of_isReal v.2 b| ^ 3 *
      |embedding_of_isReal v.2 d| ^ ((15 : ℝ) / 2))

/-- **Archimedean constant at a complex place $v$ of $F$**:
$1/(1024\,\|\sigma_v a\|^6\|\sigma_v b\|^6\|\sigma_v d\|^{15})$. -/
def nsKappaC (a b d : F) (v : {v : InfinitePlace F // v.IsComplex}) : ℝ :=
  1 / (1024 * ‖v.1.embedding a‖ ^ 6 * ‖v.1.embedding b‖ ^ 6 * ‖v.1.embedding d‖ ^ (15 : ℝ))

theorem abs_embedding_isReal (v : {v : InfinitePlace F // v.IsReal}) (x : F) :
    |embedding_of_isReal v.2 x| = v.1 x := by
  rw [← Real.norm_eq_abs]; exact norm_embedding_of_isReal v.2 x

/-- The archimedean norm in terms of the place absolute values. -/
theorem prod_places_expr (x : F) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, |sR w x|) * ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖sC w x‖ ^ 2 =
      (∏ w : {w : InfinitePlace F // w.IsReal}, w.1 x) * ∏ w : {w : InfinitePlace F // w.IsComplex}, (w.1 x) ^ 2 := by
  congr 1
  · exact Finset.prod_congr rfl fun w _ => abs_embedding_isReal w x
  · exact Finset.prod_congr rfl fun w _ => by rw [sC, norm_embedding_eq]

/-- $\|x\|_v = 1$ when $v(x) = 1$ (no total reality hypothesis). -/
theorem norm_algebraMap_eq_one_any {v : HeightOneSpectrum (𝓞 F)} {x : F} (hx : v.valuation F x = 1) :
    ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by
    intro h; rw [map_eq_zero_iff _ (algebraMap F _).injective] at h; rw [h, map_zero] at hx; exact zero_ne_one hx
  rw [LocalZeta.norm_eq_absNorm_pow v hx0, valued_algebraMap, hx, WithZero.log_one, zpow_zero]

/-- **Product formula over a finite set of places**: if $|x|_v = 1$ off $S$, then
$\prod_{v\in S}\|x\|_v = \bigl(\prod_{w\ \mathrm{real}} |x|_w \prod_{w\ \mathrm{complex}} |x|_w^2\bigr)^{-1}$. -/
theorem prod_norm_eq_of_good_any (S : Finset (HeightOneSpectrum (𝓞 F))) {x : F} (hx : x ≠ 0)
    (hS : ∀ v ∉ S, v.valuation F x = 1) :
    ∏ v ∈ S, ‖algebraMap F (v.adicCompletion F) x‖ =
      ((∏ w : {w : InfinitePlace F // w.IsReal}, w.1 x) * ∏ w : {w : InfinitePlace F // w.IsComplex}, (w.1 x) ^ 2)⁻¹ := by
  rw [← prod_places_expr, ← finprod_norm_eq_inv_real_complex x hx]
  exact (QuadFormsKB.Tamagawa.finprod_eq_prod_of_one S fun v hv =>
    norm_algebraMap_eq_one_any (hS v hv)).symm

theorem ohatVol_pow_six_any : ohatVol F ^ 6 = cF F 4 := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
  rw [ohatVol, cF, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num

variable {a b d : 𝓞 F} {bK : Module.Basis (Fin 2) F K} {α β : 𝓞 K}

/-- $K_\infty(K;\alpha,\beta)$ regrouped over the places of $F$. -/
theorem kInf_ns_eq (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F)) :
    kInf K α β = cF K 3 *
      (∏ v : {v : InfinitePlace F // v.IsReal},
        (if 0 < embedding_of_isReal v.2 (d : F) then nsFR (a : F) (b : F) v.1 ^ 2 else 1)) *
      ((∏ v : {v : InfinitePlace F // v.IsReal},
        (if 0 < embedding_of_isReal v.2 (d : F) then 1 else nsFC (a : F) (b : F) v.1)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, nsFC (a : F) (b : F) v.1 ^ 2) := by
  have hR : ∏ w : {w : InfinitePlace K // w.IsReal}, 1 / (8 * |sR w (α : K)| ^ 3 * |sR w (β : K)| ^ 3) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, nsFR (a : F) (b : F) (w.1.comap (algebraMap F K)) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    have h1 : |sR w (α : K)| = w.1.comap (algebraMap F K) (a : F) := by
      rw [sR, abs_embedding_isReal, hα]; rfl
    have h2 : |sR w (β : K)| = w.1.comap (algebraMap F K) (b : F) := by
      rw [sR, abs_embedding_isReal, hβ]; rfl
    rw [h1, h2, nsFR]
  have hC : ∏ w : {w : InfinitePlace K // w.IsComplex}, 1 / (8 * ‖sC w (α : K)‖ ^ 3 * ‖sC w (β : K)‖ ^ 3) ^ 2 =
      ∏ w : {w : InfinitePlace K // w.IsComplex}, nsFC (a : F) (b : F) (w.1.comap (algebraMap F K)) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    have h1 : ‖sC w (α : K)‖ = w.1.comap (algebraMap F K) (a : F) := by
      rw [sC, norm_embedding_eq, hα]; rfl
    have h2 : ‖sC w (β : K)‖ = w.1.comap (algebraMap F K) (b : F) := by
      rw [sC, norm_embedding_eq, hβ]; rfl
    rw [h1, h2, nsFC]
  rw [kInf, hR, hC, prod_real_comap (M := ℝ) bK hb₀ hb₁, prod_complex_comap (M := ℝ) bK hb₀ hb₁, mul_assoc]

/-- Per-place identity at a real place of $F$. -/
theorem nsX_eq_kappaR (a b d : F) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (v : {v : InfinitePlace F // v.IsReal}) :
    2 * (if 0 < embedding_of_isReal v.2 d then 1 else (8 : ℝ)) *
      (if 0 < embedding_of_isReal v.2 d then nsFR a b v.1 ^ 2 else 1) *
      (if 0 < embedding_of_isReal v.2 d then 1 else nsFC a b v.1) * (v.1 a * v.1 b) ^ 3 *
        (v.1 d ^ ((15 : ℝ) / 2))⁻¹ = nsKappaR a b d v := by
  have hu : 0 < v.1 a := (AbsoluteValue.pos_iff _).2 ha
  have hw : 0 < v.1 b := (AbsoluteValue.pos_iff _).2 hb
  have ht : 0 < v.1 d := (AbsoluteValue.pos_iff _).2 hd
  have he : 0 < v.1 d ^ ((15 : ℝ) / 2) := Real.rpow_pos_of_pos ht _
  unfold nsKappaR
  rw [abs_embedding_isReal, abs_embedding_isReal, abs_embedding_isReal]
  by_cases h : 0 < embedding_of_isReal v.2 d
  · simp only [h, ite_true, nsFR]
    field_simp
    ring
  · simp only [h, ite_false, nsFC]
    field_simp
    ring

/-- Per-place identity at a complex place of $F$. -/
theorem nsY_eq_kappaC (a b d : F) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (v : {v : InfinitePlace F // v.IsComplex}) :
    2 * 8 ^ 2 * nsFC a b v.1 ^ 2 * ((v.1 a * v.1 b) ^ 2) ^ 3 * ((v.1 d ^ 2) ^ ((15 : ℝ) / 2))⁻¹ * 2 =
      64 * nsKappaC a b d v := by
  have hu : 0 < v.1 a := (AbsoluteValue.pos_iff _).2 ha
  have hw : 0 < v.1 b := (AbsoluteValue.pos_iff _).2 hb
  have ht : 0 < v.1 d := (AbsoluteValue.pos_iff _).2 hd
  have h15 : (v.1 d ^ 2) ^ ((15 : ℝ) / 2) = v.1 d ^ (15 : ℝ) := by
    rw [← Real.rpow_natCast (v.1 d) 2, ← Real.rpow_mul ht.le]; norm_num
  have he : 0 < v.1 d ^ (15 : ℝ) := Real.rpow_pos_of_pos ht _
  unfold nsKappaC
  rw [norm_embedding_eq, norm_embedding_eq, norm_embedding_eq, h15]
  simp only [nsFC]
  field_simp
  ring

variable (bK) in
/-- **The archimedean constant identity of the non-square model over an arbitrary number field $F$.** -/
theorem const_identity_ns_any (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0) :
    (2 : ℝ) ^ Fintype.card (InfinitePlace F) * 8 ^ nrComplexPlaces K * kInf K α β *
        (∏ v ∈ nsBad (bK := bK) ha0 hb0 hd0, nsRatio K a b d v) * 2 ^ nrComplexPlaces F =
      cF F 4 * cxWeil F 4 * ((∏ v : {v : InfinitePlace F // v.IsReal}, nsKappaR (a : F) (b : F) (d : F) v) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, nsKappaC (a : F) (b : F) (d : F) v) := by
  classical
  set S := nsBad (bK := bK) ha0 hb0 hd0 with hSdef
  have hint := isIntegral_basis hb₀ hb₁
  have hSg : ∀ v ∉ S, relDisc K v = 1 ∧ v.valuation F ((a : F) * (b : F)) = 1 ∧ v.valuation F (d : F) = 1 := by
    intro v hv
    obtain ⟨-, hav, hbv, hdv, hdisc⟩ := nsGood_of_not_mem bK hv
    refine ⟨relDisc_eq_one hint hdisc, ?_, ?_⟩
    · rw [← valued_algebraMap, map_mul, Valuation.map_mul, hav, hbv, one_mul]
    · rw [← valued_algebraMap]; exact hdv
  have hab : (a : F) * (b : F) ≠ 0 := mul_ne_zero ha0 hb0
  have hpos : ∀ x : F, x ≠ 0 → ∀ v : InfinitePlace F, 0 < v x := fun x hx v => (AbsoluteValue.pos_iff _).2 hx
  -- the finite product
  have hP : ∏ v ∈ S, nsRatio K a b d v = (ohatVol K / ohatVol F ^ 2)⁻¹ ^ 3 *
      (((∏ w : {w : InfinitePlace F // w.IsReal}, w.1 (a : F) * w.1 (b : F)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (w.1 (a : F) * w.1 (b : F)) ^ 2) ^ 3) *
      (((∏ w : {w : InfinitePlace F // w.IsReal}, w.1 (d : F)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (w.1 (d : F)) ^ 2)⁻¹) ^ ((15 : ℝ) / 2) := by
    unfold nsRatio
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_inv_distrib,
      Finset.prod_inv_distrib, Real.finsetProd_rpow S _ (fun v _ => norm_nonneg _),
      prod_relDisc_eq S (fun v hv => (hSg v hv).1), prod_norm_eq_of_good_any S hab (fun v hv => (hSg v hv).2.1),
      prod_norm_eq_of_good_any S hd0 (fun v hv => (hSg v hv).2.2), inv_inv]
    simp only [map_mul]
  have hPd : (((∏ w : {w : InfinitePlace F // w.IsReal}, w.1 (d : F)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (w.1 (d : F)) ^ 2)⁻¹) ^ ((15 : ℝ) / 2) =
      ((∏ w : {w : InfinitePlace F // w.IsReal}, w.1 (d : F) ^ ((15 : ℝ) / 2)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, ((w.1 (d : F)) ^ 2) ^ ((15 : ℝ) / 2))⁻¹ := by
    have h1 : 0 ≤ ∏ w : {w : InfinitePlace F // w.IsReal}, w.1 (d : F) :=
      Finset.prod_nonneg fun w _ => (hpos _ hd0 _).le
    have h2 : 0 ≤ ∏ w : {w : InfinitePlace F // w.IsComplex}, (w.1 (d : F)) ^ 2 :=
      Finset.prod_nonneg fun w _ => sq_nonneg _
    rw [Real.inv_rpow (mul_nonneg h1 h2), Real.mul_rpow h1 h2,
      ← Real.finsetProd_rpow _ _ (fun w _ => (hpos _ hd0 _).le),
      ← Real.finsetProd_rpow _ _ (fun w _ => sq_nonneg _)]
  have hc : cF K 3 * (ohatVol K / ohatVol F ^ 2)⁻¹ ^ 3 = cF F 4 := by
    rw [← cF_three_eq, ← ohatVol_pow_six_any]
    have := ohatVol_pos (F := K)
    have := ohatVol_pos (F := F)
    field_simp
  have h2N : (2 : ℝ) ^ Fintype.card (InfinitePlace F) =
      (∏ v : {v : InfinitePlace F // v.IsReal}, (2 : ℝ)) * ∏ v : {v : InfinitePlace F // v.IsComplex}, (2 : ℝ) := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact prod_eq_prod_mul_prod (fun _ => (2 : ℝ))
  have h8 : (8 : ℝ) ^ nrComplexPlaces K =
      (∏ v : {v : InfinitePlace F // v.IsReal}, (if 0 < embedding_of_isReal v.2 (d : F) then 1 else (8 : ℝ))) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, (8 : ℝ) ^ 2 := by
    calc (8 : ℝ) ^ nrComplexPlaces K = ∏ w : {w : InfinitePlace K // w.IsComplex}, (8 : ℝ) := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = _ := prod_complex_comap bK hb₀ hb₁ (fun _ => (8 : ℝ))
  have h2r : (2 : ℝ) ^ nrComplexPlaces F = ∏ v : {v : InfinitePlace F // v.IsComplex}, (2 : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ]
  have hcx : cxWeil F 4 = ∏ v : {v : InfinitePlace F // v.IsComplex}, (64 : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, cxWeil, show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul]
  have hL : (2 : ℝ) ^ Fintype.card (InfinitePlace F) * 8 ^ nrComplexPlaces K * kInf K α β *
        (∏ v ∈ S, nsRatio K a b d v) * 2 ^ nrComplexPlaces F =
      cF F 4 * ((∏ v : {v : InfinitePlace F // v.IsReal},
          (2 * (if 0 < embedding_of_isReal v.2 (d : F) then 1 else (8 : ℝ)) *
            (if 0 < embedding_of_isReal v.2 (d : F) then nsFR (a : F) (b : F) v.1 ^ 2 else 1) *
            (if 0 < embedding_of_isReal v.2 (d : F) then 1 else nsFC (a : F) (b : F) v.1) *
            (v.1 (a : F) * v.1 (b : F)) ^ 3 * (v.1 (d : F) ^ ((15 : ℝ) / 2))⁻¹)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex},
          (2 * 8 ^ 2 * nsFC (a : F) (b : F) v.1 ^ 2 * ((v.1 (a : F) * v.1 (b : F)) ^ 2) ^ 3 *
            ((v.1 (d : F) ^ 2) ^ ((15 : ℝ) / 2))⁻¹ * 2)) := by
    rw [h2N, h8, kInf_ns_eq hb₀ hb₁ hα hβ, hP, hPd, ← hc, h2r]
    simp only [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
    ring
  have hR : cF F 4 * cxWeil F 4 * ((∏ v : {v : InfinitePlace F // v.IsReal}, nsKappaR (a : F) (b : F) (d : F) v) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, nsKappaC (a : F) (b : F) (d : F) v) =
      cF F 4 * ((∏ v : {v : InfinitePlace F // v.IsReal}, nsKappaR (a : F) (b : F) (d : F) v) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, (64 * nsKappaC (a : F) (b : F) (d : F) v)) := by
    rw [hcx]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hL, hR]
  congr 2
  · exact Finset.prod_congr rfl fun v _ => nsX_eq_kappaR (a : F) b d ha0 hb0 hd0 v
  · exact Finset.prod_congr rfl fun v _ => nsY_eq_kappaC (a : F) b d ha0 hb0 hd0 v

end Const

end

end QuadFormsKB.Tamagawa.Measure.Weil
