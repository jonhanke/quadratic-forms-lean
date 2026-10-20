/-
# The maximal order of a local quaternion division algebra

**Layer:** $R$ a Henselian valuation ring (e.g. a complete DVR such as $\mathfrak o_v$) with fraction field $K$, and
$D = (a,b)_K$ ($a, b \in R$) a **division** algebra ($\operatorname{nrd}(x) = 0 \Rightarrow x = 0$).

**Contents.**
* `isInteger_trd_of_nrd`: $\operatorname{nrd}(x) \in R \Rightarrow \operatorname{trd}(x) \in R$ (Hensel's lemma applied to
  $y^2 - y + \operatorname{nrd}(x)/\operatorname{trd}(x)^2$: otherwise $x$ would have a root of its reduced characteristic polynomial in $K$,
  and $D$ would have zero divisors).
* `valOrder`: $\mathcal O = \{x \in D : \operatorname{nrd}(x) \in R\}$, a subring (the valuation ring of $w = v\circ\operatorname{nrd}/2$).
* `isOrder_valOrder`, `le_valOrder`, `isMaximalOrder_valOrder`, `eq_valOrder_of_isMaximalOrder`: $\mathcal O$ is an order
  ($R$ Noetherian), it contains every order, and it is **the unique maximal order** of $D$ (Voight Prop. 13.3.4, by the
  reduced-norm argument of Voight Remark 13.3.6 / Exercise 13.4).
* `mem_span_singleton_iff`: for $y \ne 0$ in $\mathcal O$, $x \in \mathcal O y \iff \operatorname{nrd}(x)/\operatorname{nrd}(y) \in R$; hence a left
  ideal $\mathcal Oy$ is determined by the ideal $(\operatorname{nrd}y)$ of $R$ (`span_singleton_eq_of_associated`), which gives the
  local ideal count "one integral left ideal of each reduced norm" at ramified places (Voight 13.3.10, Lemma 26.4.1).

Sources: Voight, *Quaternion Algebras* (2021), §13.3 (Prop. 13.3.4, Remark 13.3.6, 13.3.7–13.3.10).
-/
import QuadFormsKB.Tamagawa.QuatOrder

open Polynomial Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat IsLocalization IsLocalRing

section Local

variable {R K : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem nrd_add {a b : K} (x y : ℍ[K,a,b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  simp [nrd, trd]; ring

theorem isInteger_mul {s t : K} (hs : IsInteger R s) (ht : IsInteger R t) : IsInteger R (s * t) := by
  obtain ⟨u, rfl⟩ := hs; obtain ⟨v, rfl⟩ := ht; exact ⟨u * v, by simp⟩

theorem isInteger_add {s t : K} (hs : IsInteger R s) (ht : IsInteger R t) : IsInteger R (s + t) := by
  obtain ⟨u, rfl⟩ := hs; obtain ⟨v, rfl⟩ := ht; exact ⟨u + v, by simp⟩

theorem sub_mul_sub_algebraMap {A : Type*} [Ring A] [Algebra K A] (x : A) (z w : K) :
    (x - algebraMap K A z) * (x - algebraMap K A w) =
      x * x - algebraMap K A (z + w) * x + algebraMap K A (z * w) := by
  rw [sub_mul, mul_sub, mul_sub, ← Algebra.commutes w x, map_add, map_mul, add_mul]; abel

/-- **Integral reduced norm forces integral reduced trace** in a quaternion division algebra over a Henselian
valuation ring: if $\operatorname{nrd}(x) \in R$ then $\operatorname{trd}(x) \in R$.

*Proof.* Put $t = \operatorname{trd}x$, $n = \operatorname{nrd}x$. If $t \notin R$ then $u = t^{-1} \in \mathfrak m$, and $y^2 - y + nu^2$ has the
simple root $0$ modulo $\mathfrak m$; by Hensel it has a root $y \in R$, so $z = ty \in K$ is a root of $X^2 - tX + n$. Then
$(x - z)(x - (t - z)) = x^2 - tx + n = 0$, so $x \in K$ ($D$ is a division algebra), and then $x^2 = n \in R$ makes $x \in R$
and $t = 2x \in R$ ($R$ is integrally closed), a contradiction.

Source: Voight 2021, Remark 13.3.6 and Exercise 13.4 (the reduced-norm proof of Prop. 13.3.4). -/
@[kb "voight2021" "Remark 13.3.6"]
theorem isInteger_trd_of_nrd {a b : K} (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0) {x : ℍ[K,a,b]}
    (hn : IsInteger R (nrd x)) : IsInteger R (trd x) := by
  by_contra ht
  -- x is not a scalar: otherwise x = c, c² = nrd x ∈ R, so c ∈ R and trd x = 2c ∈ R.
  have hns : ∀ c : K, x ≠ algebraMap K ℍ[K,a,b] c := by
    rintro c rfl
    apply ht
    have hc : IsIntegral R c := by
      obtain ⟨m, hm⟩ := hn
      refine ⟨X ^ 2 - C m, (monic_X_pow 2).sub_of_left (by
        rw [degree_X_pow]; exact lt_of_le_of_lt degree_C_le (by norm_num)), ?_⟩
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hm]
      simp [nrd, QuaternionAlgebra.algebraMap_eq]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    exact ⟨2 * r, by simp [trd, QuaternionAlgebra.algebraMap_eq, hr, map_ofNat]⟩
  set t := trd x
  set n := nrd x
  have ht0 : t ≠ 0 := fun h => ht ⟨0, by rw [h, map_zero]⟩
  obtain ⟨u, hu⟩ := (ValuationRing.isInteger_or_isInteger R t).resolve_left ht
  have hum : u ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, rfl⟩
    apply ht
    refine ⟨(w⁻¹ : Rˣ), ?_⟩
    rw [← inv_inv t, ← hu, map_units_inv]
  obtain ⟨m, hm⟩ := hn
  set c : R := m * u ^ 2 with hc
  have hcm : c ∈ maximalIdeal R := Ideal.mul_mem_left _ m (by rw [pow_two]; exact Ideal.mul_mem_left _ u hum)
  set f : R[X] := X ^ 2 - X + C c with hf
  have hfm : f.Monic := by
    rw [hf, sub_eq_add_neg]
    refine ((monic_X_pow 2).add_of_left ?_).add_of_left ?_
    · rw [degree_neg, degree_X, degree_X_pow]; norm_num
    · refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_add_eq_left_of_degree_lt (by rw [degree_neg, degree_X, degree_X_pow]; norm_num), degree_X_pow]
      norm_num
  obtain ⟨y, hy, -⟩ := HenselianLocalRing.is_henselian f hfm 0
    (by simpa [hf] using hcm)
    (by simp [hf])
  have hy' : algebraMap R K y ^ 2 - algebraMap R K y + n * t⁻¹ ^ 2 = 0 := by
    have := congrArg (algebraMap R K) hy.eq_zero
    simp only [hf, eval_add, eval_sub, eval_pow, eval_X, eval_C, map_add, map_sub, map_pow,
      map_zero] at this
    rw [hc, map_mul, map_pow, hm, hu] at this
    exact this
  set z : K := t * algebraMap R K y
  have hz : z * (t - z) = n := by
    have : t ^ 2 * (algebraMap R K y ^ 2 - algebraMap R K y + n * t⁻¹ ^ 2) = 0 := by rw [hy', mul_zero]
    have e : t ^ 2 * (n * t⁻¹ ^ 2) = n := by field_simp
    simp only [z]; linear_combination (-1 : K) * this + e
  have hprod : (x - algebraMap K ℍ[K,a,b] z) * (x - algebraMap K ℍ[K,a,b] (t - z)) = 0 := by
    rw [sub_mul_sub_algebraMap, add_sub_cancel, hz, mul_self_eq x, Algebra.smul_def]; abel
  have h0 := congrArg nrd hprod
  rw [nrd_mul, show nrd (0 : ℍ[K,a,b]) = 0 by simp [nrd]] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact hns z (sub_eq_zero.1 (hdiv _ h))
  · exact hns _ (sub_eq_zero.1 (hdiv _ h))

end Local

section ValOrder

variable {R K : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {a b : K}

theorem nrd_algebraMap (c : K) : nrd (algebraMap K ℍ[K,a,b] c) = c ^ 2 := by
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

/-- **The valuation ring of a quaternion division algebra** $D = (a,b)_K$ over a Henselian valuation ring $R$:
$\mathcal O = \{x \in D : \operatorname{nrd}(x) \in R\}$, a subring by `isInteger_trd_of_nrd` and
$\operatorname{nrd}(x + y) = \operatorname{nrd}x + \operatorname{nrd}y + \operatorname{trd}(x\bar y)$.

Source: Voight 2021, 13.3.3 and Remark 13.3.6. -/
@[kb "voight2021" "13.3.3"]
def valOrder (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0) : Subalgebra R ℍ[K,a,b] where
  carrier := {x | IsInteger R (nrd x)}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, nrd_mul] at *; exact isInteger_mul hx hy
  one_mem' := ⟨1, by simp⟩
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, nrd_add] at *
    refine isInteger_add (isInteger_add hx hy) (isInteger_trd_of_nrd hdiv ?_)
    rw [nrd_mul, nrd_star]; exact isInteger_mul hx hy
  zero_mem' := ⟨0, by simp [nrd]⟩
  algebraMap_mem' r := by
    refine ⟨r ^ 2, ?_⟩
    rw [IsScalarTower.algebraMap_apply R K ℍ[K,a,b], nrd_algebraMap, map_pow]

variable (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0)

theorem mem_valOrder {x : ℍ[K,a,b]} : x ∈ valOrder (R := R) hdiv ↔ IsInteger R (nrd x) := Iff.rfl

/-- **Every order lies in the valuation ring** $\mathcal O$ (Voight Cor. 10.3.6: elements of orders have integral
reduced norm). -/
@[kb "voight2021" "Prop. 13.3.4"]
theorem le_valOrder {O : Subalgebra R ℍ[K,a,b]} (hO : IsOrder R K O) : O ≤ valOrder hdiv :=
  fun _ hx => (isInteger_trd_nrd hO hx).2

/-- **Units of $\mathcal O$:** $x \in \mathcal O^\times \iff \operatorname{nrd}(x) \in R^\times$ (here: $\operatorname{nrd}(x)^{-1} \in R$).

Source: Voight 2021, (13.3.8). -/
@[kb "voight2021" "(13.3.8)"]
theorem isUnit_valOrder_iff {x : ℍ[K,a,b]} (hx : x ∈ valOrder (R := R) hdiv) :
    IsUnit (⟨x, hx⟩ : valOrder (R := R) hdiv) ↔ nrd x ≠ 0 ∧ IsInteger R (nrd x)⁻¹ := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 := congrArg (fun z : valOrder (R := R) hdiv => nrd (z : ℍ[K,a,b])) w.mul_inv
    simp only [Subalgebra.coe_mul, nrd_mul, Subalgebra.coe_one, nrd_one, hw] at h1
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact (w⁻¹ : (valOrder (R := R) hdiv)ˣ).1.2
  · rintro ⟨hn, hinv⟩
    have hy : ((nrd x)⁻¹ • star x) ∈ valOrder (R := R) hdiv := by
      rw [mem_valOrder, nrd_smul, nrd_star]
      convert hinv using 1; field_simp
    refine ⟨⟨⟨x, hx⟩, ⟨_, hy⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
      rw [mul_smul_comm, mul_star_eq_nrd, ← QuaternionAlgebra.coe_smul, smul_eq_mul, inv_mul_cancel₀ hn]; rfl
    · simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
      rw [smul_mul_assoc, star_mul_eq_nrd, ← QuaternionAlgebra.coe_smul, smul_eq_mul, inv_mul_cancel₀ hn]; rfl

end ValOrder

section ValOrderMax

variable {R K : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {a b : R}
  (hdiv : ∀ x : ℍ[K,algebraMap R K a,algebraMap R K b], nrd x = 0 → x = 0)

theorem stdOrder_le_valOrder : stdOrder K a b ≤ valOrder (R := R) hdiv := by
  intro x hx
  obtain ⟨⟨r0, h0⟩, ⟨r1, h1⟩, ⟨r2, h2⟩, ⟨r3, h3⟩⟩ := mem_stdOrder.1 hx
  refine ⟨r0 ^ 2 - a * r1 ^ 2 - b * r2 ^ 2 + a * b * r3 ^ 2, ?_⟩
  simp [nrd, h0, h1, h2, h3]

/-- **The valuation ring is an order** ($R$ a Noetherian Henselian valuation ring, i.e. a Henselian DVR or a field,
$2ab \ne 0$): it is contained in $(2ab)^{-1}R\langle 1,i,j,k\rangle$ and contains $R\langle 1,i,j,k\rangle$.

Source: Voight 2021, Prop. 13.3.4. -/
@[kb "voight2021" "Prop. 13.3.4"]
theorem isOrder_valOrder [IsNoetherianRing R] (h2ab : algebraMap R K (2 * a * b) ≠ 0) :
    IsOrder R K (valOrder (R := R) hdiv) where
  fg := by
    have hN := isNoetherian_of_fg_of_noetherian _ (stdBound_fg (K := K) a b)
    exact Submodule.FG.of_le_of_isNoetherian
      (le_stdBound_of_trd h2ab (fun _ hy => isInteger_trd_of_nrd hdiv hy) (stdOrder_le_valOrder hdiv))
  span := eq_top_iff.2 ((isOrder_stdOrder (K := K) a b).span.symm.le.trans
    (Submodule.span_mono (stdOrder_le_valOrder hdiv)))

/-- **The unique maximal order of a local quaternion division algebra:** $\mathcal O = \{x : \operatorname{nrd}(x) \in R\}$
is a maximal order. -/
@[kb "voight2021" "Prop. 13.3.4"]
theorem isMaximalOrder_valOrder [IsNoetherianRing R] (h2ab : algebraMap R K (2 * a * b) ≠ 0) :
    IsMaximalOrder R K (valOrder (R := R) hdiv) :=
  ⟨isOrder_valOrder hdiv h2ab, fun _ hO' hle => le_antisymm (le_valOrder hdiv hO') hle⟩

/-- **Uniqueness:** every maximal order of the local division algebra $D$ is $\mathcal O$. -/
@[kb "voight2021" "Prop. 13.3.4"]
theorem eq_valOrder_of_isMaximalOrder [IsNoetherianRing R] (h2ab : algebraMap R K (2 * a * b) ≠ 0)
    {M : Subalgebra R ℍ[K,algebraMap R K a,algebraMap R K b]} (hM : IsMaximalOrder R K M) :
    M = valOrder (R := R) hdiv :=
  (hM.2 _ (isOrder_valOrder hdiv h2ab) (le_valOrder hdiv hM.1)).symm

end ValOrderMax

section Ideals

variable {R K : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [HenselianLocalRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] {a b : K}
  (hdiv : ∀ x : ℍ[K,a,b], nrd x = 0 → x = 0)

/-- **Left ideals of $\mathcal O$ are governed by the reduced norm:** for $x, y \in \mathcal O$, $y \ne 0$,
$x \in \mathcal O y \iff \operatorname{nrd}(x)/\operatorname{nrd}(y) \in R$ (take $z = xy^{-1}$, $\operatorname{nrd}z = \operatorname{nrd}x/\operatorname{nrd}y$).

Source: Voight 2021, 13.3.10. -/
@[kb "voight2021" "13.3.10"]
theorem mem_span_singleton_iff (x y : valOrder (R := R) hdiv) (hy : (y : ℍ[K,a,b]) ≠ 0) :
    x ∈ Ideal.span {y} ↔ IsInteger R (nrd (x : ℍ[K,a,b]) / nrd (y : ℍ[K,a,b])) := by
  have hn : nrd (y : ℍ[K,a,b]) ≠ 0 := fun h => hy (hdiv _ h)
  rw [Ideal.span, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, rfl⟩
    rw [smul_eq_mul, Subalgebra.coe_mul, nrd_mul, mul_div_cancel_right₀ _ hn]
    exact z.2
  · intro h
    have hz : (nrd (y : ℍ[K,a,b]))⁻¹ • ((x : ℍ[K,a,b]) * star (y : ℍ[K,a,b])) ∈ valOrder (R := R) hdiv := by
      rw [mem_valOrder, nrd_smul, nrd_mul, nrd_star]
      convert h using 1; field_simp
    refine ⟨⟨_, hz⟩, Subtype.ext ?_⟩
    rw [smul_eq_mul, Subalgebra.coe_mul]
    simp only
    rw [smul_mul_assoc, mul_assoc, star_mul_eq_nrd, ← QuaternionAlgebra.coe_algebraMap, ← Algebra.commutes,
      ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- **A principal left ideal is determined by the reduced norm of its generator** (up to units of $R$):
$\mathcal O x = \mathcal O y$ iff $\operatorname{nrd}x$ and $\operatorname{nrd}y$ divide each other in $R$. So there is at most one
integral left ideal $\mathcal O x$ of each reduced norm. -/
@[kb "voight2021" "13.3.10"]
theorem span_singleton_eq_iff (x y : valOrder (R := R) hdiv) (hx : (x : ℍ[K,a,b]) ≠ 0) (hy : (y : ℍ[K,a,b]) ≠ 0) :
    Ideal.span {x} = Ideal.span {y} ↔
      IsInteger R (nrd (x : ℍ[K,a,b]) / nrd (y : ℍ[K,a,b])) ∧ IsInteger R (nrd (y : ℍ[K,a,b]) / nrd (x : ℍ[K,a,b])) := by
  constructor
  · intro h
    exact ⟨(mem_span_singleton_iff hdiv x y hy).1 (h ▸ Ideal.subset_span rfl),
      (mem_span_singleton_iff hdiv y x hx).1 (h.symm ▸ Ideal.subset_span rfl)⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact (mem_span_singleton_iff hdiv x y hy).2 h1
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact (mem_span_singleton_iff hdiv y x hx).2 h2

/-- **Every left ideal of $\mathcal O$ is principal** ($R$ a Noetherian valuation ring): a nonzero left ideal $I$ is
$\mathcal O y$ for any $y \in I$ whose reduced norm generates the largest of the ideals $(\operatorname{nrd} x) \subseteq R$, $x \in I$.

Source: Voight 2021, 13.3.10. -/
@[kb "voight2021" "13.3.10"]
theorem exists_eq_span_singleton [IsNoetherianRing R] (I : Ideal (valOrder (R := R) hdiv)) :
    ∃ y : valOrder (R := R) hdiv, I = Ideal.span {y} := by
  by_cases hI : I = ⊥
  · exact ⟨0, by rw [hI, Ideal.span_singleton_eq_bot.2 rfl]⟩
  -- the R-element of the reduced norm
  have hint : ∀ x : valOrder (R := R) hdiv, ∃ r : R, algebraMap R K r = nrd (x : ℍ[K,a,b]) := fun x => x.2
  choose nr hnr using hint
  let S : Set (Ideal R) := {J | ∃ x ∈ I, (x : ℍ[K,a,b]) ≠ 0 ∧ J = Ideal.span {nr x}}
  have hS : S.Nonempty := by
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨_, x, hxI, fun h => hx0 (Subtype.ext h), rfl⟩
  obtain ⟨J, ⟨y, hyI, hy0, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 inferInstance S hS
  refine ⟨y, le_antisymm (fun x hxI => ?_) (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hyI)⟩
  by_cases hx0 : (x : ℍ[K,a,b]) = 0
  · have : x = 0 := Subtype.ext hx0
    rw [this]; exact Ideal.zero_mem _
  rw [mem_span_singleton_iff hdiv x y hy0]
  have hle : Ideal.span {nr x} ≤ Ideal.span {nr y} := by
    rcases (ValuationRing.le_total_ideal (A := R)).total (Ideal.span {nr x}) (Ideal.span {nr y}) with h | h
    · exact h
    · rcases h.lt_or_eq with h' | h'
      · exact absurd h' (hmax _ ⟨x, hxI, hx0, rfl⟩)
      · exact h'.ge
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hle (Ideal.mem_span_singleton_self _))
  refine ⟨c, ?_⟩
  have hn : nrd (y : ℍ[K,a,b]) ≠ 0 := fun h => hy0 (hdiv _ h)
  rw [eq_div_iff hn, ← hnr, ← hnr, ← map_mul, hc]

/-- **The reduced norm of a left ideal** $I$ of $\mathcal O$: the ideal of $R$ generated by the reduced norms of its elements. -/
def nrdIdeal (I : Ideal (valOrder (R := R) hdiv)) : Ideal R :=
  Ideal.span {r | ∃ x ∈ I, algebraMap R K r = nrd (x : ℍ[K,a,b])}

theorem nrdIdeal_span_singleton (y : valOrder (R := R) hdiv) {r : R} (hr : algebraMap R K r = nrd (y : ℍ[K,a,b])) :
    nrdIdeal hdiv (Ideal.span {y}) = Ideal.span {r} := by
  apply le_antisymm
  · rw [nrdIdeal, Ideal.span_le]
    rintro t ⟨x, hx, ht⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨u, hu⟩ := z.2
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    refine ⟨u, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hu, hr, ht, smul_eq_mul, Subalgebra.coe_mul, nrd_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨y, Ideal.mem_span_singleton_self y, hr⟩

/-- **At most one integral left ideal of each reduced norm** ($R$ a Noetherian Henselian valuation ring, $D$ division): left
ideals of $\mathcal O$ with the same reduced norm are equal. With `exists_eq_span_singleton`, the nonzero left ideals are
the $\mathcal O y$, classified by $(\operatorname{nrd}y)$; this is the local factor "one ideal of each norm" of $\zeta_{\mathcal O}$ at a
ramified place.

Source: Voight 2021, 13.3.10 and Lemma 26.4.1 (ramified case). -/
@[kb "voight2021" "Lemma 26.4.1"]
theorem eq_of_nrdIdeal_eq [IsNoetherianRing R] {I J : Ideal (valOrder (R := R) hdiv)}
    (h : nrdIdeal hdiv I = nrdIdeal hdiv J) : I = J := by
  obtain ⟨x, rfl⟩ := exists_eq_span_singleton hdiv I
  obtain ⟨y, rfl⟩ := exists_eq_span_singleton hdiv J
  obtain ⟨r, hr⟩ := x.2
  obtain ⟨t, ht⟩ := y.2
  rw [nrdIdeal_span_singleton hdiv x hr, nrdIdeal_span_singleton hdiv y ht] at h
  by_cases hx : (x : ℍ[K,a,b]) = 0
  · have hr0 : r = 0 := IsFractionRing.injective R K (by rw [hr, hx, map_zero]; simp [nrd])
    rw [hr0, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at h
    have hy : (y : ℍ[K,a,b]) = 0 := hdiv _ (by rw [← ht, h, map_zero])
    rw [show x = 0 from Subtype.ext hx, show y = 0 from Subtype.ext hy]
  by_cases hy : (y : ℍ[K,a,b]) = 0
  · have ht0 : t = 0 := IsFractionRing.injective R K (by rw [ht, hy, map_zero]; simp [nrd])
    rw [ht0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.span_singleton_eq_bot] at h
    exact absurd (hdiv _ (by rw [← hr, h, map_zero])) hx
  have hnx : nrd (x : ℍ[K,a,b]) ≠ 0 := fun h0 => hx (hdiv _ h0)
  have hny : nrd (y : ℍ[K,a,b]) ≠ 0 := fun h0 => hy (hdiv _ h0)
  rw [span_singleton_eq_iff hdiv x y hx hy]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self r)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self t)
  refine ⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩
  · rw [eq_div_iff hny, ← hr, ← ht, ← map_mul, hc]
  · rw [eq_div_iff hnx, ← hr, ← ht, ← map_mul, hd]

end Ideals

end QuadFormsKB.QuatOrder
