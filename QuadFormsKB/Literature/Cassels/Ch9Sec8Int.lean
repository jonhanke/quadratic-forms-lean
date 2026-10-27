/-
# Cassels, Chapter 9, §8 (Theorem 1.5): representations by indefinite forms in $n \ge 4$ variables

**Layer:** integer-valued forms `f : QuadForm ℤ n` with $\det H \ne 0$ ($H$ the Hessian; Cassels' integral forms are
the classically integral ones, `IsClassicallyIntegral`); representations over $\mathbb Z_p$ = `ℤ_[p]` by vectors of
`Fin n → ℤ_[p]` and over $\mathbb Z$ by vectors of `Fin n → ℤ`; indefiniteness over $\mathbb R$ is stated concretely as
$f(\mathbf x) < 0 < f(\mathbf y)$ for some real vectors, and bridged to `Lattices.IsIndefinite` (isotropy at the
infinite place of $\mathbb Q$).

**Proves**
* Theorem 1.5, approximation form (`exists_rep_approx`): let $f$ be regular and indefinite in $n \ge 4$ variables, $a \ne 0$
  an integer represented by $f$ over every $\mathbb Z_p$ ($p = \infty$ is automatic: $f$ is indefinite). Let $P$ be a
  finite set of primes and $b_p \in \mathbb Z_p^n$ ($p \in P$) a representation of $a$. Then for every $k \in \mathbb N$
  there is $\mathbf x \in \mathbb Z^n$ with $f(\mathbf x) = a$ and $\mathbf x \equiv b_p \pmod{p^k}$ for all $p \in P$;
* Theorem 1.5, first assertion (`exists_rep_of_local`): $a$ is represented by $f$ over $\mathbb Z$.

*Generalization:* $f$ is only required to be integer-valued (Cassels: classically integral). "Arbitrarily close to
$b_p$" is "congruent modulo $p^k$ for any prescribed $k$".

*Proof:* Hasse–Minkowski gives $u \in \mathbb Q^n$ with $f(u) = a$; the strong approximation property for vectors
(`Lattices.vecApprox_of_indefinite`, O'Meara 104:3, adelic, not Cassels' proof) with the finite set $T$ of primes
dividing a denominator of $u$ or lying in $P$, the local vectors $b_p$ ($p \in P$) and arbitrary local representations
elsewhere, and neighbourhoods $b_p + p^k\mathbb Z_p^n$ (resp. $\mathbb Z_p^n$), gives $y \in \mathbb Q^n$, integral at every
prime, hence $y \in \mathbb Z^n$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec5
import QuadFormsKB.Lattices.SAVectorsAnisotropic

open NumberField IsDedekindDomain Matrix Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-- **Real indefiniteness gives a real isotropic vector:** if $f(\mathbf x) < 0 < f(\mathbf y)$ for real vectors
$\mathbf x, \mathbf y$, then $f(\mathbf z) = 0$ for some $\mathbf z \ne 0$ (intermediate value theorem on the segment
from $\mathbf x$ to $\mathbf y$, which avoids $0$ since $\mathbf x, \mathbf y$ are not negatively proportional). -/
theorem exists_real_isotropic_of_neg_pos (f : QuadForm ℤ n) (x y : Fin n → ℝ) (hx : f.evalIn ℝ x < 0)
    (hy : 0 < f.evalIn ℝ y) : ∃ z : Fin n → ℝ, z ≠ 0 ∧ f.evalIn ℝ z = 0 := by
  have hsmul : ∀ (c : ℝ) (w : Fin n → ℝ), f.evalIn ℝ (c • w) = c ^ 2 * f.evalIn ℝ w := by
    intro c w
    simp only [QuadForm.evalIn, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  let g : ℝ → ℝ := fun t => f.evalIn ℝ ((1 - t) • x + t • y)
  have hg : Continuous g := by
    simp only [g, QuadForm.evalIn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs <;> fun_prop
  have g0 : g 0 = f.evalIn ℝ x := by simp [g]
  have g1 : g 1 = f.evalIn ℝ y := by simp [g]
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (zero_le_one' ℝ) hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (g 0) (g 1) from ⟨by rw [g0]; exact hx.le, by rw [g1]; exact hy.le⟩)
  refine ⟨(1 - t) • x + t • y, ?_, hgt⟩
  intro hz
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp only [g] at hgt
    simp at hgt
    linarith
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp only [g] at hgt
    simp at hgt
    linarith
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hy' : y = (-((1 - t) / t)) • x := by
    have h1 : t • y = -((1 - t) • x) := eq_neg_of_add_eq_zero_right hz
    have : y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [this, h1, smul_neg, smul_smul, ← neg_smul]
    congr 1
    field_simp
  rw [hy', hsmul] at hy
  nlinarith [sq_nonneg ((1 - t) / t)]

/-- **Real indefiniteness gives `IsIndefinite`:** for $f(\mathbf x) < 0 < f(\mathbf y)$ with real $\mathbf x, \mathbf y$,
the rational form $f \otimes \mathbb Q$ is isotropic at the infinite place of $\mathbb Q$. -/
theorem isIndefinite_of_neg_pos (f : QuadForm ℤ n) (x y : Fin n → ℝ) (hx : f.evalIn ℝ x < 0)
    (hy : 0 < f.evalIn ℝ y) : IsIndefinite (f.map (Int.castRingHom ℚ)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace ℚ))
  obtain ⟨z, hz0, hz⟩ := exists_real_isotropic_of_neg_pos f x y hx hy
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  refine ⟨w, fun i => ψ.symm (z i), ?_, ?_⟩
  · intro h
    apply hz0
    funext i
    have := congrFun h i
    simpa using this
  · rw [evalIn_castHom_rat]
    have := hom_eval_castHom f ψ.symm.toRingHom z
    have e : (f.map (Int.castRingHom ℝ)).eval z = f.evalIn ℝ z := by
      simp [QuadForm.evalIn, QuadForm.map]
    rw [e, hz] at this
    simpa using this.symm

/-- **A real vector of value $a$ from real indefiniteness:** if $f(\mathbf x) < 0 < f(\mathbf y)$ and $a \ne 0$, then
$f(\mathbf z) = a$ for some real $\mathbf z$ (scale $\mathbf x$ or $\mathbf y$). -/
theorem exists_real_rep_of_neg_pos (f : QuadForm ℤ n) (x y : Fin n → ℝ) (hx : f.evalIn ℝ x < 0)
    (hy : 0 < f.evalIn ℝ y) {a : ℤ} (ha : a ≠ 0) : ∃ z : Fin n → ℝ, f.evalIn ℝ z = a := by
  have hsmul : ∀ (c : ℝ) (w : Fin n → ℝ), f.evalIn ℝ (c • w) = c ^ 2 * f.evalIn ℝ w := by
    intro c w
    simp only [QuadForm.evalIn, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rcases lt_or_gt_of_ne ha with h | h
  · have hr : (0 : ℝ) < (a : ℝ) / f.evalIn ℝ x := div_pos_of_neg_of_neg (by exact_mod_cast h) hx
    refine ⟨Real.sqrt ((a : ℝ) / f.evalIn ℝ x) • x, ?_⟩
    rw [hsmul, Real.sq_sqrt hr.le, div_mul_cancel₀ _ hx.ne]
  · have hr : (0 : ℝ) < (a : ℝ) / f.evalIn ℝ y := div_pos (by exact_mod_cast h) hy
    refine ⟨Real.sqrt ((a : ℝ) / f.evalIn ℝ y) • y, ?_⟩
    rw [hsmul, Real.sq_sqrt hr.le, div_mul_cancel₀ _ hy.ne']

/-- **The primes as a `Fact`:** a `Nat.Primes` has prime underlying natural number (so `ℤ_[p]` makes sense for
`p : Nat.Primes`). -/
instance factPrimeOfPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The integer form evaluated at an integer vector, viewed in $\mathbb Q$, is the rational form at the vector. -/
theorem evalIn_rat_intCast (f : QuadForm ℤ n) (x : Fin n → ℤ) :
    (f.map (Int.castRingHom ℚ)).evalIn ℚ (fun i => (x i : ℚ)) = ((f.eval x : ℤ) : ℚ) := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- **A representation over $\mathbb Z_p$ gives a representation over the completion $F_v$**, via the isomorphism
$\mathbb Z_p \cong \mathfrak o_v$ (`padicIntEquiv`) for the place $v$ over $p$. -/
theorem eval_locVec_of_padic (f : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) {a : ℤ}
    (x : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])
    (h : (f.map (Int.castRingHom ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])).eval x = a) :
    (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ)
      (fun i => (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm (x i) :
        v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) = algebraMap ℚ (v.adicCompletion ℚ) a := by
  let φ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv
  rw [evalIn_castHom_rat]
  have := hom_eval_castHom f ((v.adicCompletionIntegers ℚ).subtype.comp (φ : _ →+* _)) x
  rw [h] at this
  have h2 : (f.map (Int.castRingHom (v.adicCompletion ℚ))).eval
      (fun i => ((φ (x i) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) =
      algebraMap ℚ (v.adicCompletion ℚ) a := by simpa using this.symm
  exact h2

/-- **The congruence box is a neighbourhood:** for $c \in \mathbb Z_p^n$ and $k \in \mathbb N$ the set of
$y \in F_v^n$ whose coordinates are the images in $\mathfrak o_v \subseteq F_v$ of some $t \in \mathbb Z_p$ with
$p^k \mid t - c_i$ is a neighbourhood of (the image of) $c$. -/
theorem box_mem_nhds (v : HeightOneSpectrum (𝓞 ℚ)) (c : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])
    (k : ℕ) :
    {y : Fin n → v.adicCompletion ℚ | ∀ i, ∃ t : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)],
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) ^ k ∣ t - c i ∧
      (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm t : v.adicCompletionIntegers ℚ) :
        v.adicCompletion ℚ) = y i} ∈
      𝓝 (fun i => (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm (c i) :
        v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) := by
  set q : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ) with hq
  set φ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm with hφ
  have hopen : IsOpen ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    Valued.isOpen_valuationSubring (v.adicCompletion ℚ)
  refine Filter.mem_of_superset (set_pi_mem_nhds (Set.finite_univ (α := Fin n))
    (s := fun i => Subtype.val '' (φ.toHomeomorph '' {t : ℤ_[q] | (q : ℤ_[q]) ^ k ∣ t - c i}))
    fun i _ => ?_) ?_
  · have hD : {t : ℤ_[q] | (q : ℤ_[q]) ^ k ∣ t - c i} ∈ 𝓝 (c i) := by
      rw [Metric.mem_nhds_iff]
      have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
      refine ⟨(q : ℝ) ^ (-(k : ℤ) + 1), zpow_pos hq0 _, fun t ht => ?_⟩
      rw [Metric.mem_ball, dist_eq_norm] at ht
      have h1 := (PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one (t - c i) (-(k : ℤ) + 1)).mp ht
      rw [show -(k : ℤ) + 1 - 1 = -(k : ℤ) by ring] at h1
      have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (t - c i) k).mp h1
      exact Ideal.mem_span_singleton.mp h2
    have h1 : φ.toHomeomorph '' {t : ℤ_[q] | (q : ℤ_[q]) ^ k ∣ t - c i} ∈ 𝓝 (φ.toHomeomorph (c i)) := by
      rw [← φ.toHomeomorph.map_nhds_eq]
      exact Filter.image_mem_map hD
    have h2 := (hopen.isOpenEmbedding_subtypeVal).map_nhds_eq (φ (c i))
    rw [← h2]
    exact Filter.image_mem_map h1
  · intro y hy i
    obtain ⟨_, ⟨t, ht, rfl⟩, hty⟩ := hy i (Set.mem_univ i)
    exact ⟨t, ht, hty⟩

end QuadFormsKB.Lattices

namespace QuadFormsKB.Siegel

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-- **Cassels, Theorem 1.5, approximation form** (Ch. 9, p. 131): *let $f$ be a regular indefinite integral form in
$n \ge 4$ variables and let $a \ne 0$ be an integer. Suppose that $a$ is represented by $f$ over all $\mathbb Z_p$. Let
$P$ be a finite set of primes $p \ne \infty$ and for $p \in P$ let $b_p \in \mathbb Z_p^n$ be any representation of
$a$. Then there is a representation $\mathbf b \in \mathbb Z^n$ of $a$ such that $\mathbf b$ is arbitrarily close to $b_p$
for every $p \in P$.*

Hypotheses: `hn` ($n \ge 4$), `hf` ($\det H \ne 0$, regular), `hind` ($f$ is indefinite over $\mathbb R$:
$f(\mathbf x) < 0 < f(\mathbf y)$ for some real $\mathbf x, \mathbf y$; this gives the real representation of $a$, i.e. the
case $p = \infty$ of the local hypothesis), `ha` ($a \ne 0$), `hloc` ($a$ is represented over every $\mathbb Z_p$), `hb`
($b_p$ represents $a$ for $p \in P$; the value of `b p` for $p \notin P$ is irrelevant). "Arbitrarily close" is: for
every $k \in \mathbb N$, $\mathbf x_i \equiv (b_p)_i \pmod{p^k}$ in $\mathbb Z_p$ for all $i$ and $p \in P$.
Here $f$ is only integer-valued (module docstring). -/
@[kb "cassels1978" "Ch. 9, Thm. 1.5, p. 131 (approximation)"]
theorem exists_rep_approx (f : QuadForm ℤ n) (hn : 4 ≤ n) (hf : f.hessian.det ≠ 0)
    (hind : ∃ x y : Fin n → ℝ, f.evalIn ℝ x < 0 ∧ 0 < f.evalIn ℝ y) {a : ℤ} (ha : a ≠ 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p], (f.map (Int.castRingHom ℤ_[p])).eval x = a)
    (P : Finset Nat.Primes) (b : ∀ p : Nat.Primes, Fin n → ℤ_[(p : ℕ)])
    (hb : ∀ p ∈ P, (f.map (Int.castRingHom ℤ_[(p : ℕ)])).eval (b p) = a) (k : ℕ) :
    ∃ x : Fin n → ℤ, f.eval x = a ∧
      ∀ p ∈ P, ∀ i, ((p : ℕ) : ℤ_[(p : ℕ)]) ^ k ∣ (x i : ℤ_[(p : ℕ)]) - b p i := by
  classical
  obtain ⟨x₀, y₀, hx₀, hy₀⟩ := hind
  have hQ := Lattices.nondegenerate_map_of_det_ne_zero f hf
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hind' := Lattices.isIndefinite_of_neg_pos f x₀ y₀ hx₀ hy₀
  have hreal := Lattices.exists_real_rep_of_neg_pos f x₀ y₀ hx₀ hy₀ ha
  -- a rational representation (Hasse–Minkowski)
  have hrep : (f.map (Int.castRingHom ℚ)).RepresentsIn ℚ (a : ℚ) := by
    rw [represents_iff_everywhere_nf _ hQ _ haq]
    intro w
    cases w with
    | infinite w =>
      exact Lattices.representsIn_congr_alg _ _ _ _ (Lattices.representsIn_inf_of_real f hreal w)
    | finite v =>
      obtain ⟨p, hpdef⟩ : ∃ p : ℕ, (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := ⟨_, rfl⟩
      have : Fact p.Prime := ⟨hpdef ▸ (Rat.HeightOneSpectrum.primesEquiv v).2⟩
      obtain ⟨y, -, hy⟩ := Lattices.exists_mem_std_of_padic f v p hpdef (hloc p)
      exact ⟨y, hy⟩
  obtain ⟨u, hu⟩ := hrep
  have hu' : (f.map (Int.castRingHom ℚ)).evalIn ℚ u = a := by simpa using hu
  -- local data at every place
  have key : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ∃ (x : Fin n → ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) (m : ℕ),
        (f.map (Int.castRingHom ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])).eval x = a ∧
        (Rat.HeightOneSpectrum.primesEquiv v ∈ P → m = k ∧ x = b (Rat.HeightOneSpectrum.primesEquiv v)) := by
    intro v
    by_cases hv : Rat.HeightOneSpectrum.primesEquiv v ∈ P
    · exact ⟨b _, k, hb _ hv, fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨x, hx⟩ := hloc (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
      exact ⟨x, 0, hx, fun h => absurd h hv⟩
  choose xv mv hxv hxP using key
  -- the finite set of places
  have hT0 : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, Lattices.locVec v u ∈ Lattices.std v := by
    have h1 : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, v.valuation ℚ (u i) ≤ 1 :=
      fun i => Lattices.eventually_valuation_le_one (u i)
    rw [← Filter.eventually_all] at h1
    filter_upwards [h1] with v hv i
    rw [Lattices.locVec_apply, Lattices.valued_algebraMap]
    simpa using hv i
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    (Filter.eventually_cofinite.mp hT0).toFinset ∪ P.image (fun p => Rat.HeightOneSpectrum.primesEquiv.symm p)
    with hTdef
  have hT : ∀ v ∉ T, Lattices.locVec v u ∈ Lattices.std v := by
    intro v hv
    by_contra hc
    exact hv (Finset.mem_union_left _ ((Filter.eventually_cofinite.mp hT0).mem_toFinset.mpr hc))
  obtain ⟨y, hyv, hyZ, hyS⟩ := Lattices.vecApprox_of_indefinite _ hn hQ hind' u
    (by rw [hu']; exact haq) T hT
    (fun v i => (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm (xv v i) :
        v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ))
    (fun v _ => by rw [hu']; exact Lattices.eval_locVec_of_padic f v (xv v) (hxv v))
    (fun v => {y : Fin n → v.adicCompletion ℚ | ∀ i, ∃ t : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)],
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) ^ mv v ∣
        t - xv v i ∧
      (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm t :
        v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = y i})
    (fun v _ => Lattices.box_mem_nhds v (xv v) (mv v))
  -- integrality of `y` at every place
  have hint : ∀ v : HeightOneSpectrum (𝓞 ℚ), Lattices.locVec v y ∈ Lattices.std v := by
    intro v
    by_cases hv : v ∈ T
    · intro i
      obtain ⟨t, -, ht⟩ := hyZ v hv i
      rw [← ht]
      have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
        ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm t).2
      simpa using this
    · exact hyS v hv
  have hyZ' : ∀ i, y i ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
    intro i
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ (y i) fun v => ?_
    have := hint v i
    rw [Lattices.locVec_apply, Lattices.valued_algebraMap] at this
    simpa using this
  choose w hw using hyZ'
  set x : Fin n → ℤ := fun i => QuadFormsKB.Tamagawa.RatBridge.eZ (w i) with hxdef
  have hxy : ∀ i, (x i : ℚ) = y i := fun i => by
    rw [hxdef]; simp only
    rw [Lattices.eZ_cast_eq]; exact hw i
  have hxfun : (fun i => (x i : ℚ)) = y := funext hxy
  refine ⟨x, ?_, ?_⟩
  · have h1 := Lattices.evalIn_rat_intCast f x
    rw [hxfun, hyv, hu'] at h1
    exact_mod_cast h1.symm
  · have main : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (q : Nat.Primes)
        (hq : Rat.HeightOneSpectrum.primesEquiv v = q), q ∈ P → ∀ i,
        ((q : ℕ) : ℤ_[(q : ℕ)]) ^ k ∣ (x i : ℤ_[(q : ℕ)]) - b q i := by
      intro v q hq
      subst hq
      intro hqP i
      obtain ⟨hm, hxb⟩ := hxP v hqP
      obtain ⟨t, ht, hty⟩ := hyZ v (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨_, hqP, by simp⟩)) i
      rw [hm, hxb] at ht
      have hyi : (((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
          (x i : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) : v.adicCompletionIntegers ℚ) :
          v.adicCompletion ℚ) = Lattices.locVec v y i := by
        rw [Lattices.locVec_apply, ← hxy i]
        simp
      have hteq : t = (x i : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) := by
        have : (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm t =
            (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm
              (x i : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) :=
          Subtype.ext (hty.trans hyi.symm)
        exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.injective this
      rwa [← hteq]
    intro p hp i
    exact main (Rat.HeightOneSpectrum.primesEquiv.symm p) p (by simp) hp i

/-- **Cassels, Theorem 1.5** (Ch. 9, p. 131): *let $f$ be a regular indefinite integral form in $n \ge 4$ variables and
let $a \ne 0$ be an integer. Suppose that $a$ is represented by $f$ over all $\mathbb Z_p$. Then $a$ is represented by
$f$ over $\mathbb Z$.* Hypotheses as in `exists_rep_approx` (here $f$ is only integer-valued). -/
@[kb "cassels1978" "Ch. 9, Thm. 1.5, p. 131"]
theorem exists_rep_of_local (f : QuadForm ℤ n) (hn : 4 ≤ n) (hf : f.hessian.det ≠ 0)
    (hind : ∃ x y : Fin n → ℝ, f.evalIn ℝ x < 0 ∧ 0 < f.evalIn ℝ y) {a : ℤ} (ha : a ≠ 0)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p], (f.map (Int.castRingHom ℤ_[p])).eval x = a) :
    ∃ x : Fin n → ℤ, f.eval x = a := by
  obtain ⟨x, hx, -⟩ := exists_rep_approx f hn hf hind ha hloc ∅ (fun _ _ => 0) (by simp) 0
  exact ⟨x, hx⟩

end QuadFormsKB.Siegel
