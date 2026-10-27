/-
# Lattices over $\mathcal O_F$: localization and the local–global correspondence

**Layer:** coordinates $V = F^n$ over a number field $F$. A *global lattice* is an $\mathcal O_F$-submodule
$L \subseteq F^n$ that is finitely generated and spans $F^n$ over $F$ (Mathlib's `Submodule.IsLattice F L`); it need
not be free. A *local lattice* at a finite prime $\mathfrak p$ (= `v : HeightOneSpectrum (𝓞 F)`) is an
$\mathfrak o_\mathfrak p$-submodule of $F_\mathfrak p^n$ that is finitely generated and spans $F_\mathfrak p^n$
(`Submodule.IsLattice F_𝔭`), where $F_\mathfrak p$ = `v.adicCompletion F` and $\mathfrak o_\mathfrak p$ =
`v.adicCompletionIntegers F`.

**Defines** the coordinatewise embedding $F^n \to F_\mathfrak p^n$ (`locVec`), the boxes
$\mathfrak p^k\mathfrak o_\mathfrak p^n = \{y : v(y_i) \le e^{-k}\ \forall i\}$ (`ball`, with $\mathfrak o_\mathfrak p^n$ =
`std`), the localization $L_\mathfrak p = \mathfrak o_\mathfrak p L$ (`loc`) and the gluing
$\mathrm{glue}(M) = \{x \in F^n : x \in M_\mathfrak p\ \forall \mathfrak p\}$ of a family of local lattices.

**Proves** the local–global correspondence for lattices over the Dedekind domain $\mathcal O_F$
(O'Meara 1963, §81E, p. 218: 81:14 and $L = \bigcap_\mathfrak p L_\mathfrak p$; Weil, *Basic Number Theory*, Ch. V, Thm. 2 [unverified]; the
$F = \mathbb Q$ case is Lemma 4.5.1 of the AWS notes, `AWS.LatticeGluing`, there an input):
* `loc_isLattice`: $L_\mathfrak p$ is a local lattice; `loc_eventually_std`: $L_\mathfrak p = \mathfrak o_\mathfrak p^n$ for
  almost all $\mathfrak p$;
* `mem_iff_forall_loc`: $L = \bigcap_\mathfrak p (F^n \cap L_\mathfrak p)$, so $L$ is determined by its localizations
  (`loc_injective`);
* `glue_isLattice`, `loc_glue` (**gluing**): every family $(M_\mathfrak p)$ of local lattices with
  $M_\mathfrak p = \mathfrak o_\mathfrak p^n$ for almost all $\mathfrak p$ is the family of localizations of the global
  lattice $\mathrm{glue}(M)$, and of no other (`existsUnique_loc_eq`).

*Proof idea.* Both lattices are sandwiched between boxes ($d\,\mathcal O_F^n \subseteq L \subseteq d^{-1}\mathcal O_F^n$,
`exists_global_bounds`; $\mathfrak p^k\mathfrak o^n \subseteq M \subseteq \mathfrak p^{-k}\mathfrak o^n$, `exists_local_bounds`).
Elements of $\mathfrak o_\mathfrak p$ are approximated by elements of $\mathcal O_F$ (`exists_approx_int`, from
$\mathcal O_F/\mathfrak p^k \cong \mathfrak o_\mathfrak p/\mathfrak p^k$) and denominators at finitely many other primes
are removed by the Chinese remainder theorem (`exists_crt`).
-/
import QuadFormsKB.LocalDensity.NFBridge

open NumberField IsDedekindDomain WithZero Matrix
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-! ### Valuations -/

section Valuations

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $v(x) = v_\mathfrak p(x)$ for $x \in F$ viewed in $F_\mathfrak p$. -/
theorem valued_algebraMap (x : F) : Valued.v (algebraMap F Fv x) = v.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

/-- $v(a) = v_\mathfrak p(a)$ for $a \in \mathcal O_F$ viewed in $F_\mathfrak p$. -/
theorem valued_algebraMap_int (a : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) Fv a) = v.intValuation a := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F Fv, valued_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap]

theorem algebraMap_int_coe (a : 𝓞 F) :
    ((algebraMap (𝓞 F) 𝔬 a : 𝔬) : Fv) = algebraMap (𝓞 F) Fv a := rfl

/-- Nonzero valuations are powers of $e$. -/
theorem exists_valued_eq_exp {x : Fv} (hx : x ≠ 0) : ∃ k : ℤ, Valued.v x = exp k := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
  exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩

/-- Every $x \in F_\mathfrak p$ has $v(x) \le e^{k}$ for some $k \in \mathbb N$. -/
theorem exists_valued_le (x : Fv) : ∃ k : ℕ, Valued.v x ≤ exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨k, hk⟩ := exists_valued_eq_exp v hx
    exact ⟨k.toNat, by rw [hk, exp_le_exp]; omega⟩

/-- A global element of valuation $e^{-1}$ (a uniformizer of $F_\mathfrak p$ coming from $F$). -/
def unifF : F := (v.valuation_exists_uniformizer F).choose

theorem valuation_unifF : v.valuation F (unifF v) = exp (-1 : ℤ) :=
  (v.valuation_exists_uniformizer F).choose_spec

theorem unifF_ne_zero : unifF v ≠ 0 := by
  intro h
  have := valuation_unifF v
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

theorem valued_unifF_zpow (k : ℤ) : Valued.v (algebraMap F Fv (unifF v ^ k)) = exp (-k) := by
  rw [valued_algebraMap, map_zpow₀, valuation_unifF, ← WithZero.exp_zsmul]
  congr 1; simp

/-- **Approximation by global integers:** every $c \in \mathfrak o_\mathfrak p$ is congruent to some $a \in \mathcal O_F$
modulo $\mathfrak p^K$ (from $\mathcal O_F/\mathfrak p^K \cong \mathfrak o_\mathfrak p/\mathfrak p^K$, `NF.redHom_surjective`). -/
theorem exists_approx_int (c : 𝔬) (K : ℕ) :
    ∃ a : 𝓞 F, Valued.v ((c : Fv) - algebraMap (𝓞 F) Fv a) ≤ exp (-(K : ℤ)) := by
  obtain ⟨a, ha⟩ := LocalDensity.NF.redHom_surjective v K (Ideal.Quotient.mk _ c)
  refine ⟨a, ?_⟩
  have h : c - LocalDensity.NF.ι v a ∈ Ideal.span {LocalDensity.NF.π v ^ K} := by
    rw [← Ideal.Quotient.eq]; exact ha.symm
  rw [LocalDensity.NF.mem_span_π_pow] at h
  rw [AddSubgroupClass.coe_sub] at h
  exact h

/-- **Approximation by global elements:** every $z \in F_\mathfrak p$ is within $e^{-K}$ of some $x \in F$. -/
theorem exists_approx (z : Fv) (K : ℤ) : ∃ x : F, Valued.v (z - algebraMap F Fv x) ≤ exp (-K) := by
  obtain ⟨j, hj⟩ := exists_valued_le v z
  set u : Fv := algebraMap F Fv (unifF v ^ (j : ℤ))
  have hu : Valued.v u = exp (-(j : ℤ)) := valued_unifF_zpow v j
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact exp_ne_zero hu.symm
  have hc : Valued.v (u * z) ≤ 1 := by
    rw [map_mul, hu]
    calc exp (-(j : ℤ)) * Valued.v z ≤ exp (-(j : ℤ)) * exp (j : ℤ) := mul_le_mul_right hj _
      _ = 1 := by rw [← exp_add]; simp
  set c : 𝔬 := ⟨u * z, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩
  obtain ⟨a, ha⟩ := exists_approx_int v c (K + j).toNat
  refine ⟨(a : F) / unifF v ^ (j : ℤ), ?_⟩
  have e : z - algebraMap F Fv ((a : F) / unifF v ^ (j : ℤ)) =
      u⁻¹ * ((c : Fv) - algebraMap (𝓞 F) Fv a) := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply]
    change z - _ / u = u⁻¹ * (u * z - _)
    field_simp
  rw [e, map_mul, map_inv₀, hu]
  calc (exp (-(j : ℤ)))⁻¹ * Valued.v ((c : Fv) - algebraMap (𝓞 F) Fv a)
      ≤ (exp (-(j : ℤ)))⁻¹ * exp (-((K + j).toNat : ℤ)) := mul_le_mul_right ha _
    _ ≤ exp (-K) := by
      rw [← WithZero.exp_neg, ← exp_add, exp_le_exp]; omega

/-- **Chinese remainder theorem with valuations:** for a finite set $S$ of primes not containing $\mathfrak p$ and
$K, e \in \mathbb N$, some $t \in \mathcal O_F$ has $t \equiv 1 \pmod{\mathfrak p^K}$ and $t \in \mathfrak q^e$ for all
$\mathfrak q \in S$. -/
theorem exists_crt (S : Finset (HeightOneSpectrum (𝓞 F))) (hv : v ∉ S) (K e : ℕ) :
    ∃ t : 𝓞 F, t - 1 ∈ v.asIdeal ^ K ∧ ∀ w ∈ S, t ∈ w.asIdeal ^ e := by
  classical
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v S)
    (fun w : HeightOneSpectrum (𝓞 F) => w.asIdeal) (fun w => if w = v then K else e)
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  refine ⟨y, ?_, fun w hw => ?_⟩
  · simpa using hy v (Finset.mem_insert_self _ _)
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    simpa [hwv] using hy w (Finset.mem_insert_of_mem hw)

/-- For $t \in \mathcal O_F$ with $t - 1 \in \mathfrak p^K$: $v(t - 1) \le e^{-K}$ in $F_\mathfrak p$. -/
theorem valued_sub_one_le {t : 𝓞 F} {K : ℕ} (h : t - 1 ∈ v.asIdeal ^ K) :
    Valued.v (algebraMap (𝓞 F) Fv t - 1) ≤ exp (-(K : ℤ)) := by
  have := (v.intValuation_le_pow_iff_mem _ K).mpr h
  rw [← valued_algebraMap_int, map_sub, map_one] at this
  exact this

/-- For $t \in \mathcal O_F$ with $t \in \mathfrak q^e$: $v_\mathfrak q(t) \le e^{-e}$ in $F_\mathfrak q$. -/
theorem valued_le_of_mem_pow {t : 𝓞 F} {e : ℕ} (h : t ∈ v.asIdeal ^ e) :
    Valued.v (algebraMap (𝓞 F) Fv t) ≤ exp (-(e : ℤ)) := by
  rw [valued_algebraMap_int]; exact (v.intValuation_le_pow_iff_mem _ e).mpr h

theorem valued_int_le_one (a : 𝓞 F) : Valued.v (algebraMap (𝓞 F) Fv a) ≤ 1 := by
  rw [valued_algebraMap_int]; exact v.intValuation_le_one a

end Valuations

/-- For $x \in F$, $v_\mathfrak p(x) \le 1$ for almost all $\mathfrak p$. -/
theorem eventually_valuation_le_one (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => ?_
  simpa [HeightOneSpectrum.Support] using hv

/-- A nonzero $d \in \mathcal O_F$ lies in only finitely many primes. -/
theorem eventually_not_mem {d : 𝓞 F} (hd : d ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, d ∉ v.asIdeal := by
  have hd' : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  filter_upwards [eventually_valuation_le_one (algebraMap (𝓞 F) F d)⁻¹] with v hv
  intro hmem
  have h1 : v.valuation F (algebraMap (𝓞 F) F d) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem v d).mpr hmem
  have h0 : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd'
  rw [map_inv₀] at hv
  have := (inv_le_one₀ (zero_lt_iff.mpr h0)).mp hv
  exact absurd (lt_of_lt_of_le h1 this) (lt_irrefl _)


/-! ### Boxes and local lattices -/

section LocalLattices

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The coordinatewise embedding** $F^n \to F_\mathfrak p^n$, $x \mapsto (x_0, \dots, x_{n-1})$, as an $F$-linear
map. -/
def locVec : (Fin n → F) →ₗ[F] (Fin n → Fv) :=
  LinearMap.pi fun i => (Algebra.linearMap F Fv).comp (LinearMap.proj i)

@[simp] theorem locVec_apply (x : Fin n → F) (i : Fin n) : locVec v x i = algebraMap F Fv (x i) := rfl

theorem locVec_smul_int (a : 𝓞 F) (x : Fin n → F) :
    locVec v (a • x) = (algebraMap (𝓞 F) 𝔬 a) • locVec v x := by
  ext i
  simp only [locVec_apply, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  rfl

theorem locVec_single (i : Fin n) (c : F) :
    locVec v (Pi.single i c) = Pi.single i (algebraMap F Fv c) := by
  ext j; by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The $\mathfrak o_\mathfrak p$-scalar action on $F_\mathfrak p^n$ is coordinatewise multiplication. -/
theorem smul_apply_coe (c : 𝔬) (y : Fin n → Fv) (i : Fin n) : (c • y) i = (c : Fv) * y i := rfl

/-- **The box** $\mathfrak p^k\mathfrak o_\mathfrak p^n = \{y \in F_\mathfrak p^n : v(y_i) \le e^{-k}\ \forall i\}$, an
$\mathfrak o_\mathfrak p$-submodule of $F_\mathfrak p^n$ ($k \in \mathbb Z$). -/
def ball (k : ℤ) : Submodule 𝔬 (Fin n → Fv) where
  carrier := {y | ∀ i, Valued.v (y i) ≤ exp (-k)}
  add_mem' ha hb i := Valuation.map_add_le _ (ha i) (hb i)
  zero_mem' i := by simp
  smul_mem' c y hy i := by
    change Valued.v ((c : Fv) * y i) ≤ _
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp c.2)).trans
      (hy i)

theorem mem_ball {k : ℤ} {y : Fin n → Fv} : y ∈ ball v k ↔ ∀ i, Valued.v (y i) ≤ exp (-k) := Iff.rfl

/-- **The standard local lattice** $\mathfrak o_\mathfrak p^n$. -/
abbrev std : Submodule 𝔬 (Fin n → Fv) := ball v 0

theorem ball_anti {k k' : ℤ} (h : k ≤ k') : ball v k' ≤ (ball v k : Submodule 𝔬 (Fin n → Fv)) :=
  fun _ hy i => (hy i).trans (by rw [exp_le_exp]; omega)

/-- The element $\varpi^k \in F_\mathfrak p$ ($\varpi$ = `unifF v`, $k \in \mathbb Z$), of valuation $e^{-k}$. -/
abbrev ϖk (k : ℤ) : Fv := algebraMap F Fv (unifF v ^ k)

theorem valued_ϖk (k : ℤ) : Valued.v (ϖk v k) = exp (-k) := valued_unifF_zpow v k

theorem ϖk_ne_zero (k : ℤ) : ϖk v k ≠ 0 := by
  intro h; have := valued_ϖk v k; rw [h, map_zero] at this; exact exp_ne_zero this.symm

theorem ϖk_mul (k l : ℤ) : ϖk v k * ϖk v l = ϖk v (k + l) := by
  change algebraMap F Fv _ * algebraMap F Fv _ = algebraMap F Fv _
  rw [← map_mul, ← zpow_add₀ (unifF_ne_zero v)]

/-- A coefficient of valuation $\le 1$, as an element of $\mathfrak o_\mathfrak p$. -/
def toO (c : Fv) (hc : Valued.v c ≤ 1) : 𝔬 := ⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hc⟩

/-- **Boxes from basis vectors:** if $\varpi^k e_i \in M$ for all $i$, then $\mathfrak p^k\mathfrak o^n \subseteq M$. -/
theorem ball_le_of_single_mem {M : Submodule 𝔬 (Fin n → Fv)} {k : ℤ}
    (h : ∀ i, Pi.single i (ϖk v k) ∈ M) : ball v k ≤ M := by
  intro y hy
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc : Valued.v (y i * (ϖk v k)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, valued_ϖk]
    calc Valued.v (y i) * (exp (-k))⁻¹ ≤ exp (-k) * (exp (-k))⁻¹ := mul_le_mul_left (hy i) _
      _ = 1 := mul_inv_cancel₀ exp_ne_zero
  have e : Pi.single i (y i) = toO v _ hc • (Pi.single i (ϖk v k) : Fin n → Fv) := by
    rw [← Pi.single_smul']; congr 1
    change y i = y i * (ϖk v k)⁻¹ * ϖk v k
    rw [inv_mul_cancel_right₀ (ϖk_ne_zero v k)]
  rw [e]; exact M.smul_mem _ (h i)

/-- $\varpi^{-k}e_i$ generate the box $\mathfrak p^{-k}\mathfrak o^n$... in the form: the box is finitely generated. -/
theorem ball_fg (k : ℤ) : (ball v k : Submodule 𝔬 (Fin n → Fv)).FG := by
  classical
  refine Submodule.FG.of_le (T := Submodule.span 𝔬 (Set.range fun i : Fin n => Pi.single i (ϖk v k)))
    (Submodule.fg_span (Set.finite_range _)) ?_
  exact ball_le_of_single_mem v fun i => Submodule.subset_span ⟨i, rfl⟩

/-- **Criterion for a local lattice:** an $\mathfrak o_\mathfrak p$-submodule sandwiched between two boxes,
$\mathfrak p^k\mathfrak o^n \subseteq M \subseteq \mathfrak p^{-k}\mathfrak o^n$, is a lattice in $F_\mathfrak p^n$. -/
theorem isLattice_of_bounds {M : Submodule 𝔬 (Fin n → Fv)} {k k' : ℤ} (h1 : ball v k ≤ M)
    (h2 : M ≤ ball v k') : M.IsLattice Fv where
  fg := Submodule.FG.of_le (ball_fg v k') h2
  span_eq_top := by
    rw [eq_top_iff]
    intro y _
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hm : Pi.single i (ϖk v k) ∈ M := by
      apply h1; intro j
      by_cases hj : j = i
      · subst hj; rw [Pi.single_eq_same]; exact (valued_ϖk v k).le
      · simp [hj]
    have e : Pi.single i (y i) = (y i * (ϖk v k)⁻¹) • Pi.single i (ϖk v k) := by
      rw [← Pi.single_smul, smul_eq_mul, inv_mul_cancel_right₀ (ϖk_ne_zero v k)]
    rw [e]; exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

/-- **Every local lattice is sandwiched between boxes:** $\mathfrak p^k\mathfrak o^n \subseteq M \subseteq
\mathfrak p^{-k}\mathfrak o^n$ for some $k \in \mathbb N$. -/
theorem exists_local_bounds {M : Submodule 𝔬 (Fin n → Fv)} (hM : M.IsLattice Fv) :
    ∃ k : ℕ, ball v k ≤ M ∧ M ≤ ball v (-k) := by
  classical
  -- upper bound from finitely many generators
  obtain ⟨s, hs⟩ := hM.fg
  have hup : ∃ k₁ : ℕ, ∀ y ∈ s, ∀ i, Valued.v (y i) ≤ exp (k₁ : ℤ) := by
    choose f hf using fun (y : Fin n → Fv) (i : Fin n) => exists_valued_le v (y i)
    refine ⟨s.sup fun y => Finset.univ.sup fun i => f y i, fun y hy i => (hf y i).trans ?_⟩
    rw [exp_le_exp, Nat.cast_le]
    exact (Finset.le_sup (f := fun i => f y i) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun y => Finset.univ.sup fun i => f y i) hy)
  obtain ⟨k₁, hk₁⟩ := hup
  -- lower bound: each basis vector is an `F_𝔭`-combination of elements of `M`
  have hlow : ∀ i, ∃ k : ℕ, Pi.single i (ϖk v k) ∈ M := by
    intro i
    have hi : Pi.single i (1 : Fv) ∈ Submodule.span Fv (M : Set (Fin n → Fv)) := by
      rw [hM.span_eq_top]; trivial
    obtain ⟨f, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hi
    choose g hg using fun a : Fin n → Fv => exists_valued_le v (f a)
    refine ⟨t.sup g, ?_⟩
    have e : Pi.single i (ϖk v (t.sup g : ℕ)) = ∑ a ∈ t, (ϖk v (t.sup g : ℕ) * f a) • a := by
      calc Pi.single i (ϖk v (t.sup g : ℕ)) = ϖk v (t.sup g : ℕ) • Pi.single i (1 : Fv) := by
            rw [← Pi.single_smul', smul_eq_mul, mul_one]
        _ = _ := by rw [← hsum, Finset.smul_sum]; simp_rw [mul_smul]
    rw [e]
    refine Submodule.sum_mem _ fun a ha => ?_
    have hc : Valued.v (ϖk v (t.sup g : ℕ) * f a) ≤ 1 := by
      rw [map_mul, valued_ϖk]
      calc exp (-((t.sup g : ℕ) : ℤ)) * Valued.v (f a) ≤ exp (-((t.sup g : ℕ) : ℤ)) * exp (g a : ℤ) :=
            mul_le_mul_right (hg a) _
        _ ≤ 1 := by
          rw [← exp_add, ← exp_zero, exp_le_exp]
          have : g a ≤ t.sup g := Finset.le_sup ha
          omega
    have : (ϖk v (t.sup g : ℕ) * f a) • a = toO v _ hc • a := rfl
    rw [this]; exact M.smul_mem _ (ht ha)
  choose kk hkk using hlow
  refine ⟨max k₁ (Finset.univ.sup kk), ?_, ?_⟩
  · refine ball_le_of_single_mem v fun i => ?_
    have hle : kk i ≤ max k₁ (Finset.univ.sup kk) :=
      (Finset.le_sup (f := kk) (Finset.mem_univ i)).trans (le_max_right _ _)
    have hc : Valued.v (ϖk v ((max k₁ (Finset.univ.sup kk) : ℕ) - kk i)) ≤ 1 := by
      rw [valued_ϖk, ← exp_zero, exp_le_exp]; omega
    have e : Pi.single i (ϖk v (max k₁ (Finset.univ.sup kk) : ℕ)) =
        toO v _ hc • (Pi.single i (ϖk v (kk i)) : Fin n → Fv) := by
      rw [← Pi.single_smul']; congr 1
      change _ = ϖk v _ * ϖk v _
      rw [ϖk_mul]; congr 1; ring
    rw [e]; exact M.smul_mem _ (hkk i)
  · rw [← hs, Submodule.span_le]
    intro y hy i
    refine (hk₁ y hy i).trans ?_
    rw [exp_le_exp]; push_cast; omega

end LocalLattices

/-! ### Global lattices -/

section GlobalLattices

/-- **The standard global lattice** $\mathcal O_F^n \subseteq F^n$ (vectors with integral coordinates). -/
def intVec : Submodule (𝓞 F) (Fin n → F) where
  carrier := {x | ∀ i, x i ∈ (algebraMap (𝓞 F) F).range}
  add_mem' {x y} hx hy i := by
    obtain ⟨a, ha⟩ := hx i; obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' i := ⟨0, by simp⟩
  smul_mem' c x hx i := by
    obtain ⟨a, ha⟩ := hx i
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem mem_intVec {x : Fin n → F} : x ∈ intVec ↔ ∀ i, x i ∈ (algebraMap (𝓞 F) F).range := Iff.rfl

theorem smul_apply_int (a : 𝓞 F) (x : Fin n → F) (i : Fin n) :
    (a • x) i = algebraMap (𝓞 F) F a * x i := by
  rw [Pi.smul_apply, Algebra.smul_def]

/-- **Integrality is local:** $x \in \mathcal O_F^n$ iff $v_\mathfrak p(x_i) \le 1$ for every prime $\mathfrak p$ and every
coordinate $i$. -/
theorem mem_intVec_iff_valuation {x : Fin n → F} :
    x ∈ intVec ↔ ∀ (w : HeightOneSpectrum (𝓞 F)) i, w.valuation F (x i) ≤ 1 := by
  constructor
  · intro hx w i
    obtain ⟨a, ha⟩ := hx i
    rw [← ha]; exact w.valuation_le_one a
  · intro h i
    exact HeightOneSpectrum.mem_integers_of_valuation_le_one F (x i) fun w => h w i

/-- Every $x \in F^n$ has a nonzero multiple $c\,x \in \mathcal O_F^n$, $c \in \mathcal O_F$. -/
theorem exists_smul_mem_intVec (x : Fin n → F) : ∃ c : 𝓞 F, c ≠ 0 ∧ c • x ∈ intVec := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image x)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hb (x i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact ⟨a, by rw [ha, Pi.smul_apply]⟩

theorem single_one_mem_intVec (i : Fin n) : (Pi.single i (1 : F) : Fin n → F) ∈ intVec := by
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

/-- An integral vector is an $\mathcal O_F$-combination of the basis vectors $e_i$. -/
theorem eq_sum_of_mem_intVec {x : Fin n → F} (hx : x ∈ intVec) :
    ∃ c : Fin n → 𝓞 F, x = ∑ i, c i • (Pi.single i (1 : F) : Fin n → F) := by
  choose c hc using hx
  refine ⟨c, ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul', Algebra.smul_def, mul_one, hc]

/-- **Every global lattice is sandwiched between boxes:** for some nonzero $d \in \mathcal O_F$,
$d\,\mathcal O_F^n \subseteq L$ and $d\,L \subseteq \mathcal O_F^n$. -/
theorem exists_global_bounds {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ (∀ x ∈ intVec, d • x ∈ L) ∧ (∀ x ∈ L, d • x ∈ intVec) := by
  classical
  -- upper bound
  obtain ⟨s, hs⟩ := hL.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (s.biUnion fun x => Finset.univ.image x)
  have hup : ∀ x ∈ L, (b : 𝓞 F) • x ∈ intVec := by
    rw [← hs]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro i
      obtain ⟨a, ha⟩ := hb (x i) (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _
        (Finset.mem_univ i)⟩)
      exact ⟨a, by rw [ha, Pi.smul_apply]⟩
    | zero => rw [smul_zero]; exact intVec.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact intVec.add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact intVec.smul_mem a hx
  -- lower bound
  have hlow : ∀ i : Fin n, ∃ c : 𝓞 F, c ≠ 0 ∧ c • (Pi.single i (1 : F) : Fin n → F) ∈ L := by
    intro i
    have hi : (Pi.single i (1 : F) : Fin n → F) ∈ Submodule.span F (L : Set (Fin n → F)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨f, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hi
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
      (t.image f)
    refine ⟨c, nonZeroDivisors.coe_ne_zero c, ?_⟩
    rw [← hsum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    obtain ⟨e, he⟩ := hc (f a) (Finset.mem_image_of_mem _ ha)
    have : (c : 𝓞 F) • f a • a = e • a := by
      rw [← smul_assoc, ← algebraMap_smul F e a, he]
    rw [this]; exact L.smul_mem e (ht ha)
  choose c hc0 hc using hlow
  set c' : 𝓞 F := ∏ i, c i
  have hc'0 : c' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i
  have hlow' : ∀ x ∈ intVec, c' • x ∈ L := by
    intro x hx
    obtain ⟨a, rfl⟩ := eq_sum_of_mem_intVec hx
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ : c i ∣ c' := Finset.dvd_prod_of_mem c (Finset.mem_univ i)
    rw [hr, smul_comm, mul_comm, mul_smul]
    exact L.smul_mem _ (L.smul_mem _ (hc i))
  refine ⟨(b : 𝓞 F) * c', mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hc'0, ?_, ?_⟩
  · intro x hx
    rw [mul_comm, mul_smul]
    exact hlow' _ (intVec.smul_mem _ hx)
  · intro x hx
    rw [mul_comm, mul_smul]
    exact intVec.smul_mem _ (hup x hx)

/-- **Criterion for a global lattice:** an $\mathcal O_F$-submodule $L \subseteq F^n$ with
$d\,\mathcal O_F^n \subseteq L$ and $d\,L \subseteq \mathcal O_F^n$ for some nonzero $d$ is a lattice. -/
theorem isLattice_of_global_bounds {L : Submodule (𝓞 F) (Fin n → F)} {d : 𝓞 F} (hd : d ≠ 0)
    (h1 : ∀ x ∈ intVec, d • x ∈ L) (h2 : ∀ x ∈ L, d • x ∈ intVec) : L.IsLattice F where
  fg := by
    classical
    have hd' : algebraMap (𝓞 F) F d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    refine Submodule.FG.of_le (Submodule.fg_span (Set.finite_range fun i : Fin n =>
      (algebraMap (𝓞 F) F d)⁻¹ • (Pi.single i (1 : F) : Fin n → F))) ?_
    intro x hx
    obtain ⟨a, ha⟩ := eq_sum_of_mem_intVec (h2 x hx)
    have : x = ∑ i, a i • ((algebraMap (𝓞 F) F d)⁻¹ • (Pi.single i (1 : F) : Fin n → F)) := by
      have e : x = (algebraMap (𝓞 F) F d)⁻¹ • (d • x) := by
        rw [← algebraMap_smul F d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
      rw [e, ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  span_eq_top := by
    have hd' : algebraMap (𝓞 F) F d ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    rw [eq_top_iff]
    intro x _
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hm := h1 _ (single_one_mem_intVec i)
    have e : (Pi.single i (x i) : Fin n → F) =
        (x i * (algebraMap (𝓞 F) F d)⁻¹) • (d • (Pi.single i (1 : F) : Fin n → F)) := by
      rw [← algebraMap_smul F d, smul_smul, inv_mul_cancel_right₀ hd', ← Pi.single_smul', smul_eq_mul,
        mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

end GlobalLattices

/-! ### Localization -/

section Localization

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The localization** $L_\mathfrak p = \mathfrak o_\mathfrak p L \subseteq F_\mathfrak p^n$ of an $\mathcal O_F$-submodule
$L \subseteq F^n$: the $\mathfrak o_\mathfrak p$-span of the image of $L$ under $F^n \to F_\mathfrak p^n$. -/
@[kb "omeara1963" "§81E, p. 217 (localization L_𝔭)"]
def loc (L : Submodule (𝓞 F) (Fin n → F)) : Submodule 𝔬 (Fin n → Fv) :=
  Submodule.span 𝔬 (locVec v '' L)

theorem locVec_mem_loc {L : Submodule (𝓞 F) (Fin n → F)} {x : Fin n → F} (hx : x ∈ L) :
    locVec v x ∈ loc v L :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem loc_mono {L L' : Submodule (𝓞 F) (Fin n → F)} (h : L ≤ L') : loc v L ≤ loc v L' :=
  Submodule.span_mono (Set.image_mono h)

theorem locVec_smul_int_apply (d : 𝓞 F) (x : Fin n → F) (i : Fin n) :
    locVec v (d • x) i = algebraMap (𝓞 F) Fv d * algebraMap F Fv (x i) := by
  rw [locVec_smul_int, smul_apply_coe, algebraMap_int_coe, locVec_apply]

/-- If $d\,\mathcal O_F^n \subseteq L$ and $v(d) = e^{-k}$, then $\mathfrak p^k\mathfrak o^n \subseteq L_\mathfrak p$. -/
theorem ball_le_loc {L : Submodule (𝓞 F) (Fin n → F)} {d : 𝓞 F} (h1 : ∀ x ∈ intVec, d • x ∈ L)
    {k : ℤ} (hk : Valued.v (algebraMap (𝓞 F) Fv d) = exp (-k)) : ball v k ≤ loc v L := by
  have hD : algebraMap (𝓞 F) Fv d ≠ 0 := by
    intro h; rw [h, map_zero] at hk; exact exp_ne_zero hk.symm
  intro y hy
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hc : Valued.v (y i * (algebraMap (𝓞 F) Fv d)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, hk]
    calc Valued.v (y i) * (exp (-k))⁻¹ ≤ exp (-k) * (exp (-k))⁻¹ := mul_le_mul_left (hy i) _
      _ = 1 := mul_inv_cancel₀ exp_ne_zero
  have hm := locVec_mem_loc v (h1 _ (single_one_mem_intVec i))
  have e : (Pi.single i (y i) : Fin n → Fv) = toO v _ hc • locVec v (d • (Pi.single i (1 : F) : Fin n → F)) := by
    rw [locVec_smul_int, locVec_single, smul_smul, map_one, ← Pi.single_smul']
    congr 1
    change y i = y i * (algebraMap (𝓞 F) Fv d)⁻¹ * algebraMap (𝓞 F) Fv d * 1
    rw [mul_one, inv_mul_cancel_right₀ hD]
  rw [e]; exact Submodule.smul_mem _ _ hm

/-- If $d\,L \subseteq \mathcal O_F^n$ and $v(d) = e^{-k}$, then $L_\mathfrak p \subseteq \mathfrak p^{-k}\mathfrak o^n$. -/
theorem loc_le_ball {L : Submodule (𝓞 F) (Fin n → F)} {d : 𝓞 F} (h2 : ∀ x ∈ L, d • x ∈ intVec)
    {k : ℤ} (hk : Valued.v (algebraMap (𝓞 F) Fv d) = exp (-k)) : loc v L ≤ ball v (-k) := by
  rw [loc, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩ i
  obtain ⟨a, ha⟩ := h2 x hx i
  have h : Valued.v (algebraMap (𝓞 F) Fv d * algebraMap F Fv (x i)) ≤ 1 := by
    rw [← locVec_smul_int_apply, locVec_apply, ← ha, ← IsScalarTower.algebraMap_apply]
    exact valued_int_le_one v a
  rw [map_mul, hk] at h
  rw [locVec_apply, neg_neg]
  calc Valued.v (algebraMap F Fv (x i)) = exp k * (exp (-k) * Valued.v (algebraMap F Fv (x i))) := by
        rw [← mul_assoc, ← exp_add]; simp
    _ ≤ exp k * 1 := mul_le_mul_right h _
    _ = exp k := mul_one _

/-- For nonzero $d \in \mathcal O_F$: $v(d) = e^{-k}$ for some $k \in \mathbb N$. -/
theorem exists_valued_int_eq {d : 𝓞 F} (hd : d ≠ 0) :
    ∃ k : ℕ, Valued.v (algebraMap (𝓞 F) Fv d) = exp (-(k : ℤ)) := by
  have hD : algebraMap (𝓞 F) Fv d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F Fv]
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F Fv).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
    exact hd
  obtain ⟨k, hk⟩ := exists_valued_eq_exp v hD
  have hle := valued_int_le_one v d
  rw [hk, ← exp_zero, exp_le_exp] at hle
  exact ⟨(-k).toNat, by rw [hk]; congr 1; omega⟩

/-- **$L_\mathfrak p$ is a lattice** in $F_\mathfrak p^n$ (finitely generated over $\mathfrak o_\mathfrak p$, spanning). -/
@[kb "omeara1963" "§81E, pp. 217–218"]
theorem loc_isLattice {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    (loc v L).IsLattice Fv := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  obtain ⟨k, hk⟩ := exists_valued_int_eq v hd
  exact isLattice_of_bounds v (ball_le_loc v h1 hk) (loc_le_ball v h2 hk)

/-- If $d\,\mathcal O_F^n \subseteq L$, $d\,L \subseteq \mathcal O_F^n$ and $d \notin \mathfrak p$, then
$L_\mathfrak p = \mathfrak o_\mathfrak p^n$. -/
theorem loc_eq_std_of_not_mem {L : Submodule (𝓞 F) (Fin n → F)} {d : 𝓞 F}
    (h1 : ∀ x ∈ intVec, d • x ∈ L) (h2 : ∀ x ∈ L, d • x ∈ intVec) (hv : d ∉ v.asIdeal) :
    loc v L = std v := by
  have hk : Valued.v (algebraMap (𝓞 F) Fv d) = exp (-(0 : ℤ)) := by
    rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff.mpr hv]; simp
  exact le_antisymm (by simpa using loc_le_ball v h2 hk) (ball_le_loc v h1 hk)

end Localization

/-- **$L_\mathfrak p = \mathfrak o_\mathfrak p^n$ for almost all $\mathfrak p$** (O'Meara §81E, p. 218, the remark before 81:14; AWS notes
p. 61 for $F = \mathbb Q$, `AWS.loc_eventually_std`). -/
@[kb "omeara1963" "§81E, p. 218 (L_𝔭 = K_𝔭 for almost all 𝔭, from 81:11)"]
theorem loc_eventually_std {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, loc v L = std v := by
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  filter_upwards [eventually_not_mem hd] with v hv
  exact loc_eq_std_of_not_mem v h1 h2 hv

/-! ### Approximation and the Chinese remainder theorem for families of local lattices -/

/-- A family $(M_\mathfrak q)_\mathfrak q$ of local lattices with $M_\mathfrak q = \mathfrak o_\mathfrak q^n$ for almost all
$\mathfrak q$ (the data of the gluing theorem). -/
structure LocFamily (F : Type*) [Field F] [NumberField F] (n : ℕ) where
  /-- The local lattice $M_\mathfrak q \subseteq F_\mathfrak q^n$. -/
  M : ∀ w : HeightOneSpectrum (𝓞 F), Submodule (w.adicCompletionIntegers F) (Fin n → w.adicCompletion F)
  /-- Each $M_\mathfrak q$ is a lattice. -/
  isLattice : ∀ w, (M w).IsLattice (w.adicCompletion F)
  /-- $M_\mathfrak q = \mathfrak o_\mathfrak q^n$ for almost all $\mathfrak q$. -/
  eventually_std : ∀ᶠ w in Filter.cofinite, M w = std w

/-- **The standard family** $(\mathfrak o_\mathfrak q^n)_\mathfrak q$. -/
def LocFamily.std : LocFamily F n where
  M w := Lattices.std w
  isLattice w := isLattice_of_bounds w le_rfl le_rfl
  eventually_std := Filter.Eventually.of_forall fun _ => rfl

/-- **Chinese remainder theorem for a family of local lattices:** for $x \in F^n$ and $K \in \mathbb N$ there is
$t \in \mathcal O_F$ with $t \equiv 1 \pmod{\mathfrak p^K}$ and $t\,x \in M_\mathfrak q$ for every prime $\mathfrak q \ne \mathfrak p$. -/
theorem LocFamily.exists_crt (M : LocFamily F n) (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → F) (K : ℕ) :
    ∃ t : 𝓞 F, t - 1 ∈ v.asIdeal ^ K ∧ ∀ w, w ≠ v → locVec w (t • x) ∈ M.M w := by
  classical
  have hB : {w | ¬ M.M w = Lattices.std w}.Finite := Filter.eventually_cofinite.mp M.eventually_std
  have hP : (⋃ i, HeightOneSpectrum.Support (𝓞 F) (x i)).Finite :=
    Set.finite_iUnion fun i => HeightOneSpectrum.Support.finite (𝓞 F) (x i)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (hB.union hP).toFinset.erase v
  choose k hk using fun w => exists_local_bounds w (M.isLattice w)
  choose N hN using fun (w : HeightOneSpectrum (𝓞 F)) (i : Fin n) =>
    exists_valued_le w (algebraMap F (w.adicCompletion F) (x i))
  set e : ℕ := S.sup fun w => k w + Finset.univ.sup (N w)
  obtain ⟨t, ht1, ht⟩ := Lattices.exists_crt v S (Finset.notMem_erase v _) K e
  refine ⟨t, ht1, fun w hw => ?_⟩
  by_cases hS : w ∈ S
  · refine (hk w).1 fun i => ?_
    rw [locVec_smul_int_apply, map_mul]
    have h1 := valued_le_of_mem_pow w (ht w hS)
    have hle : k w + N w i ≤ e :=
      (Nat.add_le_add_left (Finset.le_sup (f := N w) (Finset.mem_univ i)) _).trans
        (Finset.le_sup (f := fun w => k w + Finset.univ.sup (N w)) hS)
    calc Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) t) *
          Valued.v (algebraMap F (w.adicCompletion F) (x i))
        ≤ exp (-(e : ℤ)) * exp (N w i : ℤ) := mul_le_mul' h1 (hN w i)
      _ ≤ exp (-(k w : ℤ)) := by rw [← exp_add, exp_le_exp]; omega
  · have hw' : w ∉ {w | ¬ M.M w = Lattices.std w} ∪ ⋃ i, HeightOneSpectrum.Support (𝓞 F) (x i) := by
      intro hmem; exact hS (Finset.mem_erase.mpr ⟨hw, (Set.Finite.mem_toFinset _).mpr hmem⟩)
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_not, Set.mem_iUnion, not_or, not_exists] at hw'
    rw [hw'.1]
    intro i
    rw [locVec_smul_int_apply, map_mul, neg_zero, exp_zero]
    have hx : Valued.v (algebraMap F (w.adicCompletion F) (x i)) ≤ 1 := by
      have := hw'.2 i
      simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt] at this
      rwa [valued_algebraMap]
    exact mul_le_one' (valued_int_le_one w t) hx

/-- **Removing denominators away from $\mathfrak p$:** if $x \in F^n$ is integral at $\mathfrak p$, then $t\,x \in \mathcal O_F^n$
for some $t \in \mathcal O_F \setminus \mathfrak p$. -/
theorem exists_not_mem_smul_mem_intVec (v : HeightOneSpectrum (𝓞 F)) {x : Fin n → F}
    (hx : ∀ i, v.valuation F (x i) ≤ 1) : ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ t • x ∈ intVec := by
  obtain ⟨t, ht1, ht⟩ := (LocFamily.std (F := F) (n := n)).exists_crt v x 1
  refine ⟨t, fun hmem => ?_, ?_⟩
  · have : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem hmem (by simpa using ht1)
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · rw [mem_intVec_iff_valuation]
    intro w i
    by_cases hw : w = v
    · subst hw
      rw [smul_apply_int, map_mul]
      exact mul_le_one' (w.valuation_le_one t) (hx i)
    · have := ht w hw i
      rw [locVec_apply, valued_algebraMap, neg_zero, exp_zero] at this
      exact this

section Approx

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Approximation in $L_\mathfrak p$ by elements of $L$:** every $m \in L_\mathfrak p$ is within
$\mathfrak p^K\mathfrak o^n$ of some $y \in L$. -/
theorem exists_mem_approx {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) {m : Fin n → Fv}
    (hm : m ∈ loc v L) (K : ℤ) : ∃ y ∈ L, locVec v y - m ∈ ball v K := by
  obtain ⟨d, hd, -, h2⟩ := exists_global_bounds hL
  obtain ⟨k₁, hk₁⟩ := exists_valued_int_eq v hd
  have hbd := loc_le_ball v h2 hk₁
  induction hm using Submodule.span_induction generalizing K with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, by rw [sub_self]; exact Submodule.zero_mem _⟩
  | zero => exact ⟨0, L.zero_mem, by rw [map_zero, sub_self]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx K
    obtain ⟨b, hb, hb'⟩ := hy K
    refine ⟨a + b, L.add_mem ha hb, ?_⟩
    rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ ha' hb'
  | smul c m hm ih =>
    obtain ⟨a, ha⟩ := exists_approx_int v c (K + k₁).toNat
    obtain ⟨y, hy, hy'⟩ := ih K
    refine ⟨a • y, L.smul_mem a hy, ?_⟩
    have e : locVec v (a • y) - c • m =
        algebraMap (𝓞 F) 𝔬 a • (locVec v y - m) + (algebraMap (𝓞 F) 𝔬 a - c) • m := by
      rw [locVec_smul_int, smul_sub, sub_smul]; abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy') fun i => ?_
    rw [smul_apply_coe, map_mul, AddSubgroupClass.coe_sub, algebraMap_int_coe,
      Valuation.map_sub_swap]
    have hmi := hbd hm i
    rw [neg_neg] at hmi
    calc Valued.v ((c : Fv) - algebraMap (𝓞 F) Fv a) * Valued.v (m i)
        ≤ exp (-((K + k₁).toNat : ℤ)) * exp (k₁ : ℤ) := mul_le_mul' ha hmi
      _ ≤ exp (-K) := by rw [← exp_add, exp_le_exp]; omega

end Approx

/-- **A lattice is the intersection of its localizations** (O'Meara §81E, p. 218; for $F = \mathbb Q$,
`AWS.mem_iff_forall_loc`): $x \in L$ iff $x \in L_\mathfrak p$ for every prime $\mathfrak p$. -/
@[kb "omeara1963" "§81E, p. 218 (L = ⋂_𝔭 (V ∩ L_𝔭))"]
theorem mem_iff_forall_loc {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) (x : Fin n → F) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 F), locVec v x ∈ loc v L := by
  refine ⟨fun hx v => locVec_mem_loc v hx, fun h => ?_⟩
  -- the conductor ideal `I = {a | a • x ∈ L}`
  set I : Ideal (𝓞 F) := L.comap (LinearMap.toSpanSingleton (𝓞 F) (Fin n → F) x)
  have hI : ∀ a, a ∈ I ↔ a • x ∈ L := fun a => Iff.rfl
  by_contra hx
  have hItop : I ≠ ⊤ := by
    intro htop
    have : (1 : 𝓞 F) ∈ I := htop ▸ Submodule.mem_top
    rw [hI, one_smul] at this; exact hx this
  obtain ⟨d, hd, h1, h2⟩ := exists_global_bounds hL
  obtain ⟨c, hc0, hc⟩ := exists_smul_mem_intVec x
  have hIbot : I ≠ ⊥ := by
    intro hbot
    have : d * c ∈ I := by rw [hI, mul_smul]; exact h1 _ hc
    rw [hbot, Ideal.mem_bot] at this
    exact mul_ne_zero hd hc0 this
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hItop
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPmax.isPrime, fun h => hIbot (eq_bot_iff.mpr (h ▸ hIP))⟩
  obtain ⟨k₀, hk₀⟩ := exists_valued_int_eq v hd
  obtain ⟨y, hy, hy'⟩ := exists_mem_approx v hL (h v) k₀
  set z := x - y
  have hd' : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hz' : ∀ i, v.valuation F (((algebraMap (𝓞 F) F d)⁻¹ • z) i) ≤ 1 := by
    intro i
    have := hy' i
    rw [show (locVec v y - locVec v x) i = -algebraMap F (v.adicCompletion F) (z i) by
      simp [z]] at this
    rw [Valuation.map_neg, valued_algebraMap] at this
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [valued_algebraMap_int, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)] at hk₀
    rw [hk₀]
    calc (exp (-(k₀ : ℤ)))⁻¹ * v.valuation F (z i) ≤ (exp (-(k₀ : ℤ)))⁻¹ * exp (-(k₀ : ℤ)) :=
          mul_le_mul_right this _
      _ = 1 := inv_mul_cancel₀ exp_ne_zero
  obtain ⟨t, htv, ht⟩ := exists_not_mem_smul_mem_intVec v hz'
  have htz : t • z ∈ L := by
    have := h1 _ ht
    rwa [smul_comm, ← algebraMap_smul F d, smul_smul, mul_inv_cancel₀ hd', one_smul] at this
  have htx : t ∈ I := by
    rw [hI, show x = z + y by simp [z]]
    rw [smul_add]; exact L.add_mem htz (L.smul_mem t hy)
  exact htv (hIP htx)

/-- **A lattice is determined by its localizations** (for $F = \mathbb Q$, `AWS.loc_injective`). -/
theorem loc_injective {L L' : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) (hL' : L'.IsLattice F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), loc v L = loc v L') : L = L' := by
  ext x
  rw [mem_iff_forall_loc hL, mem_iff_forall_loc hL']
  simp only [h]

/-- **Inclusions of lattices are local:** $L \subseteq L'$ iff $L_\mathfrak p \subseteq L'_\mathfrak p$ for all $\mathfrak p$. -/
theorem le_iff_forall_loc {L L' : Submodule (𝓞 F) (Fin n → F)} (hL' : L'.IsLattice F) :
    L ≤ L' ↔ ∀ v : HeightOneSpectrum (𝓞 F), loc v L ≤ loc v L' := by
  refine ⟨fun h v => loc_mono v h, fun h x hx => ?_⟩
  rw [mem_iff_forall_loc hL']
  exact fun v => h v (locVec_mem_loc v hx)

/-! ### Gluing -/

namespace LocFamily

/-- **The gluing** $\mathrm{glue}(M) = \{x \in F^n : x \in M_\mathfrak p \text{ for every prime } \mathfrak p\}$ of a family of local
lattices: an $\mathcal O_F$-submodule of $F^n$. -/
@[kb "omeara1963" "§81E, 81:14, p. 218"]
def glue (M : LocFamily F n) : Submodule (𝓞 F) (Fin n → F) where
  carrier := {x | ∀ w, locVec w x ∈ M.M w}
  add_mem' hx hy w := by rw [map_add]; exact (M.M w).add_mem (hx w) (hy w)
  zero_mem' w := by rw [map_zero]; exact (M.M w).zero_mem
  smul_mem' c x hx w := by rw [locVec_smul_int]; exact (M.M w).smul_mem _ (hx w)

theorem mem_glue {M : LocFamily F n} {x : Fin n → F} : x ∈ M.glue ↔ ∀ w, locVec w x ∈ M.M w := Iff.rfl

/-- The glued module is sandwiched between boxes: $D\,\mathcal O_F^n \subseteq \mathrm{glue}(M)$ and
$D\,\mathrm{glue}(M) \subseteq \mathcal O_F^n$, with $D = \prod_{\mathfrak q \in S} \varpi_\mathfrak q^N$ over the finitely many
$\mathfrak q$ with $M_\mathfrak q \ne \mathfrak o_\mathfrak q^n$. -/
theorem glue_bounds (M : LocFamily F n) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (∀ x ∈ intVec, D • x ∈ M.glue) ∧ (∀ x ∈ M.glue, D • x ∈ intVec) := by
  classical
  have hB : {w | ¬ M.M w = Lattices.std w}.Finite := Filter.eventually_cofinite.mp M.eventually_std
  set S := hB.toFinset
  choose k hk using fun w => exists_local_bounds w (M.isLattice w)
  set N : ℕ := S.sup k
  set D : 𝓞 F := ∏ w ∈ S, LocalDensity.NF.unif w ^ N
  have hunif : ∀ w : HeightOneSpectrum (𝓞 F), LocalDensity.NF.unif w ≠ 0 := by
    intro w h
    have := LocalDensity.NF.intValuation_unif w
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hunif w)
  have hDv : ∀ w ∈ S, Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) ≤ exp (-(N : ℤ)) := by
    intro w hw
    rw [valued_algebraMap_int]
    change w.intValuation (∏ x ∈ S, LocalDensity.NF.unif x ^ N) ≤ _
    rw [← Finset.mul_prod_erase S _ hw, map_mul, map_pow,
      LocalDensity.NF.intValuation_unif]
    calc exp (-1 : ℤ) ^ N * w.intValuation (∏ x ∈ S.erase w, LocalDensity.NF.unif x ^ N)
        ≤ exp (-1 : ℤ) ^ N * 1 := mul_le_mul_right (w.intValuation_le_one _) _
      _ = exp (-(N : ℤ)) := by rw [mul_one, ← WithZero.exp_nsmul]; congr 1; simp
  have hkN : ∀ w ∈ S, k w ≤ N := fun w hw => Finset.le_sup (f := k) hw
  have hstd : ∀ w ∉ S, M.M w = Lattices.std w := by
    intro w hw; by_contra h; exact hw ((Set.Finite.mem_toFinset _).mpr h)
  refine ⟨D, hD0, ?_, ?_⟩
  · intro x hx w
    choose a ha using hx
    by_cases hw : w ∈ S
    · refine (hk w).1 fun i => ?_
      rw [locVec_smul_int_apply, map_mul]
      have hxi : Valued.v (algebraMap F (w.adicCompletion F) (x i)) ≤ 1 := by
        rw [← ha i, ← IsScalarTower.algebraMap_apply]; exact valued_int_le_one w _
      calc Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) *
            Valued.v (algebraMap F (w.adicCompletion F) (x i))
          ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hDv w hw) hxi
        _ ≤ exp (-(k w : ℤ)) := by rw [mul_one, exp_le_exp]; have := hkN w hw; omega
    · rw [hstd w hw]
      intro i
      rw [locVec_smul_int_apply, map_mul, neg_zero, exp_zero]
      refine mul_le_one' (valued_int_le_one w D) ?_
      rw [← ha i, ← IsScalarTower.algebraMap_apply]; exact valued_int_le_one w _
  · intro x hx
    rw [mem_intVec_iff_valuation]
    intro w i
    rw [smul_apply_int, ← valued_algebraMap, map_mul, map_mul, ← IsScalarTower.algebraMap_apply]
    by_cases hw : w ∈ S
    · have hxi := (hk w).2 (hx w) i
      rw [locVec_apply, neg_neg] at hxi
      calc Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) *
            Valued.v (algebraMap F (w.adicCompletion F) (x i))
          ≤ exp (-(N : ℤ)) * exp (k w : ℤ) := mul_le_mul' (hDv w hw) hxi
        _ ≤ 1 := by rw [← exp_add, ← exp_zero, exp_le_exp]; have := hkN w hw; omega
    · have hxi := hx w
      rw [hstd w hw] at hxi
      have := hxi i
      rw [locVec_apply, neg_zero, exp_zero] at this
      exact mul_le_one' (valued_int_le_one w D) this

/-- **The glued module is a lattice.** -/
theorem glue_isLattice (M : LocFamily F n) : M.glue.IsLattice F := by
  obtain ⟨D, hD, h1, h2⟩ := M.glue_bounds
  exact isLattice_of_global_bounds hD h1 h2

/-- **Gluing (existence half of the local–global correspondence):** the localizations of $\mathrm{glue}(M)$ are the
$M_\mathfrak p$ (O'Meara §81E, 81:14, p. 218; Weil, *Basic Number Theory*, Ch. V, Thm. 2 [unverified]). For
$F = \mathbb Q$ this is the AWS notes' Lemma 4.5.1 (`AWS.LatticeGluing`, an input there). -/
@[kb "omeara1963" "§81E, 81:14, p. 218"]
theorem loc_glue (M : LocFamily F n) (v : HeightOneSpectrum (𝓞 F)) : loc v M.glue = M.M v := by
  apply le_antisymm
  · rw [loc, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx v
  · intro m hm
    obtain ⟨D, hD, h1, -⟩ := M.glue_bounds
    obtain ⟨k₀, hk₀⟩ := exists_valued_int_eq v hD
    obtain ⟨kv, hkv1, hkv2⟩ := exists_local_bounds v (M.isLattice v)
    set K : ℕ := max k₀ kv
    have hball : ball v K ≤ loc v M.glue ⊓ M.M v :=
      le_inf ((ball_anti v (by simp [K])).trans (ball_le_loc v h1 hk₀))
        ((ball_anti v (by simp [K])).trans hkv1)
    choose z hz using fun i => exists_approx v (m i) (K : ℤ)
    obtain ⟨t, ht1, ht⟩ := M.exists_crt v z (K + kv)
    have hdiff : locVec v (t • z) - m ∈ ball v K := by
      intro i
      have hmi := hkv2 hm i
      rw [neg_neg] at hmi
      have hzi : Valued.v (algebraMap F (v.adicCompletion F) (z i)) ≤ exp (kv : ℤ) := by
        have e : algebraMap F (v.adicCompletion F) (z i) =
            m i - (m i - algebraMap F (v.adicCompletion F) (z i)) := by ring
        rw [e]
        refine Valuation.map_sub_le _ hmi ((hz i).trans ?_)
        rw [exp_le_exp]; omega
      have e : (locVec v (t • z) - m) i = (algebraMap (𝓞 F) (v.adicCompletion F) t - 1) *
          algebraMap F (v.adicCompletion F) (z i) - (m i - algebraMap F (v.adicCompletion F) (z i)) := by
        rw [Pi.sub_apply, locVec_smul_int_apply]; ring
      rw [e]
      refine Valuation.map_sub_le _ ?_ (hz i)
      rw [map_mul]
      calc Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) t - 1) *
            Valued.v (algebraMap F (v.adicCompletion F) (z i))
          ≤ exp (-((K + kv : ℕ) : ℤ)) * exp (kv : ℤ) := mul_le_mul' (valued_sub_one_le v ht1) hzi
        _ = exp (-(K : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    have hy : t • z ∈ M.glue := by
      intro w
      by_cases hw : w = v
      · subst hw
        have : locVec w (t • z) = m + (locVec w (t • z) - m) := by abel
        rw [this]
        exact (M.M w).add_mem hm (hball hdiff).2
      · exact ht w hw
    have : m = locVec v (t • z) - (locVec v (t • z) - m) := by abel
    rw [this]
    exact Submodule.sub_mem _ (locVec_mem_loc v hy) (hball hdiff).1

/-- **The local–global correspondence for lattices over $\mathcal O_F$:** a family $(M_\mathfrak p)$ of local lattices,
almost all standard, is the family of localizations of exactly one global lattice. -/
@[kb "omeara1963" "§81E, 81:14, p. 218 (existence); p. 218 (L = K ⇔ L_𝔭 = K_𝔭 ∀𝔭); cassels1978 Ch. 11, Thm. 1.1, p. 198"]
theorem existsUnique_loc_eq (M : LocFamily F n) :
    ∃! L : Submodule (𝓞 F) (Fin n → F), L.IsLattice F ∧ ∀ v, loc v L = M.M v :=
  ⟨M.glue, ⟨M.glue_isLattice, M.loc_glue⟩, fun _ ⟨hL, hloc⟩ =>
    loc_injective hL M.glue_isLattice fun v => (hloc v).trans (M.loc_glue v).symm⟩

end LocFamily

/-- **The family of localizations** $(L_\mathfrak p)_\mathfrak p$ of a global lattice. -/
def locFamily {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) : LocFamily F n where
  M v := loc v L
  isLattice v := loc_isLattice v hL
  eventually_std := loc_eventually_std hL

/-- **Gluing the localizations of $L$ returns $L$.** -/
theorem glue_locFamily {L : Submodule (𝓞 F) (Fin n → F)} (hL : L.IsLattice F) :
    (locFamily hL).glue = L :=
  loc_injective (locFamily hL).glue_isLattice hL (locFamily hL).loc_glue

end QuadFormsKB.Lattices
