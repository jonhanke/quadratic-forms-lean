/-
# O'Meara §33F: $S$-units and the Dirichlet Unit Theorem (33:8, 33:9, 33:10)

**Setting.** $F$ is a number field. O'Meara's $S$ is a set of discrete spots with $\Omega - S$ finite; here $S$ is a set
of finite spots (`Set (HeightOneSpectrum (𝓞 F))`) with $S^c$ finite, and $\Omega - S$ is `outsideS S` (the finite
spots outside $S$ together with all infinite spots, `Sec65A.lean`), with $s$ elements. The group of $S$-units
$\mathfrak u(S) = \{a \in F^\times : |a|_{\mathfrak p} = 1 \text{ for all } \mathfrak p \in S\}$ is Mathlib's
`Set.unit (Sᶜ) F` (Mathlib indexes $S$-units by the exceptional set $S^c$). The group of absolute units is
`absoluteUnits F` (`Sec33A.lean`). At a spot $\mathfrak p$ of $\Omega - S$ only the comparison of $|a|_{\mathfrak p}$
with $1$ matters, so `placeAbs` uses the norm of the completion (normalized at finite spots, ordinary at infinite
ones).

**Proves** `exists_sUnit_one_lt` (**33:8**), `sUnits_independent_finiteIndex` (**33:9**), `sUnit_theorem`
(**33:10**, the Dirichlet Unit Theorem for $S$-units).
-/
import QuadFormsKB.Citation
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Algebra.Module.ZLattice.Basic
import QuadFormsKB.Literature.OMeara.Sec33A
import QuadFormsKB.Literature.OMeara.Sec65A

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

/-- The absolute value of $a \in F$ at a place of $F$: the norm of $a$ in the completion (`v.adicCompletion F` at a
finite spot, `w.Completion` at an infinite one). -/
def placeAbs : NFPlace F → F → ℝ
  | .infinite w, a => ‖(a : w.Completion)‖
  | .finite v, a => ‖(a : v.adicCompletion F)‖

/-!
### Auxiliary development for 33:8 to 33:10

The proof goes through the logarithmic map $\ell : \mathfrak u(S) \to \mathbb R^{\Omega - S}$,
$\ell(x)_{\mathfrak p} = n_{\mathfrak p} \log |x|_{\mathfrak p}$ ($n_{\mathfrak p}$ the local degree), whose image lies in the
hyperplane $H = \{\sum_{\mathfrak p} x_{\mathfrak p} = 0\}$ (product formula). Its image $L$ is a discrete
(finitely many $S$-units with bounded $\ell$) subgroup of $H$ spanning $H$ (Mathlib's Dirichlet unit theorem for
$\mathcal O_F^\times$ plus, for each $\mathfrak p \in S^c$, a generator of a power of $\mathfrak p$, which exists
since the class group is finite), so $L$ is a $\mathbb Z$-lattice of rank $s - 1$ in $H$. The kernel of $\ell$ is the
group of absolute units.
-/
namespace SUnitAux

theorem placeAbs_infinite (w : InfinitePlace F) (a : F) : placeAbs (.infinite w) a = w a := by
  simp only [placeAbs]
  exact InfinitePlace.Completion.norm_coe (v := w) (WithAbs.equiv w.1 |>.symm a)

theorem placeAbs_finite (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    placeAbs (.finite v) a = FinitePlace.mk v a := by
  simp only [placeAbs]; rfl

/-- The absolute value at a place, as a Mathlib `AbsoluteValue`. -/
def abv : NFPlace F → AbsoluteValue F ℝ
  | .infinite w => w.1
  | .finite v => (FinitePlace.mk v).1

theorem placeAbs_eq_abv (p : NFPlace F) (a : F) : placeAbs p a = abv p a := by
  cases p with
  | infinite w => exact placeAbs_infinite w a
  | finite v => exact placeAbs_finite v a

theorem placeAbs_mul (p : NFPlace F) (a b : F) : placeAbs p (a * b) = placeAbs p a * placeAbs p b := by
  simp [placeAbs_eq_abv]

theorem placeAbs_pos (p : NFPlace F) {a : F} (ha : a ≠ 0) : 0 < placeAbs p a := by
  rw [placeAbs_eq_abv]; exact (abv p).pos ha

/-- The local degree $n_{\mathfrak p}$: $2$ at complex places, $1$ otherwise. -/
def wt : NFPlace F → ℝ
  | .infinite w => (w.mult : ℝ)
  | .finite _ => 1

theorem wt_pos (p : NFPlace F) : 0 < wt p := by
  cases p with
  | infinite w => show (0:ℝ) < (w.mult : ℝ); exact_mod_cast w.mult_pos
  | finite v => exact one_pos

/-- $n_{\mathfrak p} \log |x|_{\mathfrak p}$. -/
def ellFun (p : NFPlace F) (x : Fˣ) : ℝ := wt p * Real.log (placeAbs p (x : F))

theorem ellFun_mul (p : NFPlace F) (x y : Fˣ) : ellFun p (x * y) = ellFun p x + ellFun p y := by
  unfold ellFun
  rw [Units.val_mul, placeAbs_mul, Real.log_mul (placeAbs_pos p x.ne_zero).ne' (placeAbs_pos p y.ne_zero).ne',
    mul_add]

theorem ellFun_one (p : NFPlace F) : ellFun p 1 = 0 := by simp [ellFun, placeAbs_eq_abv]

open scoped Classical nonZeroDivisors

variable {S : Set (HeightOneSpectrum (𝓞 F))}

/-- $\Omega - S$ as a `Finset`. -/
def Pfin (hS : Sᶜ.Finite) : Finset (NFPlace F) := (outsideS_finite hS).toFinset

theorem mem_Pfin (hS : Sᶜ.Finite) {p : NFPlace F} : p ∈ Pfin hS ↔ p ∈ outsideS S :=
  Set.Finite.mem_toFinset _

theorem Pfin_eq (hS : Sᶜ.Finite) : Pfin hS =
    (hS.toFinset.map ⟨NFPlace.finite, fun _ _ h => NFPlace.finite.inj h⟩) ∪
      (Finset.univ : Finset (InfinitePlace F)).map ⟨NFPlace.infinite, fun _ _ h => NFPlace.infinite.inj h⟩ := by
  apply Finset.coe_injective
  rw [← outsideS_eq_coe hS]
  ext p; simp [Pfin]

theorem norm_eq_one_of_mem {x : Sᶜ.unit F} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ Sᶜ) :
    ‖FinitePlace.embedding v ((x : Fˣ) : F)‖ = 1 := by
  rw [FinitePlace.norm_embedding', x.2 v hv]; simp

/-- Product formula for $S$-units: $\sum_{\mathfrak p \in \Omega - S} n_{\mathfrak p} \log |x|_{\mathfrak p} = 0$. -/
theorem sum_ellFun (hS : Sᶜ.Finite) (x : Sᶜ.unit F) : ∑ p ∈ Pfin hS, ellFun p (x : Fˣ) = 0 := by
  have hx0 : ((x : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hfp : ∏ᶠ w : FinitePlace F, w ((x : Fˣ) : F) =
      ∏ v ∈ hS.toFinset, ‖FinitePlace.embedding v ((x : Fˣ) : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    exact hv (norm_eq_one_of_mem (by simpa using hvS))
  have hpf := prod_abs_eq_one hx0
  rw [hfp] at hpf
  have hAne : ∀ v ∈ hS.toFinset, ‖FinitePlace.embedding v ((x : Fˣ) : F)‖ ≠ 0 :=
    fun v _ => (norm_pos_iff.2 ((map_ne_zero (FinitePlace.embedding v)).2 hx0)).ne'
  have hBne : ∀ w ∈ (Finset.univ : Finset (InfinitePlace F)), w ((x : Fˣ) : F) ^ w.mult ≠ 0 :=
    fun w _ => (pow_pos (InfinitePlace.pos_iff.2 hx0) _).ne'
  have hA : ∑ v ∈ hS.toFinset, ellFun (NFPlace.finite v) (x : Fˣ) =
      Real.log (∏ v ∈ hS.toFinset, ‖FinitePlace.embedding v ((x : Fˣ) : F)‖) := by
    rw [Real.log_prod hAne]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [ellFun, wt, placeAbs_finite, FinitePlace.mk_apply]
  have hB : ∑ w : InfinitePlace F, ellFun (NFPlace.infinite w) (x : Fˣ) =
      Real.log (∏ w : InfinitePlace F, w ((x : Fˣ) : F) ^ w.mult) := by
    rw [Real.log_prod hBne]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [ellFun, wt, placeAbs_infinite, Real.log_pow]
  have hsum : Real.log (∏ v ∈ hS.toFinset, ‖FinitePlace.embedding v ((x : Fˣ) : F)‖) +
      Real.log (∏ w : InfinitePlace F, w ((x : Fˣ) : F) ^ w.mult) = 0 := by
    rw [← Real.log_mul (Finset.prod_ne_zero_iff.2 hAne) (Finset.prod_ne_zero_iff.2 hBne), mul_comm, hpf,
      Real.log_one]
  rw [← hA, ← hB] at hsum
  rw [Pfin_eq, Finset.sum_union (Finset.disjoint_left.2 (by simp)), Finset.sum_map, Finset.sum_map]
  exact hsum

theorem placeAbs_finite_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    placeAbs (.finite v) a = 1 ↔ v.valuation F a = 1 := by
  rw [placeAbs_finite, FinitePlace.mk_apply, FinitePlace.norm_embedding']
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ h1.ne'

theorem placeAbs_finite_lt_one_iff (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    placeAbs (.finite v) a < 1 ↔ v.valuation F a < 1 := by
  rw [placeAbs_finite, FinitePlace.mk_apply, FinitePlace.norm_embedding']
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [← NNReal.coe_one, NNReal.coe_lt_coe]
  exact WithZeroMulInt.toNNReal_lt_one_iff h1

/-- The index type $\Omega - S$ of the coordinates. -/
abbrev Pl (hS : Sᶜ.Finite) := {p // p ∈ Pfin (F := F) hS}

/-- The logarithmic map $\ell : \mathfrak u(S) \to \mathbb R^{\Omega - S}$ (as an additive homomorphism). -/
def ell (hS : Sᶜ.Finite) : Additive (Sᶜ.unit F) →+ (Pl hS → ℝ) where
  toFun x p := ellFun p.1 ((x.toMul : Sᶜ.unit F) : Fˣ)
  map_zero' := by ext p; exact ellFun_one p.1
  map_add' x y := by ext p; exact ellFun_mul p.1 _ _

theorem ell_apply (hS : Sᶜ.Finite) (x : Sᶜ.unit F) (p : Pl hS) :
    ell hS (Additive.ofMul x) p = ellFun p.1 (x : Fˣ) := rfl

theorem ellFun_eq_zero_iff (p : NFPlace F) (x : Fˣ) : ellFun p x = 0 ↔ placeAbs p (x : F) = 1 := by
  unfold ellFun
  rw [mul_eq_zero, or_iff_right (wt_pos p).ne']
  constructor
  · intro h
    exact Real.eq_one_of_pos_of_log_eq_zero (placeAbs_pos p x.ne_zero) h
  · intro h; rw [h, Real.log_one]

/-- The kernel of $\ell$ on $\mathfrak u(S)$ is the group of absolute units. -/
theorem ell_eq_zero_iff (hS : Sᶜ.Finite) (x : Sᶜ.unit F) :
    ell hS (Additive.ofMul x) = 0 ↔ (x : Fˣ) ∈ absoluteUnits F := by
  constructor
  · intro h
    have key : ∀ p : NFPlace F, p ∈ outsideS S → placeAbs p ((x : Fˣ) : F) = 1 := by
      intro p hp
      have := congrFun h ⟨p, (mem_Pfin hS).2 hp⟩
      exact (ellFun_eq_zero_iff p _).1 this
    refine ⟨fun v => ?_, fun w => ?_⟩
    · by_cases hv : v ∈ Sᶜ
      · exact (placeAbs_finite_eq_one_iff v _).1 (key (.finite v) hv)
      · exact x.2 v hv
    · rw [← placeAbs_infinite]; exact key (.infinite w) trivial
  · intro h
    ext ⟨p, hp⟩
    rw [ell_apply, Pi.zero_apply, ellFun_eq_zero_iff]
    cases p with
    | infinite w => rw [placeAbs_infinite]; exact h.2 w
    | finite v => exact (placeAbs_finite_eq_one_iff v _).2 (h.1 v)

theorem absoluteUnits_le_unit : absoluteUnits F ≤ Sᶜ.unit F := fun _ hx => fun v _ => hx.1 v

theorem valuation_le_of_placeAbs_le (v : HeightOneSpectrum (𝓞 F)) (a : F) (m : ℕ)
    (h : placeAbs (.finite v) a ≤ 2 ^ m) : v.valuation F a ≤ WithZero.exp (m : ℤ) := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hmono := WithZeroMulInt.toNNReal_strictMono h1
  have h2 := hmono hlt
  have e1 : WithZeroMulInt.toNNReal h1.ne_zero (WithZero.exp (m : ℤ)) =
      (Ideal.absNorm v.asIdeal : NNReal) ^ m := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp), WithZero.log_exp]; simp
  rw [e1] at h2
  have h3 : ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^ m < placeAbs (.finite v) a := by
    rw [placeAbs_finite, FinitePlace.mk_apply, FinitePlace.norm_embedding']
    exact_mod_cast h2
  have h4 : (2 : ℝ) ^ m ≤ ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^ m := by
    gcongr
    exact_mod_cast HeightOneSpectrum.two_le_absNorm_nnreal v
  linarith

theorem exists_mem_prod_pow (T : Finset (HeightOneSpectrum (𝓞 F))) (m : ℕ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v ∈ T, v.intValuation c ≤ WithZero.exp (-(m : ℤ)) := by
  have hne : (∏ v ∈ T, v.asIdeal ^ m) ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    simp only [not_exists, not_and]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨c, hc0, fun v hv => ?_⟩
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) hc

/-- For $\mathfrak p \in S^c$ there is an $S$-unit $g$ (a generator of a power of $\mathfrak p$, which is principal
since the class group is finite) with $|g|_{\mathfrak p} < 1$ and $|g|_{\mathfrak q} = 1$ at all other finite spots
$\mathfrak q$. -/
theorem exists_elem (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ Sᶜ) :
    ∃ x : Sᶜ.unit F, ellFun (.finite v) (x : Fˣ) < 0 ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F ((x : Fˣ) : F) = 1 := by
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hn0 : 0 < n := Fintype.card_pos
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have hpow : (v.asIdeal ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hv0 n)]
    have := pow_card_eq_one (G := ClassGroup (𝓞 F)) (x := ClassGroup.mk0 ⟨v.asIdeal, hv0⟩)
    rw [← map_pow] at this
    exact this
  obtain ⟨g, hg⟩ := hpow.principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    have : v.asIdeal ^ n = ⊥ := by rw [hg]; simp
    exact pow_ne_zero n v.ne_bot this
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F), g ∈ w.asIdeal ↔ w = v := by
    intro w
    constructor
    · intro h
      have h1 : v.asIdeal ^ n ≤ w.asIdeal := by
        rw [hg, Ideal.span_singleton_le_iff_mem]; exact h
      have h2 : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le h1
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm
    · rintro rfl
      have : g ∈ w.asIdeal ^ n := by
        rw [hg]; exact Ideal.mem_span_singleton_self g
      exact (Ideal.pow_le_self hn0.ne') this
  have hgF : algebraMap (𝓞 F) F g ≠ 0 := by
    simpa using hg0
  refine ⟨⟨Units.mk0 _ hgF, fun w hw => ?_⟩, ?_, ?_⟩
  · have : w ≠ v := fun h => hw (h ▸ hv)
    show w.valuation F (algebraMap (𝓞 F) F g) = 1
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => this ((hmem w).1 h)
  · unfold ellFun
    rw [wt, one_mul]
    apply Real.log_neg (placeAbs_pos _ hgF)
    rw [placeAbs_finite_lt_one_iff]
    show v.valuation F (algebraMap (𝓞 F) F g) < 1
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact (hmem v).2 rfl
  · intro w hw
    show w.valuation F (algebraMap (𝓞 F) F g) = 1
    rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => hw ((hmem w).1 h)

/-- Only finitely many $S$-units have all $|\ell(x)_{\mathfrak p}| \le B$ (discreteness of $\ell(\mathfrak u(S))$). -/
theorem finite_ell_bounded (hS : Sᶜ.Finite) (B : ℝ) :
    {x : Sᶜ.unit F | ∀ p : Pl hS, |ell hS (Additive.ofMul x) p| ≤ B}.Finite := by
  obtain ⟨c, hc0, hc⟩ := exists_mem_prod_pow hS.toFinset ⌈B / Real.log 2⌉₊
  set m := ⌈B / Real.log 2⌉₊ with hm
  set A : ℝ := Real.exp B * ∑ φ : F →+* ℂ, ‖φ (c : F)‖ with hA
  have hfin := Embeddings.finite_of_norm_le F ℂ A
  have hc0' : (c : F) ≠ 0 := by simpa using hc0
  let f : Sᶜ.unit F → F := fun x => ((x : Fˣ) : F) * (c : F)
  have hinj : Function.Injective f := fun x y h => by
    apply Subtype.ext; apply Units.ext; exact mul_right_cancel₀ hc0' h
  refine Set.Finite.of_finite_image (f := f) (hfin.subset ?_) hinj.injOn
  rintro _ ⟨x, hx, rfl⟩
  have hx0 : ((x : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hbd : ∀ p : NFPlace F, p ∈ outsideS S → |ellFun p (x : Fˣ)| ≤ B := fun p hp =>
    hx ⟨p, (mem_Pfin hS).2 hp⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp B ≤ 2 ^ m := by
    have h1 : B ≤ m * Real.log 2 := by
      have := Nat.le_ceil (B / Real.log 2)
      rw [div_le_iff₀ hlog2] at this
      exact this
    calc Real.exp B ≤ Real.exp (m * Real.log 2) := Real.exp_le_exp.2 h1
      _ = 2 ^ m := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hplace : ∀ p : NFPlace F, p ∈ outsideS S → placeAbs p ((x : Fˣ) : F) ≤ Real.exp B := by
    intro p hp
    have h1 := hbd p hp
    have hw := wt_pos p
    have hw1 : 1 ≤ wt p := by
      cases p with
      | infinite w => show (1:ℝ) ≤ (w.mult : ℝ); exact_mod_cast InfinitePlace.mult_pos
      | finite v => exact le_refl _
    have hpos := placeAbs_pos p hx0
    have h2 : Real.log (placeAbs p ((x : Fˣ) : F)) ≤ B := by
      unfold ellFun at h1
      rw [abs_mul, abs_of_pos hw] at h1
      calc _ ≤ |Real.log (placeAbs p ((x : Fˣ) : F))| := le_abs_self _
        _ ≤ wt p * |Real.log (placeAbs p ((x : Fˣ) : F))| := le_mul_of_one_le_left (abs_nonneg _) hw1
        _ ≤ B := h1
    exact (Real.log_le_iff_le_exp hpos).1 h2
  refine ⟨?_, fun φ => ?_⟩
  · have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (f x) ≤ 1 := by
      intro v
      show v.valuation F (((x : Fˣ) : F) * (c : F)) ≤ 1
      rw [Valuation.map_mul]
      by_cases hvS : v ∈ Sᶜ
      · have h1 : v.valuation F ((x : Fˣ) : F) ≤ WithZero.exp (m : ℤ) :=
          valuation_le_of_placeAbs_le v _ m ((hplace (.finite v) hvS).trans hexp)
        have h2 : v.valuation F (c : F) ≤ WithZero.exp (-(m : ℤ)) := by
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact hc v (by simpa using hvS)
        calc _ ≤ WithZero.exp (m : ℤ) * WithZero.exp (-(m : ℤ)) := mul_le_mul' h1 h2
          _ = 1 := by rw [← WithZero.exp_add]; simp
      · rw [x.2 v hvS, one_mul]; exact HeightOneSpectrum.valuation_le_one v c
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (f x) hv
    rw [← hy]
    exact RingOfIntegers.isIntegral_coe y
  · have hw : (InfinitePlace.mk φ) ((x : Fˣ) : F) ≤ Real.exp B := by
      have := hplace (.infinite (InfinitePlace.mk φ)) trivial
      rwa [placeAbs_infinite] at this
    show ‖φ (((x : Fˣ) : F) * (c : F))‖ ≤ A
    rw [map_mul, norm_mul]
    have h1 : ‖φ ((x : Fˣ) : F)‖ ≤ Real.exp B := hw
    have h2 : ‖φ (c : F)‖ ≤ ∑ φ : F →+* ℂ, ‖φ (c : F)‖ :=
      Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ (c : F)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le

/-- The sum-of-coordinates functional on $\mathbb R^{\Omega - S}$. -/
def sumLin (hS : Sᶜ.Finite) : (Pl (F := F) hS → ℝ) →ₗ[ℝ] ℝ := ∑ p : Pl (F := F) hS, LinearMap.proj p

/-- The hyperplane $\sum_p x_p = 0$. -/
def Hs (hS : Sᶜ.Finite) : Submodule ℝ (Pl (F := F) hS → ℝ) := LinearMap.ker (sumLin hS)

theorem mem_Hs {hS : Sᶜ.Finite} {f : Pl (F := F) hS → ℝ} : f ∈ Hs hS ↔ ∑ p, f p = 0 := by
  simp [Hs, sumLin, LinearMap.mem_ker]

theorem ell_mem_Hs (hS : Sᶜ.Finite) (x : Additive (Sᶜ.unit F)) : ell hS x ∈ Hs hS := by
  rw [mem_Hs]
  exact (Finset.sum_coe_sort (Pfin hS) (fun p => ellFun p (x.toMul : Fˣ))).trans (sum_ellFun hS x.toMul)

/-- $\ell$ with codomain the hyperplane $H$. -/
def ellH (hS : Sᶜ.Finite) : Additive (Sᶜ.unit F) →+ Hs (F := F) hS :=
  (ell hS).codRestrict (Hs hS).toAddSubgroup (fun x => ell_mem_Hs hS x)

/-- The lattice $\ell(\mathfrak u(S)) \subseteq H$. -/
def Lat (hS : Sᶜ.Finite) : Submodule ℤ (Hs (F := F) hS) := LinearMap.range (ellH hS).toIntLinearMap

theorem mem_Lat {hS : Sᶜ.Finite} {l : Hs (F := F) hS} : l ∈ Lat hS ↔ ∃ x, ellH hS x = l := by
  exact LinearMap.mem_range

theorem coe_ellH (hS : Sᶜ.Finite) (x : Additive (Sᶜ.unit F)) :
    ((ellH hS x : Hs hS) : Pl hS → ℝ) = ell hS x := rfl

instance discrete_Lat (hS : Sᶜ.Finite) : DiscreteTopology (Lat (F := F) hS) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1)
    (Metric.closedBall_mem_nhds _ one_pos) ?_
  have hfin := finite_ell_bounded hS 1
  refine (hfin.image (fun x : Sᶜ.unit F => (⟨ellH hS (Additive.ofMul x), mem_Lat.2 ⟨_, rfl⟩⟩ : Lat hS))).subset ?_
  intro l hl
  obtain ⟨x, hx⟩ := mem_Lat.1 l.2
  refine ⟨x.toMul, fun p => ?_, ?_⟩
  · have h1 : ‖((l : Hs hS) : Pl hS → ℝ)‖ ≤ 1 := by
      have := mem_closedBall_zero_iff.1 hl
      simpa using this
    have h2 := norm_le_pi_norm ((l : Hs hS) : Pl hS → ℝ) p
    rw [Real.norm_eq_abs] at h2
    have h3 := h2.trans h1
    rw [← hx] at h3
    simpa [coe_ellH] using h3
  · apply Subtype.ext
    simpa using hx

/-- The coordinate of $\Omega - S$ at an infinite spot. -/
def infP (hS : Sᶜ.Finite) (w : InfinitePlace F) : Pl (F := F) hS :=
  ⟨.infinite w, (mem_Pfin hS).2 trivial⟩

/-- The coordinate of $\Omega - S$ at a finite spot of $S^c$. -/
def finP (hS : Sᶜ.Finite) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ Sᶜ) : Pl (F := F) hS :=
  ⟨.finite v, (mem_Pfin hS).2 hv⟩

theorem Pl_cases (hS : Sᶜ.Finite) (p : Pl (F := F) hS) :
    (∃ w, p = infP hS w) ∨ ∃ v, ∃ hv : v ∈ Sᶜ, p = finP hS v hv := by
  obtain ⟨q, hq⟩ := p
  cases q with
  | infinite w => exact Or.inl ⟨w, rfl⟩
  | finite v => exact Or.inr ⟨v, (mem_Pfin hS).1 hq, rfl⟩

theorem unit_val_eq_one (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    v.valuation F (algebraMap (𝓞 F) F (u : 𝓞 F)) = 1 := by
  have h1 := HeightOneSpectrum.valuation_le_one (K := F) v (u : 𝓞 F)
  have h2 := HeightOneSpectrum.valuation_le_one (K := F) v ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  refine valuation_eq_one_of_mul_eq_one h1 h2 ?_
  rw [← Valuation.map_mul, ← map_mul]
  simp

/-- A unit of $\mathcal O_F$ viewed as an $S$-unit. -/
def unitU (u : (𝓞 F)ˣ) : Sᶜ.unit F :=
  ⟨Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u, fun v _ => unit_val_eq_one u v⟩

theorem coe_unitU (u : (𝓞 F)ˣ) : ((unitU (S := S) u : Fˣ) : F) = ((u : 𝓞 F) : F) := rfl

theorem ellFun_unitU_finite (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ellFun (.finite v) (unitU (S := S) u : Fˣ) = 0 := by
  rw [ellFun_eq_zero_iff, placeAbs_finite_eq_one_iff]
  exact unit_val_eq_one u v

/-- Restriction to the infinite places other than the distinguished one. -/
def Rres (hS : Sᶜ.Finite) : (Pl (F := F) hS → ℝ) →ₗ[ℝ] Units.dirichletUnitTheorem.logSpace F :=
  LinearMap.pi (fun w => LinearMap.proj (infP hS w.1))

theorem Rres_ell_unitU (hS : Sᶜ.Finite) (u : (𝓞 F)ˣ) :
    Rres hS (ell hS (Additive.ofMul (unitU (S := S) u))) = Units.logEmbedding F (Additive.ofMul u) := by
  ext w
  simp only [Rres, LinearMap.pi_apply, LinearMap.proj_apply, ell_apply,
    Units.dirichletUnitTheorem.logEmbedding_component]
  simp [infP, ellFun, wt, placeAbs_infinite, coe_unitU]

/-- $\ell(\mathfrak u(S))$ spans the hyperplane $H$ over $\mathbb R$. -/
theorem Hs_le_span (hS : Sᶜ.Finite) : Hs hS ≤ Submodule.span ℝ (Set.range (ell hS)) := by
  intro f hf
  set W := Submodule.span ℝ (Set.range (ell hS)) with hW
  have hell : ∀ x : Additive (Sᶜ.unit F), ell hS x ∈ W := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Sᶜ.unit F, v ∈ Sᶜ →
      (ellFun (.finite v) (x : Fˣ) < 0 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F ((x : Fˣ) : F) = 1) := by
    intro v
    by_cases hv : v ∈ Sᶜ
    · obtain ⟨x, hx⟩ := exists_elem v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose g hg using hex
  let a : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    if hv : v ∈ Sᶜ then f (finP hS v hv) / ellFun (.finite v) (g v : Fˣ) else 0
  let T := ∑ v ∈ hS.toFinset, a v • ell hS (Additive.ofMul (g v))
  have hTW : T ∈ W := Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (hell _)
  let f' : Pl (F := F) hS → ℝ := f - T
  have hf'H : f' ∈ Hs hS :=
    Submodule.sub_mem _ hf (Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (ell_mem_Hs hS _))
  have hf'fin : ∀ w (hw : w ∈ Sᶜ), f' (finP hS w hw) = 0 := by
    intro w hw
    have h1 : T (finP hS w hw) = a w * ellFun (.finite w) (g w : Fˣ) := by
      simp only [T, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single w]
      · rfl
      · intro v hv hvw
        have h2 : ellFun (.finite w) (g v : Fˣ) = 0 := by
          rw [ellFun_eq_zero_iff, placeAbs_finite_eq_one_iff]
          exact (hg v (by simpa using hv)).2 w (Ne.symm hvw)
        show a v * ellFun (.finite w) (g v : Fˣ) = 0
        rw [h2, mul_zero]
      · intro h; exact absurd (by simpa using hw) h
    have hne : ellFun (.finite w) (g w : Fˣ) ≠ 0 := (hg w hw).1.ne
    show f (finP hS w hw) - T (finP hS w hw) = 0
    rw [h1]
    simp only [a, hw, ↓reduceDIte]
    rw [div_mul_cancel₀ _ hne, sub_self]
  -- units
  let Wu := Submodule.span ℝ (Set.range fun u : (𝓞 F)ˣ => ell hS (Additive.ofMul (unitU (S := S) u)))
  have hWuW : Wu ≤ W := Submodule.span_mono (by rintro _ ⟨u, rfl⟩; exact ⟨_, rfl⟩)
  have hWuH : Wu ≤ Hs hS := Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact ell_mem_Hs hS _)
  have hWuZ : ∀ y ∈ Wu, ∀ v (hv : v ∈ Sᶜ), y (finP hS v hv) = 0 := by
    intro y hy v hv
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, rfl⟩ := hz
      exact ellFun_unitU_finite u v
    | zero => rfl
    | add y1 y2 _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h => simp [h]
  have hspan : Submodule.span ℝ (Units.unitLattice F : Set (Units.dirichletUnitTheorem.logSpace F)) ≤
      Wu.map (Rres hS) := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, -, rfl⟩ := hz
    refine ⟨ell hS (Additive.ofMul (unitU (S := S) x.toMul)), Submodule.subset_span ⟨x.toMul, rfl⟩, ?_⟩
    rw [Rres_ell_unitU]
    rfl
  have hR : Rres hS f' ∈ Wu.map (Rres hS) := by
    apply hspan
    rw [Units.dirichletUnitTheorem.unitLattice_span_eq_top]; trivial
  obtain ⟨y, hyW, hy⟩ := hR
  have hh : f' - y = 0 := by
    have hhH : f' - y ∈ Hs hS := Submodule.sub_mem _ hf'H (hWuH hyW)
    have hz : ∀ p, p ≠ infP hS Units.dirichletUnitTheorem.w₀ → (f' - y) p = 0 := by
      intro p hp
      rcases Pl_cases hS p with ⟨w, rfl⟩ | ⟨v, hv, rfl⟩
      · have hw : w ≠ Units.dirichletUnitTheorem.w₀ := fun h => hp (by rw [h])
        have := congrFun hy ⟨w, hw⟩
        simp only [Rres, LinearMap.pi_apply, LinearMap.proj_apply] at this
        simp [this]
      · simp [hf'fin v hv, hWuZ y hyW v hv]
    rw [mem_Hs, Finset.sum_eq_single (infP hS Units.dirichletUnitTheorem.w₀) (fun p _ hp => hz p hp)
      (fun h => absurd (Finset.mem_univ _) h)] at hhH
    funext p
    by_cases hp : p = infP hS Units.dirichletUnitTheorem.w₀
    · rw [hp]; exact hhH
    · exact hz p hp
  have : f' = y := sub_eq_zero.1 hh
  have hfW : f = f' + T := by simp [f']
  rw [hfW, this]
  exact W.add_mem (hWuW hyW) hTW

theorem span_Lat (hS : Sᶜ.Finite) : Submodule.span ℝ (Lat (F := F) hS : Set (Hs hS)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hz : (z : Pl hS → ℝ) ∈ Submodule.span ℝ (Set.range (ell hS)) := Hs_le_span hS z.2
  have h1 : Submodule.span ℝ (Set.range (ell hS)) ≤
      (Submodule.span ℝ (Lat (F := F) hS : Set (Hs hS))).map (Hs hS).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨ellH hS x, Submodule.subset_span (mem_Lat.2 ⟨x, rfl⟩), rfl⟩
  obtain ⟨y, hy, hyz⟩ := h1 hz
  have : y = z := Subtype.ext hyz
  rwa [this] at hy

instance isZLattice_Lat (hS : Sᶜ.Finite) : IsZLattice ℝ (Lat (F := F) hS) := ⟨span_Lat hS⟩

theorem card_Pl (hS : Sᶜ.Finite) : Fintype.card (Pl (F := F) hS) = (outsideS S).ncard := by
  rw [Fintype.card_coe, Set.ncard_eq_toFinset_card _ (outsideS_finite hS)]
  rfl

theorem finrank_Hs (hS : Sᶜ.Finite) : Module.finrank ℝ (Hs (F := F) hS) = (outsideS S).ncard - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumLin hS)
  have hr : LinearMap.range (sumLin hS) = ⊤ := by
    rw [eq_top_iff]
    intro r _
    refine ⟨Pi.single (infP hS (Classical.arbitrary (InfinitePlace F))) r, ?_⟩
    simp [sumLin]
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card, card_Pl] at h
  have : Hs hS = LinearMap.ker (sumLin hS) := rfl
  rw [this]
  omega

theorem finrank_Lat (hS : Sᶜ.Finite) :
    Module.finrank ℤ (Lat (F := F) hS) = (outsideS S).ncard - 1 := by
  rw [ZLattice.rank ℝ, finrank_Hs]

/-- A `ℤ`-basis of the lattice lifted to $S$-units: every $S$-unit has unique coordinates. -/
theorem exists_eta (hS : Sᶜ.Finite) :
    ∃ η : Fin ((outsideS S).ncard - 1) → Sᶜ.unit F, ∀ y : Sᶜ.unit F,
      ∃! k : Fin ((outsideS S).ncard - 1) → ℤ,
        ellH hS (Additive.ofMul y) = ∑ i, k i • ellH hS (Additive.ofMul (η i)) := by
  let b := Module.finBasisOfFinrankEq ℤ (Lat (F := F) hS) (finrank_Lat hS)
  choose η hη using fun i => mem_Lat.1 (b i).2
  have hcoe : ∀ k : Fin ((outsideS S).ncard - 1) → ℤ, (((∑ i, k i • b i : Lat (F := F) hS)) : Hs hS) =
      ∑ i, k i • ellH hS (η i) := by
    intro k
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, hη i]
  refine ⟨fun i => (η i).toMul, fun y => ?_⟩
  have hy : ellH hS (Additive.ofMul y) ∈ Lat hS := mem_Lat.2 ⟨_, rfl⟩
  have key : ∀ k : Fin ((outsideS S).ncard - 1) → ℤ,
      ellH hS (Additive.ofMul y) = ∑ i, k i • ellH hS (Additive.ofMul (η i).toMul) ↔
        (⟨_, hy⟩ : Lat hS) = ∑ i, k i • b i := by
    intro k
    simp only [ofMul_toMul]
    rw [← hcoe k]
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  refine ⟨fun i => b.repr ⟨_, hy⟩ i, (key _).2 ?_, fun k hk => ?_⟩
  · exact (b.sum_repr ⟨_, hy⟩).symm
  · have := (key k).1 hk
    funext i
    rw [this, b.repr_sum_self]

/-- Cocompactness of the lattice: for each coordinate $\mathfrak q$ there is an $S$-unit with
$\ell_{\mathfrak q} > 0$ and $\ell_{\mathfrak p} < 0$ for $\mathfrak p \ne \mathfrak q$. -/
theorem exists_ell_sign (hS : Sᶜ.Finite) (hs : 2 ≤ (outsideS S).ncard) (q : Pl (F := F) hS) :
    ∃ x : Sᶜ.unit F, 0 < ell hS (Additive.ofMul x) q ∧ ∀ p, p ≠ q → ell hS (Additive.ofMul x) p < 0 := by
  let b := Module.finBasisOfFinrankEq ℤ (Lat (F := F) hS) (finrank_Lat hS)
  let bR := b.ofZLatticeBasis ℝ (Lat hS)
  set C : ℝ := ∑ i, ‖bR i‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hcard : 2 ≤ Fintype.card (Pl (F := F) hS) := by rw [card_Pl]; exact hs
  set n : ℝ := ((Fintype.card (Pl (F := F) hS) : ℕ) : ℝ) with hn
  let t : Pl (F := F) hS → ℝ := fun p => if p = q then (n - 1) * (C + 1) else -(C + 1)
  have ht : t ∈ Hs hS := by
    rw [mem_Hs]
    have : ∑ p, t p = ∑ p, (-(C+1) + if p = q then n * (C+1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p = q
      · simp [t, hp]; ring
      · simp [t, hp]
    rw [this, Finset.sum_add_distrib]
    simp [hn]
    ring
  let t' : Hs hS := ⟨t, ht⟩
  let l : Hs hS := (ZSpan.floor bR t' : Hs hS)
  have hlL : l ∈ Lat (F := F) hS := by
    have h2 : l ∈ Submodule.span ℤ (Set.range bR) := (ZSpan.floor bR t').2
    have hspan : Submodule.span ℤ (Set.range bR) = Lat hS := b.ofZLatticeBasis_span ℝ
    rwa [hspan] at h2
  have hfr : ‖t' - l‖ ≤ C := ZSpan.norm_fract_le bR t'
  have hcoord : ∀ p, |t p - l.1 p| ≤ C := by
    intro p
    have h1 : ‖(t' - l : Hs hS).1 p‖ ≤ ‖(t' - l : Hs hS).1‖ := norm_le_pi_norm _ p
    have h2 : ‖(t' - l : Hs hS).1‖ ≤ C := hfr
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  obtain ⟨x, hx⟩ := mem_Lat.1 hlL
  have hxl : ∀ p, ell hS x p = l.1 p := fun p => by rw [← hx]; rfl
  have hneg : ∀ p, p ≠ q → l.1 p < 0 := by
    intro p hp
    have := hcoord p
    have h2 : t p = -(C + 1) := by simp [t, hp]
    rw [abs_le] at this
    linarith [this.1]
  refine ⟨x.toMul, ?_, fun p hp => ?_⟩
  · rw [ofMul_toMul, hxl]
    have hsum : ∑ p, l.1 p = 0 := mem_Hs.1 l.2
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ q)] at hsum
    have hne : (Finset.univ.erase q).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ]
      omega
    have := Finset.sum_neg (fun p hp => hneg p (Finset.ne_of_mem_erase hp)) hne
    linarith
  · rw [ofMul_toMul, hxl]; exact hneg p hp

theorem ellFun_pos_iff (p : NFPlace F) (x : Fˣ) : 0 < ellFun p x ↔ 1 < placeAbs p (x : F) := by
  unfold ellFun
  rw [mul_pos_iff_of_pos_left (wt_pos p), Real.log_pos_iff (placeAbs_pos p x.ne_zero).le]

theorem ellFun_neg_iff (p : NFPlace F) (x : Fˣ) : ellFun p x < 0 ↔ placeAbs p (x : F) < 1 := by
  unfold ellFun
  rw [← Real.log_neg_iff (placeAbs_pos p x.ne_zero)]
  exact ⟨fun h => neg_of_mul_neg_right h (wt_pos p).le, fun h => mul_neg_of_pos_of_neg (wt_pos p) h⟩

theorem sumT_pos (hS : Sᶜ.Finite) (T : Finset (NFPlace F)) (hT : (T : Set (NFPlace F)) ⊆ outsideS S)
    (hcard : T.card + 1 = (outsideS S).ncard) (x : Sᶜ.unit F) (q : NFPlace F) (hqT : q ∈ T)
    (hx : ∀ p ∈ outsideS S, p ≠ q → ellFun p (x : Fˣ) < 0) : 0 < ∑ p ∈ T, ellFun p (x : Fˣ) := by
  have hTP : T ⊆ Pfin hS := fun p hp => (mem_Pfin hS).2 (hT hp)
  have hc : T.card < (Pfin hS).card := by
    have : (Pfin hS).card = (outsideS S).ncard := by
      rw [← card_Pl hS]; exact (Fintype.card_coe _).symm
    omega
  obtain ⟨p0, hp0, hp0T⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hsub := Finset.sum_sdiff hTP (f := fun p => ellFun p (x : Fˣ))
  rw [sum_ellFun hS x] at hsub
  have : ∑ p ∈ Pfin hS \ T, ellFun p (x : Fˣ) < 0 :=
    Finset.sum_neg (fun p hp => hx p ((mem_Pfin hS).1 (Finset.mem_sdiff.1 hp).1)
      (fun h => (Finset.mem_sdiff.1 hp).2 (h ▸ hqT))) ⟨p0, Finset.mem_sdiff.2 ⟨hp0, hp0T⟩⟩
  linarith

/-- The logarithmic vectors of the $\varepsilon_{\mathfrak q}$ of 33:9 are linearly independent over $\mathbb R$
(their matrix is strictly diagonally dominant). -/
theorem indep_ell (hS : Sᶜ.Finite) (T : Finset (NFPlace F)) (hT : (T : Set (NFPlace F)) ⊆ outsideS S)
    (hcard : T.card + 1 = (outsideS S).ncard) (ε : NFPlace F → Sᶜ.unit F)
    (hε : ∀ q ∈ T, 1 < placeAbs q ((ε q : Fˣ) : F) ∧
      ∀ p ∈ outsideS S, p ≠ q → placeAbs p ((ε q : Fˣ) : F) < 1) :
    LinearIndependent ℝ (fun q : T => ellH hS (Additive.ofMul (ε q.1))) := by
  have hpos : ∀ q ∈ T, 0 < ellFun q (ε q : Fˣ) := fun q hq => (ellFun_pos_iff _ _).2 (hε q hq).1
  have hneg : ∀ q ∈ T, ∀ p ∈ outsideS S, p ≠ q → ellFun p (ε q : Fˣ) < 0 :=
    fun q hq p hp hpq => (ellFun_neg_iff _ _).2 ((hε q hq).2 p hp hpq)
  let A : Matrix T T ℝ := fun q p => ellFun p.1 (ε q.1 : Fˣ)
  have hdet : A.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro q
    have hqpos := hpos q.1 q.2
    have hsum := sumT_pos hS T hT hcard (ε q.1) q.1 q.2 (hneg q.1 q.2)
    have h1 : ∑ j ∈ Finset.univ.erase q, ‖A q j‖ = ∑ j ∈ Finset.univ.erase q, -A q j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjq : j.1 ≠ q.1 := fun h => (Finset.ne_of_mem_erase hj) (Subtype.ext h)
      rw [Real.norm_eq_abs, abs_of_neg (hneg q.1 q.2 j.1 (hT j.2) hjq)]
    have h2 := Finset.add_sum_erase Finset.univ (fun j => A q j) (Finset.mem_univ q)
    have h3 : ∑ j : T, A q j = ∑ p ∈ T, ellFun p (ε q.1 : Fˣ) :=
      Finset.sum_coe_sort T (fun p => ellFun p (ε q.1 : Fˣ))
    rw [Real.norm_eq_abs (A q q), abs_of_pos hqpos, h1, Finset.sum_neg_distrib]
    have : A q q = ellFun q.1 (ε q.1 : Fˣ) := rfl
    linarith
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : Matrix.vecMul c A = 0 := by
    funext p
    have := congrArg (fun z : Hs hS => (z : Pl hS → ℝ) ⟨p.1, (mem_Pfin hS).2 (hT p.2)⟩) hc
    simpa [Matrix.vecMul, dotProduct, A, Submodule.coe_sum, Finset.sum_apply, coe_ellH, ell_apply] using this
  exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) i

end SUnitAux

open SUnitAux

/-- **33:8.** Let $S$ be a set of discrete spots of $F$ with $\Omega - S$ finite of $s \ge 2$ elements. Then for each
$\mathfrak q \in \Omega - S$ there is an $S$-unit $\varepsilon_{\mathfrak q}$ with $|\varepsilon_{\mathfrak q}|_{\mathfrak q} > 1$
and $|\varepsilon_{\mathfrak q}|_{\mathfrak p} < 1$ for all $\mathfrak p \in \Omega - (S \cup \mathfrak q)$. -/
@[kb "omeara1963" "§33F, 33:8, p. 74"]
theorem exists_sUnit_one_lt {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite)
    (hs : 2 ≤ (outsideS S).ncard) {q : NFPlace F} (hq : q ∈ outsideS S) :
    ∃ ε ∈ Sᶜ.unit F, 1 < placeAbs q (ε : F) ∧
      ∀ p ∈ outsideS S, p ≠ q → placeAbs p (ε : F) < 1 := by
  obtain ⟨x, hx1, hx2⟩ := exists_ell_sign hS hs ⟨q, (mem_Pfin hS).2 hq⟩
  refine ⟨((x : Sᶜ.unit F) : Fˣ), x.2, ?_, fun p hp hpq => ?_⟩
  · exact (ellFun_pos_iff _ _).1 (by simpa [ell_apply] using hx1)
  · have := hx2 ⟨p, (mem_Pfin hS).2 hp⟩ (fun h => hpq (congrArg Subtype.val h))
    exact (ellFun_neg_iff _ _).1 (by simpa [ell_apply] using this)

/-- **33:9.** In the situation of 33:8 let $T$ be a set of $s - 1$ elements of $\Omega - S$, and for each
$\mathfrak q \in T$ let $\varepsilon_{\mathfrak q}$ be an $S$-unit as in 33:8. Then the $\varepsilon_{\mathfrak q}$ are
multiplicatively independent and generate a subgroup of finite index in $\mathfrak u(S)$. -/
@[kb "omeara1963" "§33F, 33:9, p. 75"]
theorem sUnits_independent_finiteIndex {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite)
    (T : Finset (NFPlace F)) (hT : (T : Set (NFPlace F)) ⊆ outsideS S) (hcard : T.card + 1 = (outsideS S).ncard)
    (ε : NFPlace F → Sᶜ.unit F)
    (hε : ∀ q ∈ T, 1 < placeAbs q ((ε q : Fˣ) : F) ∧
      ∀ p ∈ outsideS S, p ≠ q → placeAbs p ((ε q : Fˣ) : F) < 1) :
    (∀ k : NFPlace F → ℤ, ∏ q ∈ T, ε q ^ k q = 1 → ∀ q ∈ T, k q = 0) ∧
      (Subgroup.closure (ε '' (T : Set (NFPlace F)))).index ≠ 0 := by
  have hli := indep_ell hS T hT hcard ε hε
  refine ⟨fun k hk q hq => ?_, ?_⟩
  · have h1 := congrArg (fun y => ellH hS (Additive.ofMul y)) hk
    simp only [ofMul_prod, ofMul_zpow, map_sum, map_zsmul, ofMul_one, map_zero] at h1
    have h2 : ∑ q : T, ((k q.1 : ℤ) : ℝ) • ellH hS (Additive.ofMul (ε q.1)) = 0 := by
      calc ∑ q : T, ((k q.1 : ℤ) : ℝ) • ellH hS (Additive.ofMul (ε q.1))
          = ∑ q : T, k q.1 • ellH hS (Additive.ofMul (ε q.1)) :=
            Finset.sum_congr rfl fun q _ =>
              Int.cast_smul_eq_zsmul ℝ (k q.1) (ellH hS (Additive.ofMul (ε q.1)))
        _ = ∑ q ∈ T, k q • ellH hS (Additive.ofMul (ε q)) :=
            Finset.sum_coe_sort T (fun q => k q • ellH hS (Additive.ofMul (ε q)))
        _ = 0 := h1
    have := Fintype.linearIndependent_iff.1 hli _ h2 ⟨q, hq⟩
    exact_mod_cast this
  · classical
    set G := Subgroup.closure (ε '' (T : Set (NFPlace F))) with hG
    let v : T → Hs hS := fun q => ellH hS (Additive.ofMul (ε q.1))
    have hcardT : Fintype.card T = Module.finrank ℝ (Hs hS) := by
      rw [Fintype.card_coe, finrank_Hs]; omega
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hcardT
    let b' : Module.Basis T ℝ (Hs hS) := Module.Basis.mk hli (le_of_eq hspan.symm)
    have hb' : ∀ q, b' q = v q := fun q => by simp [b']; rfl
    set C : ℝ := ∑ i, ‖b' i‖ with hC
    have hY := finite_ell_bounded hS C
    have hmemG : ∀ z ∈ Submodule.span ℤ (Set.range b'), ∃ g ∈ G, ellH hS (Additive.ofMul g) = z := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨q, rfl⟩ := hz
        exact ⟨ε q.1, Subgroup.subset_closure ⟨q.1, q.2, rfl⟩, (hb' q).symm⟩
      | zero => exact ⟨1, G.one_mem, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨g1, h1, e1⟩ := ha
        obtain ⟨g2, h2, e2⟩ := hb
        exact ⟨g1 * g2, G.mul_mem h1 h2, by rw [ofMul_mul, map_add, e1, e2]⟩
      | smul c a _ ha =>
        obtain ⟨g, h, e⟩ := ha
        exact ⟨g ^ c, G.zpow_mem h c, by rw [ofMul_zpow, map_zsmul, e]⟩
    have hcover : ∀ x : Sᶜ.unit F, ∃ g ∈ G, ∃ y : Sᶜ.unit F,
        (∀ p : Pl hS, |ell hS (Additive.ofMul y) p| ≤ C) ∧ x = g * y := by
      intro x
      let m : Hs hS := ellH hS (Additive.ofMul x)
      obtain ⟨g, hgG, hg⟩ := hmemG (ZSpan.floor b' m : Hs hS) (ZSpan.floor b' m).2
      refine ⟨g, hgG, g⁻¹ * x, fun p => ?_, by simp⟩
      have h1 : ellH hS (Additive.ofMul (g⁻¹ * x)) = ZSpan.fract b' m := by
        rw [ofMul_mul, ofMul_inv, map_add, map_neg, hg, ZSpan.fract_apply]
        abel
      have h2 := norm_le_pi_norm ((ZSpan.fract b' m : Hs hS) : Pl hS → ℝ) p
      have h3 : ‖ZSpan.fract b' m‖ ≤ C := ZSpan.norm_fract_le b' m
      rw [Real.norm_eq_abs] at h2
      have h4 : ‖((ZSpan.fract b' m : Hs hS) : Pl hS → ℝ)‖ ≤ C := h3
      have := h2.trans h4
      rw [← h1] at this
      simpa [coe_ellH] using this
    have : Finite (Sᶜ.unit F ⧸ G) := by
      have : Finite ↥{y : Sᶜ.unit F | ∀ p : Pl hS, |ell hS (Additive.ofMul y) p| ≤ C} := hY.to_subtype
      refine Finite.of_surjective
        (fun y : ↥{y : Sᶜ.unit F | ∀ p : Pl hS, |ell hS (Additive.ofMul y) p| ≤ C} =>
          (QuotientGroup.mk y.1 : Sᶜ.unit F ⧸ G)) ?_
      intro a
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨g, hgG, y, hy, hxy⟩ := hcover x
      refine ⟨⟨y, hy⟩, ?_⟩
      show (QuotientGroup.mk y : Sᶜ.unit F ⧸ G) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      have : y⁻¹ * x = g := by rw [hxy, mul_comm g y, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]; exact hgG
    exact Subgroup.index_ne_zero_of_finite

/-- **33:10 (The Dirichlet Unit Theorem).** Let $S$ be a set of discrete spots of $F$ with $\Omega - S$ finite of
$s \ge 1$ elements. Then the group $\mathfrak u(S)$ of $S$-units is the direct product of the group of absolute units
(the roots of unity of $F$, 33:6) with $s - 1$ infinite cyclic groups: there are $S$-units
$\eta_1, \dots, \eta_{s-1}$ such that every $S$-unit is uniquely $\zeta\,\eta_1^{k_1}\cdots\eta_{s-1}^{k_{s-1}}$ with
$\zeta$ an absolute unit and $k_i \in \mathbb Z$. -/
@[kb "omeara1963" "§33F, 33:10, p. 77 (Dirichlet Unit Theorem)"]
theorem sUnit_theorem {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    absoluteUnits F ≤ Sᶜ.unit F ∧
      ∃ η : Fin ((outsideS S).ncard - 1) → Sᶜ.unit F, ∀ x : Sᶜ.unit F,
        ∃! p : absoluteUnits F × (Fin ((outsideS S).ncard - 1) → ℤ),
          (x : Fˣ) = (p.1 : Fˣ) * ∏ i, ((η i : Sᶜ.unit F) : Fˣ) ^ p.2 i := by
  refine ⟨absoluteUnits_le_unit, ?_⟩
  obtain ⟨η, hη⟩ := exists_eta hS
  refine ⟨η, fun x => ?_⟩
  let Q : (Fin ((outsideS S).ncard - 1) → ℤ) → Sᶜ.unit F :=
    fun k => (∑ i, k i • Additive.ofMul (η i)).toMul
  have hQ1 : ∀ k, ellH hS (Additive.ofMul (Q k)) = ∑ i, k i • ellH hS (Additive.ofMul (η i)) := by
    intro k
    simp only [Q, ofMul_toMul, map_sum, map_zsmul]
  have hQ2 : ∀ k, ((Q k : Sᶜ.unit F) : Fˣ) = ∏ i, ((η i : Sᶜ.unit F) : Fˣ) ^ k i := by
    intro k
    simp [Q, toMul_sum, toMul_zsmul]
  have hzero : ∀ z : Sᶜ.unit F, ellH hS (Additive.ofMul z) = 0 ↔ (z : Fˣ) ∈ absoluteUnits F := by
    intro z
    rw [← ell_eq_zero_iff hS z]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  obtain ⟨k, hk, hku⟩ := hη x
  have hz0 : ellH hS (Additive.ofMul (x * (Q k)⁻¹)) = 0 := by
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, hQ1, hk]
    simp
  have hzmem := (hzero _).1 hz0
  refine ⟨(⟨((x * (Q k)⁻¹ : Sᶜ.unit F) : Fˣ), hzmem⟩, k), ?_, ?_⟩
  · show (x : Fˣ) = ((x * (Q k)⁻¹ : Sᶜ.unit F) : Fˣ) * ∏ i, ((η i : Sᶜ.unit F) : Fˣ) ^ k i
    rw [← hQ2 k]
    simp
  · rintro ⟨ζ, k'⟩ h
    have h1 : (x : Fˣ) = (ζ : Fˣ) * ((Q k' : Sᶜ.unit F) : Fˣ) := by rw [hQ2 k']; exact h
    let ζU : Sᶜ.unit F := ⟨(ζ : Fˣ), absoluteUnits_le_unit ζ.2⟩
    have h2 : x = ζU * Q k' := Subtype.ext h1
    have h3 : ellH hS (Additive.ofMul x) = ∑ i, k' i • ellH hS (Additive.ofMul (η i)) := by
      rw [h2, ofMul_mul, map_add, hQ1, (hzero ζU).2 ζ.2, zero_add]
    have h4 : k' = k := hku k' h3
    subst h4
    have h5 : (ζ : Fˣ) = ((x * (Q k')⁻¹ : Sᶜ.unit F) : Fˣ) := by
      rw [h2]; simp [ζU]
    exact Prod.ext (Subtype.ext h5) rfl

end QuadFormsKB.OMeara
