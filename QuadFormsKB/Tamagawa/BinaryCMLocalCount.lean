import QuadFormsKB.Tamagawa.BinaryCMMass
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Norm-one elements of quadratic orders over $\mathfrak o_\mathfrak p$, counted modulo $\mathfrak p^k$

**Layer:** $F$ a number field, $\mathfrak p$ a finite prime, $\mathfrak o = \mathfrak o_\mathfrak p$ with uniformizer $\varpi$ (`NF.π`),
$q = N\mathfrak p$; a quadratic order $\Gamma = \mathfrak o[\omega]$, $\omega^2 = a + b\omega$ (Mathlib's `QuadraticAlgebra 𝔬 a b`), and its
reductions $\Gamma_k = \Gamma/\varpi^k\Gamma$ (`QuadraticAlgebra (𝔬/ϖ^k) ā b̄`).

**Proves** (finite counting; no Hensel):
* `card_units_Ok`: $|(\mathfrak o/\varpi^k)^\times| = q^{k-1}(q-1)$; `card_units_QA`: $|\Gamma_k^\times| = q^{2(k-1)}\,|\Gamma_1^\times|$ (an element is a
  unit iff its norm is, iff it is a unit modulo $\varpi$);
* **`card_normOne_mul_card_range`**: $\#\{z \in \Gamma_k : N(z) = 1\}\cdot\#N(\Gamma_k^\times) = |\Gamma_k^\times|$ (the norm-one elements are the
  kernel of $N : \Gamma_k^\times \to (\mathfrak o/\varpi^k)^\times$; `card_range_mul_card_ker`).

So $q^{-k}\#\{N = 1\} = |\Gamma_1^\times|\,j_k/(q(q-1))$ with $j_k = [(\mathfrak o/\varpi^k)^\times : N(\Gamma_k^\times)]$: the local density of the norm
form of $\Gamma$ at $1$ is a unit count times a norm index.

Source: Siegel 1935 / Kitaoka 1993, §5.6 (local densities as limits of counts) [unverified].

-/

open NumberField IsDedekindDomain QuadraticAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM.Loc

open LocalDensity

/-! ### Fibres of a surjective additive homomorphism -/

theorem card_preimage {A B : Type*} [AddGroup A] [AddGroup B] (f : A →+ B) (hf : Function.Surjective f)
    (S : Set B) : Nat.card {x : A // f x ∈ S} = Nat.card S * Nat.card f.ker := by
  refine DVR.natCard_eq_of_fibres (fun x : {x : A // f x ∈ S} => (⟨f x, x.2⟩ : S)) fun s => ?_
  let x₀ := (hf s.1).choose
  have hx₀ : f x₀ = s.1 := (hf s.1).choose_spec
  exact
    { toFun := fun x => ⟨x.1.1 - x₀, by
        rw [AddMonoidHom.mem_ker, map_sub, hx₀]
        have := congrArg Subtype.val x.2
        simp only at this
        rw [this, sub_self]⟩
      invFun := fun y => ⟨⟨y.1 + x₀, by rw [map_add, y.2, zero_add, hx₀]; exact s.2⟩, by
        apply Subtype.ext; simp only; rw [map_add, y.2, zero_add, hx₀]⟩
      left_inv := fun x => by apply Subtype.ext; apply Subtype.ext; simp
      right_inv := fun y => by apply Subtype.ext; simp }

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "𝔬" => v.adicCompletionIntegers F

/-- The uniformizer $\varpi \in \mathfrak o_\mathfrak p$. -/
abbrev πv : 𝔬 := NF.π v

/-- $\mathfrak o/\varpi^k$. -/
abbrev Ok (k : ℕ) : Type := 𝔬 ⧸ Ideal.span {πv v ^ k}

/-- $q = N\mathfrak p$. -/
abbrev qv : ℕ := Ideal.absNorm v.asIdeal

theorem card_Ok (k : ℕ) : Nat.card (Ok v k) = qv v ^ k := NF.card_quot_π_pow v k

theorem qv_pos : 0 < qv v := by
  have := Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  exact Nat.pos_of_ne_zero this

theorem one_lt_qv : 1 < qv v := by
  have h := NF.q_completion v
  have h2 : 2 ≤ DVR.q (v.adicCompletionIntegers F) := by
    rw [h]
    exact (Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top) |> fun hne =>
      Nat.lt_of_le_of_ne (qv_pos v) (Ne.symm hne)
  rw [h] at h2; exact h2

instance finite_Ok (k : ℕ) : Finite (Ok v k) :=
  Nat.finite_of_card_ne_zero (by rw [card_Ok]; exact pow_ne_zero _ (qv_pos v).ne')

theorem span_pow_le {m k : ℕ} (h : m ≤ k) : Ideal.span {πv v ^ k} ≤ Ideal.span {πv v ^ m} := by
  rw [Ideal.span_singleton_le_span_singleton]; exact pow_dvd_pow _ h

/-- The reduction $\mathfrak o/\varpi^k \to \mathfrak o/\varpi^m$ ($m \le k$). -/
def red {m k : ℕ} (h : m ≤ k) : Ok v k →+* Ok v m := Ideal.Quotient.factor (span_pow_le v h)

theorem red_mk {m k : ℕ} (h : m ≤ k) (x : 𝔬) :
    red v h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem red_surjective {m k : ℕ} (h : m ≤ k) : Function.Surjective (red v h) :=
  Ideal.Quotient.factor_surjective _

/-- **Units of $\mathfrak o/\varpi^k$ are the classes of units** ($k \ge 1$): $\bar x$ is a unit iff $\varpi \nmid x$. -/
theorem span_pow_ne_top {k : ℕ} (hk : 1 ≤ k) : Ideal.span {πv v ^ k} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, isUnit_pow_iff (by omega)]
  exact (NF.irreducible_π v).not_isUnit

instance nontrivial_Ok (k : ℕ) [Fact (1 ≤ k)] : Nontrivial (Ok v k) :=
  Ideal.Quotient.nontrivial_iff.mpr (span_pow_ne_top v Fact.out)

theorem isUnit_mk_iff {k : ℕ} (hk : 1 ≤ k) (x : 𝔬) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {πv v ^ k}) x) ↔ ¬ πv v ∣ x := by
  haveI : Fact (1 ≤ k) := ⟨hk⟩
  constructor
  · rintro hu ⟨y, rfl⟩
    -- π̄ is nilpotent in 𝔬/π^k
    have hnil : (Ideal.Quotient.mk (Ideal.span {πv v ^ k}) (πv v)) ^ k = 0 := by
      have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (πv v ^ k))
      rwa [map_pow] at h0
    have hu' := hu.pow k
    rw [map_mul, mul_pow, hnil, zero_mul] at hu'
    exact not_isUnit_zero hu'
  · intro h
    have hx : IsUnit x := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) h
    exact hx.map _

theorem card_ker_red {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (red v hk).toAddMonoidHom.ker = qv v ^ (k - 1) := by
  have h := card_preimage (red v hk).toAddMonoidHom (red_surjective v hk) Set.univ
  have e1 : Nat.card {x : Ok v k // (red v hk).toAddMonoidHom x ∈ (Set.univ : Set (Ok v 1))} = qv v ^ k := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => Set.mem_univ _), card_Ok]
  rw [e1, Nat.card_univ, card_Ok, pow_one] at h
  have hq := qv_pos v
  have : qv v ^ k = qv v * qv v ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  rw [this] at h
  exact (Nat.eq_of_mul_eq_mul_left hq h).symm

theorem isUnit_iff_red {k : ℕ} (hk : 1 ≤ k) (w : Ok v k) : IsUnit w ↔ IsUnit (red v hk w) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [red_mk, isUnit_mk_iff v hk, isUnit_mk_iff v le_rfl]

theorem isUnit_one_iff (w : Ok v 1) : IsUnit w ↔ w ≠ 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [isUnit_mk_iff v le_rfl, Ne, Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]

theorem card_units_eq_card_isUnit (M : Type*) [Monoid M] : Nat.card Mˣ = Nat.card {x : M // IsUnit x} :=
  Nat.card_congr
    { toFun := fun u => ⟨u, u.isUnit⟩
      invFun := fun x => x.2.unit
      left_inv := fun u => Units.ext rfl
      right_inv := fun x => Subtype.ext rfl }

/-- **$|(\mathfrak o/\varpi^k)^\times| = q^{k-1}(q-1)$** for $k \ge 1$. -/
theorem card_units_Ok {k : ℕ} (hk : 1 ≤ k) : Nat.card (Ok v k)ˣ = qv v ^ (k - 1) * (qv v - 1) := by
  rw [card_units_eq_card_isUnit]
  have e : {x : Ok v k // IsUnit x} ≃
      {x : Ok v k // (red v hk).toAddMonoidHom x ∈ ({y | y ≠ 0} : Set (Ok v 1))} :=
    Equiv.subtypeEquivRight fun _ => by
      rw [isUnit_iff_red v hk, isUnit_one_iff]; rfl
  rw [Nat.card_congr e, card_preimage (red v hk).toAddMonoidHom (red_surjective v hk), card_ker_red v hk]
  have h1 : Nat.card ({y | y ≠ 0} : Set (Ok v 1)) = qv v - 1 := by
    classical
    have h3 : Nat.card {y : Ok v 1 // y = 0} + Nat.card {y : Ok v 1 // ¬ y = 0} = Nat.card (Ok v 1) := by
      rw [← Nat.card_sum]; exact Nat.card_congr (Equiv.sumCompl _)
    have h4 : Nat.card {y : Ok v 1 // y = 0} = 1 := Nat.card_unique
    have h5 : Nat.card (Ok v 1) = qv v := by rw [card_Ok, pow_one]
    show Nat.card {y : Ok v 1 // ¬ y = 0} = _
    omega
  rw [h1, mul_comm]

/-! ### Quadratic algebras modulo $\varpi^k$ -/

variable (a b : v.adicCompletionIntegers F)

/-- $\Gamma_k = \Gamma/\varpi^k\Gamma$ for $\Gamma = \mathfrak o[\omega]$, $\omega^2 = a + b\omega$. -/
abbrev QAk (a b : v.adicCompletionIntegers F) (k : ℕ) : Type :=
  QuadraticAlgebra (Ok v k) (Ideal.Quotient.mk (Ideal.span {πv v ^ k}) a) (Ideal.Quotient.mk (Ideal.span {πv v ^ k}) b)

instance finite_QAk (k : ℕ) : Finite (QAk v a b k) := Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm

theorem card_QAk (k : ℕ) : Nat.card (QAk v a b k) = qv v ^ (2 * k) := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd _ _), Nat.card_prod, card_Ok]; ring

/-- The reduction $\Gamma_k \to \Gamma_m$. -/
def redQA {m k : ℕ} (h : m ≤ k) : QAk v a b k →+* QAk v a b m :=
  QuadraticAlgebra.mapRingHom (red v h) _ _

theorem redQA_surjective {m k : ℕ} (h : m ≤ k) : Function.Surjective (redQA v a b h) :=
  QuadraticAlgebra.mapRingHom_surjective _ _ _ (red_surjective v h)

theorem norm_redQA {m k : ℕ} (h : m ≤ k) (z : QAk v a b k) :
    QuadraticAlgebra.norm (redQA v a b h z) = red v h (QuadraticAlgebra.norm z) :=
  QuadraticAlgebra.norm_mapRingHom _ _ _ z

theorem isUnit_QAk_iff {k : ℕ} (hk : 1 ≤ k) (z : QAk v a b k) : IsUnit z ↔ IsUnit (redQA v a b hk z) := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_redQA,
    isUnit_iff_red v hk]

theorem card_ker_redQA {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (redQA v a b hk).toAddMonoidHom.ker = qv v ^ (2 * (k - 1)) := by
  have h := card_preimage (redQA v a b hk).toAddMonoidHom (redQA_surjective v a b hk) Set.univ
  have e1 : Nat.card {x : QAk v a b k // (redQA v a b hk).toAddMonoidHom x ∈
      (Set.univ : Set (QAk v a b 1))} = qv v ^ (2 * k) := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => Set.mem_univ _), card_QAk]
  rw [e1, Nat.card_univ, card_QAk] at h
  have hq := pow_pos (qv_pos v) (2 * 1)
  have : qv v ^ (2 * k) = qv v ^ (2 * 1) * qv v ^ (2 * (k - 1)) := by rw [← pow_add]; congr 1; omega
  rw [this] at h
  exact (Nat.eq_of_mul_eq_mul_left hq h).symm

/-- **$|\Gamma_k^\times| = q^{2(k-1)}\,|\Gamma_1^\times|$** ($k \ge 1$): units are the preimage of the units of $\Gamma_1$. -/
theorem card_units_QAk {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (QAk v a b k)ˣ = Nat.card (QAk v a b 1)ˣ * qv v ^ (2 * (k - 1)) := by
  rw [card_units_eq_card_isUnit, card_units_eq_card_isUnit]
  have e : {x : QAk v a b k // IsUnit x} ≃
      {x : QAk v a b k // (redQA v a b hk).toAddMonoidHom x ∈ ({y | IsUnit y} : Set (QAk v a b 1))} :=
    Equiv.subtypeEquivRight fun x => isUnit_QAk_iff v a b hk x
  rw [Nat.card_congr e, card_preimage _ (redQA_surjective v a b hk), card_ker_redQA v a b hk]
  rfl

/-- The norm on units, $\Gamma_k^\times \to (\mathfrak o/\varpi^k)^\times$. -/
abbrev normU (k : ℕ) : (QAk v a b k)ˣ →* (Ok v k)ˣ := Units.map QuadraticAlgebra.norm

/-- **$\#\{N = 1\}\cdot\#N(\Gamma_k^\times) = |\Gamma_k^\times|$.** -/
theorem card_normOne_mul_card_range (k : ℕ) :
    Nat.card {z : QAk v a b k // QuadraticAlgebra.norm z = 1} * Nat.card (Set.range (normU v a b k)) =
      Nat.card (QAk v a b k)ˣ := by
  rw [mul_comm, ← Binary.Rel.card_range_mul_card_ker (normU v a b k)]
  congr 1
  refine Nat.card_congr
    { toFun := fun z => ⟨(QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [z.2]; exact isUnit_one)).unit,
        Units.ext (by simpa using z.2)⟩
      invFun := fun g => ⟨g.1, by simpa [Units.ext_iff] using g.2⟩
      left_inv := fun z => rfl
      right_inv := fun g => by apply Subtype.ext; exact Units.ext rfl }

/-! ### The norm index at infinite level -/

/-- The norm on units of $\Gamma = \mathfrak o[\omega]$. -/
abbrev normΓ : (QuadraticAlgebra (v.adicCompletionIntegers F) a b)ˣ →* (v.adicCompletionIntegers F)ˣ :=
  Units.map QuadraticAlgebra.norm

/-- **The norm index** $j(\Gamma) = [\mathfrak o^\times : N(\Gamma^\times)]$. -/
abbrev jΓ : ℕ := (normΓ v a b).range.index

/-- The reduction of units $\mathfrak o^\times \to (\mathfrak o/\varpi^k)^\times$. -/
abbrev redU (k : ℕ) : (v.adicCompletionIntegers F)ˣ →* (Ok v k)ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {πv v ^ k})).toMonoidHom

theorem redU_surjective {k : ℕ} (hk : 1 ≤ k) : Function.Surjective (redU v k) := by
  intro u
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : Ok v k)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {πv v ^ k}) x) := hx ▸ u.isUnit
  have hx' : IsUnit x := DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) ((isUnit_mk_iff v hk x).mp hu)
  exact ⟨hx'.unit, Units.ext (by simp [hx])⟩

/-- The reduction $\Gamma \to \Gamma_k$. -/
abbrev redΓ (k : ℕ) : QuadraticAlgebra (v.adicCompletionIntegers F) a b →+* QAk v a b k :=
  QuadraticAlgebra.mapRingHom (Ideal.Quotient.mk _) a b

theorem redΓ_surjective (k : ℕ) : Function.Surjective (redΓ v a b k) :=
  QuadraticAlgebra.mapRingHom_surjective _ _ _ Ideal.Quotient.mk_surjective

theorem isUnit_of_isUnit_redΓ {k : ℕ} (hk : 1 ≤ k) {z : QuadraticAlgebra (v.adicCompletionIntegers F) a b}
    (h : IsUnit (redΓ v a b k z)) : IsUnit z := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit] at h ⊢
  rw [QuadraticAlgebra.norm_mapRingHom] at h
  exact DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) ((isUnit_mk_iff v hk _).mp h)

/-- The value $e$ with $v(4) = e^{-e}$. -/
theorem exists_valued_four : ∃ e : ℕ, Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ)) :=
  Lattices.exists_valued_int_eq v (by norm_num : (4 : 𝓞 F) ≠ 0)

/-- **Units congruent to $1$ modulo $\varpi^k$, $k > v(4)$, are squares of units** (the local square theorem,
`HN.isSquare_of_valued_sub_one_lt`). -/
theorem exists_sq_of_redU_eq_one {e k : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) (hk : e + 1 ≤ k)
    (u : (v.adicCompletionIntegers F)ˣ) (hu : redU v k u = 1) :
    ∃ y : (v.adicCompletionIntegers F)ˣ, u = y ^ 2 := by
  have hmem : ((u : v.adicCompletionIntegers F) - 1) ∈ Ideal.span {πv v ^ k} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
    exact congrArg Units.val hu
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  have hval : Valued.v (((u : v.adicCompletionIntegers F) : v.adicCompletion F) - 1) <
      Valued.v (4 : v.adicCompletion F) := by
    have e1 : ((u : v.adicCompletionIntegers F) : v.adicCompletion F) - 1 =
        (t : v.adicCompletion F) * ((πv v : v.adicCompletionIntegers F) : v.adicCompletion F) ^ k := by
      have h := congrArg Subtype.val ht
      push_cast at h
      linear_combination -h
    have e4 : (4 : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) 4 := (map_ofNat _ 4).symm
    rw [e1, e4, he, map_mul, map_pow, NF.valued_π]
    have ht1 : Valued.v (t : v.adicCompletion F) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2
    calc Valued.v (t : v.adicCompletion F) * WithZero.exp (-1 : ℤ) ^ k ≤ 1 * WithZero.exp (-1 : ℤ) ^ k :=
          mul_le_mul_left ht1 _
      _ = WithZero.exp (-(k : ℤ)) := by rw [one_mul, ← WithZero.exp_nsmul]; congr 1; ring
      _ < WithZero.exp (-(e : ℤ)) := by rw [WithZero.exp_lt_exp]; omega
  obtain ⟨y, hy⟩ := HN.isSquare_of_valued_sub_one_lt v _ hval
  have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u : v.adicCompletionIntegers F).2
  have hn1 : ‖((u : v.adicCompletionIntegers F) : v.adicCompletion F)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr h1
  have hy1 : Valued.v y ≤ 1 := by
    refine (Valued.toNormedField.norm_le_one_iff).mp ?_
    rw [hy, norm_mul] at hn1
    nlinarith [norm_nonneg y]
  let y' : v.adicCompletionIntegers F := ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hy1⟩
  have hy' : (u : v.adicCompletionIntegers F) = y' * y' := Subtype.ext hy
  have hyu : IsUnit y' := isUnit_of_mul_isUnit_left (hy' ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, hy'])⟩

theorem normΓ_algebraMap (y : (v.adicCompletionIntegers F)ˣ) :
    normΓ v a b (Units.map (algebraMap _ (QuadraticAlgebra (v.adicCompletionIntegers F) a b)).toMonoidHom y) =
      y ^ 2 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact QuadraticAlgebra.norm_algebraMap (y : v.adicCompletionIntegers F)

theorem redU_normΓ (k : ℕ) (z : (QuadraticAlgebra (v.adicCompletionIntegers F) a b)ˣ) :
    redU v k (normΓ v a b z) = normU v a b k (Units.map (redΓ v a b k).toMonoidHom z) := by
  apply Units.ext
  exact (QuadraticAlgebra.norm_mapRingHom _ _ _ (z : QuadraticAlgebra (v.adicCompletionIntegers F) a b)).symm

/-- **The finite norm index stabilizes to $j(\Gamma)$:** $|(\mathfrak o/\varpi^k)^\times| = j(\Gamma)\cdot\#N(\Gamma_k^\times)$ for $k > v(4)$. -/
theorem card_units_Ok_eq_jΓ_mul {e k : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) (hk : e + 1 ≤ k) :
    Nat.card (Ok v k)ˣ = jΓ v a b * Nat.card (Set.range (normU v a b k)) := by
  have hk1 : 1 ≤ k := by omega
  set H := (normU v a b k).range
  have hcomap : H.comap (redU v k) = (normΓ v a b).range := by
    ext u
    rw [Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨z₀, hz₀⟩ := redΓ_surjective v a b k (w : QAk v a b k)
      have hzu : IsUnit z₀ := isUnit_of_isUnit_redΓ v a b hk1 (hz₀ ▸ w.isUnit)
      have hzw : Units.map (redΓ v a b k).toMonoidHom hzu.unit = w := Units.ext (by
        rw [Units.coe_map, IsUnit.unit_spec]; exact hz₀)
      have h1 : redU v k (normΓ v a b hzu.unit) = redU v k u := by rw [redU_normΓ, hzw, hw]
      have h2 : redU v k (u * (normΓ v a b hzu.unit)⁻¹) = 1 := by
        rw [map_mul, map_inv, h1, mul_inv_cancel]
      obtain ⟨y, hy⟩ := exists_sq_of_redU_eq_one v he hk _ h2
      refine ⟨hzu.unit * Units.map (algebraMap _ (QuadraticAlgebra (v.adicCompletionIntegers F) a b)).toMonoidHom y, ?_⟩
      rw [map_mul, normΓ_algebraMap, ← hy, mul_comm u, ← mul_assoc, mul_inv_cancel, one_mul]
    · rintro ⟨z, rfl⟩
      exact ⟨Units.map (redΓ v a b k).toMonoidHom z, (redU_normΓ v a b k z).symm⟩
  have hidx : jΓ v a b = H.index := by
    rw [jΓ, ← hcomap, Subgroup.index_comap_of_surjective _ (redU_surjective v hk1)]
  rw [hidx, ← H.card_mul_index, mul_comm]
  congr 1

theorem card_range_normU_pos (k : ℕ) : 0 < Nat.card (Set.range (normU v a b k)) :=
  Nat.card_pos_iff.mpr ⟨⟨1, 1, map_one _⟩, inferInstance⟩

theorem jΓ_pos {e : ℕ} (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) :
    0 < jΓ v a b := by
  have h := card_units_Ok_eq_jΓ_mul v a b he (le_refl (e + 1))
  rw [card_units_Ok v (by omega)] at h
  have hq := one_lt_qv v
  rcases Nat.eq_zero_or_pos (jΓ v a b) with h0 | h0
  · rw [h0, zero_mul] at h
    exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (pow_pos (qv_pos v) _) (by omega)))
  · exact h0

/-- **The local density of the norm form of $\Gamma$ at $1$:** for $k > v(4)$,
$$q^{-k}\,\#\{z \in \Gamma_k : N(z) = 1\} = \frac{|\Gamma_1^\times|\,j(\Gamma)}{q(q-1)} .$$ -/
theorem normOne_div_pow {e k : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) (hk : e + 1 ≤ k) :
    (Nat.card {z : QAk v a b k // QuadraticAlgebra.norm z = 1} : ℝ) / (qv v : ℝ) ^ k =
      Nat.card (QAk v a b 1)ˣ * jΓ v a b / (qv v * (qv v - 1)) := by
  have hk1 : 1 ≤ k := by omega
  have h1 := card_normOne_mul_card_range v a b k
  have h2 := card_units_QAk v a b hk1
  have h3 := card_units_Ok_eq_jΓ_mul v a b he hk
  rw [card_units_Ok v hk1] at h3
  have hq : (1 : ℝ) < qv v := by exact_mod_cast one_lt_qv v
  have hr : (0 : ℝ) < Nat.card (Set.range (normU v a b k)) := by exact_mod_cast card_range_normU_pos v a b k
  have h1' : (Nat.card {z : QAk v a b k // QuadraticAlgebra.norm z = 1} : ℝ) *
      Nat.card (Set.range (normU v a b k)) = Nat.card (QAk v a b 1)ˣ * (qv v : ℝ) ^ (2 * (k - 1)) := by
    have := congrArg (Nat.cast : ℕ → ℝ) (h1.trans h2)
    push_cast at this
    exact this
  have h3' : (qv v : ℝ) ^ (k - 1) * ((qv v : ℝ) - 1) = jΓ v a b * Nat.card (Set.range (normU v a b k)) := by
    have : ((qv v - 1 : ℕ) : ℝ) = (qv v : ℝ) - 1 := by
      rw [Nat.cast_sub (one_lt_qv v).le, Nat.cast_one]
    rw [← this]; exact_mod_cast h3
  have hk' : (qv v : ℝ) ^ k = qv v * (qv v : ℝ) ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hk2 : (qv v : ℝ) ^ (2 * (k - 1)) = (qv v : ℝ) ^ (k - 1) * (qv v : ℝ) ^ (k - 1) := by
    rw [← pow_add]; congr 1; omega
  have hqk : (0 : ℝ) < (qv v : ℝ) ^ (k - 1) := by positivity
  rw [div_eq_div_iff (by positivity) (by nlinarith), hk']
  rw [hk2] at h1'
  apply mul_right_cancel₀ hr.ne'
  linear_combination ((qv v : ℝ) * ((qv v : ℝ) - 1)) * h1' +
    ((Nat.card (QAk v a b 1)ˣ : ℝ) * (qv v : ℝ) * (qv v : ℝ) ^ (k - 1)) * h3'

/-! ### The suborder $\mathfrak o + \varpi^c\Gamma$ -/

variable (c : ℕ)

/-- **The suborder** $\mathfrak o[\varpi^c\omega] \hookrightarrow \mathfrak o[\omega]$: $\langle x, y\rangle \mapsto x + y\varpi^c\omega$, from
`QuadraticAlgebra 𝔬 (ϖ^{2c} a) (ϖ^c b)` (generator $\omega' = \varpi^c\omega$). -/
def ιc : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * c) * a) (πv v ^ c * b) →+*
    QuadraticAlgebra (v.adicCompletionIntegers F) a b where
  toFun z := ⟨z.re, πv v ^ c * z.im⟩
  map_one' := by refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  map_mul' z w := by refine QuadraticAlgebra.ext ?_ ?_ <;> simp <;> ring
  map_zero' := by refine QuadraticAlgebra.ext ?_ ?_ <;> simp
  map_add' z w := by refine QuadraticAlgebra.ext ?_ ?_ <;> simp; ring

theorem ιc_re (z : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * c) * a) (πv v ^ c * b)) :
    (ιc v a b c z).re = z.re := rfl

theorem ιc_im (z : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * c) * a) (πv v ^ c * b)) :
    (ιc v a b c z).im = πv v ^ c * z.im := rfl

theorem norm_ιc (z : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * c) * a) (πv v ^ c * b)) :
    QuadraticAlgebra.norm (ιc v a b c z) = QuadraticAlgebra.norm z := by
  simp only [QuadraticAlgebra.norm_def, ιc_re, ιc_im]; ring

theorem πv_ne_zero : πv v ≠ 0 := (NF.irreducible_π v).ne_zero

theorem ιc_injective : Function.Injective (ιc v a b c) := by
  intro z w h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  rw [ιc_re, ιc_re] at h1
  rw [ιc_im, ιc_im] at h2
  exact QuadraticAlgebra.ext h1 (mul_left_cancel₀ (pow_ne_zero c (πv_ne_zero v)) h2)

/-- The units of the suborder inside $\Gamma^\times$. -/
abbrev Hc : Subgroup (QuadraticAlgebra (v.adicCompletionIntegers F) a b)ˣ :=
  (Units.map (ιc v a b c).toMonoidHom).range

/-- **$[\Gamma^\times : (\mathfrak o + \varpi^c\Gamma)^\times]\cdot|(\mathfrak o/\varpi^c)^\times| = |\Gamma_c^\times|$** ($c \ge 1$): the suborder's units are the
preimage of the constants $(\mathfrak o/\varpi^c)^\times \subset \Gamma_c^\times$. -/
theorem index_Hc_mul {c : ℕ} (hc : 1 ≤ c) :
    (Hc v a b c).index * Nat.card (Ok v c)ˣ = Nat.card (QAk v a b c)ˣ := by
  set rc : (QuadraticAlgebra (v.adicCompletionIntegers F) a b)ˣ →* (QAk v a b c)ˣ :=
    Units.map (redΓ v a b c).toMonoidHom
  have hrc : Function.Surjective rc := by
    intro w
    obtain ⟨z₀, hz₀⟩ := redΓ_surjective v a b c (w : QAk v a b c)
    have hzu : IsUnit z₀ := isUnit_of_isUnit_redΓ v a b hc (hz₀ ▸ w.isUnit)
    exact ⟨hzu.unit, Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; exact hz₀)⟩
  set C : Subgroup (QAk v a b c)ˣ := (Units.map (algebraMap (Ok v c) (QAk v a b c)).toMonoidHom).range
  have hcomap : C.comap rc = Hc v a b c := by
    ext z
    rw [Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      have him : (redΓ v a b c (z : QuadraticAlgebra _ a b)).im = 0 := by
        have := congrArg (fun w : (QAk v a b c)ˣ => (w : QAk v a b c).im) hu
        change (algebraMap (Ok v c) (QAk v a b c) (u : Ok v c)).im =
          (redΓ v a b c (z : QuadraticAlgebra _ a b)).im at this
        rw [QuadraticAlgebra.algebraMap_im] at this
        exact this.symm
      have hdvd : πv v ^ c ∣ (z : QuadraticAlgebra _ a b).im := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]; exact him
      obtain ⟨t, ht⟩ := hdvd
      set s : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * c) * a) (πv v ^ c * b) :=
        ⟨(z : QuadraticAlgebra _ a b).re, t⟩
      have hs : ιc v a b c s = z := QuadraticAlgebra.ext rfl ht.symm
      have hsu : IsUnit s := by
        rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, ← norm_ιc, hs, ← QuadraticAlgebra.isUnit_iff_norm_isUnit]
        exact z.isUnit
      exact ⟨hsu.unit, Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; exact hs)⟩
    · rintro ⟨s, rfl⟩
      have hre : IsUnit (Ideal.Quotient.mk (Ideal.span {πv v ^ c}) s.val.re) := by
        have hn : IsUnit (Ideal.Quotient.mk (Ideal.span {πv v ^ c}) (QuadraticAlgebra.norm s.val)) :=
          (s.isUnit.map QuadraticAlgebra.norm).map _
        rw [QuadraticAlgebra.norm_def] at hn
        have hz1 : Ideal.Quotient.mk (Ideal.span {πv v ^ c}) (πv v ^ c) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
        have hz2 : Ideal.Quotient.mk (Ideal.span {πv v ^ c}) (πv v ^ (2 * c)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact pow_dvd_pow _ (by omega)
        simp only [map_add, map_sub, map_mul, hz1, hz2, zero_mul, add_zero, sub_zero] at hn
        exact isUnit_of_mul_isUnit_left hn
      refine ⟨hre.unit, Units.ext ?_⟩
      rw [Units.coe_map, IsUnit.unit_spec]
      refine QuadraticAlgebra.ext rfl ?_
      show (0 : Ok v c) = Ideal.Quotient.mk _ (πv v ^ c * s.val.im)
      rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
  have hidx : (Hc v a b c).index = C.index := by
    rw [← hcomap, Subgroup.index_comap_of_surjective _ hrc]
  have hcard : Nat.card C = Nat.card (Ok v c)ˣ := by
    have hinj : Function.Injective (Units.map (algebraMap (Ok v c) (QAk v a b c)).toMonoidHom) := by
      intro u w h
      apply Units.ext
      have := congrArg (fun x : (QAk v a b c)ˣ => (x : QAk v a b c).re) h
      simpa using this
    rw [show Nat.card C = Nat.card (Set.range (Units.map (algebraMap (Ok v c) (QAk v a b c)).toMonoidHom)) from
      Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_range)]
    exact Nat.card_range_of_injective hinj
  rw [hidx, ← hcard, mul_comm, C.card_mul_index]

/-! ### The index identity and the local factor -/

/-- **$[G : H] = [f(G) : f(H)]\cdot[\ker f : H \cap \ker f]$** for a homomorphism $f$ on a commutative group. -/
theorem index_eq_relIndex_mul {G G' : Type*} [CommGroup G] [Group G'] (f : G →* G') (H : Subgroup G) :
    H.index = (H.map f).relIndex f.range * H.relIndex f.ker := by
  have hN : H.Normal := Subgroup.normal_of_isMulCommutative H
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ f.ker), Subgroup.relIndex_sup_left, mul_comm]
  congr 1
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]

theorem norm_eq_re_mul_re {R : Type*} [CommRing R] {a' b' : R} (ha : a' = 0) (hb : b' = 0)
    (z : QuadraticAlgebra R a' b') : QuadraticAlgebra.norm z = z.re * z.re := by
  subst ha; subst hb; rw [QuadraticAlgebra.norm_def]; ring

/-- $|(\mathfrak o + \varpi^c\Gamma)_1^\times| = q(q-1)$ for $c \ge 1$: modulo $\varpi$ the suborder is $k[\varepsilon]$. -/
theorem card_units_QAk_sub {c : ℕ} (hc : 1 ≤ c) :
    Nat.card (QAk v (πv v ^ (2 * c) * a) (πv v ^ c * b) 1)ˣ = qv v * (qv v - 1) := by
  rw [card_units_eq_card_isUnit]
  have hz1 : Ideal.Quotient.mk (Ideal.span {πv v ^ 1}) (πv v ^ c * b) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hc) _
  have hz2 : Ideal.Quotient.mk (Ideal.span {πv v ^ 1}) (πv v ^ (2 * c) * a) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
  have : Fact (1 ≤ 1) := ⟨le_rfl⟩
  have e : {z : QAk v (πv v ^ (2 * c) * a) (πv v ^ c * b) 1 // IsUnit z} ≃ {x : Ok v 1 // x ≠ 0} × Ok v 1 :=
    { toFun := fun z => (⟨z.1.re, by
          intro h0
          have := (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp z.2)
          rw [norm_eq_re_mul_re hz2 hz1, h0, zero_mul] at this
          exact not_isUnit_zero (M₀ := Ok v 1) this⟩, z.1.im)
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, by
          rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_eq_re_mul_re hz2 hz1]
          exact ((isUnit_one_iff v _).mpr p.1.2).mul ((isUnit_one_iff v _).mpr p.1.2)⟩
      left_inv := fun z => by apply Subtype.ext; rfl
      right_inv := fun p => rfl }
  classical
  have h3 : Nat.card {y : Ok v 1 // y = 0} + Nat.card {y : Ok v 1 // ¬ y = 0} = Nat.card (Ok v 1) := by
    rw [← Nat.card_sum]; exact Nat.card_congr (Equiv.sumCompl _)
  have h4 : Nat.card {y : Ok v 1 // y = 0} = 1 := Nat.card_unique
  have h5 : Nat.card (Ok v 1) = qv v := by rw [card_Ok, pow_one]
  have hne : Nat.card {y : Ok v 1 // ¬ y = 0} = qv v - 1 := by omega
  rw [Nat.card_congr e, Nat.card_prod]
  change Nat.card {y : Ok v 1 // ¬ y = 0} * Nat.card (Ok v 1) = _
  rw [hne, h5, mul_comm]

/-- The norm-one subgroup index $\rho = [\Gamma^1 : (\mathfrak o + \varpi^c\Gamma)^1]$. -/
abbrev ρc : ℕ := (Hc v a b c).relIndex (normΓ v a b).ker

/-- **The local factor identity** ($c \ge 1$, $k > v(4)$): for the suborder $R = \mathfrak o + \varpi^c\Gamma$,
$$[\Gamma^1 : R^1]\cdot q^{-k}\#\{z \in R_k : N(z) = 1\} = q^c\,\frac{|\Gamma_1^\times|\,j(\Gamma)}{q(q-1)} .$$
*Proof:* $[\Gamma^\times : R^\times] = [N\Gamma^\times : NR^\times]\,[\Gamma^1 : R^1]$ (`index_eq_relIndex_mul`), $[N\Gamma^\times : NR^\times]\,j(\Gamma) = j(R)$,
$[\Gamma^\times : R^\times] = |\Gamma_c^\times|/|(\mathfrak o/\varpi^c)^\times|$ (`index_Hc_mul`), $|R_1^\times| = q(q-1)$, and the density formula
(`normOne_div_pow`) for $R$. -/
theorem rho_mul_normOne_div_pow {c : ℕ} (hc : 1 ≤ c) {e k : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) (hk : e + 1 ≤ k) :
    (ρc v a b c : ℝ) *
        ((Nat.card {z : QAk v (πv v ^ (2 * c) * a) (πv v ^ c * b) k // QuadraticAlgebra.norm z = 1} : ℝ) /
          (qv v : ℝ) ^ k) =
      (qv v : ℝ) ^ c * (Nat.card (QAk v a b 1)ˣ * jΓ v a b / (qv v * (qv v - 1))) := by
  set a' := πv v ^ (2 * c) * a
  set b' := πv v ^ c * b
  rw [normOne_div_pow v a' b' he hk, card_units_QAk_sub v a b hc]
  -- the group-theoretic identities
  have hmap : (Hc v a b c).map (normΓ v a b) = (normΓ v a' b').range := by
    rw [MonoidHom.map_range]
    congr 1
    exact MonoidHom.ext fun s => Units.ext (norm_ιc v a b c s.val)
  have hG5 := index_eq_relIndex_mul (normΓ v a b) (Hc v a b c)
  rw [hmap] at hG5
  have hle : (normΓ v a' b').range ≤ (normΓ v a b).range := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Units.map (ιc v a b c).toMonoidHom s, Units.ext (norm_ιc v a b c s.val)⟩
  have hj := Subgroup.relIndex_mul_index hle
  have hI := index_Hc_mul v a b hc
  rw [card_units_QAk v a b hc, card_units_Ok v hc] at hI
  have hjΛ := jΓ_pos v a b he
  have hq : (1 : ℝ) < qv v := by exact_mod_cast one_lt_qv v
  -- cast to ℝ
  have hG5' : ((Hc v a b c).index : ℝ) = ((normΓ v a' b').range.relIndex (normΓ v a b).range : ℝ) * ρc v a b c := by
    exact_mod_cast hG5
  have hj' : ((normΓ v a' b').range.relIndex (normΓ v a b).range : ℝ) * jΓ v a b = jΓ v a' b' := by
    exact_mod_cast hj
  have hI' : ((Hc v a b c).index : ℝ) * ((qv v : ℝ) ^ (c - 1) * ((qv v : ℝ) - 1)) =
      Nat.card (QAk v a b 1)ˣ * (qv v : ℝ) ^ (2 * (c - 1)) := by
    have : ((qv v - 1 : ℕ) : ℝ) = (qv v : ℝ) - 1 := by rw [Nat.cast_sub (one_lt_qv v).le, Nat.cast_one]
    rw [← this]; exact_mod_cast hI
  have hc' : (qv v : ℝ) ^ c = qv v * (qv v : ℝ) ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
  have hc2 : (qv v : ℝ) ^ (2 * (c - 1)) = (qv v : ℝ) ^ (c - 1) * (qv v : ℝ) ^ (c - 1) := by
    rw [← pow_add]; congr 1; omega
  have hqc : (0 : ℝ) < (qv v : ℝ) ^ (c - 1) := by positivity
  have hjpos : (0 : ℝ) < jΓ v a b := by exact_mod_cast hjΛ
  rw [hc2] at hI'
  have hq0 : (qv v : ℝ) * ((qv v : ℝ) - 1) ≠ 0 := by nlinarith
  have key : (ρc v a b c : ℝ) * jΓ v a' b' = (Hc v a b c).index * jΓ v a b := by
    rw [hG5', ← hj']; ring
  have key2 : ((Hc v a b c).index : ℝ) * ((qv v : ℝ) - 1) = Nat.card (QAk v a b 1)ˣ * (qv v : ℝ) ^ (c - 1) := by
    apply mul_left_cancel₀ hqc.ne'
    linear_combination hI'
  rw [show ((qv v * (qv v - 1) : ℕ) : ℝ) = (qv v : ℝ) * ((qv v : ℝ) - 1) by
    rw [Nat.cast_mul, Nat.cast_sub (one_lt_qv v).le, Nat.cast_one]]
  calc (ρc v a b c : ℝ) * ((qv v : ℝ) * ((qv v : ℝ) - 1) * jΓ v a' b' / ((qv v : ℝ) * ((qv v : ℝ) - 1)))
      = (ρc v a b c : ℝ) * jΓ v a' b' := by rw [mul_div_cancel_left₀ _ hq0]
    _ = (Hc v a b c).index * jΓ v a b := key
    _ = (qv v : ℝ) ^ c * (Nat.card (QAk v a b 1)ˣ * jΓ v a b / (qv v * (qv v - 1))) := by
      rw [hc']
      field_simp
      linear_combination key2

theorem mem_Hc_iff' (z : (QuadraticAlgebra (v.adicCompletionIntegers F) a b)ˣ) :
    z ∈ Hc v a b c ↔ πv v ^ c ∣ (z : QuadraticAlgebra _ a b).im := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val.im, ιc_im v a b c s.val⟩
  · rintro ⟨t, ht⟩
    set s : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * c) * a) (πv v ^ c * b) :=
      ⟨(z : QuadraticAlgebra _ a b).re, t⟩
    have hs : ιc v a b c s = z := QuadraticAlgebra.ext rfl ht.symm
    have hsu : IsUnit s := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, ← norm_ιc, hs, ← QuadraticAlgebra.isUnit_iff_norm_isUnit]
      exact z.isUnit
    exact ⟨hsu.unit, Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; exact hs)⟩

/-- **The local factor identity for every $c \ge 0$** ($k > v(4)$). -/
theorem rho_mul_normOne_div_pow_all (c : ℕ) {e k : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) (hk : e + 1 ≤ k) :
    (ρc v a b c : ℝ) *
        ((Nat.card {z : QAk v (πv v ^ (2 * c) * a) (πv v ^ c * b) k // QuadraticAlgebra.norm z = 1} : ℝ) /
          (qv v : ℝ) ^ k) =
      (qv v : ℝ) ^ c * (Nat.card (QAk v a b 1)ˣ * jΓ v a b / (qv v * (qv v - 1))) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have hρ : ρc v a b 0 = 1 :=
      Subgroup.relIndex_eq_one.mpr fun z _ => (mem_Hc_iff' v a b 0 z).mpr (by rw [pow_zero]; exact one_dvd _)
    have h1 : πv v ^ (2 * 0) * a = a := by simp
    have h2 : πv v ^ 0 * b = b := by simp
    rw [hρ, h1, h2, Nat.cast_one, one_mul, pow_zero, one_mul]
    exact normOne_div_pow v a b he hk
  · exact rho_mul_normOne_div_pow v a b hc he hk

end QuadFormsKB.Tamagawa.BinaryCM.Loc
