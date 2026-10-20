/-
# Hanke, AWS 2009 notes, §2.6, §2.7.1, §2.7.3: mass formulas and canonical local measures

J. Hanke, *Quadratic Forms and Automorphic Forms* (bibkey `hanke2011aws`), §2.6 (pp. 34–35) and
§2.7.1 (p. 36). The list D1, D2, … of the notes' derivations is in `AWS/Overview.lean`; this file is
**D1, D2, D3, D5**.

Forms are given by their Hessians $H = C + C^{\mathsf T} \in M_n(\mathbb{Z})$ (`QuadForm.hessian`); over
$\mathbb{Z}$ a form is determined by its Hessian, and $X \in M_n(\mathbb{Z})$ represents $Q$ by $Q''$
($Q''(X\vec x) = Q(\vec x)$) iff $X^{\mathsf T} H'' X = H$.

- **D1** ((2.8), p. 34): `card_reps_of_equiv`, `card_reps_of_not_equiv` (for $Q''$ with
  $\det H'' = \det H \ne 0$, e.g. $Q'' \in \mathrm{Gen}(Q)$: $r_{Q''}(Q) = \#\mathrm{Aut}(Q)$ if
  $Q'' \sim Q$ and $0$ otherwise) and `eisenstein_coeff_self` ($a_E(Q) = 1/\mathrm{Mass}(Q)$).
- **D2** (p. 35): `mass_le_half_classNumber`: $\mathrm{Mass}(Q) \le h(Q)/2$.
- **D3** (§2.7.1, p. 36): `measure_span_pow`, `measure_pi_span_pow`: for an additive Haar measure
  on $\mathbb{Z}_p$ (resp. $\mathbb{Z}_p^n$) of total mass $1$, $\mu(p^i\mathbb{Z}_p) = p^{-i}$ and
  $\mu(p^i\mathbb{Z}_p^n) = p^{-ni}$ (via Mathlib's `AddSubgroup.index_mul_measure`).
- **D5** (Lemma 2.7.2, §2.7.3, pp. 37–38): `vol_preimage_div_vol`, `beta_eq_localDensity`: the ratio
  $\mathrm{Vol}(Q^{-1}(m + p^i\mathbb{Z}_p))/\mathrm{Vol}(m + p^i\mathbb{Z}_p)$ is $r_{p^i}(m)/p^{(n-1)i}$, so
  the notes' $\beta_p(m)$ is this repo's `LocalDensity.localDensity`.

*Clarification (candidate; pending author):* p. 34, after (2.8): "the number of representations
$r_Q(Q'')$ of any quadratic form $Q'' \in \mathrm{Gen}(Q)$ by $Q$" — (2.8) uses $r_{Q''}(Q)$, the number of
representations of $Q$ by $Q''$. The two agree here (both are $\#\mathrm{Aut}(Q)$ or $0$), but the
displayed case formula is for $r_{Q''}(Q)$.
-/
import QuadFormsKB.LocalDensity.Basic

open Matrix MeasureTheory

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-! ### D1: representations of $Q$ by forms in its genus -/

/-- **Representations of $Q$ by $Q''$** (Hessians $H$, $H''$): the integral matrices $X$ with
$X^{\mathsf T} H'' X = H$, i.e. $Q''(X\vec x) = Q(\vec x)$. $r_{Q''}(Q)$ is its cardinality. -/
def reps (H H'' : Matrix (Fin n) (Fin n) ℤ) : Set (Matrix (Fin n) (Fin n) ℤ) :=
  {X | Xᵀ * H'' * X = H}

/-- **Isometries** $Q \to Q''$: invertible $X \in \mathrm{GL}_n(\mathbb{Z})$ with $X^{\mathsf T}H''X = H$. -/
def isoms (H H'' : Matrix (Fin n) (Fin n) ℤ) : Set (GL (Fin n) ℤ) := {X | X.valᵀ * H'' * X.val = H}

/-- **The automorphism group** $\mathrm{Aut}(Q) = \{X \in \mathrm{GL}_n(\mathbb{Z}) : X^{\mathsf T}HX = H\}$. -/
def autZ (H : Matrix (Fin n) (Fin n) ℤ) : Set (GL (Fin n) ℤ) := isoms H H

/-- $Q$ and $Q''$ are $\mathbb{Z}$-equivalent: some isometry exists. -/
def EquivZ (H H'' : Matrix (Fin n) (Fin n) ℤ) : Prop := (isoms H H'').Nonempty

/-- **A representation between forms of the same nonzero determinant is invertible:** if
$X^{\mathsf T}H''X = H$ and $\det H'' = \det H \ne 0$ then $\det X = \pm 1$. -/
theorem isUnit_det_of_mem_reps {H H'' : Matrix (Fin n) (Fin n) ℤ} (hdet : H''.det = H.det)
    (h0 : H.det ≠ 0) {X : Matrix (Fin n) (Fin n) ℤ} (hX : X ∈ reps H H'') : IsUnit X.det := by
  have h := congrArg Matrix.det hX
  simp only [det_mul, det_transpose, hdet] at h
  have h2 : X.det * X.det = 1 := by
    have : (X.det * X.det - 1) * H.det = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linear_combination h'
    · exact absurd h' h0
  exact isUnit_iff_exists_inv.mpr ⟨_, h2⟩

/-- With equal nonzero determinants, representations are exactly the isometries. -/
theorem card_reps_eq_card_isoms {H H'' : Matrix (Fin n) (Fin n) ℤ} (hdet : H''.det = H.det)
    (h0 : H.det ≠ 0) : Nat.card (reps H H'') = Nat.card (isoms H H'') := by
  refine (Nat.card_congr ?_).symm
  exact
    { toFun := fun X => ⟨X.1.val, X.2⟩
      invFun := fun X => ⟨Matrix.nonsingInvUnit X.1 (isUnit_det_of_mem_reps hdet h0 X.2), X.2⟩
      left_inv := fun X => by ext1; ext1; rfl
      right_inv := fun X => rfl }

/-- **D1, (2.8), p. 34 (equivalent case):** if $Q'' \sim_\mathbb{Z} Q$ (and so $\det H'' = \det H$),
then $r_{Q''}(Q) = \#\mathrm{Aut}(Q)$: composing a fixed isometry $X_0 : Q \to Q''$ with
$\mathrm{Aut}(Q)$ gives all representations. -/
@[kb "hanke2011aws" "§2.6, p. 34"]
theorem card_reps_of_equiv {H H'' : Matrix (Fin n) (Fin n) ℤ} (h0 : H.det ≠ 0)
    (he : EquivZ H H'') : Nat.card (reps H H'') = Nat.card (autZ H) := by
  obtain ⟨X₀, hX₀⟩ := he
  have hdet : H''.det = H.det := by
    have h := congrArg Matrix.det hX₀
    simp only [det_mul, det_transpose] at h
    have hu : IsUnit (X₀.val.det) := (Matrix.isUnit_iff_isUnit_det _).mp X₀.isUnit
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] at h <;> linear_combination h
  rw [card_reps_eq_card_isoms hdet h0]
  refine Nat.card_congr
    { toFun := fun X => ⟨X₀⁻¹ * X.1, ?_⟩
      invFun := fun A => ⟨X₀ * A.1, ?_⟩
      left_inv := fun X => by ext1; simp
      right_inv := fun A => by ext1; simp }
  · -- (X₀⁻¹ X)ᵀ H (X₀⁻¹ X) = H
    obtain ⟨X, hX⟩ := X
    show (X₀⁻¹ * X).valᵀ * H * (X₀⁻¹ * X).val = H
    change X.valᵀ * H'' * X.val = H at hX
    have hH'' : H'' = X₀⁻¹.valᵀ * H * X₀⁻¹.val := by
      rw [← hX₀]
      simp only [← Matrix.mul_assoc, ← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        transpose_one, Matrix.one_mul]
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hH''] at hX
    rw [Units.val_mul, transpose_mul]
    calc (X.val)ᵀ * (X₀⁻¹.val)ᵀ * H * (X₀⁻¹.val * X.val)
        = X.valᵀ * (X₀⁻¹.valᵀ * H * X₀⁻¹.val) * X.val := by simp only [Matrix.mul_assoc]
      _ = H := hX
  · show (X₀ * A.1).valᵀ * H'' * (X₀ * A.1).val = H
    have hA := A.2
    change A.1.valᵀ * H * A.1.val = H at hA
    rw [Units.val_mul, transpose_mul]
    calc A.1.valᵀ * X₀.valᵀ * H'' * (X₀.val * A.1.val)
        = A.1.valᵀ * (X₀.valᵀ * H'' * X₀.val) * A.1.val := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hX₀, hA]

/-- **D1, (2.8), p. 34 (inequivalent case):** if $\det H'' = \det H \ne 0$ (as for $Q'' \in \mathrm{Gen}(Q)$)
and $Q'' \not\sim_\mathbb{Z} Q$, then $r_{Q''}(Q) = 0$. -/
@[kb "hanke2011aws" "§2.6, p. 34"]
theorem card_reps_of_not_equiv {H H'' : Matrix (Fin n) (Fin n) ℤ} (hdet : H''.det = H.det)
    (h0 : H.det ≠ 0) (hne : ¬ EquivZ H H'') : Nat.card (reps H H'') = 0 := by
  rw [card_reps_eq_card_isoms hdet h0]
  have : isoms H H'' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  rw [this]; simp

/-- **The mass** $\mathrm{Mass}(Q) = \sum_{Q'' \in \mathrm{Gen}(Q)} 1/|\mathrm{Aut}(Q'')|$ (§2.6, p. 34), for a
finite family $(H_i)_{i \in \iota}$ of representatives of the classes in the genus. (The value at an
infinite automorphism group would be $1/0 = 0$; for positive definite forms all $\mathrm{Aut}$ are
finite.) -/
@[kb "hanke2011aws" "§2.6, p. 34"]
noncomputable def mass {ι : Type*} [Fintype ι] (H : ι → Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  ∑ i, ((Nat.card (autZ (H i)) : ℝ))⁻¹

/-- **D1, (2.8), p. 34: the Siegel–Eisenstein coefficient at $Q$ itself is $1/\mathrm{Mass}(Q)$.**
Let $(H_i)_{i\in\iota}$ be pairwise inequivalent forms of the same nonzero determinant (representatives
of the classes in $\mathrm{Gen}(Q)$), with finite automorphism groups, and $H = H_{i_0}$. Then
$$a_E(Q) := \frac{\sum_i r_{Q_i}(Q)/|\mathrm{Aut}(Q_i)|}{\sum_i 1/|\mathrm{Aut}(Q_i)|} = \frac{1}{\mathrm{Mass}(Q)}.$$ -/
@[kb "hanke2011aws" "§2.6, (2.8), p. 34"]
theorem eisenstein_coeff_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Matrix (Fin n) (Fin n) ℤ) (i₀ : ι) (h0 : (H i₀).det ≠ 0)
    (hdet : ∀ i, (H i).det = (H i₀).det) (hineq : ∀ i, EquivZ (H i₀) (H i) → i = i₀)
    (hfin : ∀ i, Finite (autZ (H i))) :
    (∑ i, (Nat.card (reps (H i₀) (H i)) : ℝ) / Nat.card (autZ (H i))) / mass H = 1 / mass H := by
  congr 1
  rw [Finset.sum_eq_single i₀]
  · rw [card_reps_of_equiv h0 ⟨1, by simp [isoms]⟩]
    have : (Nat.card (autZ (H i₀)) : ℝ) ≠ 0 := by
      have := hfin i₀
      have h1 : (1 : GL (Fin n) ℤ) ∈ autZ (H i₀) := by simp [autZ, isoms]
      have hne : Nonempty (autZ (H i₀)) := ⟨⟨1, h1⟩⟩
      exact_mod_cast (Nat.card_pos (α := autZ (H i₀))).ne'
    exact div_self this
  · intro i _ hi
    rw [card_reps_of_not_equiv (hdet i) h0 (fun he => hi (hineq i he))]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### D2: $\mathrm{Mass}(Q) \le h(Q)/2$ -/

/-- $\pm 1$ are automorphisms, and they are distinct for $n \ge 1$, so $\#\mathrm{Aut}(Q) \ge 2$ when
$\mathrm{Aut}(Q)$ is finite. -/
theorem two_le_card_autZ (hn : 0 < n) (H : Matrix (Fin n) (Fin n) ℤ) [Finite (autZ H)] :
    2 ≤ Nat.card (autZ H) := by
  have h1 : (1 : GL (Fin n) ℤ) ∈ autZ H := by simp [autZ, isoms]
  have h2 : (-1 : GL (Fin n) ℤ) ∈ autZ H := by simp [autZ, isoms]
  have hne : (1 : GL (Fin n) ℤ) ≠ -1 := by
    intro h
    have := congrArg (fun g : GL (Fin n) ℤ => g.val ⟨0, hn⟩ ⟨0, hn⟩) h
    simp at this
  have : ({⟨1, h1⟩, ⟨-1, h2⟩} : Set (autZ H)).ncard = 2 :=
    Set.ncard_pair (fun h => hne (congrArg Subtype.val h))
  rw [← this]
  exact Set.ncard_le_card _

/-- **D2 (p. 35): $\mathrm{Mass}(Q) \le h(Q)/2$** ("using the fact that every quadratic form has at
least two automorphisms (e.g. $\vec x \mapsto \pm\vec x$)"), for $n \ge 1$; $h(Q) = |\iota|$ is the number
of classes. (No finiteness hypothesis is needed: an infinite $\mathrm{Aut}$ contributes $0$.) -/
@[kb "hanke2011aws" "§2.6, p. 35"]
theorem mass_le_half_classNumber (hn : 0 < n) {ι : Type*} [Fintype ι]
    (H : ι → Matrix (Fin n) (Fin n) ℤ) : mass H ≤ (Fintype.card ι : ℝ) / 2 := by
  unfold mass
  have : ∀ i, ((Nat.card (autZ (H i)) : ℝ))⁻¹ ≤ 1 / 2 := by
    intro i
    by_cases hfin : Finite (autZ (H i))
    · have h2 : (2 : ℝ) ≤ Nat.card (autZ (H i)) := by exact_mod_cast two_le_card_autZ hn (H i)
      rw [one_div]
      exact inv_anti₀ (by norm_num) h2
    · have : Infinite (autZ (H i)) := not_finite_iff_infinite.mp hfin
      rw [Nat.card_eq_zero_of_infinite]
      norm_num
  calc ∑ i, ((Nat.card (autZ (H i)) : ℝ))⁻¹ ≤ ∑ _i : ι, (1 / 2 : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = (Fintype.card ι : ℝ) / 2 := by simp [div_eq_mul_inv]

/-! ### D3: canonical measures on $\mathbb{Z}_p$ and $\mathbb{Z}_p^n$ (§2.7.1) -/

section padic

variable (p : ℕ) [Fact p.Prime]

theorem toZModPow_surjective (i : ℕ) : Function.Surjective (PadicInt.toZModPow (p := p) i) := by
  intro a
  refine ⟨((a.val : ℕ) : ℤ_[p]), ?_⟩
  simp

/-- **D3 (§2.7.1, p. 36): $\mu_{\mathbb{Z}_p}(p^i\mathbb{Z}_p) = p^{-i}$** for every additive
(translation-invariant) measure on $\mathbb{Z}_p$ with $\mu(\mathbb{Z}_p) = 1$: $\mathbb{Z}_p$ is the disjoint
union of the $p^i$ cosets $a + p^i\mathbb{Z}_p$, which all have the same measure. -/
@[kb "hanke2011aws" "§2.7.1, p. 36"]
theorem measure_span_pow [MeasurableSpace ℤ_[p]] [MeasurableAdd ℤ_[p]] (μ : Measure ℤ_[p])
    [μ.IsAddLeftInvariant] (hμ : μ Set.univ = 1) (i : ℕ)
    (hmeas : MeasurableSet ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p])) :
    μ ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]) = ((p : ENNReal) ^ i)⁻¹ := by
  let f : ℤ_[p] →+ ZMod (p ^ i) := (PadicInt.toZModPow i).toAddMonoidHom
  have hker : (f.ker : Set ℤ_[p]) = ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    ext x
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, f, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have hidx : f.ker.index = p ^ i := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (toZModPow_surjective p i),
      AddSubgroup.card_top, Nat.card_zmod]
  haveI : f.ker.FiniteIndex := ⟨by rw [hidx]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := AddSubgroup.index_mul_measure f.ker (hker ▸ hmeas) μ
  rw [hidx, hμ, hker] at h
  have h' : ((p : ENNReal) ^ i) * μ ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]) = 1 := by
    exact_mod_cast h
  have hp0 : ((p : ENNReal) ^ i) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hpt : ((p : ENNReal) ^ i) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  rw [← one_div, ENNReal.eq_div_iff hp0 hpt]; exact h'

/-- **D3 (§2.7.1, p. 36): $\mu_{\mathbb{Z}_p^n}(p^i\mathbb{Z}_p^n) = p^{-ni}$** for every additive measure on
$\mathbb{Z}_p^n$ with $\mu(\mathbb{Z}_p^n) = 1$ ("and also $\mu_{\mathbb{Z}_p^n}(p^i\mathbb{Z}_p^n) = \frac{1}{p^{n\cdot i}}$"). -/
@[kb "hanke2011aws" "§2.7.1, p. 36"]
theorem measure_pi_span_pow (n : ℕ) [MeasurableSpace (Fin n → ℤ_[p])] [MeasurableAdd (Fin n → ℤ_[p])]
    (μ : Measure (Fin n → ℤ_[p])) [μ.IsAddLeftInvariant] (hμ : μ Set.univ = 1) (i : ℕ)
    (hmeas : MeasurableSet (Set.univ.pi fun _ : Fin n =>
      ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))) :
    μ (Set.univ.pi fun _ : Fin n => ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p])) =
      ((p : ENNReal) ^ (n * i))⁻¹ := by
  let f : (Fin n → ℤ_[p]) →+ (Fin n → ZMod (p ^ i)) :=
    AddMonoidHom.compLeft (PadicInt.toZModPow i).toAddMonoidHom (Fin n)
  have hker : (f.ker : Set (Fin n → ℤ_[p])) =
      Set.univ.pi fun _ : Fin n => ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    ext x
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, f, Set.mem_pi, Set.mem_univ, true_implies,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, funext_iff, AddMonoidHom.compLeft_apply,
      Function.comp_apply, Pi.zero_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  have hsurj : Function.Surjective f := by
    intro b
    choose a ha using fun j => toZModPow_surjective p i (b j)
    exact ⟨a, funext fun j => ha j⟩
  have hidx : f.ker.index = p ^ (n * i) := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, mul_comm]
  haveI : f.ker.FiniteIndex := ⟨by rw [hidx]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := AddSubgroup.index_mul_measure f.ker (hker ▸ hmeas) μ
  rw [hidx, hμ, hker] at h
  have h' : ((p : ENNReal) ^ (n * i)) *
      μ (Set.univ.pi fun _ : Fin n => ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p])) = 1 := by
    exact_mod_cast h
  have hp0 : ((p : ENNReal) ^ (n * i)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hpt : ((p : ENNReal) ^ (n * i)) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  rw [← one_div, ENNReal.eq_div_iff hp0 hpt]; exact h'

end padic

/-! ### Lemma 2.7.2: the local density as a ratio of volumes -/

open scoped Pointwise

/-- **Volume of a union of fibres:** for a surjective homomorphism $f : A \to C$ onto a finite group and
an additive measure $\mu$, $\mu(f^{-1}(T)) = |T|\,\mu(\ker f)$. -/
theorem measure_preimage_eq_card_mul {A C : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd A]
    [AddGroup C] (f : A →+ C) (hf : Function.Surjective f) (μ : Measure A) [μ.IsAddLeftInvariant]
    (hker : MeasurableSet (f.ker : Set A)) (T : Finset C) :
    μ (f ⁻¹' (T : Set C)) = T.card * μ (f.ker : Set A) := by
  classical
  choose x hx using hf
  have hfib : ∀ c, f ⁻¹' {c} = x c +ᵥ (f.ker : Set A) := by
    intro c
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_vadd_set, SetLike.mem_coe,
      AddMonoidHom.mem_ker, vadd_eq_add]
    constructor
    · intro ha
      exact ⟨-x c + a, by rw [map_add, map_neg, hx, ha, neg_add_cancel], by simp⟩
    · rintro ⟨b, hb, rfl⟩
      rw [map_add, hx, hb, add_zero]
  have hU : f ⁻¹' (T : Set C) = ⋃ c ∈ T, f ⁻¹' {c} := by
    ext a; simp
  rw [hU, measure_biUnion_finset]
  · simp only [hfib, measure_vadd, Finset.sum_const, nsmul_eq_mul]
  · intro c _ d _ hcd
    exact Set.disjoint_left.mpr fun a ha hb => hcd (ha.symm.trans hb)
  · intro c _
    rw [hfib]; exact hker.const_vadd _

/-- Evaluation of an integral form commutes with ring homomorphisms. -/
theorem evalIn_map {n : ℕ} (Q : QuadForm ℤ n) {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (x : Fin n → A) : φ (Q.evalIn A x) = Q.evalIn B (φ ∘ x) := by
  simp only [QuadForm.evalIn, map_sum, Function.comp_apply, eq_intCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

section padic2

variable (p : ℕ) [Fact p.Prime]

/-- **D5: Lemma 2.7.2 (§2.7.3, pp. 37–38), at a finite level.** Let $\mu_1$, $\mu_n$ be additive measures
on $\mathbb{Z}_p$, $\mathbb{Z}_p^n$ of total mass $1$, $U_i = m + p^i\mathbb{Z}_p$. Then
$$\frac{\mathrm{Vol}_{\mathbb{Z}_p^n}(Q^{-1}(U_i))}{\mathrm{Vol}_{\mathbb{Z}_p}(U_i)} =
\frac{\#\{\vec x \in (\mathbb{Z}/p^i)^n : Q(\vec x) \equiv m \pmod{p^i}\}}{p^{(n-1)i}}$$
("each solution $\vec x$ of $Q(\vec x) \equiv m \pmod{p^i}$ gives a $p$-adic coset $\vec x + p^i\mathbb{Z}_p^n$ of
solutions in $Q^{-1}(U_i)$"). The right side is `LocalDensity.repCount`$/p^{i(n-1)}$, so the notes'
$\beta_p(m)$ ((2.7), as the limit of the left side) is this repo's `LocalDensity.localDensity`
(`beta_eq_localDensity`). -/
@[kb "hanke2011aws" "§2.7.3, Lemma 2.7.2, pp. 37-38"]
theorem vol_preimage_div_vol {n : ℕ} (Q : QuadForm ℤ n) (m : ℤ) (i : ℕ) (hn : 1 ≤ n)
    [MeasurableSpace ℤ_[p]] [MeasurableAdd ℤ_[p]] (μ₁ : Measure ℤ_[p]) [μ₁.IsAddLeftInvariant]
    (hμ₁ : μ₁ Set.univ = 1)
    (hmeas₁ : MeasurableSet ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))
    [MeasurableSpace (Fin n → ℤ_[p])] [MeasurableAdd (Fin n → ℤ_[p])]
    (μ : Measure (Fin n → ℤ_[p])) [μ.IsAddLeftInvariant] (hμ : μ Set.univ = 1)
    (hmeas : MeasurableSet (Set.univ.pi fun _ : Fin n =>
      ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))) :
    (μ {x | Q.evalIn ℤ_[p] x - m ∈ (Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p])}).toReal /
      (μ₁ ((m : ℤ_[p]) +ᵥ ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))).toReal =
      (LocalDensity.repCount Q p i m : ℝ) / (p : ℝ) ^ (i * (n - 1)) := by
  classical
  -- the coordinatewise reduction map and its kernel
  let φ : (Fin n → ℤ_[p]) →+ (Fin n → ZMod (p ^ i)) :=
    AddMonoidHom.compLeft (PadicInt.toZModPow i).toAddMonoidHom (Fin n)
  have hker : (φ.ker : Set (Fin n → ℤ_[p])) =
      Set.univ.pi fun _ : Fin n => ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    ext x
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, φ, Set.mem_pi, Set.mem_univ, true_implies,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, funext_iff, AddMonoidHom.compLeft_apply,
      Function.comp_apply, Pi.zero_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
  have hsurj : Function.Surjective φ := by
    intro b
    choose a ha using fun j => toZModPow_surjective p i (b j)
    exact ⟨a, funext fun j => ha j⟩
  -- the solution set mod p^i
  let T : Finset (Fin n → ZMod (p ^ i)) :=
    Finset.univ.filter fun y => Q.evalIn (ZMod (p ^ i)) y = (m : ZMod (p ^ i))
  have hS : {x : Fin n → ℤ_[p] | Q.evalIn ℤ_[p] x - m ∈ (Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p])}
      = φ ⁻¹' (T : Set _) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.coe_filter, Finset.mem_univ, true_and,
      T, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_intCast, sub_eq_zero]
    rw [evalIn_map]
    rfl
  have hT : T.card = LocalDensity.repCount Q p i m := by
    rw [LocalDensity.repCount, ← Nat.card_eq_finsetCard]
    simp [T]
  -- volumes
  have hvol : μ {x | Q.evalIn ℤ_[p] x - m ∈ (Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p])} =
      T.card * ((p : ENNReal) ^ (n * i))⁻¹ := by
    rw [hS, measure_preimage_eq_card_mul φ hsurj μ (hker ▸ hmeas), hker,
      measure_pi_span_pow p n μ hμ i hmeas]
  have hvol₁ : μ₁ ((m : ℤ_[p]) +ᵥ ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p])) =
      ((p : ENNReal) ^ i)⁻¹ := by
    rw [measure_vadd, measure_span_pow p μ₁ hμ₁ i hmeas₁]
  rw [hvol, hvol₁, hT]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [show i * (n - 1) = n * i - i by
    rcases n with _ | n
    · omega
    · rw [Nat.succ_sub_one, Nat.succ_mul]; ring_nf; omega]
  rw [pow_sub₀ _ hp0 (by nlinarith)]
  field_simp

/-- **D5: Lemma 2.7.2 (p. 37): the notes' $\beta_p(m)$ is this repo's local density.** The notes define
$\beta_p(m) = \lim_{U \to \{m\}} \mathrm{Vol}(Q^{-1}(U))/\mathrm{Vol}(U)$ ((2.7)); along $U_i = m + p^i\mathbb{Z}_p$
this is `LocalDensity.localDensity Q p m` $= \lim_i r_{p^i}(m)/p^{(n-1)i}$ (Hanke 2004, (5.1)–(5.2)). -/
@[kb "hanke2011aws" "§2.7.3, Lemma 2.7.2, p. 37"]
theorem beta_eq_localDensity {n : ℕ} (Q : QuadForm ℤ n) (m : ℤ) (hn : 1 ≤ n)
    [MeasurableSpace ℤ_[p]] [MeasurableAdd ℤ_[p]] (μ₁ : Measure ℤ_[p]) [μ₁.IsAddLeftInvariant]
    (hμ₁ : μ₁ Set.univ = 1)
    (hmeas₁ : ∀ i, MeasurableSet ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))
    [MeasurableSpace (Fin n → ℤ_[p])] [MeasurableAdd (Fin n → ℤ_[p])]
    (μ : Measure (Fin n → ℤ_[p])) [μ.IsAddLeftInvariant] (hμ : μ Set.univ = 1)
    (hmeas : ∀ i, MeasurableSet (Set.univ.pi fun _ : Fin n =>
      ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))) :
    Filter.limUnder Filter.atTop (fun i : ℕ =>
      (μ {x | Q.evalIn ℤ_[p] x - m ∈ (Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p])}).toReal /
        (μ₁ ((m : ℤ_[p]) +ᵥ ((Ideal.span {(p : ℤ_[p]) ^ i} : Ideal ℤ_[p]) : Set ℤ_[p]))).toReal) =
      LocalDensity.localDensity Q p m := by
  rw [LocalDensity.localDensity]
  congr 1
  funext i
  exact vol_preimage_div_vol p Q m i hn μ₁ hμ₁ (hmeas₁ i) μ hμ (hmeas i)

end padic2

end QuadFormsKB.AWS
