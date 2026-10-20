/-
# Weight-2 Eisenstein series with characters as modular forms

* `eis2MF`: for a residue weight $W$ of total mass $0$ invariant under $\Gamma_1(N)$, $E_W$ is a Mathlib
  `ModularForm (Gamma1 N) 2` (holomorphy `mdifferentiable_eis2`, transformation `eis2_slash`, boundedness at every
  cusp from `tendsto_eis2_atImInfty` applied to $E_W|\gamma = E_{W\cdot\gamma}$).
* `IsModularFormWithChar χ f`: $f\,|_k\,\gamma = \chi(d)\,f$ for $\gamma \in \Gamma_0(N)$ — the packaging of
  $M_k(\Gamma_0(N), \chi)$ used for theta series (`thetaMFGamma1`, `thetaH_slash_gamma0`) and cusp forms
  (`IsCuspFormWithChar`).
* The **Diamond–Shurman weight** (§4.5–4.6): for Dirichlet characters $\psi$ mod $u$, $\varphi$ mod $v$ and $t \ge 1$
  with $uvt \mid N$,
  $$w^{\psi,\varphi}_t(c, d) = \mathbf{1}_{vt \mid c}\;\psi\!\Big(\frac{c}{vt}\Big)\,\bar\varphi(d),$$
  so that $E_{w} = \sum_{c,d}\psi(c)\bar\varphi(d)(cvtz + d)^{-2} = G_2^{\psi,\varphi}(tz)$.  Its total mass vanishes
  unless $\psi = \varphi = 1$ (`totalSum_dsW`), and for $\gamma \in \Gamma_0(N)$ it transforms by
  $(\psi\varphi)(\gamma_{11})$ (`slashW_dsW`).  Hence `dsEisMF ψ φ t` $\in M_2(\Gamma_0(N), \psi\varphi)$
  (`isModularFormWithChar_dsEisMF`), for $\psi \ne 1$ or $\varphi \ne 1$.
-/
import QuadFormsKB.Siegel.EisensteinWt2.QExp
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import QuadFormsKB.Citation

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups Manifold

namespace QuadFormsKB.Siegel.EisensteinWt2

variable {N : ℕ} [NeZero N]

lemma isBoundedAtImInfty_eis2 (W : ZMod N → ZMod N → ℂ) : UpperHalfPlane.IsBoundedAtImInfty (eis2 W) :=
  (tendsto_eis2_atImInfty W).isBigO_one ℝ

/-- **$f \in M_k(\Gamma_0(N), \chi)$** for a modular form $f$ on $\Gamma_1(N)$: $f\,|_k\,\gamma = \chi(\gamma_{11})\,f$ for every
$\gamma \in \Gamma_0(N)$ (0-based entries). Mathlib has no spaces of modular forms with character; this is the
modular-form analogue of `IsCuspFormWithChar` (`Siegel/EigenformBound.lean`).

Parameters: `χ`, a Dirichlet character modulo $N$; `f`, a Mathlib modular form of weight $k$ for $\Gamma_1(N)$. -/
@[kb "diamondshurman2005" "§4.3 (M_k(N, χ)) [unverified]"]
def IsModularFormWithChar (χ : DirichletCharacter ℂ N) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 N) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
    (⇑f : ℍ → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod N) • (⇑f : ℍ → ℂ)

/-- **$E_W$ as a modular form of weight 2 for $\Gamma_1(N)$**, for $W$ of total mass $0$ with $W\cdot\gamma = W$ for all
$\gamma \in \Gamma_1(N)$. -/
noncomputable def eis2MF (W : ZMod N → ZMod N → ℂ) (hW : totalSum W = 0)
    (hinv : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → slashW W γ = W) :
    ModularForm (CongruenceSubgroup.Gamma1 N) 2 where
  toFun := eis2 W
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    change eis2 W ∣[(2 : ℤ)] γ = eis2 W
    rw [eis2_slash W hW, hinv γ hγ]
  holo' := mdifferentiable_eis2 W
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [eis2_slash W hW]
    exact isBoundedAtImInfty_eis2 _

@[simp] lemma eis2MF_apply (W : ZMod N → ZMod N → ℂ) (hW : totalSum W = 0) (hinv) (z : ℍ) :
    eis2MF W hW hinv z = eis2 W z := rfl

omit [NeZero N] in
lemma eis2_const_mul (a : ℂ) (W : ZMod N → ZMod N → ℂ) :
    eis2 (fun x y => a * W x y) = a • eis2 W := by
  ext z
  simp only [eis2, wt, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  exact tsum_congr fun c => tsum_congr fun d => by ring

/-- A character law for the weight gives the character law for $E_W$. -/
theorem isModularFormWithChar_eis2MF (χ : DirichletCharacter ℂ N) (W : ZMod N → ZMod N → ℂ)
    (hW : totalSum W = 0) (hinv)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      slashW W γ = fun x y => χ ((γ 1 1 : ℤ) : ZMod N) * W x y) :
    IsModularFormWithChar χ (eis2MF W hW hinv) := by
  intro γ hγ
  change eis2 W ∣[(2 : ℤ)] γ = _
  rw [eis2_slash W hW, hχ γ hγ, eis2_const_mul]
  rfl

/-! ### Weights from $N$-periodic functions on $\mathbb{Z}^2$ -/

/-- The residue weight attached to a function $F$ on $\mathbb{Z}^2$ (meaningful when $F$ is $N$-periodic). -/
def ofPer (F : ℤ → ℤ → ℂ) (a b : ZMod N) : ℂ := F a.val b.val

omit [NeZero N] in
lemma per_emod {f : ℤ → ℂ} (hf : ∀ x, f (x + N) = f x) (x : ℤ) : f (x % N) = f x := by
  have hP : Function.Periodic f (N : ℤ) := hf
  have := (hP.int_mul (x / N)) (x % N)
  rw [← this]; congr 1; rw [mul_comm, add_comm]; simp only [Int.cast_id]; exact Int.mul_ediv_add_emod x N

lemma ofPer_intCast {F : ℤ → ℤ → ℂ} (h1 : ∀ c d, F (c + N) d = F c d)
    (h2 : ∀ c d, F c (d + N) = F c d) (x y : ℤ) : ofPer F (x : ZMod N) (y : ZMod N) = F x y := by
  simp only [ofPer]
  rw [show (((x : ZMod N).val : ℕ) : ℤ) = x % N from ZMod.val_intCast x,
    show (((y : ZMod N).val : ℕ) : ℤ) = y % N from ZMod.val_intCast y]
  rw [per_emod (f := fun c => F c (y % N)) (fun c => h1 c _) x,
    per_emod (f := fun d => F x d) (fun d => h2 x d) y]

lemma wt_ofPer {F : ℤ → ℤ → ℂ} (h1 : ∀ c d, F (c + N) d = F c d)
    (h2 : ∀ c d, F c (d + N) = F c d) (c d : ℤ) : wt (ofPer (N := N) F) c d = F c d :=
  ofPer_intCast h1 h2 c d

lemma slashW_ofPer_intCast {F : ℤ → ℤ → ℂ} (h1 : ∀ c d, F (c + N) d = F c d)
    (h2 : ∀ c d, F c (d + N) = F c d) (γ : SL(2, ℤ)) (x y : ℤ) :
    slashW (ofPer F) γ (x : ZMod N) (y : ZMod N) =
      F (x * γ 1 1 - y * γ 1 0) (-(x * γ 0 1) + y * γ 0 0) := by
  rw [slashW, ← ofPer_intCast h1 h2]
  push_cast
  rfl

lemma totalSum_ofPer {F : ℤ → ℤ → ℂ} (h1 : ∀ c d, F (c + N) d = F c d)
    (h2 : ∀ c d, F c (d + N) = F c d) :
    totalSum (ofPer (N := N) F) = ∑ c ∈ Finset.range N, ∑ d ∈ Finset.range N, F c d := by
  rw [totalSum, ← sum_range_zmod (fun a => ∑ b, ofPer F a b)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← sum_range_zmod (fun b => ofPer F ((c : ℤ) : ZMod N) b)]
  exact Finset.sum_congr rfl fun d _ => ofPer_intCast h1 h2 _ _

/-- Splitting $[0, MK)$ into $K$ blocks of length $M$. -/
lemma sum_range_mul_split (h : ℕ → ℂ) (M K : ℕ) :
    ∑ c ∈ Finset.range (M * K), h c = ∑ j ∈ Finset.range K, ∑ r ∈ Finset.range M, h (M * j + r) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sum_range_mul_of_periodic {g : ℕ → ℂ} {p : ℕ} (hg : ∀ x, g (x + p) = g x) (K : ℕ) :
    ∑ c ∈ Finset.range (p * K), g c = K * ∑ r ∈ Finset.range p, g r := by
  rw [sum_range_mul_split]
  have : ∀ j r, g (p * j + r) = g r := by
    intro j r
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, show p * j + p + r = (p * j + r) + p by ring, hg, ih]
  simp [this]

/-! ### The Diamond–Shurman weight $w^{\psi,\varphi}_t$ -/

section DS

variable {u v : ℕ} (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The Diamond–Shurman weight on $\mathbb{Z}^2$:** $F(c, d) = \mathbf{1}_{M \mid c}\,\psi(c/M)\,\bar\varphi(d)$
($M = vt$ in applications; $\bar\varphi = \varphi^{-1}$). -/
noncomputable def dsF (M : ℕ) (c d : ℤ) : ℂ :=
  (if (M : ℤ) ∣ c then ψ ((c / M : ℤ) : ZMod u) else 0) * φ⁻¹ (d : ZMod v)

variable {ψ φ}

lemma dsF_add_left {M : ℕ} (hN : u * M ∣ N) (c d : ℤ) : dsF ψ φ M (c + N) d = dsF ψ φ M c d := by
  obtain ⟨k, hk⟩ := hN
  have hMN : (M : ℤ) ∣ N := ⟨u * k, by rw [hk]; push_cast; ring⟩
  simp only [dsF]
  congr 1
  by_cases hc : (M : ℤ) ∣ c
  · have hc' : (M : ℤ) ∣ c + N := dvd_add hc hMN
    simp only [hc, hc', ↓reduceIte]
    rw [Int.add_ediv_of_dvd_left hc]
    congr 1
    have : ((N : ℤ) / M : ℤ) = u * k := by
      rcases eq_or_ne M 0 with hM | hM
      · subst hM; simp at hk; exact absurd hk (NeZero.ne N)
      · rw [hk]; push_cast
        rw [show (u : ℤ) * M * k = (M : ℤ) * (u * k) by ring, Int.mul_ediv_cancel_left _ (by exact_mod_cast hM)]
    rw [this]; push_cast; simp
  · have hc' : ¬ (M : ℤ) ∣ c + N := fun h => hc (by simpa using dvd_sub h hMN)
    simp only [hc, hc', ↓reduceIte]

omit [NeZero N] in
lemma dsF_add_right {M : ℕ} (hv : v ∣ N) (c d : ℤ) : dsF ψ φ M c (d + N) = dsF ψ φ M c d := by
  simp only [dsF]
  congr 2
  push_cast
  have : ((N : ℕ) : ZMod v) = 0 := (ZMod.natCast_eq_zero_iff N v).mpr hv
  rw [this, add_zero]

/-- **The Diamond–Shurman residue weight** $w^{\psi,\varphi}_t$ on $(\mathbb{Z}/N)^2$. -/
noncomputable def dsW (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v) (t : ℕ) :
    ZMod N → ZMod N → ℂ :=
  ofPer (dsF ψ φ (v * t))

omit [NeZero N] in
lemma isCoprime_of_gamma0 {γ : SL(2, ℤ)} (hγ : (N : ℤ) ∣ γ 1 0) : IsCoprime (γ 1 1) (N : ℤ) := by
  obtain ⟨g, hg⟩ := hγ
  exact ⟨γ 0 0, -(γ 0 1 * g), by linear_combination det_SL γ + γ 0 1 * hg⟩

omit [NeZero N] in
lemma dvd_gamma10_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : (N : ℤ) ∣ γ 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ; exact hγ

omit [NeZero N] in
/-- **The $\Gamma_0(N)$ transformation of the Diamond–Shurman weight**, on integers: for $N \mid \gamma_{10}$,
$F\bigl((c,d)\gamma^{-1}\bigr) = \psi(\gamma_{11})\varphi(\gamma_{11})\,F(c,d)$. -/
lemma dsF_transform {t : ℕ} (hN : u * (v * t) ∣ N) (hN0 : N ≠ 0) (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0)
    (c d : ℤ) :
    dsF ψ φ (v * t) (c * γ 1 1 - d * γ 1 0) (-(c * γ 0 1) + d * γ 0 0) =
      ψ ((γ 1 1 : ℤ) : ZMod u) * φ ((γ 1 1 : ℤ) : ZMod v) * dsF ψ φ (v * t) c d := by
  set M := v * t with hMdef
  have hdet := det_SL γ
  have hM0 : M ≠ 0 := by
    rintro h; rw [h, mul_zero, zero_dvd_iff] at hN; exact hN0 hN
  obtain ⟨g, hg⟩ : ((u * M : ℕ) : ℤ) ∣ γ 1 0 := dvd_trans (by exact_mod_cast hN) hγ
  push_cast at hg
  by_cases hc : (M : ℤ) ∣ c
  · obtain ⟨c', rfl⟩ := hc
    have hX : (M : ℤ) * c' * γ 1 1 - d * γ 1 0 = M * (c' * γ 1 1 - d * (u * g)) := by
      rw [hg]; ring
    have hXd : (M : ℤ) ∣ (M : ℤ) * c' * γ 1 1 - d * γ 1 0 := ⟨_, hX⟩
    have hMc : (M : ℤ) ∣ (M : ℤ) * c' := dvd_mul_right _ _
    simp only [dsF, hXd, hMc, ↓reduceIte]
    rw [hX, Int.mul_ediv_cancel_left _ (by exact_mod_cast hM0),
      Int.mul_ediv_cancel_left _ (by exact_mod_cast hM0)]
    have hvM : ((M : ℤ) : ZMod v) = 0 := by
      rw [hMdef]; push_cast; simp
    have hv10 : ((γ 1 0 : ℤ) : ZMod v) = 0 := by
      rw [hg, hMdef]; push_cast; simp
    have hunit : ((γ 0 0 : ℤ) : ZMod v) * ((γ 1 1 : ℤ) : ZMod v) = 1 := by
      have := congr_arg (Int.cast : ℤ → ZMod v) hdet
      push_cast at this; rw [hv10, mul_zero, sub_zero] at this; exact this
    have hφ : φ⁻¹ ((γ 0 0 : ℤ) : ZMod v) = φ ((γ 1 1 : ℤ) : ZMod v) := by
      rw [MulChar.inv_apply_eq_inv']
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, hunit, map_one]
    have h1 : ((c' * γ 1 1 - d * (u * g) : ℤ) : ZMod u) = (c' : ZMod u) * ((γ 1 1 : ℤ) : ZMod u) := by
      push_cast; simp
    have h2 : ((-((M : ℤ) * c' * γ 0 1) + d * γ 0 0 : ℤ) : ZMod v) =
        (d : ZMod v) * ((γ 0 0 : ℤ) : ZMod v) := by
      push_cast; rw [show ((M : ℕ) : ZMod v) = 0 by exact_mod_cast hvM]; ring
    rw [h1, h2, map_mul, map_mul, hφ]
    ring
  · have hX : ¬ (M : ℤ) ∣ c * γ 1 1 - d * γ 1 0 := by
      intro h
      apply hc
      have h1 : (M : ℤ) ∣ c * γ 1 1 := by
        have : (M : ℤ) ∣ d * γ 1 0 := ⟨d * (u * g), by rw [hg]; ring⟩
        simpa using dvd_add h this
      have h2 : (M : ℤ) ∣ c * γ 1 1 * γ 0 0 - c * γ 0 1 * γ 1 0 :=
        dvd_sub (dvd_mul_of_dvd_left h1 _) ⟨c * γ 0 1 * (u * g), by rw [hg]; ring⟩
      have : c * γ 1 1 * γ 0 0 - c * γ 0 1 * γ 1 0 = c := by linear_combination c * hdet
      rwa [this] at h2
    simp only [dsF, hX, hc, ↓reduceIte, zero_mul, mul_zero]

/-- The character $\chi = \psi\varphi$ as a Dirichlet character modulo $N$. -/
noncomputable def dsChar (hu : u ∣ N) (hv : v ∣ N) : DirichletCharacter ℂ N :=
  DirichletCharacter.changeLevel hu ψ * DirichletCharacter.changeLevel hv φ

omit [NeZero N] in
lemma dsChar_intCast (hu : u ∣ N) (hv : v ∣ N) {a : ℤ} (ha : IsCoprime a N) :
    dsChar (ψ := ψ) (φ := φ) hu hv (a : ZMod N) = ψ (a : ZMod u) * φ (a : ZMod v) := by
  rw [dsChar, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hu ha,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hv ha]

omit [NeZero N] in
lemma dvd_of_dvd_mul3 {t : ℕ} (hN : u * (v * t) ∣ N) : u ∣ N ∧ v ∣ N :=
  ⟨dvd_trans (dvd_mul_right _ _) hN, dvd_trans (dvd_trans (dvd_mul_right _ _) (dvd_mul_left _ _)) hN⟩

/-- **The weight $w^{\psi,\varphi}_t$ transforms under $\Gamma_0(N)$ by $\chi = \psi\varphi$.** -/
theorem slashW_dsW {t : ℕ} (hN : u * (v * t) ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    slashW (dsW (N := N) ψ φ t) γ = fun x y =>
      dsChar (ψ := ψ) (φ := φ) (dvd_of_dvd_mul3 hN).1 (dvd_of_dvd_mul3 hN).2 ((γ 1 1 : ℤ) : ZMod N) *
        dsW ψ φ t x y := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have h10 := dvd_gamma10_of_mem hγ
  ext x y
  obtain ⟨c, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨d, rfl⟩ := ZMod.intCast_surjective y
  have h1 := fun c d => dsF_add_left (ψ := ψ) (φ := φ) (N := N) (M := v * t)
    (by rw [← mul_assoc] at hN ⊢; exact hN) c d
  have h2 := fun c d => dsF_add_right (ψ := ψ) (φ := φ) (N := N) (M := v * t) (dvd_of_dvd_mul3 hN).2 c d
  rw [dsW, slashW_ofPer_intCast h1 h2, ofPer_intCast h1 h2, dsF_transform hN hN0 γ h10,
    dsChar_intCast _ _ (isCoprime_of_gamma0 h10)]

/-- The total mass of $w^{\psi,\varphi}_t$ vanishes unless $\psi$ and $\varphi$ are both trivial. -/
theorem totalSum_dsW {t : ℕ} (hN : u * (v * t) ∣ N) (hne : ψ ≠ 1 ∨ φ ≠ 1) :
    totalSum (dsW (N := N) ψ φ t) = 0 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set M := v * t with hMdef
  have h1 := fun c d => dsF_add_left (ψ := ψ) (φ := φ) (N := N) (M := M)
    (by rw [← mul_assoc] at hN ⊢; exact hN) c d
  have h2 := fun c d => dsF_add_right (ψ := ψ) (φ := φ) (N := N) (M := M) (dvd_of_dvd_mul3 hN).2 c d
  rw [dsW, totalSum_ofPer h1 h2]
  simp only [dsF]
  rw [← Finset.sum_mul_sum]
  obtain ⟨k, hk⟩ := hN
  have hu0 : u ≠ 0 := by rintro rfl; apply hN0; rw [hk]; simp
  have hM0 : M ≠ 0 := by intro h; apply hN0; rw [hk, h]; simp
  have hv0 : v ≠ 0 := by rintro rfl; apply hM0; rw [hMdef]; simp
  have : NeZero u := ⟨hu0⟩
  have : NeZero v := ⟨hv0⟩
  rw [mul_eq_zero]
  rcases hne with hψ | hφ
  · -- the ψ-sum vanishes
    left
    have hsplit : N = M * (u * k) := by rw [hk]; ring
    rw [hsplit, sum_range_mul_split]
    have hinner : ∀ j : ℕ, ∑ r ∈ Finset.range M,
        (if (M : ℤ) ∣ ((M * j + r : ℕ) : ℤ) then ψ ((((M * j + r : ℕ) : ℤ) / M : ℤ) : ZMod u) else 0) =
        ψ (j : ZMod u) := by
      intro j
      rw [Finset.sum_eq_single 0]
      · simp only [add_zero, Nat.cast_mul, dvd_mul_right, ↓reduceIte]
        rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hM0)]; simp
      · intro r hr hr0
        have : ¬ (M : ℤ) ∣ ((M * j + r : ℕ) : ℤ) := by
          intro h
          have h' : (M : ℤ) ∣ (r : ℤ) := by
            have := dvd_sub h (dvd_mul_right (M : ℤ) (j : ℤ)); push_cast at this; simpa using this
          have := Int.le_of_dvd (by exact_mod_cast Nat.pos_of_ne_zero hr0) h'
          have := Finset.mem_range.mp hr
          omega
        push_cast at this
        simp [this]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero hM0)) h
    simp_rw [hinner]
    rw [sum_range_mul_of_periodic (g := fun j => ψ (j : ZMod u)) (fun x => by simp) k]
    rw [show ∑ r ∈ Finset.range u, ψ (r : ZMod u) = ∑ r ∈ Finset.range u, ψ ((r : ℤ) : ZMod u) by simp,
      sum_range_zmod (N := u) ψ, MulChar.sum_eq_zero_of_ne_one hψ, mul_zero]
  · right
    have hsplit : N = v * (u * t * k) := by rw [hk]; ring
    rw [hsplit, sum_range_mul_of_periodic (g := fun d => φ⁻¹ (((d : ℕ) : ℤ) : ZMod v))
      (fun x => by push_cast; simp) _]
    rw [sum_range_zmod (N := v) (fun b => φ⁻¹ b), MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hφ),
      mul_zero]

lemma dsF_periodic {t : ℕ} (hN : u * (v * t) ∣ N) :
    (∀ c d, dsF ψ φ (v * t) (c + N) d = dsF ψ φ (v * t) c d) ∧
      (∀ c d, dsF ψ φ (v * t) c (d + N) = dsF ψ φ (v * t) c d) :=
  ⟨fun c d => dsF_add_left (N := N) (by rw [← mul_assoc] at hN ⊢; exact hN) c d,
    fun c d => dsF_add_right (N := N) (dvd_of_dvd_mul3 hN).2 c d⟩

/-- **$E_2^{\psi,\varphi,t}$** (Diamond–Shurman's $G_2^{\psi,\varphi}(tz)$, unnormalized) **as a modular form of weight 2 for
$\Gamma_1(N)$**, for Dirichlet characters $\psi$ mod $u$, $\varphi$ mod $v$, not both trivial, and $uvt \mid N$:
$$E_2^{\psi,\varphi,t}(z) = \sum_{c \in \mathbb{Z}}\sum_{d \in \mathbb{Z}}\mathbf{1}_{vt \mid c}\,\psi\Big(\frac{c}{vt}\Big)
  \bar\varphi(d)\,(cz+d)^{-2}$$
(iterated sum; `dsEisMF_apply`). Its $\Gamma_0(N)$ law is `isModularFormWithChar_dsEisMF`. -/
@[kb "diamondshurman2005" "§4.6, Thm 4.6.2 (weight 2, ψ, φ not both trivial) [unverified]"]
noncomputable def dsEisMF (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v) (t : ℕ)
    (hN : u * (v * t) ∣ N) (hne : ψ ≠ 1 ∨ φ ≠ 1) : ModularForm (CongruenceSubgroup.Gamma1 N) 2 :=
  eis2MF (dsW ψ φ t) (totalSum_dsW hN hne) fun γ hγ => by
    obtain ⟨_, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma0_mem.mpr h10
    rw [slashW_dsW hN hγ0]
    ext x y
    rw [show ((γ 1 1 : ℤ) : ZMod N) = 1 from h11, map_one, one_mul]

theorem dsEisMF_apply {t : ℕ} (hN : u * (v * t) ∣ N) (hne : ψ ≠ 1 ∨ φ ≠ 1) (z : ℍ) :
    dsEisMF ψ φ t hN hne z = ∑' c : ℤ, ∑' d : ℤ, dsF ψ φ (v * t) c d * (((c : ℂ) * z + d) ^ 2)⁻¹ := by
  change eis2 (dsW ψ φ t) z = _
  simp only [eis2, dsW, wt_ofPer (dsF_periodic hN).1 (dsF_periodic hN).2]

/-- **$E_2^{\psi,\varphi,t} \in M_2(\Gamma_0(N), \psi\varphi)$:** for $\gamma \in \Gamma_0(N)$,
$E_2^{\psi,\varphi,t}\,|_2\,\gamma = (\psi\varphi)(\gamma_{11})\,E_2^{\psi,\varphi,t}$. -/
@[kb "diamondshurman2005" "§4.6, Thm 4.6.2 [unverified]"]
theorem isModularFormWithChar_dsEisMF {t : ℕ} (hN : u * (v * t) ∣ N) (hne : ψ ≠ 1 ∨ φ ≠ 1) :
    IsModularFormWithChar (dsChar (ψ := ψ) (φ := φ) (dvd_of_dvd_mul3 hN).1 (dvd_of_dvd_mul3 hN).2)
      (dsEisMF ψ φ t hN hne) :=
  isModularFormWithChar_eis2MF _ _ _ _ fun _ hγ => slashW_dsW hN hγ

end DS

end QuadFormsKB.Siegel.EisensteinWt2
