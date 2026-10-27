import QuadFormsKB.LocalDensity.DVRDyadic
import QuadFormsKB.LocalDensity.BridgeExplicit
import QuadFormsKB.LocalDensity.NFDepth
import QuadFormsKB.Siegel.LocalProduct
import QuadFormsKB.Binary.GenusAverage

/-!
# Local densities of binary forms

For a primitive binary form $f = ax^2 + bxy + cy^2$ of fundamental discriminant $D$ (any sign), a prime $p$ and
$m \ne 0$, the repo's local density $\beta_p(m) = \lim_k r_{p^k}(m)/p^{k}$ (`LocalDensity.localDensity`, $n = 2$) is:

* **$p \nmid D$** (`localDensity_good_binary`, $p = 2$ included): with $\chi = \chi_D(p) = \pm 1$ (`kronZ D p`),
  $$\beta_p(m) = \Big(1 - \frac{\chi}{p}\Big)\sum_{j=0}^{v_p(m)}\chi^j \quad (\texttt{goodFactor}).$$
* **$p \mid D$, $p \nmid m$** (`localDensity_ram_unit`, $p = 2$ included): with Gauss's genus characters
  $\chi_p(f)$ = `formChar f p` and $\psi_p$ = `genusChar D p` (D3),
  $$\beta_p(m) = 1 + \chi_p(f)\,\psi_p(m) \in \{0, 2\}.$$

**Method (local counting).** Two Hensel counts, valid for every integral form (`QuadForm ℤ n`), proved from the
DVR layer's general lifting lemma `DVR.countG_add` over $\mathbb{Z}_p$:
* `LocalDensity.repCount_unit_add`: for $p \nmid m$, $r_{p^{k+l}}(m) = p^{(n-1)l}r_{p^k}(m)$ from $k \ge 2\,\mathrm{ord}_p(2) + 1$
  (at a unit value $(H\vec x)\cdot\vec x = 2Q(\vec x)$ bounds the gradient valuation by $\mathrm{ord}_p 2$);
* `LocalDensity.repCountOf_nonZero_add_of_det`: for $p \nmid \det H$, the non-Zero-type counts lift from $k = 1$
  ($\operatorname{adj}(H)H\vec x = \det(H)\vec x$).
Then the counts mod $p$ (or mod $8$): for $p \nmid D$ odd from the diagonalization `Siegel.exists_diag_unimodular_same_counts_det`
and Table 1 (`card_diag_mod_p`); for $p = 2 \nmid D$ by a check over $\mathbb{F}_2$; for odd $p \mid D$ by the substitution
$4a f = (2ax + by)^2 - Dy^2 \equiv (2ax+by)^2$ (`repCount_one_ram`); for $p = 2 \mid D$ by $a f = (ax + b'y)^2 - \frac D4 y^2$ and a
check over $(\mathbb{Z}/8)^2$ (`repCount_three_two`). The Zero-type recursion $r^{\mathrm{Zero}}_{p^k}(m) = p^2 r_{p^{k-2}}(m/p^2)$
(`repCountZero_eq`, Hanke 2004 p. 359) gives $\beta_p(p^2m') = \beta_p(m') + (1 - \frac1p)(1 + \chi)$ at $p \nmid D$
(`eventually_repCount_good`).

$\beta_p(m)$ for $p \mid \gcd(m, D)$ is in `BinaryDensitiesRam.lean` (`localDensity_ram`: again $0$ or $2$).

Indices are 0-based (`Fin 2`: $v_0, v_1$). Sources: Siegel (1935), §§1–2 (the densities $\alpha_p$) [unverified locator];
Yang (1998), explicit local densities [unverified locator]; Hanke (2004), Lemma 3.2, p. 358, and the map $\pi_Z$,
p. 359; Cox, §3.B (genus characters) [unverified locator].
-/

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- $Q(s\vec y) = s^2 Q(\vec y)$ over $R$. -/
theorem eval_smul' (Q : QuadForm R n) (s : R) (y : Fin n → R) : Q.eval (s • y) = s ^ 2 * Q.eval y := by
  have h := eval_add_smul' Q 0 y s
  have h0 : Q.eval 0 = 0 := by simp [QuadForm.evalIn]
  rw [zero_add, h0, mulVec_zero, zero_dotProduct, mul_zero, zero_add, zero_add] at h
  exact h

/-- $(H\vec x)\cdot\vec x = 2Q(\vec x)$. -/
theorem hessian_dot_self (Q : QuadForm R n) (x : Fin n → R) :
    (Q.hessian *ᵥ x) ⬝ᵥ x = 2 * Q.eval x := by
  have h := eval_add_smul' Q x x 1
  have h2 : x + (1 : R) • x = (2 : R) • x := by ext i; simp; ring
  rw [h2, eval_smul'] at h
  linear_combination -h

/-- The vectors with unit value, $G = \{\vec x : \pi \nmid Q(\vec x)\}$, are stable under $\pi R^n$-shifts. -/
theorem unitValue_add (Q : QuadForm R n) (π : R) (x y : Fin n → R) (hx : ¬ π ∣ Q.eval x) :
    ¬ π ∣ Q.eval (x + π • y) := by
  intro h
  apply hx
  rw [eval_add_smul'] at h
  have : Q.eval x = (Q.eval x + π * ((Q.hessian *ᵥ x) ⬝ᵥ y) + π ^ 2 * Q.eval y) -
      π * ((Q.hessian *ᵥ x) ⬝ᵥ y + π * Q.eval y) := by ring
  rw [this]
  exact dvd_sub h (dvd_mul_right _ _)

/-- **Gradient bound at unit values:** if $\pi^e \,\|\, 2$ and $\pi \nmid Q(\vec x)$, some entry of $H\vec x$ is not
divisible by $\pi^{e+1}$ (since $(H\vec x)\cdot\vec x = 2Q(\vec x)$). -/
theorem exists_hessian_not_dvd_of_unit (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (x : Fin n → R) (hx : ¬ π ∣ Q.eval x) :
    ∃ j, ¬ π ^ (e + 1) ∣ (Q.hessian *ᵥ x) j := by
  by_contra hall
  push Not at hall
  have h1 : π ^ (e + 1) ∣ 2 * Q.eval x := by
    rw [← hessian_dot_self]
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (hall j) _
  obtain ⟨u, hu⟩ := he.1
  have hu' : ¬ π ∣ u := by
    rintro ⟨v, rfl⟩
    exact he.2 ⟨v, by rw [hu]; ring⟩
  rw [hu, pow_succ, mul_assoc] at h1
  have hπ0 : π ^ e ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have h2 : π ∣ u * Q.eval x := (mul_dvd_mul_iff_left hπ0).mp h1
  rcases hπ.prime.dvd_or_dvd h2 with h | h
  · exact hu' h
  · exact hx h

/-- **Gradient bound for primitive vectors when $\det H$ is a unit:** if $\pi \nmid \det H$ and some
$x_i$ is a unit, then some entry of $H\vec x$ is a unit ($\operatorname{adj}(H)H\vec x = \det(H)\vec x$). -/
theorem exists_hessian_not_dvd_of_det (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (hdet : ¬ π ∣ Q.hessian.det) (x : Fin n → R) (hx : GoodR Finset.univ π x) :
    ∃ j, ¬ π ^ (0 + 1) ∣ (Q.hessian *ᵥ x) j := by
  by_contra hall
  push Not at hall
  obtain ⟨i, -, hi⟩ := hx
  apply hi
  have h1 : π ∣ (Q.hessian.adjugate *ᵥ (Q.hessian *ᵥ x)) i := by
    show π ∣ ∑ j, Q.hessian.adjugate i j * (Q.hessian *ᵥ x) j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (by simpa using hall j) _
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul] at h1
  exact (hπ.prime.dvd_or_dvd h1).resolve_left hdet

/-- For $\pi \nmid m$ and $K \ge 1$: $r_{\pi^K}(m)$ is the count `countG` over $G = \{\pi \nmid Q(\vec x)\}$. -/
theorem repCount_eq_countG_unit (Q : QuadForm R n) (π : R) (m : R) (hm : ¬ π ∣ m) (K : ℕ) (hK : 1 ≤ K) :
    repCount Q π K m = countG Q π (fun x => ¬ π ∣ Q.eval x) m K := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have hev : Q.evalIn (R ⧸ Ideal.span {π ^ K}) x = Ideal.Quotient.mk _ (Q.eval (liftV π K x)) := by
    conv_lhs => rw [← redV_liftV π K x]
    exact evalIn_redV Q π K _
  rw [hev, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · intro h
    refine ⟨h, fun h' => hm ?_⟩
    have : m = Q.eval (liftV π K x) - (Q.eval (liftV π K x) - m) := by ring
    rw [this]
    exact dvd_sub h' ((dvd_pow_self π (by omega)).trans h)
  · exact fun h => h.1

/-- **Unit values lift from level $2e + 1$** ($\pi^e \,\|\, 2$, any $Q$): for $\pi \nmid m$ and $k \ge 2e+1$,
$r_{\pi^{k+l}}(m) = q^{(n-1)l}\,r_{\pi^k}(m)$. -/
theorem repCount_unit_add (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (m : R) (hm : ¬ π ∣ m) (k l : ℕ) (hk : 2 * e + 1 ≤ k) :
    repCount Q π (k + l) m = q R ^ ((n - 1) * l) * repCount Q π k m := by
  rw [repCount_eq_countG_unit Q π m hm _ (by omega), repCount_eq_countG_unit Q π m hm _ (by omega)]
  exact countG_add Q π hπ _ (unitValue_add Q π) e (exists_hessian_not_dvd_of_unit Q π hπ e he) m k l hk

/-- **Non-Zero-type solutions lift from level $1$ when $\pi \nmid \det H$:** for $k \ge 1$,
$r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^{k+l}}(m) = q^{(n-1)l}\,r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m)$. -/
theorem repCountOf_nonZero_add_of_det (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (hdet : ¬ π ∣ Q.hessian.det) (m : R) (k l : ℕ) (hk : 1 ≤ k) :
    repCountOf Q π (k + l) m (fun x => ¬ IsZeroType π (k + l) x) =
      q R ^ ((n - 1) * l) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  have hT : ∀ K, (fun x => ¬ IsZeroType π K x) = IsGoodType (Finset.univ : Finset (Fin n)) π K := by
    intro K; funext x
    simp only [IsGoodType, IsZeroType, Finset.mem_univ, true_and, not_forall]
    exact propext ⟨fun h => ⟨h, h⟩, fun h => h.2⟩
  rw [hT, hT, repCountOf_good_eq Q _ π _ (by omega), repCountOf_good_eq Q _ π _ hk]
  exact countG_add Q π hπ (GoodR Finset.univ π) (goodR_add_pi _ π) 0
    (exists_hessian_not_dvd_of_det Q π hπ hdet) m k l (by omega)

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- $\mathrm{ord}_p(2)$ as a natural number: $1$ for $p = 2$, else $0$. -/
def eTwo (p : ℕ) : ℕ := if p = 2 then 1 else 0

theorem not_padic_dvd_of_not_dvd {p : ℕ} [Fact p.Prime] {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) :
    ¬ (p : ℤ_[p]) ∣ (m : ℤ_[p]) := fun h => hm (Binary.int_dvd_of_padic_dvd h)

/-- **Unit values lift from level $2\,\mathrm{ord}_p(2) + 1$, over $\mathbb{Z}$** (any form): for $p \nmid m$ and
$k \ge 2e + 1$ ($e = 1$ for $p = 2$, else $0$), $r_{p^{k+l}}(m) = p^{(n-1)l}r_{p^k}(m)$. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358 (unit values, level 2·ord_p 2 + 1)"]
theorem repCount_unit_add (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : ¬ (p : ℤ) ∣ m)
    (k l : ℕ) (hk : 2 * eTwo p + 1 ≤ k) :
    repCount Q p (k + l) m = p ^ ((n - 1) * l) * repCount Q p k m := by
  rw [(repCount_eq_padic Q p ∅ (k + l) m).1, (repCount_eq_padic Q p ∅ k m).1,
    DVR.repCount_unit_add _ _ PadicInt.irreducible_p _ (padicInt_pow_dvd_two p) _
      (not_padic_dvd_of_not_dvd hm) k l hk, q_padicInt]

/-- **Non-Zero-type solutions lift from level $1$ when $p \nmid \det H$, over $\mathbb{Z}$.** -/
@[kb "hanke2004" "Lemma 3.2, p. 358; proof, p. 359 (k = 1 when p ∤ det H)"]
theorem repCountOf_nonZero_add_of_det (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (m : ℤ) (k l : ℕ) (hk : 1 ≤ k) :
    repCountOf Q p (k + l) m (fun x => ¬ IsZeroType p (k + l) x) =
      p ^ ((n - 1) * l) * repCountOf Q p k m (fun x => ¬ IsZeroType p k x) := by
  rw [repCountOf_nonZero_eq_padic, repCountOf_nonZero_eq_padic,
    DVR.repCountOf_nonZero_add_of_det _ _ PadicInt.irreducible_p (by
      rw [det_map_padic]; exact not_padic_dvd_of_not_dvd hdet) _ k l hk, q_padicInt]

end QuadFormsKB.LocalDensity

namespace QuadFormsKB.Binary

open QuadForm LocalDensity BinQF

/-- A binary form evaluated over any commutative ring: $f(\vec v) = a v_0^2 + b v_0 v_1 + c v_1^2$. -/
theorem evalIn_bin (f : BinQF) {K : Type*} [CommRing K] (v : Fin 2 → K) :
    f.evalIn K v = (f.a : K) * v 0 ^ 2 + (f.b : K) * v 0 * v 1 + (f.c : K) * v 1 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_two, BinQF.a, BinQF.b, BinQF.c]
  ring

/-- $r_p(m)$ as a count over $\mathbb{F}_p^2$. -/
theorem repCount_one_eq (f : BinQF) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    repCount f p 1 m = Nat.card {v : Fin 2 → ZMod p //
      (f.a : ZMod p) * v 0 ^ 2 + (f.b : ZMod p) * v 0 * v 1 + (f.c : ZMod p) * v 1 ^ 2 = m} := by
  let e : ZMod (p ^ 1) ≃+* ZMod p := ZMod.ringEquivCongr (pow_one p)
  refine Nat.card_congr ((Equiv.piCongrRight fun _ => e.toEquiv).subtypeEquiv fun v => ?_)
  rw [evalIn_bin, ← e.injective.eq_iff]
  simp only [map_add, map_mul, map_pow, map_intCast]
  rfl

/-- Counting square roots in $\mathbb{F}_p$, $p$ odd: $\#\{X : X^2 = t\} = 1 + \left(\frac tp\right)$. -/
theorem card_sqrt_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (t : ℤ) :
    (Nat.card {X : ZMod p // X ^ 2 = t} : ℤ) = legendreSym p t + 1 := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have := quadraticChar_card_sqrts hc (t : ZMod p)
  rw [legendreSym, ← this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext x; simp

/-- **Count mod $p$ at a ramified odd prime** ($p \mid D$, $p \nmid a$): $r_p(m) = p\,(1 + (\frac{am}{p}))$. -/
theorem repCount_one_ram (f : BinQF) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpD : (p : ℤ) ∣ f.disc)
    (ha : ¬ (p : ℤ) ∣ f.a) (m : ℤ) :
    (repCount f p 1 m : ℤ) = p * (1 + legendreSym p (f.a * m)) := by
  classical
  have hpp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have ha' : (f.a : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hD : (f.b : ZMod p) ^ 2 - 4 * f.a * f.c = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpD
    rw [disc] at this; push_cast at this; exact this
  set A : ZMod p := (f.a : ZMod p) with hA
  set B : ZMod p := (f.b : ZMod p) with hB
  set C : ZMod p := (f.c : ZMod p) with hC
  have h2a : (2 * A) ≠ 0 := mul_ne_zero h2 ha'
  -- the change of variables (x, y) ↦ (2ax + by, y)
  let φ : (Fin 2 → ZMod p) ≃ (Fin 2 → ZMod p) :=
    { toFun := fun v => ![2 * A * v 0 + B * v 1, v 1]
      invFun := fun w => ![(w 0 - B * w 1) / (2 * A), w 1]
      left_inv := fun v => by
        funext i; fin_cases i <;> simp; field_simp
      right_inv := fun w => by
        funext i; fin_cases i <;> simp; field_simp; ring }
  have key : ∀ v : Fin 2 → ZMod p, (A * v 0 ^ 2 + B * v 0 * v 1 + C * v 1 ^ 2 = m ↔
      (φ v) 0 ^ 2 = ((4 * f.a * m : ℤ) : ZMod p)) := by
    intro v
    simp only [φ, Equiv.coe_fn_mk, Matrix.cons_val_zero]
    push_cast
    have h4a : (4 * A) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) ha'
    constructor
    · intro h; rw [← h]; linear_combination (v 1 ^ 2) * hD
    · intro h
      apply mul_left_cancel₀ h4a
      linear_combination h - (v 1 ^ 2) * hD
  rw [repCount_one_eq]
  have e1 : Nat.card {v : Fin 2 → ZMod p // A * v 0 ^ 2 + B * v 0 * v 1 + C * v 1 ^ 2 = m} =
      Nat.card {w : Fin 2 → ZMod p // w 0 ^ 2 = ((4 * f.a * m : ℤ) : ZMod p)} :=
    Nat.card_congr (φ.subtypeEquiv key)
  have e2 : Nat.card {w : Fin 2 → ZMod p // w 0 ^ 2 = ((4 * f.a * m : ℤ) : ZMod p)} =
      Nat.card {X : ZMod p // X ^ 2 = ((4 * f.a * m : ℤ) : ZMod p)} * p := by
    let ψ : {w : Fin 2 → ZMod p // w 0 ^ 2 = ((4 * f.a * m : ℤ) : ZMod p)} ≃
        {X : ZMod p // X ^ 2 = ((4 * f.a * m : ℤ) : ZMod p)} × ZMod p :=
      { toFun := fun w => (⟨w.1 0, w.2⟩, w.1 1)
        invFun := fun q => ⟨![q.1.1, q.2], by simpa using q.1.2⟩
        left_inv := fun w => by
          apply Subtype.ext; funext i; fin_cases i <;> rfl
        right_inv := fun q => by rfl }
    rw [Nat.card_congr ψ, Nat.card_prod, Nat.card_zmod]
  rw [e1, e2, Nat.cast_mul, card_sqrt_zmod p hp]
  have h4 : legendreSym p (4 * f.a * m) = legendreSym p (f.a * m) := by
    rw [show (4 : ℤ) * f.a * m = 2 ^ 2 * (f.a * m) by ring, legendreSym.mul,
      legendreSym.sq_one' p (by exact_mod_cast h2), one_mul]
  rw [h4]; ring

/-- The form with $a$ and $c$ exchanged, $f(y, x)$. -/
def swapF (f : BinQF) : BinQF := BinQF.mk f.c f.b f.a

@[simp] theorem swapF_a (f : BinQF) : (swapF f).a = f.c := a_mk _ _ _
@[simp] theorem swapF_b (f : BinQF) : (swapF f).b = f.b := b_mk _ _ _
@[simp] theorem swapF_c (f : BinQF) : (swapF f).c = f.a := c_mk _ _ _

theorem disc_swapF (f : BinQF) : (swapF f).disc = f.disc := by simp [disc]; ring

/-- Exchanging the variables does not change the counts $r_{p^k}(m)$. -/
theorem repCount_swapF (f : BinQF) (p k : ℕ) (m : ℤ) :
    repCount (swapF f) p k m = repCount f p k m := by
  let σ : (Fin 2 → ZMod (p ^ k)) ≃ (Fin 2 → ZMod (p ^ k)) :=
    { toFun := fun v => ![v 1, v 0], invFun := fun v => ![v 1, v 0]
      left_inv := fun v => by funext i; fin_cases i <;> rfl
      right_inv := fun v => by funext i; fin_cases i <;> rfl }
  refine Nat.card_congr (σ.subtypeEquiv fun v => ?_)
  rw [evalIn_bin, evalIn_bin]
  simp only [swapF_a, swapF_b, swapF_c, σ, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  constructor <;> intro h <;> rw [← h] <;> ring

/-- **Count mod $p$ at a ramified odd prime, by the genus character:** for $f$ primitive, $p \mid D = \operatorname{disc} f$
odd: $r_p(m) = p\,(1 + \chi_p(f)\psi_p(m))$, with $\chi_p(f)$ = `formChar f p`, $\psi_p$ = `genusChar D p`. -/
@[kb "cox2013" "§3.B, Lemma 3.17 [unverified locator]"]
theorem repCount_one_ram_formChar {f : BinQF} (hf : Primitive f) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hpD : (p : ℤ) ∣ f.disc) (m : ℤ) :
    (repCount f p 1 m : ℤ) = p * (1 + formChar f p * genusChar f.disc p m) := by
  have hpp : p.Prime := Fact.out
  have hr := not_dvd_charCoeff hf hpp hpD
  have hfc : formChar f p = legendreSym p (charCoeff f p) := by
    rw [formChar, genusChar, ite_eq_right hp, jacobiSym.legendreSym.to_jacobiSym]
  have hgm : genusChar f.disc p m = legendreSym p m := by
    rw [genusChar, ite_eq_right hp, jacobiSym.legendreSym.to_jacobiSym]
  rw [hfc, hgm, ← legendreSym.mul]
  unfold charCoeff at hr ⊢
  split_ifs with ha
  · rw [ite_eq_left ha] at hr
    rw [← repCount_swapF]
    have := repCount_one_ram (swapF f) p hp (by rwa [disc_swapF]) (by simpa using hr) m
    simpa using this
  · exact repCount_one_ram f p hp hpD ha m

/-- $r_{p^k}(m)$ as a count over $(\mathbb{Z}/N)^2$ for $N = p^k$. -/
theorem repCount_eq_card (f : BinQF) (p k N : ℕ) (h : p ^ k = N) (m : ℤ) :
    repCount f p k m = Nat.card {v : Fin 2 → ZMod N //
      (f.a : ZMod N) * v 0 ^ 2 + (f.b : ZMod N) * v 0 * v 1 + (f.c : ZMod N) * v 1 ^ 2 = m} := by
  let e : ZMod (p ^ k) ≃+* ZMod N := ZMod.ringEquivCongr h
  refine Nat.card_congr ((Equiv.piCongrRight fun _ => e.toEquiv).subtypeEquiv fun v => ?_)
  rw [evalIn_bin, ← e.injective.eq_iff]
  simp only [map_add, map_mul, map_pow, map_intCast]
  rfl

theorem card8_aux (P : ZMod 8 × ZMod 8 → Prop) [DecidablePred P] :
    Nat.card {v : Fin 2 → ZMod 8 // P (v 0, v 1)} = (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ((finTwoArrowEquiv (ZMod 8)).subtypeEquiv fun v => Iff.rfl)

theorem card8_d2 : ∀ n : ZMod 8, ZMod.χ₈ n ≠ 0 →
    (((Finset.univ : Finset (ZMod 8 × ZMod 8)).filter fun w => w.1 ^ 2 - 2 * w.2 ^ 2 = n).card : ℤ) =
      8 * (1 + ZMod.χ₈ n) := by decide

theorem card8_d6 : ∀ n : ZMod 8, ZMod.χ₈' n ≠ 0 →
    (((Finset.univ : Finset (ZMod 8 × ZMod 8)).filter fun w => w.1 ^ 2 - 6 * w.2 ^ 2 = n).card : ℤ) =
      8 * (1 + ZMod.χ₈' n) := by decide

theorem card8_d3 : ∀ n : ZMod 8, ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) n) ≠ 0 →
    (((Finset.univ : Finset (ZMod 8 × ZMod 8)).filter fun w => w.1 ^ 2 - 3 * w.2 ^ 2 = n).card : ℤ) =
      8 * (1 + ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) n)) := by decide

theorem card8_d7 : ∀ n : ZMod 8, ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) n) ≠ 0 →
    (((Finset.univ : Finset (ZMod 8 × ZMod 8)).filter fun w => w.1 ^ 2 - 7 * w.2 ^ 2 = n).card : ℤ) =
      8 * (1 + ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) n)) := by decide

/-- **Count mod $8$ at $p = 2 \mid D$, $a$ odd:** $r_8(m) = \#\{(X, Y) \in (\mathbb{Z}/8)^2 : X^2 - dY^2 = am\}$ with
$d = D/4$ (the substitution $X = ax + b'y$, $Y = y$, $b = 2b'$; $a \cdot f = X^2 - dY^2$). -/
theorem repCount_three_two_aux {f : BinQF} (ha : ¬ (2 : ℤ) ∣ f.a) {b' : ℤ} (hb : f.b = 2 * b') (m : ℤ) :
    repCount f 2 3 m = Nat.card {v : Fin 2 → ZMod 8 //
      v 0 ^ 2 - ((b' ^ 2 - f.a * f.c : ℤ) : ZMod 8) * v 1 ^ 2 = ((f.a * m : ℤ) : ZMod 8)} := by
  rw [repCount_eq_card f 2 3 8 (by norm_num)]
  have hA : ((f.a : ℤ) : ZMod 8) ^ 2 = 1 := sq_odd_zmod8 ha
  let φ : (Fin 2 → ZMod 8) ≃ (Fin 2 → ZMod 8) :=
    { toFun := fun v => ![(f.a : ZMod 8) * v 0 + (b' : ZMod 8) * v 1, v 1]
      invFun := fun w => ![(f.a : ZMod 8) * (w 0 - (b' : ZMod 8) * w 1), w 1]
      left_inv := fun v => by
        funext i; fin_cases i <;> simp; linear_combination (v 0) * hA
      right_inv := fun w => by
        funext i; fin_cases i <;> simp; linear_combination (w 0 - (b' : ZMod 8) * w 1) * hA }
  refine Nat.card_congr (φ.subtypeEquiv fun v => ?_)
  simp only [φ, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hb]
  push_cast
  constructor
  · intro h; rw [← h]; ring
  · intro h
    have : (f.a : ZMod 8) * ((f.a : ZMod 8) * v 0 ^ 2 + 2 * (b' : ZMod 8) * v 0 * v 1 +
        (f.c : ZMod 8) * v 1 ^ 2) = (f.a : ZMod 8) * m := by
      linear_combination h
    linear_combination (f.a : ZMod 8) * this - ((f.a : ZMod 8) * v 0 ^ 2 + 2 * (b' : ZMod 8) * v 0 * v 1 +
        (f.c : ZMod 8) * v 1 ^ 2 - m) * hA

/-- **Count mod $8$ at $p = 2 \mid D$, by the genus character:** for $f$ primitive of fundamental discriminant
$D$ with $2 \mid D$ and $m$ odd: $r_8(m) = 8\,(1 + \chi_2(f)\psi_2(m))$. -/
@[kb "cox2013" "§3.B, Thm. 3.15 [unverified locator]"]
theorem repCount_three_two {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (h2D : (2 : ℤ) ∣ D) (m : ℤ) (hm : ¬ (2 : ℤ) ∣ m) :
    (repCount f 2 3 m : ℤ) = 8 * (1 + formChar f 2 * genusChar D 2 m) := by
  -- reduce to `a` odd
  suffices H : ∀ g : BinQF, g.disc = D → ¬ (2 : ℤ) ∣ g.a →
      (repCount g 2 3 m : ℤ) = 8 * (1 + genusChar D 2 (g.a * m)) by
    have hr := not_dvd_charCoeff hf Nat.prime_two (by rw [hD]; exact_mod_cast h2D)
    rw [formChar, hD, ← genusChar_mul]
    unfold charCoeff at hr ⊢
    split_ifs with ha
    · rw [ite_eq_left ha] at hr
      rw [← repCount_swapF]
      have := H (swapF f) (by rw [disc_swapF, hD]) (by simpa using hr)
      simpa using this
    · exact H f hD ha
  intro g hgD ha
  have hb2 : (2 : ℤ) ∣ g.b := by
    have : g.b ^ 2 = D + 4 * g.a * g.c := by rw [← hgD, disc]; ring
    have h2 : (2 : ℤ) ∣ g.b ^ 2 := by
      rw [this]; exact dvd_add h2D (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _)
    exact int_prime_dvd_of_dvd_sq (p := 2) Nat.prime_two (by exact_mod_cast h2)
  obtain ⟨b', hb'⟩ := hb2
  have hd4 : D / 4 = b' ^ 2 - g.a * g.c := by
    rw [← hgD, disc, hb', show (2 * b') ^ 2 - 4 * g.a * g.c = 4 * (b' ^ 2 - g.a * g.c) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [repCount_three_two_aux ha hb' m, ← hd4]
  have ham : ¬ (2 : ℤ) ∣ g.a * m := fun h => (int_prime_dvd_mul Nat.prime_two h).elim ha hm
  have hc := (two_dvd_iff_of_fund (D := D)).mp h2D
  rw [genusChar_two_eq]
  have hne : ∀ z : ℤ, ¬ (2 : ℤ) ∣ z → ZMod.χ₈ (z : ZMod 8) ≠ 0 ∧ ZMod.χ₈' (z : ZMod 8) ≠ 0 ∧
      ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) (z : ZMod 8)) ≠ 0 := by
    intro z hz
    have e : ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) (z : ZMod 8) = (z : ZMod 4) := map_intCast _ z
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [ZMod.χ₈_int_eq_if_mod_eight]; split_ifs <;> omega
    · rw [ZMod.χ₈'_int_eq_if_mod_eight]; split_ifs <;> omega
    · rw [ZMod.χ₄_int_eq_if_mod_four]; split_ifs <;> omega
  obtain ⟨n1, n2, n3⟩ := hne _ ham
  rw [card8_aux (fun w => w.1 ^ 2 - ((D / 4 : ℤ) : ZMod 8) * w.2 ^ 2 = ((g.a * m : ℤ) : ZMod 8))]
  split_ifs with h8 h24
  · have hd : ((D / 4 : ℤ) : ZMod 8) = 2 := zmod8_cast_eq_of_emod (r := 2) (by omega)
    rw [hd]; exact card8_d2 _ n1
  · have hd : ((D / 4 : ℤ) : ZMod 8) = 6 := zmod8_cast_eq_of_emod (r := 6) (by omega)
    rw [hd]; exact card8_d6 _ n2
  · rcases (show D % 32 = 12 ∨ D % 32 = 28 by omega) with h | h
    · have hd : ((D / 4 : ℤ) : ZMod 8) = 3 := zmod8_cast_eq_of_emod (r := 3) (by omega)
      rw [hd]; exact card8_d3 _ n3
    · have hd : ((D / 4 : ℤ) : ZMod 8) = 7 := zmod8_cast_eq_of_emod (r := 7) (by omega)
      rw [hd]; exact card8_d7 _ n3

/-! ### Densities from counts at a fixed level -/

/-- If the counts are $r_{p^{K+l}}(m) = p^l r_{p^K}(m)$ for all $l$, then $\beta_p(m) = r_{p^K}(m)/p^K$ ($n = 2$). -/
theorem localDensity_eq_of_lift (f : BinQF) (p : ℕ) [Fact p.Prime] (m : ℤ) (K : ℕ)
    (h : ∀ l, repCount f p (K + l) m = p ^ l * repCount f p K m) :
    localDensity f p m = (repCount f p K m : ℝ) / (p : ℝ) ^ K := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop K] with k hk
  obtain ⟨l, rfl⟩ : ∃ l, k = K + l := ⟨k - K, by omega⟩
  rw [h l, show (K + l) * (2 - 1) = K + l by omega, pow_add]
  push_cast
  field_simp

/-- **$\beta_p(m)$ at a ramified prime, $p \nmid m$** ($D$ fundamental, $f$ primitive of discriminant $D$, $p \mid D$
prime, including $p = 2$): $\beta_p(m) = 1 + \chi_p(f)\psi_p(m) \in \{0, 2\}$. -/
@[kb "siegel1935" "§§1–2, the densities α_p (binary case) [unverified locator]"]
theorem localDensity_ram_unit {D : ℤ} [IsQuadDisc D] {f : BinQF} (hf : Primitive f) (hD : f.disc = D)
    (p : ℕ) [Fact p.Prime] (hpD : (p : ℤ) ∣ D) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    localDensity f p m = 1 + formChar f p * genusChar D p m := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hlift : ∀ l, repCount f p (2 * eTwo p + 1 + l) m = p ^ l * repCount f p (2 * eTwo p + 1) m := by
    intro l
    rw [repCount_unit_add f p m hm _ l le_rfl, show (2 - 1) * l = l by omega]
  rw [localDensity_eq_of_lift f p m _ hlift]
  by_cases hp2 : p = 2
  · subst hp2
    have h3 : 2 * eTwo 2 + 1 = 3 := rfl
    rw [h3]
    have := repCount_three_two hf hD (by exact_mod_cast hpD) m (by exact_mod_cast hm)
    have h' : (repCount f 2 3 m : ℝ) = 8 * (1 + formChar f 2 * genusChar D 2 m) := by exact_mod_cast this
    rw [h']; push_cast; ring
  · have h1 : 2 * eTwo p + 1 = 1 := by simp [eTwo, hp2]
    rw [h1]
    have := repCount_one_ram_formChar hf p hp2 (by rw [hD]; exact hpD) m
    rw [hD] at this
    have h' : (repCount f p 1 m : ℝ) = p * (1 + formChar f p * genusChar D p m) := by exact_mod_cast this
    rw [h', pow_one]; field_simp

/-! ### Counts mod $p$ at a prime $p \nmid D$ -/

theorem repCount_congr_dvd (f : BinQF) (p k : ℕ) {m m' : ℤ} (h : ((p ^ k : ℕ) : ℤ) ∣ m - m') :
    repCount f p k m = repCount f p k m' := by
  have : (m : ZMod (p ^ k)) = (m' : ZMod (p ^ k)) :=
    ((ZMod.intCast_eq_intCast_iff_dvd_sub m' m (p ^ k)).mpr h).symm
  unfold repCount
  rw [this]

theorem kron_two_values : ∀ A C m : ZMod 2,
    (((Finset.univ : Finset (ZMod 2 × ZMod 2)).filter fun w => A * w.1 ^ 2 + 1 * w.1 * w.2 + C * w.2 ^ 2 = m).card : ℤ) =
      if m = 0 then (if A * C = 0 then 3 else 1) else (if A * C = 0 then 1 else 3) := by decide

theorem card2_aux (P : ZMod 2 × ZMod 2 → Prop) [DecidablePred P] :
    Nat.card {v : Fin 2 → ZMod 2 // P (v 0, v 1)} = (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ((finTwoArrowEquiv (ZMod 2)).subtypeEquiv fun v => Iff.rfl)

/-- **Counts mod $p$ for $p \nmid D$** ($D$ fundamental, $\chi = \chi_D(p) = \pm 1$, $p = 2$ allowed):
$r_p(m) = p + \chi(p - 1)$ if $p \mid m$ and $r_p(m) = p - \chi$ if $p \nmid m$. -/
@[kb "hanke2004" "Table 1, p. 363 (n = 2), and p = 2"]
theorem repCount_one_good {D : ℤ} [IsQuadDisc D] (f : BinQF) (hD : f.disc = D) (p : ℕ) [Fact p.Prime]
    (hpD : ¬ (p : ℤ) ∣ D) (m : ℤ) :
    (repCount f p 1 m : ℤ) = if (p : ℤ) ∣ m then p + kronZ D (p : ZMod D.natAbs) * (p - 1)
      else p - kronZ D (p : ZMod D.natAbs) := by
  have hpp : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    have hD1 : D % 4 = 1 := by
      rcases fund_cases (D := D) with h | h | h | h | h
      · exact h
      all_goals exact absurd (by omega : (2 : ℤ) ∣ D) (by exact_mod_cast hpD)
    have hbodd : ¬ (2 : ℤ) ∣ f.b := fun h => hpD (by
      rw [← hD, disc]; obtain ⟨t, ht⟩ := h
      exact ⟨2 * t ^ 2 - 2 * f.a * f.c, by rw [ht]; push_cast; ring⟩)
    have hb : ((f.b : ℤ) : ZMod 2) = 1 := by
      rw [intCast_zmod_two, ite_eq_right]
      intro h0; exact hbodd (Int.dvd_of_emod_eq_zero h0)
    simp only [Nat.cast_ofNat]
    rw [kronZ_two, ite_eq_left hD1, repCount_eq_card f 2 1 2 (by norm_num) m, hb,
      card2_aux (fun w => (f.a : ZMod 2) * w.1 ^ 2 + 1 * w.1 * w.2 + (f.c : ZMod 2) * w.2 ^ 2 = (m : ZMod 2)),
      kron_two_values]
    have hm2 : ((m : ℤ) : ZMod 2) = 0 ↔ (2 : ℤ) ∣ m := ZMod.intCast_zmod_eq_zero_iff_dvd m 2
    have hac : (f.a : ZMod 2) * (f.c : ZMod 2) = 0 ↔ D % 8 = 1 := by
      rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have : D = f.b ^ 2 - 4 * (f.a * f.c) := by rw [← hD, disc]; ring
      have hbo : f.b % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one f.b with h | h
        · exfalso
          have : ((f.b : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (Int.dvd_of_emod_eq_zero h)
          rw [hb] at this; exact one_ne_zero this
        · exact h
      have hb8 : f.b ^ 2 % 8 = 1 := by
        have : f.b % 8 = 1 ∨ f.b % 8 = 3 ∨ f.b % 8 = 5 ∨ f.b % 8 = 7 := by omega
        rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]
      constructor
      · rintro ⟨t, ht⟩; rw [this, ht]; omega
      · intro h8
        have : (f.a * f.c) % 2 = 0 := by omega
        exact Int.dvd_of_emod_eq_zero this
    simp only [hm2, hac]
    split_ifs <;> norm_num
  · obtain ⟨a, ha, hcount, u, hu, hdet⟩ := Siegel.exists_diag_unimodular_same_counts_det f p hp2
      (by rw [hessian_det_two]; intro h; apply hpD
          have : (4 * f.coeff 0 0 * f.coeff 1 1 - f.coeff 0 1 ^ 2) = -D := by
            rw [← hD, disc]; simp only [BinQF.a, BinQF.b, BinQF.c]; ring
          rw [this] at h; exact (dvd_neg).mp h)
    have hL : legendreSym p ((-1) ^ (2 / 2) * ∏ i, a i) = kronZ D (p : ZMod D.natAbs) := by
      rw [kronZ_odd_prime p hp2]
      have hdetD : f.hessian.det = -D := by
        rw [hessian_det_two, ← hD, disc]; simp only [BinQF.a, BinQF.b, BinQF.c]; ring
      rw [hdetD] at hdet
      have hu' : ((u : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have h2' : ((2 : ℤ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (by exact_mod_cast h))
      have e : (2 ^ 2) * ((-1) ^ (2 / 2) * ∏ i, a i) = u ^ 2 * D := by
        simp only [show (2 : ℕ) / 2 = 1 from rfl, pow_one]; linear_combination (-1 : ℤ) * hdet
      have := congrArg (legendreSym p) e
      rw [legendreSym.mul p (2 ^ 2), legendreSym.mul p (u ^ 2), legendreSym.sq_one' p h2',
        legendreSym.sq_one' p hu', one_mul, one_mul] at this
      exact this
    have hcd := (card_diag_mod_p a p hp2 ha (by norm_num) 1 (by
      intro h; exact hpp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))).1 even_two
    rw [hL] at hcd
    split_ifs with hm
    · rw [repCount_congr_dvd f p 1 (m' := 0) (by simpa using hm), hcount, hcd.1]
      simp
    · have hcd' := (card_diag_mod_p a p hp2 ha (by norm_num) m hm).1 even_two
      rw [hL] at hcd'
      rw [hcount, hcd'.2]
      simp

/-! ### $\beta_p(m)$ at $p \nmid D$: the recursion -/

/-- **The good Euler factor** $(1 - \chi/p)\sum_{j=0}^{v}\chi^j$. -/
@[kb "siegel1935" "§§1–2 [unverified locator]"]
noncomputable def goodFactor (χ : ℤ) (p v : ℕ) : ℝ :=
  (1 - (χ : ℝ) / p) * ∑ j ∈ Finset.range (v + 1), (χ : ℝ) ^ j

theorem goodFactor_zero (χ : ℤ) (p : ℕ) : goodFactor χ p 0 = 1 - (χ : ℝ) / p := by
  simp [goodFactor]

theorem goodFactor_one (χ : ℤ) (hχ : χ = 1 ∨ χ = -1) (p : ℕ) (hp : (p : ℝ) ≠ 0) :
    goodFactor χ p 1 = ((p : ℝ) - 1) * (1 + χ) / p := by
  rcases hχ with rfl | rfl
  · simp [goodFactor]; field_simp; norm_num
  · simp [goodFactor]

theorem goodFactor_add_two (χ : ℤ) (hχ : χ = 1 ∨ χ = -1) (p v : ℕ) (hp : (p : ℝ) ≠ 0) :
    goodFactor χ p (v + 2) = goodFactor χ p v + ((p : ℝ) - 1) * (1 + χ) / p := by
  unfold goodFactor
  rw [show v + 2 + 1 = (v + 1) + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
  rcases hχ with rfl | rfl
  · simp; field_simp; ring
  · push_cast
    have : ((-1 : ℝ)) ^ (v + 1) + (-1) ^ (v + 1 + 1) = 0 := by rw [pow_succ]; ring
    field_simp
    linear_combination (↑p + 1) * (↑p:ℝ) * this

/-- Zero-type solutions mod $p$: only $\vec 0$, when $p \mid m$. -/
theorem repCountOf_zero_one (f : BinQF) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    repCountOf f p 1 m (IsZeroType p 1) = if (p : ℤ) ∣ m then 1 else 0 := by
  have hp0 : (p : ZMod (p ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff p (p ^ 1)).mpr (by rw [pow_one])
  have hz : ∀ x : Fin 2 → ZMod (p ^ 1), IsZeroType p 1 x ↔ x = 0 := by
    intro x
    simp only [IsZeroType, hp0, zero_dvd_iff, funext_iff, Pi.zero_apply]
  have hm : (m : ZMod (p ^ 1)) = 0 ↔ (p : ℤ) ∣ m := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, pow_one]
  unfold repCountOf
  simp only [hz]
  split_ifs with h
  · rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, ?_, rfl⟩, fun y => Subtype.ext y.2.2⟩
    rw [evalIn_bin, hm.mpr h]; simp
  · rw [Nat.card_eq_zero]; left
    exact ⟨fun y => h (hm.mp (by rw [← y.2.1, y.2.2, evalIn_bin]; simp))⟩

theorem int_dvd_iff_natAbs {p : ℕ} {m : ℤ} : (p : ℤ) ∣ m ↔ p ∣ m.natAbs := Int.natCast_dvd

theorem factorization_eq_one {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ∣ n) (h2 : ¬ p ^ 2 ∣ n) :
    n.factorization p = 1 := by
  have a := (hp.pow_dvd_iff_le_factorization hn).mp (by rwa [pow_one])
  have b : ¬ 2 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hn).mpr h)
  omega

theorem factorization_sq_mul {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (p ^ 2 * n).factorization p = n.factorization p + 2 := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hn, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, hp.factorization_self]
  simp; ring

/-- **The recursion at $p \nmid \det H$** ($n = 2$): if $r_p(m) = p + \chi(p-1)$ for $p \mid m$ and $p - \chi$ for
$p \nmid m$, with $\chi = \pm 1$, then for every $m \ne 0$ the normalized counts are eventually
$(1 - \chi/p)\sum_{j=0}^{v_p(m)}\chi^j$. -/
@[kb "hanke2004" "§3, map π_Z, p. 359; Lemma 3.2, p. 358"]
theorem eventually_repCount_good (f : BinQF) (p : ℕ) [Fact p.Prime] (hdet : ¬ (p : ℤ) ∣ f.hessian.det)
    (χ : ℤ) (hχ : χ = 1 ∨ χ = -1)
    (hcount : ∀ m : ℤ, (repCount f p 1 m : ℤ) = if (p : ℤ) ∣ m then p + χ * (p - 1) else p - χ) :
    ∀ N : ℕ, ∀ m : ℤ, m.natAbs = N → m ≠ 0 →
      ∀ᶠ k in Filter.atTop, (repCount f p k m : ℝ) / (p : ℝ) ^ k = goodFactor χ p (m.natAbs.factorization p) := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  -- the non-Zero-type count
  have hnz1 : ∀ m : ℤ, (repCountOf f p 1 m (fun x => ¬ IsZeroType p 1 x) : ℝ) =
      if (p : ℤ) ∣ m then ((p : ℝ) - 1) * (1 + χ) else (p : ℝ) - χ := by
    intro m
    have e := repCount_eq_zero_add_nonZero f p 1 m
    rw [repCountOf_zero_one] at e
    have e' : (repCount f p 1 m : ℝ) = ((if (p : ℤ) ∣ m then 1 else 0 : ℕ) : ℝ) +
        (repCountOf f p 1 m (fun x => ¬ IsZeroType p 1 x) : ℝ) := by exact_mod_cast e
    have hc : (repCount f p 1 m : ℝ) = ((if (p : ℤ) ∣ m then p + χ * (p - 1) else p - χ : ℤ) : ℝ) := by
      exact_mod_cast hcount m
    rw [hc] at e'
    split_ifs at e' ⊢ with h
    · push_cast at e'; linarith
    · push_cast at e'; linarith
  have hnz : ∀ (m : ℤ) (k : ℕ), 1 ≤ k → (repCountOf f p k m (fun x => ¬ IsZeroType p k x) : ℝ) =
      (p : ℝ) ^ (k - 1) * (if (p : ℤ) ∣ m then ((p : ℝ) - 1) * (1 + χ) else (p : ℝ) - χ) := by
    intro m k hk
    obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
    rw [repCountOf_nonZero_add_of_det f p hdet m 1 l le_rfl, show (2 - 1) * l = l by omega,
      show 1 + l - 1 = l by omega]
    push_cast
    rw [hnz1]
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro m hmN hm0
  have hmA : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  -- the total count for k ≥ 2
  have htot : ∀ k, 2 ≤ k → (repCount f p k m : ℝ) =
      (if (p : ℤ) ^ 2 ∣ m then (p : ℝ) ^ 2 * repCount f p (k - 2) (m / p ^ 2) else 0) +
        (p : ℝ) ^ (k - 1) * (if (p : ℤ) ∣ m then ((p : ℝ) - 1) * (1 + χ) else (p : ℝ) - χ) := by
    intro k hk
    rw [repCount_eq_zero_add_nonZero, repCountZero_eq f p m k hk, Nat.cast_add, hnz m k (by omega)]
    split_ifs <;> push_cast <;> ring
  by_cases h2 : (p : ℤ) ^ 2 ∣ m
  · -- m = p² m'
    obtain ⟨m', rfl⟩ := h2
    have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm0
    have hdiv : (p : ℤ) ^ 2 * m' / (p : ℤ) ^ 2 = m' :=
      Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero))
    have hA : ((p : ℤ) ^ 2 * m').natAbs = p ^ 2 * m'.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    have hlt : m'.natAbs < N := by
      rw [← hmN, hA]
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hpp.one_lt
      have h0 : 0 < m'.natAbs := Int.natAbs_pos.mpr hm'0
      nlinarith
    have IH := ih _ hlt m' rfl hm'0
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp IH
    rw [Filter.eventually_atTop]
    refine ⟨J + 2, fun k hk => ?_⟩
    rw [htot k (by omega), ite_eq_left ⟨m', rfl⟩, ite_eq_left (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _),
      hdiv, hA, factorization_sq_mul hpp (Int.natAbs_ne_zero.mpr hm'0),
      goodFactor_add_two χ hχ p _ hp0, ← hJ (k - 2) (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show j + 2 - 2 = j by omega, show j + 2 - 1 = j + 1 by omega]
    field_simp
    ring
  · rw [Filter.eventually_atTop]
    refine ⟨2, fun k hk => ?_⟩
    rw [htot k hk, ite_eq_right h2, zero_add]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega]
    by_cases h1 : (p : ℤ) ∣ m
    · rw [ite_eq_left h1, factorization_eq_one hpp hmA (int_dvd_iff_natAbs.mp h1)
        (by rw [← Int.natCast_dvd]; push_cast; exact h2), goodFactor_one χ hχ p hp0]
      field_simp; ring
    · rw [ite_eq_right h1, Nat.factorization_eq_zero_of_not_dvd (fun h => h1 (int_dvd_iff_natAbs.mpr h)),
        goodFactor_zero]
      field_simp; ring

/-- **$\beta_p(m)$ at a prime $p \nmid D$** ($D$ fundamental, $f$ of discriminant $D$, $p = 2$ allowed, $m \ne 0$):
$$\beta_p(m) = \Big(1 - \frac{\chi_D(p)}{p}\Big)\sum_{j=0}^{v_p(m)}\chi_D(p)^j.$$ -/
@[kb "yang1998" "binary case [unverified locator]"]
theorem localDensity_good_binary {D : ℤ} [IsQuadDisc D] (f : BinQF) (hD : f.disc = D) (p : ℕ) [Fact p.Prime]
    (hpD : ¬ (p : ℤ) ∣ D) (m : ℤ) (hm : m ≠ 0) :
    localDensity f p m = goodFactor (kronZ D (p : ZMod D.natAbs)) p (m.natAbs.factorization p) := by
  have hpp : p.Prime := Fact.out
  have hχ : kronZ D (p : ZMod D.natAbs) = 1 ∨ kronZ D (p : ZMod D.natAbs) = -1 := by
    by_cases hp2 : p = 2
    · subst hp2
      have hD1 : D % 4 = 1 := by
        rcases fund_cases (D := D) with h | h | h | h | h
        · exact h
        all_goals exact absurd (by omega : (2 : ℤ) ∣ D) (by exact_mod_cast hpD)
      simp only [Nat.cast_ofNat]
      rw [kronZ_two, ite_eq_left hD1]; split_ifs <;> simp
    · rw [kronZ_odd_prime p hp2]
      exact legendreSym.eq_one_or_neg_one p (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])
  have hdet : ¬ (p : ℤ) ∣ f.hessian.det := by
    have : f.hessian.det = -D := by
      rw [hessian_det_two, ← hD, disc]; simp only [BinQF.a, BinQF.b, BinQF.c]; ring
    rw [this, dvd_neg]; exact hpD
  have := eventually_repCount_good f p hdet _ hχ (repCount_one_good f hD p hpD) _ m rfl hm
  apply limUnder_eq_of_eventually
  filter_upwards [this] with k hk
  rw [show k * (2 - 1) = k by omega]; exact hk

end QuadFormsKB.Binary
