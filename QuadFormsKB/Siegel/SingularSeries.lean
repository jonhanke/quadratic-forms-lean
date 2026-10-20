/-
# The singular series and the Euler product of local densities

For an integral form $Q$ in $n$ variables, $A = H/2$ its Gram matrix, $m \in \mathbb{Z}$ and $c \ge 1$ put
$$A_c(m) = c^{-n}\sum_{\substack{0 \le a < c\\ \gcd(a, c) = 1}} G_A(a, c)\,e\Big(\!-\frac{am}{c}\Big), \qquad
  G_A(a, c) = \sum_{\vec{r} \bmod c} e\Big(\frac{a\,Q(\vec{r})}{c}\Big)$$
(`ssTerm`; $A_0 = 0$). The **singular series** is $\sum_{c \ge 1}A_c(m)$. Results:

* `ssTerm_one`, `ssTerm_mul`: $A_1 = 1$ and $A_{c_1c_2} = A_{c_1}A_{c_2}$ for coprime $c_1, c_2$ (Chinese remainder theorem:
  $e(y/c_1c_2) = e(u y/c_1)\,e(v y/c_2)$ for $uc_2 + vc_1 = 1$).
* `sum_ssTerm_prime_pow`: $\sum_{e=0}^{k}A_{p^e}(m) = r_{p^k}(m)/p^{k(n-1)}$ (orthogonality of additive characters, and
  $G_A(pb, p^{k+1}) = p^nG_A(b, p^k)$).
* `hasSum_ssTerm`: for $Q$ nondegenerate, $n \ge 4$, $m \ne 0$, if the singular series is summable then its sum is
  $\prod_p\beta_p(m)$ (`eulerProduct`; Mathlib's Euler product `EulerProduct.eulerProduct_hasProd`).

Reference: Siegel 1935 (the singular series) [unverified]; Iwaniec 1997, §11 [unverified].
-/
import QuadFormsKB.Siegel.LocalProduct
import QuadFormsKB.Siegel.ThetaGamma0
import QuadFormsKB.LocalDensity.General

open Complex Finset
open QuadFormsKB.Analysis (quadAt)

namespace QuadFormsKB.Siegel.SingularSeries

open QuadFormsKB.LocalDensity (repCount localDensity)

variable {n : ℕ}

/-- **The term $A_c(m)$ of the singular series**:
$A_c(m) = c^{-n}\sum_{0 \le a < c,\ \gcd(a,c) = 1}G_A(a, c)\,e(-am/c)$ for $c \ge 1$ (with $G_A$ = `gaussSum (gramMatrix Q) a c 0`),
and $A_0(m) = 0$. -/
@[kb "siegel1935" "singular series [unverified]"]
noncomputable def ssTerm (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) : ℂ :=
  if hc : c = 0 then 0 else
    haveI : NeZero c := ⟨hc⟩
    ((c : ℂ) ^ n)⁻¹ * ∑ a ∈ (Finset.range c).filter (fun a => Nat.Coprime a c),
      gaussSum (gramMatrix Q) (a : ℤ) c 0 * Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * (m : ℂ) / c))

theorem ssTerm_zero (Q : QuadForm ℤ n) (m : ℤ) : ssTerm Q m 0 = 0 := by simp [ssTerm]

/-! ### Gauss sums over `ZMod c` -/

/-- $G(a) = \sum_{\vec r \in (\mathbb{Z}/c)^n}\psi_c(a\,Q(\vec r))$, $\psi_c$ = `ZMod.stdAddChar`. -/
noncomputable def gz (Q : QuadForm ℤ n) (c : ℕ) [NeZero c] (a : ZMod c) : ℂ :=
  ∑ r : Fin n → ZMod c, ZMod.stdAddChar (a * Q.evalIn (ZMod c) r)

/-- A ring homomorphism commutes with evaluation of an integral form. -/
lemma map_evalIn {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (Q : QuadForm ℤ n)
    (x : Fin n → A) : f (Q.evalIn A x) = Q.evalIn B (fun i => f (x i)) := by
  simp [QuadForm.evalIn, map_sum, apply_ite]

lemma liftZ_cast {c : ℕ} [NeZero c] (r : Fin n → ZMod c) : (fun i => ((liftZ r i : ℤ) : ZMod c)) = r := by
  funext i; simp [liftZ]

lemma gaussSum_eq_gz (Q : QuadForm ℤ n) (c : ℕ) [NeZero c] (a : ℤ) :
    gaussSum (gramMatrix Q) a c 0 = gz Q c (a : ZMod c) := by
  unfold gaussSum gz
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : ((a : ZMod c) * Q.evalIn (ZMod c) r) = (((a * Q.eval (liftZ r) : ℤ)) : ZMod c) := by
    rw [Int.cast_mul, ← LocalDensity.evalIn_intCast_vec, liftZ_cast]
  rw [h1, ZMod.stdAddChar_coe, quadAt_gramMatrix]
  congr 1
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
  push_cast
  ring

lemma exp_neg_eq (c : ℕ) [NeZero c] (a : ℕ) (m : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * (m : ℂ) / c)) =
      ZMod.stdAddChar (-((a : ZMod c) * (m : ZMod c))) := by
  have : (-((a : ZMod c) * (m : ZMod c))) = (((-(a * m) : ℤ)) : ZMod c) := by push_cast; ring
  rw [this, ZMod.stdAddChar_coe]
  congr 1; push_cast; ring

/-- The summand $f_c(x) = G(x)\,\psi_c(-xm)$ on `ZMod c`. -/
noncomputable def fz (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) [NeZero c] (x : ZMod c) : ℂ :=
  gz Q c x * ZMod.stdAddChar (-(x * (m : ZMod c)))

/-- The coprime part $U(c) = \sum_{a < c,\ (a,c)=1} f_c(a)$. -/
noncomputable def uSum (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) [NeZero c] : ℂ :=
  ∑ a ∈ (Finset.range c).filter (fun a => Nat.Coprime a c), fz Q m c a

lemma ssTerm_eq (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) [NeZero c] :
    ssTerm Q m c = ((c : ℂ) ^ n)⁻¹ * uSum Q m c := by
  simp only [ssTerm, NeZero.ne c, ↓reduceDIte, uSum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [gaussSum_eq_gz, exp_neg_eq, fz]
  push_cast; rfl

theorem ssTerm_one (Q : QuadForm ℤ n) (m : ℤ) : ssTerm Q m 1 = 1 := by
  rw [ssTerm_eq, uSum]
  have : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  rw [this, Finset.sum_singleton, fz, gz]
  simp

/-! ### Sums over residues -/

lemma sum_range_eq_sum_zmod (c : ℕ) [NeZero c] (f : ZMod c → ℂ) :
    ∑ a ∈ Finset.range c, f (a : ZMod c) = ∑ x : ZMod c, f x := by
  refine Finset.sum_bij' (fun a _ => (a : ZMod c)) (fun x _ => x.val) (fun _ _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) (fun a ha => ?_) (fun x _ => ZMod.natCast_zmod_val x)
    (fun _ _ => rfl)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]

/-- **Orthogonality:** $\sum_{x \in \mathbb{Z}/c}f_c(x) = c\cdot\#\{\vec r : Q(\vec r) \equiv m \bmod c\}$. -/
lemma sum_fz (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) [NeZero c] :
    ∑ x : ZMod c, fz Q m c x =
      c * ((Finset.univ.filter fun r : Fin n → ZMod c => Q.evalIn (ZMod c) r = (m : ZMod c)).card : ℂ) := by
  classical
  simp only [fz, gz, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ r : Fin n → ZMod c, ∑ x : ZMod c,
      ZMod.stdAddChar (x * Q.evalIn (ZMod c) r) * ZMod.stdAddChar (-(x * (m : ZMod c))) =
      if Q.evalIn (ZMod c) r - (m : ZMod c) = 0 then (c : ℂ) else 0 := by
    intro r
    have h := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := c)) (Q.evalIn (ZMod c) r - (m : ZMod c))
      (ZMod.isPrimitive_stdAddChar c)
    rw [ZMod.card] at h
    rw [show (if Q.evalIn (ZMod c) r - (m : ZMod c) = 0 then (c : ℂ) else 0) =
      ((if Q.evalIn (ZMod c) r - (m : ZMod c) = 0 then c else 0 : ℕ) : ℂ) by split_ifs <;> simp, ← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [Finset.sum_congr rfl fun r _ => key r, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 3
  ext r; simp [sub_eq_zero]

lemma repCount_eq_card (Q : QuadForm ℤ n) (p k : ℕ) (m : ℤ) [NeZero (p ^ k)] :
    repCount Q p k m =
      (Finset.univ.filter fun r : Fin n → ZMod (p ^ k) => Q.evalIn (ZMod (p ^ k)) r = (m : ZMod (p ^ k))).card := by
  classical
  rw [repCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### Prime powers -/

section PrimePow

variable (p : ℕ) [hp : Fact p.Prime]

local instance (k : ℕ) : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

omit hp in
lemma pow_dvd_pow_succ' (k : ℕ) : p ^ k ∣ p ^ (k + 1) := pow_dvd_pow p (Nat.le_succ k)

/-- The reduction map $\mathbb{Z}/p^{k+1} 	o \mathbb{Z}/p^k$. -/
noncomputable abbrev red (k : ℕ) : ZMod (p ^ (k + 1)) →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow_succ' p k) (ZMod (p ^ k))

lemma stdAddChar_p_mul (k : ℕ) (y : ZMod (p ^ (k + 1))) :
    ZMod.stdAddChar ((p : ZMod (p ^ (k + 1))) * y) = ZMod.stdAddChar (red p k y) := by
  have hy : y = ((y.val : ℤ) : ZMod (p ^ (k + 1))) := by simp
  have e1 : (p : ZMod (p ^ (k + 1))) * y = (((p : ℤ) * y.val : ℤ) : ZMod (p ^ (k + 1))) := by
    conv_lhs => rw [hy]
    push_cast; ring
  have e2 : red p k y = ((y.val : ℤ) : ZMod (p ^ k)) := by
    conv_lhs => rw [hy]
    rw [map_intCast]
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast
  field_simp
  ring

/-- **Fibration:** $\sum_{ec r \in (\mathbb{Z}/p^{k+1})^n} g(ar{ec r}) = p^n\sum_{ec s \in (\mathbb{Z}/p^k)^n} g(ec s)$. -/
lemma sum_red_comp (k : ℕ) (g : (Fin n → ZMod (p ^ k)) → ℂ) :
    ∑ r : Fin n → ZMod (p ^ (k + 1)), g (fun i => red p k (r i)) = (p : ℂ) ^ n * ∑ s, g s := by
  classical
  set Φ : (Fin n → ZMod (p ^ (k + 1))) →+ (Fin n → ZMod (p ^ k)) :=
    (red p k).toAddMonoidHom.compLeft (Fin n) with hΦ
  have hΦapp : ∀ r, Φ r = fun i => red p k (r i) := fun r => rfl
  have hsurj : Function.Surjective Φ := by
    intro s
    refine ⟨fun i => ((s i).val : ZMod (p ^ (k + 1))), ?_⟩
    funext i
    rw [hΦapp]
    simp
  have hcomp := Finset.sum_comp (s := Finset.univ) g Φ
  rw [show (∑ r : Fin n → ZMod (p ^ (k + 1)), g (fun i => red p k (r i))) = ∑ r, g (Φ r) from rfl, hcomp]
  have himage : Finset.univ.image Φ = Finset.univ := by
    ext s; simp [hsurj s]
  set K := (Finset.univ.filter fun r => Φ r = 0).card with hK
  have hfib : ∀ s, (Finset.univ.filter fun r => Φ r = s).card = K := fun s =>
    AddMonoidHom.card_fiber_eq_of_mem_range Φ (hsurj s) (hsurj 0)
  have hKval : (K : ℂ) = (p : ℂ) ^ n := by
    have htot : (Finset.univ : Finset (Fin n → ZMod (p ^ (k + 1)))).card =
        ∑ s ∈ Finset.univ.image Φ, (Finset.univ.filter fun r => Φ r = s).card :=
      Finset.card_eq_sum_card_image Φ Finset.univ
    rw [himage, Finset.sum_congr rfl fun s _ => hfib s, Finset.sum_const, Finset.card_univ,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, ZMod.card, Fintype.card_fin,
      smul_eq_mul] at htot
    have hc : ((p ^ k : ℕ) : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (NeZero.ne (p ^ k)))
    have : ((p ^ (k + 1) : ℕ) : ℂ) ^ n = ((p ^ k : ℕ) : ℂ) ^ n * K := by
      exact_mod_cast htot
    rw [pow_succ, Nat.cast_mul, mul_pow] at this
    exact (mul_left_cancel₀ hc this).symm
  have : ∀ s ∈ Finset.univ.image Φ,
      (Finset.univ.filter fun r => Φ r = s).card • g s = (p : ℂ) ^ n * g s := by
    intro s _
    rw [hfib s, nsmul_eq_mul, hKval]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, himage]

lemma gz_p_mul (Q : QuadForm ℤ n) (k : ℕ) (b : ZMod (p ^ (k + 1))) :
    gz Q (p ^ (k + 1)) ((p : ZMod (p ^ (k + 1))) * b) = (p : ℂ) ^ n * gz Q (p ^ k) (red p k b) := by
  unfold gz
  have : ∀ r : Fin n → ZMod (p ^ (k + 1)),
      ZMod.stdAddChar ((p : ZMod (p ^ (k + 1))) * b * Q.evalIn (ZMod (p ^ (k + 1))) r) =
        ZMod.stdAddChar (red p k b * Q.evalIn (ZMod (p ^ k)) (fun i => red p k (r i))) := by
    intro r
    rw [mul_assoc, stdAddChar_p_mul, map_mul, map_evalIn]
  rw [Finset.sum_congr rfl fun r _ => this r]
  exact sum_red_comp p k (fun s => ZMod.stdAddChar (red p k b * Q.evalIn (ZMod (p ^ k)) s))

lemma fz_p_mul (Q : QuadForm ℤ n) (m : ℤ) (k b : ℕ) :
    fz Q m (p ^ (k + 1)) ((p * b : ℕ) : ZMod (p ^ (k + 1))) = (p : ℂ) ^ n * fz Q m (p ^ k) (b : ZMod (p ^ k)) := by
  unfold fz
  rw [Nat.cast_mul, gz_p_mul, map_natCast]
  have : ZMod.stdAddChar (-((p : ZMod (p ^ (k + 1))) * (b : ZMod (p ^ (k + 1))) * (m : ZMod (p ^ (k + 1))))) =
      ZMod.stdAddChar (-((b : ZMod (p ^ k)) * (m : ZMod (p ^ k)))) := by
    rw [show -((p : ZMod (p ^ (k + 1))) * (b : ZMod (p ^ (k + 1))) * (m : ZMod (p ^ (k + 1)))) =
      (p : ZMod (p ^ (k + 1))) * (-((b : ZMod (p ^ (k + 1))) * (m : ZMod (p ^ (k + 1))))) by ring,
      stdAddChar_p_mul]
    congr 1
    rw [map_neg, map_mul, map_natCast, map_intCast]
  rw [this]; ring

/-- The full sum $T(c) = \sum_{a < c}f_c(a)$. -/
noncomputable def tSum (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) [NeZero c] : ℂ :=
  ∑ a ∈ Finset.range c, fz Q m c a

lemma tSum_eq (Q : QuadForm ℤ n) (m : ℤ) (k : ℕ) :
    tSum Q m (p ^ k) = (p ^ k : ℕ) * (repCount Q p k m : ℂ) := by
  rw [tSum, sum_range_eq_sum_zmod (p ^ k) (fz Q m (p ^ k)), sum_fz, repCount_eq_card]

lemma tSum_succ (Q : QuadForm ℤ n) (m : ℤ) (k : ℕ) :
    tSum Q m (p ^ (k + 1)) = uSum Q m (p ^ (k + 1)) + (p : ℂ) ^ n * tSum Q m (p ^ k) := by
  rw [tSum, uSum, ← Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ (k + 1)))
    (fun a => Nat.Coprime a (p ^ (k + 1)))]
  congr 1
  rw [tSum, Finset.mul_sum]
  have hiff : ∀ a, ¬ Nat.Coprime a (p ^ (k + 1)) ↔ p ∣ a := by
    intro a
    rw [Nat.coprime_pow_right_iff (Nat.succ_pos k), Nat.coprime_comm, hp.out.coprime_iff_not_dvd, not_not]
  refine Finset.sum_nbij' (fun a => a / p) (fun b => p * b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, hiff] at ha
    simp only [Finset.mem_range]
    obtain ⟨b, rfl⟩ := ha.2
    rw [Nat.mul_div_cancel_left _ hp.out.pos]
    rw [pow_succ, mul_comm] at ha
    exact Nat.lt_of_mul_lt_mul_right ha.1
  · intro b hb
    simp only [Finset.mem_range] at hb
    simp only [Finset.mem_filter, Finset.mem_range, hiff]
    refine ⟨?_, dvd_mul_right p b⟩
    rw [pow_succ, mul_comm (p ^ k)]
    exact Nat.mul_lt_mul_of_pos_left hb hp.out.pos
  · intro a ha
    simp only [Finset.mem_filter, hiff] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro b _
    exact Nat.mul_div_cancel_left _ hp.out.pos
  · intro a ha
    simp only [Finset.mem_filter, hiff] at ha
    obtain ⟨b, rfl⟩ := ha.2
    rw [Nat.mul_div_cancel_left _ hp.out.pos, fz_p_mul]

lemma tSum_one (Q : QuadForm ℤ n) (m : ℤ) : tSum Q m 1 = uSum Q m 1 := by
  rw [tSum, uSum]
  congr 1

lemma sum_ssTerm_prime_pow_aux (Q : QuadForm ℤ n) (m : ℤ) (k : ℕ) :
    ∑ e ∈ Finset.range (k + 1), ssTerm Q m (p ^ e) = (((p : ℂ) ^ k) ^ n)⁻¹ * tSum Q m (p ^ k) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_pow, inv_one, one_mul]
    rw [ssTerm_eq, tSum_one]; simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, ssTerm_eq, tSum_succ]
    push_cast
    field_simp
    ring

/-- **Partial sums of the singular series at $p$:** $\sum_{e=0}^{k}A_{p^e}(m) = r_{p^k}(m)/p^{k(n-1)}$ ($n \ge 1$). -/
theorem sum_ssTerm_prime_pow (Q : QuadForm ℤ n) (hn : 1 ≤ n) (m : ℤ) (k : ℕ) :
    ∑ e ∈ Finset.range (k + 1), ssTerm Q m (p ^ e) =
      (((repCount Q p k m : ℝ) / (p : ℝ) ^ (k * (n - 1)) : ℝ) : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [sum_ssTerm_prime_pow_aux, tSum_eq]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [← pow_mul, mul_comm k n', pow_mul, pow_succ, ← pow_mul]
  field_simp
  ring

end PrimePow

/-! ### Multiplicativity -/

section Mul

/-- Reduction $\mathbb{Z}/c_1c_2 \to \mathbb{Z}/c_1$. -/
noncomputable abbrev red₁ (c₁ c₂ : ℕ) : ZMod (c₁ * c₂) →+* ZMod c₁ := ZMod.castHom (dvd_mul_right c₁ c₂) (ZMod c₁)
/-- Reduction $\mathbb{Z}/c_1c_2 \to \mathbb{Z}/c_2$. -/
noncomputable abbrev red₂ (c₁ c₂ : ℕ) : ZMod (c₁ * c₂) →+* ZMod c₂ := ZMod.castHom (dvd_mul_left c₂ c₁) (ZMod c₂)
/-- $u = c_2^{-1} \bmod c_1$. -/
noncomputable abbrev uu (c₁ c₂ : ℕ) : ZMod c₁ := (Nat.gcdB c₁ c₂ : ZMod c₁)
/-- $v = c_1^{-1} \bmod c_2$. -/
noncomputable abbrev vv (c₁ c₂ : ℕ) : ZMod c₂ := (Nat.gcdA c₁ c₂ : ZMod c₂)

variable {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] (h : Nat.Coprime c₁ c₂)

local instance : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩

include h

omit [NeZero c₁] [NeZero c₂] in
lemma cr_fst (x : ZMod (c₁ * c₂)) : (ZMod.chineseRemainder h x).1 = red₁ c₁ c₂ x := by
  show (ZMod.cast x : ZMod c₁ × ZMod c₂).1 = _
  rw [Prod.fst_zmod_cast]; rfl

omit [NeZero c₁] [NeZero c₂] in
lemma cr_snd (x : ZMod (c₁ * c₂)) : (ZMod.chineseRemainder h x).2 = red₂ c₁ c₂ x := by
  show (ZMod.cast x : ZMod c₁ × ZMod c₂).2 = _
  rw [Prod.snd_zmod_cast]; rfl

omit [NeZero c₁] [NeZero c₂] in
lemma bezout_int : (1 : ℤ) = c₁ * Nat.gcdA c₁ c₂ + c₂ * Nat.gcdB c₁ c₂ := by
  have := Nat.gcd_eq_gcd_ab c₁ c₂
  rw [show c₁.gcd c₂ = 1 from h] at this
  exact_mod_cast this

omit [NeZero c₁] [NeZero c₂] in
lemma isUnit_uu : IsUnit (uu c₁ c₂) := by
  have e := congrArg (fun z : ℤ => (z : ZMod c₁)) (bezout_int h)
  simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    zero_add] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact e.symm⟩

omit [NeZero c₁] [NeZero c₂] in
lemma isUnit_vv : IsUnit (vv c₁ c₂) := by
  have e := congrArg (fun z : ℤ => (z : ZMod c₂)) (bezout_int h)
  simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    add_zero] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact e.symm⟩

/-- **Splitting the additive character:** $\psi_{c_1c_2}(y) = \psi_{c_1}(u\bar y)\,\psi_{c_2}(v\bar y)$. -/
lemma stdAddChar_split (y : ZMod (c₁ * c₂)) :
    ZMod.stdAddChar y = ZMod.stdAddChar (uu c₁ c₂ * red₁ c₁ c₂ y) * ZMod.stdAddChar (vv c₁ c₂ * red₂ c₁ c₂ y) := by
  have hy : y = ((y.val : ℤ) : ZMod (c₁ * c₂)) := by simp
  set j : ℤ := (y.val : ℤ)
  have e1 : uu c₁ c₂ * red₁ c₁ c₂ y = ((Nat.gcdB c₁ c₂ * j : ℤ) : ZMod c₁) := by
    rw [hy, map_intCast]; push_cast; rfl
  have e2 : vv c₁ c₂ * red₂ c₁ c₂ y = ((Nat.gcdA c₁ c₂ * j : ℤ) : ZMod c₂) := by
    rw [hy, map_intCast]; push_cast; rfl
  rw [e1, e2, hy, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hb : (1 : ℂ) = c₁ * Nat.gcdA c₁ c₂ + c₂ * Nat.gcdB c₁ c₂ := by exact_mod_cast bezout_int h
  have h1 : (c₁ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c₁
  have h2 : (c₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c₂
  have key : 2 * (Real.pi : ℂ) * I * (j : ℂ) / ((c₁ * c₂ : ℕ) : ℂ) =
      2 * (Real.pi : ℂ) * I * (j : ℂ) * (c₁ * Nat.gcdA c₁ c₂ + c₂ * Nat.gcdB c₁ c₂) / ((c₁ * c₂ : ℕ) : ℂ) := by
    rw [← hb, mul_one]
  rw [key]
  push_cast
  field_simp
  ring

/-- The CRT equivalence on vectors. -/
noncomputable def crtVec : (Fin n → ZMod (c₁ * c₂)) ≃ (Fin n → ZMod c₁) × (Fin n → ZMod c₂) :=
  (Equiv.piCongrRight fun _ => (ZMod.chineseRemainder h).toEquiv).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

omit [NeZero c₁] [NeZero c₂] in
lemma crtVec_apply (r : Fin n → ZMod (c₁ * c₂)) :
    crtVec h r = (fun i => red₁ c₁ c₂ (r i), fun i => red₂ c₁ c₂ (r i)) := by
  ext i
  · exact cr_fst h (r i)
  · exact cr_snd h (r i)

lemma gz_mul (Q : QuadForm ℤ n) (x : ZMod (c₁ * c₂)) :
    gz Q (c₁ * c₂) x = gz Q c₁ (uu c₁ c₂ * red₁ c₁ c₂ x) * gz Q c₂ (vv c₁ c₂ * red₂ c₁ c₂ x) := by
  unfold gz
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_equiv (crtVec h) (fun _ => by simp) fun r _ => ?_
  rw [crtVec_apply h, stdAddChar_split h, map_mul (red₁ c₁ c₂), map_mul (red₂ c₁ c₂), map_evalIn (red₁ c₁ c₂),
    map_evalIn (red₂ c₁ c₂), mul_assoc, mul_assoc]

lemma fz_mul (Q : QuadForm ℤ n) (m : ℤ) (x : ZMod (c₁ * c₂)) :
    fz Q m (c₁ * c₂) x = fz Q m c₁ (uu c₁ c₂ * red₁ c₁ c₂ x) * fz Q m c₂ (vv c₁ c₂ * red₂ c₁ c₂ x) := by
  unfold fz
  rw [gz_mul h, stdAddChar_split h (-(x * (m : ZMod (c₁ * c₂))))]
  simp only [map_neg, map_mul, map_intCast]
  ring_nf

omit [NeZero c₁] [NeZero c₂] h in
lemma uSum_eq_units (Q : QuadForm ℤ n) (m : ℤ) (c : ℕ) [NeZero c] :
    uSum Q m c = ∑ x ∈ Finset.univ.filter (fun x : ZMod c => IsUnit x), fz Q m c x := by
  classical
  rw [uSum]
  refine Finset.sum_bij' (fun a _ => (a : ZMod c)) (fun x _ => x.val) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    simp [(ZMod.isUnit_iff_coprime a c).mpr ha.2]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact hx
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha.1]
  · intro x _; exact ZMod.natCast_zmod_val x

lemma uSum_mul (Q : QuadForm ℤ n) (m : ℤ) :
    uSum Q m (c₁ * c₂) = uSum Q m c₁ * uSum Q m c₂ := by
  classical
  rw [uSum_eq_units Q m (c₁ * c₂), uSum_eq_units Q m c₁, uSum_eq_units Q m c₂, Finset.sum_mul_sum, ← Finset.sum_product',
    ← Finset.filter_product]
  set ι : ZMod (c₁ * c₂) ≃ ZMod c₁ × ZMod c₂ :=
    (ZMod.chineseRemainder h).toEquiv.trans
      (Equiv.prodCongr (Units.mulLeft (isUnit_uu h).unit) (Units.mulLeft (isUnit_vv h).unit)) with hι
  have hιapp : ∀ x, ι x = (uu c₁ c₂ * red₁ c₁ c₂ x, vv c₁ c₂ * red₂ c₁ c₂ x) := by
    intro x
    simp only [hι, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Units.mulLeft_apply,
      IsUnit.unit_spec, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, cr_fst, cr_snd]
  refine Finset.sum_equiv ι (fun x => ?_) fun x _ => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, hιapp]
    rw [IsUnit.mul_iff, IsUnit.mul_iff]
    simp only [isUnit_uu h, isUnit_vv h, true_and]
    rw [← cr_fst h, ← cr_snd h, ← Prod.isUnit_iff, MulEquiv.isUnit_map (ZMod.chineseRemainder h)]
  · rw [hιapp, fz_mul h]

end Mul

theorem ssTerm_mul (Q : QuadForm ℤ n) (m : ℤ) {c₁ c₂ : ℕ} (h : Nat.Coprime c₁ c₂) :
    ssTerm Q m (c₁ * c₂) = ssTerm Q m c₁ * ssTerm Q m c₂ := by
  rcases Nat.eq_zero_or_pos c₁ with rfl | h1
  · simp [ssTerm_zero]
  rcases Nat.eq_zero_or_pos c₂ with rfl | h2
  · simp [ssTerm_zero]
  have : NeZero c₁ := ⟨h1.ne'⟩
  have : NeZero c₂ := ⟨h2.ne'⟩
  rw [ssTerm_eq, ssTerm_eq, ssTerm_eq, uSum_mul h]
  push_cast
  rw [mul_pow, mul_inv]
  ring

/-! ### The Euler product -/

/-- **The local factor of the singular series is the local density:** $\sum_{e \ge 0}A_{p^e}(m) = \beta_p(m)$ (for $Q$
nondegenerate, $n \ge 1$, $m \ne 0$, the series being summable). -/
theorem tsum_ssTerm_prime_pow {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {m : ℤ} (hm : m ≠ 0)
    (p : ℕ) [Fact p.Prime] (hs : Summable fun e => ssTerm Q m (p ^ e)) :
    ∑' e, ssTerm Q m (p ^ e) = ((localDensity Q p m : ℝ) : ℂ) := by
  have h1 : Filter.Tendsto (fun k => ∑ e ∈ Finset.range (k + 1), ssTerm Q m (p ^ e)) Filter.atTop
      (nhds (∑' e, ssTerm Q m (p ^ e))) :=
    hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto (fun k => ∑ e ∈ Finset.range (k + 1), ssTerm Q m (p ^ e)) Filter.atTop
      (nhds ((localDensity Q p m : ℝ) : ℂ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [LocalDensity.localDensity_eventually_eq Q hQ p m hm] with k hk
    rw [sum_ssTerm_prime_pow p Q hn m k, hk]
  exact tendsto_nhds_unique h1 h2

/-- **The singular series is the Euler product of the local densities:** for $Q$ nondegenerate, $n \ge 4$, $m \ne 0$,
if $\sum_c A_c(m)$ is summable then $\sum_{c \ge 1}A_c(m) = \prod_p\beta_p(m)$ (`eulerProduct`). *Proof:* $A$ is
multiplicative with $A_1 = 1$ (`ssTerm_one`, `ssTerm_mul`), so Mathlib's Euler product
(`EulerProduct.eulerProduct_hasProd`) gives $\sum_c A_c(m) = \prod_p\sum_e A_{p^e}(m)$, and
$\sum_e A_{p^e}(m) = \beta_p(m)$ (`tsum_ssTerm_prime_pow`). -/
@[kb "siegel1935" "singular series = product of local densities [unverified]"]
theorem hasSum_ssTerm {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {m : ℤ} (hm : m ≠ 0)
    (hsum : Summable (ssTerm Q m)) : HasSum (ssTerm Q m) ((eulerProduct Q m : ℝ) : ℂ) := by
  have hE := EulerProduct.eulerProduct_hasProd (f := ssTerm Q m) (ssTerm_one Q m)
    (fun h => ssTerm_mul Q m h) (summable_norm_iff.mpr hsum) (ssTerm_zero Q m)
  have hfac : ∀ p : Nat.Primes, ∑' e, ssTerm Q m ((p : ℕ) ^ e) = ((eulerFactor Q m p : ℝ) : ℂ) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    exact tsum_ssTerm_prime_pow hQ (by omega) hm p
      (hsum.comp_injective (Nat.pow_right_injective p.2.two_le))
  simp only [hfac] at hE
  have hR := (hasProd_eulerProduct Q hQ hn hm).map Complex.ofRealHom Complex.continuous_ofReal
  have := hE.unique hR
  rw [Complex.ofRealHom_eq_coe] at this
  rw [← this]
  exact hsum.hasSum

end QuadFormsKB.Siegel.SingularSeries
