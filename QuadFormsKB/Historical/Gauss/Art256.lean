import QuadFormsKB.Historical.Gauss.Example161

/-!
# The three classes of determinant $D \equiv 5 \pmod 8$ (*Disq. Arith.* Art. 256 VI, Art. 259 II)

(Gauss, *Disquisitiones Arithmeticae* (1801), Art. 256 VI and Art. 259 II).

Let $D \equiv 5 \pmod 8$ (any sign; $D$ is then automatically not a square). Gauss's forms
$K = (1, 0, -D)$, $K' = (4, 1, (1-D)/4)$, $K'' = (4, 3, (9-D)/4)$ (library `gaussForm a b c` $= [a, 2b, c]$, discriminant
$4D$) are properly primitive, because $(1-D)/4$ and $(9-D)/4$ are odd. We work in the class group
`Composition.FormClass (4 * D)`.

**Proved** (`art256_order_three`), unconditionally: $K'^2 = K''$, $K' K'' = K = 1$, $K'^3 = 1$, and hence either
$K = K' = K''$ (all three classes coincide) or $K, K', K''$ are three pairwise distinct classes.

The proof writes $D = 8k + 5$ and uses explicit proper equivalences to concordant forms (Dirichlet composition)
with symbolic coefficients.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition _root_.QuadFormsKB.Composition.FormClass

/-- For $D \equiv 5 \pmod 8$, the discriminant $4D$ satisfies the hypotheses of the class group
(it is nonzero and $\equiv 0 \pmod 4$). -/
theorem nonzeroDisc_four_mul_of_mod_eight (D : ℤ) (hD : D % 8 = 5) : NonzeroDisc (4 * D) :=
  ⟨by omega, by omega⟩

/-- **The primitive form $(a, b, c)$ of determinant $D$** as an element of `PrimForm (4 * D)`, given a
primitivity certificate. -/
def gpfD (D a b c : ℤ) [NonzeroDisc (4 * D)] (hp : ∀ d : ℤ, d ∣ a → d ∣ 2 * b → d ∣ c → IsUnit d)
    (hd : b ^ 2 - a * c = D) : PrimForm (4 * D) :=
  ⟨gaussForm a b c, by
    intro d h1 h2 h3
    simp only [gaussForm, a_mk, b_mk, c_mk] at h1 h2 h3
    exact hp d h1 h2 h3, by rw [disc_gaussForm]; unfold gaussDet; rw [hd]⟩

/-- **The class of Gauss's principal form $K = (1, 0, -D)$** in `FormClass (4 * D)`. -/
def classK (D : ℤ) [NonzeroDisc (4 * D)] : FormClass (4 * D) :=
  FormClass.mk (gpfD D 1 0 (-D) (fun d h _ _ => isUnit_of_dvd_one h) (by ring))

/-- **The class of Gauss's form $K' = (4, 1, (1-D)/4)$** for $D \equiv 5 \pmod 8$. -/
def classK1 (D : ℤ) (hD : D % 8 = 5) [NonzeroDisc (4 * D)] : FormClass (4 * D) :=
  FormClass.mk (gpfD D 4 1 ((1 - D) / 4)
    (fun d h1 h2 h3 => isUnit_of_dvd_one (by
      have e : (1 : ℤ) = 2 * (-(((1 - D) / 4 - 1) / 2)) + (1 - D) / 4 := by omega
      rw [e]; exact dvd_add (Dvd.dvd.mul_right (by simpa using h2) _) h3)) (by omega))

/-- **The class of Gauss's form $K'' = (4, 3, (9-D)/4)$** for $D \equiv 5 \pmod 8$. -/
def classK2 (D : ℤ) (hD : D % 8 = 5) [NonzeroDisc (4 * D)] : FormClass (4 * D) :=
  FormClass.mk (gpfD D 4 3 ((9 - D) / 4)
    (fun d h1 h2 h3 => isUnit_of_dvd_one (by
      have e : (1 : ℤ) = 4 * (((9 - D) / 4 - 1) / 2) + 6 * (-(((9 - D) / 4 - 1) / 2)) + (9 - D) / 4 := by omega
      rw [e]; exact dvd_add (dvd_add (Dvd.dvd.mul_right h1 _) (Dvd.dvd.mul_right (by simpa using h2) _)) h3))
    (by omega))

/-- **Product of two classes through concordant representatives** (helper). -/
theorem cls_mul {D : ℤ} [NonzeroDisc (4 * D)] (P Q R : PrimForm (4 * D)) (g1 g2 : BinQF)
    (hc : Concordant g1 g2) (h1 : SLEquiv P.1 g1) (h2 : SLEquiv Q.1 g2)
    (h3 : SLEquiv (Composition.comp g1 g2) R.1) : FormClass.mk P * FormClass.mk Q = FormClass.mk R := by
  have e1 := mk_ofEquiv P h1
  have e2 := mk_ofEquiv Q h2
  calc FormClass.mk P * FormClass.mk Q
      = FormClass.mk (ofEquiv P h1) * FormClass.mk (ofEquiv Q h2) := by rw [e1, e2]
    _ = FormClass.mk (PrimForm.comp (ofEquiv P h1) (ofEquiv Q h2) hc) := mk_mul_mk _ _ hc
    _ = FormClass.mk R := mk_eq_mk.2 h3

local macro "nsD" : tactic =>
  `(tactic| (simp only [gaussForm, a_mk, b_mk, c_mk]; ring))

/-- Concordant forms for $K'^2$ (with $D = 8k+5$, $m = 2k+1$):
$[4,\ 8k+2,\ 4k^2-1]$ and $[-m,\ 8k+2,\ 4(1-2k)]$. -/
theorem concordant_sq (k : ℤ) :
    Concordant (BinQF.mk 4 (8 * k + 2) (4 * k ^ 2 - 1))
      (BinQF.mk (-(2 * k + 1)) (8 * k + 2) (4 * (1 - 2 * k))) := by
  refine ⟨by simp only [a_mk]; omega, rfl, ?_, ?_⟩
  · simp only [BinQF.disc, a_mk, b_mk, c_mk]; ring
  · exact ⟨-(2 * k - 1), by simp only [BinQF.disc, a_mk, b_mk, c_mk]; ring⟩

/-- Their composition is $[-4m,\ 8k+2,\ 1-2k]$. -/
theorem comp_sq (k : ℤ) :
    Composition.comp (BinQF.mk 4 (8 * k + 2) (4 * k ^ 2 - 1))
      (BinQF.mk (-(2 * k + 1)) (8 * k + 2) (4 * (1 - 2 * k))) =
      BinQF.mk (-(4 * (2 * k + 1))) (8 * k + 2) (1 - 2 * k) := by
  unfold Composition.comp
  simp only [a_mk, b_mk, c_mk, BinQF.disc]
  congr 1
  · ring
  · apply Int.ediv_eq_of_eq_mul_right (by omega)
    ring

/-- Concordant forms for $K' K''$: $[4,\ 2,\ -m]$ and $[-m,\ 2,\ 4]$. -/
theorem concordant_prod (k : ℤ) :
    Concordant (BinQF.mk 4 2 (-(2 * k + 1))) (BinQF.mk (-(2 * k + 1)) 2 4) := by
  refine ⟨by simp only [a_mk]; omega, rfl, ?_, ?_⟩
  · simp only [BinQF.disc, a_mk, b_mk, c_mk]; ring
  · exact ⟨1, by simp only [BinQF.disc, a_mk, b_mk, c_mk]; ring⟩

/-- Their composition is $[-4m,\ 2,\ 1]$. -/
theorem comp_prod (k : ℤ) :
    Composition.comp (BinQF.mk 4 2 (-(2 * k + 1))) (BinQF.mk (-(2 * k + 1)) 2 4) =
      BinQF.mk (-(4 * (2 * k + 1))) 2 1 := by
  unfold Composition.comp
  simp only [a_mk, b_mk, c_mk, BinQF.disc]
  congr 1
  · ring
  · apply Int.ediv_eq_of_eq_mul_right (by omega)
    ring

/-- **The three classes of determinant $D \equiv 5 \pmod 8$ form a group of order dividing three**
(*Disq. Arith.* Art. 256 VI, Art. 259 II). For an integer $D \equiv 5 \pmod 8$
(any sign) and Gauss's forms $K = (1, 0, -D)$, $K' = (4, 1, (1-D)/4)$, $K'' = (4, 3, (9-D)/4)$ (library
$[a, 2b, c]$, discriminant $4D$, properly primitive) with classes in `Composition.FormClass (4 * D)`:

1. $K'^2 = K''$ (Art. 256 VI, "$K' + K' = K''$");
2. $K' K'' = K$, and $K$ is the identity class ($K'$ and $K''$ are mutually inverse);
3. $K'^3 = 1$;
4. either $K' = K'' = 1$ (all three classes coincide) or $K' \ne 1$, $K'' \ne 1$, $K' \ne K''$ (three distinct classes).

Gauss writes the group additively; here it is the multiplicative class group. The instance
`NonzeroDisc (4 * D)` is automatic from $D \equiv 5 \pmod 8$ (`nonzeroDisc_four_mul_of_mod_eight`); it is a
proposition, so the choice is irrelevant. Unconditional; no differences from the source. -/
@[kb "gauss1801" "Art. 256"]
theorem art256_order_three (D : ℤ) (hD : D % 8 = 5) [NonzeroDisc (4 * D)] :
    classK1 D hD ^ 2 = classK2 D hD ∧ classK1 D hD * classK2 D hD = classK D ∧ classK D = 1 ∧
    classK1 D hD ^ 3 = 1 ∧
    ((classK1 D hD = 1 ∧ classK2 D hD = 1) ∨
      (classK1 D hD ≠ 1 ∧ classK2 D hD ≠ 1 ∧ classK1 D hD ≠ classK2 D hD)) := by
  obtain ⟨k, rfl⟩ : ∃ k, D = 8 * k + 5 := ⟨D / 8, by omega⟩
  have hc1 : (1 - (8 * k + 5)) / 4 = -(2 * k) - 1 := by omega
  have hc2 : (9 - (8 * k + 5)) / 4 = 1 - 2 * k := by omega
  -- equivalences
  have a1 : SLEquiv (gaussForm 4 1 ((1 - (8 * k + 5)) / 4)) (BinQF.mk 4 (8 * k + 2) (4 * k ^ 2 - 1)) := by
    rw [hc1]; exact sl_of _ _ 1 k 0 1 (by norm_num) (by nsD) (by nsD) (by nsD)
  have a2 : SLEquiv (gaussForm 4 1 ((1 - (8 * k + 5)) / 4))
      (BinQF.mk (-(2 * k + 1)) (8 * k + 2) (4 * (1 - 2 * k))) := by
    rw [hc1]; exact sl_of _ _ 0 (-1) 1 (-2) (by norm_num) (by nsD) (by nsD) (by nsD)
  have a3 : SLEquiv (BinQF.mk (-(4 * (2 * k + 1))) (8 * k + 2) (1 - 2 * k))
      (gaussForm 4 3 ((9 - (8 * k + 5)) / 4)) := by
    rw [hc2]; exact sl_of _ _ 1 0 2 1 (by norm_num) (by nsD) (by nsD) (by nsD)
  have b1 : SLEquiv (gaussForm 4 1 ((1 - (8 * k + 5)) / 4)) (BinQF.mk 4 2 (-(2 * k + 1))) := by
    rw [hc1]; exact sl_of _ _ 1 0 0 1 (by norm_num) (by nsD) (by nsD) (by nsD)
  have b2 : SLEquiv (gaussForm 4 3 ((9 - (8 * k + 5)) / 4)) (BinQF.mk (-(2 * k + 1)) 2 4) := by
    rw [hc2]; exact sl_of _ _ (-1) (-1) 1 0 (by norm_num) (by nsD) (by nsD) (by nsD)
  have b3 : SLEquiv (BinQF.mk (-(4 * (2 * k + 1))) 2 1) (gaussForm 1 0 (-(8 * k + 5))) :=
    sl_of _ _ 0 (-1) 1 1 (by norm_num) (by nsD) (by nsD) (by nsD)
  have h1 : classK1 (8 * k + 5) hD ^ 2 = classK2 (8 * k + 5) hD := by
    rw [pow_two]
    exact cls_mul _ _ _ _ _ (concordant_sq k) a1 a2 (by rw [comp_sq]; exact a3)
  have h2 : classK1 (8 * k + 5) hD * classK2 (8 * k + 5) hD = classK (8 * k + 5) :=
    cls_mul _ _ _ _ _ (concordant_prod k) b1 b2 (by rw [comp_prod]; exact b3)
  have h0 : classK (8 * k + 5) = 1 := by
    unfold classK
    rw [mk_eq_one_iff]
    exact ⟨1, 0, by simp [gpfD, eval_gaussForm]⟩
  rw [h0] at h2
  refine ⟨h1, by rw [h2, h0], h0, ?_, ?_⟩
  · rw [pow_succ', h1, h2]
  · by_cases ha : classK1 (8 * k + 5) hD = 1
    · exact Or.inl ⟨ha, by rw [← h1, ha]; simp⟩
    · refine Or.inr ⟨ha, ?_, ?_⟩
      · intro hb
        rw [hb, mul_one] at h2
        exact ha h2
      · intro hab
        apply ha
        have : classK1 (8 * k + 5) hD * classK1 (8 * k + 5) hD = classK1 (8 * k + 5) hD * 1 := by
          rw [mul_one, ← pow_two, h1, ← hab]
        exact mul_left_cancel this

end QuadFormsKB.Historical.Gauss
