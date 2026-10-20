/-
# Bridge for the explicit results: the $\mathbb{Q}$ layer is the DVR layer at $R = \mathbb{Z}_p$

**Layer:** bridge between `Explicit.lean`/`Table2.lean` ($\mathbb{Q}$) and `DVRExplicit.lean`/`DVRTable2.lean`
(DVR), with $Q_p = $ `Q.map (Int.castRingHom ℤ_[p])`. **Proves** the dictionary
- `repCountOf_isZeroType_eq_padic`, `repCountOf_nonZero_eq_padic`: Zero-type and non-Zero-type counts agree;
- `isLocallyRepresentedAt_iff_padic` (Def. 3.5), `isPStable_iff_padic` (Def. 3.6), `isotropicIn_iff_padic`
  (Def. 3.7: $Q$ over $\mathbb{Q}_p$ vs. $Q_p$ over $\mathbb{Q}_p = \mathrm{Frac}(\mathbb{Z}_p)$);
- `localDensityOf_nonZero_eq_padic` (Def. 5.1), `localConstC_eq_padic` ((5.8), p. 370);
and, as corollaries, the $\mathbb{Q}$ results re-derived from the DVR ones: Lemma 3.8 corrected
(`anisotropic_iff_zeroType_of_padic`), Cor. 3.8.2 (`card_rep_mul_pow_sq_of_padic`, with $A = \mathbb{Z}$) and
(5.6) (`localDensity_le_mul_sq_of_padic`). **Depends on** `Bridge.lean`, `DVRTable2.lean`.
-/
import QuadFormsKB.LocalDensity.Bridge
import QuadFormsKB.LocalDensity.DVRTable2

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **Counts of a type defined by divisibility of coordinates agree over $\mathbb{Z}/p^k$ and $\mathbb{Z}_p/p^k$**:
the Zero-type and non-Zero-type counts (Def. 3.1, p. 358) of $Q$ and of $Q_p$ are equal. -/
theorem repCountOf_type_eq_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (k : ℕ) (m : ℤ) :
    repCountOf Q p k m (IsZeroType p k) =
        DVR.repCountOf (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) k (m : ℤ_[p])
          (DVR.IsZeroType (p : ℤ_[p]) k) ∧
      repCountOf Q p k m (fun x => ¬ IsZeroType p k x) =
        DVR.repCountOf (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) k (m : ℤ_[p])
          (fun x => ¬ DVR.IsZeroType (p : ℤ_[p]) k x) := by
  set e := padicQuotEquivZModPow p k
  let E : (Fin n → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ k}) ≃ (Fin n → ZMod (p ^ k)) :=
    Equiv.piCongrRight fun _ => e.toEquiv
  have hE : ∀ x i, E x i = e (x i) := fun _ _ => rfl
  have hval : ∀ x, (Q.map (Int.castRingHom ℤ_[p])).evalIn _ x =
      Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k}) (m : ℤ_[p]) ↔
      Q.evalIn (ZMod (p ^ k)) (E x) = (m : ZMod (p ^ k)) := by
    intro x
    rw [evalIn_map_intCast, map_intCast, ← e.injective.eq_iff,
      show e (Q.evalIn _ x) = Q.evalIn _ (E x) from evalIn_intForm_map e.toRingHom Q x, map_intCast]
  have hp : e (Ideal.Quotient.mk _ (p : ℤ_[p])) = (p : ZMod (p ^ k)) := by
    rw [map_natCast, map_natCast]
  have hdvd : ∀ x i, Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ k}) (p : ℤ_[p]) ∣ x i ↔
      (p : ZMod (p ^ k)) ∣ E x i := by
    intro x i
    rw [hE, ← hp]
    exact (map_dvd_iff e).symm
  constructor
  · refine (Nat.card_congr (E.subtypeEquiv fun x => ?_)).symm
    simp only [DVR.IsZeroType, IsZeroType, hval, hdvd]
  · refine (Nat.card_congr (E.subtypeEquiv fun x => ?_)).symm
    simp only [DVR.IsZeroType, IsZeroType, hval, hdvd]

/-- Non-Zero-type counts agree (`repCountOf_type_eq_padic`). -/
theorem repCountOf_nonZero_eq_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (k : ℕ) (m : ℤ) :
    repCountOf Q p k m (fun x => ¬ IsZeroType p k x) =
      DVR.repCountOf (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) k (m : ℤ_[p])
        (fun x => ¬ DVR.IsZeroType (p : ℤ_[p]) k x) :=
  (repCountOf_type_eq_padic Q p k m).2

/-- **Def. 3.5 agrees** (Hanke 2004, p. 362): locally represented at $p$ over $\mathbb{Z}$ iff over $\mathbb{Z}_p$. -/
@[kb "hanke2004" "Def. 3.5, p. 362"]
theorem isLocallyRepresentedAt_iff_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    IsLocallyRepresentedAt Q p m ↔
      DVR.IsLocallyRepresentedAt (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) (m : ℤ_[p]) := by
  unfold IsLocallyRepresentedAt DVR.IsLocallyRepresentedAt
  simp only [(repCount_eq_padic Q p ∅ _ m).1]

/-- **Def. 3.6 agrees** (Hanke 2004, p. 362): $p$-stable over $\mathbb{Z}$ iff over $\mathbb{Z}_p$. -/
@[kb "hanke2004" "Def. 3.6, p. 362"]
theorem isPStable_iff_padic (Q : QuadForm ℤ n) (S₀ : Finset (Fin n)) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    IsPStable Q S₀ p m ↔
      DVR.IsPStable (Q.map (Int.castRingHom ℤ_[p])) S₀ (p : ℤ_[p]) (m : ℤ_[p]) := by
  unfold IsPStable DVR.IsPStable
  rw [isLocallyRepresentedAt_iff_padic]
  have hc : ∀ j : ℕ, (((p : ℤ) ^ j * m : ℤ) : ℤ_[p]) = (p : ℤ_[p]) ^ j * (m : ℤ_[p]) := fun j => by
    push_cast; ring
  simp only [repCountOf_nonZero_eq_padic, hc]

/-- **Def. 3.7 agrees** (Hanke 2004, p. 363): $Q$ is isotropic over $\mathbb{Q}_p$ iff $Q_p$ is (with $\mathbb{Q}_p$ the
fraction field of $\mathbb{Z}_p$). -/
@[kb "hanke2004" "Def. 3.7, p. 363"]
theorem isotropicIn_iff_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] :
    Q.IsotropicIn ℚ_[p] ↔ (Q.map (Int.castRingHom ℤ_[p])).IsotropicIn ℚ_[p] := by
  unfold QuadForm.IsotropicIn
  simp only [evalIn_map_intCast]

/-- **Def. 5.1 agrees** (Hanke 2004, p. 368) for the non-Zero-type density. -/
theorem localDensityOf_nonZero_eq_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    localDensityOf Q p m (fun k x => ¬ IsZeroType p k x) =
      DVR.localDensityOf (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) (m : ℤ_[p])
        (fun k x => ¬ DVR.IsZeroType (p : ℤ_[p]) k x) := by
  unfold localDensityOf DVR.localDensityOf
  congr 1
  funext k
  rw [repCountOf_nonZero_eq_padic, q_padicInt]

/-- **The local constant agrees** (Hanke 2004, (5.8), p. 370): $C_p(T')$ over $\mathbb{Z}$ is $C_p(T')$ over $\mathbb{Z}_p$. -/
@[kb "hanke2004" "(5.8), p. 370"]
theorem localConstC_eq_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (T : ℤ) :
    localConstC Q p T = DVR.localConstC (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) (T : ℤ_[p]) := by
  unfold localConstC DVR.localConstC
  rw [localDensityOf_nonZero_eq_padic, localDensity_eq_padic, q_padicInt]
  push_cast
  rfl

/-! ### The $\mathbb{Q}$ results as specializations of the DVR results -/

/-- **Lemma 3.8 (corrected) over $\mathbb{Q}$ from the DVR version** at $R = \mathbb{Z}_p$ (no normal form needed):
the statement of `anisotropic_iff_zeroType`, derived from `DVR.anisotropic_iff_zeroType`. -/
theorem anisotropic_iff_zeroType_of_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (S₀ : Finset (Fin n)) (m : ℤ) (hm : IsPStable Q S₀ p m) :
    ¬ Q.IsotropicIn ℚ_[p] ↔
      ∀ᶠ k in Filter.atTop,
        repCount Q p k ((p : ℤ) ^ 2 * m) = repCountOf Q p k ((p : ℤ) ^ 2 * m) (IsZeroType p k) := by
  rw [isotropicIn_iff_padic, DVR.anisotropic_iff_zeroType ℚ_[p] _ (p : ℤ_[p]) PadicInt.irreducible_p S₀
    (m : ℤ_[p]) ((isPStable_iff_padic Q S₀ p m).1 hm)]
  have hc : (((p : ℤ) ^ 2 * m : ℤ) : ℤ_[p]) = (p : ℤ_[p]) ^ 2 * (m : ℤ_[p]) := by push_cast; ring
  simp only [(repCount_eq_padic Q p ∅ _ _).1, (repCountOf_type_eq_padic Q p _ _).1, hc]

/-- **Cor. 3.8.2 over $\mathbb{Q}$ from the DVR version** with $A = \mathbb{Z} \to R = \mathbb{Z}_p$: the statement of
`card_rep_mul_pow_sq` (no normal form needed), derived from `DVR.card_rep_mul_pow_sq`. -/
theorem card_rep_mul_pow_sq_of_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (S₀ : Finset (Fin n))
    (haniso : ¬ Q.IsotropicIn ℚ_[p]) (m : ℤ) (hm : IsPStable Q S₀ p m) (e : ℕ) :
    Set.ncard {x : Fin n → ℤ | Q.eval x = (p : ℤ) ^ (2 * e) * m} =
      Set.ncard {x : Fin n → ℤ | Q.eval x = m} :=
  DVR.card_rep_mul_pow_sq ℚ_[p] (Int.castRingHom ℤ_[p]) Q (p : ℤ) (p : ℤ_[p]) PadicInt.irreducible_p
    (by simp) (fun a ha => by simpa using (padic_pow_dvd_int_iff p 1 a).1 (by simpa using ha)) S₀
    ((isotropicIn_iff_padic Q p).not.1 haniso) m ((isPStable_iff_padic Q S₀ p m).1 hm) e

/-- **(5.6) over $\mathbb{Q}$ from the DVR version** at $R = \mathbb{Z}_p$: the statement of
`localDensity_le_mul_sq`, derived from `DVR.localDensity_le_mul_sq` (with $2 \ne 0$ in $\mathbb{Z}_p$). -/
theorem localDensity_le_mul_sq_of_padic (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    localDensity Q p m ≤ (p : ℝ) ^ (n - 2) * localDensity Q p ((p : ℤ) ^ 2 * m) := by
  have hQp : (Q.map (Int.castRingHom ℤ_[p])).Nondegenerate := by
    unfold QuadForm.Nondegenerate at hQ ⊢
    have : (Q.map (Int.castRingHom ℤ_[p])).hessian = Q.hessian.map (Int.castRingHom ℤ_[p]) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact_mod_cast hQ
  have h := DVR.localDensity_le_mul_sq _ hQp hn (p : ℤ_[p]) PadicInt.irreducible_p two_ne_zero
    (m : ℤ_[p]) (by exact_mod_cast hm)
  have hc : (((p : ℤ) ^ 2 * m : ℤ) : ℤ_[p]) = (p : ℤ_[p]) ^ 2 * (m : ℤ_[p]) := by push_cast; ring
  rwa [← localDensity_eq_padic, q_padicInt, ← hc, ← localDensity_eq_padic] at h

end QuadFormsKB.LocalDensity
