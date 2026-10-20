/-
# Local densities: $\mathbb{Z}/p^k$ versus $\mathbb{Z}_p/p^k$

**Layer:** bridge ($\mathbb{Q}$ ↔ DVR at $R = \mathbb{Z}_p$). **Proves** $q(\mathbb{Z}_p) = p$ (`q_padicInt`),
$\mathbb{Z}_p/p^k \cong \mathbb{Z}/p^k$ (`padicQuotEquivZModPow`), that counts and Good-type counts agree
(`repCount_eq_padic`, Hanke 2004, §2, p. 356), that the printed normal form transfers (`isJordanForm_padic`,
(2.3), p. 355), and Lemma 3.2 over $\mathbb{Q}$ for forms in normal form (`repCountGood_add`, eq. (3.1), p. 358)
from `DVR.repCountGood_add`. **Depends on** `Lemma32.lean`. The full dictionary (normal forms, densities) is
`Bridge.lean`.
-/
import QuadFormsKB.LocalDensity.Lemma32

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **The residue field of $\mathbb{Z}_p$ has $p$ elements:** `DVR.q ℤ_[p] = p`. -/
@[kb "serre1973" "Ch. II §1 [unverified]"]
theorem q_padicInt (p : ℕ) [Fact p.Prime] : DVR.q ℤ_[p] = p := by
  unfold DVR.q
  rw [Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]

/-- **$\mathbb{Z}_p/p^k \cong \mathbb{Z}/p^k$** as rings (from `PadicInt.toZModPow`, its kernel
`PadicInt.ker_toZModPow`, and surjectivity of every ring map onto `ZMod`). Valid for all `k ≥ 0`. -/
noncomputable def padicQuotEquivZModPow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ k} ≃+* ZMod (p ^ k) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow k)))

/-- **Evaluation of an integral form commutes with ring maps:** $f(Q(\vec{x})) = Q(f(\vec{x}))$. -/
theorem evalIn_intForm_map {K L : Type*} [CommRing K] [CommRing L] [Algebra ℤ K] [Algebra ℤ L]
    (f : K →+* L)
    (Q : QuadForm ℤ n) (x : Fin n → K) :
    f (Q.evalIn K x) = Q.evalIn L (fun i => f (x i)) := by
  simp only [QuadForm.evalIn, map_sum, eq_intCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **Base change of an integral form to $\mathbb{Z}_p$, then evaluation in an $\mathbb{Z}_p$-algebra,
equals evaluation as an integral form.** -/
theorem evalIn_map_intCast {K : Type*} [CommRing K] (R : Type*) [CommRing R] [Algebra R K]
    [Algebra ℤ K]
    (Q : QuadForm ℤ n) (x : Fin n → K) :
    (Q.map (Int.castRingHom R)).evalIn K x = Q.evalIn K x := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, eq_intCast,
    map_intCast]

/-- **Counts over $\mathbb{Z}/p^k$ equal counts over $\mathbb{Z}_p/p^k$**, for an integral form viewed over
$\mathbb{Z}_p$, for any solution type that is defined compatibly; here for all solutions and for Good type
relative to $S_0$. *Proof:* transport along the ring isomorphism $\mathbb{Z}/p^k \cong \mathbb{Z}_p/p^k$, which maps
$p \mapsto p$ (so "divisible by $p$" corresponds). -/
@[kb "hanke2004" "§2, p. 356"]
theorem repCount_eq_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (S₀ : Finset (Fin n)) (k : ℕ)
    (m : ℤ) :
    repCount Q p k m = DVR.repCount (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) k (m : ℤ_[p]) ∧
      repCountOf Q p k m (IsGoodType S₀ p k) =
        DVR.repCountOf (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) k (m : ℤ_[p])
          (DVR.IsGoodType S₀ (p : ℤ_[p]) k) := by
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
  · exact (Nat.card_congr (E.subtypeEquiv hval)).symm
  · refine (Nat.card_congr (E.subtypeEquiv fun x => ?_)).symm
    simp only [DVR.IsGoodType, DVR.IsZeroType, IsGoodType, IsZeroType, hval, hdvd]

/-- **Local normal form transfers to $\mathbb{Z}_p$:** if `IsJordanForm Q p P ν` over $\mathbb{Z}$, then
`DVR.IsJordanForm (Q.map …) p P ν` over $\mathbb{Z}_p$ (integers prime to $p$ are units in $\mathbb{Z}_p$). -/
@[kb "hanke2004" "(2.3), p. 355"]
theorem isJordanForm_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) :
    DVR.IsJordanForm (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) P ν := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hJ
  have hu : ∀ u : ℤ, ¬ (p : ℤ) ∣ u → IsUnit (u : ℤ_[p]) := fun u hup => by
    by_contra h
    exact hup ((PadicInt.norm_int_lt_one_iff_dvd u).mp (PadicInt.not_isUnit_iff.mp h))
  have hc : ∀ i j, (Q.map (Int.castRingHom ℤ_[p])).coeff i j = (Q.coeff i j : ℤ_[p]) := fun i j => by
    simp [QuadForm.map]
  refine ⟨fun hP => ?_, h1, h2, fun i j hij hP => ?_, fun e he => ?_, fun i hi => ?_⟩
  · obtain rfl := h0 hP
    exact ⟨1, by norm_num⟩
  · rw [hc, h3 i j hij hP]; simp
  · obtain ⟨hν, ⟨b, hb, hbp⟩, ⟨d1, hd1⟩, ⟨d2, hd2⟩⟩ := h4 e he
    refine ⟨hν, ⟨(b : ℤ_[p]), ?_, hu b hbp⟩, ⟨(d1 : ℤ_[p]), ?_⟩, ⟨(d2 : ℤ_[p]), ?_⟩⟩
    · rw [hc, hb]; push_cast; ring
    · rw [hc, hd1]; push_cast; ring
    · rw [hc, hd2]; push_cast; ring
  · obtain ⟨u, hu', hup⟩ := h5 i hi
    exact ⟨u, by rw [hc, hu']; push_cast; ring, hu u hup⟩

/-- **$\mathrm{ord}_p(2)$ in $\mathbb{Z}_p$:** with $e = 1$ if $p = 2$ and $e = 0$ otherwise,
$p^e \mid 2$ and $p^{e+1} \nmid 2$ in $\mathbb{Z}_p$. -/
theorem padicInt_pow_dvd_two (p : ℕ) [Fact p.Prime] :
    (p : ℤ_[p]) ^ (if p = 2 then 1 else 0) ∣ 2 ∧
      ¬ (p : ℤ_[p]) ^ ((if p = 2 then 1 else 0) + 1) ∣ 2 := by
  have h1 : ¬ (p : ℤ_[p]) ∣ 1 := by
    rw [← PadicInt.norm_lt_one_iff_dvd]; simp
  split_ifs with hp
  · subst hp
    refine ⟨by simp, fun ⟨c, hc⟩ => h1 ⟨c, ?_⟩⟩
    have h2 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    push_cast at hc ⊢
    linear_combination hc
  · refine ⟨by simp, fun h => ?_⟩
    rw [zero_add, pow_one, show (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) by norm_num,
      ← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_int_lt_one_iff_dvd] at h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

/-- **Good-type solutions lift uniformly** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358) for a form in
local normal form: for $k \ge 2\,\mathrm{ord}_p(2) + 1$ and $l \ge 0$,
$r^{\mathrm{Good}}_{p^{k+l}}(m) = p^{(n-1)l}\, r^{\mathrm{Good}}_{p^k}(m)$, Good type taken relative to the
unimodular coordinates $S_0$.

*Proof.* From `DVR.repCountGood_add` over $\mathbb{Z}_p$, via `repCount_eq_padic`, `isJordanForm_padic` and
`q_padicInt` ($\mathrm{ord}_p(2) = 1$ if $p = 2$, else $0$). The underlying argument (pp. 358–359): Pick a unimodular block $j$ with $\vec{x}_j \not\equiv 0$ (canonically, the least
coordinate $i \in S_0$ with $p \nmid x_i$). If the block is 1-dimensional, solve $u x^2 \equiv m'$ by Hensel
($u x_i$ a unit, $k \ge 2\,\mathrm{ord}_p(2) + 1$). If it is $a x^2 + b xy + c y^2$ with $b$ a unit, the partial
derivative in the *other* variable of the block is a unit at $\vec{x}_j$ (e.g. $\partial_y = b x + 2 c y$ when
$p \nmid x$), so Hensel applies to that variable; lift all other coordinates freely. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358"]
theorem repCountGood_add (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (m : ℤ) (k l : ℕ)
    (hk : 2 * (if p = 2 then 1 else 0) + 1 ≤ k) :
    repCountOf Q p (k + l) m (IsGoodType (unimodularCoords ν) p (k + l)) =
      p ^ ((n - 1) * l) * repCountOf Q p k m (IsGoodType (unimodularCoords ν) p k) := by
  rw [(repCount_eq_padic Q p (unimodularCoords ν) (k + l) m).2,
    (repCount_eq_padic Q p (unimodularCoords ν) k m).2,
    DVR.repCountGood_add _ _ PadicInt.irreducible_p P ν
      ((isJordanForm_padic Q p P ν hJ).toW PadicInt.irreducible_p) _
      (padicInt_pow_dvd_two p) _ k l hk, q_padicInt]

end QuadFormsKB.LocalDensity
