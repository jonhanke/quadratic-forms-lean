/-
# Local densities over $\mathbb{Q}$: stabilization for every nondegenerate form

**Layer:** $\mathbb{Q}$. **Proves** Hanke 2004, §3 (the recursion of Lemma 3.4, p. 361) and (5.2), p. 368 (corrected):
for $Q$ nondegenerate and $m \ne 0$, $r_{p^{k+1}}(m) = p^{n-1} r_{p^k}(m)$ for $k \gg 0$ (`repCount_stabilizes`),
so $\beta_p(m)$ is attained (`localDensity_eventually_eq`). First for forms in normal form
(`repCount_stabilizes_J`, induction on $\mathrm{ord}_p(m)$ as in `Stabilization.lean`), then in general via
Lemma 2.1 (`exists_jordanForm`). **Depends on** `Stabilization.lean`, `JordanReduction.lean`, `Padic.lean`
(Lemma 3.2). The DVR analogue is `DVRGeneral.lean`.
-/
import QuadFormsKB.LocalDensity.Stabilization
import QuadFormsKB.LocalDensity.JordanReduction
import QuadFormsKB.LocalDensity.Padic

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **Coefficients of a local normal form lie inside blocks** (Hanke 2004, (2.3), p. 355): a nonzero
coefficient $c_{ij}$, $i \le j$, has $\nu_i = \nu_j$ and $p^{\nu_i} \mid c_{ij}$. -/
theorem IsJordanForm.coeff_block {Q : QuadForm ℤ n} {p : ℕ} {P : Finset (Fin n × Fin n)}
    {ν : Fin n → ℕ} (hJ : IsJordanForm Q p P ν) (i j : Fin n) (hij : i ≤ j) (h0 : Q.coeff i j ≠ 0) :
    ν i = ν j ∧ (p:ℤ)^(ν i) ∣ Q.coeff i j := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hJ
  rcases hij.lt_or_eq with hlt | rfl
  · by_cases hP : (i, j) ∈ P
    · obtain ⟨hν, ⟨b, hb, _⟩, _, _⟩ := h5 _ hP
      exact ⟨hν, ⟨b, hb⟩⟩
    · exact absurd (h4 i j hlt hP) h0
  · refine ⟨rfl, ?_⟩
    by_cases hp : IsPaired P i
    · obtain ⟨e, he, h | h⟩ := hp
      · obtain ⟨_, _, hd, _⟩ := h5 e he
        subst h; exact hd
      · obtain ⟨hν, _, _, hd⟩ := h5 e he
        subst h; rw [← hν]; exact hd
    · obtain ⟨u, hu, _⟩ := h6 i hp
      exact ⟨u, hu⟩

/-- **Evaluation commutes with casting integer vectors:** $Q(\bar{\vec v}) = \overline{Q(\vec v)}$ in any
commutative ring $K$. -/
theorem evalIn_intCast_vec (K : Type*) [CommRing K] (Q : QuadForm ℤ n) (v : Fin n → ℤ) :
    QuadForm.evalIn K Q (fun i => (v i : K)) = ((Q.eval v : ℤ) : K) := by
  simp only [QuadForm.eval, QuadForm.evalIn, Int.cast_sum, algebraMap_int_eq, eq_intCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> push_cast <;> rfl

/-- **Rescaling $S_2$ undoes $Q \mapsto Q''$** (Hanke 2004, §3, p. 360): for $Q$ in local normal form,
$Q(\vec{y}) = Q''(\vec{y}')$ where $y'_i = p\,y_i$ for $\nu_i \ge 2$ and $y'_i = y_i$ otherwise. -/
theorem eval_badIIFormJ_rescale (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (Y : Fin n → ℤ) :
    Q.eval Y = (badIIFormJ Q p ν).eval (fun i => if 2 ≤ ν i then (p:ℤ) * Y i else Y i) := by
  simp only [QuadForm.eval, QuadForm.evalIn, algebraMap_int_eq, eq_intCast, Int.cast_id]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i ≤ j
  · simp only [hij, ite_true, badIIFormJ, QuadForm.ofUpper, Matrix.of_apply]
    by_cases h0 : Q.coeff i j = 0
    · simp [h0]
    obtain ⟨hν, hd⟩ := hJ.coeff_block i j hij h0
    by_cases h2 : 2 ≤ ν i
    · have h2' : 2 ≤ ν j := by omega
      have hd2 : (p:ℤ)^2 ∣ Q.coeff i j := (pow_dvd_pow _ h2).trans hd
      obtain ⟨c, hc⟩ := hd2
      have hp0 : (p:ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      simp only [h2, h2', ite_true, hc, Int.mul_ediv_cancel_left _ hp0]
      ring
    · have h2' : ¬ 2 ≤ ν j := by omega
      simp only [h2, h2', ite_false]
  · simp [hij]

/-- **Solutions vanishing mod $p$ on a set of coordinates, general version** (Hanke 2004, §3, p. 359):
if $Q'(\vec{y}) = Q(\vec{y}')$ with $y'_i = p y_i$ ($i \in T$), $y'_i = y_i$ otherwise, then for $k \ge 1$,
$p^{|T|} \cdot \#\{\vec{x} : Q(\vec{x}) \equiv m \bmod p^k,\ \vec{x}_T \equiv \vec{0}\} = r_{p^k}(Q', m)$. -/
theorem repCount_zeroOn_of_rescale (Q Q' : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (T : Finset (Fin n))
    (hQ' : ∀ Y : Fin n → ℤ, Q'.eval Y = Q.eval (fun i => if i ∈ T then (p:ℤ) * Y i else Y i))
    (m : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    p ^ T.card * repCountOf Q p k m (fun x => ∀ i ∈ T, (p : ZMod (p ^ k)) ∣ x i) =
      repCount Q' p k m := by
  classical
  have gen : ∀ (Q Q' : (Fin n → ZMod (p^k)) → ZMod (p^k)) (f : (Fin n → ZMod (p^k)) → (Fin n → ZMod (p^k))),
      (∀ y, Q' y = Q (f y)) → (∀ y, ∀ i ∈ T, (p : ZMod (p ^ k)) ∣ f y i) →
      (∀ x : Fin n → ZMod (p^k), (∀ i ∈ T, (p : ZMod (p ^ k)) ∣ x i) →
        (Finset.univ.filter (fun y => f y = x)).card = p ^ T.card) →
      p ^ T.card * Nat.card { x // Q x = m ∧ (∀ i ∈ T, (p : ZMod (p ^ k)) ∣ x i) } =
        Nat.card { x // Q' x = m } := by
    intro Q Q' f hf hfT hfib
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ.filter (fun y => Q' y = m)) (t := Finset.univ.filter (fun x => Q x = m ∧ (∀ i ∈ T, (p : ZMod (p ^ k)) ∣ x i)))]
    · rw [Finset.sum_congr rfl (g := fun _ => p ^ T.card), Finset.sum_const, smul_eq_mul, mul_comm]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [← hfib x hx.2, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun y _ => ?_
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [hf, h, hx.1], h⟩
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨by rw [← hf]; exact hy, hfT y⟩
  have hp := ‹Fact p.Prime›
  have : NeZero (p^k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hker : Fintype.card {w : ZMod (p^k) // (p : ZMod (p^k)) * w = 0} = p := by
    have hpk : p ^ k = p ^ (k-1) * p := by rw [← pow_succ]; congr 1; omega
    have hp0 : 0 < p := hp.out.pos
    have hp1 : 0 < p ^ (k-1) := pow_pos hp0 _
    symm
    refine (Fintype.card_fin p).symm.trans ?_
    refine Fintype.card_of_bijective (f := fun j : Fin p => (⟨((p^(k-1) * j.val : ℕ) : ZMod (p^k)), ?_⟩ : {w : ZMod (p^k) // (p : ZMod (p^k)) * w = 0})) ⟨?_, ?_⟩
    · rw [← Nat.cast_mul, ← mul_assoc, ← pow_succ', show k - 1 + 1 = k by omega, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    · intro j j' h
      simp only [Subtype.mk.injEq] at h
      rw [ZMod.natCast_eq_natCast_iff' _ _ (p^k), Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h
      · exact Fin.ext (Nat.eq_of_mul_eq_mul_left hp1 h)
      · rw [hpk]; exact Nat.mul_lt_mul_of_pos_left j'.2 hp1
      · rw [hpk]; exact Nat.mul_lt_mul_of_pos_left j.2 hp1
    · rintro ⟨w, hw⟩
      have h1 : ((p * w.val : ℕ) : ZMod (p^k)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hw
      rw [ZMod.natCast_eq_zero_iff] at h1
      have h2 : p * p^(k-1) ∣ p * w.val := by
        have e : p * p^(k-1) = p^k := by rw [hpk, mul_comm]
        rw [e]; exact h1
      obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left hp0 h2
      have hjp : j < p := by
        have := ZMod.val_lt w
        rw [hj, hpk] at this
        exact Nat.lt_of_mul_lt_mul_left this
      refine ⟨⟨j, hjp⟩, ?_⟩
      simp only [Subtype.mk.injEq]
      rw [← hj, ZMod.natCast_zmod_val]
  set f : (Fin n → ZMod (p^k)) → (Fin n → ZMod (p^k)) :=
    fun y i => if i ∈ T then (p : ZMod (p^k)) * y i else y i with hfdef
  have hf : ∀ y, QuadForm.evalIn (ZMod (p^k)) Q' y = QuadForm.evalIn (ZMod (p^k)) Q (f y) := by
    intro y
    set v : Fin n → ℤ := fun i => ((y i).val : ℤ) with hv
    have hy : y = fun i => (v i : ZMod (p^k)) := by
      funext i; simp [hv]
    have hfy : f y = fun i => (((fun i => if i ∈ T then (p:ℤ) * v i else v i) i : ℤ) : ZMod (p^k)) := by
      rw [hy]; funext i; simp only [hfdef]; split_ifs <;> push_cast <;> rfl
    rw [hfy, evalIn_intCast_vec, hy, evalIn_intCast_vec, hQ']
  have hfT : ∀ y, ∀ i ∈ T, (p : ZMod (p ^ k)) ∣ f y i := by
    intro y i hi
    simp only [hfdef, hi, ite_true]
    exact Dvd.intro _ rfl
  have hfib : ∀ x : Fin n → ZMod (p^k), (∀ i ∈ T, (p : ZMod (p ^ k)) ∣ x i) →
      (Finset.univ.filter (fun y => f y = x)).card = p ^ T.card := by
    intro x hx
    rw [← Fintype.card_subtype]
    have e1 : Fintype.card {y // f y = x} = Fintype.card {y : Fin n → ZMod (p^k) // ∀ i, (if i ∈ T then (p : ZMod (p^k)) * y i else y i) = x i} := by
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun y => ?_)
      simp only [hfdef, funext_iff]
    rw [e1]
    rw [Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ => ZMod (p^k)) (p := fun i z => (if i ∈ T then (p:ZMod (p^k)) * z else z) = x i)), Fintype.card_pi]
    rw [Finset.prod_congr rfl (g := fun i => if i ∈ T then p else 1)]
    · rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    · intro i _
      by_cases hi : i ∈ T
      · simp only [hi, ite_true]
        obtain ⟨c, hc⟩ := hx i hi
        refine Eq.trans ?_ hker
        rw [hc]
        refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.subRight c) fun z => ?_)
        simp [mul_sub, sub_eq_zero]
      · simp only [hi, ite_false]
        exact Fintype.card_unique
  exact gen _ _ f hf hfT hfib

/-- **Divisibility of values on vectors vanishing on low blocks** (Hanke 2004, §3, p. 360): for $Q$ in local
normal form, $e \le 2$, and $\vec{x}$ with $p \mid x_i$ whenever $\nu_i < e$, $p^e \mid Q(\vec{x})$ in
$\mathbb{Z}/p^k$. -/
theorem pow_dvd_evalIn_J (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (k e : ℕ) (he : e ≤ 2) (x : Fin n → ZMod (p ^ k))
    (hx : ∀ i, ν i < e → (p : ZMod (p ^ k)) ∣ x i) :
    (p : ZMod (p ^ k)) ^ e ∣ QuadForm.evalIn (ZMod (p ^ k)) Q x := by
  unfold QuadForm.evalIn
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  split_ifs with hij
  · by_cases h0 : Q.coeff i j = 0
    · simp [h0]
    obtain ⟨hν, hd⟩ := hJ.coeff_block i j hij h0
    by_cases hlt : ν i < e
    · obtain ⟨a, ha⟩ := hx i hlt
      obtain ⟨b, hb⟩ := hx j (hν ▸ hlt)
      rw [ha, hb]
      refine (pow_dvd_pow _ he).trans ⟨algebraMap ℤ (ZMod (p^k)) (Q.coeff i j) * a * b, by ring⟩
    · obtain ⟨c, hc⟩ := (pow_dvd_pow (p:ℤ) (show e ≤ ν i by omega)).trans hd
      rw [hc]
      exact ⟨(c : ZMod (p^k)) * x i * x j, by simp; ring⟩
  · exact dvd_zero _

/-- **Divisibility in $\mathbb{Z}/p^k$ descends to $\mathbb{Z}$** for exponents $e \le k$. -/
theorem intCast_pow_dvd_of_zmod (p : ℕ) [Fact p.Prime] (k e : ℕ) (he : e ≤ k) (m : ℤ)
    (h : (p : ZMod (p ^ k)) ^ e ∣ (m : ZMod (p ^ k))) : (p:ℤ)^e ∣ m := by
  obtain ⟨c, hc⟩ := h
  have : NeZero (p^k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h1 : (((m - (p:ℤ)^e * (c.cast : ℤ) : ℤ)) : ZMod (p^k)) = 0 := by
    push_cast
    rw [hc, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have h2 : (p:ℤ)^e ∣ m - (p:ℤ)^e * (c.cast : ℤ) :=
    dvd_trans (by push_cast; exact pow_dvd_pow _ he) h1
  have := dvd_add h2 (dvd_mul_right ((p:ℤ)^e) (c.cast : ℤ))
  simpa using this

/-- **Stabilization for forms in local normal form** (Hanke 2004, §3): if `IsJordanForm Q p P ν`,
$Q$ is nondegenerate and $m \ne 0$, then $r_{p^{k+1}}(m) = p^{n-1} r_{p^k}(m)$ for all large $k$.
*Proof:* as `repCount_stabilizes_diag` (induction on $\mathrm{ord}_p(m)$ over all forms in local normal
form at once), with `repCountGood_add`, `repCountZero_eq`, `repCountBadI_eq_J`, `repCountBadII_eq_J`,
`isJordanForm_badI_badII`, and the blockwise version of `repCount_zeroOn`. -/
@[kb "hanke2004" "§3, pp. 357–360; (5.2), p. 368"]
theorem repCount_stabilizes_J (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) (hJ : IsJordanForm Q p P ν) (m : ℤ) (hm : m ≠ 0) :
    ∃ K, ∀ k ≥ K, repCount Q p (k + 1) m = p ^ (n - 1) * repCount Q p k m := by
  classical
  have hp := ‹Fact p.Prime›
  let Stab : (ℕ → ℕ) → Prop := fun f => ∃ K, ∀ k ≥ K, f (k+1) = p^(n-1) * f k
  have hStabDef : ∀ f, Stab f ↔ ∃ K, ∀ k ≥ K, f (k+1) = p^(n-1) * f k := fun _ => Iff.rfl
  have hcongr : ∀ f g : ℕ → ℕ, ∀ K0, (∀ k ≥ K0, f k = g k) → Stab g → Stab f := by
    intro f g K0 hfg ⟨K, hK⟩
    refine ⟨max K K0, fun k hk => ?_⟩
    rw [hfg k (by omega), hfg (k+1) (by omega), hK k (by omega)]
  have hadd : ∀ f g : ℕ → ℕ, Stab f → Stab g → Stab (fun k => f k + g k) := by
    intro f g ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨max K K', fun k hk => ?_⟩
    simp only
    rw [hK k (by omega), hK' k (by omega), mul_add]
  have hsub : ∀ f g h : ℕ → ℕ, (∀ k, h k = f k + g k) → Stab h → Stab g → Stab f := by
    intro f g h hh ⟨K, hK⟩ ⟨K', hK'⟩
    refine ⟨max K K', fun k hk => ?_⟩
    have e1 := hK k (by omega)
    have e2 := hK' k (by omega)
    rw [hh, hh, e2, mul_add] at e1
    omega
  have hmul : ∀ (c : ℕ) (f : ℕ → ℕ), Stab f → Stab (fun k => c * f k) := by
    intro c f ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    simp only
    rw [hK k hk]; ring
  have hcancel : ∀ (c : ℕ) (f : ℕ → ℕ), 0 < c → Stab (fun k => c * f k) → Stab f := by
    intro c f hc ⟨K, hK⟩
    refine ⟨K, fun k hk => ?_⟩
    have := hK k hk
    simp only at this
    rw [mul_left_comm] at this
    exact Nat.eq_of_mul_eq_mul_left hc this
  have hshift : ∀ (d : ℕ) (f : ℕ → ℕ), Stab f → Stab (fun k => f (k - d)) := by
    intro d f ⟨K, hK⟩
    refine ⟨K + d, fun k hk => ?_⟩
    simp only
    rw [show k + 1 - d = (k - d) + 1 by omega, hK _ (by omega)]
  have hzero : Stab (fun _ => 0) := ⟨0, fun k _ => by simp⟩
  have hGoodStab : ∀ (Q : QuadForm ℤ n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanForm Q p P ν → ∀ m : ℤ,
      Stab (fun k => repCountOf Q p k m (IsGoodType (unimodularCoords ν) p k)) := by
    intro Q P ν hJ m
    refine ⟨3, fun k hk => ?_⟩
    have := repCountGood_add Q p P ν hJ m k 1 (by split_ifs <;> omega)
    simpa using this
  clear_value Stab
  have split : ∀ {α : Type} [Fintype α] (A B C P : α → Prop), (∀ x, B x ↔ A x ∧ P x) → (∀ x, C x ↔ A x ∧ ¬ P x) →
      Nat.card {x // A x} = Nat.card {x // B x} + Nat.card {x // C x} := by
    intro α _ A B C P hB hC
    classical
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype,
      ← Finset.card_filter_add_card_filter_not (p := P), Finset.filter_filter, Finset.filter_filter]
    congr 2 <;> ext x <;> simp [hB, hC]
  -- Bad-type counts vanish when `p^e ∤ m` (`e = 1`: all Bad; `e = 2`: Bad with `x_{S₁} ≡ 0`).
  have hBad0 : ∀ (Q : QuadForm ℤ n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanForm Q p P ν → ∀ (m : ℤ) (k e : ℕ), e ≤ 2 → e ≤ k → ¬ (p:ℤ)^e ∣ m →
      repCountOf Q p k m (fun x => IsBadType (unimodularCoords ν) p k x ∧
        ∀ i, ν i = 1 → e = 2 → (p : ZMod (p^k)) ∣ x i) = 0 := by
    intro Q P ν hJ m k e he hek hme
    unfold repCountOf
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx, hbad, hS1⟩ => hme (intCast_pow_dvd_of_zmod p k e hek m ?_)⟩
    rw [← hx]
    refine pow_dvd_evalIn_J Q p P ν hJ k e he x fun i hi => ?_
    rcases (by omega : ν i = 0 ∨ (ν i = 1 ∧ e = 2)) with h | ⟨h, h2⟩
    · by_contra hc
      exact hbad.2 ⟨hbad.1, i, by simp [unimodularCoords, h], hc⟩
    · exact hS1 i h h2
  have main : ∀ N, ∀ (Q : QuadForm ℤ n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      IsJordanForm Q p P ν → ∀ m : ℤ, m ≠ 0 → m.natAbs = N →
      Stab (fun k => repCount Q p k m) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
    intro Q P ν hJ m hm hN
    have IH2 : (p:ℤ)^2 ∣ m → ∀ (Q' : QuadForm ℤ n) (P' : Finset (Fin n × Fin n)) (ν' : Fin n → ℕ),
        IsJordanForm Q' p P' ν' → Stab (fun k => repCount Q' p k (m / (p:ℤ)^2)) := by
      intro h2 Q' P' ν' hJ'
      obtain ⟨q, hq⟩ := h2
      have hp0 : (p:ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      have hq0 : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hq
        exact hm hq
      have hdivq : m / (p:ℤ)^2 = q := by rw [hq]; exact Int.mul_ediv_cancel_left _ hp0
      rw [hdivq]
      refine IH _ ?_ Q' P' ν' hJ' _ hq0 rfl
      rw [← hN, hq, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      have h2p := hp.out.two_le
      have hqpos : 0 < q.natAbs := Int.natAbs_pos.mpr hq0
      have h4 : 4 ≤ p^2 := by nlinarith
      nlinarith
    have hJI := (isJordanForm_badI_badII Q p P ν hJ).1
    have hJII := (isJordanForm_badI_badII Q p P ν hJ).2
    have hZero : Stab (fun k => repCountOf Q p k m (IsZeroType p k)) := by
      by_cases h2 : (p:ℤ)^2 ∣ m
      · refine hcongr _ (fun k => p^n * repCount Q p (k - 2) (m / (p:ℤ)^2)) 2 (fun k hk => ?_)
          (hmul (p^n) _ (hshift 2 _ (IH2 h2 Q P ν hJ)))
        rw [repCountZero_eq _ p m k hk]; exact ite_eq_left_iff.mpr (absurd h2)
      · refine hcongr _ (fun _ => 0) 2 (fun k hk => ?_) hzero
        rw [repCountZero_eq _ p m k hk]; exact ite_eq_right_iff.mpr (absurd · h2)
    have hBad : Stab (fun k => repCountOf Q p k m (IsBadType (unimodularCoords ν) p k)) := by
      by_cases h1 : (p:ℤ) ∣ m
      · have hsplit : ∀ k, repCountOf Q p k m (IsBadType (unimodularCoords ν) p k) =
            repCountOf Q p k m (fun x => IsBadType (unimodularCoords ν) p k x ∧ ∃ i, ν i = 1 ∧ ¬ (p : ZMod (p^k)) ∣ x i) +
            repCountOf Q p k m (fun x => IsBadType (unimodularCoords ν) p k x ∧ ∀ i, ν i = 1 → (p : ZMod (p^k)) ∣ x i) := by
          intro k
          unfold repCountOf
          exact split _ _ _ (fun x => ∃ i, ν i = 1 ∧ ¬ (p : ZMod (p^k)) ∣ x i) (fun x => by simp only [and_assoc]) (fun x => by simp only [and_assoc, not_exists, not_and, not_not])
        have hBI : Stab (fun k => repCountOf Q p k m (fun x => IsBadType (unimodularCoords ν) p k x ∧ ∃ i, ν i = 1 ∧ ¬ (p : ZMod (p^k)) ∣ x i)) :=
          hcongr _ _ 2 (fun k hk => repCountBadI_eq_J Q p P ν hJ m k hk h1)
            (hmul _ _ (hshift 1 _ (hGoodStab _ P _ hJI (m / p))))
        have hBII : Stab (fun k => repCountOf Q p k m (fun x => IsBadType (unimodularCoords ν) p k x ∧ ∀ i, ν i = 1 → (p : ZMod (p^k)) ∣ x i)) := by
          by_cases h2 : (p:ℤ)^2 ∣ m
          · set T : Finset (Fin n) := Finset.univ.filter fun i => 2 ≤ ν i with hT
            have hresc : ∀ Y : Fin n → ℤ, Q.eval Y =
                (badIIFormJ Q p ν).eval (fun i => if i ∈ T then (p:ℤ) * Y i else Y i) := by
              intro Y
              rw [eval_badIIFormJ_rescale Q p P ν hJ Y]
              simp [hT]
            have hZ : Stab (fun j => repCountOf (badIIFormJ Q p ν) p j (m / (p:ℤ)^2) (fun y => ∀ i ∈ T, (p : ZMod (p^j)) ∣ y i)) := by
              refine hcancel (p ^ T.card) _ (pow_pos hp.out.pos _) ?_
              refine hcongr _ _ 1 (fun j hj => ?_) (IH2 h2 Q P ν hJ)
              exact repCount_zeroOn_of_rescale (badIIFormJ Q p ν) Q p T hresc _ j hj
            have hR : Stab (fun j => repCountOf (badIIFormJ Q p ν) p j (m / (p:ℤ)^2) (fun y => ∃ i, 2 ≤ ν i ∧ ¬ (p : ZMod (p^j)) ∣ y i)) := by
              refine hsub _ _ _ (fun j => ?_) (IH2 h2 _ P _ hJII) hZ
              unfold repCount repCountOf
              exact split _ _ _ (fun y => ∃ i, 2 ≤ ν i ∧ ¬ (p : ZMod (p^j)) ∣ y i) (fun x => Iff.rfl)
                (fun x => by simp [hT])
            exact hcongr _ _ 3 (fun k hk => repCountBadII_eq_J Q p P ν hJ m k hk h2) (hmul _ _ (hshift 2 _ hR))
          · refine hcongr _ _ 2 (fun k hk => ?_) hzero
            have := hBad0 Q P ν hJ m k 2 le_rfl hk h2
            simpa using this
        exact hcongr _ _ 0 (fun k _ => hsplit k) (hadd _ _ hBI hBII)
      · refine hcongr _ _ 1 (fun k hk => ?_) hzero
        have := hBad0 Q P ν hJ m k 1 (by norm_num) hk (by simpa using h1)
        simpa using this
    exact hcongr _ _ 0 (fun k _ => repCount_eq_add_types _ (unimodularCoords ν) p k m)
      (hadd _ _ (hadd _ _ hZero (hGoodStab Q P ν hJ m)) hBad)
  exact (hStabDef _).mp (main _ Q P ν hJ m hm rfl)

/-- **Stabilization for every nondegenerate form** (Hanke 2004, §3 and (5.2)): for $Q$ nondegenerate
and $m \ne 0$, $r_{p^{k+1}}(m) = p^{n-1} r_{p^k}(m)$ for all large $k$.
*Proof:* `exists_jordanForm` gives $Q'$ in local normal form with the same counts; apply
`repCount_stabilizes_J`. -/
@[kb "hanke2004" "§3; (5.2), p. 368"]
theorem repCount_stabilizes (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (m : ℤ) (hm : m ≠ 0) :
    ∃ K, ∀ k ≥ K, repCount Q p (k + 1) m = p ^ (n - 1) * repCount Q p k m := by
  obtain ⟨Q', P, ν, hJ, hQ', -, hc⟩ := exists_jordanForm Q hQ p
  obtain ⟨K, hK⟩ := repCount_stabilizes_J Q' hQ' p P ν hJ m hm
  exact ⟨K, fun k hk => by rw [hc, hc]; exact hK k hk⟩

/-- **The local density is attained** (Hanke 2004, §3 and (5.2), p. 368): for $Q$ nondegenerate and
$m \ne 0$, the normalized counts $r_{p^k}(m)/p^{k(n-1)}$ are eventually constant, and their value is
`localDensity Q p m`.

*Proof sketch.* Induct on $\mathrm{ord}_p(m)$ using the reduction maps: Good-type counts stabilize
by Lemma 3.2 (`repCountGood_add_diag`, for diagonal forms; general Jordan splittings to follow); Zero-type counts reduce to $m/p^2$ by `repCountZero_eq`; Bad-type counts
reduce (maps $\pi_{B'}$, $\pi_{B''}$, p. 360) to forms $Q', Q''$ with smaller determinant valuation
(to be added to this blueprint). -/
@[kb "hanke2004" "§3, pp. 357–360; (5.2), p. 368"]
theorem localDensity_eventually_eq (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (p : ℕ)
    [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ∀ᶠ k in Filter.atTop, (repCount Q p k m : ℝ) / (p : ℝ) ^ (k * (n - 1)) = localDensity Q p m := by
  obtain ⟨K, hK⟩ := repCount_stabilizes Q hQ p m hm
  set f : ℕ → ℝ := fun k => (repCount Q p k m : ℝ) / (p : ℝ) ^ (k * (n - 1)) with hf
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hstep : ∀ k ≥ K, f (k + 1) = f k := by
    intro k hk
    simp only [hf]
    rw [hK k hk]
    push_cast
    rw [show (k + 1) * (n - 1) = (n - 1) + k * (n - 1) by ring, pow_add]
    have : (p:ℝ) ^ (n-1) ≠ 0 := pow_ne_zero _ hp0
    field_simp
  have hconst : ∀ k ≥ K, f k = f K := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [hstep k hk, ih]
  have hT : Filter.Tendsto f Filter.atTop (nhds (f K)) := by
    apply tendsto_const_nhds.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨K, fun k hk => (hconst k hk).symm⟩
  have hL : localDensity Q p m = f K := hT.limUnder_eq
  rw [Filter.eventually_atTop]
  exact ⟨K, fun k hk => by rw [hL]; exact hconst k hk⟩

end QuadFormsKB.LocalDensity
