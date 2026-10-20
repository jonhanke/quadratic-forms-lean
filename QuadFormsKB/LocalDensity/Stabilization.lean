/-
# Local densities over $\mathbb{Q}$: stabilization for diagonal forms

**Layer:** $\mathbb{Q}$. **Proves** for a nondegenerate diagonal form and $m \ne 0$ that
$r_{p^{k+1}}(m) = p^{n-1} r_{p^k}(m)$ for $k \gg 0$ (`repCount_stabilizes_diag`), so $\beta_p(m)$ is attained
(`localDensity_eventually_eq_diag`): Hanke 2004, §3 (the recursion of Lemma 3.4, p. 361, via the maps of
pp. 359–360) and (5.2), p. 368 (corrected). Also the $m = 0$ case for $n \ge 3$ (`tendsto_localDensity_zero_diag`)
and the rescaling identity for $\pi_{B''}$ (`repCount_zeroOn`, p. 359). **Depends on** `Reduction.lean`
(induction on $\mathrm{ord}_p(m)$ through Zero, Bad I and Bad II types; Good type by Lemma 3.2).
-/
import QuadFormsKB.LocalDensity.Reduction

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **Solutions vanishing mod $p$ on a set of coordinates** (Hanke 2004, §3: the congruence
conditions $\vec{x}_{\mathbb{S}} \equiv \vec{0}$ used with the reduction maps, p. 359): for a diagonal form,
$k \ge 1$ and $T \subseteq \{0, \dots, n-1\}$,
$p^{|T|} \cdot \#\{\vec{x} : Q(\vec{x}) \equiv m \bmod p^k,\ \vec{x}_T \equiv \vec{0} \bmod p\} = r_{p^k}(Q_T, m)$,
where $Q_T$ multiplies the coefficients $a_i$, $i \in T$, by $p^2$.

*Proof.* Write $x_i = p y_i$ for $i \in T$; $y_i$ is determined mod $p^{k-1}$, and $p^2 a_i y_i^2 \bmod p^k$
depends only on $y_i \bmod p^{k-1}$, so each such $\vec{x}$ corresponds to exactly $p^{|T|}$ solutions of
$Q_T(\vec{y}) \equiv m \pmod{p^k}$ (the lifts of $\vec{y}_T$ from $p^{k-1}$ to $p^k$). -/
@[kb "hanke2004" "§3, p. 359"]
theorem repCount_zeroOn (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (m : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (T : Finset (Fin n)) :
    p ^ T.card * repCountOf (QuadForm.diag a) p k m (fun x => ∀ i ∈ T, (p : ZMod (p ^ k)) ∣ x i) =
      repCount (QuadForm.diag fun i => if i ∈ T then (p : ℤ) ^ 2 * a i else a i) p k m := by
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
  have hker : Fintype.card {w : ZMod (p^k) // (p : ZMod (p^k)) * w = 0} = p := by
    have hpk : p ^ k = p ^ (k-1) * p := by rw [← pow_succ]; congr 1; omega
    have hp0 : 0 < p := hp.out.pos
    have hp1 : 0 < p ^ (k-1) := pow_pos hp0 _
    have : NeZero (p^k) := ⟨by positivity⟩
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
  have hev : ∀ (b : Fin n → ℤ) (x : Fin n → ZMod (p^k)),
      QuadForm.evalIn (ZMod (p^k)) (QuadForm.diag b) x = ∑ i, (b i : ZMod (p^k)) * x i * x i := by
    intro b x
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  set f : (Fin n → ZMod (p^k)) → (Fin n → ZMod (p^k)) :=
    fun y i => if i ∈ T then (p : ZMod (p^k)) * y i else y i with hfdef
  have hf : ∀ y, QuadForm.evalIn (ZMod (p^k)) (QuadForm.diag fun i => if i ∈ T then (p : ℤ) ^ 2 * a i else a i) y
      = QuadForm.evalIn (ZMod (p^k)) (QuadForm.diag a) (f y) := by
    intro y
    rw [hev, hev]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hfdef]
    split_ifs
    · push_cast; ring
    · rfl
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

/-- **Stabilization for diagonal forms** (Hanke 2004, §3 and (5.2)): for $a_i \ne 0$ and $m \ne 0$, there
is $K$ with $r_{p^{k+1}}(m) = p^{n-1} r_{p^k}(m)$ for all $k \ge K$. See the module docstring for the
induction on $\mathrm{ord}_p(m)$ through the reduction maps; strengthen the induction to also cover the
Good-type counts and the counts with $\vec{x}_T \not\equiv \vec{0}$ conditions. -/
@[kb "hanke2004" "§3, pp. 357–360; (5.2), p. 368"]
theorem repCount_stabilizes_diag (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (p : ℕ) [Fact p.Prime]
    (m : ℤ) (hm : m ≠ 0) :
    ∃ K, ∀ k ≥ K, repCount (QuadForm.diag a) p (k + 1) m = p ^ (n - 1) * repCount (QuadForm.diag a) p k m := by
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
  have hGoodStab : ∀ (b : Fin n → ℤ) (m : ℤ), Stab (fun k => repCountOf (QuadForm.diag b) p k m
      (IsGoodType ({i | ¬ (p:ℤ) ∣ b i} : Finset (Fin n)) p k)) := by
    intro b m
    refine ⟨3, fun k hk => ?_⟩
    have := repCountGood_add_diag b p m k 1 (by split_ifs <;> omega)
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
  have hS0 : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → S₀ b p = ({i | ¬ (p:ℤ) ∣ b i} : Finset (Fin n)) := by
    intro b hb
    ext i
    simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and]
    have := padicValInt_dvd_iff (p := p) 1 (b i)
    simp only [pow_one, hb i, false_or] at this
    rw [this]; omega
  have hI : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → ∀ i, badIForm b p i ≠ 0 := by
    intro b hb i
    simp only [badIForm]
    split_ifs with h
    · exact mul_ne_zero (by exact_mod_cast hp.out.ne_zero) (hb i)
    · have hd : (p:ℤ) ∣ b i := by
        have := (padicValInt_dvd_iff (p := p) 1 (b i)).mpr (Or.inr (by omega))
        simpa using this
      intro h0
      have := Int.ediv_mul_cancel hd
      rw [h0, zero_mul] at this
      exact hb i this.symm
  have hII : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → ∀ i, badIIForm b p i ≠ 0 := by
    intro b hb i
    simp only [badIIForm]
    split_ifs with h
    · have hd : (p:ℤ)^2 ∣ b i := (padicValInt_dvd_iff (p := p) 2 (b i)).mpr (Or.inr h)
      intro h0
      have := Int.ediv_mul_cancel hd
      rw [h0, zero_mul] at this
      exact hb i this.symm
    · exact hb i
  have hII' : ∀ b : Fin n → ℤ, (fun i => if i ∈ S₂ b p then (p:ℤ)^2 * badIIForm b p i else badIIForm b p i) = b := by
    intro b
    funext i
    simp only [S₂, badIIForm, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact Int.mul_ediv_cancel' ((padicValInt_dvd_iff (p := p) 2 (b i)).mpr (Or.inr h))
    · rfl
  have hdiv : ∀ k, 2 ≤ k → ∀ m : ℤ, ((p:ZMod (p^k))^2 ∣ (m : ZMod (p^k))) → (p:ℤ)^2 ∣ m := by
    intro k hk m ⟨c, hc⟩
    have : NeZero (p^k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    have h1 : (((m - (p:ℤ)^2 * (c.cast : ℤ) : ℤ)) : ZMod (p^k)) = 0 := by
      push_cast
      rw [hc, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    have h2 : (p:ℤ)^2 ∣ m - (p:ℤ)^2 * (c.cast : ℤ) :=
      dvd_trans (by push_cast; exact pow_dvd_pow _ hk) h1
    have := dvd_add h2 (dvd_mul_right ((p:ℤ)^2) (c.cast : ℤ))
    simpa using this
  have hev : ∀ (k : ℕ) (b : Fin n → ℤ) (x : Fin n → ZMod (p^k)),
      QuadForm.evalIn (ZMod (p^k)) (QuadForm.diag b) x = ∑ i, (b i : ZMod (p^k)) * x i * x i := by
    intro k b x
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hBII0 : ∀ (b : Fin n → ℤ) (m : ℤ) (k : ℕ), 2 ≤ k → ¬ (p:ℤ)^2 ∣ m →
      repCountOf (QuadForm.diag b) p k m (fun x => IsBadType (S₀ b p) p k x ∧ ∀ i ∈ S₁ b p, (p : ZMod (p^k)) ∣ x i) = 0 := by
    intro b m k hk hm2
    unfold repCountOf
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨x, hx, hbad, hS1⟩ => hm2 (hdiv k hk m ?_)⟩
    have hS0' : ∀ i ∈ S₀ b p, (p : ZMod (p^k)) ∣ x i := by
      intro i hi
      by_contra hc
      exact hbad.2 ⟨hbad.1, i, hi, hc⟩
    rw [← hx, hev]
    refine Finset.dvd_sum fun i _ => ?_
    have hv : padicValInt p (b i) = 0 ∨ padicValInt p (b i) = 1 ∨ 2 ≤ padicValInt p (b i) := by omega
    rcases hv with hv | hv | hv
    · obtain ⟨c, hc⟩ := hS0' i (by simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv)
      rw [hc]; exact ⟨(b i : ZMod (p^k)) * c * c, by ring⟩
    · obtain ⟨c, hc⟩ := hS1 i (by simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv)
      rw [hc]; exact ⟨(b i : ZMod (p^k)) * c * c, by ring⟩
    · obtain ⟨d, hd⟩ := (padicValInt_dvd_iff (p := p) 2 (b i)).mpr (Or.inr hv)
      rw [hd]; exact ⟨(d : ZMod (p^k)) * x i * x i, by push_cast; ring⟩
  have main : ∀ N, ∀ (b : Fin n → ℤ), (∀ i, b i ≠ 0) → ∀ m : ℤ, m ≠ 0 → m.natAbs = N →
      Stab (fun k => repCount (QuadForm.diag b) p k m) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
    intro b hb m hm hN
    have IH2 : (p:ℤ)^2 ∣ m → ∀ b' : Fin n → ℤ, (∀ i, b' i ≠ 0) →
        Stab (fun k => repCount (QuadForm.diag b') p k (m / (p:ℤ)^2)) := by
      intro h2 b' hb'
      obtain ⟨q, hq⟩ := h2
      have hp0 : (p:ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
      have hq0 : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hq
        exact hm hq
      have hdivq : m / (p:ℤ)^2 = q := by rw [hq]; exact Int.mul_ediv_cancel_left _ hp0
      rw [hdivq]
      refine IH _ ?_ b' hb' _ hq0 rfl
      rw [← hN, hq, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      have h2p := hp.out.two_le
      have hqpos : 0 < q.natAbs := Int.natAbs_pos.mpr hq0
      have h4 : 4 ≤ p^2 := by nlinarith
      nlinarith
    have hGood : Stab (fun k => repCountOf (QuadForm.diag b) p k m (IsGoodType (S₀ b p) p k)) := by
      rw [hS0 b hb]; exact hGoodStab b m
    have hZero : Stab (fun k => repCountOf (QuadForm.diag b) p k m (IsZeroType p k)) := by
      by_cases h2 : (p:ℤ)^2 ∣ m
      · refine hcongr _ (fun k => p^n * repCount (QuadForm.diag b) p (k - 2) (m / (p:ℤ)^2)) 2 (fun k hk => ?_)
          (hmul (p^n) _ (hshift 2 _ (IH2 h2 b hb)))
        beta_reduce
        rw [repCountZero_eq _ p m k hk, if_pos h2]
      · refine hcongr _ (fun _ => 0) 2 (fun k hk => ?_) hzero
        beta_reduce
        rw [repCountZero_eq _ p m k hk, if_neg h2]
    have hBad : Stab (fun k => repCountOf (QuadForm.diag b) p k m (IsBadType (S₀ b p) p k)) := by
      by_cases h1 : (p:ℤ) ∣ m
      · have hsplit : ∀ k, repCountOf (QuadForm.diag b) p k m (IsBadType (S₀ b p) p k) =
            repCountOf (QuadForm.diag b) p k m (fun x => IsBadType (S₀ b p) p k x ∧ ∃ i ∈ S₁ b p, ¬ (p : ZMod (p^k)) ∣ x i) +
            repCountOf (QuadForm.diag b) p k m (fun x => IsBadType (S₀ b p) p k x ∧ ∀ i ∈ S₁ b p, (p : ZMod (p^k)) ∣ x i) := by
          intro k
          unfold repCountOf
          exact split _ _ _ (fun x => ∃ i ∈ S₁ b p, ¬ (p : ZMod (p^k)) ∣ x i) (fun x => by simp only [and_assoc]) (fun x => by simp only [and_assoc, not_exists, not_and, not_not])
        have hBI : Stab (fun k => repCountOf (QuadForm.diag b) p k m (fun x => IsBadType (S₀ b p) p k x ∧ ∃ i ∈ S₁ b p, ¬ (p : ZMod (p^k)) ∣ x i)) := by
          have hG' : Stab (fun k => repCountOf (QuadForm.diag (badIForm b p)) p k (m / p) (IsGoodType (S₀ (badIForm b p) p) p k)) := by
            rw [hS0 _ (hI b hb)]; exact hGoodStab _ _
          exact hcongr _ _ 2 (fun k hk => repCountBadI_eq b hb p m k hk h1) (hmul _ _ (hshift 1 _ hG'))
        have hBII : Stab (fun k => repCountOf (QuadForm.diag b) p k m (fun x => IsBadType (S₀ b p) p k x ∧ ∀ i ∈ S₁ b p, (p : ZMod (p^k)) ∣ x i)) := by
          by_cases h2 : (p:ℤ)^2 ∣ m
          · have hZ : Stab (fun j => repCountOf (QuadForm.diag (badIIForm b p)) p j (m / (p:ℤ)^2) (fun y => ∀ i ∈ S₂ b p, (p : ZMod (p^j)) ∣ y i)) := by
              refine hcancel (p ^ (S₂ b p).card) _ (pow_pos hp.out.pos _) ?_
              refine hcongr _ _ 1 (fun j hj => ?_) (IH2 h2 b hb)
              beta_reduce
              rw [repCount_zeroOn (badIIForm b p) p (m / (p:ℤ)^2) j hj (S₂ b p), hII' b]
            have hR : Stab (fun j => repCountOf (QuadForm.diag (badIIForm b p)) p j (m / (p:ℤ)^2) (fun y => ∃ i ∈ S₂ b p, ¬ (p : ZMod (p^j)) ∣ y i)) := by
              refine hsub _ _ _ (fun j => ?_) (IH2 h2 (badIIForm b p) (hII b hb)) hZ
              beta_reduce
              unfold repCount repCountOf
              exact split _ _ _ (fun y => ∃ i ∈ S₂ b p, ¬ (p : ZMod (p^j)) ∣ y i) (fun x => Iff.rfl) (fun x => by simp only [not_exists, not_and, not_not])
            exact hcongr _ _ 3 (fun k hk => repCountBadII_eq b hb p m k hk h2) (hmul _ _ (hshift 2 _ hR))
          · exact hcongr _ _ 2 (fun k hk => hBII0 b m k hk h2) hzero
        exact hcongr _ _ 0 (fun k _ => hsplit k) (hadd _ _ hBI hBII)
      · exact hcongr _ _ 1 (fun k hk => repCountBad_eq_zero b p m k hk h1) hzero
    exact hcongr _ _ 0 (fun k _ => repCount_eq_add_types _ (S₀ b p) p k m)
      (hadd _ _ (hadd _ _ hZero hGood) hBad)
  exact (hStabDef _).mp (main _ a ha m hm rfl)

/-- **The local density of a diagonal form is attained** (Hanke 2004, (5.2), p. 368, corrected): for
$a_i \ne 0$ and $m \ne 0$, $r_{p^k}(m)/p^{k(n-1)}$ is eventually equal to `localDensity`.
*Proof:* by `repCount_stabilizes_diag` the sequence is eventually constant, so `limUnder` is its value. -/
@[kb "hanke2004" "(5.2), p. 368"]
theorem localDensity_eventually_eq_diag (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (p : ℕ) [Fact p.Prime]
    (m : ℤ) (hm : m ≠ 0) :
    ∀ᶠ k in Filter.atTop, (repCount (QuadForm.diag a) p k m : ℝ) / (p : ℝ) ^ (k * (n - 1)) =
      localDensity (QuadForm.diag a) p m := by
  obtain ⟨K, hK⟩ := repCount_stabilizes_diag a ha p m hm
  set f : ℕ → ℝ := fun k => (repCount (QuadForm.diag a) p k m : ℝ) / (p : ℝ) ^ (k * (n - 1)) with hf
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
  have hL : localDensity (QuadForm.diag a) p m = f K := hT.limUnder_eq
  rw [Filter.eventually_atTop]
  exact ⟨K, fun k hk => by rw [hL]; exact hconst k hk⟩

/-- **The case $m = 0$: convergence, not stabilization** (Hanke 2004, §3 and (5.2), p. 368, corrected;
discussion with the author 2026-10-15). For a nondegenerate diagonal form in $n \ge 3$ variables, the
normalized counts $r_{p^k}(0)/p^{k(n-1)}$ **converge** to `localDensity Q p 0` (they need not be eventually
constant).

*Proof sketch.* The induction on $\mathrm{ord}_p(m)$ is unavailable ($m/p^2 = 0$). Instead: nondegeneracy
bounds the Jordan exponents ($\sum_j \nu_j \dim Q_j \le \mathrm{ord}_p(D_{2Q})$, (2.4)), so the reduction maps
(Zero: $Q \mapsto Q$; Bad I: $\nu \mapsto \nu \pm 1$; Bad II: $\nu_{S_2} \mapsto \nu_{S_2} - 2$) stay inside a finite
set of diagonal forms, and the normalized counts satisfy a finite linear recursion in $k$ whose
Zero-type part contracts by the factor $p^{2-n} < 1$; Good-type parts are eventually constant by
Lemma 3.2. Hence the limit exists. (For $n \le 2$, $\beta_p(0)$ can be infinite, e.g. a $p$-adically
isotropic binary form.) -/
@[kb "hanke2004" "§3; (5.2), p. 368"]
theorem tendsto_localDensity_zero_diag (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hn : 3 ≤ n) (p : ℕ)
    [Fact p.Prime] :
    Filter.Tendsto (fun k : ℕ => (repCount (QuadForm.diag a) p k 0 : ℝ) / (p : ℝ) ^ (k * (n - 1)))
      Filter.atTop (nhds (localDensity (QuadForm.diag a) p 0)) := by
  classical
  have hp := ‹Fact p.Prime›
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpR : (1:ℝ) < p := by exact_mod_cast hp2
  have hpR0 : (0:ℝ) < p := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (p:ℝ)^(n-1) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ pow_pos hpR0 _
  let F : (Fin n → ℤ) → ℕ → ℝ := fun b k => (repCount (QuadForm.diag b) p k 0 : ℝ) / q ^ k
  have hFeq : ∀ b k, (repCount (QuadForm.diag b) p k 0 : ℝ) / (p:ℝ) ^ (k * (n-1)) = F b k := by
    intro b k; simp only [F, hq, pow_mul']
  have lim_rec : ∀ (y : ℕ → ℝ) (g c : ℝ), 0 ≤ c → c < 1 → (∀ k, y (k+2) = g + c * y k) →
      ∃ L, Filter.Tendsto y Filter.atTop (nhds L) := by
    intro y g c hc0 hc1 hy
    refine ⟨g / (1 - c), ?_⟩
    have h1c : (1 - c) ≠ 0 := by intro h; linarith
    set z : ℕ → ℝ := fun k => y k - g / (1 - c) with hz
    have hzrec : ∀ k, z (k+2) = c * z k := by
      intro k; simp only [hz, hy k]; field_simp; ring
    set M := |z 0| + |z 1| with hM
    have hbound : ∀ k, |z k| ≤ M * c ^ (k/2) ∧ |z (k+1)| ≤ M * c ^ ((k+1)/2) := by
      intro k
      induction k with
      | zero =>
        simp only [Nat.zero_div, pow_zero, mul_one, zero_add, Nat.reduceDiv, hM]
        constructor <;> linarith [abs_nonneg (z 0), abs_nonneg (z 1)]
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [show k + 1 + 1 = k + 2 by ring, hzrec, abs_mul, abs_of_nonneg hc0,
          show (k+2)/2 = k/2 + 1 by omega, pow_succ]
        have := mul_le_mul_of_nonneg_left ih.1 hc0
        linarith
    have hlim : Filter.Tendsto (fun k : ℕ => M * c ^ (k/2)) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp (Nat.tendsto_div_const_atTop (show (2:ℕ) ≠ 0 by norm_num))
      simpa using this.const_mul M
    have hz0 : Filter.Tendsto z Filter.atTop (nhds 0) :=
      squeeze_zero_norm (fun k => (hbound k).1) hlim
    have := hz0.add_const (g / (1 - c))
    simpa [hz] using this
  have lim_shift : ∀ (x y : ℕ → ℝ) (g c L : ℝ), Filter.Tendsto y Filter.atTop (nhds L) →
      (∀ k, x (k+4) = g + c * y (k+2)) → ∃ L, Filter.Tendsto x Filter.atTop (nhds L) := by
    intro x y g c L hy hx
    refine ⟨g + c * L, ?_⟩
    rw [← Filter.tendsto_add_atTop_iff_nat 4]
    have := ((hy.comp (Filter.tendsto_add_atTop_nat 2)).const_mul c).const_add g
    refine this.congr fun k => ?_
    simp [hx k]
  have split : ∀ {α : Type} [Fintype α] (A B C P : α → Prop), (∀ x, B x ↔ A x ∧ P x) → (∀ x, C x ↔ A x ∧ ¬ P x) →
      Nat.card {x // A x} = Nat.card {x // B x} + Nat.card {x // C x} := by
    intro α _ A B C P hB hC
    classical
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype,
      ← Finset.card_filter_add_card_filter_not (p := P), Finset.filter_filter, Finset.filter_filter]
    congr 2 <;> ext x <;> simp [hB, hC]
  have hS0 : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → S₀ b p = ({i | ¬ (p:ℤ) ∣ b i} : Finset (Fin n)) := by
    intro b hb
    ext i
    simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and]
    have := padicValInt_dvd_iff (p := p) 1 (b i)
    simp only [pow_one, hb i, false_or] at this
    rw [this]; omega
  have hII : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → ∀ i, badIIForm b p i ≠ 0 := by
    intro b hb i
    simp only [badIIForm]
    split_ifs with h
    · have hd : (p:ℤ)^2 ∣ b i := (padicValInt_dvd_iff (p := p) 2 (b i)).mpr (Or.inr h)
      intro h0
      have := Int.ediv_mul_cancel hd
      rw [h0, zero_mul] at this
      exact hb i this.symm
    · exact hb i
  have hII' : ∀ b : Fin n → ℤ, (fun i => if i ∈ S₂ b p then (p:ℤ)^2 * badIIForm b p i else badIIForm b p i) = b := by
    intro b
    funext i
    simp only [S₂, badIIForm, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact Int.mul_ediv_cancel' ((padicValInt_dvd_iff (p := p) 2 (b i)).mpr (Or.inr h))
    · rfl
  have hcard : ∀ b : Fin n → ℤ, (S₀ b p).card + (S₁ b p).card + (S₂ b p).card = n := by
    intro b
    have e1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => padicValInt p (b i) = 0)
    have e2 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun i => ¬ padicValInt p (b i) = 0)) (fun i => padicValInt p (b i) = 1)
    rw [Finset.filter_filter, Finset.filter_filter] at e2
    have h1 : S₁ b p = Finset.univ.filter (fun i => ¬ padicValInt p (b i) = 0 ∧ padicValInt p (b i) = 1) := by
      ext i; simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h2 : S₂ b p = Finset.univ.filter (fun i => ¬ padicValInt p (b i) = 0 ∧ ¬ padicValInt p (b i) = 1) := by
      ext i; simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h0 : S₀ b p = Finset.univ.filter (fun i => padicValInt p (b i) = 0) := rfl
    rw [h0, h1, h2]
    rw [Finset.card_univ, Fintype.card_fin] at e1
    omega
  have hnat : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → ∀ k,
      repCount (QuadForm.diag b) p (k+4) 0 =
        repCountOf (QuadForm.diag b) p (k+4) 0 (IsGoodType (S₀ b p) p (k+4)) +
        p ^ ((S₁ b p).card + (S₂ b p).card) *
          repCountOf (QuadForm.diag (badIForm b p)) p (k+3) 0 (IsGoodType (S₀ (badIForm b p) p) p (k+3)) +
        p ^ (2 * n - (S₀ b p).card - (S₁ b p).card) * repCount (QuadForm.diag (badIIForm b p)) p (k+2) 0 := by
    intro b hb k
    have hsplit : repCountOf (QuadForm.diag b) p (k+4) 0 (IsBadType (S₀ b p) p (k+4)) =
        repCountOf (QuadForm.diag b) p (k+4) 0 (fun x => IsBadType (S₀ b p) p (k+4) x ∧ ∃ i ∈ S₁ b p, ¬ (p : ZMod (p^(k+4))) ∣ x i) +
        repCountOf (QuadForm.diag b) p (k+4) 0 (fun x => IsBadType (S₀ b p) p (k+4) x ∧ ∀ i ∈ S₁ b p, (p : ZMod (p^(k+4))) ∣ x i) := by
      unfold repCountOf
      exact split _ _ _ (fun x => ∃ i ∈ S₁ b p, ¬ (p : ZMod (p^(k+4))) ∣ x i) (fun x => by simp only [and_assoc]) (fun x => by simp only [and_assoc, not_exists, not_and, not_not])
    have hBI : repCountOf (QuadForm.diag b) p (k+4) 0 (fun x => IsBadType (S₀ b p) p (k+4) x ∧ ∃ i ∈ S₁ b p, ¬ (p : ZMod (p^(k+4))) ∣ x i) =
        p ^ ((S₁ b p).card + (S₂ b p).card) *
          repCountOf (QuadForm.diag (badIForm b p)) p (k+3) (0 / (p:ℤ)) (IsGoodType (S₀ (badIForm b p) p) p (k+3)) :=
      repCountBadI_eq b hb p 0 (k+4) (by omega) (dvd_zero _)
    have hBII : repCountOf (QuadForm.diag b) p (k+4) 0 (fun x => IsBadType (S₀ b p) p (k+4) x ∧ ∀ i ∈ S₁ b p, (p : ZMod (p^(k+4))) ∣ x i) =
        p ^ (2 * n - (S₀ b p).card - (S₁ b p).card) *
          repCountOf (QuadForm.diag (badIIForm b p)) p (k+2) (0 / (p:ℤ)^2) (fun y => ∃ i ∈ S₂ b p, ¬ (p : ZMod (p^(k+2))) ∣ y i) :=
      repCountBadII_eq b hb p 0 (k+4) (by omega) (dvd_zero _)
    have hZ : repCountOf (QuadForm.diag b) p (k+4) 0 (IsZeroType p (k+4)) =
        if (p:ℤ)^2 ∣ 0 then p^n * repCount (QuadForm.diag b) p (k+2) (0 / (p:ℤ)^2) else 0 :=
      repCountZero_eq (QuadForm.diag b) p 0 (k+4) (by omega)
    rw [if_pos (dvd_zero _)] at hZ
    rw [Int.zero_ediv] at hZ hBI hBII
    have hRZ : repCount (QuadForm.diag (badIIForm b p)) p (k+2) 0 =
        repCountOf (QuadForm.diag (badIIForm b p)) p (k+2) 0 (fun y => ∃ i ∈ S₂ b p, ¬ (p : ZMod (p^(k+2))) ∣ y i) +
        repCountOf (QuadForm.diag (badIIForm b p)) p (k+2) 0 (fun y => ∀ i ∈ S₂ b p, (p : ZMod (p^(k+2))) ∣ y i) := by
      unfold repCount repCountOf
      exact split _ _ _ (fun y => ∃ i ∈ S₂ b p, ¬ (p : ZMod (p^(k+2))) ∣ y i) (fun x => Iff.rfl) (fun x => by simp only [not_exists, not_and, not_not])
    have hZO := repCount_zeroOn (badIIForm b p) p 0 (k+2) (by omega) (S₂ b p)
    rw [hII' b] at hZO
    rw [repCount_eq_add_types _ (S₀ b p) p (k+4) 0, hZ, hsplit, hBI, hBII, hRZ, ← hZO,
      show 2 * n - (S₀ b p).card - (S₁ b p).card = n + (S₂ b p).card by have := hcard b; omega,
      pow_add p n (S₂ b p).card]
    ring
  have hreal : ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → ∃ g : ℝ, ∀ k,
      F b (k+4) = g + ((p:ℝ) ^ (2 * n - (S₀ b p).card - (S₁ b p).card) / q^2) * F (badIIForm b p) (k+2) := by
    intro b hb
    have hG : ∀ k, repCountOf (QuadForm.diag b) p (k+4) 0 (IsGoodType (S₀ b p) p (k+4)) =
        p^((n-1)*(k+1)) * repCountOf (QuadForm.diag b) p 3 0 (IsGoodType (S₀ b p) p 3) := by
      intro k
      rw [hS0 b hb]
      have := repCountGood_add_diag b p 0 3 (k+1) (by split_ifs <;> omega)
      rw [show 3 + (k+1) = k+4 by omega] at this
      exact this
    have hG' : ∀ k, repCountOf (QuadForm.diag (badIForm b p)) p (k+3) 0 (IsGoodType (S₀ (badIForm b p) p) p (k+3)) =
        p^((n-1)*k) * repCountOf (QuadForm.diag (badIForm b p)) p 3 0 (IsGoodType (S₀ (badIForm b p) p) p 3) := by
      intro k
      have hI : ∀ i, badIForm b p i ≠ 0 := by
        intro i
        simp only [badIForm]
        split_ifs with h
        · exact mul_ne_zero (by exact_mod_cast hp.out.ne_zero) (hb i)
        · have hd : (p:ℤ) ∣ b i := by
            have := (padicValInt_dvd_iff (p := p) 1 (b i)).mpr (Or.inr (by omega))
            simpa using this
          intro h0
          have := Int.ediv_mul_cancel hd
          rw [h0, zero_mul] at this
          exact hb i this.symm
      rw [hS0 _ hI]
      have := repCountGood_add_diag (badIForm b p) p 0 3 k (by split_ifs <;> omega)
      rw [show 3 + k = k+3 by omega] at this
      exact this
    refine ⟨(repCountOf (QuadForm.diag b) p 3 0 (IsGoodType (S₀ b p) p 3) : ℝ) / q^3 +
      (p:ℝ)^((S₁ b p).card + (S₂ b p).card) *
        (repCountOf (QuadForm.diag (badIForm b p)) p 3 0 (IsGoodType (S₀ (badIForm b p) p) p 3) : ℝ) / q^4, fun k => ?_⟩
    simp only [F]
    rw [hnat b hb k, hG k, hG' k]
    push_cast
    rw [show (p:ℝ)^((n-1)*(k+1)) = q^(k+1) by rw [hq, ← pow_mul],
      show (p:ℝ)^((n-1)*k) = q^k by rw [hq, ← pow_mul]]
    field_simp
    ring
  have main : ∀ N, ∀ b : Fin n → ℤ, (∀ i, b i ≠ 0) → ∑ i, (b i).natAbs = N →
      ∃ L, Filter.Tendsto (F b) Filter.atTop (nhds L) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
    intro b hb hN
    obtain ⟨g, hg⟩ := hreal b hb
    by_cases hS2 : S₂ b p = ∅
    · have hbb : badIIForm b p = b := by
        funext i
        have : i ∉ S₂ b p := by rw [hS2]; simp
        simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at this
        simp only [badIIForm, if_neg this]
      rw [hbb] at hg
      have hc := hcard b
      rw [hS2, Finset.card_empty, add_zero] at hc
      have hc1 : (p:ℝ) ^ (2 * n - (S₀ b p).card - (S₁ b p).card) / q^2 < 1 := by
        rw [div_lt_one (pow_pos hq0 _), hq, ← pow_mul]
        exact pow_lt_pow_right₀ hpR (by omega)
      have hc0 : 0 ≤ (p:ℝ) ^ (2 * n - (S₀ b p).card - (S₁ b p).card) / q^2 := by positivity
      obtain ⟨L, hL⟩ := lim_rec (fun k => F b (k+2)) g _ hc0 hc1 (fun k => hg k)
      exact ⟨L, (Filter.tendsto_add_atTop_iff_nat 2).mp hL⟩
    · have hdecr : ∀ i, 2 ≤ padicValInt p (b i) → (b i / (p:ℤ)^2).natAbs < (b i).natAbs := by
        intro i h
        obtain ⟨d, hd⟩ := (padicValInt_dvd_iff (p := p) 2 (b i)).mpr (Or.inr h)
        have hp2' : (p:ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
        have hd0 : d ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hd
          exact hb i hd
        rw [hd, Int.mul_ediv_cancel_left _ hp2', Int.natAbs_mul]
        have h1 : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
        have h2 : 1 < ((p:ℤ)^2).natAbs := by
          rw [Int.natAbs_pow, Int.natAbs_natCast]; nlinarith
        nlinarith
      have hlt : ∑ i, (badIIForm b p i).natAbs < N := by
        rw [← hN]
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS2
        apply Finset.sum_lt_sum
        · intro i _
          simp only [badIIForm]
          split_ifs with h
          · exact (hdecr i h).le
          · exact le_refl _
        · refine ⟨j, Finset.mem_univ _, ?_⟩
          simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp only [badIIForm, if_pos hj]
          exact hdecr j hj
      obtain ⟨L, hL⟩ := IH _ hlt (badIIForm b p) (hII b hb) rfl
      exact lim_shift (F b) (F (badIIForm b p)) g _ L hL hg
  obtain ⟨L, hL⟩ := main _ a ha rfl
  have hT : Filter.Tendsto (fun k : ℕ => (repCount (QuadForm.diag a) p k 0 : ℝ) / (p : ℝ) ^ (k * (n - 1))) Filter.atTop (nhds L) :=
    hL.congr fun k => (hFeq a k).symm
  unfold localDensity
  rw [hT.limUnder_eq]
  exact hT

end QuadFormsKB.LocalDensity
