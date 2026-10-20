/-
# Local densities over $\mathbb{Q}$: the Bad-type reduction maps for diagonal forms

**Layer:** $\mathbb{Q}$. For a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ at $p$, with
$S_t = \{i : \mathrm{ord}_p(a_i) = t\}$ ($t = 0, 1$) and $S_2 = \{i : \mathrm{ord}_p(a_i) \ge 2\}$, **proves**
the counting identities for the maps $\pi_{B'}$ (Bad type I, `repCountBadI_eq`) and $\pi_{B''}$ (Bad type II,
`repCountBadII_eq`) of Hanke 2004, §3, p. 360 (multiplicities $q^{s_1+s_2}$ and $q^{2n-s_0-s_1}$), and that Bad
type is empty when $p \nmid m$ (`repCountBad_eq_zero`). **Depends on** `Basic.lean`. The block-diagonal
version is `JordanReduction.lean`; the DVR version is `DVRReductions.lean`.
-/
import QuadFormsKB.LocalDensity.Basic

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- **The Jordan index sets of a diagonal form at $p$** (Hanke 2004, p. 360): $S_t(a)$ is the set of
coordinates $i$ with $\mathrm{ord}_p(a_i) = t$ for $t = 0, 1$; `S₂` collects those with $\mathrm{ord}_p(a_i) \ge 2$. -/
def S₀ (a : Fin n → ℤ) (p : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => padicValInt p (a i) = 0

/-- See `S₀`. -/
def S₁ (a : Fin n → ℤ) (p : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => padicValInt p (a i) = 1

/-- See `S₀`. -/
def S₂ (a : Fin n → ℤ) (p : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => 2 ≤ padicValInt p (a i)

/-- **The form $Q'$ of Bad type I** (Hanke 2004, p. 360): coefficients $p a_j$ for $j \in S_0$ and
$a_j / p$ otherwise (so $\nu'_j = \nu_j + 1$ on $S_0$ and $\nu_j - 1$ elsewhere), so that
$Q(\vec{x}) = p\, Q'(\pi_{B'}\vec{x})$. -/
def badIForm (a : Fin n → ℤ) (p : ℕ) : Fin n → ℤ :=
  fun i => if padicValInt p (a i) = 0 then p * a i else a i / p

/-- **The form $Q''$ of Bad type II** (Hanke 2004, p. 360): coefficients $a_j$ for $j \in S_0 \cup S_1$
and $a_j / p^2$ for $j \in S_2$, so that $Q(\vec{x}) = p^2\, Q''(\pi_{B''}\vec{x})$. -/
def badIIForm (a : Fin n → ℤ) (p : ℕ) : Fin n → ℤ :=
  fun i => if 2 ≤ padicValInt p (a i) then a i / p ^ 2 else a i

/-- **Bad-type solutions need $p \mid m$** (Hanke 2004, p. 360): if $p \nmid m$ there are no Bad-type
solutions mod $p^k$ ($k \ge 1$). *Proof:* on Bad type $\vec{x}_{S_0} \equiv 0$, and every other coefficient
is divisible by $p$, so $Q(\vec{x}) \equiv 0 \pmod p$. -/
@[kb "hanke2004" "§3, p. 360"]
theorem repCountBad_eq_zero (a : Fin n → ℤ) (p : ℕ) [Fact p.Prime] (m : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hm : ¬ (p : ℤ) ∣ m) :
    repCountOf (QuadForm.diag a) p k m (IsBadType (S₀ a p) p k) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx, hbad⟩
  have hgood : ∀ i ∈ S₀ a p, (p : ZMod (p ^ k)) ∣ x i := by
    intro i hi
    by_contra h
    exact hbad.2 ⟨hbad.1, i, hi, h⟩
  have hdvd : (p : ZMod (p ^ k)) ∣ (m : ZMod (p ^ k)) := by
    rw [← hx]
    unfold evalIn
    apply Finset.dvd_sum
    intro i _
    apply Finset.dvd_sum
    intro j _
    split_ifs with hij
    · by_cases hij' : i = j
      · subst hij'
        simp only [QuadForm.diag, Matrix.diagonal_apply_eq]
        by_cases hi : i ∈ S₀ a p
        · exact Dvd.dvd.mul_left (hgood i hi) _
        · have : (p : ℤ) ∣ a i := by
            simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            by_contra h
            exact hi (padicValInt.eq_zero_of_not_dvd h)
          apply Dvd.dvd.mul_right
          apply Dvd.dvd.mul_right
          obtain ⟨c, hc⟩ := this
          refine ⟨(c : ZMod (p ^ k)), ?_⟩
          simp [hc]
      · simp [QuadForm.diag, Matrix.diagonal_apply_ne _ hij']
    · exact dvd_zero _
  have hk0 : k ≠ 0 := by omega
  let f := ZMod.castHom (dvd_pow_self p hk0) (ZMod p)
  obtain ⟨c, hc⟩ := hdvd
  have := congrArg f hc
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul, map_intCast] at this
  exact hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mp this)

/-- **Bad type I reduction** (Hanke 2004, §3, map $\pi_{B'}$, p. 360), for diagonal forms with all
$a_i \ne 0$, $p \mid m$ and $k \ge 2$: the Bad-type solutions with $\vec{x}_{S_1} \not\equiv \vec{0}$ number
$p^{s_1 + s_2}$ times the Good-type solutions of $Q'(\vec{x}') \equiv m/p \pmod{p^{k-1}}$ (Good type for $Q'$,
whose unimodular coordinates are $S_1$).

*Proof.* $\pi_{B'}$ is well defined ($x_j \equiv 0 \bmod p$ on $S_0$), $Q(\vec{x}) = p\,Q'(\pi_{B'}\vec{x})$,
the image is Good for $Q'$ exactly because $\vec{x}_{S_1} \not\equiv 0$, and each image vector has
$p^{s_1 + s_2}$ preimages (free choice of the lifts mod $p^k$ of the coordinates in $S_1 \cup S_2$,
which are only determined mod $p^{k-1}$). -/
@[kb "hanke2004" "§3, map π_{B'}, p. 360"]
theorem repCountBadI_eq (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (p : ℕ) [Fact p.Prime] (m : ℤ)
    (k : ℕ) (hk : 2 ≤ k) (hm : (p : ℤ) ∣ m) :
    repCountOf (QuadForm.diag a) p k m
        (fun x => IsBadType (S₀ a p) p k x ∧ ∃ i ∈ S₁ a p, ¬ (p : ZMod (p ^ k)) ∣ x i) =
      p ^ ((S₁ a p).card + (S₂ a p).card) *
        repCountOf (QuadForm.diag (badIForm a p)) p (k - 1) (m / p)
          (IsGoodType (S₀ (badIForm a p) p) p (k - 1)) := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : 1 ≤ k' := by omega
  rw [show k' + 1 - 1 = k' by omega]
  have hp : p.Prime := Fact.out
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have heval : ∀ {N : ℕ} (b : Fin n → ℤ) (x : Fin n → ZMod N), QuadForm.evalIn (ZMod N) (QuadForm.diag b) x = ∑ i, (b i : ZMod N) * x i ^ 2 := by
    intro N b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]; ring
    · intro j _ hj; simp [Matrix.diagonal, Ne.symm hj]
    · simp
  have hfib : ∀ y : ZMod (p^k'), (Finset.univ.filter fun x : ZMod (p^(k'+1)) => (ZMod.cast x : ZMod (p^k')) = y).card = p := by
    intro y
    have hs := ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ k'))
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := ZMod.castHom (pow_dvd_pow p (Nat.le_succ k')) (ZMod (p^k'))) (by simp)
    rw [Finset.sum_congr rfl (fun z _ => AddMonoidHom.card_fiber_eq_of_mem_range (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k')) (ZMod (p^k'))) (hs z) (hs y))] at this
    simp [ZMod.card, pow_succ] at this
    rcases this with h | h
    · exact h.symm
    · exact absurd h.1 hp.ne_zero
  have hmulp : ∀ U V : ℤ, (p:ℤ)^k' ∣ U - V → (((p:ℤ) * U : ℤ) : ZMod (p^(k'+1))) = (((p:ℤ) * V : ℤ) : ZMod (p^(k'+1))) := by
    intro U V h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [pow_succ, show (p:ℤ) * V - p * U = (V - U) * p by ring]
    exact mul_dvd_mul_right (by rw [← neg_sub]; exact (dvd_neg).2 h) _
  have hcastval : ∀ (x : ZMod (p^(k'+1))) (y : ZMod (p^k')), (ZMod.cast x : ZMod (p^k')) = y → (p:ℤ)^k' ∣ (x.val:ℤ) - (y.val:ℤ) := by
    intro x y h
    rw [ZMod.cast_eq_val] at h
    have h2 : (((x.val : ℤ)) : ZMod (p^k')) = (((y.val : ℤ)) : ZMod (p^k')) := by
      simpa using h
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
    push_cast at this
    exact dvd_sub_comm.1 this
  have hinj : ∀ y y' : ZMod (p^k'), (p : ZMod (p^(k'+1))) * (y.val : ZMod (p^(k'+1))) = (p : ZMod (p^(k'+1))) * (y'.val : ZMod (p^(k'+1))) → y = y' := by
    intro y y' h
    have h2 : (((p:ℤ) * y.val : ℤ) : ZMod (p^(k'+1))) = (((p:ℤ) * y'.val : ℤ) : ZMod (p^(k'+1))) := by
      push_cast; exact h
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
    push_cast at h3
    rw [pow_succ, ← mul_sub, mul_comm ((p:ℤ)^k'), mul_dvd_mul_iff_left hp0] at h3
    have h4 : (((y.val : ℤ)) : ZMod (p^k')) = (((y'.val : ℤ)) : ZMod (p^k')) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast; exact h3
    simpa using h4
  have hdvdgen : ∀ j, 1 ≤ j → ∀ u : ℕ, (p : ZMod (p^j)) ∣ (u : ZMod (p^j)) ↔ p ∣ u := by
    intro j hj u
    constructor
    · rintro ⟨c, hc⟩
      have := congrArg (ZMod.castHom (dvd_pow_self p (by omega : j ≠ 0)) (ZMod p)) hc
      rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at this
      exact (ZMod.natCast_eq_zero_iff _ _).1 this
    · rintro ⟨w, rfl⟩; exact ⟨w, by push_cast; ring⟩
  have hdvd : ∀ x : ZMod (p^(k'+1)), (p : ZMod _) ∣ x ↔ (p : ZMod (p^k')) ∣ (ZMod.cast x : ZMod (p^k')) := by
    intro x
    rw [ZMod.cast_eq_val, hdvdgen k' hk', ← hdvdgen (k'+1) (by omega), ZMod.natCast_zmod_val]
  set S0 := S₀ a p with hS0def
  set S1 := S₁ a p with hS1def
  set S2 := S₂ a p with hS2def
  set a' := badIForm a p with ha'def
  have hdiv : ∀ i, i ∉ S0 → (p:ℤ) ∣ a i := by
    intro i hi
    by_contra h
    apply hi
    simp only [S0, S₀, Finset.mem_filter, Finset.mem_univ, true_and]; exact padicValInt.eq_zero_of_not_dvd h
  have ha'0 : ∀ i, i ∈ S0 → a' i = p * a i := by 
    intro i hi; simp only [a', badIForm]; rw [if_pos (by simpa [S0, S₀] using hi)]
  have ha'1 : ∀ i, i ∉ S0 → a i = p * a' i := by
    intro i hi; have := hdiv i hi; simp only [a', badIForm]; rw [if_neg (by simpa [S0, S₀] using hi)]; exact (Int.mul_ediv_cancel' this).symm
  have hS : S₀ a' p = S1 := by
    ext i; simp only [S₀, S₁, Finset.mem_filter, Finset.mem_univ, true_and, S1]
    by_cases h : i ∈ S0
    · rw [ha'0 i h]; have h0 : padicValInt p (a i) = 0 := by simpa [S0, S₀] using h
      rw [padicValInt.mul hp0 (ha i), h0, padicValInt.self hp.one_lt]; simp
    · have h1 := ha'1 i h
      have hb : a' i ≠ 0 := by intro h0; exact ha i (by rw [h1, h0, mul_zero])
      rw [h1, padicValInt.mul hp0 hb, padicValInt.self hp.one_lt]; omega
  have hS10 : ∀ i ∈ S1, i ∉ S0 := by
    intro i hi h0; simp only [S1, S₁, S0, S₀, Finset.mem_filter, Finset.mem_univ, true_and] at hi h0; omega
  have hcard : (Finset.univ.filter (fun i => i ∉ S0)).card = S1.card + S2.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp only [S0, S1, S2, S₀, S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
    · exact Finset.disjoint_filter.2 (by intros; omega)
  rw [hS]
  clear_value S0 S1 S2 a'
  let L : ZMod (p^k') → ZMod (p^(k'+1)) := fun y => (p : ZMod (p^(k'+1))) * (y.val : ZMod (p^(k'+1)))
  let F : (Fin n → ZMod (p^k')) → Finset (Fin n → ZMod (p^(k'+1))) := fun y =>
    Fintype.piFinset fun j => if j ∈ S0 then {L (y j)} else Finset.univ.filter fun c => (ZMod.cast c : ZMod (p^k')) = y j
  have hFcard : ∀ y, (F y).card = p ^ (S1.card + S2.card) := by
    intro y
    simp only [F, Fintype.card_piFinset]
    rw [← hcard, Finset.prod_congr rfl (g := fun j => if j ∈ S0 then 1 else p)]
    · rw [Finset.prod_ite]; simp
    · intro j _; split_ifs <;> simp [hfib]
  have hmemF : ∀ x y, x ∈ F y ↔ ∀ j, (j ∈ S0 → x j = L (y j)) ∧ (j ∉ S0 → (ZMod.cast (x j) : ZMod (p^k')) = y j) := by
    intro x y
    simp only [F, Fintype.mem_piFinset]
    refine forall_congr' fun j => ?_
    split_ifs with h <;> simp [h]
  have hmeq : ∀ N : ℤ, ((((p:ℤ) * N : ℤ)) : ZMod (p^(k'+1))) = (m : ZMod _) ↔ ((N : ℤ) : ZMod (p^k')) = ((m / p : ℤ) : ZMod _) := by
    intro N
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
    obtain ⟨m', rfl⟩ := hm
    rw [Int.mul_ediv_cancel_left _ hp0]
    push_cast
    rw [pow_succ, ← mul_sub, mul_comm ((p:ℤ)^k'), mul_dvd_mul_iff_left hp0]
  have hkey : ∀ y x, x ∈ F y → ((QuadForm.evalIn (ZMod (p^(k'+1))) (diag a) x = m ∧ IsBadType S0 p (k'+1) x ∧ ∃ i ∈ S1, ¬ (p : ZMod (p^(k'+1))) ∣ x i) ↔ (QuadForm.evalIn (ZMod (p^k')) (diag a') y = ((m / p : ℤ) : ZMod (p^k')) ∧ IsGoodType S1 p k' y)) := by
    intro y x hx
    rw [hmemF] at hx
    have hN : QuadForm.evalIn _ (diag a) x = (((p:ℤ) * ∑ i, a' i * ((y i).val : ℤ)^2 : ℤ) : ZMod (p^(k'+1))) := by
      rw [heval, Finset.mul_sum, Int.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ S0
      · rw [(hx i).1 hi, ha'0 i hi]; simp only [L]; push_cast; ring
      · rw [ha'1 i hi]
        have h1 := hmulp (a' i * ((x i).val:ℤ)^2) (a' i * ((y i).val : ℤ)^2) ?_
        · rw [← h1]; push_cast; rw [ZMod.natCast_zmod_val]; ring
        · have := hcastval _ _ ((hx i).2 hi)
          rw [show a' i * ((x i).val:ℤ)^2 - a' i * ((y i).val : ℤ)^2 = (((x i).val:ℤ) - (y i).val) * (a' i * (((x i).val:ℤ) + (y i).val)) by ring]
          exact dvd_mul_of_dvd_left this _
    have hN' : QuadForm.evalIn _ (diag a') y = ((∑ i, a' i * ((y i).val : ℤ)^2 : ℤ) : ZMod (p^k')) := by
      rw [heval]; push_cast; simp
    have hx0 : ∀ j ∈ S0, (p : ZMod (p^(k'+1))) ∣ x j := fun j hj => by rw [(hx j).1 hj]; exact Dvd.intro _ rfl
    have hiff : ∀ i ∈ S1, ((p : ZMod (p^(k'+1))) ∣ x i ↔ (p : ZMod (p^k')) ∣ y i) := by
      intro i hi; rw [hdvd, (hx i).2 (hS10 i hi)]
    rw [hN, hN', hmeq]
    refine and_congr_right fun _ => ?_
    unfold IsBadType IsGoodType IsZeroType
    constructor
    · rintro ⟨⟨hz, hg⟩, i, hi, hni⟩
      exact ⟨fun h => hni ((hiff i hi).2 (h i)), i, hi, fun h => hni ((hiff i hi).2 h)⟩
    · rintro ⟨hz, i, hi, hni⟩
      have hnx : ¬ (p : ZMod (p^(k'+1))) ∣ x i := fun h => hni ((hiff i hi).1 h)
      exact ⟨⟨fun h => hnx (h i), fun ⟨_, j, hj, hnj⟩ => hnj (hx0 j hj)⟩, i, hi, hnx⟩
  unfold repCountOf
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hA : (Finset.univ.filter fun x : Fin n → ZMod (p^(k'+1)) => QuadForm.evalIn (ZMod (p^(k'+1))) (diag a) x = m ∧ IsBadType S0 p (k'+1) x ∧ ∃ i ∈ S1, ¬ (p : ZMod (p^(k'+1))) ∣ x i) = (Finset.univ.filter fun y : Fin n → ZMod (p^k') => QuadForm.evalIn (ZMod (p^k')) (diag a') y = ((m / p : ℤ) : ZMod (p^k')) ∧ IsGoodType S1 p k' y).biUnion F := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hx
      have h0 : ∀ j ∈ S0, ∃ c, x j = (p : ZMod (p^(k'+1))) * c := by
        intro j hj; by_contra hc; exact hx.2.1.2 ⟨hx.2.1.1, j, hj, hc⟩
      choose c hc using h0
      let y : Fin n → ZMod (p^k') := fun j => if h : j ∈ S0 then ZMod.cast (c j h) else ZMod.cast (x j)
      have hxF : x ∈ F y := by
        rw [hmemF]
        intro j
        refine ⟨fun hj => ?_, fun hj => by simp [y, hj]⟩
        rw [hc j hj]
        simp only [L, y, dif_pos hj]
        have := hmulp _ _ (hcastval (c j hj) _ rfl)
        push_cast at this
        rw [ZMod.natCast_zmod_val] at this
        exact this
      exact ⟨y, (hkey y x hxF).1 hx, hxF⟩
    · rintro ⟨y, hy, hxF⟩
      exact (hkey y x hxF).2 hy
  rw [hA, Finset.card_biUnion, Finset.sum_congr rfl (fun y _ => hFcard y), Finset.sum_const, smul_eq_mul, mul_comm]
  intro y _ y' _ hne
  refine Finset.disjoint_left.2 fun x h1 h2 => hne ?_
  rw [hmemF] at h1 h2
  funext j
  by_cases hj : j ∈ S0
  · exact hinj _ _ (((h1 j).1 hj).symm.trans ((h2 j).1 hj))
  · exact ((h1 j).2 hj).symm.trans ((h2 j).2 hj)

/-- **Bad type II reduction** (Hanke 2004, §3, map $\pi_{B''}$, p. 360), for diagonal forms with all
$a_i \ne 0$, $p^2 \mid m$ and $k \ge 3$: the Bad-type solutions with $\vec{x}_{S_1} \equiv \vec{0}$ number
$p^{2n - s_0 - s_1}$ times the solutions of $Q''(\vec{x}'') \equiv m/p^2 \pmod{p^{k-2}}$ with
$\vec{x}''_{S_2} \not\equiv \vec{0}$.

*Proof.* As for type I: $Q(\vec{x}) = p^2 Q''(\pi_{B''}\vec{x})$; the map is $p$-to-1 on each coordinate of
$S_0 \cup S_1$ (division by $p$, then reduction mod $p^{k-2}$) and $p^2$-to-1 on each coordinate of
$S_2$ (reduction mod $p^{k-2}$), giving $p^{(s_0 + s_1) + 2 s_2} = p^{2n - s_0 - s_1}$. -/
@[kb "hanke2004" "§3, map π_{B''}, p. 360"]
theorem repCountBadII_eq (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (p : ℕ) [Fact p.Prime] (m : ℤ)
    (k : ℕ) (hk : 3 ≤ k) (hm : (p : ℤ) ^ 2 ∣ m) :
    repCountOf (QuadForm.diag a) p k m
        (fun x => IsBadType (S₀ a p) p k x ∧ ∀ i ∈ S₁ a p, (p : ZMod (p ^ k)) ∣ x i) =
      p ^ (2 * n - (S₀ a p).card - (S₁ a p).card) *
        repCountOf (QuadForm.diag (badIIForm a p)) p (k - 2) (m / p ^ 2)
          (fun y => ∃ i ∈ S₂ a p, ¬ (p : ZMod (p ^ (k - 2))) ∣ y i) := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have A : ∀ {G H : Type} [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H] (f : G →+ H) (P : H → Prop),
      Nat.card {g // P (f g)} = Nat.card f.ker * Nat.card {h // h ∈ f.range ∧ P h} := by
    intro G H _ _ _ _ f P
    have : Fintype G := Fintype.ofFinite G
    have : Fintype {h // h ∈ f.range ∧ P h} := Fintype.ofFinite _
    have e : {g // P (f g)} ≃ Σ (h : {h // h ∈ f.range ∧ P h}), {g // f g = h.1} :=
      { toFun := fun g => ⟨⟨f g.1, ⟨g.1, rfl⟩, g.2⟩, ⟨g.1, rfl⟩⟩
        invFun := fun s => ⟨s.2.1, by rw [s.2.2]; exact s.1.2.2⟩
        left_inv := fun g => rfl
        right_inv := by
          rintro ⟨⟨h, h1, h2⟩, ⟨g, hg⟩⟩
          simp only at hg
          subst hg
          rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
    have hfib : ∀ h : {h // h ∈ f.range ∧ P h}, Nat.card {g // f g = h.1} = Nat.card f.ker := by
      rintro ⟨h, ⟨g₀, rfl⟩, _⟩
      apply Nat.card_congr
      exact { toFun := fun g => ⟨g.1 - g₀, by simp [AddMonoidHom.mem_ker, g.2]⟩
              invFun := fun k => ⟨k.1 + g₀, by have := k.2; rw [AddMonoidHom.mem_ker] at this; simp [this]⟩
              left_inv := fun g => by ext; simp
              right_inv := fun k => by ext; simp }
    rw [Finset.sum_congr rfl (fun h _ => hfib h), Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Nat.card_eq_fintype_card (α := {h // h ∈ f.range ∧ P h})]
  have hmulz : ∀ (k j : ℕ) (hj : j ≤ k) (t : ZMod (p ^ k)),
      (p ^ j : ZMod (p ^ k)) * t = 0 ↔ ZMod.castHom (pow_dvd_pow p (Nat.sub_le k j)) (ZMod (p ^ (k - j))) t = 0 := by
    intro k j hj t
    have : NeZero (p ^ k) := ⟨by positivity⟩
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    conv_lhs => rw [← ZMod.natCast_zmod_val t]
    rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    generalize t.val = v
    have : p ^ k = p ^ j * p ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
    rw [this, Nat.mul_dvd_mul_iff_left (by positivity)]
  have hdvdp : ∀ (j : ℕ) (hj : j ≠ 0) (t : ZMod (p ^ j)),
      (p : ZMod (p ^ j)) ∣ t ↔ ZMod.castHom (dvd_pow_self p hj) (ZMod p) t = 0 := by
    intro j hj t
    have : NeZero (p ^ j) := ⟨by positivity⟩
    constructor
    · rintro ⟨s, rfl⟩
      rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
    · intro h
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at h
      obtain ⟨q, hq⟩ := h
      refine ⟨q, ?_⟩
      rw [← ZMod.natCast_zmod_val t, hq]; push_cast; rfl
  have K : ∀ (k j : ℕ), j ≤ k → Nat.card {t : ZMod (p ^ k) // (p ^ j : ZMod (p ^ k)) * t = 0} = p ^ j := by
    intro k j hj
    have hNZ : NeZero (p ^ (k - j)) := ⟨by positivity⟩
    have : NeZero (p ^ k) := ⟨by positivity⟩
    let f := (ZMod.castHom (pow_dvd_pow p (Nat.sub_le k j)) (ZMod (p ^ (k - j)))).toAddMonoidHom
    have e1 : {t : ZMod (p ^ k) // (p ^ j : ZMod (p ^ k)) * t = 0} ≃ f.ker :=
      Equiv.subtypeEquivRight (fun t => by rw [hmulz k j hj t]; rfl)
    have h := A f (fun _ => True)
    have e2 : {h // h ∈ f.range ∧ True} ≃ ZMod (p ^ (k - j)) :=
      (Equiv.subtypeEquivRight (fun h => by simp only [and_true, AddMonoidHom.mem_range]; exact iff_of_true (ZMod.castHom_surjective (pow_dvd_pow p (Nat.sub_le k j)) h) trivial)).trans (Equiv.subtypeUnivEquiv (fun _ => trivial))
    rw [Nat.card_congr e2, Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_zmod, Nat.card_zmod, ← Nat.card_congr e1] at h
    have h2 : p ^ k = p ^ j * p ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hj]
    have h3 := h2.symm.trans h
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h3).symm
  set S2 := S₂ a p with hS2def
  set b := badIIForm a p with hb
  have hk2 : k - 2 ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  haveI : NeZero (p ^ k) := ⟨by positivity⟩
  haveI : NeZero (p ^ (k - 2)) := ⟨by positivity⟩
  have hdiv : p ^ (k - 2) ∣ p ^ k := pow_dvd_pow p (Nat.sub_le k 2)
  have hevalz : ∀ (N : ℕ) (c : Fin n → ℤ) (x : Fin n → ZMod N), evalIn (ZMod N) (diag c) x = ∑ i, (c i : ZMod N) * x i ^ 2 := by
    intro N c x
    unfold evalIn diag
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]; ring
    · intro j _ hj; simp [Matrix.diagonal, Ne.symm hj]
    · simp
  have hnot2 : ∀ i, i ∉ S2 ↔ (i ∈ S₀ a p ∨ i ∈ S₁ a p) := by
    intro i; simp only [hS2def, S₀, S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hab : ∀ i ∈ S2, a i = (p:ℤ)^2 * b i := by
    intro i hi
    have h2 : 2 ≤ padicValInt p (a i) := by simpa [hS2def, S₂] using hi
    have hd : (p:ℤ)^2 ∣ a i := (padicValInt_dvd_iff 2 (a i)).2 (Or.inr h2)
    simp only [hb, badIIForm, if_pos h2]
    exact (Int.mul_ediv_cancel' hd).symm
  have hab' : ∀ i ∉ S2, b i = a i := by
    intro i hi
    have h2 : ¬ 2 ≤ padicValInt p (a i) := by simpa [hS2def, S₂] using hi
    simp only [hb, badIIForm, if_neg h2]
  let e : Fin n → ℕ := fun i => if i ∈ S2 then 0 else 1
  let Ψ : (Fin n → ZMod (p ^ k)) →+ (Fin n → ZMod (p ^ k)) :=
    AddMonoidHom.mk' (fun z i => (p : ZMod (p ^ k)) ^ (e i) * z i) (by intro x y; ext i; simp [mul_add])
  let C : (Fin n → ZMod (p ^ k)) →+ (Fin n → ZMod (p ^ (k - 2))) :=
    AddMonoidHom.mk' (fun z i => ZMod.castHom hdiv (ZMod (p ^ (k - 2))) (z i)) (by intro x y; ext i; exact map_add (ZMod.castHom hdiv (ZMod (p ^ (k - 2)))) (x i) (y i))
  have hΨ : ∀ z i, Ψ z i = (p : ZMod (p ^ k)) ^ (e i) * z i := fun z i => rfl
  have hC : ∀ z i, C z i = ZMod.castHom hdiv (ZMod (p ^ (k - 2))) (z i) := fun z i => rfl
  have hdvdC : ∀ t : ZMod (p ^ k), (p : ZMod (p ^ k)) ∣ t ↔ (p : ZMod (p ^ (k-2))) ∣ ZMod.castHom hdiv (ZMod (p ^ (k - 2))) t := by
    intro t
    rw [hdvdp k hk0, hdvdp (k-2) hk2, ← RingHom.comp_apply, ZMod.castHom_comp]
  have hΨS2 : ∀ z, ∀ i ∈ S2, Ψ z i = z i := by intro z i hi; simp [hΨ, e, hi]
  have hΨn : ∀ z, ∀ i ∉ S2, (p : ZMod (p ^ k)) ∣ Ψ z i := by
    intro z i hi; simp only [hΨ, e, if_neg hi, pow_one]; exact dvd_mul_right _ _
  let R : (Fin n → ZMod (p ^ k)) → Prop := fun x => evalIn (ZMod (p ^ k)) (diag a) x = m ∧ (IsBadType (S₀ a p) p k x ∧ ∀ i ∈ S₁ a p, (p : ZMod (p ^ k)) ∣ x i)
  let P : (Fin n → ZMod (p ^ (k-2))) → Prop := fun y => evalIn (ZMod (p ^ (k-2))) (diag b) y = ((m / p^2 : ℤ) : ZMod (p ^ (k-2))) ∧ ∃ i ∈ S2, ¬ (p : ZMod (p ^ (k - 2))) ∣ y i
  have hRbad : ∀ x : Fin n → ZMod (p ^ k), (IsBadType (S₀ a p) p k x ∧ ∀ i ∈ S₁ a p, (p : ZMod (p ^ k)) ∣ x i) ↔ ((∀ i ∉ S2, (p : ZMod (p ^ k)) ∣ x i) ∧ ∃ i ∈ S2, ¬ (p : ZMod (p ^ k)) ∣ x i) := by
    intro x
    simp only [IsBadType, IsGoodType, IsZeroType]
    constructor
    · rintro ⟨⟨hnz, hng⟩, hS1⟩
      have hall : ∀ i ∉ S2, (p : ZMod (p ^ k)) ∣ x i := by
        intro i hi
        rcases (hnot2 i).1 hi with h | h
        · by_contra hc; exact hng ⟨hnz, i, h, hc⟩
        · exact hS1 i h
      refine ⟨hall, ?_⟩
      push_neg at hnz
      obtain ⟨i, hi⟩ := hnz
      exact ⟨i, by by_contra h; exact hi (hall i h), hi⟩
    · rintro ⟨hall, i, hi, hndvd⟩
      refine ⟨⟨fun h => hndvd (h i), ?_⟩, fun j hj => hall j ((hnot2 j).2 (Or.inr hj))⟩
      rintro ⟨_, j, hj, hjn⟩
      exact hjn (hall j ((hnot2 j).2 (Or.inl hj)))
  have hm' : (m : ZMod (p ^ k)) = (p : ZMod (p ^ k))^2 * ((m / p^2 : ℤ) : ZMod (p ^ k)) := by
    conv_lhs => rw [← Int.mul_ediv_cancel' hm]
    push_cast; ring
  have heval : ∀ z, evalIn (ZMod (p ^ k)) (diag a) (Ψ z) = (p : ZMod (p ^ k))^2 * ∑ i, (b i : ZMod (p ^ k)) * z i ^ 2 := by
    intro z
    rw [hevalz, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S2
    · rw [hΨS2 z i hi, hab i hi]; push_cast; ring
    · rw [hΨ, hab' i hi]; simp only [e, if_neg hi]; ring
  have key : ∀ z, R (Ψ z) ↔ P (C z) := by
    intro z
    simp only [R, P]
    rw [hRbad]
    apply and_congr
    · rw [heval, hm', ← sub_eq_zero, ← mul_sub, hmulz k 2 (by omega), map_sub, sub_eq_zero, hevalz]
      simp only [map_sum, map_mul, map_pow, map_intCast, hC]
    · rw [and_iff_right (fun i hi => hΨn z i hi)]
      exact exists_congr (fun i => and_congr_right (fun hi => by rw [hΨS2 z i hi, hC, hdvdC]))
  have hrange : ∀ x, R x → x ∈ Ψ.range := by
    intro x hx
    have hall : ∀ i, i ∉ S2 → ∃ c, x i = (p : ZMod (p ^ k)) * c := ((hRbad x).1 hx.2).1
    choose! q hq using hall
    refine ⟨fun i => if i ∈ S2 then x i else q i, ?_⟩
    ext i
    rw [hΨ]
    by_cases hi : i ∈ S2
    · simp [e, hi]
    · simp only [e, if_neg hi, pow_one]; exact (hq i hi).symm
  have hCsurj : ∀ y, y ∈ C.range := fun y => ⟨fun i => (ZMod.castHom_surjective hdiv (y i)).choose, by ext i; simp only [hC]; exact (ZMod.castHom_surjective hdiv (y i)).choose_spec⟩
  have h1 := A Ψ R
  have h2 := A C P
  have e1 : {x // x ∈ Ψ.range ∧ R x} ≃ {x // R x} := Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨hrange x h, h⟩⟩)
  have e2 : {z // R (Ψ z)} ≃ {z // P (C z)} := Equiv.subtypeEquivRight key
  have e3 : {y // y ∈ C.range ∧ P y} ≃ {y // P y} := Equiv.subtypeEquivRight (fun y => ⟨fun h => h.2, fun h => ⟨hCsurj y, h⟩⟩)
  rw [Nat.card_congr e1, Nat.card_congr e2] at h1
  rw [Nat.card_congr e3] at h2
  have hfilt : Finset.univ.filter (fun i => ¬ i ∈ S2) = S₀ a p ∪ S₁ a p := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; exact hnot2 i
  have hdisj : Disjoint (S₀ a p) (S₁ a p) := by
    simp only [S₀, S₁]; exact Finset.disjoint_filter.2 (fun i _ h0 h1 => by omega)
  have hs : (S₀ a p).card + (S₁ a p).card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    simpa using Finset.card_le_univ (S₀ a p ∪ S₁ a p)
  have hkerΨ : Nat.card Ψ.ker = p ^ ((S₀ a p).card + (S₁ a p).card) := by
    have e4 : Ψ.ker ≃ ∀ i, {t : ZMod (p ^ k) // (p : ZMod (p ^ k)) ^ (e i) * t = 0} :=
      (Equiv.subtypeEquivRight (fun z => by simp [AddMonoidHom.mem_ker, funext_iff, hΨ])).trans (Equiv.subtypePiEquivPi)
    rw [Nat.card_congr e4, Nat.card_pi]
    rw [Finset.prod_congr rfl (fun i _ => K k (e i) (by simp only [e]; split_ifs <;> omega))]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    simp only [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one, zero_add, hfilt, Finset.card_union_of_disjoint hdisj]
  have hkerC : Nat.card C.ker = p ^ (2 * n) := by
    have h := A C (fun _ => True)
    have e5 : {h // h ∈ C.range ∧ True} ≃ (Fin n → ZMod (p ^ (k-2))) := (Equiv.subtypeEquivRight (fun y => by simp only [and_true]; exact iff_of_true (hCsurj y) trivial)).trans (Equiv.subtypeUnivEquiv (fun _ => trivial))
    rw [Nat.card_congr e5, Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_pi, Nat.card_pi] at h
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    have : (p ^ k) ^ n = p ^ (2 * n) * (p ^ (k - 2)) ^ n := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; rw [← Nat.add_mul]; congr 1; omega
    rw [this] at h
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm
  rw [hkerΨ] at h1
  rw [hkerC] at h2
  show Nat.card {x // R x} = p ^ (2 * n - (S₀ a p).card - (S₁ a p).card) * Nat.card {y // P y}
  have hpow : p ^ (2 * n) = p ^ ((S₀ a p).card + (S₁ a p).card) * p ^ (2 * n - (S₀ a p).card - (S₁ a p).card) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, h1, mul_assoc] at h2
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h2

end QuadFormsKB.LocalDensity
