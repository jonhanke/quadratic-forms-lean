/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, an odd binary pair $\langle a, b\rangle$ with $a + b \equiv 0 \pmod 4$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicRootGroup.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ (`locGram`, $G_{kk} = 2Q(b_k)$); the root group `rootGroup`.

**Proves**
* `pair_adm`: for $\alpha = G_{l_1l_1}$, $G_{l_2l_2} = \alpha r$ ($r \in \mathbb Z_2$) and orthogonal $b_{l_1}, b_{l_2}$,
  every $sb_{l_1} + tb_{l_2}$ ($s, t \in \mathbb Z_2$) with $s^2 + rt^2$ a unit is a $2$-adic root vector, of norm
  $(\alpha/2)(s^2 + rt^2)$;
* `sqClassOf_pair_mem`: two unit values of $s^2 + rt^2$ have product in the root group;
* `units_le_rootGroup_of_pair`: if $\lvert G_{l_1l_1}\rvert = \lvert G_{l_2l_2}\rvert$ and
  $\lvert G_{l_1l_1} + G_{l_2l_2}\rvert \le \lvert 4G_{l_1l_1}\rvert$ (so $r = G_{l_2l_2}/G_{l_1l_1}$ is a unit
  $\equiv 3 \pmod 4$), every unit class lies in the root group (via the values $1$, $1 + 4r \equiv 5$, $r$ and
  Cassels' `unit_cover`);
* `units_le_rootGroup_of_pair'`: the same, stated with a scalar $c$ normalizing the pair.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicTernary

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **Admissible symmetries from two orthogonal basis vectors.** If $b_{l_1}, b_{l_2}$ are orthogonal to all other
basis vectors, $G_{l_1l_1} = \alpha \ne 0$ and $G_{l_2l_2} = \alpha r$ with $r \in \mathbb Z_2$, then for
$s, t \in \mathbb Z_2$ with $s^2 + rt^2$ a unit, $x = sb_{l_1} + tb_{l_2}$ is a root vector of norm
$(\alpha/2)(s^2 + rt^2)$. -/
theorem pair_adm (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n} (hij : i ≠ j)
    (horth_i : ∀ m, m ≠ i → locGram Q v γ m i = 0) (horth_j : ∀ m, m ≠ j → locGram Q v γ m j = 0)
    {α : Fv} (hα : α ≠ 0) {r : 𝔬} (hgi : locGram Q v γ i i = α) (hgj : locGram Q v γ j j = α * r)
    (s t : 𝔬) (hB : IsUnit (s ^ 2 + r * t ^ 2)) :
    ∃ x, Q.evalIn Fv x = α / 2 * ((s ^ 2 + r * t ^ 2 : 𝔬) : Fv) ∧ symm Q Fv x ∈ locStabV Q v L := by
  set c : Fin n → Fv := Pi.single i (s : Fv) + Pi.single j (t : Fv) with hc
  have hci : c i = s := by simp [hc, hij]
  have hcj : c j = t := by simp [hc, hij.symm]
  have hcm : ∀ m, m ≠ i → m ≠ j → c m = 0 := by
    intro m h1 h2; simp [hc, h1, h2]
  have hcstd : c ∈ std v :=
    (std v).add_mem (single_mem_std i (vle_one s)) (single_mem_std j (vle_one t))
  have hdiag : ∀ m, (locGram Q v γ *ᵥ c) m = locGram Q v γ m m * c m := fun m =>
    gram_mulVec_diag_of γ fun l hl hcl => by
      have : l = i ∨ l = j := by
        by_contra h
        push Not at h
        exact hcl (hcm l h.1 h.2)
      rcases this with rfl | rfl
      · exact horth_i m (Ne.symm hl)
      · exact horth_j m (Ne.symm hl)
  have hdot : ∀ d : Fin n → Fv, c ⬝ᵥ d = s * d i + t * d j := fun d => by
    rw [hc, add_dotProduct, single_dotProduct, single_dotProduct]
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hQ2 : 2 * Q.evalIn Fv (γ.val *ᵥ c) = α * ((s ^ 2 + r * t ^ 2 : 𝔬) : Fv) := by
    rw [two_mul_evalIn_locGram, hdot, hdiag i, hdiag j, hci, hcj, hgi, hgj]
    push_cast
    ring
  have hQx : Q.evalIn Fv (γ.val *ᵥ c) = α / 2 * ((s ^ 2 + r * t ^ 2 : 𝔬) : Fv) := by
    rw [div_mul_eq_mul_div, eq_div_iff h2ne]
    linear_combination hQ2
  have hBne : ((s ^ 2 + r * t ^ 2 : 𝔬) : Fv) ≠ 0 := fun h => hB.ne_zero (by exact_mod_cast h)
  have hvB : Valued.v ((s ^ 2 + r * t ^ 2 : 𝔬) : Fv) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hB
  have hx0 : Q.evalIn Fv (γ.val *ᵥ c) ≠ 0 := by
    rw [hQx]; exact mul_ne_zero (div_ne_zero hα h2ne) hBne
  refine ⟨γ.val *ᵥ c, hQx, symm_mem_of_gram L γ hγ hcstd hx0 fun m => ?_⟩
  have hle : Valued.v α ≤ Valued.v (Q.evalIn Fv (γ.val *ᵥ c)) := by
    rw [hQx, map_mul, hvB, mul_one, map_div₀,
      le_div_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ne))]
    exact mul_le_of_le_one_right' valued_two_le_one
  refine le_trans ?_ hle
  have hbd : ∀ (g : Fv) (x y : 𝔬), g = α * x → Valued.v (g * y) ≤ Valued.v α := by
    intro g x y hg
    rw [hg, mul_assoc, map_mul, map_mul]
    calc Valued.v α * (Valued.v (x : Fv) * Valued.v (y : Fv)) ≤ Valued.v α * (1 * 1) :=
          mul_le_mul' le_rfl (mul_le_mul' (vle_one x) (vle_one y))
      _ = Valued.v α := by simp
  rw [hdiag m]
  by_cases hmi : m = i
  · subst hmi; rw [hci]; exact hbd _ 1 s (by rw [hgi]; simp)
  by_cases hmj : m = j
  · subst hmj; rw [hcj]; exact hbd _ r t hgj
  rw [hcm m hmi hmj, mul_zero, map_zero]
  exact zero_le

/-- **Two unit values of $s^2 + rt^2$ give an element of the root group.** -/
theorem sqClassOf_pair_mem (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n}
    (hij : i ≠ j) (horth_i : ∀ m, m ≠ i → locGram Q v γ m i = 0)
    (horth_j : ∀ m, m ≠ j → locGram Q v γ m j = 0)
    {α : Fv} (hα : α ≠ 0) {r : 𝔬} (hgi : locGram Q v γ i i = α) (hgj : locGram Q v γ j j = α * r)
    {s t s' t' : 𝔬} (h1 : IsUnit (s ^ 2 + r * t ^ 2)) (h1' : IsUnit (s' ^ 2 + r * t' ^ 2)) :
    sqClassOf (((s ^ 2 + r * t ^ 2) * (s' ^ 2 + r * t' ^ 2) : 𝔬) : Fv) ∈ rootGroup Q L v := by
  obtain ⟨x, hx, hxs⟩ := pair_adm γ hγ hij horth_i horth_j hα hgi hgj s t h1
  obtain ⟨y, hy, hys⟩ := pair_adm γ hγ hij horth_i horth_j hα hgi hgj s' t' h1'
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hB : ((s ^ 2 + r * t ^ 2 : 𝔬) : Fv) ≠ 0 := fun h => h1.ne_zero (by exact_mod_cast h)
  have hB' : ((s' ^ 2 + r * t' ^ 2 : 𝔬) : Fv) ≠ 0 := fun h => h1'.ne_zero (by exact_mod_cast h)
  have hx0 : Q.evalIn Fv x ≠ 0 := by rw [hx]; exact mul_ne_zero (div_ne_zero hα h2ne) hB
  have hy0 : Q.evalIn Fv y ≠ 0 := by rw [hy]; exact mul_ne_zero (div_ne_zero hα h2ne) hB'
  have hmem := sqClassOf_mul_mem_rootGroup (L := L) ⟨hx0, hxs⟩ ⟨hy0, hys⟩
  have e : Q.evalIn Fv x * Q.evalIn Fv y =
      (α / 2) ^ 2 * (((s ^ 2 + r * t ^ 2) * (s' ^ 2 + r * t' ^ 2) : 𝔬) : Fv) := by
    rw [hx, hy]; push_cast; ring
  rwa [e, sqClassOf_sq_mul (div_ne_zero hα h2ne) (by push_cast; exact mul_ne_zero hB hB')] at hmem

/-- **Units from the core data** $G_{l_1l_1} = \alpha$, $G_{l_2l_2} = \alpha r$ with $r \equiv 3 \pmod 4$. -/
theorem units_le_rootGroup_of_pair_core (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {i j : Fin n} (hij : i ≠ j)
    (horth_i : ∀ m, m ≠ i → locGram Q v γ m i = 0) (horth_j : ∀ m, m ≠ j → locGram Q v γ m j = 0)
    {α : Fv} (hα : α ≠ 0) {r m : 𝔬} (hr : IsUnit r) (hrm : r = -1 + 4 * m)
    (hgi : locGram Q v γ i i = α) (hgj : locGram Q v γ j j = α * r) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  have hcoe0 : ∀ x : 𝔬, IsUnit x → (x : Fv) ≠ 0 := fun x hx h => hx.ne_zero (by exact_mod_cast h)
  obtain ⟨a, ha⟩ := Rl.exists h2 m
  have hRr : Rl r (-1 + 4 * a) :=
    hrm ▸ Rl.add (Rl.neg (by simpa using Rl.natCast (v := v) 1)) (Rl.mul (by simpa using Rl.natCast (v := v) 4) ha)
  have hcase : ∀ a : ZMod 8, (-1 + 4 * a = 3 ∨ -1 + 4 * a = 7) := by decide
  have hr37 : Rl r 3 ∨ Rl r 7 := by
    rcases hcase a with h | h
    · exact Or.inl (h ▸ hRr)
    · exact Or.inr (h ▸ hRr)
  have u5 : IsUnit (1 + 4 * r) := by
    have := isUnit_one_add_two_mul h2 (2 * r); convert this using 1; ring
  have hR5 : Rl (1 + 4 * r) 5 := by
    rcases hr37 with h | h
    · have := Rl.add (Rl.natCast (v := v) 1) (Rl.mul (Rl.natCast (v := v) 4) h)
      have e : ((1 : ℕ) : ZMod 8) + ((4 : ℕ) : ZMod 8) * 3 = 5 := by decide
      rw [e] at this; simpa using this
    · have := Rl.add (Rl.natCast (v := v) 1) (Rl.mul (Rl.natCast (v := v) 4) h)
      have e : ((1 : ℕ) : ZMod 8) + ((4 : ℕ) : ZMod 8) * 7 = 5 := by decide
      rw [e] at this; simpa using this
  have u1 : IsUnit ((1 : 𝔬) ^ 2 + r * 0 ^ 2) := by simp
  have u2 : IsUnit ((1 : 𝔬) ^ 2 + r * 2 ^ 2) := by convert u5 using 1; ring
  have u3 : IsUnit ((0 : 𝔬) ^ 2 + r * 1 ^ 2) := by simpa using hr
  have hM5 : sqClassOf (((1 + 4 * r : 𝔬)) : Fv) ∈ rootGroup Q L v := by
    have := sqClassOf_pair_mem γ hγ hij horth_i horth_j hα hgi hgj u2 u1
    have e : (((1 : 𝔬) ^ 2 + r * 2 ^ 2) * (1 ^ 2 + r * 0 ^ 2) : 𝔬) = 1 + 4 * r := by ring
    rwa [e] at this
  have hMr : sqClassOf ((r : 𝔬) : Fv) ∈ rootGroup Q L v := by
    have := sqClassOf_pair_mem γ hγ hij horth_i horth_j hα hgi hgj u3 u1
    have e : (((0 : 𝔬) ^ 2 + r * 1 ^ 2) * (1 ^ 2 + r * 0 ^ 2) : 𝔬) = r := by ring
    rwa [e] at this
  have key := unit_cover h2 (fun x : 𝔬 => sqClassOf (x : Fv) ∈ rootGroup Q L v)
    (fun x y hx hy hMx hMy => by
      show sqClassOf (((x * y : 𝔬)) : Fv) ∈ rootGroup Q L v
      push_cast
      rw [sqClassOf_mul (hcoe0 x hx) (hcoe0 y hy)]
      exact (rootGroup Q L v).mul_mem hMx hMy)
    (fun x s hx hs => by
      show sqClassOf (((x * s ^ 2 : 𝔬)) : Fv) ∈ rootGroup Q L v ↔ sqClassOf (x : Fv) ∈ rootGroup Q L v
      push_cast
      rw [mul_comm, sqClassOf_sq_mul (hcoe0 s hs) (hcoe0 x hx)])
    (by show sqClassOf ((1 : 𝔬) : Fv) ∈ rootGroup Q L v
        push_cast; rw [sqClassOf_one]; exact (rootGroup Q L v).one_mem)
    hM5 hR5 hMr hr37
  intro u hu
  exact key (toO v u hu.le) (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu)

/-- **An odd binary pair $\langle a, b\rangle$ with $a + b \equiv 0 \pmod 4$ puts every unit class in the root
group** (Conway–Sloane §9.5, p. 391). Here $b_{l_1}, b_{l_2}$ ($l_1 \ne l_2$) are orthogonal to all other basis
vectors, $\alpha = G_{l_1l_1} \ne 0$, $\beta = G_{l_2l_2}$ with $\lvert\alpha\rvert = \lvert\beta\rvert$ and
$\lvert\alpha + \beta\rvert \le \lvert 4\alpha\rvert$, i.e. $\beta/\alpha$ is a unit $\equiv 3 \pmod 4$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic root vectors of an odd binary constituent ⟨a, b⟩ with a + b ≡ 0 mod 4)"]
theorem units_le_rootGroup_of_pair (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {l₁ l₂ : Fin n} (hne : l₁ ≠ l₂)
    (horth₁ : ∀ i, i ≠ l₁ → locGram Q v γ i l₁ = 0) (horth₂ : ∀ i, i ≠ l₂ → locGram Q v γ i l₂ = 0)
    (hα0 : locGram Q v γ l₁ l₁ ≠ 0)
    (hv : Valued.v (locGram Q v γ l₁ l₁) = Valued.v (locGram Q v γ l₂ l₂))
    (hsum : Valued.v (locGram Q v γ l₁ l₁ + locGram Q v γ l₂ l₂) ≤ Valued.v (4 * locGram Q v γ l₁ l₁)) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  set α := locGram Q v γ l₁ l₁ with hα
  set β := locGram Q v γ l₂ l₂ with hβ
  have hvα : Valued.v α ≠ 0 := (Valuation.ne_zero_iff _).mpr hα0
  have h4 : (4 : Fv) ≠ 0 := by norm_num
  have hv4 : Valued.v (4 : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr h4
  have hrv : Valued.v (β / α) = 1 := by
    rw [map_div₀, ← hv]; exact div_self hvα
  have hr1 : Valued.v (β / α) ≤ 1 := hrv.le
  have hmv : Valued.v ((β / α + 1) / 4) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hv4)]
    have e : β / α + 1 = (α + β) / α := by field_simp; ring
    rw [e, map_div₀, div_le_iff₀ (zero_lt_iff.mpr hvα)]
    calc Valued.v (α + β) ≤ Valued.v (4 * α) := hsum
      _ = Valued.v (4 : Fv) * Valued.v α := map_mul _ _ _
  have hr : IsUnit (toO v (β / α) hr1) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hrv
  have hrm : toO v (β / α) hr1 = -1 + 4 * toO v ((β / α + 1) / 4) hmv := by
    have : ((toO v (β / α) hr1 : 𝔬) : Fv) = -1 + 4 * ((toO v ((β / α + 1) / 4) hmv : 𝔬) : Fv) := by
      show β / α = -1 + 4 * ((β / α + 1) / 4)
      field_simp; ring
    apply Subtype.ext
    push_cast
    exact this
  refine units_le_rootGroup_of_pair_core h2 γ hγ hne horth₁ horth₂ (α := α) hα0 hr hrm rfl ?_
  show β = α * (β / α)
  field_simp

/-- **The same, normalized by a scalar $c$**: for $c \ne 0$ with $\lvert c\alpha/2\rvert = 1$,
$\lvert c\beta/2\rvert = 1$ and $\lvert c(\alpha + \beta)/2\rvert \le \lvert 4\rvert$, where
$\alpha = G_{l_1l_1}$, $\beta = G_{l_2l_2}$ (the form used in `PairGlue.Data`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic root vectors of an odd binary constituent ⟨a, b⟩ with a + b ≡ 0 mod 4, scaled form)"]
theorem units_le_rootGroup_of_pair' (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {l₁ l₂ : Fin n} (hne : l₁ ≠ l₂)
    (horth₁ : ∀ i, i ≠ l₁ → locGram Q v γ i l₁ = 0) (horth₂ : ∀ i, i ≠ l₂ → locGram Q v γ i l₂ = 0)
    {c : Fv} (hc : c ≠ 0)
    (hα : Valued.v (c * locGram Q v γ l₁ l₁ / 2) = 1) (hβ : Valued.v (c * locGram Q v γ l₂ l₂ / 2) = 1)
    (hsum : Valued.v (c * (locGram Q v γ l₁ l₁ + locGram Q v γ l₂ l₂) / 2) ≤ Valued.v (4 : Fv)) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hcv : 0 < Valued.v (c / 2) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (div_ne_zero hc h2ne))
  have e : ∀ x : Fv, c * x / 2 = c / 2 * x := fun x => by ring
  rw [e, map_mul] at hα hβ
  rw [e, map_mul] at hsum
  have hα0 : locGram Q v γ l₁ l₁ ≠ 0 := fun h => by rw [h, map_zero, mul_zero] at hα; exact zero_ne_one hα
  refine units_le_rootGroup_of_pair h2 γ hγ hne horth₁ horth₂ hα0 ?_ ?_
  · exact mul_left_cancel₀ hcv.ne' (hα.trans hβ.symm)
  · rw [map_mul]
    refine le_of_mul_le_mul_left ?_ hcv
    calc Valued.v (c / 2) * Valued.v (locGram Q v γ l₁ l₁ + locGram Q v γ l₂ l₂) ≤ Valued.v (4 : Fv) := hsum
      _ = Valued.v (4 : Fv) * (Valued.v (c / 2) * Valued.v (locGram Q v γ l₁ l₁)) := by rw [hα, mul_one]
      _ = _ := mul_left_comm _ _ _

end QuadFormsKB.ConwaySloane