/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for ternary unary-constituent shapes

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$, for $2$-adic Jordan shapes containing three
mutually orthogonal $1$-dimensional summands $\langle a_i\rangle, \langle a_j\rangle, \langle a_k\rangle$ of the
patterns of Cassels' Lemma 3.8 (ii), (iii) (Ch. 11, p. 214).

**Layer.** As in `Section9Theorem18DyadicRootGroup.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ (`locGram`, $G_{kk} = 2Q(b_k)$); the root group `rootGroup`.

**Proves**
* `sqClassOf_ternary_pair_mem`: for $b_i, b_j, b_k$ spanning an orthogonal summand with $G_{ii} = wp$, $G_{jj} = wq$,
  $G_{kk} = wr$, two unit values $B(s,t,z)$, $B(s',t',z')$ of $B = ps^2 + qt^2 + rz^2$ have product in the root
  group (the vectors $sb_i + tb_j + zb_k$ are root vectors, Cassels' `ternary_adm`);
* `units_le_rootGroup_of_ternary`: in the patterns of Cassels' Lemma 3.8 (ii), (iii) (`Pat`), every unit class lies
  in the root group (Cassels' `pattern_cover` and `unit_cover`, with the root group in place of $\theta$);
* `rootGroup_eq_top_of_units_of_basis_pair`: if every unit class lies in the root group and two basis vectors
  $b_a, b_b$ spanning $1$-dimensional orthogonal summands have $G_{aa}G_{bb}$ of odd order, the root group is
  everything;
* the shapes (orders $\operatorname{ord}_2 G_{ii}, \operatorname{ord}_2 G_{jj}, \operatorname{ord}_2 G_{kk}$):
  `theorem18OnlyIf_of_ternary_adjacent` $(e, e, e \pm 1)$, `theorem18OnlyIf_of_ternary_chain` $(e, e+1, e+2)$, and
  `theorem18OnlyIf_of_ternary_equal_single` $(e, e, e)$ together with a fourth $1$-dimensional summand $b_l$ with
  $\operatorname{ord}_2 G_{ll} - e$ odd: in each case the root group is everything, so Theorem 18 ("only if") holds.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicRootGroup

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **Two unit values of the ternary form give an element of the root group.** -/
theorem sqClassOf_ternary_pair_mem (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fv} (hw : w ≠ 0) {p q r : 𝔬}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r)
    {s t z s' t' z' : 𝔬} (h1 : IsUnit (Bf p q r s t z)) (h1' : IsUnit (Bf p q r s' t' z')) :
    sqClassOf ((Bf p q r s t z * Bf p q r s' t' z' : 𝔬) : Fv) ∈ rootGroup Q L v := by
  obtain ⟨x, hx, hxs⟩ := ternary_adm L γ hγ hij hik hjk horth hw hgi hgj hgk s t z h1
  obtain ⟨y, hy, hys⟩ := ternary_adm L γ hγ hij hik hjk horth hw hgi hgj hgk s' t' z' h1'
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have hB : ((Bf p q r s t z : 𝔬) : Fv) ≠ 0 := fun h => h1.ne_zero (by exact_mod_cast h)
  have hB' : ((Bf p q r s' t' z' : 𝔬) : Fv) ≠ 0 := fun h => h1'.ne_zero (by exact_mod_cast h)
  have hx0 : Q.evalIn Fv x ≠ 0 := by rw [hx]; exact mul_ne_zero (div_ne_zero hw h2ne) hB
  have hy0 : Q.evalIn Fv y ≠ 0 := by rw [hy]; exact mul_ne_zero (div_ne_zero hw h2ne) hB'
  have hmem := sqClassOf_mul_mem_rootGroup (L := L) ⟨hx0, hxs⟩ ⟨hy0, hys⟩
  have e : Q.evalIn Fv x * Q.evalIn Fv y =
      (w / 2) ^ 2 * ((Bf p q r s t z * Bf p q r s' t' z' : 𝔬) : Fv) := by
    rw [hx, hy]; push_cast; ring
  rwa [e, sqClassOf_sq_mul (div_ne_zero hw h2ne) (by push_cast; exact mul_ne_zero hB hB')] at hmem

/-- **The ternary patterns put every unit class in the root group** (Cassels, Lemma 3.8 (ii), (iii), p. 214, for
the root group instead of $\theta$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic root vectors of three unary Jordan constituents)"]
theorem units_le_rootGroup_of_ternary (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fv} (hw : w ≠ 0) {p q r : 𝔬} (hpat : Pat p q r)
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r) :
    ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v := by
  obtain ⟨⟨s, t, z, s', t', z', h1, h1', h5⟩, ⟨s2, t2, z2, s3, t3, z3, h2', h2'', h37⟩⟩ :=
    pattern_cover h2 hpat
  have hcoe0 : ∀ x : 𝔬, IsUnit x → (x : Fv) ≠ 0 := fun x hx h => hx.ne_zero (by exact_mod_cast h)
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
    (sqClassOf_ternary_pair_mem γ hγ hij hik hjk horth hw hgi hgj hgk h1 h1') h5
    (sqClassOf_ternary_pair_mem γ hγ hij hik hjk horth hw hgi hgj hgk h2' h2'') h37
  intro u hu
  exact key (toO v u hu.le) (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu)

/-- **Unit classes and one odd product of basis root vectors give everything**: if every unit class lies in the
root group and $b_a, b_b$ span $1$-dimensional orthogonal summands ($G_{ma} = 0$ for $m \ne a$, $G_{mb} = 0$ for
$m \ne b$) with $\lvert G_{aa}G_{bb}\rvert = e^{2m+1}$, the root group is everything
($Q(b_a)Q(b_b) = G_{aa}G_{bb}/4$ has odd order). -/
theorem rootGroup_eq_top_of_units_of_basis_pair (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v)
    {a b : Fin n} (horth_a : ∀ m, m ≠ a → locGram Q v γ m a = 0) (horth_b : ∀ m, m ≠ b → locGram Q v γ m b = 0)
    (m : ℤ) (hodd : Valued.v (locGram Q v γ a a * locGram Q v γ b b) = exp (2 * m + 1)) :
    rootGroup Q L v = ⊤ := by
  have hprod0 : locGram Q v γ a a * locGram Q v γ b b ≠ 0 := fun h => by
    rw [h, map_zero] at hodd; exact exp_ne_zero.symm hodd
  have ha0 : locGram Q v γ a a ≠ 0 := left_ne_zero_of_mul hprod0
  have hb0 : locGram Q v γ b b ≠ 0 := right_ne_zero_of_mul hprod0
  have hmem := sqClassOf_mul_mem_rootGroup (isRootVector_basis_of_orth γ hγ a horth_a ha0)
    (isRootVector_basis_of_orth γ hγ b horth_b hb0)
  rw [evalIn_basis_eq, evalIn_basis_eq] at hmem
  refine rootGroup_eq_top_of_units_of_odd h2 hunits (m + 1) ?_ hmem
  have hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ) := valued_two_dyadic v h2
  rw [show locGram Q v γ a a / 2 * (locGram Q v γ b b / 2) =
      locGram Q v γ a a * locGram Q v γ b b * ((2 : Fv)⁻¹) ^ 2 by ring, map_mul, map_pow, map_inv₀, hv2, hodd,
    ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← exp_add]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- $\lvert ab\rvert$ has odd order when $\lvert b\rvert = \lvert 2a\rvert$. -/
theorem exists_odd_of_eq_two_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {a b : Fv} (ha : a ≠ 0)
    (h : Valued.v b = Valued.v (2 * a)) : ∃ m : ℤ, Valued.v (a * b) = exp (2 * m + 1) := by
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  refine ⟨log (Valued.v a) - 1, ?_⟩
  rw [map_mul, h, map_mul, valued_two_dyadic v h2, ← exp_log hva, ← exp_add, ← exp_add, log_exp]
  congr 1
  ring

/-- The diagonal entries of an orthogonal summand of a nondegenerate lattice are nonzero. -/
theorem locGram_diag_ne_zero_of_orth (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv) {l : Fin n}
    (horth : ∀ m, m ≠ l → locGram Q v γ l m = 0) : locGram Q v γ l l ≠ 0 := fun h0 => by
  refine locGram_det_ne_zero hQ γ (Matrix.det_eq_zero_of_row_eq_zero l fun m => ?_)
  by_cases hm : m = l
  · subst hm; exact h0
  · exact horth m hm

/-- **Shape $(e, e, e \pm 1)$** (Cassels, Lemma 3.8 (ii), second and third patterns): $b_i, b_j, b_k$ span an
orthogonal summand of $L_2$ with $\lvert G_{jj}\rvert = \lvert G_{ii}\rvert$ and $\lvert G_{kk}\rvert =
\lvert 2G_{ii}\rvert$ or $\lvert G_{ii}\rvert = \lvert 2G_{kk}\rvert$. Then the root group is everything and Theorem 18
("only if") holds. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': unary Jordan constituents of orders e, e, e ± 1)"]
theorem theorem18OnlyIf_of_ternary_adjacent (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    (hji : Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ i i))
    (hk : Valued.v (locGram Q v γ k k) = Valued.v (2 * locGram Q v γ i i) ∨
      Valued.v (locGram Q v γ i i) = Valued.v (2 * locGram Q v γ k k)) :
    Theorem18OnlyIf Q L v hQ := by
  have hrow : ∀ l, (l = i ∨ l = j ∨ l = k) → locGram Q v γ l l ≠ 0 := fun l hl =>
    locGram_diag_ne_zero_of_orth hQ γ fun m hm => horth l m (Ne.symm hm) hl
  have hcol : ∀ l, (l = i ∨ l = j ∨ l = k) → ∀ m, m ≠ l → locGram Q v γ m l = 0 := fun l hl m hm => by
    rw [locGram_symm']; exact horth l m (Ne.symm hm) hl
  have hgi0 := hrow i (Or.inl rfl)
  have hgk0 := hrow k (Or.inr (Or.inr rfl))
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  obtain ⟨uj, huj, hj⟩ := exists_unit_ratio hgi0 hji
  refine theorem18OnlyIf_of_eq_top hQ ?_
  rcases hk with hk | hk
  · obtain ⟨uk, huk, hk'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgi0) hk
    have hunits := units_le_rootGroup_of_ternary h2 γ hγ hij hik hjk horth hgi0 (p := 1) (q := uj)
      (r := 2 * uk) (Or.inr (Or.inl ⟨isUnit_one, huj, uk, huk, rfl⟩)) (by simp) hj
      (by rw [hk']; push_cast; rw [coe_two_eq]; ring)
    obtain ⟨m, hm⟩ := exists_odd_of_eq_two_mul h2 hgi0 hk
    exact rootGroup_eq_top_of_units_of_basis_pair h2 γ hγ hunits (hcol i (Or.inl rfl))
      (hcol k (Or.inr (Or.inr rfl))) m hm
  · obtain ⟨ui, hui, hi'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgk0) hk
    obtain ⟨uj', huj', hj'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgk0) (hji.trans hk)
    have hunits := units_le_rootGroup_of_ternary h2 γ hγ (Ne.symm hik) (Ne.symm hjk) hij
      (fun l m hlm hl => horth l m hlm (by tauto)) hgk0 (p := 1) (q := 2 * ui) (r := 2 * uj')
      (Or.inr (Or.inr (Or.inl ⟨isUnit_one, ui, uj', hui, huj', rfl, rfl⟩))) (by simp)
      (by rw [hi']; push_cast; rw [coe_two_eq]; ring) (by rw [hj']; push_cast; rw [coe_two_eq]; ring)
    obtain ⟨m, hm⟩ := exists_odd_of_eq_two_mul h2 hgk0 hk
    exact rootGroup_eq_top_of_units_of_basis_pair h2 γ hγ hunits (hcol k (Or.inr (Or.inr rfl)))
      (hcol i (Or.inl rfl)) m hm

/-- **Shape $(e, e+1, e+2)$** (Cassels, Lemma 3.8 (iii)): $b_i, b_j, b_k$ span an orthogonal summand of $L_2$ with
$\lvert G_{jj}\rvert = \lvert 2G_{ii}\rvert$ and $\lvert G_{kk}\rvert = \lvert 4G_{ii}\rvert$. Then the root group is
everything and Theorem 18 ("only if") holds. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': unary Jordan constituents of orders e, e + 1, e + 2)"]
theorem theorem18OnlyIf_of_ternary_chain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    (hj : Valued.v (locGram Q v γ j j) = Valued.v (2 * locGram Q v γ i i))
    (hk : Valued.v (locGram Q v γ k k) = Valued.v (4 * locGram Q v γ i i)) :
    Theorem18OnlyIf Q L v hQ := by
  have hgi0 : locGram Q v γ i i ≠ 0 :=
    locGram_diag_ne_zero_of_orth hQ γ fun m hm => horth i m (Ne.symm hm) (Or.inl rfl)
  have hcol : ∀ l, (l = i ∨ l = j ∨ l = k) → ∀ m, m ≠ l → locGram Q v γ m l = 0 := fun l hl m hm => by
    rw [locGram_symm']; exact horth l m (Ne.symm hm) hl
  have h2ne : (2 : Fv) ≠ 0 := two_ne_zero
  have h4ne : (4 : Fv) ≠ 0 := by norm_num
  obtain ⟨uj, huj, hj'⟩ := exists_unit_ratio (mul_ne_zero h2ne hgi0) hj
  obtain ⟨uk, huk, hk'⟩ := exists_unit_ratio (mul_ne_zero h4ne hgi0) hk
  have hunits := units_le_rootGroup_of_ternary h2 γ hγ hij hik hjk horth hgi0 (p := 1) (q := 2 * uj)
    (r := 4 * uk) (Or.inr (Or.inr (Or.inr ⟨isUnit_one, uj, uk, huj, huk, rfl, rfl⟩))) (by simp)
    (by rw [hj']; push_cast; rw [coe_two_eq]; ring) (by rw [hk']; push_cast; rw [coe_four_eq]; ring)
  obtain ⟨m, hm⟩ := exists_odd_of_eq_two_mul h2 hgi0 hj
  exact theorem18OnlyIf_of_eq_top hQ (rootGroup_eq_top_of_units_of_basis_pair h2 γ hγ hunits
    (hcol i (Or.inl rfl)) (hcol j (Or.inr (Or.inl rfl))) m hm)

/-- **Shape $(e, e, e)$ plus a unary constituent at odd relative order** (Cassels, Lemma 3.8 (ii), first pattern):
$b_i, b_j, b_k$ span an orthogonal summand of $L_2$ with $\lvert G_{jj}\rvert = \lvert G_{kk}\rvert =
\lvert G_{ii}\rvert$, and $b_l$ spans a $1$-dimensional orthogonal summand with $\lvert G_{ii}G_{ll}\rvert =
e^{2m+1}$. Then the root group is everything and Theorem 18 ("only if") holds. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': three unary Jordan constituents of equal order and one at odd relative order)"]
theorem theorem18OnlyIf_of_ternary_equal_single (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ a b, a ≠ b → (a = i ∨ a = j ∨ a = k) → locGram Q v γ a b = 0)
    (hji : Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ i i))
    (hki : Valued.v (locGram Q v γ k k) = Valued.v (locGram Q v γ i i))
    (hlorth : ∀ a, a ≠ l → locGram Q v γ a l = 0) (m : ℤ)
    (hodd : Valued.v (locGram Q v γ i i * locGram Q v γ l l) = exp (2 * m + 1)) :
    Theorem18OnlyIf Q L v hQ := by
  have hgi0 : locGram Q v γ i i ≠ 0 :=
    locGram_diag_ne_zero_of_orth hQ γ fun a ha => horth i a (Ne.symm ha) (Or.inl rfl)
  have hcoli : ∀ a, a ≠ i → locGram Q v γ a i = 0 := fun a ha => by
    rw [locGram_symm']; exact horth i a (Ne.symm ha) (Or.inl rfl)
  obtain ⟨uj, huj, hj⟩ := exists_unit_ratio hgi0 hji
  obtain ⟨uk, huk, hk⟩ := exists_unit_ratio hgi0 hki
  have hunits := units_le_rootGroup_of_ternary h2 γ hγ hij hik hjk horth hgi0 (p := 1) (q := uj) (r := uk)
    (Or.inl ⟨isUnit_one, huj, huk⟩) (by simp) hj hk
  exact theorem18OnlyIf_of_eq_top hQ
    (rootGroup_eq_top_of_units_of_basis_pair h2 γ hγ hunits hcoli hlorth m hodd)

end QuadFormsKB.ConwaySloane
