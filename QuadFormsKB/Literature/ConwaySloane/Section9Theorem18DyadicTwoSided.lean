/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$, peeling from both ends

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 and the remark after it, at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicPeelPair.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ = `locGram Q v γ` of $B$ ($G_{kk} = 2Q(b_k)$), the relative statement
`FixTheta Q L v γ T` (rotations fixing the peeled vectors $b_t$, $t \in T$, have the spinor norm of Theorem 18).
Indices are $0$-based.

**The idea.** A peeling step (`fixTheta_peel`, `fixTheta_peel_pair`) removes an orthogonal basis vector $b_k$ of
*largest* norm order from the bottom of the remainder. The dual lattice $L_2^\#$ has the same automorphisms and the
same root vectors (`locStabV_eq_of_isDualLoc`, `isRootVector_congr`), and if $\gamma N$ is the dual basis
($GN = 1$, `dualGam`), its Gram matrix is $N = G^{-1}$. When the peeled vectors $b_t$ ($t \in T$) are orthogonal to
all others, the dual basis vectors are $b_t^\# = G_{tt}^{-1}b_t$ (`basisVec_dualGam_of_orth`), so a rotation fixes the
$b_t$ if and only if it fixes the $b_t^\#$, and `FixTheta` for $(L, \gamma, T)$ and for $(L', \gamma N, T)$ are
equivalent (`fixTheta_iff_dual`). A peeling step in $N$ removes a vector from the bottom of the dual remainder, i.e.
from the **top** of the remainder of $L_2$. Alternating the two kinds of steps peels a lattice from both ends.

**Defines**
* `PeelStep G T k o` (a **condition** on a matrix $G$, a set $T$ and an index $k$, with an optional partner $j$):
  the hypotheses of a peeling step (`PeelChainPair`'s steps);
* `TwoSidedChain Q v γ N hN T ks` (a **condition**): a list of peeling steps, each in $G$ (bottom) or in $N = G^{-1}$
  (top), ending in a `PeelChainPair` of $\gamma$ or of the dual basis.

**Proves**
* `fixTheta_of_rootGroup_eq_top`: if the root group is everything, `FixTheta` holds for every $T$;
* `col_orth_of_mul_eq_one`, `basisVec_dualGam_of_orth`, `fixTheta_transfer`, `fixTheta_iff_dual`;
* `fixTheta_of_twoSidedChain`, **`theorem18OnlyIf_of_twoSidedChain`** (Theorem 18, "only if", at $p = 2$ for
  two-sided peeling chains, unconditional);
* the valuation lemmas `valued_le_two_mul_of_lt` ($\lvert a\rvert < \lvert b\rvert \Rightarrow
  \lvert a\rvert \le \lvert 2b\rvert$), `valued_one_add_unit_le` ($\lvert 1 + u\rvert \le \lvert 2\rvert$ for a unit
  $u$), `valued_add_le_two_mul` ($\lvert x + y\rvert \le \lvert 2x\rvert$ when $\lvert x\rvert = \lvert y\rvert$).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual10

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Valuations

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **Discreteness**: $\lvert a\rvert < \lvert b\rvert$ implies $\lvert a\rvert \le \lvert 2b\rvert$ (the value
group of $\mathbb Q_2$ is $e^{\mathbb Z}$ and $\lvert 2\rvert = e^{-1}$). -/
theorem valued_le_two_mul_of_lt (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {a b : Fv} (h : Valued.v a < Valued.v b) :
    Valued.v a ≤ Valued.v (2 * b) := by
  by_cases ha : a = 0
  · rw [ha, map_zero]; exact zero_le
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact (not_lt_zero h).elim
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hvb : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  rw [← exp_log hva, ← exp_log hvb, exp_lt_exp] at h
  rw [map_mul, valued_two_dyadic v h2, ← exp_log hva, ← exp_log hvb, ← exp_add, exp_le_exp]
  omega

/-- **$\lvert 1 + u\rvert \le \lvert 2\rvert$ for a unit $u$** (the residue field of $\mathbb Z_2$ is
$\mathbb F_2$). -/
theorem valued_one_add_unit_le (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (1 + u) ≤ Valued.v (2 : Fv) := by
  have hu' : IsUnit (toO v u hu.le) :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hu
  obtain ⟨a, ha, hod⟩ := Rl.unit_exists h2 hu'
  have h1 : Rl (((1 : ℕ) : 𝔬) + toO v u hu.le) (((1 : ℕ) : ZMod 8) + a) := Rl.add (Rl.natCast 1) ha
  have hev : ∀ a : ZMod 8, Od a → ∃ k : ZMod 8, ((1 : ℕ) : ZMod 8) + a = 2 * k := by decide
  obtain ⟨k, hk⟩ := hev a hod
  obtain ⟨y, hy⟩ := h1.even k hk
  have e : (1 + u : Fv) = 2 * (y : Fv) := by
    have := congrArg (fun z : 𝔬 => (z : Fv)) hy
    simp only [toO] at this
    push_cast at this
    exact_mod_cast this
  rw [e, map_mul]
  exact mul_le_of_le_one_right' (vle_one y)

/-- **$\lvert x + y\rvert \le \lvert 2x\rvert$ when $\lvert x\rvert = \lvert y\rvert$.** -/
theorem valued_add_le_two_mul (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x y : Fv} (hx : x ≠ 0)
    (h : Valued.v x = Valued.v y) : Valued.v (x + y) ≤ Valued.v (2 * x) := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hu : Valued.v (y / x) = 1 := by rw [map_div₀, ← h, div_self hvx]
  have e : x + y = x * (1 + y / x) := by field_simp
  rw [e, map_mul, map_mul, mul_comm (Valued.v (2 : Fv))]
  exact mul_le_mul' le_rfl (valued_one_add_unit_le h2 hu)

end Valuations

section TwoSided

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **`FixTheta` when the root group is everything**: every $\sigma \in O(V)$ is a product of reflections
$\tau_{y_1}\cdots\tau_{y_r}$ (Cartan–Dieudonné, `exists_symmProd_eq`); if $r$ is even, the class
$Q(y_1)\cdots Q(y_r)$ is a product of an even number of root norms; if $r$ is odd, the class times $Q(x_0)$ is, for
one root vector $x_0$. -/
theorem fixTheta_of_rootGroup_eq_top (hQ : Q.Nondegenerate) (h : rootGroup Q L v = ⊤) {x₀ : Fin n → Fv}
    (hx₀ : IsRootVector Q L v x₀) (γ : GL (Fin n) Fv) (T : Finset (Fin n)) : FixTheta Q L v γ T := by
  intro σ _ _
  obtain ⟨ys, hys, rfl⟩ := exists_symmProd_eq Q Fv hQ σ
  have hdet : ((symmProd Q Fv ys : orthGroup Q Fv) : GL (Fin n) Fv).val.det = (-1) ^ ys.length :=
    det_symmProd_pow ys hys
  have hθ := spinorNorm_symmProd Q Fv hQ ys hys
  have hx0 : Q.evalIn Fv x₀ ≠ 0 := hx₀.1
  rcases Nat.even_or_odd ys.length with he | ho
  · have hmem : sqClassOf (valProd Q Fv ys) ∈ rootGroup Q L v := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨xs, hxe, hxr, hxc⟩ := hmem
    refine ⟨xs, hxr, ?_, hθ.trans hxc⟩
    rw [hdet, he.neg_one_pow, hxe.neg_one_pow]
  · have hmem : sqClassOf (valProd Q Fv ys) * sqClassOf (Q.evalIn Fv x₀) ∈ rootGroup Q L v := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨xs, hxe, hxr, hxc⟩ := hmem
    have hxs0 : ∀ x ∈ xs, Q.evalIn Fv x ≠ 0 := fun x hx => (hxr x hx).1
    refine ⟨x₀ :: xs, fun x hx => ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      exacts [hx₀, hxr x hx]
    · rw [hdet, ho.neg_one_pow, List.length_cons, (hxe.add_one).neg_one_pow]
    · have e : valProd Q Fv (x₀ :: xs) = Q.evalIn Fv x₀ * valProd Q Fv xs := by simp [valProd]
      rw [hθ, e, sqClassOf_mul hx0 (valProd_ne_zero Q Fv hxs0), ← hxc, mul_comm, mul_assoc,
        SqClass.mul_self, mul_one]

/-- **Columns orthogonal in $A$ are orthogonal in $A^{-1}$**: if $BA = 1$ and the $k$-th column of $A$ vanishes off
the diagonal, so does the $k$-th column of $B$, and $B_{kk}A_{kk} = 1$. -/
theorem col_orth_of_mul_eq_one {A B : Matrix (Fin n) (Fin n) Fv} (h : B * A = 1) {k : Fin n}
    (hk : ∀ m, m ≠ k → A m k = 0) : (∀ m, m ≠ k → B m k = 0) ∧ B k k * A k k = 1 := by
  have key : ∀ m, B m k * A k k = (1 : Matrix (Fin n) (Fin n) Fv) m k := by
    intro m
    rw [← h, Matrix.mul_apply, Finset.sum_eq_single k]
    · intro l _ hl; rw [hk l hl, mul_zero]
    · simp
  refine ⟨fun m hm => ?_, by simpa using key k⟩
  have hA : A k k ≠ 0 := fun h0 => by have := key k; rw [h0, mul_zero] at this; simp at this
  have := key m
  rw [Matrix.one_apply_ne hm] at this
  exact (mul_eq_zero.mp this).resolve_right hA

/-- **The dual basis vector of an orthogonal basis vector**: if $GN = 1$ and $b_t$ is orthogonal to the other basis
vectors, then $b_t^\# = \gamma N e_t = N_{tt}b_t$, $N_{tt} = G_{tt}^{-1} \ne 0$, and the $t$-th column of $N$
vanishes off the diagonal. -/
theorem basisVec_dualGam_of_orth (γ : GL (Fin n) Fv) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {t : Fin n} (ht : ∀ m, m ≠ t → locGram Q v γ m t = 0) :
    basisVec (dualGam Q v γ N hN) t = N t t • basisVec γ t ∧ N t t ≠ 0 ∧ ∀ m, m ≠ t → N m t = 0 := by
  have hNG : N * locGram Q v γ = 1 := mul_eq_one_comm.mp hN
  obtain ⟨hcol, hdiag⟩ := col_orth_of_mul_eq_one hNG ht
  have hNt : N t t ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdiag; exact zero_ne_one hdiag
  refine ⟨?_, hNt, hcol⟩
  have hv : N *ᵥ Pi.single t 1 = N t t • Pi.single t 1 := by
    ext m
    rw [Matrix.mulVec_single_one]
    by_cases hm : m = t
    · subst hm; simp
    · simp [hcol m hm, hm]
  simp only [basisVec, dualGam_val, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- **Transfer of `FixTheta` between lattices with the same automorphisms**, when the fixed vectors are
proportional. -/
theorem fixTheta_transfer {L' : Lat ℚ n} (hstab : locStabV Q v L = locStabV Q v L') {γ γ' : GL (Fin n) Fv}
    {T : Finset (Fin n)} (hb : ∀ t ∈ T, ∃ c : Fv, basisVec γ' t = c • basisVec γ t)
    (h : FixTheta Q L' v γ' T) : FixTheta Q L v γ T := by
  intro σ hσ hfix
  have hσ' : σ ∈ locStabV Q v L' := hstab ▸ hσ
  have hfix' : ∀ t ∈ T, (σ : GL (Fin n) Fv).val *ᵥ basisVec γ' t = basisVec γ' t := by
    intro t ht
    obtain ⟨c, hc⟩ := hb t ht
    rw [hc, Matrix.mulVec_smul, hfix t ht]
  obtain ⟨xs, hxs, hdet, hθ⟩ := h σ hσ' hfix'
  exact ⟨xs, fun x hx => (isRootVector_congr hstab x).mpr (hxs x hx), hdet, hθ⟩

/-- **`FixTheta` for $L$ and for its dual** (with the dual basis $\gamma N$), when the $b_t$ ($t \in T$) are
orthogonal to the other basis vectors. -/
theorem fixTheta_iff_dual {L' : Lat ℚ n} (h₁ : IsDualLoc Q (loc v L.1) (loc v L'.1))
    (h₂ : IsDualLoc Q (loc v L'.1) (loc v L.1)) (γ : GL (Fin n) Fv) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {T : Finset (Fin n)} (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) :
    FixTheta Q L v γ T ↔ FixTheta Q L' v (dualGam Q v γ N hN) T := by
  have hstab := locStabV_eq_of_isDualLoc h₁ h₂
  constructor
  · refine fixTheta_transfer hstab.symm fun t ht => ?_
    obtain ⟨he, hNt, -⟩ := basisVec_dualGam_of_orth γ N hN (hT t ht)
    exact ⟨(N t t)⁻¹, by rw [he, smul_smul, inv_mul_cancel₀ hNt, one_smul]⟩
  · refine fixTheta_transfer hstab fun t ht => ?_
    exact ⟨N t t, (basisVec_dualGam_of_orth γ N hN (hT t ht)).1⟩

variable (v) in
/-- **One peeling step in a matrix $G$** (a **condition**): with no partner, $k \notin T$, $G_{mk} = 0$ for
$m \ne k$, and $\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{k\}$ (the step of
`PeelChainTheta`); with a partner $j$, the step of `PeelChainPair` ($k, j \notin T$, $j \ne k$, $b_k$ and $b_j$
orthogonal to the other basis vectors, $\lvert G_{jj}\rvert = \lvert G_{kk}\rvert$, and
$\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ for $i, i' \notin T \cup \{j, k\}$). -/
def PeelStep (G : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) (T : Finset (Fin n)) (k : Fin n) :
    Option (Fin n) → Prop
  | none => k ∉ T ∧ (∀ m, m ≠ k → G m k = 0) ∧
      (∀ i i', i ∉ insert k T → i' ∉ insert k T → Valued.v (G i i') ≤ Valued.v (2 * G k k))
  | some j => k ∉ T ∧ j ∉ T ∧ j ≠ k ∧ (∀ m, m ≠ k → G m k = 0) ∧ (∀ m, m ≠ j → G m j = 0) ∧
      Valued.v (G j j) = Valued.v (G k k) ∧
      (∀ i i', i ∉ insert k (insert j T) → i' ∉ insert k (insert j T) →
        Valued.v (G i i') ≤ Valued.v (2 * G k k))

theorem PeelStep.orth {G : Matrix (Fin n) (Fin n) Fv} {T : Finset (Fin n)} {k : Fin n} {o : Option (Fin n)}
    (h : PeelStep v G T k o) : ∀ m, m ≠ k → G m k = 0 := by
  cases o with
  | none => exact h.2.1
  | some j => exact h.2.2.2.1

/-- `FixTheta` through one peeling step. -/
theorem fixTheta_of_peelStep (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)} (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0)
    {k : Fin n} {o : Option (Fin n)} (hs : PeelStep v (locGram Q v γ) T k o)
    (hgen : FixTheta Q L v γ (insert k T)) : FixTheta Q L v γ T := by
  cases o with
  | none =>
    obtain ⟨hkT, hk, hd⟩ := hs
    exact fixTheta_peel hQ h2 γ hγ T k hkT hT hk hd hgen
  | some j =>
    obtain ⟨hkT, hjT, hjk, hk, hj, hjj, hd⟩ := hs
    exact fixTheta_peel_pair hQ h2 γ hγ T k j hkT hjT hjk hT hk hj hjj hd hgen

variable (Q v) in
/-- **Two-sided peeling chains** (a **condition** on a basis $\gamma$ of $L_2$ and the Gram matrix $N$ of the dual
basis, $GN = 1$): given the set $T$ of indices already peeled and a list of steps $(k, j?, s)$,
* if the list is empty, $\gamma$ or the dual basis $\gamma N$ has a peeling chain with partners starting at $T$
  (`PeelChainPair`);
* a step with $s = $ `false` is a peeling step in $G$ = `locGram Q v γ` (from the bottom of the remainder), a step
  with $s = $ `true` is a peeling step in $N$ (from the bottom of the dual remainder, i.e. from the top of the
  remainder), see `PeelStep`;
and after a step the chain continues with $T \cup \{k\}$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (remark after Thm. 18: peeling chains from both ends, through the dual lattice, p = 2)"]
def TwoSidedChain (γ : GL (Fin n) (v.adicCompletion ℚ)) (N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ))
    (hN : locGram Q v γ * N = 1) : Finset (Fin n) → List (Fin n × Option (Fin n) × Bool) → Prop
  | T, [] => (∃ ks, PeelChainPair Q v γ T ks) ∨ (∃ ks, PeelChainPair Q v (dualGam Q v γ N hN) T ks)
  | T, (k, o, false) :: ks => PeelStep v (locGram Q v γ) T k o ∧ TwoSidedChain γ N hN (insert k T) ks
  | T, (k, o, true) :: ks => PeelStep v N T k o ∧ TwoSidedChain γ N hN (insert k T) ks

/-- **`FixTheta` along a two-sided peeling chain.** -/
theorem fixTheta_of_twoSidedChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv) (hN : locGram Q v γ * N = 1)
    {L' : Lat ℚ n} (hL' : loc v L'.1 = locAct v (dualGam Q v γ N hN) (std v))
    (h₁ : IsDualLoc Q (loc v L.1) (loc v L'.1)) (h₂ : IsDualLoc Q (loc v L'.1) (loc v L.1)) :
    ∀ (ks : List (Fin n × Option (Fin n) × Bool)) (T : Finset (Fin n)),
      (∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) → TwoSidedChain Q v γ N hN T ks → FixTheta Q L v γ T
  | [], T, hT, hc => by
    rcases hc with ⟨ks, hks⟩ | ⟨ks, hks⟩
    · exact fixTheta_of_peelChainPair hQ h2 γ hγ ks T hT hks
    · refine (fixTheta_iff_dual h₁ h₂ γ N hN hT).mpr ?_
      refine fixTheta_of_peelChainPair hQ h2 _ hL' ks T (fun t ht m hm => ?_) hks
      rw [locGram_dualGam]
      exact (basisVec_dualGam_of_orth γ N hN (hT t ht)).2.2 m hm
  | (k, o, false) :: ks, T, hT, ⟨hs, hrest⟩ => by
    have hT' : ∀ t ∈ insert k T, ∀ m, m ≠ t → locGram Q v γ m t = 0 := by
      intro t ht m hm
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hs.orth m hm
      · exact hT t ht m hm
    exact fixTheta_of_peelStep hQ h2 γ hγ hT hs (fixTheta_of_twoSidedChain hQ h2 γ hγ N hN hL' h₁ h₂ ks _ hT' hrest)
  | (k, o, true) :: ks, T, hT, ⟨hs, hrest⟩ => by
    have hk : ∀ m, m ≠ k → locGram Q v γ m k = 0 :=
      (col_orth_of_mul_eq_one hN hs.orth).1
    have hT' : ∀ t ∈ insert k T, ∀ m, m ≠ t → locGram Q v γ m t = 0 := by
      intro t ht m hm
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hk m hm
      · exact hT t ht m hm
    have hnext := fixTheta_of_twoSidedChain hQ h2 γ hγ N hN hL' h₁ h₂ ks _ hT' hrest
    rw [fixTheta_iff_dual h₁ h₂ γ N hN hT'] at hnext
    refine (fixTheta_iff_dual h₁ h₂ γ N hN hT).mpr ?_
    have hTd : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v (dualGam Q v γ N hN) m t = 0 := by
      intro t ht m hm
      rw [locGram_dualGam]
      exact (basisVec_dualGam_of_orth γ N hN (hT t ht)).2.2 m hm
    have hs' : PeelStep v (locGram Q v (dualGam Q v γ N hN)) T k o := by rw [locGram_dualGam]; exact hs
    exact fixTheta_of_peelStep hQ h2 _ hL' hTd hs' hnext

/-- **Theorem 18, "only if", for a two-sided peeling chain** (Conway–Sloane §9.5, p. 391; $p = 2$; unconditional):
if $L_2$ has a basis $b = \gamma e$, $GN = 1$, and a list of steps with `TwoSidedChain Q v γ N hN ∅ ks`, every
element of $\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root
vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': two-sided peeling chains)"]
theorem theorem18OnlyIf_of_twoSidedChain (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) (ks : List (Fin n × Option (Fin n) × Bool))
    (hc : TwoSidedChain Q v γ N hN ∅ ks) : Theorem18OnlyIf Q L v hQ := by
  obtain ⟨L', hL', h₁, h₂⟩ := exists_dual_lat γ hγ N hN
  intro A hA
  obtain ⟨σ, ⟨hσL, hσS⟩, hσB⟩ := (mem_localSpinorNormGroup Q hQ v L).mp hA
  obtain ⟨xs, hxs, hdet, hθ⟩ :=
    fixTheta_of_twoSidedChain hQ h2 γ hγ N hN hL' h₁ h₂ ks ∅ (by simp) hc σ hσL (by simp)
  have h1 : ((σ : GL (Fin n) Fv).val).det = 1 := hσS
  refine ⟨xs, ?_, hxs, hσB.symm.trans hθ⟩
  rw [h1] at hdet
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : Fv) ≠ 1)).mp hdet.symm

end TwoSided

end QuadFormsKB.ConwaySloane
