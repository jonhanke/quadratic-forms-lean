/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for the shapes $\langle a, b\rangle \perp 16\langle c, d\rangle$
and $\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** Over $\mathbb Q$ at the prime $v$ over $2$; a basis $\gamma$ of $L_2$ with Gram matrix $G$ =
`locGram Q v γ` of the bilinear form $B$ ($G_{kk} = 2Q(b_k)$). Indices are $0$-based.

**The shapes.** In Conway–Sloane's notation (form matrix $M$, $Q(x) = x^{\mathsf T}Mx$, $G = 2M$), for arbitrary
$2$-adic units (no congruence conditions):
* *Shape B*: $\langle a, b\rangle \perp 16\langle c, d\rangle$, with $G = \operatorname{diag}(2a, 2b, 32c, 32d)$
  (`shapeBG`);
* *Shape C*: $\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$, with
  $G = \operatorname{diag}(2a, 2b, 8c, 32d, 32e)$ (`shapeCG`).

**The chains** (`PeelChainPair`, from `Section9Theorem18DyadicPeelPair.lean`):
* Shape B: `[(0, some 1), (1, none)]`. Peel $b_0$ with partner $b_1$ ($\lvert G_{11}\rvert = \lvert G_{00}\rvert =
  \lvert 2\rvert$; the entries $32c, 32d, 0$ on $\{2, 3\}$ are $\le \lvert 2G_{00}\rvert = \lvert 4\rvert$), then peel
  $b_1$ alone (same bound); the complement $\{2, 3\}$ has at most $2$ elements.
* Shape C: `[(0, some 1), (1, none), (2, none)]`. The first two steps are as above (the entries $8c, 32d, 32e$ on
  $\{2, 3, 4\}$ are $\le \lvert 4\rvert$); then peel $b_2$ ($\lvert 32\rvert \le \lvert 2G_{22}\rvert = \lvert 16\rvert$
  on $\{3, 4\}$); the complement $\{3, 4\}$ has at most $2$ elements.

**Why pair peeling.** The root group of shape B is not the group of unit classes in general: e.g.
$\langle 1, 1\rangle \perp 16\langle 1, 1\rangle$ has root group $\{1, 5, 2, 10\}$ modulo squares, so the
even-order method (which needs the roots to be the unit classes) cannot handle it, whereas peeling with orthogonal
partners does.

**Proves** `peelChainPair_shapeB`, `theorem18OnlyIf_of_shapeB`, `covered10_of_shapeB`, and the same three for shape C
(unconditional).
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual10
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicShapeA

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The Gram matrix $G = \operatorname{diag}(2a,\ 2b,\ 32c,\ 32d)$ of the bilinear form $B$ in a Jordan basis of the
$2$-adic lattice $\langle a, b\rangle \perp 16\langle c, d\rangle$ (Conway–Sloane's notation, $G = 2M$). -/
def shapeBG {K : Type*} [Field K] (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![2 * a, 0, 0, 0; 0, 2 * b, 0, 0; 0, 0, 32 * c, 0; 0, 0, 0, 32 * d]

/-- The Gram matrix $G = \operatorname{diag}(2a,\ 2b,\ 8c,\ 32d,\ 32e)$ of the bilinear form $B$ in a Jordan basis
of the $2$-adic lattice $\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$. -/
def shapeCG {K : Type*} [Field K] (a b c d e : K) : Matrix (Fin 5) (Fin 5) K :=
  !![2 * a, 0, 0, 0, 0; 0, 2 * b, 0, 0, 0; 0, 0, 8 * c, 0, 0; 0, 0, 0, 32 * d, 0; 0, 0, 0, 0, 32 * e]

/-- Evaluate the entries of an explicit `!![...]` matrix at numerals. -/
local macro "shapeBC_ent" : tactic =>
  `(tactic| simp only [Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk])

section Aux

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- $\lvert 2\cdot(2u)\rvert = e^{-2}$ for a unit $u$. -/
theorem shapeBC_v_two_two (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (2 * (2 * u)) = exp (-2 : ℤ) := by
  rw [show (2 : Fv) * (2 * u) = 4 * u by ring]; exact shapeA_v_four_mul h2 hu

/-- $\lvert 2\cdot(8u)\rvert = e^{-4}$ for a unit $u$. -/
theorem shapeBC_v_two_eight (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : Fv} (hu : Valued.v u = 1) :
    Valued.v (2 * (8 * u)) = exp (-4 : ℤ) := by
  have := shapeA_valued_two_pow_mul h2 4 hu
  rw [show (2 : Fv) ^ 4 = 16 by norm_num] at this
  rw [show (2 : Fv) * (8 * u) = 16 * u by ring, this]; simp

end Aux

section Main

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

/-- **Shape B chain**: if $G = \operatorname{diag}(2a, 2b, 32c, 32d)$ with $a, b, c, d$ units, then
`PeelChainPair Q v γ ∅ [(0, some 1), (1, none)]`. -/
theorem peelChainPair_shapeB (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 4} (γ : GL (Fin 4) Fv)
    {a b c d : Fv} (hG : locGram Q v γ = shapeBG a b c d) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) :
    PeelChainPair Q v γ ∅ [(0, some 1), (1, none)] := by
  have va := shapeA_v_two_mul h2 ha
  have vb := shapeA_v_two_mul h2 hb
  have vc := shapeA_v_thirtytwo_mul h2 hc
  have vd := shapeA_v_thirtytwo_mul h2 hd
  have ra := shapeBC_v_two_two h2 ha
  have rb := shapeBC_v_two_two h2 hb
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeBG]; shapeBC_ent)
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeBG]; shapeBC_ent)
  · rw [hG]; simp only [shapeBG]; shapeBC_ent; rw [va, vb]
  · intro i i' hi hi'; rw [hG]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hi' (by decide)
        | (simp only [shapeBG]; shapeBC_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeBG]; shapeBC_ent; rw [vc, ra, exp_le_exp]; norm_num)
        | (simp only [shapeBG]; shapeBC_ent; rw [vd, ra, exp_le_exp]; norm_num)
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeBG]; shapeBC_ent)
  · intro i i' hi hi'; rw [hG]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hi' (by decide)
        | (simp only [shapeBG]; shapeBC_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeBG]; shapeBC_ent; rw [vc, rb, exp_le_exp]; norm_num)
        | (simp only [shapeBG]; shapeBC_ent; rw [vd, rb, exp_le_exp]; norm_num)
  · left; decide

/-- **Theorem 18, "only if", at $p = 2$ for $\langle a, b\rangle \perp 16\langle c, d\rangle$** (Conway–Sloane §9.5,
p. 391; unconditional): if $L_2$ has a basis $\gamma$ with Gram matrix $\operatorname{diag}(2a, 2b, 32c, 32d)$, with
$a, b, c, d$ arbitrary $2$-adic units, then every element of $\theta(O^+(L_2))$ is, up to squares, the product of the
norms of an even number of $2$-adic root vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': ⟨a, b⟩ ⊥ 16⟨c, d⟩)"]
theorem theorem18OnlyIf_of_shapeB {L : Lat ℚ 4} {Q : QuadForm ℚ 4} (hQ : Q.Nondegenerate)
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a b c d : Fv}
    (hG : locGram Q v γ = shapeBG a b c d) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) : Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_peelChainPair hQ h2 γ hγ _ (peelChainPair_shapeB h2 γ hG ha hb hc hd)

/-- **The shape $\langle a, b\rangle \perp 16\langle c, d\rangle$ is covered**, tenth version (a peeling chain with
an orthogonal partner). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: ⟨a, b⟩ ⊥ 16⟨c, d⟩ is a covered shape, tenth version)"]
theorem covered10_of_shapeB (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {L : Lat ℚ 4} {Q : QuadForm ℚ 4}
    (γ : GL (Fin 4) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a b c d : Fv}
    (hG : locGram Q v γ = shapeBG a b c d) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) : Theorem18DyadicCovered10 Q L v :=
  Or.inr (Or.inl ⟨γ, _, hγ, peelChainPair_shapeB h2 γ hG ha hb hc hd⟩)

/-- **Shape C chain**: if $G = \operatorname{diag}(2a, 2b, 8c, 32d, 32e)$ with $a, b, c, d, e$ units, then
`PeelChainPair Q v γ ∅ [(0, some 1), (1, none), (2, none)]`. -/
theorem peelChainPair_shapeC (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {Q : QuadForm ℚ 5} (γ : GL (Fin 5) Fv)
    {a b c d e : Fv} (hG : locGram Q v γ = shapeCG a b c d e) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) (he : Valued.v e = 1) :
    PeelChainPair Q v γ ∅ [(0, some 1), (1, none), (2, none)] := by
  have va := shapeA_v_two_mul h2 ha
  have vb := shapeA_v_two_mul h2 hb
  have vc := shapeA_v_eight_mul h2 hc
  have vd := shapeA_v_thirtytwo_mul h2 hd
  have ve := shapeA_v_thirtytwo_mul h2 he
  have ra := shapeBC_v_two_two h2 ha
  have rb := shapeBC_v_two_two h2 hb
  have rc := shapeBC_v_two_eight h2 hc
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, by decide, ?_, ?_, by decide, ?_, ?_, ?_⟩
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeCG]; shapeBC_ent)
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeCG]; shapeBC_ent)
  · rw [hG]; simp only [shapeCG]; shapeBC_ent; rw [va, vb]
  · intro i i' hi hi'; rw [hG]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hi' (by decide)
        | (simp only [shapeCG]; shapeBC_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeCG]; shapeBC_ent; rw [vc, ra, exp_le_exp]; norm_num)
        | (simp only [shapeCG]; shapeBC_ent; rw [vd, ra, exp_le_exp]; norm_num)
        | (simp only [shapeCG]; shapeBC_ent; rw [ve, ra, exp_le_exp]; norm_num)
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeCG]; shapeBC_ent)
  · intro i i' hi hi'; rw [hG]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hi' (by decide)
        | (simp only [shapeCG]; shapeBC_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeCG]; shapeBC_ent; rw [vc, rb, exp_le_exp]; norm_num)
        | (simp only [shapeCG]; shapeBC_ent; rw [vd, rb, exp_le_exp]; norm_num)
        | (simp only [shapeCG]; shapeBC_ent; rw [ve, rb, exp_le_exp]; norm_num)
  · intro m hm; rw [hG]
    fin_cases m <;> first | exact absurd rfl hm | (simp only [shapeCG]; shapeBC_ent)
  · intro i i' hi hi'; rw [hG]
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd hi (by decide)
        | exact absurd hi' (by decide)
        | (simp only [shapeCG]; shapeBC_ent; rw [map_zero]; exact zero_le)
        | (simp only [shapeCG]; shapeBC_ent; rw [vd, rc, exp_le_exp]; norm_num)
        | (simp only [shapeCG]; shapeBC_ent; rw [ve, rc, exp_le_exp]; norm_num)
  · left; decide

/-- **Theorem 18, "only if", at $p = 2$ for $\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$**
(Conway–Sloane §9.5, p. 391; unconditional): if $L_2$ has a basis $\gamma$ with Gram matrix
$\operatorname{diag}(2a, 2b, 8c, 32d, 32e)$, with $a, b, c, d, e$ arbitrary $2$-adic units, then every element of
$\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': ⟨a, b⟩ ⊥ 4⟨c⟩ ⊥ 16⟨d, e⟩)"]
theorem theorem18OnlyIf_of_shapeC {L : Lat ℚ 5} {Q : QuadForm ℚ 5} (hQ : Q.Nondegenerate)
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin 5) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a b c d e : Fv}
    (hG : locGram Q v γ = shapeCG a b c d e) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) (he : Valued.v e = 1) : Theorem18OnlyIf Q L v hQ :=
  theorem18OnlyIf_of_peelChainPair hQ h2 γ hγ _ (peelChainPair_shapeC h2 γ hG ha hb hc hd he)

/-- **The shape $\langle a, b\rangle \perp 4\langle c\rangle \perp 16\langle d, e\rangle$ is covered**, tenth
version (a peeling chain with an orthogonal partner). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: ⟨a, b⟩ ⊥ 4⟨c⟩ ⊥ 16⟨d, e⟩ is a covered shape, tenth version)"]
theorem covered10_of_shapeC (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {L : Lat ℚ 5} {Q : QuadForm ℚ 5}
    (γ : GL (Fin 5) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {a b c d e : Fv}
    (hG : locGram Q v γ = shapeCG a b c d e) (ha : Valued.v a = 1) (hb : Valued.v b = 1)
    (hc : Valued.v c = 1) (hd : Valued.v d = 1) (he : Valued.v e = 1) : Theorem18DyadicCovered10 Q L v :=
  Or.inr (Or.inl ⟨γ, _, hγ, peelChainPair_shapeC h2 γ hG ha hb hc hd he⟩)

end Main

end QuadFormsKB.ConwaySloane
