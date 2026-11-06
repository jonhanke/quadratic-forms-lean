/-
# Conway–Sloane, Ch. 15, §9.5: $2$-adic root vectors of non-unit norm

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, pp. 391–392
(`conwaysloane1999`).

**Layer.** As in Cassels' Lemma 3.8 (`Literature/Cassels/Ch11Sec3Dyadic.lean`): $V_2 = \mathbb Q_2^n$ with the
rational form $Q$, a lattice $L$ with $L_2 = \gamma\mathbb Z_2^n$, the Gram matrix $G = \gamma^tH\gamma$ of
$B(x, y) = Q(x+y) - Q(x) - Q(y)$ (`locGram`, so $G_{kk} = 2Q(b_k)$), and $\theta(O^+(L_2))$ =
`localSpinorNormGroup`.

A **$p$-adic root vector** (Conway–Sloane §9.5, p. 391) is a vector $x$ whose reflection
$\tau_x(y) = y - \frac{B(x, y)}{Q(x)}x$ is a $p$-adically integral automorphism; for $x = \gamma c$ this holds when
$\lvert (Gc)_m\rvert \le \lvert Q(x)\rvert$ for every $m$ (`Lattices.symm_mem_of_gram`). Cassels' Lemma 3.8 uses root
vectors of unit norm only; the rules (i), (ii) of Conway–Sloane's algorithm also use root vectors of norm $2^k$ times a
unit, for example $e_1 + e_2$ of norm $2$ for $I_2$ (p. 392).

**Proves**
* `ternary_adm_gen`: in the span of three orthogonal basis vectors with $G_{ii} = wp$, $G_{jj} = wq$, $G_{kk} = wr$,
  the vector $x = sb_i + tb_j + zb_k$ ($s, t, z \in \mathbb Z_2$) has $Q(x) = \frac w2 B(s,t,z)$,
  $B = ps^2 + qt^2 + rz^2$, and is a root vector as soon as $\lvert 2ps\rvert, \lvert 2qt\rvert, \lvert 2rz\rvert \le
  \lvert B\rvert$.
* `ternary_InT_gen`: the product of the norms of two such root vectors lies in $\theta(O^+(L_2))$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec3DyadicCor

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

section Spin

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q : QuadForm F n} {v : HeightOneSpectrum (𝓞 F)}
  (hQ : Q.Nondegenerate) (L : Lat F n)

local notation "Fw" => v.adicCompletion F
local notation "𝔬w" => v.adicCompletionIntegers F

/-- **Root vectors in the span of three orthogonal basis vectors** (generalizing `Lattices.ternary_adm` from unit
values of $B$ to all values with $\lvert 2ps\rvert, \lvert 2qt\rvert, \lvert 2rz\rvert \le \lvert B(s,t,z)\rvert$). -/
theorem ternary_adm_gen (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fw} (hw : w ≠ 0) {p q r : 𝔬w}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r)
    (s t z : 𝔬w) (hB0 : (Bf p q r s t z : 𝔬w) ≠ 0)
    (hps : Valued.v ((2 * p * s : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw))
    (hqt : Valued.v ((2 * q * t : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw))
    (hrz : Valued.v ((2 * r * z : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw)) :
    ∃ x, Q.evalIn Fw x = w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) ∧ symm Q Fw x ∈ locStabV Q v L := by
  set c : Fin n → Fw := Pi.single i (s : Fw) + Pi.single j (t : Fw) + Pi.single k (z : Fw) with hc
  have hci : c i = s := by simp [hc, hij, hik]
  have hcj : c j = t := by simp [hc, hij.symm, hjk]
  have hck : c k = z := by simp [hc, hik.symm, hjk.symm]
  have hcm : ∀ m, m ≠ i → m ≠ j → m ≠ k → c m = 0 := by
    intro m h1 h2 h3; simp [hc, h1, h2, h3]
  have hcstd : c ∈ std v :=
    (std v).add_mem ((std v).add_mem (single_mem_std i (vle_one s)) (single_mem_std j (vle_one t)))
      (single_mem_std k (vle_one z))
  have hdiag : ∀ m, (locGram Q v γ *ᵥ c) m = locGram Q v γ m m * c m := fun m =>
    gram_mulVec_diag_of γ fun l hl hcl => by
      have : l = i ∨ l = j ∨ l = k := by
        by_contra h
        push Not at h
        exact hcl (hcm l h.1 h.2.1 h.2.2)
      rw [locGram_symm']
      exact horth l m hl this
  have hdot : ∀ d : Fin n → Fw, c ⬝ᵥ d = s * d i + t * d j + z * d k := fun d => by
    rw [hc, add_dotProduct, add_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hQ2 : 2 * Q.evalIn Fw (γ.val *ᵥ c) = w * ((Bf p q r s t z : 𝔬w) : Fw) := by
    rw [two_mul_evalIn_locGram, hdot, hdiag i, hdiag j, hdiag k, hci, hcj, hck, hgi, hgj, hgk]
    simp only [Bf]
    push_cast
    ring
  have hQx : Q.evalIn Fw (γ.val *ᵥ c) = w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) := by
    rw [div_mul_eq_mul_div, eq_div_iff h2ne]
    linear_combination hQ2
  have hBne : ((Bf p q r s t z : 𝔬w) : Fw) ≠ 0 := fun h => hB0 (by exact_mod_cast h)
  have hx0 : Q.evalIn Fw (γ.val *ᵥ c) ≠ 0 := by
    rw [hQx]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne
  refine ⟨γ.val *ᵥ c, hQx, symm_mem_of_gram L γ hγ hcstd hx0 fun m => ?_⟩
  have h2pos : 0 < Valued.v (2 : Fw) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h2ne)
  -- `|w a c| ≤ |w/2 · B|` from `|2 a c| ≤ |B|`
  have key : ∀ (a y : 𝔬w), Valued.v ((2 * a * y : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw) →
      Valued.v (w * (a : Fw) * (y : Fw)) ≤ Valued.v (Q.evalIn Fw (γ.val *ᵥ c)) := by
    intro a y h
    rw [hQx]
    have e : ((2 * a * y : 𝔬w) : Fw) = 2 * (a : Fw) * (y : Fw) := by push_cast; rfl
    rw [e] at h
    have e1 : w * (a : Fw) * (y : Fw) * 2 = w * (2 * (a : Fw) * (y : Fw)) := by ring
    have e2 : w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) * 2 = w * ((Bf p q r s t z : 𝔬w) : Fw) := by
      field_simp
    refine le_of_mul_le_mul_right ?_ h2pos
    rw [← map_mul, ← map_mul, e1, e2, map_mul (Valued.v) w, map_mul (Valued.v) w]
    exact mul_le_mul' le_rfl h
  rw [hdiag m]
  by_cases hmi : m = i
  · subst hmi; rw [hci, hgi]; exact key p s hps
  by_cases hmj : m = j
  · subst hmj; rw [hcj, hgj]; exact key q t hqt
  by_cases hmk : m = k
  · subst hmk; rw [hck, hgk]; exact key r z hrz
  rw [hcm m hmi hmj hmk, mul_zero, map_zero]
  exact zero_le

/-- A pair $(s, t, z)$ giving a root vector: $B(s,t,z) \ne 0$ and $\lvert 2ps\rvert, \lvert 2qt\rvert,
\lvert 2rz\rvert \le \lvert B(s,t,z)\rvert$. -/
def Adm (p q r s t z : 𝔬w) : Prop :=
  (Bf p q r s t z : 𝔬w) ≠ 0 ∧
    Valued.v ((2 * p * s : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw) ∧
    Valued.v ((2 * q * t : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw) ∧
    Valued.v ((2 * r * z : 𝔬w) : Fw) ≤ Valued.v ((Bf p q r s t z : 𝔬w) : Fw)

/-- **The product of the norms of two root vectors** $sb_i + tb_j + zb_k$, $s'b_i + t'b_j + z'b_k$ lies in
$\theta(O^+(L_2))$ (up to the square $(w/2)^2$): $B(s,t,z)B(s',t',z') \in \theta(O^+(L_2))$. -/
theorem ternary_InT_gen (γ : GL (Fin n) Fw) (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (horth : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → locGram Q v γ l m = 0)
    {w : Fw} (hw : w ≠ 0) {p q r : 𝔬w}
    (hgi : locGram Q v γ i i = w * p) (hgj : locGram Q v γ j j = w * q) (hgk : locGram Q v γ k k = w * r)
    {s t z s' t' z' : 𝔬w} (hB : Adm p q r s t z) (hB' : Adm p q r s' t' z') :
    InT hQ L (((Bf p q r s t z * Bf p q r s' t' z' : 𝔬w)) : Fw) := by
  obtain ⟨x, hx, hxs⟩ := ternary_adm_gen L γ hγ hij hik hjk horth hw hgi hgj hgk s t z hB.1 hB.2.1 hB.2.2.1
    hB.2.2.2
  obtain ⟨y, hy, hys⟩ := ternary_adm_gen L γ hγ hij hik hjk horth hw hgi hgj hgk s' t' z' hB'.1 hB'.2.1
    hB'.2.2.1 hB'.2.2.2
  have h2ne : (2 : Fw) ≠ 0 := two_ne_zero
  have hBne : ((Bf p q r s t z : 𝔬w) : Fw) ≠ 0 := fun h => hB.1 (by exact_mod_cast h)
  have hBne' : ((Bf p q r s' t' z' : 𝔬w) : Fw) ≠ 0 := fun h => hB'.1 (by exact_mod_cast h)
  have hx0 : Q.evalIn Fw x ≠ 0 := by rw [hx]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne
  have hy0 : Q.evalIn Fw y ≠ 0 := by rw [hy]; exact mul_ne_zero (div_ne_zero hw h2ne) hBne'
  have := InT.of_symm_pair hQ L hx0 hy0 hxs hys
  rw [hx, hy] at this
  have e : w / 2 * ((Bf p q r s t z : 𝔬w) : Fw) * (w / 2 * ((Bf p q r s' t' z' : 𝔬w) : Fw)) =
      ((Bf p q r s t z * Bf p q r s' t' z' : 𝔬w) : Fw) * (w / 2) ^ 2 := by push_cast; ring
  rw [e] at this
  exact (InT.sq_mul_iff hQ L (div_ne_zero hw h2ne)).mp this

end Spin

end QuadFormsKB.ConwaySloane
