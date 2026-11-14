/-
# Elements of $\mathbb{F}_q(t)$ with prescribed local Hilbert symbols

`RatFuncPlace.prescribedHilbert_of_inputs`: for a finite field $k$ of odd characteristic, the named input
`RatFuncPlace.PrescribedHilbert k` (O'Meara 71:19, Serre III §2.2 Thm. 4, for $F = k(t)$) follows from

* `HilbertReciprocity k` (O'Meara 71:18 for $k(t)$; proved as `RatFuncPlace.hilbertReciprocity`, so
  `prescribedHilbert_of_squarePrimes` needs only the second input), and
* the new named input `PrescribedSquarePrimes k`: primes of $k[t]$ with prescribed square classes (the function field case of
  `PresNF.exists_prime_sq_nonsq`, a Chebotarev-type statement for $k(t)(\sqrt{a_i}, \sqrt u)$).

**Route** (the number field proof of `Literature/LocalGlobal/PrescribedNF.lean`, with $k[t]$ for $\mathcal O_F$ and the single
infinite place $\infty$):

1. *Finite duality* (`PresNF.SignPairing`, reused): in $G_S = \prod_{v \in S} k(t)_v^\times / k(t)_v^{\times 2} \times
   k(t)_\infty^\times / k(t)_\infty^{\times 2}$ with the product of the local Hilbert pairings.
2. *The Lagrangian of $S$-units* (`card_lamS`): its image $\Lambda_S$ is isotropic (Hilbert reciprocity), and
   $|\Lambda_S|^2 = |G_S|$: each local square class group has at most $4$ elements (`card_sqCl_le`, from
   `FF.OddLocalAxioms`), and $\Lambda_S$ has at least $2^{|S| + 1}$ elements (the classes of $c_0^b \prod_{v \in T} \pi_v$,
   $T \subseteq S$, $b \in \{0, 1\}$, $c_0$ a nonsquare constant, $\pi_v$ a generator of $v$, are distinct).
3. *Factorization* (`exists_sUnit_mul_sq`): an element of $k(t)^\times$ with even valuation outside $S$ is an $S$-unit times a
   square (squarefree decomposition in $k[t]$); hence the kernel condition (`isSquare_of_locMap_eq_one`).
4. *Assembly* (`prescribedHilbert_of_inputs`), as in `PresNF.exists_prescribed_hilbert`.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.OddLocalClassification
import QuadFormsKB.FunctionField.RatFuncReciprocity
import QuadFormsKB.Literature.LocalGlobal.PrescribedNF

open IsDedekindDomain Polynomial WithZero QuadFormsKB.SqDual

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB

/-! ### Generic facts under the odd local axioms -/

namespace FF.OddLocalAxioms

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- Two units have Hilbert symbol $1$. -/
lemma hs_units (h : OddLocalAxioms K) {a b : K} (ha : Valued.v a = 1) (hb : Valued.v b = 1) :
    hilbertSymbol K a b = 1 := by
  by_cases hsq : IsSquare a
  · exact hs_of_isSquare hsq b
  obtain ⟨π, hπ⟩ := h.exists_uniformizer
  rw [h.unit_hs_iff hπ ha hsq (ne_zero_of_v one_ne_zero hb), L_of_v (n := 0) (by rw [hb]; rfl)]
  exact ⟨0, rfl⟩

/-- The Hilbert symbol on square classes is multiplicative. -/
lemma hilbCl_mul (h : OddLocalAxioms K) (x x' y : SqCl K) :
    hilbCl K (x * x') y = hilbCl K x y * hilbCl K x' y := by
  induction x using QuotientGroup.induction_on
  induction x' using QuotientGroup.induction_on
  induction y using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul, hilbCl_mk, hilbCl_mk, hilbCl_mk, Units.val_mul]
  exact h.hilbertSymbol_mul_left _ _ _ (Units.ne_zero _) (Units.ne_zero _) (Units.ne_zero _)

/-- The Hilbert pairing on square classes is nondegenerate. -/
@[kb "omeara1963" "§63B, 63:13, p. 166 (nondegeneracy, non-dyadic case)"]
lemma hilbCl_nondeg (h : OddLocalAxioms K) (y : SqCl K) (hy : y ≠ 1) : ∃ x, hilbCl K x y = -1 := by
  induction y using QuotientGroup.induction_on with
  | H c =>
  have hc : ¬ IsSquare (c : K) := fun hc => hy ((mk_eq_one_iff_isSquare _ c).mpr hc)
  obtain ⟨x, hx0, hx⟩ := h.exists_neg_one (c : K) c.ne_zero hc
  exact ⟨QuotientGroup.mk (Units.mk0 x hx0), by rw [hilbCl_mk, hilbertSymbol_comm]; exact hx⟩

/-- **At most four square classes:** every class is that of $u_0^{b_1} \pi^{b_2}$, $u_0$ a nonsquare unit and $\pi$ a
uniformizer. -/
@[kb "omeara1963" "§63A, 63:9 (square classes of a non-dyadic local field) [unverified]"]
lemma card_sqCl_le (h : OddLocalAxioms K) : Finite (SqCl K) ∧ Nat.card (SqCl K) ≤ 4 := by
  classical
  obtain ⟨π, hπ⟩ := h.exists_uniformizer
  obtain ⟨u₀, hu₀, hu₀s⟩ := h.exists_nonsquare_unit
  have hπ0 : π ≠ 0 := ne_zero_of_v exp_ne_zero hπ
  have hu0 : u₀ ≠ 0 := ne_zero_of_v one_ne_zero hu₀
  set U : Kˣ := Units.mk0 u₀ hu0
  set Pu : Kˣ := Units.mk0 π hπ0
  let f : Bool × Bool → SqCl K := fun b =>
    QuotientGroup.mk ((if b.1 then U else 1) * (if b.2 then Pu else 1))
  have sq_mul : ∀ {s r : K}, IsSquare s → IsSquare (s * r ^ 2) := fun {s r} ⟨m, hm⟩ =>
    ⟨m * r, by rw [hm]; ring⟩
  have hsurj : Function.Surjective f := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
    have hx0 : (x : K) ≠ 0 := x.ne_zero
    obtain ⟨hwv, hxw⟩ := unit_decomp hπ hx0
    set w := (x : K) * π ^ (L (x : K))
    have hw0 : w ≠ 0 := ne_zero_of_v one_ne_zero hwv
    -- the unit class
    obtain ⟨b₁, hb₁⟩ : ∃ b₁ : Bool, IsSquare (w * (if b₁ then u₀⁻¹ else 1)) := by
      rcases h.unit_sq_classes w u₀ hwv hu₀ with hs | hs | hs
      · exact ⟨false, by simpa using hs⟩
      · exact absurd hs hu₀s
      · refine ⟨true, ?_⟩
        have : w * (if true = true then u₀⁻¹ else 1) = w * u₀ * (u₀⁻¹) ^ 2 := by
          simp only [ite_true]; field_simp
        rw [this]; exact sq_mul hs
    have key : ∀ r : Kˣ, IsSquare ((r : K)⁻¹ * (x : K)) → (QuotientGroup.mk r : SqCl K) = QuotientGroup.mk x := by
      intro r hr
      rw [QuotientGroup.eq, ← QuotientGroup.eq_one_iff, mk_eq_one_iff_isSquare]
      simpa using hr
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (L (x : K))
    · refine ⟨(b₁, false), key _ ?_⟩
      have e : (x : K) = w * (π ^ (-j)) ^ 2 := by
        rw [hxw, hj, ← zpow_natCast, ← zpow_mul]; congr 2; push_cast; ring
      cases b₁
      · simp only [Bool.false_eq_true, ite_false, mul_one, Units.val_one, inv_one, one_mul] at hb₁ ⊢
        rw [e]; exact sq_mul hb₁
      · simp only [Bool.false_eq_true, ite_false, ite_true, mul_one, Units.val_mk0, U] at hb₁ ⊢
        rw [e, ← mul_assoc, mul_comm _ w]; exact sq_mul hb₁
    · refine ⟨(b₁, true), key _ ?_⟩
      have e : (x : K) = π * w * (π⁻¹ * π ^ (-j)) ^ 2 := by
        rw [hxw, hj, mul_pow, ← zpow_natCast (π ^ (-j)), ← zpow_mul]
        have e2 : -(2 * j + 1) = ((-j) * ((2 : ℕ) : ℤ)) + (-1) := by push_cast; ring
        rw [e2, zpow_add₀ hπ0, zpow_neg_one]
        field_simp
      cases b₁
      · simp only [Bool.false_eq_true, ite_false, mul_one, ite_true, one_mul, Units.val_mk0, Pu] at hb₁ ⊢
        rw [e, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hπ0, one_mul]; exact sq_mul hb₁
      · simp only [ite_true, Units.val_mul, Units.val_mk0, U, Pu] at hb₁ ⊢
        rw [e, mul_inv, show u₀⁻¹ * π⁻¹ * (π * w * (π⁻¹ * π ^ (-j)) ^ 2) =
          (w * u₀⁻¹) * (π⁻¹ * π ^ (-j)) ^ 2 by field_simp]
        exact sq_mul hb₁
  exact ⟨Finite.of_surjective f hsurj, (Nat.card_le_card_of_surjective f hsurj).trans (by simp)⟩

end FF.OddLocalAxioms

namespace RatFuncPlace

open scoped Classical

variable (k : Type) [Field k]

/-- **Primes of $k[t]$ with prescribed square classes (named input; the function field case of
`PresNF.exists_prime_sq_nonsq`).** Let $a_i \in k(t)$ ($i \in s$, a finite set) and $u \in k(t)$ with
$u \prod_{i \in t} a_i$ a nonsquare in $k(t)$ for every $t \subseteq s$ (i.e. $u \notin \langle a_i \rangle k(t)^{\times 2}$; in
particular all $a_i$ and $u$ are nonzero). Then for every finite set $B$ of finite places of $k(t)$ there is a finite place
$\mathfrak p \notin B$ at which every $a_i$ is a square in $k(t)_{\mathfrak p}$ and $u$ is not.

For $k = \mathbb{F}_q$ this is a case of the Chebotarev density theorem for the multiquadratic extension
$k(t)(\sqrt{a_i}, \sqrt u)$ (Rosen, Thm. 9.13B), and by quadratic reciprocity in $\mathbb{F}_q[t]$ it is equivalent to a
statement about primes in residue classes and of prescribed degree parity, i.e. to Kornblum's Dirichlet theorem for
$\mathbb{F}_q[t]$ (Rosen, Thm. 4.8). It is not proved here: the proof needs the $L$-functions of quadratic characters of
$\mathbb{F}_q[t]$ and their nonvanishing at $u = 1/q$ (equivalently, that the zeta function of a quadratic extension of
$\mathbb{F}_q(t)$ has a simple pole), which needs Riemann–Roch for curves. (Over a number field the library proves the
analogue from Dedekind's density argument applied in the quadratic extensions, `PresNF.exists_prime_sq_nonsq`.) For
infinite $k$ the statement can fail; it is used only for finite $k$. -/
@[kb "rosen2002" "Ch. 9, Thm. 9.13B (Chebotarev density theorem for function fields) [unverified]; milne2020cft Ch. VII, Lemma 6.2 (function field case) [unverified]"]
structure PrescribedSquarePrimes : Prop where
  exists_prime : ∀ {ι : Type} (s : Finset ι) (a : ι → RatFunc k) (u : RatFunc k),
    (∀ t ⊆ s, ¬ IsSquare (u * ∏ i ∈ t, a i)) →
    ∀ B : Finset (HeightOneSpectrum k[X]), ∃ p ∉ B,
      (∀ i ∈ s, IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) (a i))) ∧
      ¬ IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) u)

variable {k}

/-! ### Factorization: even valuations outside $S$ -/

/-- **Even valuation outside $S$ means $S$-unit times square** (any field $k$): if $x \in k(t)^\times$ has
$v(x) = g^2$ for every finite place $v \notin S$, then $x = d z^2$ with $d \in k[t]$ a unit at every finite place outside
$S$. *Proof.* Write $x = p/q$ and $pq = e^2 d$ with $d$ squarefree; an irreducible factor $P$ of $d$ outside $S$ would give
$v_P(d) = 1$ while $v_P(pq) = v_P(x q^2)$ is even. -/
@[kb "omeara1963" "§65 (S-units, function field case) [unverified]"]
theorem exists_poly_mul_sq (S : Finset (HeightOneSpectrum k[X])) (x : RatFunc k) (hx : x ≠ 0)
    (heven : ∀ v ∉ S, ∃ g : ℤᵐ⁰, v.valuation (RatFunc k) x = g * g) :
    ∃ d : k[X], d ≠ 0 ∧ (∀ v ∉ S, v.intValuation d = 1) ∧
      ∃ z : RatFunc k, z ≠ 0 ∧ x = algebraMap k[X] (RatFunc k) d * z ^ 2 := by
  classical
  set p := x.num
  set q := x.denom
  have hq : q ≠ 0 := RatFunc.denom_ne_zero x
  have hp : p ≠ 0 := by simpa [p] using hx
  have hpq : algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q = x :=
    RatFunc.num_div_denom x
  have hqK : algebraMap k[X] (RatFunc k) q ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact hq
  obtain ⟨e, d, hed, hd⟩ := exists_sq_mul_squarefree (p * q)
  have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hed; exact mul_ne_zero hp hq hed.symm
  have he0 : e ≠ 0 := by
    rintro rfl; rw [zero_pow two_ne_zero, zero_mul] at hed; exact mul_ne_zero hp hq hed.symm
  have heK : algebraMap k[X] (RatFunc k) e ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact he0
  have hxq : algebraMap k[X] (RatFunc k) (p * q) = x * algebraMap k[X] (RatFunc k) q ^ 2 := by
    rw [← hpq, map_mul]; field_simp
  refine ⟨d, hd0, ?_, algebraMap k[X] (RatFunc k) e / algebraMap k[X] (RatFunc k) q,
    div_ne_zero heK hqK, ?_⟩
  · intro v hv
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    intro hmem
    obtain ⟨P, hP⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
    have hP' : v.asIdeal = Ideal.span {P} := hP
    have h2 : d ∉ v.asIdeal ^ 2 := by
      intro hmem2
      rw [hP', Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem2
      have hu : IsUnit P := hd P (by rw [← sq]; exact hmem2)
      exact v.isPrime.ne_top (by rw [hP']; exact Ideal.span_singleton_eq_top.mpr hu)
    have hv1 := FF.intValuation_eq_exp_neg_one v d hmem h2
    obtain ⟨g, hg⟩ := heven v hv
    have hval := congrArg (v.valuation (RatFunc k)) hxq
    rw [HeightOneSpectrum.valuation_of_algebraMap, ← hed, map_mul, map_pow, hv1, map_mul, map_pow,
      hg, HeightOneSpectrum.valuation_of_algebraMap] at hval
    have hve : v.intValuation e ≠ 0 := v.intValuation_ne_zero e he0
    apply FF.mul_self_ne_exp_neg_one (g * v.intValuation q / v.intValuation e)
    have hvq : v.intValuation q ≠ 0 := v.intValuation_ne_zero q hq
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hve hve)]
    calc g * v.intValuation q * (g * v.intValuation q) = g * g * v.intValuation q ^ 2 := by rw [sq]; ac_rfl
      _ = v.intValuation e ^ 2 * exp (-1 : ℤ) := hval.symm
      _ = exp (-1 : ℤ) * (v.intValuation e * v.intValuation e) := by rw [sq, mul_comm]
  · rw [← hpq]
    have : algebraMap k[X] (RatFunc k) p * algebraMap k[X] (RatFunc k) q =
        algebraMap k[X] (RatFunc k) e ^ 2 * algebraMap k[X] (RatFunc k) d := by
      rw [← map_mul, ← hed, map_mul, map_pow]
    field_simp
    linear_combination this

/-- The place $t = 0$ of $k(t)$ (the prime $(t)$ of $k[t]$). -/
abbrev placeX : HeightOneSpectrum k[X] := ofIrreducible (X : k[X]) Polynomial.irreducible_X

/-- **A constant that is a square at $t = 0$ is a square in $k$** (the residue field at $t = 0$ is $k$). -/
lemma isSquare_of_isSquare_placeX (c : k)
    (h : IsSquare (algebraMap (RatFunc k) ((placeX (k := k)).adicCompletion (RatFunc k))
      (algebraMap k[X] (RatFunc k) (C c)))) : IsSquare c := by
  obtain ⟨r, hr⟩ := FF.exists_sq_mod_of_isSquare (placeX (k := k)) (C c) h
  rw [ofIrreducible_asIdeal, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero] at hr
  simp only [eval_sub, eval_C, eval_pow] at hr
  exact ⟨r.eval 0, by linear_combination hr⟩

/-- **Parity over $S \cup \{\infty\}$:** if $e$ is $\pm 1$-valued with an even number of $-1$'s, all at $\infty$ or at
finite places in $S$, then $\prod_{v \in S} e_v \cdot e_\infty = 1$. -/
lemma prod_eps_eq_one (S : Finset (HeightOneSpectrum k[X])) (e : RatFuncPlace k → ℤ)
    (he : ∀ v, e v = 1 ∨ e v = -1) (hS : ∀ v : HeightOneSpectrum k[X], e (finite v) = -1 → v ∈ S)
    (heven : Even {v : RatFuncPlace k | e v = -1}.ncard) :
    (∏ v : S, e (finite v.1)) * e infinite = 1 := by
  classical
  set A := Finset.univ.filter fun v : S => e (finite v.1) = -1
  rw [prod_pm_eq_pow (fun v : S => e (finite v.1)) fun v => he _]
  have hinj : Function.Injective fun v : S => (finite v.1 : RatFuncPlace k) := fun x y h =>
    Subtype.ext (finite.inj h)
  have himg : {v : RatFuncPlace k | e v = -1} ∩ Set.range finite =
      (fun v : S => (finite v.1 : RatFuncPlace k)) '' (A : Set S) := by
    ext v
    constructor
    · rintro ⟨hv, w, rfl⟩
      exact ⟨⟨w, hS w hv⟩, by simpa [A] using hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨by simpa [A] using hw, w.1, rfl⟩
  have hcardA : ({v : RatFuncPlace k | e v = -1} ∩ Set.range finite).ncard = A.card := by
    rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]
  rcases he infinite with hinf | hinf
  · have hE : {v : RatFuncPlace k | e v = -1} = {v | e v = -1} ∩ Set.range finite := by
      ext v
      cases v with
      | finite w => simp
      | infinite => simp [hinf]
    rw [hinf, mul_one]
    rw [hE, hcardA] at heven
    exact heven.neg_one_pow
  · have hE : {v : RatFuncPlace k | e v = -1} =
        insert infinite ({v | e v = -1} ∩ Set.range finite) := by
      ext v
      cases v with
      | finite w => simp
      | infinite => simp [hinf]
    have hnot : infinite ∉ ({v : RatFuncPlace k | e v = -1} ∩ Set.range finite) := by
      rintro ⟨-, w, hw⟩; cases hw
    have hfin : ({v : RatFuncPlace k | e v = -1} ∩ Set.range finite).Finite := by
      rw [himg]; exact Set.toFinite _
    rw [hE, Set.ncard_insert_of_notMem hnot hfin, hcardA] at heven
    rw [hinf, ← pow_succ]
    exact heven.neg_one_pow

/-! ### The group $G_S$ and its pairing -/

section Global

variable [Fintype k] [hk : Fact (ringChar k ≠ 2)]

include hk

lemma oddFin (v : HeightOneSpectrum k[X]) : FF.OddLocalAxioms (v.adicCompletion (RatFunc k)) :=
  oddLocalAxioms_finite v hk.out

lemma oddInf : FF.OddLocalAxioms (RatFunc.CompletionAtInfty k) := oddLocalAxioms_infty hk.out

instance (v : HeightOneSpectrum k[X]) : Finite (SqCl (v.adicCompletion (RatFunc k))) :=
  (oddFin v).card_sqCl_le.1

instance : Finite (SqCl (RatFunc.CompletionAtInfty k)) := (oddInf (k := k)).card_sqCl_le.1

variable (k) in
/-- **The group $G_S = \prod_{v \in S} k(t)_v^\times/k(t)_v^{\times 2} \times k(t)_\infty^\times/k(t)_\infty^{\times 2}$** for a finite
set $S$ of finite places. -/
abbrev GSq (S : Finset (HeightOneSpectrum k[X])) : Type :=
  ((v : S) → SqCl (v.1.adicCompletion (RatFunc k))) × SqCl (RatFunc.CompletionAtInfty k)

/-- **$|G_S| \le 4^{|S| + 1}$.** -/
lemma card_GSq_le (S : Finset (HeightOneSpectrum k[X])) : Nat.card (GSq k S) ≤ 4 ^ (S.card + 1) := by
  rw [Nat.card_prod, Nat.card_pi, pow_succ]
  refine Nat.mul_le_mul ?_ (oddInf (k := k)).card_sqCl_le.2
  calc ∏ v : S, Nat.card (SqCl (v.1.adicCompletion (RatFunc k))) ≤ 4 ^ (Finset.univ : Finset S).card :=
        Finset.prod_le_pow_card _ _ _ fun v _ => (oddFin v.1).card_sqCl_le.2
    _ = 4 ^ S.card := by rw [Finset.card_univ, Fintype.card_coe]

/-- **The localization map** $k(t)^\times \to G_S$. -/
def locMapS (S : Finset (HeightOneSpectrum k[X])) : (RatFunc k)ˣ →* GSq k S :=
  MonoidHom.prod
    (MonoidHom.pi fun v : S => (QuotientGroup.mk' _).comp
      (Units.map (algebraMap (RatFunc k) (v.1.adicCompletion (RatFunc k))).toMonoidHom))
    ((QuotientGroup.mk' _).comp (Units.map (algebraMap (RatFunc k) (RatFunc.CompletionAtInfty k)).toMonoidHom))

/-- **The product pairing** $\langle x, y \rangle_S = \prod_{v \in S \cup \{\infty\}} (x_v, y_v)_v$ on $G_S$. -/
def BSq (S : Finset (HeightOneSpectrum k[X])) (x y : GSq k S) : ℤ :=
  (∏ v : S, hilbCl _ (x.1 v) (y.1 v)) * hilbCl _ x.2 y.2

lemma BSq_pm (S : Finset (HeightOneSpectrum k[X])) (x y : GSq k S) : BSq S x y = 1 ∨ BSq S x y = -1 := by
  have h1 := prod_pm Finset.univ (fun v : S => hilbCl _ (x.1 v) (y.1 v)) fun v => hilbCl_pm _ _ _
  unfold BSq
  rcases h1 with h | h <;> rcases hilbCl_pm _ x.2 y.2 with h' | h' <;> rw [h, h'] <;> norm_num

lemma BSq_mul (S : Finset (HeightOneSpectrum k[X])) (x x' y : GSq k S) :
    BSq S (x * x') y = BSq S x y * BSq S x' y := by
  unfold BSq
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  rw [Finset.prod_congr rfl fun v _ => (oddFin v.1).hilbCl_mul _ _ _, (oddInf (k := k)).hilbCl_mul,
    Finset.prod_mul_distrib]
  ring

lemma BSq_symm (S : Finset (HeightOneSpectrum k[X])) (x y : GSq k S) : BSq S x y = BSq S y x := by
  unfold BSq
  rw [Finset.prod_congr rfl fun v _ => hilbCl_symm _ (x.1 v) (y.1 v), hilbCl_symm _ x.2]

lemma BSq_nondeg (S : Finset (HeightOneSpectrum k[X])) (y : GSq k S) (hy : y ≠ 1) :
    ∃ x, BSq S x y = -1 := by
  classical
  by_cases h1 : y.1 = 1
  · have h2 : y.2 ≠ 1 := fun h => hy (Prod.ext h1 h)
    obtain ⟨c, hc⟩ := (oddInf (k := k)).hilbCl_nondeg y.2 h2
    refine ⟨(1, c), ?_⟩
    unfold BSq
    rw [Finset.prod_eq_one (fun v _ => by exact hilbCl_one_left _ _), one_mul]
    exact hc
  · obtain ⟨v, hv⟩ : ∃ v, y.1 v ≠ 1 := by
      by_contra h; push Not at h; exact h1 (funext h)
    obtain ⟨c, hc⟩ := (oddFin v.1).hilbCl_nondeg (y.1 v) hv
    refine ⟨(Pi.mulSingle v c, 1), ?_⟩
    unfold BSq
    have e2 : ∏ v' : S, hilbCl _ (Pi.mulSingle (M := fun v' : S => SqCl (v'.1.adicCompletion (RatFunc k)))
        v c v') (y.1 v') = hilbCl _ c (y.1 v) := by
      rw [Finset.prod_eq_single v (fun v' _ hv' => by rw [Pi.mulSingle_eq_of_ne hv', hilbCl_one_left])
        (by simp), Pi.mulSingle_eq_same]
    rw [e2, hilbCl_one_left, mul_one, hc]

/-- The pairing $\langle\,,\rangle_S$ as a `PresNF.SignPairing`. -/
def pairingSq (S : Finset (HeightOneSpectrum k[X])) : PresNF.SignPairing (GSq k S) :=
  ⟨BSq S, BSq_pm S, BSq_mul S, BSq_symm S, BSq_nondeg S⟩

lemma BSq_locMapS (S : Finset (HeightOneSpectrum k[X])) (a b : (RatFunc k)ˣ) :
    BSq S (locMapS S a) (locMapS S b) =
      (∏ v : S, (finite v.1).hilbert (a : RatFunc k) (b : RatFunc k)) *
        infinite.hilbert (a : RatFunc k) (b : RatFunc k) := rfl

variable (k) in
/-- **The $S$-units** of $k(t)$: the $x \in k(t)^\times$ with $v(x) = 1$ at every finite place $v \notin S$. -/
def SUnitS (S : Finset (HeightOneSpectrum k[X])) : Subgroup (RatFunc k)ˣ where
  carrier := {x | ∀ v ∉ S, v.valuation (RatFunc k) (x : RatFunc k) = 1}
  one_mem' := fun v _ => by simp
  mul_mem' := fun {x y} hx hy v hv => by rw [Units.val_mul, map_mul, hx v hv, hy v hv, one_mul]
  inv_mem' := fun {x} hx v hv => by rw [Units.val_inv_eq_inv_val, map_inv₀, hx v hv, inv_one]

/-- **The image $\Lambda_S$ of the $S$-units** in $G_S$. -/
abbrev LamSq (S : Finset (HeightOneSpectrum k[X])) : Subgroup (GSq k S) := (SUnitS k S).map (locMapS S)

/-- **Two units at a finite place have Hilbert symbol $1$.** -/
lemma hilbert_units_fin (v : HeightOneSpectrum k[X]) (a b : RatFunc k)
    (ha : v.valuation (RatFunc k) a = 1) (hb : v.valuation (RatFunc k) b = 1) :
    (finite v).hilbert a b = 1 :=
  (oddFin v).hs_units (by rw [FF.valued_algebraMap]; exact ha) (by rw [FF.valued_algebraMap]; exact hb)

/-- **$\Lambda_S$ is isotropic** (Hilbert reciprocity). -/
@[kb "omeara1963" "§71, 71:18 (applied to S-units, F = F_q(t)) [unverified]"]
theorem BSq_sUnit (hR : HilbertReciprocity k) (S : Finset (HeightOneSpectrum k[X])) {a b : (RatFunc k)ˣ}
    (ha : a ∈ SUnitS k S) (hb : b ∈ SUnitS k S) : BSq S (locMapS S a) (locMapS S b) = 1 := by
  rw [BSq_locMapS]
  obtain ⟨-, heven⟩ := hR.reciprocity a b a.ne_zero b.ne_zero
  refine prod_eps_eq_one S (fun v => v.hilbert a b) (fun v => hilbert_pm v _ _) (fun v hv => ?_) heven
  by_contra hvS
  have := hilbert_units_fin v _ _ (ha v hvS) (hb v hvS)
  rw [this] at hv; norm_num at hv

/-- An element with trivial image in $G_S$ is a square at every $v \in S$. -/
lemma isSquare_of_locMapS_fin {S : Finset (HeightOneSpectrum k[X])} {z : (RatFunc k)ˣ}
    (h : locMapS S z = 1) (v : S) :
    IsSquare (algebraMap (RatFunc k) (v.1.adicCompletion (RatFunc k)) (z : RatFunc k)) :=
  (mk_eq_one_iff_isSquare _ _).mp (congrFun (congrArg Prod.fst h) v)

/-- $g^2 \ne \exp(1)$ in $\mathbb{Z}_{(0)}$. -/
lemma mul_self_ne_exp_one (g : ℤᵐ⁰) : g * g ≠ exp (1 : ℤ) := by
  intro h
  apply FF.mul_self_ne_exp_neg_one g⁻¹
  rw [← mul_inv, h, ← exp_neg]

/-! ### Generators of the finite places -/

/-- A generator $\pi_v \in k[t]$ of the prime $v$. -/
def gen (v : HeightOneSpectrum k[X]) : k[X] := Submodule.IsPrincipal.generator v.asIdeal

lemma span_gen (v : HeightOneSpectrum k[X]) : Ideal.span {gen v} = v.asIdeal :=
  Ideal.span_singleton_generator v.asIdeal

lemma gen_mem (v : HeightOneSpectrum k[X]) : gen v ∈ v.asIdeal :=
  Submodule.IsPrincipal.generator_mem v.asIdeal

lemma gen_ne_zero (v : HeightOneSpectrum k[X]) : gen v ≠ 0 := by
  intro h
  apply v.ne_bot
  rw [← span_gen, h, Ideal.span_singleton_eq_bot]

lemma intValuation_gen_self (v : HeightOneSpectrum k[X]) : v.intValuation (gen v) = exp (-1 : ℤ) := by
  refine FF.intValuation_eq_exp_neg_one v _ (gen_mem v) fun hmem => ?_
  rw [← span_gen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hu : IsUnit (gen v * c) := by
    have : gen v * 1 = gen v * (gen v * c) := by rw [mul_one]; nth_rw 1 [hc]; ring
    rw [← mul_left_cancel₀ (gen_ne_zero v) this]; exact isUnit_one
  apply v.isPrime.ne_top
  rw [← span_gen]
  exact Ideal.span_singleton_eq_top.mpr (isUnit_of_mul_isUnit_left hu)

lemma intValuation_gen_ne {v w : HeightOneSpectrum k[X]} (h : w ≠ v) : w.intValuation (gen v) = 1 := by
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply h
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [← span_gen, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm

lemma intValuation_C {c : k} (hc : c ≠ 0) (w : HeightOneSpectrum k[X]) : w.intValuation (C c) = 1 := by
  rw [HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (isUnit_C.mpr (Ne.isUnit hc)))

/-- $\pi_v$ as a unit of $k(t)$. -/
def genU (v : HeightOneSpectrum k[X]) : (RatFunc k)ˣ :=
  Units.mk0 (algebraMap k[X] (RatFunc k) (gen v))
    ((map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (gen_ne_zero v))

/-- A nonzero constant as a unit of $k(t)$. -/
def constU (c : k) (hc : c ≠ 0) : (RatFunc k)ˣ :=
  Units.mk0 (algebraMap k[X] (RatFunc k) (C c))
    ((map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (C_ne_zero.mpr hc))

/-- The representatives $c_0^b \prod_{v \in T} \pi_v$ of $\Lambda_S$. -/
def rep {S : Finset (HeightOneSpectrum k[X])} (c₀ : k) (hc₀ : c₀ ≠ 0) (T : Finset S) (b : Bool) :
    (RatFunc k)ˣ :=
  (if b then constU c₀ hc₀ else 1) * ∏ v ∈ T, genU v.1

lemma valuation_rep {S : Finset (HeightOneSpectrum k[X])} (c₀ : k) (hc₀ : c₀ ≠ 0) (T : Finset S)
    (b : Bool) (w : HeightOneSpectrum k[X]) :
    w.valuation (RatFunc k) (rep c₀ hc₀ T b : RatFunc k) = ∏ v ∈ T, w.intValuation (gen v.1) := by
  have hc : w.valuation (RatFunc k) ((if b then constU c₀ hc₀ else 1 : (RatFunc k)ˣ) : RatFunc k) = 1 := by
    cases b
    · simp
    · simp only [ite_true, constU, Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap]
      exact intValuation_C hc₀ w
  rw [rep, Units.val_mul, map_mul, hc, one_mul, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [genU, Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap]

lemma rep_mem {S : Finset (HeightOneSpectrum k[X])} (c₀ : k) (hc₀ : c₀ ≠ 0) (T : Finset S) (b : Bool) :
    rep c₀ hc₀ T b ∈ SUnitS k S := by
  intro w hw
  rw [valuation_rep]
  exact Finset.prod_eq_one fun v _ => intValuation_gen_ne fun h => hw (h ▸ v.2)

lemma valuation_rep_self {S : Finset (HeightOneSpectrum k[X])} (c₀ : k) (hc₀ : c₀ ≠ 0) (T : Finset S)
    (b : Bool) (u : S) :
    u.1.valuation (RatFunc k) (rep c₀ hc₀ T b : RatFunc k) = if u ∈ T then exp (-1 : ℤ) else 1 := by
  rw [valuation_rep]
  rw [Finset.prod_congr rfl fun v _ => show u.1.intValuation (gen v.1) =
      if v = u then exp (-1 : ℤ) else 1 by
    split_ifs with h
    · rw [h]; exact intValuation_gen_self u.1
    · exact intValuation_gen_ne fun h' => h (Subtype.ext h'.symm)]
  rw [Finset.prod_ite_eq']

/-- **The kernel condition:** an $S$-unit that is a square at every place of $S$ and at $\infty$ is a square, if $S$ contains the
place $t = 0$. -/
@[kb "omeara1963" "§65 (S-units and squares, F = F_q(t)) [unverified]"]
theorem isSquare_of_locMapS_eq_one {S : Finset (HeightOneSpectrum k[X])} (hX : placeX ∈ S)
    {x : (RatFunc k)ˣ} (hx : x ∈ SUnitS k S) (h1 : locMapS S x = 1) : IsSquare (x : RatFunc k) := by
  have heven : ∀ v ∉ (∅ : Finset (HeightOneSpectrum k[X])),
      ∃ g : ℤᵐ⁰, v.valuation (RatFunc k) (x : RatFunc k) = g * g := by
    intro v _
    by_cases hv : v ∈ S
    · exact FF.valuation_isSquare_of_isSquare v _ (isSquare_of_locMapS_fin h1 ⟨v, hv⟩)
    · exact ⟨1, by rw [hx v hv, one_mul]⟩
  obtain ⟨d, hd0, hd1, z, hz0, hxz⟩ := exists_poly_mul_sq ∅ _ x.ne_zero heven
  -- `d` is a constant
  obtain ⟨c, hc, rfl⟩ : ∃ c : k, c ≠ 0 ∧ C c = d := by
    have hunit : IsUnit d := by
      by_contra hnu
      obtain ⟨P, hP, hPd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd0
      have h1 := hd1 (ofIrreducible P hP) (Finset.notMem_empty _)
      rw [HeightOneSpectrum.intValuation_eq_one_iff] at h1
      exact h1 (by rw [ofIrreducible_asIdeal]; exact Ideal.mem_span_singleton.mpr hPd)
    obtain ⟨c, hcu, hcd⟩ := Polynomial.isUnit_iff.mp hunit
    exact ⟨c, hcu.ne_zero, hcd⟩
  have hsq := isSquare_of_locMapS_fin h1 ⟨placeX, hX⟩
  have hc0 : IsSquare (algebraMap (RatFunc k) ((placeX (k := k)).adicCompletion (RatFunc k))
      (algebraMap k[X] (RatFunc k) (C c))) := by
    obtain ⟨s, hs⟩ := hsq
    refine ⟨s / algebraMap (RatFunc k) _ z, ?_⟩
    have hzK : algebraMap (RatFunc k) ((placeX (k := k)).adicCompletion (RatFunc k)) z ≠ 0 :=
      (_root_.map_ne_zero _).mpr hz0
    have : algebraMap k[X] (RatFunc k) (C c) = (x : RatFunc k) / z ^ 2 := by
      rw [hxz]; field_simp
    rw [this, map_div₀, hs, map_pow]
    field_simp
  obtain ⟨r, hr⟩ := isSquare_of_isSquare_placeX c hc0
  refine ⟨algebraMap k[X] (RatFunc k) (C r) * z, ?_⟩
  rw [hxz, hr, C_mul, map_mul]
  ring

/-- **$\Lambda_S$ is a Lagrangian:** $|\Lambda_S|^2 = |G_S|$, for $S$ containing the place $t = 0$. -/
@[kb "serre1973" "Ch. III §2.2, proof of Thm. 4 (function field case) [unverified]"]
theorem card_lamSq (hR : HilbertReciprocity k) {S : Finset (HeightOneSpectrum k[X])} (hX : placeX ∈ S) :
    Nat.card (LamSq S) * Nat.card (LamSq S) = Nat.card (GSq k S) := by
  set P := pairingSq S
  set Λ := LamSq S
  have hiso : ∀ x ∈ Λ, ∀ y ∈ Λ, P.B x y = 1 := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact BSq_sUnit hR S ha hb
  have hle : Λ ≤ P.orth Λ := fun y hy x hx => hiso x hx y hy
  have hm := P.card_mul_card_orth Λ
  have hle' : Nat.card Λ ≤ Nat.card (P.orth Λ) := Subgroup.card_le_of_le hle
  have hG := card_GSq_le S
  -- the lower bound `2 ^ (|S| + 1) ≤ |Λ|`
  obtain ⟨c₀, hc₀⟩ := FiniteField.exists_nonsquare hk.out
  have hc₀0 : c₀ ≠ 0 := by rintro rfl; exact hc₀ ⟨0, by simp⟩
  let f : Finset S × Bool → Λ := fun p =>
    ⟨locMapS S (rep c₀ hc₀0 p.1 p.2), Subgroup.mem_map_of_mem _ (rep_mem c₀ hc₀0 p.1 p.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨T, b⟩ ⟨T', b'⟩ hTT
    have hloc : locMapS S ((rep c₀ hc₀0 T b)⁻¹ * rep c₀ hc₀0 T' b') = 1 := by
      have := congrArg Subtype.val hTT
      simp only [f] at this
      rw [map_mul, map_inv, this]; exact inv_mul_cancel (G := GSq k S) _
    have hval : ∀ u : S, ∃ g : ℤᵐ⁰, (if u ∈ T then exp (-1 : ℤ) else 1)⁻¹ *
        (if u ∈ T' then exp (-1 : ℤ) else 1) = g * g := by
      intro u
      obtain ⟨g, hg⟩ := FF.valuation_isSquare_of_isSquare u.1 _ (isSquare_of_locMapS_fin hloc u)
      refine ⟨g, ?_⟩
      rw [← hg, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valuation_rep_self,
        valuation_rep_self]
    have hT : T = T' := by
      ext u
      obtain ⟨g, hg⟩ := hval u
      by_cases h1 : u ∈ T <;> by_cases h2 : u ∈ T' <;> simp only [h1, h2, ite_true, ite_false,
        inv_one, one_mul, mul_one] at hg ⊢
      · exact (mul_self_ne_exp_one (k := k) g (by rw [← hg, ← exp_neg, neg_neg])).elim
      · exact (FF.mul_self_ne_exp_neg_one g hg.symm).elim
    subst hT
    have hb : b = b' := by
      by_contra hbb
      have hsq := isSquare_of_locMapS_fin hloc ⟨placeX, hX⟩
      have hcancel : ((rep c₀ hc₀0 T b)⁻¹ * rep c₀ hc₀0 T b' : (RatFunc k)ˣ) =
          (if b then constU c₀ hc₀0 else 1)⁻¹ * (if b' then constU c₀ hc₀0 else 1) := by
        rw [rep, rep, mul_comm (if b then _ else _), mul_comm (if b' then _ else _), mul_inv_rev,
          mul_assoc, inv_mul_cancel_left]
      rw [hcancel] at hsq
      apply hc₀
      apply isSquare_of_isSquare_placeX
      cases b <;> cases b' <;> simp only [not_true_eq_false, Bool.false_eq_true,
        not_false_eq_true, reduceCtorEq] at hbb
      · simpa [constU] using hsq
      · have := hsq.inv
        simpa [constU] using this
    rw [hb]
  have hlow : 2 ^ (S.card + 1) ≤ Nat.card Λ := by
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := Finset S × Bool), Fintype.card_prod, Fintype.card_finset,
      Fintype.card_coe, Fintype.card_bool, ← pow_succ] at this
    exact this
  apply le_antisymm
  · calc Nat.card Λ * Nat.card Λ ≤ Nat.card Λ * Nat.card (P.orth Λ) := Nat.mul_le_mul_left _ hle'
      _ = Nat.card (GSq k S) := hm
  · calc Nat.card (GSq k S) ≤ 4 ^ (S.card + 1) := hG
      _ = 2 ^ (S.card + 1) * 2 ^ (S.card + 1) := by
        rw [← mul_pow]; norm_num
      _ ≤ Nat.card Λ * Nat.card Λ := Nat.mul_le_mul hlow hlow

end Global

/-! ### Assembly -/

/-- Only finitely many finite places have $v(a) \ne 1$, for $a \in k(t)^\times$. -/
lemma finite_valuation_ne_one (a : RatFunc k) (ha : a ≠ 0) :
    {v : HeightOneSpectrum k[X] | v.valuation (RatFunc k) a ≠ 1}.Finite := by
  have hfin : ∀ p : k[X], p ≠ 0 → {v : HeightOneSpectrum k[X] | p ∈ v.asIdeal}.Finite := by
    intro p hp
    refine (Ideal.finite_factors (I := Ideal.span {p}) (by simpa using hp)).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    rw [Ideal.dvd_span_singleton]; exact hv
  refine ((hfin a.num (RatFunc.num_ne_zero ha)).union (hfin a.denom a.denom_ne_zero)).subset ?_
  intro v hv
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
  apply hv
  rw [← RatFunc.num_div_denom a, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hcon.1,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hcon.2, div_one]

section Main

variable [Fintype k] [hk : Fact (ringChar k ≠ 2)]

include hk

lemma GSq_inv (S : Finset (HeightOneSpectrum k[X])) (g : GSq k S) : g⁻¹ = g :=
  Prod.ext (funext fun v => PresNF.sqCl_inv _ (g.1 v)) (PresNF.sqCl_inv _ g.2)

/-- A global square has trivial image in $G_S$. -/
lemma locMapS_eq_one_of_isSquare (S : Finset (HeightOneSpectrum k[X])) (w : (RatFunc k)ˣ)
    (h : IsSquare (w : RatFunc k)) : locMapS S w = 1 := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  have : w = Units.mk0 r hr0 ^ 2 := Units.ext (by simp [hr, sq])
  rw [this, map_pow]
  set g := locMapS S (Units.mk0 r hr0)
  exact Prod.ext (funext fun v => sqCl_sq _ (g.1 v))
    (sqCl_sq _ g.2)

lemma BSq_prod (S : Finset (HeightOneSpectrum k[X])) {ι : Type*} (t : Finset ι) (x : ι → GSq k S)
    (y : GSq k S) : BSq S (∏ i ∈ t, x i) y = ∏ i ∈ t, BSq S (x i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact (pairingSq S).one_left y
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, BSq_mul, ih]

/-- A chosen $S$-unit lifting an element of $\Lambda_S$. -/
def liftU {S : Finset (HeightOneSpectrum k[X])} (d : LamSq S) : (RatFunc k)ˣ :=
  (Subgroup.mem_map.mp d.2).choose

lemma liftU_mem {S : Finset (HeightOneSpectrum k[X])} (d : LamSq S) : liftU d ∈ SUnitS k S :=
  (Subgroup.mem_map.mp d.2).choose_spec.1

lemma locMapS_liftU {S : Finset (HeightOneSpectrum k[X])} (d : LamSq S) : locMapS S (liftU d) = d :=
  (Subgroup.mem_map.mp d.2).choose_spec.2

/-- **Elements of $\mathbb{F}_q(t)$ with prescribed local Hilbert symbols**, from Hilbert reciprocity and primes with
prescribed square classes (Serre III §2.2, Thm. 4, and O'Meara 71:19, for $F = \mathbb{F}_q(t)$, $q$ odd). The proof of
`PresNF.exists_prescribed_hilbert`: take $S$ containing $t = 0$, the support of $\varepsilon$ and of the $a_i$; for each
$\lambda \in \Lambda_S$ whose lift is not in $\langle a_i \rangle k(t)^{\times 2}$ add a prime where all $a_i$ are squares and
the lift is not (`PrescribedSquarePrimes`), giving $S'$; solve modulo the Lagrangian $\Lambda_{S'}$
(`PresNF.SignPairing.exists_mul_mem_of_orth`); outside $S'$ all symbols are symbols of units, hence $1$. -/
@[kb "serre1973" "Ch. III §2.2, Thm. 4 (function field case) [unverified]; omeara1963 §71D, 71:19, p. 203 (F = F_q(t))"]
theorem prescribedHilbert_of_inputs' (hR : HilbertReciprocity k) (hD : PrescribedSquarePrimes k) :
    PrescribedHilbert k := by
  refine ⟨fun {ι} _ a ha ε hε h1 h2 h3 => ?_⟩
  classical
  set aU : ι → (RatFunc k)ˣ := fun i => Units.mk0 (a i) (ha i) with haU
  -- the set `S`
  obtain ⟨S, hXS, hεS, haS⟩ : ∃ S : Finset (HeightOneSpectrum k[X]), placeX ∈ S ∧
      (∀ i (v : HeightOneSpectrum k[X]), ε i (finite v) = -1 → v ∈ S) ∧
      (∀ i, ∀ v ∉ S, v.valuation (RatFunc k) (a i) = 1) := by
    have hεfin : {v : HeightOneSpectrum k[X] | ∃ i, ε i (finite v) = -1}.Finite :=
      h1.preimage (f := (finite : HeightOneSpectrum k[X] → RatFuncPlace k))
        (fun x _ y _ h => finite.inj h)
    have hafin : ∀ i, {v : HeightOneSpectrum k[X] | v.valuation (RatFunc k) (a i) ≠ 1}.Finite :=
      fun i => finite_valuation_ne_one (a i) (ha i)
    refine ⟨{placeX} ∪ hεfin.toFinset ∪ Finset.univ.biUnion (fun i => (hafin i).toFinset),
      by simp, fun i v hv => Finset.mem_union_left _ (Finset.mem_union_right _
        (hεfin.mem_toFinset.mpr ⟨i, hv⟩)), fun i v hv => ?_⟩
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using h⟩))
  -- the added primes `R`
  let : Fintype (LamSq S) := Fintype.ofFinite _
  obtain ⟨R, hRS, hRbad⟩ : ∃ R : Finset (HeightOneSpectrum k[X]),
      (∀ p ∈ R, p ∉ S ∧ ∀ i, IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) (a i))) ∧
      (∀ d : LamSq S, (∀ t : Finset ι, ¬ IsSquare (((liftU d : (RatFunc k)ˣ) : RatFunc k) * ∏ i ∈ t, a i)) →
        ∃ p ∈ R, ¬ IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k))
          ((liftU d : (RatFunc k)ˣ) : RatFunc k))) := by
    have hgood : ∀ d : {d : LamSq S // ∀ t : Finset ι,
        ¬ IsSquare (((liftU d : (RatFunc k)ˣ) : RatFunc k) * ∏ i ∈ t, a i)},
        ∃ p : HeightOneSpectrum k[X], (p ∉ S ∧
          ∀ i, IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) (a i))) ∧
          ¬ IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k))
            ((liftU d.1 : (RatFunc k)ˣ) : RatFunc k)) := by
      rintro ⟨d, hd⟩
      obtain ⟨p, hp, hps, hpu⟩ := hD.exists_prime Finset.univ a ((liftU d : (RatFunc k)ˣ) : RatFunc k)
        (fun t _ => hd t) S
      exact ⟨p, ⟨hp, fun i => hps i (Finset.mem_univ i)⟩, hpu⟩
    choose f hf using hgood
    refine ⟨Finset.univ.image f, fun p hp => ?_, fun d hd => ⟨f ⟨d, hd⟩,
      Finset.mem_image_of_mem _ (Finset.mem_univ _), (hf ⟨d, hd⟩).2⟩⟩
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hf d).1
  set S' := S ∪ R with hS'def
  have hSS' : S ⊆ S' := Finset.subset_union_left
  have hXS' : placeX ∈ S' := hSS' hXS
  -- the local solutions
  have hxf : ∀ v : HeightOneSpectrum k[X], ∃ x : (v.adicCompletion (RatFunc k))ˣ,
      ∀ i, hilbertSymbol _ (algebraMap (RatFunc k) _ (a i)) (x : v.adicCompletion (RatFunc k)) =
        ε i (finite v) := by
    intro v
    obtain ⟨x, hx0, hx⟩ : ∃ x : v.adicCompletion (RatFunc k), x ≠ 0 ∧
        ∀ i, hilbertSymbol _ (algebraMap (RatFunc k) _ (a i)) x = ε i (finite v) := h3 (finite v)
    exact ⟨Units.mk0 x hx0, hx⟩
  obtain ⟨xi, hxi⟩ : ∃ x : (RatFunc.CompletionAtInfty k)ˣ,
      ∀ i, hilbertSymbol _ (algebraMap (RatFunc k) _ (a i)) (x : RatFunc.CompletionAtInfty k) =
        ε i infinite := by
    obtain ⟨x, hx0, hx⟩ : ∃ x : RatFunc.CompletionAtInfty k, x ≠ 0 ∧
        ∀ i, hilbertSymbol _ (algebraMap (RatFunc k) _ (a i)) x = ε i infinite := h3 infinite
    exact ⟨Units.mk0 x hx0, hx⟩
  choose xf hxf using hxf
  set ω : GSq k S' := (fun v => QuotientGroup.mk (xf v.1), QuotientGroup.mk xi) with hω
  -- the subgroup `Q` of classes with trivial symbols against all `a i`
  let Q : Subgroup (GSq k S') :=
    { carrier := {g | (∀ i (v : S'), hilbCl _ ((locMapS S' (aU i)).1 v) (g.1 v) = 1) ∧
        ∀ i, hilbCl _ ((locMapS S' (aU i)).2) g.2 = 1}
      one_mem' := ⟨fun i v => PresNF.hilbCl_one_right _ _, fun i => PresNF.hilbCl_one_right _ _⟩
      mul_mem' := fun {g h} hg hh => ⟨fun i v => by
          show hilbCl _ _ (g.1 v * h.1 v) = 1
          rw [hilbCl_symm, (oddFin v.1).hilbCl_mul, hilbCl_symm, hg.1 i v, hilbCl_symm, hh.1 i v, one_mul],
        fun i => by
          show hilbCl _ _ (g.2 * h.2) = 1
          rw [hilbCl_symm, (oddInf (k := k)).hilbCl_mul, hilbCl_symm, hg.2 i, hilbCl_symm, hh.2 i,
            one_mul]⟩
      inv_mem' := fun {g} hg => ⟨fun i v => by
          show hilbCl _ _ (g.1 v)⁻¹ = 1
          rw [PresNF.sqCl_inv]; exact hg.1 i v,
        fun i => by
          show hilbCl _ _ (g.2)⁻¹ = 1
          rw [PresNF.sqCl_inv]; exact hg.2 i⟩ }
  -- the pairing of `[a i]` with the target is `∏_v ε i v = 1`
  have hBa : ∀ i, BSq S' (locMapS S' (aU i)) ω = 1 := by
    intro i
    have e1 : ∀ v : S', hilbCl _ ((locMapS S' (aU i)).1 v) (ω.1 v) = ε i (finite v.1) := fun v =>
      hxf v.1 i
    have e2 : hilbCl _ ((locMapS S' (aU i)).2) ω.2 = ε i infinite := hxi i
    unfold BSq
    rw [Finset.prod_congr rfl fun v _ => e1 v, e2]
    exact prod_eps_eq_one S' (ε i) (hε i) (fun v hv => hSS' (hεS i v hv)) (h2 i)
  -- the obstruction vanishes
  have hobs : ∀ y ∈ LamSq S', (∀ q ∈ Q, BSq S' q y = 1) → BSq S' y ω = 1 := by
    intro y hy hyQ
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hy
    -- (a) `u'` is a square at the added primes
    have hsqR : ∀ p ∈ R, IsSquare (algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) (u' : RatFunc k)) := by
      intro p hpR
      have hpS' : p ∈ S' := Finset.mem_union_right _ hpR
      by_contra hns
      have hc : (locMapS S' u').1 ⟨p, hpS'⟩ ≠ 1 := fun h => hns ((mk_eq_one_iff_isSquare _ _).mp h)
      obtain ⟨g, hg⟩ := (oddFin p).hilbCl_nondeg _ hc
      set q : GSq k S' :=
        (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion (RatFunc k))) ⟨p, hpS'⟩ g, 1) with hq
      have hqQ : q ∈ Q := by
        refine ⟨fun i v => ?_, fun i => PresNF.hilbCl_one_right _ _⟩
        by_cases hv : v = ⟨p, hpS'⟩
        · subst hv
          have h1 : (locMapS S' (aU i)).1 ⟨p, hpS'⟩ = 1 :=
            (mk_eq_one_iff_isSquare _ _).mpr ((hRS p hpR).2 i)
          rw [h1]; exact hilbCl_one_left _ _
        · show hilbCl _ _ (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion (RatFunc k)))
            ⟨p, hpS'⟩ g v) = 1
          rw [Pi.mulSingle_eq_of_ne hv]; exact PresNF.hilbCl_one_right _ _
      have hBq : BSq S' q (locMapS S' u') = hilbCl _ g ((locMapS S' u').1 ⟨p, hpS'⟩) := by
        unfold BSq
        have e2 : ∏ v : S', hilbCl _ (q.1 v) ((locMapS S' u').1 v) =
            hilbCl _ g ((locMapS S' u').1 ⟨p, hpS'⟩) := by
          rw [Finset.prod_eq_single ⟨p, hpS'⟩ (fun v' _ hv' => by
            show hilbCl _ (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion (RatFunc k)))
              ⟨p, hpS'⟩ g v') _ = 1
            rw [Pi.mulSingle_eq_of_ne hv', hilbCl_one_left]) (by simp)]
          show hilbCl _ (Pi.mulSingle (M := fun v : S' => SqCl (v.1.adicCompletion (RatFunc k)))
            ⟨p, hpS'⟩ g ⟨p, hpS'⟩) _ = _
          rw [Pi.mulSingle_eq_same]
        rw [e2]
        show _ * hilbCl _ 1 _ = _
        rw [hilbCl_one_left, mul_one]
      have := hyQ q hqQ
      rw [hBq, hg] at this
      norm_num at this
    -- (b) up to a square, `u'` is an `S`-unit
    have heven : ∀ q ∉ S, ∃ g : ℤᵐ⁰, q.valuation (RatFunc k) (u' : RatFunc k) = g * g := by
      intro q hq
      by_cases hqR : q ∈ R
      · exact FF.valuation_isSquare_of_isSquare q _ (hsqR q hqR)
      · have hqS' : q ∉ S' := by rw [hS'def, Finset.mem_union]; tauto
        exact ⟨1, by rw [hu' q hqS', one_mul]⟩
    obtain ⟨d₀, hd₀, hd₁, z, hz0, hdz⟩ := exists_poly_mul_sq S _ u'.ne_zero heven
    have hd₀K : algebraMap k[X] (RatFunc k) d₀ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hd₀
    set u'' : (RatFunc k)ˣ := Units.mk0 _ hd₀K with hu''def
    have hu'' : u'' ∈ SUnitS k S := fun v hv => by
      simp only [hu''def, Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap]
      exact hd₁ v hv
    -- (c) compare with the chosen lift `u₀` of its class
    set d : LamSq S := ⟨locMapS S u'', Subgroup.mem_map_of_mem _ hu''⟩ with hd
    set u₀ := liftU d with hu₀
    have hsq0 : IsSquare (((u'' * u₀⁻¹ : (RatFunc k)ˣ)) : RatFunc k) := by
      apply isSquare_of_locMapS_eq_one hXS ((SUnitS k S).mul_mem hu'' ((SUnitS k S).inv_mem (liftU_mem d)))
      rw [map_mul, map_inv, locMapS_liftU]; exact mul_inv_cancel (G := GSq k S) _
    obtain ⟨r, hr⟩ := hsq0
    have hr0 : r ≠ 0 := by
      rintro rfl; simp at hr
    have hu₀eq : ((u₀ : (RatFunc k)ˣ) : RatFunc k) = (u' : RatFunc k) / (z * r) ^ 2 := by
      have e2 : (u'' : RatFunc k) = r * r * (u₀ : RatFunc k) := by
        have : (u'' : RatFunc k) * ((u₀ : (RatFunc k)ˣ) : RatFunc k)⁻¹ = r * r := by simpa using hr
        field_simp at this ⊢
        linear_combination this
      have e1 : (u' : RatFunc k) = (u'' : RatFunc k) * z ^ 2 := by rw [hdz, hu''def, Units.val_mk0]
      rw [e1, e2]; field_simp
    -- (d) `u₀` lies in `⟨a_i⟩ k(t)^{×2}` by the choice of `R`
    obtain ⟨t, ht⟩ : ∃ t : Finset ι, IsSquare (((u₀ : (RatFunc k)ˣ) : RatFunc k) * ∏ i ∈ t, a i) := by
      by_contra hbad
      push Not at hbad
      obtain ⟨p, hpR, hpns⟩ := hRbad d hbad
      apply hpns
      obtain ⟨m, hm⟩ := hsqR p hpR
      refine ⟨m / algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) (z * r), ?_⟩
      have hz0' : algebraMap (RatFunc k) (p.adicCompletion (RatFunc k)) (z * r) ≠ 0 :=
        (_root_.map_ne_zero _).mpr (mul_ne_zero hz0 hr0)
      rw [← hu₀, hu₀eq, map_div₀, map_pow, hm]
      field_simp
    -- (e) so `[u'] = ∏_{i ∈ t} [a_i]`, which pairs trivially with the target
    have hsq' : IsSquare (((u' * ∏ i ∈ t, aU i : (RatFunc k)ˣ)) : RatFunc k) := by
      obtain ⟨m, hm⟩ := ht
      refine ⟨z * r * m, ?_⟩
      have e : ((u' * ∏ i ∈ t, aU i : (RatFunc k)ˣ) : RatFunc k) =
          (z * r) ^ 2 * (((u₀ : (RatFunc k)ˣ) : RatFunc k) * ∏ i ∈ t, a i) := by
        rw [Units.val_mul, Units.coe_prod]
        simp only [haU, Units.val_mk0]
        rw [hu₀eq]
        field_simp
      rw [e, hm]; ring
    have hloc := locMapS_eq_one_of_isSquare S' _ hsq'
    rw [map_mul, map_prod] at hloc
    have hy' : locMapS S' u' = ∏ i ∈ t, locMapS S' (aU i) := by
      rw [← GSq_inv S' (∏ i ∈ t, locMapS S' (aU i))]
      exact eq_inv_of_mul_eq_one_left (G := GSq k S') hloc
    rw [hy', BSq_prod, Finset.prod_eq_one fun i _ => hBa i]
  -- solve modulo the Lagrangian `Λ_{S'}`
  have hiso : ∀ x ∈ LamSq S', ∀ y ∈ LamSq S', BSq S' x y = 1 := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact BSq_sUnit hR S' hb hc
  obtain ⟨q, hqQ, hmem⟩ := (pairingSq S').exists_mul_mem_of_orth (LamSq S') Q hiso
    (card_lamSq hR hXS') ω hobs
  obtain ⟨x, hxS', hxloc⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(x : RatFunc k), x.ne_zero, fun i v => ?_⟩
  cases v with
  | infinite =>
    have h := congrArg Prod.snd hxloc
    have : infinite.hilbert (a i) (x : RatFunc k) =
        hilbCl _ ((locMapS S' (aU i)).2) ((locMapS S' x).2) := rfl
    rw [this, h]
    show hilbCl _ _ (ω.2 * q.2) = _
    rw [hilbCl_symm, (oddInf (k := k)).hilbCl_mul, hilbCl_symm, hilbCl_symm _ q.2, hqQ.2 i, mul_one]
    exact hxi i
  | finite v =>
    by_cases hv : v ∈ S'
    · have h := congrFun (congrArg Prod.fst hxloc) ⟨v, hv⟩
      have : (finite v).hilbert (a i) (x : RatFunc k) =
          hilbCl _ ((locMapS S' (aU i)).1 ⟨v, hv⟩) ((locMapS S' x).1 ⟨v, hv⟩) := rfl
      rw [this, h]
      show hilbCl _ _ (ω.1 ⟨v, hv⟩ * q.1 ⟨v, hv⟩) = _
      rw [hilbCl_symm, (oddFin v).hilbCl_mul, hilbCl_symm, hilbCl_symm _ (q.1 ⟨v, hv⟩), hqQ.1 i ⟨v, hv⟩,
        mul_one]
      exact hxf v i
    · have hvS : v ∉ S := fun h => hv (hSS' h)
      rw [hilbert_units_fin v _ _ (haS i v hvS) (hxS' v hv)]
      exact ((hε i _).resolve_right fun h => hvS (hεS i v h)).symm

end Main

/-- **Elements of $\mathbb{F}_q(t)$ with prescribed local Hilbert symbols** ($q$ odd), conditional on Hilbert reciprocity
(`HilbertReciprocity k`, proved as `RatFuncPlace.hilbertReciprocity`) and the named input `PrescribedSquarePrimes k`:
the named input `PrescribedHilbert k` (O'Meara 71:19 for $\mathbb{F}_q(t)$). See `prescribedHilbert_of_inputs'`. -/
@[kb "serre1973" "Ch. III §2.2, Thm. 4 (function field case) [unverified]; omeara1963 §71D, 71:19, p. 203 (F = F_q(t))"]
theorem prescribedHilbert_of_inputs [Fintype k] (hk : ringChar k ≠ 2) (hR : HilbertReciprocity k)
    (hD : PrescribedSquarePrimes k) : PrescribedHilbert k :=
  have : Fact (ringChar k ≠ 2) := ⟨hk⟩
  prescribedHilbert_of_inputs' hR hD

/-- **Elements of $\mathbb{F}_q(t)$ with prescribed local Hilbert symbols** ($q$ odd; O'Meara 71:19 for
$\mathbb{F}_q(t)$), conditional only on the named input `PrescribedSquarePrimes k`: Hilbert reciprocity is proved
(`RatFuncPlace.hilbertReciprocity`). -/
@[kb "serre1973" "Ch. III §2.2, Thm. 4 (function field case) [unverified]; omeara1963 §71D, 71:19, p. 203 (F = F_q(t))"]
theorem prescribedHilbert_of_squarePrimes [Fintype k] (hk : ringChar k ≠ 2) (hD : PrescribedSquarePrimes k) :
    PrescribedHilbert k :=
  prescribedHilbert_of_inputs hk (hilbertReciprocity hk) hD

end RatFuncPlace

end QuadFormsKB
