/-
# The places of the rational function field $k(t)$ and squares local–global

For a field $k$, the **places** of the rational function field $k(t)$ (trivial on $k$) are

* the finite places: the monic irreducible polynomials $P \in k[t]$, i.e. the height-one primes of
  $k[t]$ (Mathlib's `IsDedekindDomain.HeightOneSpectrum k[X]`), with completion $k(t)_P$
  (`adicCompletion`, isomorphic to the Laurent series $\kappa_P((P))$ over $\kappa_P = k[t]/(P)$);
* the place at infinity, with valuation $-\deg$ and completion $k((t^{-1}))$
  (Mathlib's `RatFunc.CompletionAtInfty k`).

This is the classical list of places of $k(t)$ trivial on $k$ (Mathlib's
`RatFunc.valuation_isEquiv_infty_or_adic` in `Mathlib/NumberTheory/RatFunc/Ostrowski.lean` proves that
every nontrivial valuation of $k(t)$ trivial on $k$ is equivalent to one of these). For a finite field
$k = \mathbb{F}_q$ this is the simplest global function field, the analogue of $\mathbb{Q}$; `RatFuncPlace`
plays the role of `RatPlace` (for $\mathbb{Q}$) and `NFPlace` (for a number field).

The first local–global theorem, **squares are local–global** (`RatFuncPlace.isSquare_iff_everywhere`),
holds for every field $k$ and has an elementary proof (no zeta function, unlike the number field
proof `SqLG.isSquare_iff_everywhere`): if $a$ is a square at every finite place, every valuation of $a$
is even, so $a = c e^2$ with $c \in k^\times$; and $c$ is a square at the place $t = 0$, whose residue
field is $k$, so $c$ is a square in $k$.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.Defs.Hilbert
import QuadFormsKB.FunctionField.DedekindLocal

open IsDedekindDomain Polynomial WithZero

namespace QuadFormsKB

/-- **The places of the rational function field $k(t)$** (trivial on $k$): a finite place, i.e. a
height-one prime $(P)$ of $k[t]$ with $P$ irreducible, or the place $\infty$ at infinity (valuation
$-\deg$). -/
@[kb "rosen2002" "Ch. 5, Thm. 5.? (places of k(T)) [unverified]; weil1967 Ch. III §1 [unverified]"]
inductive RatFuncPlace (k : Type) [Field k]
  | finite (v : HeightOneSpectrum k[X])
  | infinite

namespace RatFuncPlace

variable {k : Type} [Field k]

open scoped Classical in
/-- **A property at the place $v$ of $k(t)$:** `atPlace P v` means $P$ holds over the completion
$k(t)_v$, which is $k(t)_P$ (`adicCompletion`) at a finite place and $k((t^{-1}))$
(`RatFunc.CompletionAtInfty k`) at infinity. $P$ is a predicate on fields $K$ with a
$k(t)$-algebra structure. -/
noncomputable def atPlace (P : (K : Type) → [Field K] → [Algebra (RatFunc k) K] → Prop) :
    RatFuncPlace k → Prop
  | finite v => P (v.adicCompletion (RatFunc k))
  | infinite => P (RatFunc.CompletionAtInfty k)

/-- **A property everywhere locally:** $P$ holds over every completion of $k(t)$, at all finite places
and at infinity. -/
noncomputable def Everywhere (P : (K : Type) → [Field K] → [Algebra (RatFunc k) K] → Prop) : Prop :=
  ∀ v : RatFuncPlace k, atPlace P v

open scoped Classical in
/-- **The local Hilbert symbol $(a,b)_v$** of $a, b \in k(t)$ at the place $v$: the Hilbert symbol over
the completion $k(t)_v$, with $a, b$ viewed in $k(t)_v$. -/
@[kb "omeara1963" "§63B, p. 164 (Hilbert symbol)"]
noncomputable def hilbert : RatFuncPlace k → RatFunc k → RatFunc k → ℤ
  | finite v, a, b => hilbertSymbol (v.adicCompletion (RatFunc k))
      (algebraMap (RatFunc k) _ a) (algebraMap (RatFunc k) _ b)
  | infinite, a, b => hilbertSymbol (RatFunc.CompletionAtInfty k)
      (algebraMap (RatFunc k) _ a) (algebraMap (RatFunc k) _ b)

/-- **The finite place of an irreducible polynomial:** for $P \in k[t]$ irreducible, the height-one
prime $(P)$ of $k[t]$. -/
noncomputable def ofIrreducible (P : k[X]) (hP : Irreducible P) : HeightOneSpectrum k[X] where
  asIdeal := Ideal.span {P}
  isPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hP)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hP.ne_zero

@[simp] theorem ofIrreducible_asIdeal (P : k[X]) (hP : Irreducible P) :
    (ofIrreducible P hP).asIdeal = Ideal.span {P} := rfl

/-- **Squares are local–global over $k(t)$** (any field $k$): $a \in k(t)$ is a square iff it is a
square in every completion $k(t)_v$. Only the finite places are needed for the hard direction
(`isSquare_of_finite`).

*Proof.* See `isSquare_of_finite`. -/
@[kb "omeara1963" "§65, 65:15 (squares, global fields) [unverified]; lam2005 Ch. VI §3 [unverified]"]
theorem isSquare_iff_everywhere (a : RatFunc k) :
    IsSquare a ↔ Everywhere (k := k) fun K _ _ => IsSquare (algebraMap (RatFunc k) K a) := by
  constructor
  · rintro ⟨r, rfl⟩ v
    cases v <;> exact ⟨algebraMap _ _ r, by simp⟩
  · intro h
    exact isSquare_of_finite a (fun v => h (.finite v))
where
  /-- **Squares local–global over $k(t)$, finite places only:** if $a \in k(t)$ is a square in
  $k(t)_P$ for every irreducible $P \in k[t]$, then $a$ is a square in $k(t)$.

  *Proof.* Write $a = p/q$ and $pq = e^2 d$ with $d$ squarefree (`exists_sq_mul_squarefree`). If $d$
  had an irreducible factor $P$, then $v_P(d) = 1$ (`FF.intValuation_eq_exp_neg_one`), while
  $v_P(pq) = v_P(a q^2)$ is even (`FF.valuation_isSquare_of_isSquare`): impossible
  (`FF.mul_self_ne_exp_neg_one`). So $d = c \in k^\times$ and $a = c (e/q)^2$. Then $c$ is a square in
  $k(t)_{(t)}$, hence $c \equiv r^2 \pmod t$ for some $r \in k[t]$ (`FF.exists_sq_mod_of_isSquare`), i.e.
  $c = r(0)^2$. -/
  isSquare_of_finite (a : RatFunc k) (h : ∀ v : HeightOneSpectrum k[X],
      IsSquare (algebraMap (RatFunc k) (v.adicCompletion (RatFunc k)) a)) : IsSquare a := by
    classical
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    set p := a.num
    set q := a.denom
    have hq : q ≠ 0 := RatFunc.denom_ne_zero a
    have hp : p ≠ 0 := by simpa [p] using ha
    have hpq : algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q = a :=
      RatFunc.num_div_denom a
    have hqK : algebraMap k[X] (RatFunc k) q ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact hq
    obtain ⟨e, d, hed, hd⟩ := exists_sq_mul_squarefree (p * q)
    have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hed; exact mul_ne_zero hp hq hed.symm
    have he0 : e ≠ 0 := by
      rintro rfl; rw [zero_pow two_ne_zero, zero_mul] at hed; exact mul_ne_zero hp hq hed.symm
    -- p q is a local square everywhere
    have hloc : ∀ v : HeightOneSpectrum k[X], IsSquare (algebraMap (RatFunc k)
        (v.adicCompletion (RatFunc k)) (algebraMap k[X] (RatFunc k) (p * q))) := by
      intro v
      obtain ⟨s, hs⟩ := h v
      refine ⟨s * algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) q), ?_⟩
      have : algebraMap k[X] (RatFunc k) (p * q) = a * algebraMap k[X] (RatFunc k) q ^ 2 := by
        rw [← hpq, map_mul]; field_simp
      rw [this, map_mul, hs, map_pow]; ring
    have hunit : IsUnit d := by
      by_contra hnu
      obtain ⟨P, hP, hPd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd0
      set v := RatFuncPlace.ofIrreducible P hP
      have h1 : d ∈ v.asIdeal := by simpa [v] using Ideal.mem_span_singleton.mpr hPd
      have h2 : d ∉ v.asIdeal ^ 2 := by
        intro hmem
        rw [ofIrreducible_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
        exact hP.not_isUnit (hd P (by rw [← sq]; exact hmem))
      have hv1 := FF.intValuation_eq_exp_neg_one v d h1 h2
      obtain ⟨w, hw⟩ := FF.valuation_isSquare_of_isSquare v _ (hloc v)
      rw [HeightOneSpectrum.valuation_of_algebraMap, ← hed, map_mul, map_pow, hv1] at hw
      have hve : v.intValuation e ≠ 0 := v.intValuation_ne_zero e he0
      apply FF.mul_self_ne_exp_neg_one (w / v.intValuation e)
      field_simp
      rw [sq, ← hw]
    obtain ⟨c, hc, rfl⟩ : ∃ c : k, c ≠ 0 ∧ C c = d := by
      obtain ⟨c, hcu, hcd⟩ := Polynomial.isUnit_iff.mp hunit
      exact ⟨c, hcu.ne_zero, hcd⟩
    have ha' : a = algebraMap k[X] (RatFunc k) (C c) *
        (algebraMap k[X] (RatFunc k) e / algebraMap k[X] (RatFunc k) q) ^ 2 := by
      rw [← hpq]
      have : algebraMap k[X] (RatFunc k) p * algebraMap k[X] (RatFunc k) q =
          algebraMap k[X] (RatFunc k) e ^ 2 * algebraMap k[X] (RatFunc k) (C c) := by
        rw [← map_mul, ← hed, map_mul, map_pow]
      field_simp
      linear_combination this
    have heK : algebraMap k[X] (RatFunc k) e ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]; exact he0
    -- c is a square at the place t = 0
    set v0 := RatFuncPlace.ofIrreducible (X : k[X]) Polynomial.irreducible_X
    have hc0 : IsSquare (algebraMap (RatFunc k) (v0.adicCompletion (RatFunc k))
        (algebraMap k[X] (RatFunc k) (C c))) := by
      obtain ⟨s, hs⟩ := h v0
      refine ⟨s * algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) q /
        algebraMap k[X] (RatFunc k) e), ?_⟩
      have : algebraMap k[X] (RatFunc k) (C c) = a *
          (algebraMap k[X] (RatFunc k) q / algebraMap k[X] (RatFunc k) e) ^ 2 := by
        rw [ha']; field_simp
      rw [this, map_mul, hs, map_pow]; ring
    obtain ⟨r, hr⟩ := FF.exists_sq_mod_of_isSquare v0 (C c) hc0
    rw [ofIrreducible_asIdeal, Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
      Polynomial.coeff_zero_eq_eval_zero] at hr
    simp only [eval_sub, eval_C, eval_pow] at hr
    refine ⟨algebraMap k[X] (RatFunc k) (C (r.eval 0)) *
      (algebraMap k[X] (RatFunc k) e / algebraMap k[X] (RatFunc k) q), ?_⟩
    rw [ha', show c = r.eval 0 ^ 2 by linear_combination hr]
    simp only [map_pow]
    ring

end RatFuncPlace

end QuadFormsKB
