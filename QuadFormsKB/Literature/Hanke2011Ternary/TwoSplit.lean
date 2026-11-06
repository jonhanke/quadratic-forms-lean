import QuadFormsKB.Literature.Hanke2011Ternary.GlobalNFSign

/-!
# Hanke 2011 (ternary masses), Theorem 7.1: the hypothesis that $2$ splits completely

J. Hanke, arXiv:1109.1054 (`hanke2011ternary`), abstract and Theorem 7.1, p. 25.  We define "$2$ splits completely in $F$"
as: the number of primes of $\mathcal O_F$ above $2$ is $[F:\mathbb Q]$, and show (fundamental identity
$\sum_{\mathfrak p\mid 2} e_{\mathfrak p}f_{\mathfrak p} = [F:\mathbb Q]$) that then every such prime has residue field
$\mathbb F_2$, i.e. $N\mathfrak p = 2$.
-/

namespace QuadFormsKB.Hanke2011Ternary.NF

open IsDedekindDomain NumberField

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-- **$2$ splits completely in $F$**: there are exactly $[F:\mathbb Q]$ primes of $\mathcal O_F$ above $2$, i.e.
$\#\{\mathfrak p \subset \mathcal O_F \text{ prime} : 2 \in \mathfrak p\} = [F:\mathbb Q]$. By the fundamental identity
$\sum_{\mathfrak p \mid 2} e_{\mathfrak p} f_{\mathfrak p} = [F:\mathbb Q]$ this is equivalent to
$e_{\mathfrak p} = f_{\mathfrak p} = 1$ for every $\mathfrak p \mid 2$. -/
@[kb "hanke2011ternary" "abstract, p. 1; Thm. 7.1, p. 25 (2 splits completely in F)"]
def TwoSplitsCompletely (F : Type) [Field F] [NumberField F] : Prop := numDyadic F = Module.finrank ℚ F

omit [NumberField F] in
/-- A prime $\mathfrak p$ of $\mathcal O_F$ lies over $2\mathbb Z$ iff $2 \in \mathfrak p$. -/
theorem liesOver_two_iff (P : Ideal (𝓞 F)) [P.IsPrime] :
    P.LiesOver (Ideal.span {(2 : ℤ)}) ↔ (2 : 𝓞 F) ∈ P := by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime := (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  have hm : (Ideal.span {(2 : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal hp (by simp)
  rw [Ideal.liesOver_iff]
  constructor
  · intro h
    have h2 : (2 : ℤ) ∈ Ideal.span {(2 : ℤ)} := Ideal.mem_span_singleton_self 2
    rw [h, Ideal.mem_comap] at h2
    simpa using h2
  · intro h
    refine hm.eq_of_le (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top ‹_›)) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using h

/-- The primes of $\mathcal O_F$ above $2$ are in bijection with the primes of $\mathcal O_F$ lying over $2\mathbb Z$. -/
def dyadicEquivPrimesOver (F : Type) [Field F] [NumberField F] :
    {v : HeightOneSpectrum (𝓞 F) // (2 : 𝓞 F) ∈ v.asIdeal} ≃
      (Ideal.span {(2 : ℤ)}).primesOver (𝓞 F) :=
  Equiv.ofBijective
    (fun v => ⟨v.1.asIdeal, v.1.isPrime, (liesOver_two_iff (F := F) v.1.asIdeal).2 v.2⟩)
    ⟨fun a b h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)), fun Q => by
      have hQ : Q.1.IsPrime := Q.2.1
      have : Q.1.LiesOver (Ideal.span {(2 : ℤ)}) := Q.2.2
      have hne : Q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (by simp) Q.2
      exact ⟨⟨⟨Q.1, hQ, hne⟩, (liesOver_two_iff (F := F) Q.1).1 Q.2.2⟩, rfl⟩⟩

/-- **Fundamental identity for $2$** ($e_{\mathfrak p} = f_{\mathfrak p} = 1$): if $2$ splits completely in $F$, every
prime $\mathfrak p \mid 2$ of $\mathcal O_F$ has residue degree $f_{\mathfrak p} = 1$, hence norm $N\mathfrak p = 2$. -/
theorem TwoSplitsCompletely.qv_eq_two (h : TwoSplitsCompletely F) (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∈ v.asIdeal) : qv v = 2 := by
  set p : Ideal ℤ := Ideal.span {(2 : ℤ)} with hpdef
  have hp : p.IsPrime := (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  let e := dyadicEquivPrimesOver F
  have hfin : Finite {v : HeightOneSpectrum (𝓞 F) // (2 : 𝓞 F) ∈ v.asIdeal} :=
    (finite_dyadic (F := F)).to_subtype
  have : Finite (p.primesOver (𝓞 F)) := Finite.of_equiv _ e
  let _ : Fintype (p.primesOver (𝓞 F)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : numDyadic F = Nat.card {v : HeightOneSpectrum (𝓞 F) // (2 : 𝓞 F) ∈ v.asIdeal} := by
    rw [numDyadic, ← Set.ncard_eq_toFinset_card _ finite_dyadic, ← Nat.card_coe_set_eq]
    rfl
  have hcard : Fintype.card (p.primesOver (𝓞 F)) = Module.finrank ℚ F := by
    rw [← h, h1, Nat.card_congr e, Nat.card_eq_fintype_card]
  have hge : ∀ q : p.primesOver (𝓞 F), 1 ≤ q.1.ramificationIdx ℤ *
      q.1.inertiaDeg ℤ := fun q => by
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver p := q.2.2
    exact Nat.mul_pos (q.1.ramificationIdx_pos ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
  have hone : ∀ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ *
      q.1.inertiaDeg ℤ = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hq⟩ := hcon
    have hlt := Finset.sum_lt_sum (s := Finset.univ) (f := fun _ : p.primesOver (𝓞 F) => 1)
      (g := fun q => q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ)
      (fun i _ => hge i) ⟨q, Finset.mem_univ _, lt_of_le_of_ne (hge q) (Ne.symm hq)⟩
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hlt
    omega
  let Q : p.primesOver (𝓞 F) := e ⟨v, hv⟩
  have hf : Q.1.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left (hone Q)
  have : Q.1.IsPrime := Q.2.1
  have : Q.1.LiesOver p := Q.2.2
  have hn := Ideal.natAbs_pow_inertiaDeg (R := 𝓞 F) 2 Q.1
  rw [hf] at hn
  exact (by simpa using hn.symm : Ideal.absNorm Q.1 = 2)

/-- If $2$ splits completely in $F$, the number of primes above $2$ is $[F:\mathbb Q]$ (the definition). -/
theorem TwoSplitsCompletely.numDyadic_eq (h : TwoSplitsCompletely F) : numDyadic F = Module.finrank ℚ F := h

end

#print axioms TwoSplitsCompletely.qv_eq_two
#print axioms TwoSplitsCompletely.numDyadic_eq

end QuadFormsKB.Hanke2011Ternary.NF
