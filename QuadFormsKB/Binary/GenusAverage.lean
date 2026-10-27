import QuadFormsKB.Binary.GenusMass

/-!
# The genus average of representation numbers of binary forms

For a fundamental discriminant $D < 0$ with $t$ prime factors, class number $h$, $w = |\mathcal O_{K_D}^\times|$,
$\chi_D$ the Kronecker character, a primitive positive definite form $f$ of discriminant $D$ and $m \ge 1$, the
repo's genus average (`Siegel.genusRepAvg`: $\mathrm{GL}_2(\mathbb{Z})$-classes, weights $1/|\mathrm{Aut}|$, the
library's
convention)
$$r_{\mathcal G}(m) = \mathrm{Mass}(\mathcal G)^{-1}\sum_{[g] \in \mathcal G}\frac{r_g(m)}{|\mathrm{Aut}(g)|}$$
is (`genusRepAvg_binary`)
$$r_{\mathcal G}(m) = \begin{cases} \dfrac{w\,2^{t-1}}{h}\displaystyle\sum_{d \mid m}\chi_D(d) &
\text{if some form in the genus } \mathcal G \text{ of } f \text{ represents } m,\\[2ex] 0 & \text{otherwise,}\end{cases}$$
and for $m$ prime to $D$ the condition is local, on the genus characters of $m$ (`genusRepAvg_binary_coprime`):
$\psi_p(m) = \chi_p(f)$ for all $p \mid D$.

**Proof.** By `repNum_eq`, $r_g(m) = w\,\#\{\mathfrak b : N\mathfrak b = m,\ [\mathfrak b] = [\mathfrak a_g]^{-1}\}$;
with the GL/SL fibre identity (`sum_div_aut_genus`),
$\sum_{[g] \in \mathcal G} r_g(m)/|\mathrm{Aut}(g)| = \tfrac12\#\{\mathfrak b : N\mathfrak b = m,\ [\mathfrak b] \in \mathcal G\}$,
and $\mathrm{Mass}(\mathcal G) = h/(2^{t-1}\cdot 2w)$ (`mass_genus`). The key fact is that **all ideals of norm $m$ lie in
one genus** (`genusHom_eq_of_absNorm_eq`): for $m$ prime to $D$ the genus characters of $[\mathfrak b]$ are $\psi_p(m)$
(`genusHom_mk0_coe`, from `genusChar_norm_eq_formChar`); in general $m = m_0m'$ with $m'$ prime to $D$ and every prime
factor of $m_0$ dividing $D$, there is exactly one ideal $\mathfrak r$ of norm $m_0$ (`card_ideals_absNorm_eq`:
$\sum_{d \mid m_0}\chi_D(d) = 1$), and every ideal of norm $m$ is $\mathfrak r\mathfrak b'$ with $N\mathfrak b' = m'$ (an
injection between sets of equal size $\sum_{d \mid m}\chi_D(d) = \sum_{d \mid m'}\chi_D(d)$). So the ideals counted are
either all ideals of norm $m$, $\sum_{d \mid m}\chi_D(d)$ of them, or none.

Sources: Siegel (1935), the binary case of the mass/representation formula; Zagier, *Zetafunktionen und quadratische
Körper*, §§8, 11 (genus characters and $r_{\mathcal G}$) [unverified locator]; Cox, §3.B, Thm. 3.15 and §7
[unverified locator]; Gauss, *Disq. Arith.* §§229–233 (characters of the represented numbers) [unverified].
-/

open QuadraticAlgebra NumberField
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ} [IsQuadDisc D]

/-! ### The genus of an ideal class, from norms -/

omit [IsQuadDisc D] in
/-- An ideal of nonzero norm is a nonzero divisor. -/
theorem mem_nonZeroDivisors_of_absNorm [IsQuadDisc D] {I : Ideal (QOrder D)} (h : Ideal.absNorm I ≠ 0) :
    I ∈ (Ideal (QOrder D))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (fun h0 => h (by rw [h0]; exact Ideal.absNorm_bot))

/-- **The genus characters of an ideal class are the characters of the norm** ($D < 0$ fundamental): if $\mathfrak b \ne 0$
has norm $m$ and $p \mid D$, $p \nmid m$, then the $p$-component of $\gamma([\mathfrak b])$ is $\psi_p(m)$. (A form $F$ in
$[\mathfrak b]^{-1}$ represents $m$, and $\gamma(x^{-1}) = \gamma(x)$.) -/
theorem genusHom_mk0_coe (hD : D < 0) {𝔟 : Ideal (QOrder D)} (h0 : 𝔟 ∈ (Ideal (QOrder D))⁰) {m : ℕ}
    (hN : Ideal.absNorm 𝔟 = m) (p : D.natAbs.primeFactors) (hpm : ¬ (p.1 : ℤ) ∣ m) :
    (((isFormClassGroupOrder hD).genusHom (ClassGroup.mk0 ⟨𝔟, h0⟩) p : ℤˣ) : ℤ) = genusChar D p m := by
  set C := isFormClassGroupOrder hD
  set x := ClassGroup.mk0 (⟨𝔟, h0⟩ : (Ideal (QOrder D))⁰)
  set F := C.rep x⁻¹
  have hF : idealClass F.toPrim = x⁻¹ := C.cls_rep x⁻¹
  have hc : ClassGroup.mk0 (⟨𝔟, h0⟩ : (Ideal (QOrder D))⁰) = (idealClass F.toPrim)⁻¹ := by rw [hF, inv_inv]
  have hp := Nat.prime_of_mem_primeFactors p.2
  have hpD : (p.1 : ℤ) ∣ D := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors p.2)
  rw [← C.genusHom_inv, ← C.cls_rep x⁻¹, C.genusHom_cls, coe_genusVec F.2.1 F.2.2.1,
    genusChar_norm_eq_formChar hD F.toPrim hN h0 hc hp hpD hpm]
  rfl

/-- **Two ideals of the same norm prime to $D$ lie in the same genus.** -/
theorem genusHom_eq_of_absNorm_eq_coprime (hD : D < 0) {𝔟 𝔠 : Ideal (QOrder D)} (h𝔟 : 𝔟 ∈ (Ideal (QOrder D))⁰)
    (h𝔠 : 𝔠 ∈ (Ideal (QOrder D))⁰) {m : ℕ} (hN𝔟 : Ideal.absNorm 𝔟 = m) (hN𝔠 : Ideal.absNorm 𝔠 = m)
    (hm : Nat.Coprime m D.natAbs) :
    (isFormClassGroupOrder hD).genusHom (ClassGroup.mk0 ⟨𝔟, h𝔟⟩) =
      (isFormClassGroupOrder hD).genusHom (ClassGroup.mk0 ⟨𝔠, h𝔠⟩) := by
  funext p
  have hpm : ¬ (p.1 : ℤ) ∣ m := by
    intro h
    have h1 : p.1 ∣ m := Int.natCast_dvd_natCast.mp h
    have h2 : p.1 ∣ D.natAbs := Nat.dvd_of_mem_primeFactors p.2
    exact (Nat.prime_of_mem_primeFactors p.2).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hm h1 h2)
  exact Units.ext ((genusHom_mk0_coe hD h𝔟 hN𝔟 p hpm).trans (genusHom_mk0_coe hD h𝔠 hN𝔠 p hpm).symm)

/-! ### Ideals of norm $m$: the part at $D$ is unique -/

omit [IsQuadDisc D] in
/-- **Splitting off the part of $m$ at $D$:** $m = m_0 m'$ with $m'$ prime to $D$ and every prime factor of $m_0$
dividing $D$. -/
theorem exists_split_at (N : ℕ) : ∀ m : ℕ, m ≠ 0 → ∃ m₀ m' : ℕ, m = m₀ * m' ∧ Nat.Coprime m' N ∧
    ∀ q : ℕ, q.Prime → q ∣ m₀ → q ∣ N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hc : Nat.Coprime m N
    · exact ⟨1, m, (one_mul m).symm, hc, fun q hq h => absurd (Nat.le_of_dvd one_pos h) (by
        have := hq.two_le; omega)⟩
    · obtain ⟨q, hq, hqm, hqN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      obtain ⟨k, rfl⟩ := hqm
      have hk : k ≠ 0 := by rintro rfl; simp at hm
      have hlt : k < q * k := by
        have := hq.two_le
        calc k = 1 * k := (one_mul k).symm
          _ < q * k := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hk)
      obtain ⟨m₀, m', rfl, hc', hq'⟩ := ih k hlt hk
      refine ⟨q * m₀, m', by ring, hc', fun r hr h => ?_⟩
      rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · rwa [(Nat.prime_dvd_prime_iff_eq hr hq).mp h]
      · exact hq' r hr h

/-- **The number of ideals of norm $n$ of $\mathbb{Z}[\omega]$** is $\sum_{d \mid n}\chi_D(d)$ (the
`card_ideals_absNorm_eq_int`, transported by `card_ideals_order_eq`). -/
theorem card_ideals_order_absNorm_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = n} : ℤ) =
      ∑ d ∈ n.divisors, kronZ D (d : ZMod D.natAbs) := by
  rw [card_ideals_order_eq, card_ideals_absNorm_eq_int hn]

/-- $\chi_D(d) = 0$ unless $d$ is prime to $D$. -/
theorem kronZ_eq_zero_of_not_coprime {d : ℕ} (hd : ¬ Nat.Coprime d D.natAbs) :
    kronZ D (d : ZMod D.natAbs) = 0 :=
  kronZ_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

/-- If every prime factor of $m_0$ divides $D$: $\sum_{d \mid m_0}\chi_D(d) = 1$ (only $d = 1$ is prime to $D$). -/
theorem sum_kronZ_of_dvd_D {m₀ : ℕ} (hm₀ : m₀ ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ m₀ → q ∣ D.natAbs) :
    ∑ d ∈ m₀.divisors, kronZ D (d : ZMod D.natAbs) = 1 := by
  rw [Finset.sum_eq_single 1 (fun d hd hd1 => ?_) (fun h1 => absurd (Nat.one_mem_divisors.mpr hm₀) h1),
    Nat.cast_one, kronZ_one]
  apply kronZ_eq_zero_of_not_coprime
  intro hc
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd1
  have hqm : q ∣ m₀ := hqd.trans (Nat.dvd_of_mem_divisors hd)
  exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hqd (h q hq hqm))

/-- If $m = m_0m'$ with $m'$ prime to $D$ and every prime factor of $m_0$ dividing $D$:
$\sum_{d \mid m}\chi_D(d) = \sum_{d \mid m'}\chi_D(d)$. -/
theorem sum_kronZ_split {m₀ m' : ℕ} (hm : m₀ * m' ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ m₀ → q ∣ D.natAbs) :
    ∑ d ∈ (m₀ * m').divisors, kronZ D (d : ZMod D.natAbs) = ∑ d ∈ m'.divisors, kronZ D (d : ZMod D.natAbs) := by
  refine (Finset.sum_subset (Nat.divisors_subset_of_dvd hm (dvd_mul_left _ _)) fun d hd hd' => ?_).symm
  apply kronZ_eq_zero_of_not_coprime
  intro hc
  apply hd'
  have hm' : m' ≠ 0 := by rintro rfl; simp at hm
  refine Nat.mem_divisors.mpr ⟨?_, hm'⟩
  have hcm : Nat.Coprime d m₀ := by
    refine Nat.coprime_of_dvd fun q hq hqd hqm => ?_
    exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hqd (h q hq hqm))
  exact hcm.dvd_of_dvd_mul_left (Nat.dvd_of_mem_divisors hd)

/-- **Every ideal of norm $m = m_0m'$ is $\mathfrak r\,\mathfrak b'$** with $N\mathfrak r = m_0$ and $N\mathfrak b' = m'$, where
$m'$ is prime to $D$ and every prime factor of $m_0$ divides $D$; and $\mathfrak r$ is the unique ideal of norm $m_0$.
(Multiplication $\{N = m_0\} \times \{N = m'\} \to \{N = m\}$ is injective, and both sides have
$\sum_{d \mid m}\chi_D(d)$ elements.) -/
theorem exists_mul_of_absNorm {m₀ m' : ℕ} (hm : m₀ * m' ≠ 0) (hc : Nat.Coprime m' D.natAbs)
    (h : ∀ q : ℕ, q.Prime → q ∣ m₀ → q ∣ D.natAbs) :
    (∀ I J : Ideal (QOrder D), Ideal.absNorm I = m₀ → Ideal.absNorm J = m₀ → I = J) ∧
    ∀ 𝔟 : Ideal (QOrder D), Ideal.absNorm 𝔟 = m₀ * m' →
      ∃ 𝔯 𝔟' : Ideal (QOrder D), Ideal.absNorm 𝔯 = m₀ ∧ Ideal.absNorm 𝔟' = m' ∧ 𝔟 = 𝔯 * 𝔟' := by
  have hm₀ : m₀ ≠ 0 := by rintro rfl; simp at hm
  have hm' : m' ≠ 0 := by rintro rfl; simp at hm
  have h1 : Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m₀} = 1 := by
    have := card_ideals_order_absNorm_eq (D := D) hm₀
    rw [sum_kronZ_of_dvd_D hm₀ h] at this
    exact_mod_cast this
  obtain ⟨hsub, ⟨𝔯₀⟩⟩ := Nat.card_eq_one_iff_unique.mp h1
  have huniq : ∀ I J : Ideal (QOrder D), Ideal.absNorm I = m₀ → Ideal.absNorm J = m₀ → I = J :=
    fun I J hI hJ => congrArg Subtype.val (hsub.elim ⟨I, hI⟩ ⟨J, hJ⟩)
  refine ⟨huniq, fun 𝔟 h𝔟 => ?_⟩
  set X := {I : Ideal (QOrder D) // Ideal.absNorm I = m₀} × {I : Ideal (QOrder D) // Ideal.absNorm I = m'}
  set Y := {I : Ideal (QOrder D) // Ideal.absNorm I = m₀ * m'}
  let P : X → Y := fun p => ⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩
  have hfin : Finite Y := (Ideal.finite_setOfPred_absNorm_eq (m₀ * m')).to_subtype
  have hinj : Function.Injective P := by
    rintro ⟨I, J⟩ ⟨I', J'⟩ hP
    have hII : I = I' := Subtype.ext (huniq _ _ I.2 I'.2)
    subst hII
    have hI0 : I.1 ≠ ⊥ := fun h0 => hm₀ (by rw [← I.2, h0]; exact Ideal.absNorm_bot)
    have : I.1 * J.1 = I.1 * J'.1 := congrArg Subtype.val hP
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ hI0 this))
  have hcard : Nat.card Y ≤ Nat.card X := by
    rw [Nat.card_prod, h1, one_mul]
    have e1 := card_ideals_order_absNorm_eq (D := D) hm
    have e2 := card_ideals_order_absNorm_eq (D := D) hm'
    rw [sum_kronZ_split hm h, ← e2] at e1
    exact (Nat.cast_inj.mp e1).le
  obtain ⟨⟨𝔯, 𝔟'⟩, hP⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨𝔟, h𝔟⟩
  exact ⟨𝔯.1, 𝔟'.1, 𝔯.2, 𝔟'.2, (congrArg Subtype.val hP).symm⟩

/-- **All ideals of norm $m$ lie in one genus** ($D < 0$ fundamental, $m \ge 1$): if $N\mathfrak b = N\mathfrak c = m$ then
$\gamma([\mathfrak b]) = \gamma([\mathfrak c])$. Write $m = m_0m'$ (`exists_split_at`); $\mathfrak b = \mathfrak r\mathfrak b'$,
$\mathfrak c = \mathfrak r\mathfrak c'$ with the same $\mathfrak r$ of norm $m_0$ (`exists_mul_of_absNorm`), and
$\gamma([\mathfrak b']) = \gamma([\mathfrak c'])$ as $N\mathfrak b' = N\mathfrak c' = m'$ is prime to $D$. Source: Zagier, §11
[unverified locator]; Gauss, *Disq. Arith.* §§229–233 [unverified]. -/
@[kb "zagier1981" "§11 [unverified locator]"]
theorem genusHom_eq_of_absNorm_eq (hD : D < 0) {𝔟 𝔠 : Ideal (QOrder D)} (h𝔟 : 𝔟 ∈ (Ideal (QOrder D))⁰)
    (h𝔠 : 𝔠 ∈ (Ideal (QOrder D))⁰) (hN : Ideal.absNorm 𝔟 = Ideal.absNorm 𝔠) (hm : Ideal.absNorm 𝔟 ≠ 0) :
    (isFormClassGroupOrder hD).genusHom (ClassGroup.mk0 ⟨𝔟, h𝔟⟩) =
      (isFormClassGroupOrder hD).genusHom (ClassGroup.mk0 ⟨𝔠, h𝔠⟩) := by
  obtain ⟨m₀, m', hsplit, hc, hq⟩ := exists_split_at D.natAbs _ hm
  have hm0 : m₀ * m' ≠ 0 := hsplit ▸ hm
  obtain ⟨huniq, hfac⟩ := exists_mul_of_absNorm hm0 hc hq
  obtain ⟨𝔯, 𝔟', hr, hb', rfl⟩ := hfac 𝔟 hsplit
  obtain ⟨𝔯', 𝔠', hr', hc', rfl⟩ := hfac 𝔠 (hN ▸ hsplit)
  obtain rfl := huniq _ _ hr' hr
  have hm₀ : m₀ ≠ 0 := by rintro rfl; simp at hm0
  have hm' : m' ≠ 0 := by rintro rfl; simp at hm0
  have h𝔯 := mem_nonZeroDivisors_of_absNorm (D := D) (I := 𝔯') (by rw [hr]; exact hm₀)
  have h𝔟' := mem_nonZeroDivisors_of_absNorm (D := D) (I := 𝔟') (by rw [hb']; exact hm')
  have h𝔠' := mem_nonZeroDivisors_of_absNorm (D := D) (I := 𝔠') (by rw [hc']; exact hm')
  rw [show (⟨𝔯' * 𝔟', h𝔟⟩ : (Ideal (QOrder D))⁰) = ⟨𝔯', h𝔯⟩ * ⟨𝔟', h𝔟'⟩ from rfl,
    show (⟨𝔯' * 𝔠', h𝔠⟩ : (Ideal (QOrder D))⁰) = ⟨𝔯', h𝔯⟩ * ⟨𝔠', h𝔠'⟩ from rfl, map_mul, map_mul, map_mul,
    map_mul, genusHom_eq_of_absNorm_eq_coprime hD h𝔟' h𝔠' hb' hc' hc]

/-- Classes with the same genus vector lie in the same genus. -/
theorem genusOf_eq_of_genusHom_eq (hD : D < 0) {x y : ClassGroup (QOrder D)}
    (h : (isFormClassGroupOrder hD).genusHom x = (isFormClassGroupOrder hD).genusHom y) :
    (isFormClassGroupOrder hD).genusOf x = (isFormClassGroupOrder hD).genusOf y :=
  ((isFormClassGroupOrder hD).genusOf_eq_iff hD x _).mpr
    (h.trans (((isFormClassGroupOrder hD).genusOf_eq_iff hD y _).mp rfl))

/-! ### Which ideal classes of norm $m$ lie in a given genus -/

/-- **An ideal class containing an ideal of norm $m$ lies in the genus of $f$ iff some form in that genus represents
$m$** ($D < 0$ fundamental, $m \ge 1$). ($\Rightarrow$: a form of the inverse class represents $m$. $\Leftarrow$: a form
$g$ in the genus representing $m$ gives an ideal of norm $m$ in $[\mathfrak a_g]^{-1}$, and all ideals of norm $m$ lie in
one genus, `genusHom_eq_of_absNorm_eq`.) -/
theorem genusOf_eq_iff_represents (hD : D < 0) (f : PosForms D) {m : ℕ} (hm : m ≠ 0) (x : ClassGroup (QOrder D))
    (hx : Nonempty (IdealsInClass x m)) :
    (isFormClassGroupOrder hD).genusOf x = Quotient.mk (genusSetoid D) f ↔
      ∃ g : BinQF, SameGenus f.1 g ∧ g.Represents m := by
  set C := isFormClassGroupOrder hD
  obtain ⟨⟨𝔟, hN, h0, hc⟩⟩ := hx
  constructor
  · intro hG
    set F := C.rep x⁻¹
    have hF : idealClass F.toPrim = x⁻¹ := C.cls_rep x⁻¹
    have hc' : ClassGroup.mk0 (⟨𝔟, h0⟩ : (Ideal (QOrder D))⁰) = (idealClass F.toPrim)⁻¹ := by rw [hF, inv_inv, hc]
    obtain ⟨u, v, huv⟩ := exists_eval_of_ideal hD F.toPrim hN h0 hc'
    have hs : SameGenus F.1 f.1 := by
      have : C.genusOf x⁻¹ = Quotient.mk (genusSetoid D) f := by rw [C.genusOf_inv hD, hG]
      exact Quotient.exact this
    exact ⟨F.1, hs.symm, u, v, huv⟩
  · rintro ⟨g, hs, u, v, huv⟩
    obtain ⟨h1, h2, h3⟩ := mem_primPosForm_of_sameGenus f.toPrim hs
    set G : PrimPosForm D := ⟨g, h1, h2, h3⟩
    obtain ⟨𝔠, hN𝔠, h𝔠, hc𝔠⟩ := exists_ideal_of_eval hD G hm huv
    have hgen : C.genusOf (ClassGroup.mk0 ⟨𝔠, h𝔠⟩) = Quotient.mk (genusSetoid D) f := by
      rw [hc𝔠, C.genusOf_inv hD]
      exact (C.genusOf_cls G.toPos).trans (Quotient.sound hs.symm)
    rw [← hgen, ← hc]
    exact genusOf_eq_of_genusHom_eq hD (genusHom_eq_of_absNorm_eq hD h0 h𝔠 (hN.trans hN𝔠.symm) (hN ▸ hm))

/-- **For $m$ prime to $D$, the genus of an ideal of norm $m$ is read off the genus characters of $m$:** it is the
genus of $f$ iff $\psi_p(m) = \chi_p(f)$ for every $p \mid D$. -/
theorem genusOf_mk0_eq_iff_coprime (hD : D < 0) (f : PosForms D) {𝔟 : Ideal (QOrder D)}
    (h0 : 𝔟 ∈ (Ideal (QOrder D))⁰) {m : ℕ} (hN : Ideal.absNorm 𝔟 = m) (hm : Nat.Coprime m D.natAbs) :
    (isFormClassGroupOrder hD).genusOf (ClassGroup.mk0 ⟨𝔟, h0⟩) = Quotient.mk (genusSetoid D) f ↔
      ∀ p ∈ D.natAbs.primeFactors, genusChar D p m = formChar f.1 p := by
  have hpm : ∀ p : D.natAbs.primeFactors, ¬ (p.1 : ℤ) ∣ m := fun p h => by
    have h1 : p.1 ∣ m := Int.natCast_dvd_natCast.mp h
    exact (Nat.prime_of_mem_primeFactors p.2).one_lt.ne'
      (Nat.eq_one_of_dvd_coprimes hm h1 (Nat.dvd_of_mem_primeFactors p.2))
  rw [(isFormClassGroupOrder hD).genusOf_eq_iff hD _ (Quotient.mk (genusSetoid D) f)]
  change _ = genusVec D f.1 ↔ _
  constructor
  · intro h p hp
    have h' := congrArg Units.val (congrFun h ⟨p, hp⟩)
    rwa [genusHom_mk0_coe hD h0 hN ⟨p, hp⟩ (hpm ⟨p, hp⟩), coe_genusVec f.2.1 f.2.2.1] at h'
  · intro h
    funext p
    apply Units.ext
    rw [genusHom_mk0_coe hD h0 hN p (hpm p), coe_genusVec f.2.1 f.2.2.1]
    exact h p p.2

open Classical in
/-- **The number of ideals of norm $m$ whose class lies in a genus**, as a sum over the classes of the genus: if
membership of the classes containing ideals of norm $m$ is decided by a proposition $P$, the count is
$\#\{\mathfrak b : N\mathfrak b = m\}$ if $P$ holds and $0$ otherwise. -/
theorem sum_card_idealsInClass_genus [Fintype (ClassGroup (QOrder D))] (hD : D < 0) (𝒢 : Genera D) {m : ℕ}
    (hm : m ≠ 0) (P : Prop)
    (hP : ∀ x : ClassGroup (QOrder D), Nonempty (IdealsInClass x m) →
      ((isFormClassGroupOrder hD).genusOf x = 𝒢 ↔ P)) :
    ∑ x ∈ Finset.univ.filter (fun x => (isFormClassGroupOrder hD).genusOf x = 𝒢), Nat.card (IdealsInClass x m) =
      if P then Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} else 0 := by
  classical
  have hne : ∀ x : ClassGroup (QOrder D), Nat.card (IdealsInClass x m) ≠ 0 → Nonempty (IdealsInClass x m) :=
    fun x h => (Nat.card_ne_zero.mp h).1
  split_ifs with hp
  · rw [card_ideals_eq_sum_classes hm]
    convert Finset.sum_filter_of_ne fun x _ h => (hP x (hne x h)).mpr hp
  · refine Finset.sum_eq_zero fun x hx => ?_
    by_contra h
    exact hp ((hP x (hne x h)).mp (Finset.mem_filter.mp hx).2)

/-! ### The genus average -/

open Classical in
/-- **The weighted sum of representation numbers over a genus** ($D < 0$ fundamental, $m \ge 1$): with the repo's
`Siegel.genusRepSum` ($\mathrm{GL}_2(\mathbb{Z})$-classes in the genus of $f$, weights $1/|\mathrm{Aut}|$),
$$\sum_{[g] \in \mathrm{Gen}(f)} \frac{r_g(m)}{|\mathrm{Aut}(g)|} = \frac12 \sum_{x \in \mathcal G}
\#\{\mathfrak b : N\mathfrak b = m,\ [\mathfrak b] = x\}$$
(`repNum_eq` and the fibre identity `sum_div_aut_genus`). -/
theorem genusRepSum_eq_half_sum [Fact (D < 0)] [Fintype (ClassGroup (QOrder D))] (f : PosForms D) {m : ℕ}
    (hm : m ≠ 0) :
    Siegel.genusRepSum f.1 m = (1 / 2 : ℝ) *
      ∑ x ∈ Finset.univ.filter (fun x => (isFormClassGroupOrder (D := D) Fact.out).genusOf x =
        Quotient.mk (genusSetoid D) f), (Nat.card (IdealsInClass x m) : ℝ) := by
  classical
  have hD : D < 0 := Fact.out
  set C := isFormClassGroupOrder hD
  set w := NumberField.Units.torsionOrder (QField D)
  have hw : (w : ℝ) ≠ 0 := by exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  rw [Siegel.genusRepSum, finsum_genusClasses f (fun c => ((c.repNum m : ℕ) : ℝ) / c.autCard)]
  have h1 : ∀ G : Quotient (glSetoid D),
      (((glToQClass G).repNum m : ℕ) : ℝ) / ((glToQClass G).autCard : ℕ) =
        (glClassRepNum m G : ℝ) / glClassAutCard G := by
    intro G
    induction G using Quotient.inductionOn with
    | h g => simp [glToQClass, glClassAutCard, glClassRepNum]
  simp_rw [h1]
  rw [sum_div_aut_genus (Quotient.mk (genusSetoid D) f) (fun G => (glClassRepNum m G : ℝ))]
  have h2 : ∀ c : Quotient (slSetoid D), (glClassRepNum m (slToGl c) : ℝ) = slClassRepNum m c := by
    intro c
    induction c using Quotient.inductionOn with | h g => rfl
  simp_rw [h2]
  have h3 : ∑ c ∈ Finset.univ.filter (fun c => slGenus c = Quotient.mk (genusSetoid D) f),
      (slClassRepNum m c : ℝ) =
      ∑ x ∈ Finset.univ.filter (fun x => C.genusOf x = Quotient.mk (genusSetoid D) f),
        (Nat.card (IdealsInClass x m) : ℝ) * w := by
    refine Finset.sum_equiv ((slClassEquivOrder hD).trans (Equiv.inv _)) (fun c => ?_) (fun c _ => ?_)
    · induction c using Quotient.inductionOn with
      | h F =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, slGenus_mk, Equiv.trans_apply,
          Equiv.inv_apply]
        change _ ↔ C.genusOf (formClassOrder F.toPos)⁻¹ = _
        rw [C.genusOf_inv hD, C.genusOf_cls]
    · induction c using Quotient.inductionOn with
      | h F =>
        simp only [slClassRepNum, Quotient.lift_mk, Equiv.trans_apply, Equiv.inv_apply]
        rw [repNum_eq hD F hm, card_units_eq_torsionOrder hD]
        push_cast
        rfl
  rw [h3, ← Finset.sum_mul, mul_div_assoc]
  rw [show (w : ℝ) / (2 * (NumberField.Units.torsionOrder (QField D) : ℝ)) = 1 / 2 by field_simp; exact div_self hw]
  ring

open Classical in
/-- **The genus average of representation numbers of binary forms** ($D < 0$ fundamental, $m \ge 1$): with the repo's
`Siegel.genusRepAvg` (the library's convention: $\mathrm{GL}_2(\mathbb{Z})$-classes in the genus $\mathcal G$
of $f$, weights
$1/|\mathrm{Aut}|$, $\mathrm{Aut} \le \mathrm{GL}_2(\mathbb{Z})$), $t$ = the number of prime factors of $D$,
$h$ = `classNumber (QField D)`, $w$ = `torsionOrder (QField D)` and $\chi_D$ = `kronZ D`,
$$r_{\mathcal G}(m) = \frac{1}{\mathrm{Mass}(\mathcal G)}\sum_{[g] \in \mathcal G}\frac{r_g(m)}{|\mathrm{Aut}(g)|} =
\begin{cases}\dfrac{w\,2^{t-1}}{h}\displaystyle\sum_{d \mid m}\chi_D(d) & \text{if some form in } \mathcal G
\text{ represents } m,\\ 0 & \text{otherwise.}\end{cases}$$
This is the input to the comparison with Siegel's $\varepsilon\,\beta_\infty(m)\prod_p\beta_p(m)$. All ideals of norm
$m$ lie in one genus (`genusHom_eq_of_absNorm_eq`), so the classes of $\mathcal G$ see all or none of them; there are
$\sum_{d \mid m}\chi_D(d)$ in all, and $\mathrm{Mass}(\mathcal G) = h/(2^{t-1}\cdot 2w)$ (`mass_genus`).
Source: Siegel (1935) for $n = 2$; Zagier, §§8, 11 [unverified locator]; Cox, Thm. 3.15 and §7 [unverified locator]. -/
@[kb "zagier1981" "§§8, 11 [unverified locator]"]
theorem genusRepAvg_binary [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0) :
    Siegel.genusRepAvg f.1 m =
      (NumberField.Units.torsionOrder (QField D) * 2 ^ (D.natAbs.primeFactors.card - 1) /
          classNumber (QField D) : ℝ) *
        if ∃ g : BinQF, SameGenus f.1 g ∧ g.Represents m then
          ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℝ) else 0 := by
  have hD : D < 0 := Fact.out
  let _ : Fintype (ClassGroup (QOrder D)) :=
    @Fintype.ofFinite _ (Finite.of_equiv _ (classGroupEquiv D).toEquiv.symm)
  have hsum := sum_card_idealsInClass_genus hD (Quotient.mk (genusSetoid D) f) hm _
    (genusOf_eq_iff_represents hD f hm)
  have hN : (Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} : ℝ) =
      ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℝ) := by
    exact_mod_cast card_ideals_order_absNorm_eq (D := D) hm
  rw [Siegel.genusRepAvg, genusRepSum_eq_half_sum f hm, mass_genus f]
  have hsumR := congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at hsumR
  rw [hsumR]
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hh : (classNumber (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (𝓞 (QField D)))).ne'
  split_ifs with hp
  · rw [hN]; field_simp
  · simp

open Classical in
/-- **The genus average for $m$ prime to $D$, by genus characters** ($D < 0$ fundamental, $m \ge 1$,
$\gcd(m, D) = 1$): the condition "some form of $\mathcal G$ represents $m$" becomes local,
$$r_{\mathcal G}(m) = \frac{w\,2^{t-1}}{h}\sum_{d \mid m}\chi_D(d)\ \text{ if } \psi_p(m) = \chi_p(f) \text{ for all } p \mid D,
\quad r_{\mathcal G}(m) = 0 \text{ otherwise},$$
with Gauss's genus characters $\psi_p$ = `genusChar D p` and $\chi_p(f)$ = `formChar f p`. As
$m \mapsto \psi_p(m)$ is multiplicative, $r_{\mathcal G}(m) = \frac{w}{h}\sum_{d \mid m}\chi_D(d)\prod_{p \mid D}(1 + \chi_p(f)\psi_p(m))$
for such $m$ (the product is $2^t$ or $0$; not stated separately). Source: Zagier, §11 [unverified locator]. -/
@[kb "zagier1981" "§11 [unverified locator]"]
theorem genusRepAvg_binary_coprime [Fact (D < 0)] (f : PosForms D) {m : ℕ} (hm : m ≠ 0)
    (hcop : Nat.Coprime m D.natAbs) :
    Siegel.genusRepAvg f.1 m =
      (NumberField.Units.torsionOrder (QField D) * 2 ^ (D.natAbs.primeFactors.card - 1) /
          classNumber (QField D) : ℝ) *
        if ∀ p ∈ D.natAbs.primeFactors, genusChar D p m = formChar f.1 p then
          ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℝ) else 0 := by
  have hD : D < 0 := Fact.out
  let _ : Fintype (ClassGroup (QOrder D)) :=
    @Fintype.ofFinite _ (Finite.of_equiv _ (classGroupEquiv D).toEquiv.symm)
  have hsum := sum_card_idealsInClass_genus hD (Quotient.mk (genusSetoid D) f) hm
    (∀ p ∈ D.natAbs.primeFactors, genusChar D p m = formChar f.1 p) fun x ⟨⟨𝔟, hN, h0, hc⟩⟩ => by
      rw [← hc]; exact genusOf_mk0_eq_iff_coprime hD f h0 hN hcop
  have hN : (Nat.card {I : Ideal (QOrder D) // Ideal.absNorm I = m} : ℝ) =
      ∑ d ∈ m.divisors, (kronZ D (d : ZMod D.natAbs) : ℝ) := by
    exact_mod_cast card_ideals_order_absNorm_eq (D := D) hm
  rw [Siegel.genusRepAvg, genusRepSum_eq_half_sum f hm, mass_genus f]
  have hsumR := congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at hsumR
  rw [hsumR]
  have hw : (NumberField.Units.torsionOrder (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.Units.torsionOrder_pos (QField D)).ne'
  have hh : (classNumber (QField D) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ClassGroup (𝓞 (QField D)))).ne'
  split_ifs with hp
  · rw [hN]; field_simp
  · simp

end QuadFormsKB.Binary
