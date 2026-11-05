/-
# An obstruction to class number one: a quadratic character of the idèles trivial on $F^\times\sigma(D)$

**Layer:** Shimura's Lemma 2.4(4) (`Hanke2005/SpinorIdeleMain.lean`: the number of proper classes of an indefinite genus
is $[F^\times_{\mathbb A} : F^\times\sigma(D)]$), Hilbert reciprocity over a number field (`HN.hilbert_product_formula_nf`),
nondegeneracy of the local Hilbert symbols (`SqDual.hilbCl_nondeg_fin`), and the Global Square Theorem
(`Lattices.isSquare_of_eventually_isSquare`).

`Hanke2005/ClassGroupSigns.lean` shows that there is one proper class when the class group with signs at the compact real
places is trivial. This file gives the converse direction in a precise form: when $F^\times\sigma(D)$ is contained in the
kernel of the quadratic idèle character $\chi_d(x) = \prod_v (x_v,d)_v$ attached to a non-square $d\in F^\times$, there are
at least two proper classes. (This is the obstruction to Hanke's printed "class number one $\Rightarrow$ one class" when
two or more real places are compact: take $d$ negative at exactly one compact real place and positive elsewhere; then
$\sigma(G_w) = F_w^{\times2}$ at the compact places and the local conditions below hold at the infinite places.)

The character $\chi_d$ itself is not constructed on all of $F^\times_{\mathbb A}$; instead the proof tests one idèle $x$
supported at a single finite place $v_0$ (with $(x_{v_0},d)_{v_0} = -1$ by local nondegeneracy) and uses Hilbert
reciprocity $\prod_p (a,d)_p = 1$ for a principal idèle $a$ to show $x\notin F^\times\sigma(D)$.

**Proves**
* `hilbert_inf_eq_of_mem_sigmaD`, `hilbert_fin_eq_of_mem_sigmaD`: if $x = a\cdot s$ with $a\in F^\times$ principal and
  $s\in\sigma(D)$, then $(a,d)_p = (x_p,d)_p$ at every place $p$ (under the local conditions (ii), (iii) below);
* `not_mem_classIdeleSub_of_hilbert`: an idèle that is $1$ at the infinite places and at every finite place but $v_0$, and
  has $(x_{v_0},d)_{v_0} = -1$, is not in $F^\times\sigma(D)$;
* **`classIdeleSub_ne_top_of_hilbert`**: for $d\in F^\times$ not a square in $F$ with (ii) $d$ a square in $F_w$ at every
  infinite $w$ where $Q$ is isotropic and (iii) $(c,d)_v = 1$ for all $c\in\sigma(SO(L_v))$ at every finite $v$,
  $F^\times\sigma(D)\ne F^\times_{\mathbb A}$;
* **`two_le_card_DC_of_hilbert`**: under the same hypotheses, for $Q_0$ nondegenerate and indefinite in $n\ge3$ variables,
  the genus has **at least two proper classes** (`2 ≤ Nat.card (DC Q₀)`); `hilbert_eq_one_of_isSquare_right` is the
  usual way to verify (iii) (e.g. $d$ a square in $F_v$).

At an anisotropic infinite place condition (ii) is not needed: $\sigma(G_w) = F_w^{\times2}$
(`isSquare_of_mem_sigmaInf`), so $(c,d)_w = 1$ for $c\in\sigma(G_w)$ automatically.

All unconditional, standard axioms only.
-/
import QuadFormsKB.Literature.Hanke2005.SpinorIdeleMain
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal
import QuadFormsKB.Literature.OMeara.Sec65Ideles
import QuadFormsKB.Literature.OMeara.Sec101B
import QuadFormsKB.Tamagawa.Indefinite.DCFinite

open NumberField IsDedekindDomain Matrix WithZero
open QuadFormsKB.OMeara (ideleAt ideleAtInf ideleAt_mul ideleAt_one ideleAt_inv ideleAtInf_mul ideleAtInf_one
  ideleAtInf_inv ideleAt_ofAdic_self ideleAt_ofAdic_ne ideleAtInf_ofAdic)

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005.SpinorIdele

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.EqualMasses

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

local notation "J" => IdeleGroup (𝓞 F) F

attribute [local instance] charZero_completion

/-- **Hilbert symbol with a square second argument:** $(a,b)_K = 1$ when $b\in K$ is a square. -/
theorem hilbert_eq_one_of_isSquare_right {K : Type*} [Field K] (a : K) {b : K} (hb : IsSquare b) :
    hilbertSymbol K a b = 1 := by
  rw [hilbertSymbol_comm]; exact QuadFormsKB.OMeara.hilbertSymbol_of_isSquare hb a

section Obstruction

variable (Q : QuadForm F n) (hQ : Q.Nondegenerate)

/-- **Local comparison at an infinite place.** Let $d\in F^\times$ be a square in $F_w$ whenever $Q$ is isotropic over
$F_w$ (condition (ii)). If $a\in F^\times$, $s\in\sigma(D)$ and $x = a\cdot s$ (as idèles), then
$(a,d)_w = (x_w,d)_w$ at every infinite place $w$. -/
theorem hilbert_inf_eq_of_mem_sigmaD (d : F) (hd0 : d ≠ 0)
    (hiso : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion → IsSquare (algebraMap F w.Completion d))
    (a : Fˣ) (s x : J) (hs : s ∈ sigmaD Q hQ) (hx : IdeleGroup.unitEmbedding (𝓞 F) F a * s = x)
    (w : InfinitePlace F) :
    (NFPlace.infinite w).hilbert (a : F) d =
      hilbertSymbol w.Completion (ideleAtInf x w) (algebraMap F w.Completion d) := by
  have e : algebraMap F w.Completion (a : F) * ideleAtInf s w = ideleAtInf x w := by
    rw [← hx, ideleAtInf_mul]; rfl
  have hz : hilbertSymbol w.Completion (ideleAtInf s w) (algebraMap F w.Completion d) = 1 := by
    by_cases hw : Q.IsotropicIn w.Completion
    · exact hilbert_eq_one_of_isSquare_right _ (hiso w hw)
    · exact QuadFormsKB.OMeara.hilbertSymbol_of_isSquare
        (isSquare_of_mem_sigmaInf Q hQ hw (ideleAtInf_ne_zero s w) (hs.1 w)) _
  show hilbertSymbol w.Completion (algebraMap F w.Completion (a : F)) (algebraMap F w.Completion d) = _
  rw [← e, NFLocal.hilbertSymbol_mul_left_infinite_nf w _ _ _ ((map_ne_zero _).mpr a.ne_zero)
    (ideleAtInf_ne_zero s w) ((map_ne_zero _).mpr hd0), hz, mul_one]

/-- **Local comparison at a finite place.** Let $d\in F^\times$ satisfy (iii): $(c,d)_v = 1$ for every
$c\in F_v^\times$ with $cF_v^{\times2}\in\sigma(SO(L_v))$. If $a\in F^\times$, $s\in\sigma(D)$ and $x = a\cdot s$, then
$(a,d)_v = (x_v,d)_v$ at every finite place $v$. -/
theorem hilbert_fin_eq_of_mem_sigmaD (d : F) (hd0 : d ≠ 0)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∀ c : v.adicCompletion F, c ≠ 0 → sqClassOf c ∈ sigmaFin Q hQ v →
      hilbertSymbol (v.adicCompletion F) c (algebraMap F (v.adicCompletion F) d) = 1)
    (a : Fˣ) (s x : J) (hs : s ∈ sigmaD Q hQ) (hx : IdeleGroup.unitEmbedding (𝓞 F) F a * s = x)
    (v : HeightOneSpectrum (𝓞 F)) :
    (NFPlace.finite v).hilbert (a : F) d =
      hilbertSymbol (v.adicCompletion F) (ideleAt x v) (algebraMap F (v.adicCompletion F) d) := by
  have e : algebraMap F (v.adicCompletion F) (a : F) * ideleAt s v = ideleAt x v := by
    rw [← hx, ideleAt_mul]; rfl
  have hz := hfin v (ideleAt s v) (ideleAt_ne_zero s v) (hs.2 v)
  show hilbertSymbol (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (a : F))
    (algebraMap F (v.adicCompletion F) d) = _
  rw [← e, HN.hilbertSymbol_mul_left_finite_nf v _ _ _ ((map_ne_zero _).mpr a.ne_zero)
    (ideleAt_ne_zero s v) ((map_ne_zero _).mpr hd0), hz, mul_one]

/-- **An idèle supported at one finite place with Hilbert symbol $-1$ is not in $F^\times\sigma(D)$.**
Let $d\in F^\times$ satisfy (ii) and (iii) (see `hilbert_inf_eq_of_mem_sigmaD`, `hilbert_fin_eq_of_mem_sigmaD`). If the idèle
$x$ is $1$ at every infinite place and at every finite place other than $v_0$, and $(x_{v_0},d)_{v_0} = -1$, then
$x\notin F^\times\sigma(D)$. *Proof:* if $x = a\cdot s$, then $(a,d)_p = (x_p,d)_p$ at every place, which is $-1$ only at
$p = v_0$; this contradicts Hilbert reciprocity (an even number of places with symbol $-1$). -/
theorem not_mem_classIdeleSub_of_hilbert (d : F) (hd0 : d ≠ 0)
    (hiso : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion → IsSquare (algebraMap F w.Completion d))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∀ c : v.adicCompletion F, c ≠ 0 → sqClassOf c ∈ sigmaFin Q hQ v →
      hilbertSymbol (v.adicCompletion F) c (algebraMap F (v.adicCompletion F) d) = 1)
    (x : J) (v₀ : HeightOneSpectrum (𝓞 F)) (hxinf : ∀ w, ideleAtInf x w = 1)
    (hxfin : ∀ v, v ≠ v₀ → ideleAt x v = 1)
    (hx₀ : hilbertSymbol (v₀.adicCompletion F) (ideleAt x v₀) (algebraMap F (v₀.adicCompletion F) d) = -1) :
    x ∉ classIdeleSub Q hQ := by
  intro hmem
  obtain ⟨y, hy, s, hs, hys⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨a, rfl⟩ := hy
  have hset : {p : NFPlace F | p.hilbert (a : F) d = -1} = {NFPlace.finite v₀} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    cases p with
    | infinite w =>
      rw [hilbert_inf_eq_of_mem_sigmaD Q hQ d hd0 hiso a s x hs hys w, hxinf w, hilbertSymbol_comm,
        hilbertSymbol_one_right]
      simp
    | finite v =>
      rw [hilbert_fin_eq_of_mem_sigmaD Q hQ d hd0 hfin a s x hs hys v]
      by_cases hv : v = v₀
      · subst hv; simp [hx₀]
      · rw [hxfin v hv, hilbertSymbol_comm, hilbertSymbol_one_right]
        simp [hv]
  have heven := (HN.hilbert_product_formula_nf (a : F) d a.ne_zero hd0).2
  rw [hset, Set.ncard_singleton] at heven
  exact Nat.not_even_one heven

/-- **$F^\times\sigma(D)\ne F^\times_{\mathbb A}$ when a nontrivial quadratic idèle character kills it.** Let
$Q$ be a nondegenerate quadratic form over $F$ and $d\in F^\times$ with
(i) $d$ not a square in $F$ (`hdsq`);
(ii) $d$ a square in $F_w$ at every infinite place $w$ where $Q$ is isotropic over $F_w$ (`hiso`);
(iii) $(c,d)_v = 1$ for every finite place $v$ and every $c\in F_v^\times$ with $cF_v^{\times2}\in\sigma(SO(L_v))$ (`hfin`;
e.g. $d$ a square in $F_v$, `hilbert_eq_one_of_isSquare_right`).
Then the principal idèles together with $\sigma(D)$ do not generate the idèle group: the character
$\chi_d(x) = \prod_v (x_v,d)_v$ is nontrivial (by (i), local nondegeneracy at a finite place where $d$ is not a local
square, `isSquare_of_eventually_isSquare`) and trivial on $F^\times$ (Hilbert reciprocity) and on $\sigma(D)$. -/
theorem classIdeleSub_ne_top_of_hilbert (d : F) (hd0 : d ≠ 0) (hdsq : ¬ IsSquare d)
    (hiso : ∀ w : InfinitePlace F, Q.IsotropicIn w.Completion → IsSquare (algebraMap F w.Completion d))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∀ c : v.adicCompletion F, c ≠ 0 → sqClassOf c ∈ sigmaFin Q hQ v →
      hilbertSymbol (v.adicCompletion F) c (algebraMap F (v.adicCompletion F) d) = 1) :
    classIdeleSub Q hQ ≠ ⊤ := by
  classical
  -- a finite place where `d` is not a local square
  obtain ⟨v₀, hv₀⟩ : ∃ v : HeightOneSpectrum (𝓞 F), ¬ IsSquare (algebraMap F (v.adicCompletion F) d) := by
    by_contra h
    push Not at h
    exact hdsq (isSquare_of_eventually_isSquare d (Filter.Eventually.of_forall h))
  have hd' : algebraMap F (v₀.adicCompletion F) d ≠ 0 := (map_ne_zero _).mpr hd0
  -- local nondegeneracy: some unit has symbol `-1` with `d`
  obtain ⟨u, hu⟩ : ∃ u : (v₀.adicCompletion F)ˣ,
      hilbertSymbol (v₀.adicCompletion F) (u : v₀.adicCompletion F) (algebraMap F (v₀.adicCompletion F) d) = -1 := by
    obtain ⟨c, hc⟩ := SqDual.hilbCl_nondeg_fin v₀ (QuotientGroup.mk (Units.mk0 _ hd'))
      (fun h => hv₀ ((SqDual.mk_eq_one_iff_isSquare _ _).mp h))
    induction c using QuotientGroup.induction_on with
    | H u => exact ⟨u, hc⟩
  intro htop
  have hx : IdeleGroup.ofAdicCompletion (𝓞 F) F v₀ u ∈ classIdeleSub Q hQ := htop ▸ Subgroup.mem_top _
  refine not_mem_classIdeleSub_of_hilbert Q hQ d hd0 hiso hfin _ v₀ (fun w => ideleAtInf_ofAdic v₀ w u)
    (fun v hv => ideleAt_ofAdic_ne v₀ v hv u) ?_ hx
  rw [ideleAt_ofAdic_self]
  exact hu

end Obstruction

section Classes

variable (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **At least two proper classes: an obstruction to class number one** (Hanke 2005, Cor. 5.2, second assertion, shown to fail
in general; the correct hypothesis is the class group with signs, `card_DC_eq_one_of_signs`). Let $Q_0$ be nondegenerate and
indefinite in $n\ge3$ variables over $\mathcal O_F$, and $d\in F^\times$ with
(i) $d$ not a square in $F$ (`hdsq`);
(ii) $d$ a square in $F_w$ at every infinite place $w$ where $Q = Q_0\otimes F$ is isotropic (`hiso`; at anisotropic places
nothing is needed since $\sigma(G_w) = F_w^{\times2}$);
(iii) $(c,d)_v = 1$ for every finite $v$ and every $c\in F_v^\times$ with $cF_v^{\times2}\in\sigma(SO(L_v))$ (`hfin`).
Then the genus of $Q_0$ has at least two proper classes: $F^\times\sigma(D)$ lies in the kernel of the nontrivial character
$\chi_d(x) = \prod_v (x_v,d)_v$ of $F^\times_{\mathbb A}$, and $\lvert\mathrm{DC}\rvert = [F^\times_{\mathbb A}:F^\times\sigma(D)]$
(Shimura's Lemma 2.4(4), `card_DC_eq_index_idele`). -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (second assertion: obstruction from the class group with signs)"]
theorem two_le_card_DC_of_hilbert (hn : 3 ≤ n) (hind : IsIndefinite QF) (d : F) (hd0 : d ≠ 0)
    (hdsq : ¬ IsSquare d)
    (hiso : ∀ w : InfinitePlace F, (QF).IsotropicIn w.Completion → IsSquare (algebraMap F w.Completion d))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∀ c : v.adicCompletion F, c ≠ 0 →
      sqClassOf c ∈ sigmaFin QF (nondegenerate_map Q₀ hQ) v →
      hilbertSymbol (v.adicCompletion F) c (algebraMap F (v.adicCompletion F) d) = 1) :
    2 ≤ Nat.card (DC Q₀) := by
  have hne : classIdeleSub QF (nondegenerate_map Q₀ hQ) ≠ ⊤ :=
    classIdeleSub_ne_top_of_hilbert QF (nondegenerate_map Q₀ hQ) d hd0 hdsq hiso hfin
  have h1 : (classIdeleSub QF (nondegenerate_map Q₀ hQ)).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hfinite : Finite (J ⧸ classIdeleSub QF (nondegenerate_map Q₀ hQ)) := by
    have := finite_DC Q₀ hQ
    exact Finite.of_equiv _ (dcEquivIdele Q₀ hQ hn hind)
  have h0 : (classIdeleSub QF (nondegenerate_map Q₀ hQ)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [card_DC_eq_index_idele Q₀ hQ hn hind]
  omega

end Classes

end QuadFormsKB.Hanke2005.SpinorIdele
