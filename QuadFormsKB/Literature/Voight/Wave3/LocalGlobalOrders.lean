/-
# Orders are determined by their completions; maximality is local (Voight, Cor. 9.4.7, Lemma 9.5.3, Lemma 10.4.3)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Lemma 9.4.6 and Corollary 9.4.7
(p. 160), Lemma 9.5.3 (p. 162), Lemma 10.4.3 (p. 175).

**Model.** $F$ a number field (any class number), $B = (a,b)_F$ with $a, b \in \mathbb Z_F$, orders
$\mathcal O \subseteq B$ over $\mathbb Z_F$, and for each finite place $v$ the completion $\mathcal O_v = \mathfrak o_v\mathcal O
\subseteq B_v$ (`localOrder`). Voight works with localizations $\mathcal O_{(\mathfrak p)}$; by Lemma 9.5.3 the
completions carry the same information, and the repository uses completions throughout.

**Contents.**
* `mem_of_forall_localOrder` (Lemma 9.4.6 for completions): $x \in B$ lies in $\mathcal O$ iff $x \in \mathcal O_v$ for every $v$,
  i.e. $\mathcal O = \bigcap_v (B \cap \mathcal O_v)$.
* `le_iff_forall_localOrder_le` (Corollary 9.4.7): $\mathcal O' \subseteq \mathcal O$ iff $\mathcal O'_v \subseteq \mathcal O_v$ for every $v$;
  `eq_iff_forall_localOrder_eq`: two orders with the same completions are equal.
* `isMaximalOrder_iff_forall_localOrder` (Lemma 10.4.3, both directions): $\mathcal O$ is maximal iff every $\mathcal O_v$ is
  a maximal $\mathfrak o_v$-order. The direction "maximal $\Rightarrow$ locally maximal" is the repository's
  `isMaximalOrder_localOrder_nf`; the converse is new.
-/
import QuadFormsKB.Literature.Voight.Wave3.LocalDiscriminant

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave3

open QuadFormsKB.Quat QuadFormsKB.QuatOrder IsLocalization

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-- **Membership is local** (Voight 2021, Lemma 9.4.6, with completions as in Lemma 9.5.3): an element $x \in B$ with
$\iota_v(x) \in \mathcal O_v$ for every finite place $v$ lies in the order $\mathcal O$. -/
@[kb "voight2021" "Lemma 9.4.6, p. 160; Lemma 9.5.3, p. 162"]
theorem mem_of_forall_localOrder {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) {x : QuatF F a b}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), complHom v a b x ∈ localOrder (v := v) a b O) : x ∈ O := by
  classical
  -- the ideal of denominators of $x$
  set I : Ideal (𝓞 F) := (Subalgebra.toSubmodule O).comap (LinearMap.toSpanSingleton (𝓞 F) _ x)
  have hmemI : ∀ s, s ∈ I ↔ s • x ∈ O := fun s => Iff.rfl
  -- every finite place contributes a denominator prime to it
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ s : 𝓞 F, s ∉ v.asIdeal ∧ s • x ∈ O := by
    intro v
    obtain ⟨L⟩ := LocFrame.exists (v := v) hO
    have hc : ∀ i, v.valuation F (L.fb.repr x i) ≤ 1 := fun i => by
      have := (L.mem_localOrder_iff (complHom v a b x)).1 (h v) i
      rw [L.cb_repr_complHom] at this
      exact (LocFrame.isInteger_algebraMap_iff (v := v) _).1 this
    refine exists_notMem_smul_mem (v := v) ?_
    rw [← L.fb.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (L.fb.repr x i) • L.fb i = (⟨L.fb.repr x i, (mem_locR_iff v).2 (hc i)⟩ : LocR v) • L.fb i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (L.mem i))
  by_contra hx
  have hI : I ≠ ⊤ := fun h1 => hx (by
    have : (1 : 𝓞 F) ∈ I := h1 ▸ Submodule.mem_top
    rw [hmemI, one_smul] at this; exact this)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)
  obtain ⟨s, hs, hsx⟩ := hloc ⟨m, hm.isPrime, hm0⟩
  exact hs (hIm ((hmemI s).2 hsx))

/-- **Inclusion of orders is local** (Voight 2021, Corollary 9.4.7, with completions): for orders $\mathcal O, \mathcal O'$,
$\mathcal O' \subseteq \mathcal O$ iff $\mathcal O'_v \subseteq \mathcal O_v$ for every finite place $v$. -/
@[kb "voight2021" "Corollary 9.4.7, p. 160; Lemma 9.5.3, p. 162"]
theorem le_iff_forall_localOrder_le {O O' : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    O' ≤ O ↔ ∀ v : HeightOneSpectrum (𝓞 F), localOrder (v := v) a b O' ≤ localOrder (v := v) a b O := by
  refine ⟨fun hle v => Submodule.span_mono (Set.image_mono hle), fun h x hx => ?_⟩
  exact mem_of_forall_localOrder hO fun v => h v (mem_localOrder_of_mem a b hx)

/-- **Orders with the same completions are equal** (Voight 2021, Lemma 9.4.6 and Lemma 9.5.3). -/
@[kb "voight2021" "Lemma 9.4.6, p. 160; Lemma 9.5.3, p. 162"]
theorem eq_iff_forall_localOrder_eq {O O' : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (hO' : IsOrder (𝓞 F) F O') :
    O' = O ↔ ∀ v : HeightOneSpectrum (𝓞 F), localOrder (v := v) a b O' = localOrder (v := v) a b O := by
  refine ⟨fun h v => h ▸ rfl, fun h => le_antisymm ?_ ?_⟩
  · exact (le_iff_forall_localOrder_le hO).2 fun v => (h v).le
  · exact (le_iff_forall_localOrder_le hO').2 fun v => (h v).ge

/-- **Maximality is local** (Voight 2021, Lemma 10.4.3, both directions, with completions): an order $\mathcal O$ of
$B = (a,b)_F$ is maximal iff for every finite place $v$ the completion $\mathcal O_v$ is a maximal
$\mathfrak o_v$-order of $B_v$. Every class number. -/
@[kb "voight2021" "Lemma 10.4.3, p. 175"]
theorem isMaximalOrder_iff_forall_localOrder {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O) :
    IsMaximalOrder (𝓞 F) F O ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      IsMaximalOrder (v.adicCompletionIntegers F) (v.adicCompletion F) (localOrder (v := v) a b O) := by
  refine ⟨fun hmax v => isMaximalOrder_localOrder_nf hmax, fun h => ⟨hO, fun O' hO' hle => ?_⟩⟩
  refine le_antisymm ((le_iff_forall_localOrder_le hO).2 fun v => ?_) hle
  have hv := (h v).2 _ (Gen.isOrder_localOrder_gen v hO') (Submodule.span_mono (Set.image_mono hle))
  exact hv.le

end QuadFormsKB.Voight.Wave3
