/-
# A height criterion for trees (used for the Bruhat–Tits tree)

General graph lemmas used for the Bruhat–Tits tree (J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, key
`voight2021`: Proposition 23.5.8 and Lemma 23.5.15).

**Contents.** For a simple graph $G$ on $V$ and a height function $h : V \to \mathbb N$:
* `isAcyclic_of_height`: if adjacent vertices have heights differing by exactly one and every vertex has at most one
  neighbour of smaller height, then $G$ has no cycles.
* `le_dist_of_height`: if heights increase by at most one along each edge, then $h(v) \le h(u) + d(u, v)$.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace QuadFormsKB.Voight.Wave8

variable {V : Type*} (G : SimpleGraph V) (h : V → ℕ)

/-- **Height criterion for acyclicity.** If $|h(u) - h(v)| = 1$ for adjacent $u, v$, and each vertex $v$ has at most
one neighbour $u$ with $h(u) + 1 = h(v)$, then $G$ is acyclic. (At a vertex of maximal height on a cycle, both cycle
neighbours would be neighbours of smaller height, and they are distinct.) -/
theorem isAcyclic_of_height
    (hadj : ∀ u v, G.Adj u v → h u + 1 = h v ∨ h v + 1 = h u)
    (huniq : ∀ v u u', G.Adj v u → G.Adj v u' → h u + 1 = h v → h u' + 1 = h v → u = u') :
    G.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := c.support.toFinset.exists_max_image h ⟨v, List.mem_toFinset.2 c.start_mem_support⟩
  rw [List.mem_toFinset] at hm
  set p := c.rotate m hm with hp
  have hpc : p.IsCycle := hc.rotate hm
  have hnil := hpc.not_nil
  have hmem : ∀ w, w ∈ p.support → h w ≤ h m := fun w hw =>
    hmax w (List.mem_toFinset.2 ((SimpleGraph.Walk.mem_support_rotate_iff c m hm).1 hw))
  have ha : G.Adj m p.snd := SimpleGraph.Walk.adj_snd hnil
  have hb : G.Adj m p.penultimate := (SimpleGraph.Walk.adj_penultimate hnil).symm
  have ha' : h p.snd ≤ h m := hmem _ (p.getVert_mem_support 1)
  have hb' : h p.penultimate ≤ h m := hmem _ (p.getVert_mem_support (p.length - 1))
  have h1 : h p.snd + 1 = h m := by
    rcases hadj _ _ ha with h2 | h2 <;> omega
  have h2 : h p.penultimate + 1 = h m := by
    rcases hadj _ _ hb with h3 | h3 <;> omega
  exact hpc.snd_ne_penultimate (huniq m _ _ ha hb h1 h2)

theorem le_length_of_height (hadj : ∀ u v, G.Adj u v → h v ≤ h u + 1) {u v : V} (w : G.Walk u v) :
    h v ≤ h u + w.length := by
  induction w with
  | nil => simp
  | cons hxy w ih =>
    rw [SimpleGraph.Walk.length_cons]
    have := hadj _ _ hxy
    omega

/-- **Heights bound distances.** If $h(v) \le h(u) + 1$ for adjacent $u, v$, then $h(v) \le h(u) + d(u, v)$ whenever $v$
is reachable from $u$. -/
theorem le_dist_of_height (hadj : ∀ u v, G.Adj u v → h v ≤ h u + 1) {u v : V} (huv : G.Reachable u v) :
    h v ≤ h u + G.dist u v := by
  obtain ⟨w, hw⟩ := huv.exists_walk_length_eq_dist
  rw [← hw]
  exact le_length_of_height G h hadj w

end QuadFormsKB.Voight.Wave8
