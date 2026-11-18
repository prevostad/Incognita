# Gardening log

One row per item examined, newest last; rows are never edited or deleted (format:
[README.md](README.md)).

| Date | Model | Item | Check | Outcome | Main |
|---|---|---|---|---|---|
| 2026-11-17 | claude-opus-5-5 | P006 thm:main (ii)-(iii), isBatched_of_isFiner and isBatched_sequential_iff | implication | together they imply the known case IsBatched.seesRewardsUpTo_zero (a learner batched on g ignores the rewards in its first batch), same hypotheses: Relations.isBatched_seesRewardsUpTo_zero_of_isBatched_sequential_iff (relation recorded) | d2da0fa803af |
| 2026-11-17 | claude-opus-5-5 | P006 thm:main (ii)-(iii), isConsistentAtBatchEnds_of_isFiner and isConsistentAtBatchEnds_sequential_iff | implication | together they give LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds on every grid (through S_{t 1}), but the Lean proof of (iii) itself uses that lemma: no relation recorded | d2da0fa803af |
| 2026-11-17 | claude-opus-5-5 | P006 thm:main (iii), isConsistentAtBatchEnds_sequential_iff | same-object | P003 def:consistency (IsConsistentOnUnit) is P006 def:consistent at the batch ends of S_s on P^K, and LMLExplore's IsConsistent on P^K (finite arms): Relations.isConsistentOnUnit_iff_isConsistentAtBatchEnds_sequential, Relations.isConsistentOnUnit_iff_isConsistent (relations recorded); the frozen form needs E ⊆ 𝒫, the general form does not | d2da0fa803af |
| 2026-11-17 | claude-opus-5-5 | P003 def:consistency | duplicate | Incognita.P003.isConsistentOnUnit_of_isConsistent repeats the computation of LMLExplore.Bandits.IsConsistent.isConsistentAtBatchEnds (BatchedBandits); proved again from it: Relations.isConsistentOnUnit_of_isConsistent_of_isConsistentAtBatchEnds (relation recorded) | d2da0fa803af |
| 2026-11-17 | claude-opus-5-5 | P006 def:instance | same-object | not the same object as P003 def:instance: 𝒫 = 𝒫^K ∩ {m⋆ < 1} (Relations.batchedUnitBandits_eq_inter; an arm δ_1 is in 𝒫^K, not in 𝒫); no relation recorded; consequence: a learner consistent in the sense of P003 is consistent at the batch ends of every grid on 𝒫 (Relations.isConsistentAtBatchEnds_of_isConsistentOnUnit) | d2da0fa803af |
| 2026-11-17 | claude-opus-5-5 | P006 thm:main (i) | duplicate | InfoModel.mono, infoModel_top_iff, exists_infoModel_and_not_infoModel and Grid.eq_of_forall_one_le_t_eq (a variant of the generated Grid.ext): no duplicate in Incognita/; they are about the library's own definitions, so the dependencies cannot provide them | d2da0fa803af |
| 2026-11-17 | claude-opus-5-5 | BatchedBandits C1-C3 | directions | none answered by a library paper (P000 is their source, P006 is the setting); literature not searched again in this pass; no Dropped line | d2da0fa803af |
