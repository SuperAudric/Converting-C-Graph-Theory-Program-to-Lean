using System.Collections.Generic;

namespace Canonizer
{
    // The refinement footprint of a decision — the linear oracle's "coupled
    // component" (docs/chain-descent-linear-oracle.md §3).
    //
    // When the descent individualizes a target-cell representative and warm-
    // refines, some cells split. Those splits — read as the diff between the
    // parent partition and the child partition — are how the decision's
    // coupling propagates. This is the mechanism the linear oracle reads to
    // build a candidate twist (§4.2), and it is *refinement*, not transitive-
    // closure provenance: TC is inert for within-cell decisions on uniform
    // graphs (cellmates are unordered among themselves, other cells are
    // P-incomparable — measured zero derived entries), so the cascade is
    // carried entirely by 1-WL. See the spec §3 correction note.
    //
    // Warm refinement is split-only (warmRefine_refines, proved), so the child
    // partition is always a refinement of the parent: every child cell sits
    // inside exactly one parent cell, and members of a parent cell never merge
    // across the boundary. That is what makes the (parentCell, childCell)
    // grouping below a sound split detector regardless of cell-id renumbering.
    internal sealed class RefinementFootprint
    {
        // The parent cells that split, by ascending parent cell id. A cell that
        // did not split is absent. Together these are the coupled component.
        public IReadOnlyList<SplitCell> SplitCells { get; }

        private RefinementFootprint(IReadOnlyList<SplitCell> splitCells) => SplitCells = splitCells;

        // Diff a parent partition against a child partition that refines it.
        // A parent cell "splits" when its members land in more than one child
        // cell. Sub-cells are ordered by child cell id (canonical, hence iso-
        // invariant within the child refinement); SplitCells by parent cell id.
        public static RefinementFootprint Compute(int n, int[] parentCellOf, int[] childCellOf)
        {
            // parent cell -> (child cell -> members), both keyed ascending so the
            // result is in canonical order without a later sort.
            var byParent = new SortedDictionary<int, SortedDictionary<int, List<int>>>();
            for (int v = 0; v < n; v++)
            {
                int pc = parentCellOf[v], cc = childCellOf[v];
                if (!byParent.TryGetValue(pc, out var sub))
                    byParent[pc] = sub = new SortedDictionary<int, List<int>>();
                if (!sub.TryGetValue(cc, out var members))
                    sub[cc] = members = new List<int>();
                members.Add(v);
            }

            var splits = new List<SplitCell>();
            foreach (var (pc, sub) in byParent)
            {
                if (sub.Count < 2) continue; // cell did not split
                var subCells = new int[sub.Count][];
                int i = 0;
                foreach (var members in sub.Values) subCells[i++] = members.ToArray();
                splits.Add(new SplitCell(pc, subCells));
            }
            return new RefinementFootprint(splits);
        }

        // The support of the coupled component: every vertex in a split cell,
        // ascending. (Vertices in cells that did not split are untouched by the
        // decision and excluded.)
        public int[] CoupledVertices()
        {
            var vs = new List<int>();
            foreach (var sc in SplitCells)
                foreach (var sub in sc.SubCells)
                    vs.AddRange(sub);
            vs.Sort();
            return vs.ToArray();
        }
    }

    // One parent cell of the coupled component, with the child sub-cells it
    // split into (ordered by canonical child cell id; each sub-cell ascending).
    internal readonly struct SplitCell
    {
        public int ParentCell { get; }
        public int[][] SubCells { get; }

        public SplitCell(int parentCell, int[][] subCells)
        {
            ParentCell = parentCell;
            SubCells = subCells;
        }

        // The all-singletons case — the forced-matching boundary the twist
        // construction needs (§4.3). NOTE: that this coincides with the
        // abelian/wall split is the orbit-recovery *conjecture*, not proved;
        // this is just the structural test, sound only as a gate before the
        // edge-by-edge verification.
        public bool AllSingletons
        {
            get
            {
                foreach (var s in SubCells)
                    if (s.Length != 1) return false;
                return true;
            }
        }
    }
}
