using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

// 1-WL canonizer with TRUE partial-order semantics on tiebreaks.
//
// Where CanonGraphOrdererOneWLPartialOrder kept (BelowCount, AboveCount)
// integer levels and used them as the lead component of every signature,
// this orderer drops the level entirely and uses the vertex's CLASS
// identity. The class identity is exactly what 1-WL refinement produces:
// "you and another vertex share a class iff 1-WL cannot tell you apart".
//
// Why the change matters for tiebreaks: setting M[a, b] = Less in the
// previous orderer changed BelowCount(b) and AboveCount(a), which in turn
// changed every other tied-class member's *relative* level versus a and
// b. The next refinement step then assigned every untouched tied-class
// member an order versus a and b — exactly what the user does NOT want.
// Here, classes only change by 1-WL refinement and explicit tiebreaks;
// setting M[a, b] = Less has no side-effect on any class that doesn't
// contain a or b.
//
// Three-vertex behaviour (the canonical examples):
//
//   Star (S center, leaves L1 L2 L3): 1-WL gives classes {S}, {L1,L2,L3}.
//     Tiebreak on (L1, L2) splits the leaves into {L1}, {L2}, and a
//     remnant {L3}. {L1} < {L2} from the tiebreak; {L3} is incomparable
//     with both. Refinement does not propagate (L3 sees only S, exactly
//     like L1 and L2 do — no neighbour-multiset distinction). M[L1, L3]
//     stays Unknown until a separate tiebreak resolves it.
//
//   Line A-B-C-D: 1-WL gives {A,D} and {B,C}. Tiebreak (A, D) splits
//     {A,D} into {A} < {D}. Refinement re-runs: B's neighbour multiset
//     contains {A}, C's contains {D} — different multisets, so {B,C}
//     splits into {B} and {C}, and the multiset comparison via class
//     partial order yields {B} < {C}. One tiebreak suffices.
//
// Code clarity is prioritized; performance will be poor.

namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    public sealed class CanonGraphOrdererOneWLTruePartialOrder : ICanonGraphOrderer
    {
        public AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
        {
            if (vertexTypes.Length != G.VertexCount)
                throw new Exception("Every vertex must be given a type. They may all be given the same type");

            int n = G.VertexCount;
            int[] adj = ExtractAdj(G);

            var cpo = ClassPartialOrder.FromVertexTypes(vertexTypes);
            cpo.RefineToFixedPoint(adj);

            while (!cpo.AllVerticesAreSingletons() || !cpo.IsTotal())
            {
                if (!cpo.AllVerticesAreSingletons())
                    cpo.Tiebreak();
                else
                    cpo.TiebreakIncomparableSingletons();
                cpo.RefineToFixedPoint(adj);
            }

            return PermuteByClassOrder(G, cpo);
        }

        public string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges) =>
            Run(vertexTypes, new AdjMatrix(edges)).ToString();

        // ── ClassPartialOrder ──────────────────────────────────────────────────
        //
        // Holds the algorithm's persistent state:
        //   * vertexClass[v]    — which class v belongs to (an int label).
        //   * classMembers[id]  — list of vertices in that class.
        //   * classOrder[a, b]  — partial order on class labels (Less / Greater
        //                         / Unknown). Unknown means the algorithm has
        //                         not yet decided their relative order; this
        //                         INCLUDES "structurally tied" and "ordered by
        //                         a tiebreak that didn't reach this class".
        //
        // Class labels are arbitrary integers — they are NOT a linearization of
        // classOrder. All ordering questions go through classOrder explicitly.

        public enum Ordering : sbyte { Less = -1, Unknown = 0, Greater = 1 }

        public sealed class ClassPartialOrder
        {
            public readonly int N;
            private int[] vertexClass;
            private readonly List<List<int>> classMembers;
            private readonly Dictionary<(int A, int B), Ordering> classOrder;
            private int nextClassId;

            private ClassPartialOrder(int n)
            {
                N = n;
                vertexClass = new int[n];
                classMembers = new List<List<int>>();
                classOrder = new Dictionary<(int A, int B), Ordering>();
                nextClassId = 0;
            }

            public static ClassPartialOrder FromVertexTypes(int[] types)
            {
                int n = types.Length;
                var cpo = new ClassPartialOrder(n);

                // Group vertices by type. One class per distinct type.
                var byType = new Dictionary<int, int>(); // type → class id
                for (int v = 0; v < n; v++)
                {
                    if (!byType.TryGetValue(types[v], out int classId))
                    {
                        classId = cpo.AllocateClass();
                        byType[types[v]] = classId;
                    }
                    cpo.AssignVertexToClass(v, classId);
                }

                // Initial classOrder: types are integer-comparable, so the
                // ordering is total over the initial classes.
                var classIdsByType = new SortedDictionary<int, int>();
                foreach (var kv in byType) classIdsByType[kv.Key] = kv.Value;
                int[] sortedClassIds = [.. classIdsByType.Values];
                for (int i = 0; i < sortedClassIds.Length; i++)
                    for (int j = i + 1; j < sortedClassIds.Length; j++)
                        cpo.SetClassOrder(sortedClassIds[i], sortedClassIds[j], Ordering.Less);

                return cpo;
            }

            // ── Class bookkeeping ─────────────────────────────────────────────

            private int AllocateClass()
            {
                int id = nextClassId++;
                while (classMembers.Count <= id) classMembers.Add(null!);
                classMembers[id] = [];
                return id;
            }

            private void AssignVertexToClass(int v, int classId)
            {
                vertexClass[v] = classId;
                classMembers[classId].Add(v);
            }

            private void SetClassOrder(int a, int b, Ordering ord)
            {
                if (a == b) return;
                classOrder[(a, b)] = ord;
                classOrder[(b, a)] = (Ordering)(-(int)ord);
            }

            public Ordering CompareClasses(int a, int b)
            {
                if (a == b) return Ordering.Unknown;
                return classOrder.TryGetValue((a, b), out var ord) ? ord : Ordering.Unknown;
            }

            // ── Queries ───────────────────────────────────────────────────────

            public bool AllVerticesAreSingletons()
            {
                for (int id = 0; id < classMembers.Count; id++)
                    if (classMembers[id] != null && classMembers[id].Count > 1) return false;
                return true;
            }

            public bool IsTotal()
            {
                // The classOrder is total iff every pair of populated classes
                // has a non-Unknown entry.
                var populated = new List<int>();
                for (int id = 0; id < classMembers.Count; id++)
                    if (classMembers[id] != null && classMembers[id].Count > 0)
                        populated.Add(id);

                for (int i = 0; i < populated.Count; i++)
                    for (int j = i + 1; j < populated.Count; j++)
                        if (CompareClasses(populated[i], populated[j]) == Ordering.Unknown)
                            return false;
                return true;
            }

            // Permutation derived from a total class partial order.
            // Precondition: AllVerticesAreSingletons() && IsTotal().
            public int[] CanonicalPermutation()
            {
                var order = new List<int>();
                for (int id = 0; id < classMembers.Count; id++)
                    if (classMembers[id] != null && classMembers[id].Count > 0)
                        order.Add(id);

                order.Sort((a, b) => (int)CompareClasses(a, b));

                var perm = new int[N];
                for (int rank = 0; rank < order.Count; rank++)
                {
                    var members = classMembers[order[rank]];
                    if (members.Count != 1)
                        throw new InvalidOperationException(
                            "CanonicalPermutation requires every class to be a singleton");
                    perm[members[0]] = rank;
                }
                return perm;
            }

            // ── Refinement ────────────────────────────────────────────────────
            //
            // 1-WL refinement: each vertex's "colour" is its current class
            // plus the sorted multiset of (neighbour class, edge, self-bit)
            // tuples. Two vertices share a class iff they share that whole
            // tuple. Each step that splits a class derives the partial order
            // between the new sub-classes by comparing their bags through
            // the *existing* class partial order: at the first position
            // where the two bags differ on class identity, the class
            // partial order at that position is the verdict — Less, Greater,
            // or Unknown (which leaves the two sub-classes incomparable in
            // the new partial order).
            //
            // The bags are sorted by integer-(cls, edge, self) lex once and
            // forever as their canonical form. The class partial order is
            // looked up at comparison time, so the algorithm doesn't need
            // class IDs to track partial-order positions.

            public void RefineToFixedPoint(int[] adj)
            {
                while (RefineOneStep(adj)) { }
            }

            private bool RefineOneStep(int[] adj)
            {
                var bags = new (int Cls, int Edge, int Self)[N][];
                for (int v = 0; v < N; v++)
                    bags[v] = ComputeBag(v, adj);

                // Group vertices by (currentClass, bag canonical form).
                var groupKey = new string[N];
                for (int v = 0; v < N; v++)
                    groupKey[v] = vertexClass[v] + ":" + BagToString(bags[v]);

                // Detect any class that splits.
                var groupsByOldClass = new Dictionary<int, HashSet<string>>();
                for (int v = 0; v < N; v++)
                {
                    int oldClass = vertexClass[v];
                    if (!groupsByOldClass.TryGetValue(oldClass, out var keys))
                        groupsByOldClass[oldClass] = keys = [];
                    keys.Add(groupKey[v]);
                }

                bool anySplit = groupsByOldClass.Values.Any(s => s.Count > 1);
                if (!anySplit) return false;

                ApplyRefinement(bags, groupKey);
                return true;
            }

            private (int Cls, int Edge, int Self)[] ComputeBag(int v, int[] adj)
            {
                var bag = new (int Cls, int Edge, int Self)[N];
                int rowBase = v * N;
                for (int u = 0; u < N; u++)
                    bag[u] = (vertexClass[u], adj[rowBase + u], u == v ? 1 : 0);
                Array.Sort(bag);
                return bag;
            }

            private static string BagToString((int Cls, int Edge, int Self)[] bag)
            {
                var sb = new StringBuilder();
                foreach (var (c, e, s) in bag) sb.Append(c).Append(',').Append(e).Append(',').Append(s).Append(';');
                return sb.ToString();
            }

            private Ordering CompareBags((int Cls, int Edge, int Self)[] b1, (int Cls, int Edge, int Self)[] b2)
            {
                int len = Math.Min(b1.Length, b2.Length);
                for (int i = 0; i < len; i++)
                {
                    if (b1[i] == b2[i]) continue;
                    if (b1[i].Cls != b2[i].Cls)
                        return CompareClasses(b1[i].Cls, b2[i].Cls);
                    if (b1[i].Edge != b2[i].Edge)
                        return b1[i].Edge < b2[i].Edge ? Ordering.Less : Ordering.Greater;
                    return b1[i].Self < b2[i].Self ? Ordering.Less : Ordering.Greater;
                }
                return Ordering.Unknown;
            }

            private void ApplyRefinement(
                (int Cls, int Edge, int Self)[][] bags,
                string[] groupKey)
            {
                // Group vertex indices by groupKey within each old class.
                var newGroups = new Dictionary<string, List<int>>();
                var newGroupParent = new Dictionary<string, int>();
                var newGroupBag = new Dictionary<string, (int Cls, int Edge, int Self)[]>();
                for (int v = 0; v < N; v++)
                {
                    if (!newGroups.TryGetValue(groupKey[v], out var lst))
                    {
                        newGroups[groupKey[v]] = lst = [];
                        newGroupParent[groupKey[v]] = vertexClass[v];
                        newGroupBag[groupKey[v]] = bags[v];
                    }
                    lst.Add(v);
                }

                // Snapshot old state for partial-order inheritance.
                var oldClassOrder = new Dictionary<(int, int), Ordering>(classOrder);

                // Allocate new class IDs and stash their bags / parents.
                var keyToNewId = new Dictionary<string, int>();
                var newIdBag = new Dictionary<int, (int Cls, int Edge, int Self)[]>();
                var newIdParent = new Dictionary<int, int>();

                // Reset state — we will rebuild from scratch.
                vertexClass = new int[N];
                classMembers.Clear();
                classOrder.Clear();
                nextClassId = 0;

                foreach (var kv in newGroups)
                {
                    int id = AllocateClass();
                    keyToNewId[kv.Key] = id;
                    newIdBag[id] = newGroupBag[kv.Key];
                    newIdParent[id] = newGroupParent[kv.Key];
                    foreach (var v in kv.Value) AssignVertexToClass(v, id);
                }

                // Build the new partial order.
                var newIds = keyToNewId.Values.ToList();
                for (int i = 0; i < newIds.Count; i++)
                {
                    int idA = newIds[i];
                    for (int j = i + 1; j < newIds.Count; j++)
                    {
                        int idB = newIds[j];
                        int parentA = newIdParent[idA];
                        int parentB = newIdParent[idB];

                        Ordering ord;
                        if (parentA == parentB)
                            ord = CompareBags(newIdBag[idA], newIdBag[idB]);
                        else
                            ord = oldClassOrder.TryGetValue((parentA, parentB), out var p)
                                ? p : Ordering.Unknown;

                        if (ord != Ordering.Unknown)
                            SetClassOrder(idA, idB, ord);
                    }
                }
            }

            // ── Tiebreaks ─────────────────────────────────────────────────────

            // Pick the lex-smallest tied pair within any non-singleton class
            // and split that class into {a}, {b}, and the remnant {C \ {a,b}}.
            // Set classOrder({a}) < classOrder({b}); leave both incomparable
            // with the remnant. Other classes inherit the relation that the
            // parent class had with them.
            //
            // "Lex-smallest" picks the lowest class ID with size ≥ 2, and
            // within it the two lowest vertex indices. This is iso-variant
            // by index — same caveat as the previous orderer's tiebreak.
            public void Tiebreak()
            {
                int chosenClass = -1;
                for (int id = 0; id < classMembers.Count; id++)
                    if (classMembers[id] != null && classMembers[id].Count >= 2)
                    { chosenClass = id; break; }
                if (chosenClass < 0)
                    throw new InvalidOperationException("Tiebreak called with no tied class");

                var members = classMembers[chosenClass].ToList();
                members.Sort();
                int aIdx = members[0];
                int bIdx = members[1];
                var remnant = members.Skip(2).ToList();

                int classA = AllocateClass();
                int classB = AllocateClass();
                int classRem = remnant.Count > 0 ? AllocateClass() : -1;

                classMembers[chosenClass] = [];
                vertexClass[aIdx] = classA; classMembers[classA].Add(aIdx);
                vertexClass[bIdx] = classB; classMembers[classB].Add(bIdx);
                foreach (var v in remnant) { vertexClass[v] = classRem; classMembers[classRem].Add(v); }

                SetClassOrder(classA, classB, Ordering.Less);

                for (int otherId = 0; otherId < classMembers.Count; otherId++)
                {
                    if (otherId == chosenClass || otherId == classA || otherId == classB || otherId == classRem) continue;
                    if (classMembers[otherId] == null || classMembers[otherId].Count == 0) continue;
                    var ord = CompareClasses(chosenClass, otherId);
                    if (ord == Ordering.Unknown) continue;
                    SetClassOrder(classA, otherId, ord);
                    SetClassOrder(classB, otherId, ord);
                    if (classRem >= 0) SetClassOrder(classRem, otherId, ord);
                }

                // Drop stale entries referencing the now-empty parent.
                var stale = classOrder.Keys.Where(k => k.A == chosenClass || k.B == chosenClass).ToList();
                foreach (var k in stale) classOrder.Remove(k);
            }

            // After all classes are singletons, some pairs may still be
            // incomparable in the class partial order (e.g. {L1}, {L2}, {L3}
            // in a star after only M[L1, L2] was broken). Force the lex-
            // smallest incomparable pair to Less and continue.
            public void TiebreakIncomparableSingletons()
            {
                for (int i = 0; i < N; i++)
                    for (int j = i + 1; j < N; j++)
                        if (CompareClasses(vertexClass[i], vertexClass[j]) == Ordering.Unknown)
                        {
                            SetClassOrder(vertexClass[i], vertexClass[j], Ordering.Less);
                            return;
                        }
                throw new InvalidOperationException("TiebreakIncomparableSingletons called on a total order");
            }
        }

        // ── Helpers ────────────────────────────────────────────────────────────

        private static int[] ExtractAdj(AdjMatrix G)
        {
            int n = G.VertexCount;
            var adj = new int[n * n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    adj[i * n + j] = G[i, j];
            return adj;
        }

        private static AdjMatrix PermuteByClassOrder(AdjMatrix G, ClassPartialOrder cpo)
        {
            int n = G.VertexCount;
            var perm = cpo.CanonicalPermutation();
            var result = new EdgeType[n, n];
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    result[perm[i], perm[j]] = G[i, j];
            return new AdjMatrix(result);
        }
    }
}
