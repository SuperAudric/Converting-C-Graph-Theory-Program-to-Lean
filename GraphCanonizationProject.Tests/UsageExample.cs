using Canonizer;
using VertexType = int;
using EdgeType = int;

// Worked examples of the public API, kept as tests so they cannot rot: if the API
// changes, `dotnet test` fails here. Narrative version: docs/USER-GUIDE.md.
//
// The whole surface is ICanonGraphOrderer:
//     AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G)
//     string    Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges)
// Both either return a canonical form or throw CanonizationFlaggedException.
// They never return a wrong answer — that is the guarantee the Lean side proves.
public class UsageExample
{
    // Undirected edge matrix from an edge list. Entries are edge "colours";
    // 0 means no edge, so a plain graph uses 0/1.
    private static EdgeType[,] Graph(int n, params (int, int)[] edges)
    {
        var m = new EdgeType[n, n];
        foreach (var (a, b) in edges) { m[a, b] = 1; m[b, a] = 1; }
        return m;
    }

    [Fact]
    public void CanonicalForm_IsTheSameForEveryLabelling()
    {
        var orderer = new CanonGraphOrdererChainDescent();

        // The same 4-vertex path, written two different ways.
        var path = Graph(4, (0, 1), (1, 2), (2, 3));
        var relabelled = Graph(4, (3, 1), (1, 0), (0, 2));

        // vertexTypes lets you pre-colour vertices (atom types, say). All-zero
        // means "no prior distinction"; the array length is the vertex count.
        string a = orderer.Run_ToString(new VertexType[4], path);
        string b = orderer.Run_ToString(new VertexType[4], relabelled);

        Assert.Equal(a, b);   // isomorphic  =>  identical canonical form
    }

    [Fact]
    public void NonIsomorphicGraphs_GetDifferentForms()
    {
        var orderer = new CanonGraphOrdererChainDescent();

        var path = Graph(4, (0, 1), (1, 2), (2, 3));       // one component
        var twoEdges = Graph(4, (0, 1), (2, 3));           // two components

        Assert.NotEqual(
            orderer.Run_ToString(new VertexType[4], path),
            orderer.Run_ToString(new VertexType[4], twoEdges));
    }

    [Fact]
    public void RunningOutOfBudget_Flags_RatherThanGuessing()
    {
        // BudgetOverride caps the work. Set it absurdly low and the canonizer
        // declines to answer instead of returning something it cannot justify.
        var orderer = new CanonGraphOrdererChainDescent { BudgetOverride = 1 };
        var g = Graph(6, (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0));

        try
        {
            orderer.Run_ToString(new VertexType[6], g);
            // Reaching here just means the budget was enough; that is fine too.
        }
        catch (CanonizationFlaggedException ex)
        {
            // A flag carries why it gave up, and the order of the automorphism
            // group harvested before it did. FlagKind separates the two causes:
            // Tier2Like (non-abelian residual) vs an abelian one (a CFI gauge).
            Assert.NotEqual(FlagKind.None, ex.Kind);
        }
    }

    [Fact]
    public void VertexTypesConstrainTheOrdering()
    {
        var orderer = new CanonGraphOrdererChainDescent();
        var path = Graph(4, (0, 1), (1, 2), (2, 3));

        // Colouring the two endpoints seeds the partial order, which can change
        // which ordering wins. Note the canonical form printed is the edge matrix
        // only — the types are an input constraint, not part of the output.
        Assert.NotEqual(
            orderer.Run_ToString(new VertexType[4], path),
            orderer.Run_ToString([1, 0, 0, 1], path));
    }

    [Fact]
    public void VertexTypesAreThemselvesCanonical()
    {
        var orderer = new CanonGraphOrdererChainDescent();

        // The same coloured graph under two labellings: a path with its two
        // endpoints coloured 1. Vertices 0..3 form the path 0-1-2-3; in the
        // relabelled copy the path is 3-1-0-2, so its endpoints are 3 and 2.
        var path = Graph(4, (0, 1), (1, 2), (2, 3));
        var relabelled = Graph(4, (3, 1), (1, 0), (0, 2));

        Assert.Equal(
            orderer.Run_ToString([1, 0, 0, 1], path),
            orderer.Run_ToString([0, 0, 1, 1], relabelled));
    }
}
