namespace Canonizer
{
    using VertexType = int;
    using EdgeType = int;

    // Common surface for the reference (CanonGraphOrdererV4) and the perf-focused
    // (CanonGraphOrdererV4Fast) canonizers. Tests that verify isomorphism-class
    // behaviour can target this interface and swap implementations with one line.
    public interface ICanonGraphOrderer
    {
        AdjMatrix Run(VertexType[] vertexTypes, AdjMatrix G);
        string Run_ToString(VertexType[] vertexTypes, EdgeType[,] edges);
    }
}
