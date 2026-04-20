using System.Collections;
using System.Collections.Generic;
using System;
using System.Linq;
using UnityEngine;

//this is a graph canonizer prototype
//it works off the idea that paths in a graph are unique to isomorphic graphs, and condenses this via dynamic programming to dinstinguish between the sets of paths between each vertex by length, rather than enumerating them all.
//The paths from vertex A to Vertex B are considered a different type to C and D if they're composed of a different count or ratio of subpaths types, or the vertices are a different type.
//Vertices are considered a different type if they're composed of a different count or ratio of subpaths types.
//These are evaluated iteratively until a steady state is reached.
//a perfect implementation of this will always return the same result for any two isomorphic graphs (as they will always have the same paths, which is what also determines vertex type). I haven't proven that any two non-isomorphic graphs won't produce the same result though so am transfering this to lean to work on.
//I'm going to try to make a version that simplifies it less, instead keeping track of "number paths to Vertex B of length C of types (a,b,c,d...)" which then gets simplified down to a single number. This should ensure there's no two verticies that could falsely be named identical
// I think it will tiebreak more or less off of which has more paths that have gone to earlier sorted types of vertices, earlier in their cycles, then more often
//I think I need to ensure two main things for it to work. ONLY two nodes that are truely isomorphic to each other will have the same neighborsByDistance (this is why I'm moving away from count and to a direct, comparision based approach) and second, each vertex can be sorted purely by its neighborsByDistance deterministically, with sort ties detectable

//this is version 4 roughly, which I'm trying to make as simple as possible
//I apparently recently broke it, it's failing on the standard cases like APointedTest

namespace Canonizer
{
    using VertexType = System.UInt32; //using some aliases for Vertex Types and Edge Types, as all we really care about is there's a discrete number of them, and they have a linear ordering.
    using EdgeType = System.UInt64;//using Uint64 (aka uLong) just so mouseover typing is easier to see, interchangable with Int32 and the like

    public class CanonGraphOrdererV4
    {
      

        PathsByLength[] pathsOfLength;//pathsByLength[lengthOfPath].constituantPaths[startVertex].connectedSubPaths[endVertex] represents the paths of length lengthOfPath, that start at [startVertex] and end at [endVertex]
        int maxDepth;//=pathsByLength.GetLength(0)
        int vertexCount;//=pathsByLength.GetLength(1)

        public string Run(VertexType[] vertexTypes, EdgeType[,] edges)
        {
            ValidateInputs(vertexTypes, edges);
            VertexType[] vertexRankings = GetVertexTypeRankings(vertexTypes);
            InitializePaths(vertexRankings, edges);
            OrderVertices(ref vertexRankings);
            EdgeType[,] CanonicalOrdering =  LabelEdgesAccordingToRankings(vertexRankings, edges);
            return AdjMatrixToString(CanonicalOrdering);
        }

        private static void ValidateInputs(VertexType[] vertexTypes, EdgeType[,] edges)
        {
            if (edges.GetLength(0) != edges.GetLength(1))
            {
                throw new Exception("Edges must be a square matrix");
            }
            if (vertexTypes.Length != edges.GetLength(0))
            {
                throw new Exception("Every vertex must be given a type. They may all be given the same type");
            }
        }

        private static VertexType[] GetVertexTypeRankings(VertexType[] vertexTypes)
        {
            VertexType[] vertexRankings = (VertexType[])vertexTypes.ToArray();//don't modify the original array by making a clone with .ToArray(); Trying to emulate the immutable arrays of Lean
            vertexRankings = GetArrayRank(vertexRankings);
            return vertexRankings;
        }

        private static VertexType[] GetArrayRank(VertexType[] arr) //this should turn [0,10,5,5,11] into [0,3,1,1,4]. Each number keeps their relative ordering, and becomes the how many numbers were less than it. NOT DENSE RANKING
        {
            if (arr.Length < 2) return arr;
            (VertexType value, int index)[] sortedByValue = arr.Select((value, index) => (value, index)).OrderBy(x => x.value).ToArray();
            int counter = 0;
            List<(VertexType newValue, int originalIndex)> output = new List<(VertexType newValue, int originalIndex)>() { ((VertexType)counter, sortedByValue[0].index) };
            for (int i = 1; i < sortedByValue.Length; i++)
            {
                if (sortedByValue[i - 1].value != sortedByValue[i].value)
                {
                    counter = i;
                }
                output.Add(((VertexType)counter, sortedByValue[i].index));
            }
            return output.OrderBy(x => x.originalIndex).Select(x => x.newValue).ToArray();
        }

        private void InitializePaths(VertexType[] vertices, EdgeType[,] edges)
        {
            pathsOfLength = new PathsByLength[vertices.Length];
            maxDepth = vertices.Length;//these variables are the same, more used here instead to help with understanding what's being used
            vertexCount = vertices.Length;
            for (int depth = 0; depth < maxDepth; depth++)
            {
                pathsOfLength[depth] = new PathsByLength(vertices);
                for (int fromVertex = 0; fromVertex < vertexCount; fromVertex++)
                {
                    pathsOfLength[depth].pathsFromVertex[fromVertex] = new AllPossiblePathsFrom(vertices,depth,fromVertex);
                    for (int toVertex = 0; toVertex < vertexCount; toVertex++)
                    {
                        pathsOfLength[depth].pathsFromVertex[fromVertex].pathsToVertex[toVertex] = new AllPossiblePathsBetween(vertices,depth, fromVertex, toVertex);
                        if (depth == 0)
                        {
                            if(fromVertex == toVertex)//handles the trivial case. In terms of paths of length 0, there is only one path from yourself to yourself
                            {
                                pathsOfLength[depth].pathsFromVertex[fromVertex].pathsToVertex[toVertex].connectedSubPaths = new PathSegment[1] { new PathSegment(vertices, fromVertex)};
                            }
                            else
                            {
                                pathsOfLength[depth].pathsFromVertex[fromVertex].pathsToVertex[toVertex].connectedSubPaths = new PathSegment[0];
                            }
                            continue;
                        }
                        else
                        {
                            for (int intermediateVertex = 0; intermediateVertex < vertexCount; intermediateVertex++)
                            {
                                pathsOfLength[depth].pathsFromVertex[fromVertex].pathsToVertex[toVertex].connectedSubPaths[intermediateVertex] = new PathSegment(edges[intermediateVertex, toVertex],pathsOfLength[depth-1].pathsFromVertex[fromVertex].pathsToVertex[intermediateVertex]);
                            }
                        }
                    }
                }
            }
            for(int i=0;i<vertices.Length;i++)
            {
                SetNewVertexLabel(ref vertices, i, vertices[i]);//only needed when provided when initialized with non-zero vertext types
            }
        }

        //outputs the Adjacency Matrix relabelled to be in the (cannonical) order provided.
        public static EdgeType[,] LabelEdgesAccordingToRankings(VertexType[] vertexRankings, EdgeType[,] edges)//If the vertex Rankings are [1,0,2,3], then that means it should take the edges and swap colum 0 and 1 and also row 0 and 1.
        {
            int[] vertexRankingsWithDuplicatesIncremented = vertexRankings.Select((item, originalIndex) => (item, originalIndex))//this mess just has the simple job of converting [4,0,1,1,3] into [4,0,1,2,3], which ONLY arises when debugging mid-sort
                                                          .OrderBy(pairedItem => pairedItem)//This whole block of code is already kind of useless, as for any normal case vertexRankings is already 0 to n in some order.
                                                          .Select((pairedItem, sortOrder) => (sortOrder, pairedItem.originalIndex))
                                                          .OrderBy(x => x.originalIndex)
                                                          .Select(x => x.sortOrder)
                                                          .ToArray();

            EdgeType[,] orderedEdges = (EdgeType[,])edges.Clone();
            for (int i = 0; i < vertexRankingsWithDuplicatesIncremented.Length; i++)
            {
                int positionToSwapWith = vertexRankingsWithDuplicatesIncremented.ToList().IndexOf(i);
                orderedEdges = SwapVertexLabelling(orderedEdges, i, positionToSwapWith);
                int temp = vertexRankingsWithDuplicatesIncremented[positionToSwapWith];
                vertexRankingsWithDuplicatesIncremented[positionToSwapWith] = vertexRankingsWithDuplicatesIncremented[i];
                vertexRankingsWithDuplicatesIncremented[i] = temp;
            }
            return orderedEdges;
            //this way works too, but may be harder to theorem prove on as it "sorts" instead of using swaps
            //var rows = vertexRankingsWithDuplicatesIncremented.Select((vertexRankingX, indexX) => (vertexRankingX, vertexRankingsWithDuplicatesIncremented.Select((vertexRankingY, indexY) => (vertexRankingY, edges[indexX, indexY])).ToArray())).ToArray(); 
            //int[][] sortedRows = rows.OrderBy(row => row.vertexRankingX).Select(x => x.Item2.OrderBy(y => y.vertexRankingY).Select(y => y.Item2).ToArray()).ToArray();
            //return string.Join("\n", sortedRows.Select(row => string.Join(", ", row)));

        }

        //swaps the rows and columns of vertex1 with vertex2, as if you'd swapped their labelling. Made to be a simple base move that mantains isomorphism
        public static EdgeType[,] SwapVertexLabelling(EdgeType[,] edges, int vertex1, int vertex2)
        {
            if (vertex1 == vertex2) 
                return (EdgeType[,])edges.Clone();
            EdgeType[,] relabelledEdges= new EdgeType[edges.GetLength(0), edges.GetLength(1)];
            for(int xIndex=0; xIndex < relabelledEdges.GetLength(0); xIndex++)
            {
                for(int yIndex =0;yIndex<relabelledEdges.GetLength(1);yIndex++)
                {
                    relabelledEdges[xIndex, yIndex] = edges[xIndex == vertex1 ? vertex2 : xIndex == vertex2 ? vertex1 : xIndex,
                                                            yIndex == vertex1 ? vertex2 : yIndex == vertex2 ? vertex1 : yIndex];
                }
            }
            return relabelledEdges;
        }

        public static string AdjMatrixToString(EdgeType[,] edges) //Displays every entry in a 2D array.
        {
            return  string.Join("\n", Enumerable.Range(0, edges.GetLength(0)).Select(xIndex => 
                    string.Join(", ", Enumerable.Range(0, edges.GetLength(1)).Select(yIndex => 
                                 edges[xIndex, yIndex].ToString()))));
        }

        private void OrderVertices(ref VertexType[] vertexRankings)
        {
            bool needsResort = true;
            for (int fullySortedVertexes = 0; fullySortedVertexes < vertexCount; fullySortedVertexes++)
            {
                for(int sortCycleCounter = 0; needsResort && (fullySortedVertexes + sortCycleCounter < vertexCount); sortCycleCounter++ )//at least one vertex is sorted per cylce of the inner loop, and at least one per outer loop
                {
                    CalculatePathRankings();
                    //Debug.Log(string.Join("\n\n", vertexRankings.Select((_,index) => LayerToString(index))));
                    //Debug.Log(LayerToString(0));//Left these in as they were extremely helpful when debugging, layer 0, 1, and 2 each deal with different bugs.
                    //Debug.Log(LayerToString(1));
                    //Debug.Log(LayerToString(2));
                    //Debug.Log(LayerToString(3));
                    needsResort = false;

                    for (int startVertex = 0; startVertex < vertexCount; startVertex++)
                    {
                        if (pathsOfLength[maxDepth - 1].pathsFromVertex[startVertex].rankInLayer != vertexRankings[startVertex])//if they're tied at this layer, they must be tied at all previous layers too
                        {
                            //Debug.Log("Vertex lable " + vertexRankings[startVertex] + " is becoming " + pathsOfLength[maxDepth - 1].pathsFromVertex[startVertex].rankInLayer);
                            needsResort = true;
                            SetNewVertexLabel(ref vertexRankings, startVertex, (VertexType) pathsOfLength[maxDepth - 1].pathsFromVertex[startVertex].rankInLayer);
                        }
                    }
                }

                bool firstAppearance = true;
                for (int i = 0; i < vertexCount; i++)
                {
                    if(vertexRankings[i] == fullySortedVertexes)
                    {
                        if(firstAppearance)
                        {
                            firstAppearance = false;
                            continue;
                        }
                        else
                        {
                            needsResort = true;
                            //Debug.Log("Vertex lable " + vertexRankings[i] + " is becoming " + (fullySortedVertexes + 1) + " due to symmetry");
                            SetNewVertexLabel(ref vertexRankings, i, (VertexType) fullySortedVertexes + 1);//this is the hardest thing to justify. If two vertices have a sorting tie after all of this, they are isomorphic to each other (i.e. the graph has a symmetry)
                        }                                                                  //If you have two isomorphic vertices, then chosing either one to come first is equivilent.
                    }
                }
            }
        }

        private void CalculatePathRankings()
        {
            for (int depth = 0; depth < vertexCount; depth++)
            {
                RankPathsBetween(pathsOfLength[depth].pathsFromVertex.SelectMany(x=>x.pathsToVertex).ToArray());
                RankPathsFrom(pathsOfLength[depth].pathsFromVertex);
            }
        }

        private void RankPathsBetween(AllPossiblePathsBetween[] allPathsBetween)
        {
            AllPossiblePathsBetweenComparer pathsBetweenComparer = new AllPossiblePathsBetweenComparer();
            AllPossiblePathsBetween[] sortedPaths = allPathsBetween.ToArray();//don't modify the original's order
            Array.Sort(sortedPaths, pathsBetweenComparer);
            int counter = 0;
            for (int toVertex = 0; toVertex < sortedPaths.Length; toVertex++)
            {
                if (toVertex != 0 && (pathsBetweenComparer.Compare(sortedPaths[toVertex - 1], sortedPaths[toVertex]) != 0))
                {
                    counter = toVertex;
                }
                sortedPaths[toVertex].rankInLayer = counter;
            }
        }
        private void RankPathsFrom(AllPossiblePathsFrom[] connectedSubPaths)
        {
            AllPossiblePathsFromComparer pathsFromComparer = new AllPossiblePathsFromComparer();
            AllPossiblePathsFrom[] sortedPaths = connectedSubPaths.ToArray();//don't modify the original's order
            Array.Sort(sortedPaths, pathsFromComparer);
            int counter = 0;
            for (int toVertex = 0; toVertex < sortedPaths.Length; toVertex++)
            {
                if (toVertex != 0 && (pathsFromComparer.Compare(sortedPaths[toVertex - 1], sortedPaths[toVertex]) != 0))
                {
                    counter = toVertex;
                }
                sortedPaths[toVertex].rankInLayer = counter;
            }
        }

        private void SetNewVertexLabel(ref VertexType[] vertexTypes, int index, VertexType value)
        {
            vertexTypes[index] = value;

            //this entire function could be skipped if I converted everything to reference varaibles, but I'm being explicit
            for (int depthToUpdateVertexType = 0; depthToUpdateVertexType < maxDepth; depthToUpdateVertexType++)
            {
                pathsOfLength[depthToUpdateVertexType].pathsFromVertex[index].startVertexType = vertexTypes[index];
                for (int endVertex = 0; endVertex < vertexCount; endVertex++)
                {
                    pathsOfLength[depthToUpdateVertexType].pathsFromVertex[index].pathsToVertex[endVertex].startVertexType = vertexTypes[index];
                }
                for (int startVertex = 0; startVertex < vertexCount; startVertex++)
                {
                    pathsOfLength[depthToUpdateVertexType].pathsFromVertex[startVertex].pathsToVertex[index].endVertexType = vertexTypes[index];
                }
            }
            pathsOfLength[0].pathsFromVertex[index].pathsToVertex[index].connectedSubPaths[0].selfVertexType = vertexTypes[index];
        }     


        private string LayerToString(int depth = 0)//Just a debug function to view all of what's in a layer. I've left it in as it was quite useful
        {
            return string.Join("\n", pathsOfLength[depth].pathsFromVertex.Select(
                pathStart =>
                {
                    return  pathStart.rankInLayer + ". " + pathStart.pathsToVertex.Length + " paths:(" +
                        string.Join(",", pathStart.pathsToVertex.Select(
                            pathBetween => 
                            "<"+string.Join("    ",pathBetween?.connectedSubPaths?.Select(path =>
                            "[" + path?.subPath?.rankInLayer.ToString() + "," + path?.edgeType.ToString() + "]"))
                        +">")) + ")";
                }
                ));
        }

        public class PathSegment //represends a layer in a path. Holds the data of the final layer, and a link to the path that is itself, except missing the final layer
        {//Needs to hold data in the form [to x of connection type y], when currently it's [from x of connection type y]. Which matters more at the bottom layer
            public EdgeType edgeType;
            public AllPossiblePathsBetween subPath;
            public bool isBottomLayer = false;
            public int selfVertexIndex;
            public VertexType selfVertexType;
            public PathSegment(EdgeType edgeType, AllPossiblePathsBetween subPath)
            {
                this.edgeType = edgeType;
                this.subPath = subPath;
            }
            public PathSegment(VertexType[] vertices, int vertexIndex)
            {
                this.isBottomLayer = true;
                this.selfVertexIndex = vertexIndex;
                this.selfVertexType = vertices[vertexIndex];
            }
        }
        private class PathSegmentComparer : IComparer<PathSegment>
        {
            public int Compare(PathSegment x, PathSegment y)
            {
                if (x.isBottomLayer != y.isBottomLayer)
                {
                    throw new Exception("Why are you comparing paths of different lengths?!");
                    return x.isBottomLayer ? 1 : -1;//should never occur
                }
                if (x.isBottomLayer)
                {
                    if (x.selfVertexType != y.selfVertexType)
                        return x.selfVertexType > y.selfVertexType ? 1 : -1;
                    return 0;
                }
                else
                {
                    if (x.subPath.rankInLayer != y.subPath.rankInLayer)
                    {
                        return x.subPath.rankInLayer < y.subPath.rankInLayer ? 1 : -1;
                    }
                    if (x.edgeType != y.edgeType)
                    {
                        return x.edgeType < y.edgeType ? 1 : -1;
                    }
                    return 0;
                }
            }
        }



        public class AllPossiblePathsBetween //represents all the paths of a given length startVertex -> subPath -> connectionType -> endVertex, (startVertex is technically inside of the subPath)
        {
            public int depth;//only for debugging
            public VertexType startVertexType;
            public int startVertexIndex;
            public VertexType endVertexType;
            public int endVertexIndex;
            public int rankInLayer = 0;
            public PathSegment[] connectedSubPaths;
            public AllPossiblePathsBetween(VertexType[] vertices, int depth, int startVertexIndex, int endVertexIndex)
            {
                this.depth             = depth;
                this.startVertexIndex  = startVertexIndex;
                this.startVertexType   = vertices[startVertexIndex];
                this.endVertexIndex    = endVertexIndex;
                this.endVertexType     = vertices[endVertexIndex];
                this.connectedSubPaths = new PathSegment[vertices.Length];
            }
        }
        private class AllPossiblePathsBetweenComparer : IComparer<AllPossiblePathsBetween> //looks at the set of all ways from A to B, and compares it to the set of all ways from C to D, and checks if you could be certain someone hadn't handed you the same pair twice
        {
            public int Compare(AllPossiblePathsBetween x, AllPossiblePathsBetween y)
            {

                if (x.endVertexType != y.endVertexType)
                    return x.endVertexType > y.endVertexType ? 1 : -1;
                PathSegmentComparer pathSegmentComparer = new PathSegmentComparer();
                int subLayerComparison = OrderInsensitiveListComparison(x.connectedSubPaths, y.connectedSubPaths, pathSegmentComparer);//Start vertex,end vertex, edge type is the sort priority for lexicographical, but now fitting that in is a bit rough
                if (subLayerComparison != 0)
                    return subLayerComparison;
                return 0;
            }
        }
        public class AllPossiblePathsFrom //represents all the paths from this vertex with a length = depth
        {
            public VertexType startVertexType;
            public int startVertexIndex;
            public int depth;//only used for debugging
            public AllPossiblePathsBetween[] pathsToVertex;//represents all the paths startVertex ->connectionType->subPath
            public int rankInLayer = 0; //must be calculated before use, this is effectively the [startVertex]'s calculated rank, mentioned in the comparer

            public AllPossiblePathsFrom(VertexType[] vertices, int depth, int startVertexIndex)
            {
                this.depth = depth;
                this.startVertexType = vertices[startVertexType];
                this.startVertexIndex = startVertexIndex;
                this.pathsToVertex = new AllPossiblePathsBetween[vertices.Length];
            }
        }

        private class AllPossiblePathsFromComparer : IComparer<AllPossiblePathsFrom>
        {
            public int Compare(AllPossiblePathsFrom x, AllPossiblePathsFrom y)
            {
                if (x.startVertexType != y.startVertexType)//if the vertex was given an earlier rank, deffer to that. Otherwise, check if the two vertices are distinguishable
                {
                    return x.startVertexType > y.startVertexType ? 1 : -1; 
                }
                return OrderInsensitiveListComparison(x.pathsToVertex, y.pathsToVertex, new AllPossiblePathsBetweenComparer());
            }
        }
        private class PathsByLength //represents all paths of a given length
        {
            public AllPossiblePathsFrom[] pathsFromVertex;
            public PathsByLength(VertexType[] vertices)
            {
                pathsFromVertex = new AllPossiblePathsFrom[vertices.Length];
            }
        }
        public static int OrderInsensitiveListComparison<T>(T[] arr1, T[] arr2, IComparer<T> comparer)//Compares an array based on what it contains, not it's order. For instance ababca == aaabbc
        {
            if (arr1.Length != arr2.Length)//this should always be unused, except length zero paths. In that case I use it for discarding paths from a to b of length zero (as that would be length 1)
                return arr1.Length < arr2.Length ? 1 : -1;
            T[] arr1Sorted = arr1.ToArray();//don't modify the original array
            T[] arr2Sorted = arr2.ToArray();
            Array.Sort(arr1Sorted, comparer);
            Array.Sort(arr2Sorted, comparer);
            for (int i = 0; i < arr1Sorted.Length; i++)
            {
                if (comparer.Compare(arr1Sorted[i], arr2Sorted[i]) != 0)
                {
                    return comparer.Compare(arr1Sorted[i], arr2Sorted[i]);
                }
            }
            return 0;
        }
    }
}
