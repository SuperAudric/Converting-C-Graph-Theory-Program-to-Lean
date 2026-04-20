
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using Canonizer;
using System;
using System.Linq;
using System.Text;
using System.Numerics;
using System.Threading;
using GraphOrderer = Canonizer.CanonGraphOrdererV4;
using System.IO;
using VertexType = System.UInt32; //using some aliases for Vertex Types and Edge Types, as all we really care about is there's a discrete number of them, and they have a linear ordering.
using EdgeType = System.UInt64;
public class GraphCannonTesterForV4Plus : MonoBehaviour
{
    VertexType[] vertices;
    EdgeType[,] edges;
    GraphOrderer myCanonGraphOrderer = new GraphOrderer();
    void Start()
    {
        Thread t = new Thread(ThreadTask);
        t.Start();
    }



    void ThreadTask()
    {
        Debug.Log("Starting");
        SimpleTest();
        
        APointedTest();//fails for V4
        TestOrderingFunction();
        TestAllPermutations(4);
        TestScramblingGenerated(8,0.75f); 
        TestScramblingValid(4);
        //TestScramblingValidLexicographical(5);//Not currently applicable
        Test3CyclePairVS6Cycle();
        TestScrambledLine(6);
        TestScrambledSpider();
        TestScrambled3Cycle();
        Debug3JoinedLineGraphs();
        Debug.Log("Finished");
    }

    private static void TestOrderingFunction()
    {
        List<VertexType> testVertexOrdering = new List<VertexType>();
        System.Random randomizer = new System.Random(102931);
        for (int i = 0; i < 10; i++)
        {
            //testVertexOrdering.Insert(randomizer.Next(0,i), i);
            testVertexOrdering.Add((VertexType)randomizer.Next(0, 9));
        }
        EdgeType[,] testEdges = new EdgeType[10, 10];
        for (int i = 0; i < testEdges.GetLength(0); i++)
        {
            for (int j = 0; j < testEdges.GetLength(1); j++)
            {
                testEdges[i, j] = (EdgeType)(testVertexOrdering[i] * testEdges.GetLength(0) + testVertexOrdering[j]);
            }
        }
        GraphOrderer.LabelEdgesAccordingToRankings(testVertexOrdering.ToArray(), testEdges);
    }

    void SimpleTest()
    {
        GraphOrderer myTestObject = new GraphOrderer();
        VertexType[] vertices1 = { 0, 0, 0, 0 };
        EdgeType[,] edges1 = { { 0, 0, 0, 0 }, { 0, 0, 0, 1 }, { 0, 0, 0, 1 }, { 0, 1, 1, 0 } };
        string run1 = myTestObject.Run(vertices1, edges1);
        VertexType[] vertices2 = { 0, 0, 0, 0 };
        EdgeType[,] edges2 = { { 0, 1, 1, 0 }, { 1, 0, 0, 0 }, { 1, 0, 0, 0 }, { 0, 0, 0, 0 } };
        string run2 = myTestObject.Run(vertices2, edges2);
        if (!run1.Equals(run2)) { Debug.Log($"Failed for {run1}\nand\n{run2}"); } else { Debug.Log("Passed SimpleTest"); }
    }
    void APointedTest()//this is one of the smallest shapes that can't be easily differentiated from it's re-arranged version
    {
        GraphOrderer myTestObject = new GraphOrderer();
        VertexType[] vertices1 = { 0, 1, 1, 3, 4, 5, 6 };
        EdgeType[,] edges1 = new EdgeType[,] {
        {0, 0, 0, 1, 1, 0, 0},
        {0, 0, 1, 0, 1, 0, 0},
        {0, 1, 0, 0, 1, 0, 0},
        {1, 0, 0, 0, 1, 0, 0},
        {1, 1, 1, 1, 0, 0, 0},
        {0, 0, 0, 0, 0, 0, 1},
        {0, 0, 0, 0, 0, 1, 0}
        };
        string run1 = myTestObject.Run(vertices1, edges1);

        VertexType[] vertices2 = { 0, 1, 1, 3, 4, 5, 6 };
        EdgeType[,] edges2 = new EdgeType[,] {
        {0, 0, 1, 0, 1, 0, 0},
        {0, 0, 0, 1, 1, 0, 0},
        {1, 0, 0, 0, 1, 0, 0},
        {0, 1, 0, 0, 1, 0, 0},
        {1, 1, 1, 1, 0, 0, 0},
        {0, 0, 0, 0, 0, 0, 1},
        {0, 0, 0, 0, 0, 1, 0}
        };
        string run2 = myTestObject.Run(vertices2, edges2);
        if (!run1.Equals(run2)) { Debug.Log($"Failed for {run1}\nand\n{run2}"); } else { Debug.Log("Passed APointedTest"); }
    }

    void TestScramblingGenerated(int size, float ratio = 0.5f)
    {
        int matrixSeed = 10593;
        int scrambleSeed = 15326;
        int maxGraphs = 10;
        int testsPerGraphs = 10;
        string uniqueGraphString = "";
        string previousUniqueGraphString;
        for (int i = 0; i < maxGraphs; i++)
        {
            previousUniqueGraphString = "";
            for (int j = 0; j < testsPerGraphs; j++)
            {
                var adjacencyMatrix = GenerateRandomAdjacencyMatrix(size, ratio, matrixSeed + i);
                Scramble(adjacencyMatrix, scrambleSeed + j);
                //Debug.Log(DisplayAdjacencyMatrix(adjacencyMatrix));
                vertices = new VertexType[size];
                uniqueGraphString = myCanonGraphOrderer.Run(vertices, adjacencyMatrix);
                if (!previousUniqueGraphString.Equals("") && !previousUniqueGraphString.Equals(uniqueGraphString)) { Debug.Log($"Failed for i={i} j{j}, \n{previousUniqueGraphString}\nand\n{uniqueGraphString}\n for adjacency matrix \n{DisplayAdjacencyMatrix(adjacencyMatrix)}"); }
                previousUniqueGraphString = uniqueGraphString;


                if (i == maxGraphs - 1 && (j == testsPerGraphs - 2 || j == testsPerGraphs - 1))//outputs so you know when it's done, twice so you can compare to see if it look right
                {
                    Debug.Log(DisplayAdjacencyMatrix(adjacencyMatrix));
                    Debug.Log(uniqueGraphString);
                }
            }
        }
    }

    void Test3CyclePairVS6Cycle()//Tests two graphs that are different, while most of these test 2 that are the same.
    {
        edges = new EdgeType[1, 1];
        AddEdge(0, 1);
        AddEdge(1, 2);
        AddEdge(2, 0);
        AddEdge(3, 4);
        AddEdge(4, 5);
        AddEdge(5, 3);
        string run1 = myCanonGraphOrderer.Run(new VertexType[Math.Max(edges.GetLength(0),edges.GetLength(1))], edges);

        Debug.Log("halfway");
        edges = new EdgeType[1, 1];
        AddEdge(0, 1);
        AddEdge(1, 2);
        AddEdge(2, 3);
        AddEdge(3, 4);
        AddEdge(4, 5);
        AddEdge(5, 0);
        string run2 = myCanonGraphOrderer.Run(new VertexType[Math.Max(edges.GetLength(0),edges.GetLength(1))], edges);
        if (run1.Equals(run2)) { Debug.Log($"Failed for {run1}\nand\n{run2}"); } else { Debug.Log("Passed 3CyclePairVS6Cycle"); }
    }

    void Debug3JoinedLineGraphs()//A case for manual inspection
    {
        edges = new EdgeType[1, 1];
        AddEdge(0, 1);
        AddEdge(1, 2);
        AddEdge(2, 7);
        AddEdge(0, 3);
        AddEdge(3, 4);
        AddEdge(4, 7);
        AddEdge(0, 5);
        AddEdge(5, 6);
        AddEdge(6, 7);
        Debug.Log(myCanonGraphOrderer.Run(GetEmptyVertexSetFromEdges(edges), edges));
    }
    void TestScrambled3Cycle()
    {
        edges = new EdgeType[1, 1];
        AddEdge(1, 2);
        AddEdge(2, 3);
        AddEdge(3, 1);
        AddEdge(0, 4);
        AddEdge(4, 5);
        AddEdge(5, 0);
        string run1 = myCanonGraphOrderer.Run(GetEmptyVertexSetFromEdges(edges), edges);
        Debug.Log("halfway");
        edges = new EdgeType[1, 1];
        AddEdge(0, 1);
        AddEdge(1, 2);
        AddEdge(2, 0);
        AddEdge(3, 4);
        AddEdge(4, 5);
        AddEdge(5, 3);
        string run2 = myCanonGraphOrderer.Run(GetEmptyVertexSetFromEdges(edges), edges);
        if (!run1.Equals(run2)) { Debug.Log($"Failed for {run1}\nand\n{run2}"); } else { Debug.Log("Passed Scrambled3Cycle"); }
    }
    void TestScrambledSpider()
    {
        int seed = 103925;
        string uniqueGraphString = "";
        string previousUniqueGraphString = "";
        for (int i = 0; i < 10; i++)
        {
            edges = new EdgeType[1, 1];
            AddEdge(0, 1);
            AddEdge(1, 2);
            AddEdge(0, 3);
            AddEdge(3, 4);
            AddEdge(0, 5);
            AddEdge(5, 6);

            Scramble(edges, seed++);
            uniqueGraphString = myCanonGraphOrderer.Run(GetEmptyVertexSetFromEdges(edges), edges);
            if (!previousUniqueGraphString.Equals(uniqueGraphString) && i > 0) { Debug.Log($"Failed for {previousUniqueGraphString}\nand\n{uniqueGraphString}"); }
            previousUniqueGraphString = uniqueGraphString;
        }
        Debug.Log("Finished ScrambledSpider\n" + uniqueGraphString);
    }
    void TestScrambledLine(int lineSize)
    {
        int seed = 103925;
        string uniqueGraphString = "";
        string previousUniqueGraphString = "";
        for (int i = 0; i < 10; i++)
        {
            edges = new EdgeType[1, 1];
            for (int j = 0; j < lineSize - 1; j++)
            {
                AddEdge(j, j + 1);
            }
            Scramble(edges, seed++);
            uniqueGraphString = myCanonGraphOrderer.Run(GetEmptyVertexSetFromEdges(edges), edges);
            if (!previousUniqueGraphString.Equals(uniqueGraphString) && i > 0) { Debug.Log($"Failed for i {i}  {previousUniqueGraphString}\nand\n{uniqueGraphString}"); }
            previousUniqueGraphString = uniqueGraphString;
        }
        Debug.Log("Finished ScrambledLine\n" + uniqueGraphString);
    }
    public void AddEdge(int a, int b)
    {
        if (edges.GetLength(0) <= a || edges.GetLength(1) <= b)
        {
            EdgeType[,] toBeEdges = new EdgeType[Math.Max(a, b) + 1, Math.Max(a, b) + 1];
            for (int i = 0; i < edges.GetLength(0); i++)
            {
                for (int j = 0; j < edges.GetLength(1); j++)
                {
                    toBeEdges[i, j] = edges[i, j];
                }
            }
            edges = toBeEdges;
        }
        edges[a, b] = 1;
        edges[b, a] = 1;
    }
    public void AddDirectedEdge(int a, int b)
    {
        if (edges.GetLength(0) <= a || edges.GetLength(1) <= b)
        {
            EdgeType[,] toBeEdges = new EdgeType[Math.Max(a, b) + 1, Math.Max(a, b) + 1];
            for (int i = 0; i < edges.GetLength(0); i++)
            {
                for (int j = 0; j < edges.GetLength(1); j++)
                {
                    toBeEdges[i, j] = edges[i, j];
                }
            }
            edges = toBeEdges;
        }
        edges[a, b] = 1;
    }

    public static string DisplayAdjacencyMatrix(EdgeType[,] adjacencyMatrix)
    {
        StringBuilder stringBuilder = new StringBuilder();
        for (int i = 0; i < adjacencyMatrix.GetLength(0); i++)
        {
            for (int j = 0; j < adjacencyMatrix.GetLength(1); j++)
            {
                stringBuilder.Append(adjacencyMatrix[i, j] > 0 ? "■" : "□");
            }
            stringBuilder.Append("\n");
        }
        return stringBuilder.ToString();
    }
    public static EdgeType[,] GenerateRandomAdjacencyMatrix(int verticesCount, float connectionRatio, int seed)
    {
        System.Random random = new System.Random(seed);
        EdgeType[,] adjacencyMatrix = new EdgeType[verticesCount, verticesCount];
        for (int i = 0; i < verticesCount; i++)
        {
            for (int j = i + 1; j < verticesCount; j++)
            {
                if (random.NextDouble() <= connectionRatio)
                {
                    adjacencyMatrix[i, j] = 1;
                    adjacencyMatrix[j, i] = 1;
                }
            }
        }
        return adjacencyMatrix;
    }
    public void TestAllPermutations(int maxSize)
    {
        for (int size = 0; size <= maxSize; size++)
        {
            BigInteger maxPermutations = BigInteger.Pow(new BigInteger(2), size * (size - 1) / 2);
            Dictionary<string, List<EdgeType[,]>> recordedCanonNames = new Dictionary<string, List<EdgeType[,]>>();
            for (BigInteger currentPermutation = 0; currentPermutation < maxPermutations; currentPermutation++)
            {
                var adjacencyMatrix = GeneratePermutedAdjacencyMatrix(size, currentPermutation);
                var canonName = myCanonGraphOrderer.Run(new VertexType[adjacencyMatrix.GetLength(0)], adjacencyMatrix);
                if (!recordedCanonNames.ContainsKey(canonName))
                {
                    recordedCanonNames.Add(canonName, new List<EdgeType[,]> { adjacencyMatrix });
                }
                else
                {
                    recordedCanonNames[canonName].Add(adjacencyMatrix);
                }
            }
            IEnumerable<string> uniqueDisplayedThings = recordedCanonNames.Keys;
            string finalFoundGraphs = "{\n" + string.Join("\n\n", uniqueDisplayedThings.Select(x => "{{" + string.Join("},\n{", x.Split("\n")) + "}},")) + "\n}";
            SavetxtFile("GraphsFoundOfSize " + size, finalFoundGraphs);
            Debug.Log("Finished size " + size + ": " + recordedCanonNames.Count() + "\n" + finalFoundGraphs);
        }
    }

    public static EdgeType[,] GeneratePermutedAdjacencyMatrix(int verticesCount, BigInteger permutation)
    {
        EdgeType[,] adjacencyMatrix = new EdgeType[verticesCount, verticesCount];
        for (int i = 0; i < verticesCount; i++)
        {
            for (int j = i + 1; j < verticesCount; j++)
            {
                if (permutation % 2 == 1)
                {
                    adjacencyMatrix[i, j] = 1;
                    adjacencyMatrix[j, i] = 1;
                }
                permutation /= 2;
            }
        }
        return adjacencyMatrix;
    }
    void TestScramblingValid(int size, int? seed = null)
    {
        int scrambleSeed = seed ?? 15326;
        EdgeType[][,] graphsToTest = ConvertJaggedArrayType<EdgeType>(UniqueGraphsBySize.graphsBySize[size]);
        int maxGraphs = graphsToTest.Length;
        int testsPerGraphs = 5;
        string uniqueGraphString = "";
        string previousUniqueGraphString;
        //int i = 729;
        for (int i = 1; i < maxGraphs; i++)
        {
            previousUniqueGraphString = "";
            for (int j = 0; j < testsPerGraphs; j++)
            {
                var adjacencyMatrix = graphsToTest[i];
                Scramble(adjacencyMatrix, scrambleSeed + j);
                vertices = new VertexType[size];
                uniqueGraphString = myCanonGraphOrderer.Run(vertices, adjacencyMatrix);
                if (!previousUniqueGraphString.Equals("") && !previousUniqueGraphString.Equals(uniqueGraphString)) 
                { 
                    Debug.Log($"Failed for i={i} j{j}, \n{previousUniqueGraphString}\nand\n{uniqueGraphString}\n for adjacency matrix \n{DisplayAdjacencyMatrix(adjacencyMatrix)}");
                }
                previousUniqueGraphString = uniqueGraphString;


                if (i == maxGraphs - 1 && (j == testsPerGraphs - 2 || j == testsPerGraphs - 1))//outputs so you know when it's done, twice so you can compare to see if it look right
                {
                    Debug.Log(DisplayAdjacencyMatrix(adjacencyMatrix));
                    Debug.Log(uniqueGraphString);
                }
            }
        }
    }
    /*
    void TestScramblingValidLexicographical(int size, int? seed = null)//this function apparently fails, in large part because my loaded graphs are in Nauty and Traces lexicographically first g6 string format
    {//That's quite different than the lexicographically first adjacency matrix that I'd actually be after.

        int scrambleSeed = seed ?? 15326;
        EdgeType[][,] graphsToTest = ConvertJaggedArrayType<EdgeType>(UniqueGraphsBySize.graphsBySize[size]);
        int maxGraphs = graphsToTest.Length;
        int testsPerGraphs = 1;
        string uniqueGraphString = "";
        string lexicographicallyFirstGraphString;
        //int i = 729;
        for (int i = 0; i < maxGraphs; i++)
        {
            lexicographicallyFirstGraphString = GraphOrderer.AdjMatrixToString(graphsToTest[i]);//the saved one is already in canonical order
            for (int j = 0; j < testsPerGraphs; j++)
            {
                var adjacencyMatrix = graphsToTest[i];
                //Scramble(adjacencyMatrix, scrambleSeed + j);
                vertices = new VertexType[] { 0, 0, 0, 0, 4 };
                uniqueGraphString = myCanonGraphOrderer.Run(vertices, adjacencyMatrix);
                if (!lexicographicallyFirstGraphString.Equals("") && !lexicographicallyFirstGraphString.Equals(uniqueGraphString)) { Debug.Log($"Failed for i={i} j{j}, \n{lexicographicallyFirstGraphString}\nand\n{uniqueGraphString}\n for adjacency matrix \n{DisplayAdjacencyMatrix(adjacencyMatrix)}"); }


                if (i == maxGraphs - 1 && (j == testsPerGraphs - 2 || j == testsPerGraphs - 1))//outputs so you know when it's done, twice so you can compare to see if it look right
                {
                    Debug.Log(DisplayAdjacencyMatrix(adjacencyMatrix));
                    Debug.Log(uniqueGraphString);
                }
            }
        }
    }
    */

    private void Scramble<T>(T[,] items, int seed)
    {
        System.Random randomizer = new System.Random(seed);
        for (int rowsRandomized = 0; rowsRandomized < items.GetLength(0) - 1; rowsRandomized++)
        {
            int randomRow = rowsRandomized + (randomizer.Next() % (items.GetLength(0) - rowsRandomized));//random row between rowsRandomized+1 and items.GetLength(0). Yes there are better ways to randomize

            for (int i = 0; i < items.GetLength(0); i++)//swap row [rowsRandomized] with row [randomRow]
            {
                T temp = items[randomRow, i];
                items[randomRow, i] = items[rowsRandomized, i];
                items[rowsRandomized, i] = temp;
            }
            for (int i = 0; i < items.GetLength(0); i++)//swap column [rowsRandomized] with column [randomRow]
            {
                T temp = items[i, randomRow];
                items[i, randomRow] = items[i, rowsRandomized];
                items[i, rowsRandomized] = temp;
            }
        }
    }

    private VertexType[] GetEmptyVertexSetFromEdges(EdgeType[,] edges)
    {
        return new VertexType[Math.Max(edges.GetLength(0), edges.GetLength(1))];
    }

    private void SavetxtFile(string fileName, string fileContents)
    {
        string filePath = Application.dataPath + "/GraphCanonizationGraphs/" + fileName + ".txt";
        StreamWriter sr;
        if (File.Exists(filePath))
        {
            File.Delete(filePath);
        }
        sr = File.CreateText(filePath);
        sr.Write(fileContents);
        sr.Close();
    }

    public static T[][,] ConvertJaggedArrayType<T>(int[][,] input)
    {
        if (input == null)
            return null;

        int outerLength = input.Length;
        T[][,] result = new T[outerLength][,];

        for (int i = 0; i < outerLength; i++)
        {
            int[,] inner = input[i];
            if (inner == null)
            {
                result[i] = null;
                continue;
            }

            int rows = inner.GetLength(0);
            int cols = inner.GetLength(1);

            T[,] converted = new T[rows, cols];
            for (int r = 0; r < rows; r++)
            {
                for (int c = 0; c < cols; c++)
                {
                    converted[r, c] = (T)Convert.ChangeType(inner[r, c], typeof(T));
                }
            }

            result[i] = converted;
        }

        return result;
    }
}