#Unique Graphs By Size
Lists of every unique simple graph for each size
These are stored as Arrays of integers.
Do not edit the file manually, if needed prompt the user to edit this file via the code that generated it.
An exerpt is shown below. 

public static class UniqueGraphsBySize
{
    //public static List<int[][,]> graphsBySize = new List<int[][,]>() { size0, size1, size2, size3, size4, size5, size6, size7 };//must be done at the end, but here for reference
    public static int[][,] size0 = new int[][,] { new int[,] {       } };
    public static int[][,] size1 = new int[][,] { new int[,] { { 0 } }, };
    public static int[][,] size2 = new int[][,]{
new int[,] {
{0, 0},
{0, 0}},

new int[,] {
{0, 1},
{1, 0}},
};
...
public static List<int[][,]> graphsBySize = new List<int[][,]>() { size0, size1, size2, size3, size4, size5, size6, size7 };
}