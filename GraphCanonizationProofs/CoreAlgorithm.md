# Core Algorithm — notes and functionality

This file is an expression and explanation of the convergeLoop in LeanGraphCanonizerV4, made for the purposes of working on the problems in OrbitCompleteAfterConv.md

## Before Dynamic Programming
The algorithm is based on paths of arbitrarily large length, that are type and index sensitive, leaving each vertex.
That is, two vertices are said to be the same if, and only if, there is some single vertex index arrangement for which the paths leaving that vertex, expressed in a form such as (Vertex type A, index 1)-->(Vertex type B, index 1)-/->(Vertex type A, index 2), for which both vertices are the same.
That is the theory anyway, the actual functionality works via direct path comparison.

'Indexes' have been replaced with directly keeping track of each vertex, and then using sorting logic to determine their ordering after the fact. If there's some ordering that's the same for both, then any ordering applied to that one would be the same, so just find one shared (like lexicographically first) to prove if it exists.
If you have want to find the lexigocraphically first index for each of them, then prioritize the paths with earliest duplicates. (skimming the step that you order indicies descending within a path, as 1234 is always better than anything else like 1243)
So if you have 2 paths like 123 or 112, then 112 should come first (even if they share no vertices, making their combined paths either [112, 345] or [123, 445])
This provides solid logic to tiebreak down until you have a lexicographically first index arrangement.
This of course has to get combined with the other things that are being sorted, such as it might not be 112, but rather 1A-/>1A->2A, however this doesn't really change any logic, it just provides a partial ordering before you begin.

Finally, vertexes are compared by their contained paths in lexicographically first order.
To me, it seems very that this is insufficient to determine between two graphs. That's basically saying that if you were placed in those two with infinite string to mark your path, pens to mark your vertices, and time to measure, you couldn't possibly tell them apart (but that somehow they were different). 

## Dynamic Programming Step
This algorithm can then be compressed to not take the exponential amount of time. Normally there are n^n paths of length n, however by realizing that each path of length n between A and B is the 1 length paths from A to X (where X is each other vertex) attatched to the set of paths of length n-1 from X to B, this is suddenly able to be stored in polynomial size.
Additionally, the sorting remains in tact. For two paths to be lexicographially tied, they must be identical from beginning to end. That is, if the paths of length 6 were not identical, then this would propagate down into paths of length 7, 8, 9... etc.

This ends up condensing into a very similar algorithm to color refinement, however there are some key differences.
Perhaps most notably, multiple similar path that start, end, or visit different vertices are not combined. For instance diverging paths that recombine <> aka [A1->A2->A3, A1, A1->A4->A3] vs || aka [A1->A2->A3, A1, A1->*A2*->A3]
Also very importantly paths that start, end, or visit repeat vertices are differentiated. For instance a line segment [A1->A2] vs a loop [A1->A1]
These properties allow it to easily differentiate uniform graphs, the main issue with color refinement and similar approaches.

## Simplifications
In this explanation I've skimmed over the exact comparions used, in large part because they're not what I think's important for proving what's left.
The remaining part I believe is to prove that being sorted equally implies they really should be, so it matters that/if they're distinguished, not in which direction. Some other important properties like, that it's consistant matter, not which. 
These were very hard to keep track of when writing the algorithm and often adjustments were needed to make it stable, like A1->A2[...] is actually sorted in the order A A 1 2 -> [...], however that shouldn't change much.
Also, a nice outcome of condensing to the dynamic programming version is that it must stablize after n iterations, so in other words, paths of length n+1 or higher don't provide new information.
