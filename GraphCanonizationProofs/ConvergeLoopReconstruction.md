
## Reconstruction
The current algorithm was made years ago, perhaps as far back as 2019 depending on when it took this form.
It's currently form has shown some success, and some issues, so let's go over what it needs to do and remake it from scratch with my hopefully improved abilities.

Given a graph, it should evaluate all paths leading out of it. Here, assume we're using paths of size n.
Order Insensitive List Comparison (OILC) is quite good at showing _if_ lists should be treated as equal, but at the start, with no information, all you can really compare is paths out of each vertex
I think that's basically the entire algorithm. Vertexes are different, if they have paths leading out of them that are substantatively different according to OILC.
I think it needs a slightly beefed up OILC though, and to specify what it's looking for. It needs to be index dependant, but index order independant, so [112, 112] is differerent than [112, 221], but the same as [221, 221]
Hmm, I think that's actually a very hard requirement thrown onto it. It kind of contains the (compare n! different combinations and keep track of those). I still think it's doable though
It's basically going to be building up a reference list to the vertices as it goes, [112, 221] implies you have a vertex of a type with paths: [112], and another of a type with paths: [112] (relabelled as the ordering is no longer relative to the first one). That's determined by the same logic as the current vertex sorting, and with a deep enough path, dropping a layer each time (so [12]) is fine because it will eventually stablize to be redundant to add layers. This sounds like an absolute recursive nightmare for re-evaluating each time, but for the dynamic version it should be very straight forwards to keep calculating deeper until it stablizes.
The only other thing I think it would need to differentiate between is connection type (no reason I see not to do it as an int instead of bool, same as current model)
I believe I found reverse polish notation (1 2 → instead of 1 → 2) ended up helping stablize the algorithm when using dynamic programming so OILC should likely compare in that order
I feel like it might need more than n iterations to propegate vertex distinctions, but the dynamic programming result showed n, so it _should_ be fine.

From there after the exponential version is built as a proof of concept, it's just a matter of reducing the time complexity with dynamic programming.
Paths of length n+1 out of a can be found by prepending a->[vertex k] to the paths out of [vertex k], my original algorithm kept track of the destination vertex too, but I think it might be unneccesary and I keep trying to factor out but get bugs or don't finish. I should make a modified version of the fast alg to test it before I commit to it here.

The comparison instead of (((a b →) c →)d...) becomes ((a b →) [sort rank of the set of paths of b sized n-1])... wait, that can't be right, that just sounds like color refinement. b's rank is also sort rank of the set of paths of b.
Ah, it's losing track of the intracicies of the loops, that's why, it needs to contain at least ((a b →)[...] c →) or else it would lose track of if it sees a non-adjacent duplicate in the path set.
A simple case ((a1 b1 →) a1 →) can sort differently than ((a1 b1 →) a2 →) (with 1 and 2 being isomorphic copies)
The question is whether the simple loops are able to store the info well enough for an arbitrary sized graph. When I originally did this I concluded yes, I think because
If there are multiple duplicates appearing along a path, then when processing the sub-paths, those should get stored into the path set types
I'll work through the logic needed on a → b → c → a → b → c
a → b → c is fine. ((a b →) c →)
Next it should condense b out to get the set of paths from a to c of size 2
c's loop get's noticed ((c a →) [set of paths a→c of length 2 ]) (though it does have to recognize loops in the ending vertex, which I didn't expect)
At the same time b → c → a → b gets processed as it's a subpath, and so that loop gets noticed, and similarly a → b → c → a.
Indirectly, those subpaths get stored into the vertices, so yeah, I feel like 2 is probably enough to store the needed info

To summarize, a path with the same vertex appearing multiple times in it should be found to be substantatively different than one which doesn't, due to it there being subpaths that start or end with those substantative differences, which will be condensed into the vertex assessments (making them have substantative differences)
Which means that although a single path alone does not contain the informtation of its duplicates, it should be differentiated from one without off the vertexes it traverses, which by neccessity would be

As long as loops are recognized between a vertex and the final destination of the (sub)path, that should get identified, and vertexes without identical looping paths would be distinguished.

