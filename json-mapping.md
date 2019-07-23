# Brief introduction

The json manipulation algorithms are presented below. The task seems one of the important 
when representing data in different schemes for systems which work with the same data but in different formats.
The bidirectional approach is used that is when we need to support the mapping from one side to another and back 
instantly.

# Json scheme and data

We use the following definitions, however they can differ in other sources. To investigate the possible
transformations we mean that (yet in non formal way):
* scheme is something permanent;
* data is something changeable.

That in particular means that in the following example 
```jsonc 
{foo : 'bar'}
``` 
`foo` stands for scheme and `'bar'` is data. Going further we see that in the following example

```jsonc 
{foo : {bar : 'baz'}}
``` 
`foo` still stands for scheme, `'bar'` has become the part of scheme also,  and `'baz'` is now data.

The scheme transformation is a procedure which produces one `json` file or memory structure from another (and possibly back) saving some data. Within the next explanations we will try to transform different data representations (schemas) saving 
as much data as possible and making the transformations bidirectional. So the mapping is being abstracted as follows
```jsonc 
f :: [scheme1, data1] <-> [scheme2, data2].
```
Then we assume that the data is the same ```data1=data2```. Because we don't care about real binary data storage we mean that business pieces of information extracted from both data are equal and further omit this simply writing equality on data.
For example we assume that in the following jsons the data are equal:
```jsonc
j1 = {phone: '1234'}
j2 = {system : 'phone'; value :'1234'}
```
What do we mean here? Actually we mean literally that there is no need for any addidtional knowledge to convert
`j1<->j2` in both directions and the behaviour of our system will be the same on both input
`j2` and `f (j1)`. Look next
```jsonc
j3 = {system : 'phone'; value :'1234'; type: 'contact'}
```
And here let's suggest that we also want to have ```data3=data1```. That means the additional input ```{type: 'contact'}```
is constant and doesn't depend on other data. However this fact cannot be learned from the input ```j1```. There is
no information about the fact that we map contact there. So the fact about possiblity to transform `j1` to `j3` cannot be deduced just looking at data - we need to postulate it. 

So finally we define the mapping as follows
```haskell
f12 :: [env1, scheme1, data1] -> [scheme2, data2]
f21 :: [env2, scheme2, data2] -> [scheme1, data1]
```
where environment arguments are implicit and means "we know what we map". The environment is usually referred as 'context' and it is of external nature.

Further we will suggest that it is given and will denote it as universal for both directions - just 'context' when needed but in most cases will omit it.

# Bidirectional transformations

Having two transformations `f12` and `f21` we need to get assured that the transformations are performed correctly
what means that functions `f12` and `f21` are inverse to each other so `f12 . f21 = f21 . f12 = id`,  where `.` denotes 
functional composition.

Speaking business language, bidirectional transformation means that we do not loose data and do not add any additional data
when transforming besides the context which always assumed as implicit parameter of all mappings (recall "we know what we map" (KWM)).

What does it mean in practice we'll see in the next paragraphs along with the potential tricks and traps.

Please note that one directional mapping can always be referred as 'projection'. Why? Actually we cannot project one integer to another, the term 'projection' means that we have some structure on the left side of projection and some structure on the right one. The projections means that the corresponding structures are "similar". In our case the structure is inherited from the json scheme.

So, we will try to build more or less generic bidirectional mapping, saving the structure, that is two projections, one inverse to another (modulo context).

# Internal representations

To speak about the projections we need to define the underlying algebraic structures which we would like to preserve.
The "algebra" of aby data can always be defined in terms of possible transformations of this data (find discussions about the "Principle of observability" somewhere, I will also write something later). 

At the moment we know that what we can do with `json` is operations like `assoc, dissoc, getin` etc. Those operations are almost the same which we can do with trees. Not giving the exact definition let's look at some examples.

## Paths
Consider the `json` structure 
```jsonc
j = {a : {aa : "a.aa"}, b: {bb: "b.bb", cc: "b.cc", dd: {aaa: "b.dd.aaa"}}}.
```
The scheme contains keys `a, aa, b, bb, cc, dd, aaa` and data `"a.aa", "b.bb", "b.cc", "b.dd.aaa"`.
We specially give the data names like that to show the fact, that we can always calculate the path from the start to 
the particulat piece of data. The path here is the list of keys which univocally define the data inside the given `json`
while the keys at each level are unique. Nevertheless it seems obvious we give the exact paths and data:
```haskell
a -> aa -> "a.aa"
b -> bb -> "b.bb"
b -> cc -> "b.cc"
b -> dd -> aaa -> "b.dd.aaa".
```
Note that the information contained in the previous 4 lines is exactly the same as in the correspondent variable `j`.
The above mentioned way of `json` data definition we will call 'paths' formalism. It is explicitly typed as follows:
```haskell
paths = [([key], data)]
```
that is the list of pairs of key list and final data. It is a simple enough data structure very similar to list of lists.
However it contains some redundant repetitions of keys for data stored within the same heads.

## Trees

One can observe easily that the same data structure we can represent by typing it by tree
```haskell
tree = empty :: tree | leaf :: node -> tree | branch :: [(key, tree)] -> tree
```
which is the tree with nodes of `node` type and links of `key` type. Our example can be shown as the
following tree:

![Alt text](https://g.gravizo.com/source/tree1?https%3A%2F%2Fraw.githubusercontent.com%2Fandruiman%2Fjson%2Dcoq%2Fmaster%2Fjson%2Dmapping.md)
<details> 
<summary></summary>
tree1
  digraph G {
    size ="4,4";
    "root 0" [shape=box];
    "root 1" [shape=box];
    "root 2" [shape=box];
    "root 6" [shape=box];
    "root 0" -> "root 1" [label="a"];
    "root 0" -> "root 2" [label="b"];
    "root 1" -> "data 3 \"a.aa\"" [label = "aa"];
    "root 2" -> "data 4 b.bb" [label = "bb"];
    "root 2" -> "data 5 b.cc" [label = "cc"];
    "root 2" -> "root 6" [label = "dd"];
    "root 6" -> "data 7 b.dd.aaa" [label = "aaa"]
  }
tree1
</details>

The `node` type represents `root` or `data`:
```haskell
node = root_node :: Integer -> node | data_node :: Integer -> data -> node.
``` 
We enumerate the nodes for further purposes. The above given internal representation we will call 'tree'.

Now we can see that actually the connections are always made between some nodes, and are labeled with some key.
What if we store them separately.

## Tables

The idea to store the nodes and links separately leads us to the following representation, which can be named 
'sparse tables'. This approach suggests storing nodes as a list like `[node]` and links as a square
table of type `Maybe key`. The presense of key (having the `Just k` in the intersection) inside the table 
at position `(m,n)` means that the link exists between node `m` and `n`. Having `Nothing` merely means there is 
no link. To show our toy data we accumulate the node as 
```haskell
nodes = [root 0, root 1, root 2, data 3 "a.aa", data 4 "b.bb", data 5 "b.cc", root 6, data 7 "b.dd.aaa"]
```
and

`table =` 

| X        | `root 0` | `root 1` | `root 2` | `data 3 "a.aa"` | `data 4 "b.bb"` | `data 5 "b.cc"` | `root 6` | `data 7 "b.dd.aaa"`
|:---------|:--------:|:--------:|:--------:|:--------:|:--------:|:--------:|:--------:|:--------:|
| `root 0` | X        |   a      |   b      | X  | X  | X  | X  | X|
| `root 1` | X        |   X      |   X      | aa | X  | X  | X  | X| 
| `root 2` | X        |   X      |   X      | X  | bb | cc | dd | X|
| `data 3 "a.aa"` | X| X| X| X| X| X| X| X|
| `data 4 "b.bb"` | X| X| X| X| X| X| X| X|
| `data 5 "b.cc"` | X| X| X| X| X| X| X| X|
| `root 6` | X| X| X| X| X| X| X| aaa|
| `data 7 "b.dd.aaa"` | X| X| X| X| X| X| X| X| 

The table is very sparse, because number of links is not more number of nodes (unless there are more 
than one link to a node) (actually the number of links is 1 less than number of nodes in a fully connected tree), 
and number of cells is squared number of nodes. The useful properties of the table are
* There is no any link (the row is empty) for `data` nodes;
* There is no any link before the diagonal (the node cannot link to the previously numbered element, if we build numbers correctly).
And where the first properties is strict (it is the fact from correctness), the second one is flexible - one can organize
the table with other indices - and the table will be still correct. From the opposite any correct table can always be presented in a such way - that is topological order of tree when the parents go before children.

We do not consider the optimization of the table formalism, some of them are however easy to perform. 

### Why do we need additional internal representation





![Alt text](https://g.gravizo.com/source/custom_mark10?https%3A%2F%2Fraw.githubusercontent.com%2Fandruiman%2Fjson%2Dcoq%2Fmaster%2Fjson%2Dmapping.md)
<details> 
<summary></summary>
custom_mark10
  digraph G {
    size ="4,4";
    main [shape=box];
    main -> parse [weight=8];
    parse -> execute;
    main -> init [style=dotted];
    main -> cleanup;
    execute -> { make_string; printf};
    init -> make_string;
    edge [color=red];
    main -> printf [style=bold,label="101 times"];
    make_string [label="make a string"];
    node [shape=box,style=filled,color=".7 .3 1.0"];
    execute -> compare;
  }
custom_mark10
</details>
