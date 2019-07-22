# Brief introduction

The json manipulation algorithms are presented below. The task seems one of the important 
when representing data in different schemes for systems which work with the data but in different formats.
The bidirectional approach is used that is when we need to support the mapping from side to side and opposite
on instant way. 

# Json scheme

We use the following definitions, however they can differ in other sources. To investigate the possible
transformations we mean that (yet in non formal way):
* scheme is something permanent;
* data is something changeable.

That in particular means that in the following example 
```json 
{foo : 'bar'}
``` 
`foo` stands for scheme and `'bar'` is data. Going further we see that in the following example

```json 
{foo : {bar : 'baz'}}
``` 
`foo` still stands for scheme, `'bar'` has became the part of scheme also,  and `'baz'` is now data.

The scheme transformation is a procedure which produces one `json` file from another (and possibly back) saving
some data. Within the next explanations we will try to transform different data representations (schemas) saving 
as much data possible and making the transformations bidirectional. So tha mapping is 
``` f :: [scheme1, data] <-> [scheme2, data]```


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
