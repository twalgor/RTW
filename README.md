# RTW

This repository contains an implementation of the
contraction-recursive algorithm RTW for treewidth, as described in the
following papaer.

@misc{tamaki2023contraction,
      title={A contraction-recursive algorithm for treewidth},
      author={Hisao Tamaki},
      year={2023},
      note={submitted for publication, will be posted to arXiv soon}
} 


The main purposes of this repository are to make the published experimental results reproducible and to make the code available for research use. 
I plan to develop a production level implementations
in the coming few years, a plan being delayed due to the new algorithmic developments. If you use the code in this repository in your research and
publish results from that research, 
please cite this repository and/or the above paper.

## How to use
The code is written in Java. You need JDK1.8 or higher to compile and run it.  
The current entry point of the code is the following class.

io.github.twalgor.main.Main
<ul>
 <li>
computes the exact treewidth k = tw(G) of a given graph G using algorithms 
described in the paper above, and provides certificates both for 
k >= tw(G), a tree-decomosition of G of width k, and for k <= tw(G), a
minimal contraction H of G such that tw(H) = k.
</li>
<li>
three arguments must be provided
  <ol>
    <li>
		the first argument is the name of the graph, such as "ex001"
	</li>
	<li>
		the second argumant is the path to the directory which contains the graph file in the graph file in the PACE gr format with extension ".gr"
	</li>
	<li>
		the third argument is the path to the output directory, in which the certificate file is to be stored. The certificate file has extension ".twc" and has the format explained by an example below
   </li>
  </ol>
 </li>
<li>
  twc file format example: see Promedus_27_15.twc in the top directory
</li>

   <li>
		c treewidth certificate Promedus_27_15 n 189 m 353 graphpath ..\instance\PACE2017bonus_gr
   </li>
   <li>
		--- this line says that the file contains a treewidth certificate for graph named "Promedus_27_15" with 189 vertices and 353 edges, stored at path ..\instance\PACE2017bonus_gr
   </li>
   <li>
	c  UNIT_BUDGET_UB 100 N_CONDUCIVES_RATIO 10
   </li>
   <li>
    --- this line shows the values of some constants in the Main class
	</li>
	<li> c width 13 time(ms) 25915
	</li>
	<li> --- this lines says that the treewidth of the graph is 13 and was computed in 25915 milliseconds
	<li> s nbags 137 </li>
	<li> --- this line starts the description of the tree-decomopsition of 137 bags, similar to the PACE .td format
	</li>
	<li> b 1 60 62 93 95 97 155 157 158 </li>
	<li> --- this line says that the bag at index 1 consists of vertices 60 62 93 95 97 155 157 158 
	<br> bag descriptions are repeated up to bag at index 137, after which descriptions of tree-decomopsition edges follow (136 lines)
	</li>
	<li> 1 2 </li>
	<li> --- this line shows that bat at 1 and bag at 2 are adjacent in the tree
	</li>
	<li> s ncomponents 33 </li>
	<li> --- this line marks the start of the description of the lower bound certificate which is a contraction of the given graph with 33 vertices
	</li>
	<li> 1 1 9 103 104 105 132 133 134 </li>
	<li> --- this line shows that the first vertex of the contraction is obtained from contracting vertices 1 9 103 104 105 132 133 134 of the original graph. This is repeated for the remainng 32 vertices of the contraction.
	</li>

</ul>


 


